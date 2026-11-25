import LeanSwe.ConnectProxy.SysBridge.SlotSteps

namespace LeanSwe.ConnectProxy.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model

/-- Advance one poll tick for a `.closingReply` slot. -/
def stepClosingReply {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (slot : ClientSlot fd dnsJob)
    (clientFd? : Option fd)
    (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool) (drained : Nat) (deadlineMs : Nat)
    (cRev : Poll.PollEvents) (nowMs : Nat) : m (ClientSlot fd dnsJob) := do
  match clientFd? with
  | none => return { slot with phase := .done }
  | some cfd =>
    match ← closingSendStep sys.net cfd replyBytes replyOff shutWr cRev with
    | none =>
      sys.closeFd cfd
      return { slot with phase := .done }
    | some (off1, shut1) =>
      match ← closingDrainStep sys.net cfd shut1 drained cRev with
      | none =>
        sys.closeFd cfd
        return { slot with phase := .done }
      | some drained1 =>
        if nowMs >= deadlineMs then
          sys.closeFd cfd
          return { slot with phase := .done }
        else
          return { slot with phase := .closingReply (some cfd) replyBytes off1 shut1 drained1 deadlineMs }

/-- Accept pending connections on `listenFd` while `slots.size < maxConcurrentTunnels`. -/
def acceptNewClientsAux {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (listenFd : fd)
    (nowMs : Nat) :
    Nat → Array (ClientSlot fd dnsJob) → m (Array (ClientSlot fd dnsJob))
  | 0, slots => pure slots
  | fuel + 1, slots => do
    if slots.size >= limits.maxConcurrentTunnels then
      return slots
    else
      match ← sys.net.accept4 listenFd { nonblock := true, cloexec := true } with
      | .ok (cfd, _) =>
        let newSlot : ClientSlot fd dnsJob :=
          { phase := .handshake cfd ByteArray.empty (nowMs + limits.headerTimeoutMs)
            eventEmitted := false
            target? := none
            pipelined := ByteArray.empty }
        acceptNewClientsAux sys limits listenFd nowMs fuel (slots.push newSlot)
      | .error e =>
        if e == Errno.EINTR then
          acceptNewClientsAux sys limits listenFd nowMs fuel slots
        else
          return slots

/-- Accept up to `MAX_ACCEPT_BATCH` clients while respecting `limits.maxConcurrentTunnels`. -/
def acceptNewClients {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (listenFd : fd)
    (nowMs : Nat)
    (slots : Array (ClientSlot fd dnsJob)) : m (Array (ClientSlot fd dnsJob)) :=
  acceptNewClientsAux sys limits listenFd nowMs MAX_ACCEPT_BATCH slots

/-- Close all descriptors owned by `slot`, cancel any pending `dnsJob`, and emit `"proxy stopped"` if undecided. -/
def teardownSlot {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (cancelDns : dnsJob → m Unit)
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent) : m (Array ConnectEvent) := do
  let (_, events1) :=
    match slot.target? with
    | some (h, p) =>
      emitSlotEvent slot events { host := some h, port := some p, outcome := .failed, reason := some "proxy stopped" }
    | none =>
      emitSlotEvent slot events { outcome := .failed, reason := some "proxy stopped" }
  match slot.phase with
  | .handshake cfd _ _ => sys.closeFd cfd
  | .dns cfd _ _ job =>
    cancelDns job
    sys.closeFd cfd
  | .connecting cfd ufd .. =>
    sys.closeFd ufd
    sys.closeFd cfd
  | .relay st =>
    let _ ← Relay.closeRelayBoth sys.closeFd st
  | .closingReply cfd? .. =>
    NetRelay.closeOptFd sys.closeFd cfd?
  | .done => pure ()
  return events1

/-- Tear down every active slot in `slots` in `accept()` order, recording `"proxy stopped"` for undecided slots. -/
def teardownAllSlotsList {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (cancelDns : dnsJob → m Unit) :
    List (ClientSlot fd dnsJob) → Array ConnectEvent → m (Array ConnectEvent)
  | [], events => pure events
  | slot :: rest, events => do
    let events1 ← teardownSlot sys cancelDns slot events
    teardownAllSlotsList sys cancelDns rest events1

/-- Synchronous single-threaded DNS resolver helper over `sys.dns` (used in relational `healthyStep` proofs and pure model runs). -/
def startDnsSync {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (slot : ClientSlot fd Unit)
    (events : Array ConnectEvent)
    (clientFd : fd)
    (host : String) (port : UInt16) : m (ClientSlot fd Unit × Array ConnectEvent) := do
  match ← sys.dns.getaddrinfo host { family := .any, sockType := .stream } with
  | .error dnsErr =>
    let msg := if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message
    let (slot1, events1) :=
      emitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
    let slot2 ← enterClosingReply sys limits slot1 clientFd 502
    return (slot2, events1)
  | .ok addrs =>
    let ips := filterUnscopedDnsAddrs addrs
    handleResolveDecision sys limits onResolved slot events clientFd host port ips

/-- Construct a synchronous, single-threaded `RawConnectProxyOpsM (StateM W)` stand-in backed purely by `sys : CProxySysOpsM (StateM W) fd`.
    Formal FD-conservation and `healthyStep` proofs verify this synchronous stand-in; the unified `Core.ConcOpsM` concurrent driver (`SysBridge.Driver.withProxyM` / `runProxyLoopM`) is verified via `Proofs.obeys_model` and runtime/mutation tests. -/
def mkSyncRawOps {W fd : Type}
    (sys : CProxySysOpsM (StateM W) fd)
    (getTable : W → SyncProxyTable fd)
    (setTable : W → SyncProxyTable fd → W) : RawConnectProxyOpsM (StateM W) :=
  { mapRawError := Model.mapRawErrorPure
    startProxy := fun vcfg _ _ => do
      match ← createListener sys vcfg with
      | .error err => return .error err
      | .ok (lfd, wakeR, wakeW, boundPort) =>
        let w ← get
        let tbl := getTable w
        let hid := freshSyncHandleId tbl
        let entry : SyncProxyEntry fd :=
          { handleId := hid
            port := boundPort
            vcfg := vcfg
            listenFd := lfd
            wakeR := wakeR
            wakeW := wakeW }
        let tbl' : SyncProxyTable fd :=
          { nextHandleId := hid + 1
            entries := entry :: tbl.entries }
        set (setTable w tbl')
        return .ok { handleId := hid, port := boundPort }
    stopProxy := fun proxy => do
      let w ← get
      let tbl := getTable w
      match tbl.entries.find? (fun e => e.handleId == proxy.handleId) with
      | none =>
        return .error (Model.mapRawErrorPure (.invalidArgument none "proxy handle is not active"))
      | some entry =>
        let tbl' : SyncProxyTable fd :=
          { tbl with entries := tbl.entries.filter (fun e => e.handleId != proxy.handleId) }
        set (setTable w tbl')
        let finalEvents ← teardownAllSlotsList sys (fun _ => pure ()) entry.slots.toList entry.events
        sys.closeFd entry.listenFd
        sys.closeFd entry.wakeR
        sys.closeFd entry.wakeW
        return .ok finalEvents
    activeProxyCount := do
      let w ← get
      return (getTable w).entries.length }

/-- Compute listener `PollEvents` (`pollin = true` iff `activeSlots < maxConcurrentTunnels`). -/
def listenPollEvents (activeSlots maxConcurrentTunnels : Nat) : Poll.PollEvents :=
  { pollin := decide (activeSlots < maxConcurrentTunnels) }

/-- Update optional minimum remaining deadline duration in milliseconds relative to `nowMs`. -/
def updatePollMinRem (nowMs : Nat) (cur? : Option Nat) (dl : Nat) : Option Nat :=
  let rem := dl - nowMs
  match cur? with
  | none => some rem
  | some prev => some (Nat.min prev rem)

/-- Structural helper building `ppoll` requests, per-slot index pairs, and minimum timeout across `slots`. -/
def buildPollBatchAux {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (pollDnsReady : dnsJob → m Bool)
    (nowMs : Nat)
    (slots : List (ClientSlot fd dnsJob))
    (reqs : Array (fd × Poll.PollEvents))
    (indices : Array (Option Nat × Option Nat))
    (minRem? : Option Nat)
    (dnsWatchFd : dnsJob → m (Option fd) := fun _ => pure none) :
    m (Array (fd × Poll.PollEvents) × Array (Option Nat × Option Nat) × Option Nat) := do
  match slots with
  | [] => pure (reqs, indices, minRem?)
  | slot :: rest =>
    match slot.phase with
    | .handshake cfd _ dl =>
      let cIdx := reqs.size
      buildPollBatchAux pollDnsReady nowMs rest
        (reqs.push (cfd, { pollin := true }))
        (indices.push (some cIdx, none))
        (updatePollMinRem nowMs minRem? dl)
        dnsWatchFd
    | .dns cfd _ _ job =>
      let cIdx := reqs.size
      let reqs1 := reqs.push (cfd, {})
      let ready ← pollDnsReady job
      let nextRem? := if ready then some 0 else minRem?
      match ← dnsWatchFd job with
      | some dfd =>
        let dIdx := reqs1.size
        buildPollBatchAux pollDnsReady nowMs rest
          (reqs1.push (dfd, { pollin := true }))
          (indices.push (some cIdx, some dIdx))
          nextRem?
          dnsWatchFd
      | none =>
        buildPollBatchAux pollDnsReady nowMs rest
          reqs1
          (indices.push (some cIdx, none))
          nextRem?
          dnsWatchFd
    | .connecting cfd ufd _ _ _ _ _ dl =>
      let cIdx := reqs.size
      let reqs1 := reqs.push (cfd, {})
      let uIdx := reqs1.size
      buildPollBatchAux pollDnsReady nowMs rest
        (reqs1.push (ufd, { pollout := true }))
        (indices.push (some cIdx, some uIdx))
        (updatePollMinRem nowMs minRem? dl)
        dnsWatchFd
    | .relay st =>
      let (reqs1, cIdx?) :=
        match st.clientFd? with
        | some cfd =>
          let cev := st.clientPollEvents
          if !cev.isEmpty then (reqs.push (cfd, cev), some reqs.size) else (reqs, none)
        | none => (reqs, none)
      let (reqs2, uIdx?) :=
        match st.upstreamFd? with
        | some ufd =>
          let uev := st.upstreamPollEvents
          if !uev.isEmpty then (reqs1.push (ufd, uev), some reqs1.size) else (reqs1, none)
        | none => (reqs1, none)
      buildPollBatchAux pollDnsReady nowMs rest reqs2 (indices.push (cIdx?, uIdx?)) minRem? dnsWatchFd
    | .closingReply cfd? _ _ shutWr _ dl =>
      match cfd? with
      | some cfd =>
        let cIdx := reqs.size
        let ev : Poll.PollEvents := if shutWr then { pollin := true } else { pollout := true }
        buildPollBatchAux pollDnsReady nowMs rest
          (reqs.push (cfd, ev))
          (indices.push (some cIdx, none))
          (updatePollMinRem nowMs minRem? dl)
          dnsWatchFd
      | none =>
        buildPollBatchAux pollDnsReady nowMs rest reqs (indices.push (none, none)) minRem? dnsWatchFd
    | .done =>
      buildPollBatchAux pollDnsReady nowMs rest reqs (indices.push (none, none)) minRem? dnsWatchFd

/-- Compute listener `PollEvents` accounting for detached DNS tasks and `EMFILE` accept backoff. -/
def listenPollEventsWithBackoff (activeSlots maxTunnels nowMs : Nat) : Nat → Nat → Poll.PollEvents
  | 0, 0 => listenPollEvents activeSlots maxTunnels
  | 0, backoffUntil + 1 =>
    { pollin := (listenPollEvents activeSlots maxTunnels).pollin &&
        !decide (nowMs < backoffUntil + 1) }
  | activeDns + 1, backoffUntil =>
    { pollin := (listenPollEvents (activeSlots + (activeDns + 1)) maxTunnels).pollin &&
        !decide (nowMs < backoffUntil) }

/-- Compute initial `ppoll` relative timeout accounting for `EMFILE` accept backoff. -/
def initPollBackoffRem (activeSlots maxTunnels nowMs : Nat) : Nat → Nat → Option Nat
  | 0, 0 => none
  | 0, backoffUntil + 1 =>
    if (listenPollEvents activeSlots maxTunnels).pollin &&
        decide (nowMs < backoffUntil + 1) then
      updatePollMinRem nowMs none (backoffUntil + 1)
    else
      none
  | activeDns + 1, backoffUntil =>
    if (listenPollEvents (activeSlots + (activeDns + 1)) maxTunnels).pollin &&
        decide (nowMs < backoffUntil) then
      updatePollMinRem nowMs none backoffUntil
    else
      none

/-- Build the `ppoll` request array, per-slot index table, and optional relative timeout (clamped via `Poll.msToPollTimespec` for 64-bit Linux `time_t`, where `ppoll(2)` saturates large relative timeouts) for one loop tick. -/
def buildPollBatchM {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (pollDnsReady : dnsJob → m Bool)
    (wakeR listenFd : fd)
    (maxTunnels : Nat)
    (nowMs : Nat)
    (slots : Array (ClientSlot fd dnsJob))
    (activeDnsTasks : Nat := 0)
    (acceptBackoffUntilMs : Nat := 0)
    (dnsWatchFd : dnsJob → m (Option fd) := fun _ => pure none) :
    m (Array (fd × Poll.PollEvents) × Array (Option Nat × Option Nat) × Option Poll.Timespec) := do
  let listenEv := listenPollEventsWithBackoff slots.size maxTunnels nowMs activeDnsTasks acceptBackoffUntilMs
  let initMinRem? := initPollBackoffRem slots.size maxTunnels nowMs activeDnsTasks acceptBackoffUntilMs
  let initReqs : Array (fd × Poll.PollEvents) := #[(wakeR, { pollin := true }), (listenFd, listenEv)]
  let (reqs, indices, minRem?) ←
    buildPollBatchAux pollDnsReady nowMs slots.toList initReqs (Array.emptyWithCapacity slots.size) initMinRem? dnsWatchFd
  return (reqs, indices, minRem?.map Poll.msToPollTimespec)

/-- Execute one polymorphic client slot transition after `ppoll` returns `revents`. -/
def stepSlotM {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (pollDns : dnsJob → m (Option (Except String (Array IpAddr))))
    (cancelDns : dnsJob → m Unit)
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (cRev uRev : Poll.PollEvents)
    (nowMs : Nat)
    (useDnsRevents : Bool := false) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  match slot.phase with
  | .handshake cfd headBuf dl =>
    stepHandshake sys limits onHead onResolved startDns slot events cfd headBuf dl cRev nowMs
  | .dns cfd host port job =>
    if cRev.pollerr || cRev.pollhup || cRev.pollnval then
      cancelDns job
      let (slot1, events1) :=
        emitSlotEvent slot events
          { host := some host, port := some port, outcome := .failed, reason := some "client disconnected" }
      sys.closeFd cfd
      return ({ slot1 with phase := .done, pipelined := ByteArray.empty }, events1)
    else if !useDnsRevents || uRev.pollin || uRev.pollhup || uRev.pollerr || uRev.pollnval then
      match ← pollDns job with
      | none => return (slot, events)
      | some (.error msg) =>
        let (slot1, events1) :=
          emitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
        let slot2 ← enterClosingReply sys limits slot1 cfd 502
        return (slot2, events1)
      | some (.ok ips) =>
        handleResolveDecision sys limits onResolved slot events cfd host port ips
    else
      return (slot, events)
  | .connecting cfd ufd host port cands idx lastErr? dl =>
    stepConnecting sys limits slot events cfd ufd host port cands idx lastErr? dl cRev uRev nowMs
  | .relay st =>
    let st' ← Relay.stepBidirectionalRelay sys.net sys.closeFd st cRev uRev
    if st'.isClosed then
      return ({ slot with phase := .done }, events)
    else
      return ({ slot with phase := .relay st' }, events)
  | .closingReply cfd? rb roff sw dr dl =>
    let slot' ← stepClosingReply sys slot cfd? rb roff sw dr dl cRev nowMs
    return (slot', events)
  | .done => return (slot, events)

/-- Structural helper stepping every slot in `slots` against `indices` and `revents`, pruning finished slots. -/
def stepSlotsListM {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (pollDns : dnsJob → m (Option (Except String (Array IpAddr))))
    (cancelDns : dnsJob → m Unit)
    (indices : Array (Option Nat × Option Nat))
    (revents : Array Poll.PollEvents)
    (nowMs : Nat)
    (idx : Nat)
    (slots : List (ClientSlot fd dnsJob))
    (accSlots : Array (ClientSlot fd dnsJob))
    (accEvents : Array ConnectEvent)
    (useDnsRevents : Bool := false) :
    m (Array (ClientSlot fd dnsJob) × Array ConnectEvent) := do
  match slots with
  | [] => pure (accSlots, accEvents)
  | slot :: rest =>
    let (cIdx?, uIdx?) := indices[idx]?.getD (none, none)
    let cRev := match cIdx? with | some ci => revents[ci]?.getD {} | none => {}
    let uRev := match uIdx? with | some ui => revents[ui]?.getD {} | none => {}
    let (slot', events') ←
      stepSlotM sys limits onHead onResolved startDns pollDns cancelDns slot accEvents cRev uRev nowMs useDnsRevents
    let accSlots' := if !slot'.isFinished then accSlots.push slot' else accSlots
    stepSlotsListM sys limits onHead onResolved startDns pollDns cancelDns indices revents nowMs
      (idx + 1) rest accSlots' events' useDnsRevents

/-- Drain `wakeR` iff `wakeRev.pollin = true`. -/
def maybeDrainWakeSocket {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (wakeR : fd) (wakeRev : Poll.PollEvents) : m Unit :=
  if wakeRev.pollin then drainWakeSocket net wakeR 64 else pure ()

/-- Accept new clients on `listenFd` iff `listenRev.pollin = true`. -/
def maybeAcceptNewClients {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits) (listenFd : fd)
    (nowMs : Nat) (listenRev : Poll.PollEvents)
    (slots : Array (ClientSlot fd dnsJob)) : m (Array (ClientSlot fd dnsJob)) :=
  if listenRev.pollin then acceptNewClients sys limits listenFd nowMs slots else pure slots

/-- Execute one complete polymorphic `ppoll` + wakeup-drain + slot-step + `acceptNewClients` tick. -/
def pollAndStepTickM {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (checkStop : m Bool)
    (pollDnsReady : dnsJob → m Bool)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (pollDns : dnsJob → m (Option (Except String (Array IpAddr))))
    (cancelDns : dnsJob → m Unit)
    (wakeR listenFd : fd)
    (slots : Array (ClientSlot fd dnsJob))
    (events : Array ConnectEvent)
    (activeDnsTasks : Nat := 0)
    (acceptBackoffUntilMs : Nat := 0)
    (countDetachedAfterStep : m Nat := pure 0)
    (dnsWatchFd : dnsJob → m (Option fd) := fun _ => pure none)
    (useDnsRevents : Bool := false)
    (extraWatchFds : Array fd := #[])
    (onExtraWatchRevents : Array Poll.PollEvents → m Unit := fun _ => pure ()) :
    m (PollTickOutcome fd dnsJob) := do
  let now0 ← monoNowMs sys
  let (reqs, indices, timeout?) ←
    buildPollBatchM pollDnsReady wakeR listenFd limits.maxConcurrentTunnels now0 slots
      activeDnsTasks acceptBackoffUntilMs dnsWatchFd
  let extraBase := reqs.size
  let pollReqs :=
    if extraWatchFds.isEmpty then reqs
    else extraWatchFds.foldl (fun acc dfd => acc.push (dfd, { pollin := true })) reqs
  match ← sys.poll.ppoll pollReqs timeout? with
  | .error e =>
    if e == Errno.EINTR then
      return .retryEintr
    else
      return .stopOrFatal
  | .ok revents =>
    maybeDrainWakeSocket sys.net wakeR (revents[0]?.getD {})
    if ← checkStop then
      return .stopOrFatal
    else
      if !extraWatchFds.isEmpty then
        onExtraWatchRevents (revents.extract extraBase (extraBase + extraWatchFds.size))
      let now1 ← monoNowMs sys
      let (nextSlots, nextEvents) ←
        stepSlotsListM sys limits onHead onResolved startDns pollDns cancelDns indices revents now1
          0 slots.toList (Array.emptyWithCapacity slots.size) events useDnsRevents
      let postDetached ← countDetachedAfterStep
      let acceptLimits : ProxyLimits :=
        match postDetached with
        | 0 => limits
        | _ + 1 => { limits with maxConcurrentTunnels := limits.maxConcurrentTunnels - postDetached }
      let acceptedSlots ← maybeAcceptNewClients sys acceptLimits listenFd now1 (revents[1]?.getD {}) nextSlots
      return .stepped acceptedSlots nextEvents

/-- Synchronous `dns.getaddrinfo` lookup helper returning `Except String (Array IpAddr)` for `stepSyncSlot` / `pollAndStepTickSync`. -/
def resolveDnsSync {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (host : String) : m (Option (Except String (Array IpAddr))) := do
  match ← sys.dns.getaddrinfo host { family := .any, sockType := .stream } with
  | .error dnsErr =>
    let msg := if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message
    return some (.error msg)
  | .ok addrs =>
    return some (.ok (filterUnscopedDnsAddrs addrs))

/-- Pure instantiation of `buildPollBatchM` for synchronous testing and verification. -/
def buildPollBatchSync {fd : Type}
    (wakeR listenFd : fd)
    (maxTunnels nowMs : Nat)
    (slots : Array (ClientSlot fd Unit)) :
    Array (fd × Poll.PollEvents) × Array (Option Nat × Option Nat) × Option Poll.Timespec :=
  Id.run (buildPollBatchM (m := Id) (fun () => pure false) wakeR listenFd maxTunnels nowMs slots)

/-- Execute one synchronous client slot transition over an arbitrary `sys : CProxySysOpsM m fd` via `stepSlotM`. -/
def stepSyncSlot {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (slot : ClientSlot fd Unit)
    (events : Array ConnectEvent)
    (cRev uRev : Poll.PollEvents)
    (nowMs : Nat) :
    m (ClientSlot fd Unit × Array ConnectEvent) :=
  let host := match slot.phase with | .dns _ h _ () => h | _ => ""
  stepSlotM sys limits onHead onResolved
    (startDnsSync sys limits onResolved)
    (fun () => resolveDnsSync sys host)
    (fun () => pure ())
    slot events cRev uRev nowMs

/-- Execute one synchronous server `ppoll` + wakeup-drain + slot-step + `acceptNewClients` tick via `pollAndStepTickM`. -/
def pollAndStepTickSync {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (stopRequested : Bool)
    (wakeR listenFd : fd)
    (slots : Array (ClientSlot fd Unit))
    (events : Array ConnectEvent) :
    m (PollTickOutcome fd Unit) :=
  pollAndStepTickM sys limits onHead onResolved
    (pure stopRequested)
    (fun () => pure false)
    (startDnsSync sys limits onResolved)
    (fun () => pure none)
    (fun () => pure ())
    wakeR listenFd slots events


/-- Cooldown duration in milliseconds (`10 ms`) suppressing `listenFd` spin after `accept4` resource exhaustion. -/
def ACCEPT_EMFILE_BACKOFF_MS : Nat := 10

/-- Return `true` iff `e` indicates transient descriptor or socket-buffer exhaustion on `accept4`. -/
def isAcceptResourceErrno (e : Errno) : Bool :=
  e == Errno.EMFILE || e == Errno.ENFILE || e == Errno.ENOMEM || e == Errno.ENOBUFS


/-- Canonical `SysBridgeTarget` wired directly to `SysBridge` and `Relay`.
    Note: `mkRawOps` binds the synchronous single-threaded stand-in `SysBridge.mkSyncRawOps` for formal FD-conservation and `healthyStep` proofs; unified `Core.ConcOpsM` concurrent DNS-task/socketpair orchestration (`SysBridge.Driver.withProxyM` / `runProxyLoopM`) is verified via `Proofs.obeys_model` and runtime/mutation tests. -/
def realBridgeTarget : SysBridgeTarget :=
  { createListener := fun sys vcfg => createListener sys vcfg
    handleCompleteHeadSync := fun sys limits onHead onResolved slot evs cfd head pipe =>
      handleCompleteHead sys limits onHead onResolved
        (startDnsSync sys limits onResolved) slot evs cfd head pipe
    acceptNewClients := fun sys limits lfd now slots =>
      acceptNewClients sys limits lfd now slots
    listenPollinEnabled := fun cur maxT => (listenPollEvents cur maxT).pollin
    buildPollBatchSync := fun wakeR lfd maxT nowMs slots =>
      buildPollBatchSync wakeR lfd maxT nowMs slots
    stepHandshakeSync := fun sys limits onHead onResolved slot evs cfd hb dl rev now =>
      stepHandshake sys limits onHead onResolved
        (startDnsSync sys limits onResolved) slot evs cfd hb dl rev now
    recvIntoRing := fun net fd fuel rb => NetRelay.recvIntoRing net fd fuel rb
    flushRingNonblock := fun net fd fuel rb => NetRelay.flushRingNonblock net fd fuel rb
    stepBidirectionalRelay := fun sys st cRev uRev =>
      Relay.stepBidirectionalRelay sys.net sys.closeFd st cRev uRev
    stepSlotSync := fun sys limits onHead onResolved slot evs cRev uRev nowMs =>
      stepSyncSlot sys limits onHead onResolved slot evs cRev uRev nowMs
    pollAndStepTickSync := fun sys limits onHead onResolved stopFlag wakeR lfd slots evs =>
      pollAndStepTickSync sys limits onHead onResolved stopFlag wakeR lfd slots evs
    mkRawOps := fun sys =>
      mkSyncRawOps sys (fun wt => wt.1.proxyTable)
        (fun (w, tr) tbl => ({ w with proxyTable := tbl }, tr)) }

end LeanSwe.ConnectProxy.SysBridge
