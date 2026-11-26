import LeanSwe.ConnectProxy.SpecMutants.RefBridgeSteps

/-!
Pure spec-passing reference `SysBridgeTarget` over `.Types` and `.Model`
for single-bug `ConnectProxy` specification mutants.
-/

namespace LeanSwe.ConnectProxy.SpecMutants

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Internal.SysBridge
  (MAX_ACCEPT_BATCH CProxySysOpsM ClientSlot SyncProxyEntry SyncProxyTable
   freshSyncHandleId PollTickOutcome)
open LeanSwe.ConnectProxy.Internal.HealthySys (SysBridgeTarget)

/-- Convert a relative timeout in milliseconds to a valid `Poll.Timespec`. -/
def refMsToPollTimespec (ms : Nat) : Poll.Timespec :=
  let clampedSec := Nat.min (ms / 1000) 9223372036854775807
  let remNs := (ms % 1000) * 1000000
  { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }

private def stepClosingReplyRef {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (slot : ClientSlot fd dnsJob) (clientFd? : Option fd)
    (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool) (drained deadlineMs : Nat)
    (cRev : Poll.PollEvents) (nowMs : Nat) : m (ClientSlot fd dnsJob) := do
  match clientFd? with
  | none => return { slot with phase := .done }
  | some cfd =>
    match ← refClosingSendStep sys.net cfd replyBytes replyOff shutWr cRev with
    | none =>
      refCloseSysFd sys cfd
      return { slot with phase := .done }
    | some (off1, shut1) =>
      match ← refClosingDrainStep sys.net cfd shut1 drained cRev with
      | none =>
        refCloseSysFd sys cfd
        return { slot with phase := .done }
      | some drained1 =>
        if nowMs >= deadlineMs then
          refCloseSysFd sys cfd
          return { slot with phase := .done }
        else
          return { slot with phase := .closingReply (some cfd) replyBytes off1 shut1 drained1 deadlineMs }

private def acceptNewClientsAuxRef {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits) (listenFd : fd) (nowMs : Nat) :
    Nat → Array (ClientSlot fd dnsJob) → m (Array (ClientSlot fd dnsJob))
  | 0, slots => pure slots
  | fuel + 1, slots => do
    if slots.size >= limits.maxConcurrentTunnels then return slots
    else
      match ← sys.net.accept4 listenFd { nonblock := true, cloexec := true } with
      | .ok (cfd, _) =>
        let newSlot : ClientSlot fd dnsJob :=
          { phase := .handshake cfd ByteArray.empty (nowMs + limits.headerTimeoutMs)
            eventEmitted := false
            target? := none
            pipelined := ByteArray.empty }
        acceptNewClientsAuxRef sys limits listenFd nowMs fuel (slots.push newSlot)
      | .error e =>
        if e == Errno.EINTR then acceptNewClientsAuxRef sys limits listenFd nowMs fuel slots
        else return slots

/-- Accept up to `MAX_ACCEPT_BATCH` clients while respecting `limits.maxConcurrentTunnels`. -/
def refAcceptNewClients {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits) (listenFd : fd) (nowMs : Nat)
    (slots : Array (ClientSlot fd dnsJob)) : m (Array (ClientSlot fd dnsJob)) :=
  acceptNewClientsAuxRef sys limits listenFd nowMs MAX_ACCEPT_BATCH slots

private def teardownSlotRef {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (cancelDns : dnsJob → m Unit)
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent) : m (Array ConnectEvent) := do
  let (_, events1) :=
    match slot.target? with
    | some (h, p) =>
      refEmitSlotEvent slot events { host := some h, port := some p, outcome := .failed, reason := some "proxy stopped" }
    | none =>
      refEmitSlotEvent slot events { outcome := .failed, reason := some "proxy stopped" }
  match slot.phase with
  | .handshake cfd _ _ => refCloseSysFd sys cfd
  | .dns cfd _ _ job =>
    cancelDns job
    refCloseSysFd sys cfd
  | .connecting cfd ufd .. =>
    refCloseSysFd sys ufd
    refCloseSysFd sys cfd
  | .relay st =>
    let _ ← refCloseRelayBoth (refCloseSysFd sys) st
  | .closingReply cfd? .. =>
    refCloseOptFd (refCloseSysFd sys) cfd?
  | .done => pure ()
  return events1

private def teardownAllSlotsListRef {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (cancelDns : dnsJob → m Unit) :
    List (ClientSlot fd dnsJob) → Array ConnectEvent → m (Array ConnectEvent)
  | [], events => pure events
  | slot :: rest, events => do
    let events1 ← teardownSlotRef sys cancelDns slot events
    teardownAllSlotsListRef sys cancelDns rest events1

/-- Synchronous DNS resolver helper over `sys.dns`. -/
def refStartDnsSync {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (slot : ClientSlot fd Unit) (events : Array ConnectEvent)
    (clientFd : fd) (host : String) (port : UInt16) :
    m (ClientSlot fd Unit × Array ConnectEvent) := do
  match ← sys.dns.getaddrinfo host { family := .any, sockType := .stream } with
  | .error dnsErr =>
    let msg := if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message
    let (slot1, events1) :=
      refEmitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
    let slot2 ← refEnterClosingReply sys limits slot1 clientFd 502
    return (slot2, events1)
  | .ok addrs =>
    refHandleResolveDecision sys limits onResolved slot events clientFd host port (refFilterUnscopedDnsAddrs addrs)

/-- Synchronous single-threaded `RawConnectProxyOpsM` builder over `CProxySysOpsM`. -/
def refMkSyncRawOps {W fd : Type}
    (sys : CProxySysOpsM (StateM W) fd)
    (getTable : W → SyncProxyTable fd)
    (setTable : W → SyncProxyTable fd → W) : RawConnectProxyOpsM (StateM W) :=
  { mapRawError := Model.mapRawErrorPure
    startProxy := fun vcfg _ _ => do
      match ← refCreateListener sys vcfg with
      | .error err => return .error err
      | .ok (lfd, wakeR, wakeW, boundPort) =>
        let w ← get
        let tbl := getTable w
        let hid := freshSyncHandleId tbl
        let entry : SyncProxyEntry fd :=
          { handleId := hid, port := boundPort, vcfg := vcfg,
            listenFd := lfd, wakeR := wakeR, wakeW := wakeW }
        set (setTable w { nextHandleId := hid + 1, entries := entry :: tbl.entries })
        return .ok { handleId := hid, port := boundPort }
    stopProxy := fun proxy => do
      let w ← get
      let tbl := getTable w
      match tbl.entries.find? (fun e => e.handleId == proxy.handleId) with
      | none =>
        return .error (Model.mapRawErrorPure (.invalidArgument none "proxy handle is not active"))
      | some entry =>
        set (setTable w { tbl with entries := tbl.entries.filter (fun e => e.handleId != proxy.handleId) })
        let finalEvents ← teardownAllSlotsListRef sys (fun _ => pure ()) entry.slots.toList entry.events
        refCloseSysFd sys entry.listenFd
        refCloseSysFd sys entry.wakeR
        refCloseSysFd sys entry.wakeW
        return .ok finalEvents
    activeProxyCount := do
      let w ← get
      return (getTable w).entries.length }

private def updatePollMinRemRef (nowMs : Nat) (cur? : Option Nat) (dl : Nat) : Option Nat :=
  let rem := dl - nowMs
  match cur? with
  | none => some rem
  | some prev => some (Nat.min prev rem)

private def buildPollBatchAuxRef {fd : Type}
    (nowMs : Nat)
    (slots : List (ClientSlot fd Unit))
    (reqs : Array (fd × Poll.PollEvents))
    (indices : Array (Option Nat × Option Nat))
    (minRem? : Option Nat) :
    Array (fd × Poll.PollEvents) × Array (Option Nat × Option Nat) × Option Nat :=
  match slots with
  | [] => (reqs, indices, minRem?)
  | slot :: rest =>
    match slot.phase with
    | .handshake cfd _ dl =>
      let cIdx := reqs.size
      buildPollBatchAuxRef nowMs rest
        (reqs.push (cfd, { pollin := true }))
        (indices.push (some cIdx, none))
        (updatePollMinRemRef nowMs minRem? dl)
    | .dns cfd _ _ () =>
      let cIdx := reqs.size
      buildPollBatchAuxRef nowMs rest (reqs.push (cfd, {})) (indices.push (some cIdx, none)) minRem?
    | .connecting cfd ufd _ _ _ _ _ dl =>
      let cIdx := reqs.size
      let reqs1 := reqs.push (cfd, {})
      let uIdx := reqs1.size
      buildPollBatchAuxRef nowMs rest
        (reqs1.push (ufd, { pollout := true }))
        (indices.push (some cIdx, some uIdx))
        (updatePollMinRemRef nowMs minRem? dl)
    | .relay st =>
      let (reqs1, cIdx?) :=
        match st.clientFd? with
        | some cfd =>
          let cev := refClientPollEvents st
          if !cev.isEmpty then (reqs.push (cfd, cev), some reqs.size) else (reqs, none)
        | none => (reqs, none)
      let (reqs2, uIdx?) :=
        match st.upstreamFd? with
        | some ufd =>
          let uev := refUpstreamPollEvents st
          if !uev.isEmpty then (reqs1.push (ufd, uev), some reqs1.size) else (reqs1, none)
        | none => (reqs1, none)
      buildPollBatchAuxRef nowMs rest reqs2 (indices.push (cIdx?, uIdx?)) minRem?
    | .closingReply cfd? _ _ shutWr _ dl =>
      match cfd? with
      | some cfd =>
        let cIdx := reqs.size
        let ev : Poll.PollEvents := if shutWr then { pollin := true } else { pollout := true }
        buildPollBatchAuxRef nowMs rest
          (reqs.push (cfd, ev))
          (indices.push (some cIdx, none))
          (updatePollMinRemRef nowMs minRem? dl)
      | none =>
        buildPollBatchAuxRef nowMs rest reqs (indices.push (none, none)) minRem?
    | .done =>
      buildPollBatchAuxRef nowMs rest reqs (indices.push (none, none)) minRem?

/-- Build the `ppoll` request array, per-slot index table, and optional relative timeout. -/
def refBuildPollBatchSync {fd : Type}
    (wakeR listenFd : fd) (maxTunnels nowMs : Nat) (slots : Array (ClientSlot fd Unit)) :
    Array (fd × Poll.PollEvents) × Array (Option Nat × Option Nat) × Option Poll.Timespec :=
  let listenEv : Poll.PollEvents := { pollin := decide (slots.size < maxTunnels) }
  let initReqs : Array (fd × Poll.PollEvents) := #[(wakeR, { pollin := true }), (listenFd, listenEv)]
  let (reqs, indices, minRem?) :=
    buildPollBatchAuxRef nowMs slots.toList initReqs (Array.emptyWithCapacity slots.size) none
  (reqs, indices, minRem?.map refMsToPollTimespec)

private def resolveDnsSyncRef {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (host : String) : m (Option (Except String (Array IpAddr))) := do
  match ← sys.dns.getaddrinfo host { family := .any, sockType := .stream } with
  | .error dnsErr =>
    let msg := if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message
    return some (.error msg)
  | .ok addrs =>
    return some (.ok (refFilterUnscopedDnsAddrs addrs))

private def stepSlotWithPollDnsRef {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (pollDns : m (Option (Except String (Array IpAddr))))
    (slot : ClientSlot fd Unit) (events : Array ConnectEvent)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat) :
    m (ClientSlot fd Unit × Array ConnectEvent) := do
  match slot.phase with
  | .handshake cfd headBuf dl =>
    refStepHandshake sys limits onHead onResolved (refStartDnsSync sys limits onResolved)
      slot events cfd headBuf dl cRev nowMs
  | .dns cfd host port () =>
    if cRev.pollerr || cRev.pollhup || cRev.pollnval then
      let (slot1, events1) :=
        refEmitSlotEvent slot events
          { host := some host, port := some port, outcome := .failed, reason := some "client disconnected" }
      refCloseSysFd sys cfd
      return ({ slot1 with phase := .done, pipelined := ByteArray.empty }, events1)
    else
      match ← pollDns with
      | none => return (slot, events)
      | some (.error msg) =>
        let (slot1, events1) :=
          refEmitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
        let slot2 ← refEnterClosingReply sys limits slot1 cfd 502
        return (slot2, events1)
      | some (.ok ips) =>
        refHandleResolveDecision sys limits onResolved slot events cfd host port ips
  | .connecting cfd ufd host port cands idx lastErr? dl =>
    refStepConnecting sys limits slot events cfd ufd host port cands idx lastErr? dl cRev uRev nowMs
  | .relay st =>
    let st' ← refStepBidirectionalRelay sys.net (refCloseSysFd sys) st cRev uRev
    if st'.isClosed then return ({ slot with phase := .done }, events)
    else return ({ slot with phase := .relay st' }, events)
  | .closingReply cfd? rb roff sw dr dl =>
    let slot' ← stepClosingReplyRef sys slot cfd? rb roff sw dr dl cRev nowMs
    return (slot', events)
  | .done => return (slot, events)

/-- Execute one synchronous client slot transition. -/
def refStepSyncSlot {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (slot : ClientSlot fd Unit) (events : Array ConnectEvent)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat) :
    m (ClientSlot fd Unit × Array ConnectEvent) :=
  let host := match slot.phase with | .dns _ h _ () => h | _ => ""
  stepSlotWithPollDnsRef sys limits onHead onResolved (resolveDnsSyncRef sys host) slot events cRev uRev nowMs

private def stepSlotsListSyncRef {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (indices : Array (Option Nat × Option Nat))
    (revents : Array Poll.PollEvents)
    (nowMs idx : Nat)
    (slots : List (ClientSlot fd Unit))
    (accSlots : Array (ClientSlot fd Unit))
    (accEvents : Array ConnectEvent) :
    m (Array (ClientSlot fd Unit) × Array ConnectEvent) := do
  match slots with
  | [] => pure (accSlots, accEvents)
  | slot :: rest =>
    let (cIdx?, uIdx?) := indices[idx]?.getD (none, none)
    let cRev : Poll.PollEvents := match cIdx? with | some ci => revents[ci]?.getD {} | none => {}
    let uRev : Poll.PollEvents := match uIdx? with | some ui => revents[ui]?.getD {} | none => {}
    let (slot', events') ←
      stepSlotWithPollDnsRef sys limits onHead onResolved (pure none) slot accEvents cRev uRev nowMs
    let accSlots' := if !slot'.isFinished then accSlots.push slot' else accSlots
    stepSlotsListSyncRef sys limits onHead onResolved indices revents nowMs (idx + 1) rest accSlots' events'

/-- Execute one synchronous server `ppoll` + wakeup-drain + slot-step + `acceptNewClients` tick. -/
def refPollAndStepTickSync {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (stopRequested : Bool) (wakeR listenFd : fd)
    (slots : Array (ClientSlot fd Unit)) (events : Array ConnectEvent) :
    m (PollTickOutcome fd Unit) := do
  let now0 ← refMonoNowMs sys
  let (reqs, indices, timeout?) := refBuildPollBatchSync wakeR listenFd limits.maxConcurrentTunnels now0 slots
  match ← sys.poll.ppoll reqs timeout? with
  | .error e =>
    if e == Errno.EINTR then return .retryEintr else return .stopOrFatal
  | .ok revents =>
    if (revents[0]?.getD ({} : Poll.PollEvents)).pollin then refDrainWakeSocket sys.net wakeR 64 else pure ()
    if stopRequested then
      return .stopOrFatal
    else
      let now1 ← refMonoNowMs sys
      let (nextSlots, nextEvents) ←
        stepSlotsListSyncRef sys limits onHead onResolved indices revents now1
          0 slots.toList (Array.emptyWithCapacity slots.size) events
      let acceptedSlots ←
        if (revents[1]?.getD ({} : Poll.PollEvents)).pollin then refAcceptNewClients sys limits listenFd now1 nextSlots
        else pure nextSlots
      return .stepped acceptedSlots nextEvents

/-- Spec-passing reference `SysBridgeTarget` built purely over `.Types` and `.Model`. -/
def refBridgeTarget : SysBridgeTarget :=
  { createListener := fun sys vcfg => refCreateListener sys vcfg
    handleCompleteHeadSync := fun sys limits onHead onResolved slot evs cfd head pipe =>
      refHandleCompleteHead sys limits onHead onResolved (refStartDnsSync sys limits onResolved)
        slot evs cfd head pipe
    acceptNewClients := fun sys limits lfd now slots => refAcceptNewClients sys limits lfd now slots
    listenPollinEnabled := fun cur maxT => decide (cur < maxT)
    buildPollBatchSync := fun wakeR lfd maxT nowMs slots => refBuildPollBatchSync wakeR lfd maxT nowMs slots
    stepHandshakeSync := fun sys limits onHead onResolved slot evs cfd hb dl rev now =>
      refStepHandshake sys limits onHead onResolved (refStartDnsSync sys limits onResolved)
        slot evs cfd hb dl rev now
    recvIntoRing := fun net fd fuel rb => refRecvIntoRing net fd fuel rb
    flushRingNonblock := fun net fd fuel rb => refFlushRingNonblock net fd fuel rb
    stepBidirectionalRelay := fun sys st cRev uRev =>
      refStepBidirectionalRelay sys.net (refCloseSysFd sys) st cRev uRev
    stepSlotSync := fun sys limits onHead onResolved slot evs cRev uRev nowMs =>
      refStepSyncSlot sys limits onHead onResolved slot evs cRev uRev nowMs
    pollAndStepTickSync := fun sys limits onHead onResolved stopFlag wakeR lfd slots evs =>
      refPollAndStepTickSync sys limits onHead onResolved stopFlag wakeR lfd slots evs
    mkRawOps := fun sys =>
      refMkSyncRawOps sys (fun wt => wt.1.proxyTable)
        (fun (w, tr) tbl => ({ w with proxyTable := tbl }, tr)) }

end LeanSwe.ConnectProxy.SpecMutants
