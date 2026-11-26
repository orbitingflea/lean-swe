import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.BridgeState
import LeanSwe.ConnectProxy.Model.HealthySys
import LeanSwe.ConnectProxy.SpecMutants.RefRelay

/-!
Pure spec-passing reference slot-transition helpers over `.Types` and `.Model`
for single-bug `ConnectProxy` specification mutants.
-/

namespace LeanSwe.ConnectProxy.SpecMutants

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Internal.Relay (RelayState)
open LeanSwe.ConnectProxy.Internal.SysBridge
  (MAX_EINTR_RETRIES MAX_HANDSHAKE_STEPS MAX_ACCEPT_BATCH
   dnsAddrToIpAddr? ipAddrToDialSockAddr CProxySysOpsM ClientSlot)

private def refHandshakeChunkMax : Nat := 8192
private def refClosingDrainMax : Nat := 65536
private def refClosingTimeoutMaxMs : Nat := 250
private def refMaxClosingSteps : Nat := 256

private def validateStartLimitsRef (vcfg : ValidProxyConfig) : Except ProxyError ValidProxyConfig :=
  let lim := vcfg.config.limits
  if lim.maxHeaderBytes == 0 || lim.headerTimeoutMs == 0 ||
     lim.connectTimeoutMs == 0 || lim.maxConcurrentTunnels == 0 then
    .error (Model.mapRawErrorPure (.invalidArgument none "proxy limits must be positive"))
  else
    .ok vcfg

private def classifyErrnoRef (port : UInt16) (e : Errno) : ConnectProxyRawError :=
  let detail := Errno.name e
  if e == Errno.EINVAL then .invalidArgument (some e) detail
  else if e == Errno.EADDRINUSE then .addressInUse port e detail
  else if e == Errno.EACCES || e == Errno.EPERM then .permissionDenied e detail
  else if e == Errno.EMFILE || e == Errno.ENFILE || e == Errno.ENOMEM ||
          e == Errno.ENOBUFS || e == Errno.EAGAIN then
    .resourceExhausted e detail
  else .otherError e detail

private def errnoToProxyErrorRef (port : UInt16) (e : Errno) : ProxyError :=
  Model.mapRawErrorPure (classifyErrnoRef port e)

/-- Filter `Dns.DnsAddr` records to unscoped IPv4/IPv6 `IpAddr` candidates. -/
def refFilterUnscopedDnsAddrs (addrs : List Dns.DnsAddr) : Array IpAddr :=
  (addrs.filterMap dnsAddrToIpAddr?).toArray

private def findCrlfCrlfAuxRef (bs : ByteArray) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, idx =>
    if idx + 3 < bs.size then
      if bs[idx]! == 13 && bs[idx + 1]! == 10 && bs[idx + 2]! == 13 && bs[idx + 3]! == 10 then
        some idx
      else findCrlfCrlfAuxRef bs fuel (idx + 1)
    else none

private def findCrlfCrlfRef (bs : ByteArray) (start : Nat := 0) : Option Nat :=
  if bs.size < 4 || start + 3 >= bs.size then none
  else findCrlfCrlfAuxRef bs (bs.size - start) start

private def closeSysFdAuxRef {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (d : fd) : Nat → m Unit
  | 0 => do let _ ← sys.files.close d
  | fuel + 1 => do
    match ← sys.files.close d with
    | .ok () => pure ()
    | .error e =>
      if e == Errno.EBUSY then
        let _ ← sys.timeRand.clock_nanosleep .monotonic false { sec := 0, nsec := 100000 }
        closeSysFdAuxRef sys d fuel
      else pure ()

/-- Close descriptor `d` via `sys.files.close` with bounded `EBUSY` retry. -/
def refCloseSysFd {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (d : fd) : m Unit :=
  closeSysFdAuxRef sys d 64

/-- Convert a non-negative `TimeRand.Timespec` reading to milliseconds. -/
def refTimespecToMs (ts : TimeRand.Timespec) : Nat :=
  ts.sec.toInt.toNat * 1000 + ts.nsec.toNat / 1000000

/-- Query `CLOCK_MONOTONIC` in milliseconds via `sys.timeRand`. -/
def refMonoNowMs {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) : m Nat := do
  match ← retryEintr (sys.timeRand.clock_gettime .monotonic) MAX_EINTR_RETRIES with
  | .ok ts => return refTimespecToMs ts
  | .error _ => return 0

/-- Drain all pending wakeup bytes from non-blocking `wakeR`. -/
def refDrainWakeSocket {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (wakeR : fd) : Nat → m Unit
  | 0 => pure ()
  | fuel + 1 => do
    match ← net.recvfrom wakeR 256 { dontwait := true } with
    | .ok bs => if bs.size == 0 then pure () else refDrainWakeSocket net wakeR fuel
    | .error e => if e == Errno.EINTR then refDrainWakeSocket net wakeR fuel else pure ()

/-- Validate limits, bind `127.0.0.1` loopback listener, resolve ephemeral port, and open wakeup `socketpair`. -/
def refCreateListener {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (vcfg : ValidProxyConfig) :
    m (Except ProxyError (fd × fd × fd × UInt16)) := do
  match validateStartLimitsRef vcfg with
  | .error err => return .error err
  | .ok _ =>
    let reqPort := vcfg.config.listenPort
    match ← retryEintr (sys.net.socket .inet .stream { nonblock := true, cloexec := true } 0) MAX_EINTR_RETRIES with
    | .error e => return .error (errnoToProxyErrorRef reqPort e)
    | .ok lfd =>
      match ← retryEintr (sys.net.setsockopt lfd .reuseAddr 1) MAX_EINTR_RETRIES with
      | .error e =>
        refCloseSysFd sys lfd
        return .error (errnoToProxyErrorRef reqPort e)
      | .ok () =>
        let bindAddr := Net.SockAddr.ipv4 Net.INADDR_LOOPBACK reqPort
        match ← retryEintr (sys.net.bind lfd bindAddr) MAX_EINTR_RETRIES with
        | .error e =>
          refCloseSysFd sys lfd
          return .error (errnoToProxyErrorRef reqPort e)
        | .ok () =>
          match ← retryEintr (sys.net.listen lfd 128) MAX_EINTR_RETRIES with
          | .error e =>
            refCloseSysFd sys lfd
            return .error (errnoToProxyErrorRef reqPort e)
          | .ok () =>
            match ← retryEintr (sys.net.getsockname lfd) MAX_EINTR_RETRIES with
            | .error e =>
              refCloseSysFd sys lfd
              return .error (errnoToProxyErrorRef reqPort e)
            | .ok boundSa =>
              let boundPort? : Option UInt16 :=
                match boundSa with
                | .ipv4 ip p =>
                  if ip == Net.INADDR_LOOPBACK && p != 0 && (reqPort == 0 || p == reqPort) then some p
                  else none
                | _ => none
              match boundPort? with
              | none =>
                refCloseSysFd sys lfd
                return .error (Model.mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port"))
              | some boundPort =>
                match ← retryEintr (sys.net.socketpair .unix .stream { nonblock := true, cloexec := true }) MAX_EINTR_RETRIES with
                | .error e =>
                  refCloseSysFd sys lfd
                  return .error (errnoToProxyErrorRef reqPort e)
                | .ok (wakeR, wakeW) =>
                  return .ok (lfd, wakeR, wakeW, boundPort)

/-- Record `ev` at most once for `slot`. -/
def refEmitSlotEvent {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent) (ev : ConnectEvent) :
    ClientSlot fd dnsJob × Array ConnectEvent :=
  if slot.eventEmitted then (slot, events)
  else ({ slot with eventEmitted := true }, events.push ev)

/-- Transition `slot` into `CLOSING_REPLY`. -/
def refEnterClosingReply {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob) (clientFd : fd) (statusCode : Nat) :
    m (ClientSlot fd dnsJob) := do
  let replyBytes :=
    if statusCode == 403 then refReply403Bytes
    else if statusCode == 503 then refReply503Bytes
    else refReply502Bytes
  let now ← refMonoNowMs sys
  let deadlineMs := now + Nat.min limits.headerTimeoutMs refClosingTimeoutMaxMs
  let slotCleared := { slot with pipelined := ByteArray.empty }
  match ← refFlushBytesNonblock sys.net clientFd replyBytes refMaxClosingSteps 0 with
  | none =>
    refCloseSysFd sys clientFd
    return { slotCleared with phase := .done }
  | some sentOff =>
    if sentOff >= replyBytes.size then
      if ← refShutdownWrClean sys.net clientFd 16 then
        return { slotCleared with phase := .closingReply (some clientFd) replyBytes sentOff true 0 deadlineMs }
      else
        refCloseSysFd sys clientFd
        return { slotCleared with phase := .done }
    else
      return { slotCleared with phase := .closingReply (some clientFd) replyBytes sentOff false 0 deadlineMs }

/-- Transition an authorized connected pair into `SLOT_RELAY`. -/
def refEnterRelay {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd upstreamFd : fd) (host : String) (port : UInt16) :
    ClientSlot fd dnsJob × Array ConnectEvent :=
  let (slot1, events1) :=
    refEmitSlotEvent slot events { host := some host, port := some port, outcome := .allowed, reason := none }
  let relaySt := RelayState.init clientFd upstreamFd slot1.pipelined
  ({ slot1 with phase := .relay relaySt, pipelined := ByteArray.empty }, events1)

private def startNextConnectAuxRef {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd : fd) (host : String) (port : UInt16) (candidates : Array IpAddr) :
    Nat → Nat → Option Errno → m (ClientSlot fd dnsJob × Array ConnectEvent)
  | 0, _, lastErr? => do
    let msg := match lastErr? with | some e => Errno.name e | none => "upstream connect failed"
    let (slot1, events1) :=
      refEmitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
    let slot2 ← refEnterClosingReply sys limits slot1 clientFd 502
    return (slot2, events1)
  | fuel + 1, candIdx, lastErr? => do
    if h : candIdx < candidates.size then
      let ip := candidates[candIdx]'h
      let sa := ipAddrToDialSockAddr ip port
      match ← retryEintr (sys.net.socket sa.domain .stream { nonblock := true, cloexec := true } 0) MAX_EINTR_RETRIES with
      | .error e =>
        startNextConnectAuxRef sys limits slot events clientFd host port candidates fuel (candIdx + 1) (some e)
      | .ok ufd =>
        match ← sys.net.connect ufd sa with
        | .ok () => return refEnterRelay slot events clientFd ufd host port
        | .error e =>
          if e == Errno.EINPROGRESS || e == Errno.EINTR then
            let now ← refMonoNowMs sys
            let deadline := now + limits.connectTimeoutMs
            return ({ slot with
              phase := .connecting clientFd ufd host port candidates (candIdx + 1) lastErr? deadline }, events)
          else
            refCloseSysFd sys ufd
            startNextConnectAuxRef sys limits slot events clientFd host port candidates fuel (candIdx + 1) (some e)
    else
      let msg := match lastErr? with | some e => Errno.name e | none => "upstream connect failed"
      let (slot1, events1) :=
        refEmitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
      let slot2 ← refEnterClosingReply sys limits slot1 clientFd 502
      return (slot2, events1)

/-- Start dialing verified `candidates` from index `candIdx`. -/
def refStartNextConnect {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd : fd) (host : String) (port : UInt16) (candidates : Array IpAddr)
    (candIdx : Nat := 0) (lastErr? : Option Errno := none) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) :=
  startNextConnectAuxRef sys limits slot events clientFd host port candidates
    (candidates.size - candIdx) candIdx lastErr?

/-- Evaluate Stage-2 `onResolved` on `ips`. -/
def refHandleResolveDecision {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd : fd) (host : String) (port : UInt16) (ips : Array IpAddr) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  match onResolved host port ips with
  | .deny reason =>
    let msg := if reason.isEmpty then "resolved IP denied" else reason
    let (slot1, events1) :=
      refEmitSlotEvent slot events { host := some host, port := some port, outcome := .denied, reason := some msg }
    let slot2 ← refEnterClosingReply sys limits slot1 clientFd 403
    return (slot2, events1)
  | .dial primary fallbacks =>
    refStartNextConnect sys limits slot events clientFd host port (#[primary] ++ fallbacks) 0 none

/-- Evaluate Stage-1 `onHead` on `headBytes`. -/
def refHandleCompleteHead {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd : fd) (headBytes pipelined : ByteArray) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  let slotWithPipe := { slot with pipelined := pipelined }
  match onHead headBytes with
  | .deny host? port? reason =>
    let msg := if reason.isEmpty then "request denied" else reason
    let (slot1, events1) :=
      refEmitSlotEvent slotWithPipe events { host := host?, port := port?, outcome := .denied, reason := some msg }
    let slot2 ← refEnterClosingReply sys limits slot1 clientFd 403
    return (slot2, events1)
  | .needResolve host port litIp? =>
    let slotTargeted := { slotWithPipe with target? := some (host, port) }
    match litIp? with
    | some litIp =>
      refHandleResolveDecision sys limits onResolved slotTargeted events clientFd host port #[litIp]
    | none =>
      startDns slotTargeted events clientFd host port

private def stepHandshakeReadAuxRef {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd : fd) (deadlineMs : Nat) :
    Nat → ByteArray → m (ClientSlot fd dnsJob × Array ConnectEvent)
  | 0, headBuf =>
    pure ({ slot with phase := .handshake clientFd headBuf deadlineMs }, events)
  | fuel + 1, headBuf => do
    let maxHead := limits.maxHeaderBytes
    if headBuf.size >= maxHead then
      let (slot1, events1) :=
        refEmitSlotEvent slot events { outcome := .denied, reason := some "request head exceeds maxHeaderBytes" }
      let slot2 ← refEnterClosingReply sys limits slot1 clientFd 403
      return (slot2, events1)
    else
      let want := UInt32.ofNat (Nat.min (maxHead - headBuf.size) refHandshakeChunkMax)
      match ← sys.net.recvfrom clientFd want { dontwait := true } with
      | .ok chunk =>
        if chunk.size == 0 then
          let (slot1, events1) :=
            refEmitSlotEvent slot events
              { outcome := .denied, reason := some "client closed before completing CONNECT headers" }
          let slot2 ← refEnterClosingReply sys limits slot1 clientFd 403
          return (slot2, events1)
        else
          let takeN := Nat.min chunk.size want.toNat
          let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
          let scanFrom := headBuf.size - 3
          let nextBuf := if headBuf.size == 0 then part else headBuf ++ part
          match findCrlfCrlfRef nextBuf scanFrom with
          | some pos =>
            let headEnd := pos + 4
            let headBytes := nextBuf.extract 0 headEnd
            let pipelined :=
              if headEnd >= nextBuf.size then ByteArray.empty else nextBuf.extract headEnd nextBuf.size
            refHandleCompleteHead sys limits onHead onResolved startDns slot events clientFd headBytes pipelined
          | none =>
            if nextBuf.size >= maxHead then
              let (slot1, events1) :=
                refEmitSlotEvent slot events { outcome := .denied, reason := some "request head exceeds maxHeaderBytes" }
              let slot2 ← refEnterClosingReply sys limits slot1 clientFd 403
              return (slot2, events1)
            else
              stepHandshakeReadAuxRef sys limits onHead onResolved startDns slot events clientFd deadlineMs fuel nextBuf
      | .error e =>
        if e == Errno.EINTR then
          stepHandshakeReadAuxRef sys limits onHead onResolved startDns slot events clientFd deadlineMs fuel headBuf
        else if e == Errno.EAGAIN then
          return ({ slot with phase := .handshake clientFd headBuf deadlineMs }, events)
        else
          let (slot1, events1) :=
            refEmitSlotEvent slot events { outcome := .denied, reason := some (Errno.name e) }
          let slot2 ← refEnterClosingReply sys limits slot1 clientFd 403
          return (slot2, events1)

/-- Advance one poll tick for a `.handshake` slot. -/
def refStepHandshake {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd : fd) (headBuf : ByteArray) (deadlineMs : Nat)
    (cRev : Poll.PollEvents) (nowMs : Nat) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  let (slot1, events1) ←
    if cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval then
      stepHandshakeReadAuxRef sys limits onHead onResolved startDns slot events clientFd deadlineMs
        MAX_HANDSHAKE_STEPS headBuf
    else pure (slot, events)
  match slot1.phase with
  | .handshake cfd _ dl =>
    if nowMs >= dl then
      let (slot2, events2) :=
        refEmitSlotEvent slot1 events1 { outcome := .denied, reason := some "header timeout" }
      let slot3 ← refEnterClosingReply sys limits slot2 cfd 403
      return (slot3, events2)
    else return (slot1, events1)
  | _ => return (slot1, events1)

/-- Advance one poll tick for a `.connecting` slot. -/
def refStepConnecting {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd) (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent)
    (clientFd upstreamFd : fd) (host : String) (port : UInt16)
    (candidates : Array IpAddr) (candIdx : Nat) (_lastErrno? : Option Errno) (deadlineMs : Nat)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  if cRev.pollerr || cRev.pollhup || cRev.pollnval then
    let (slot1, events1) :=
      refEmitSlotEvent slot events
        { host := some host, port := some port, outcome := .failed, reason := some "client disconnected" }
    refCloseSysFd sys upstreamFd
    refCloseSysFd sys clientFd
    return ({ slot1 with phase := .done, pipelined := ByteArray.empty }, events1)
  else if uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval then
    let soErr : Errno ← do
      match ← retryEintr (sys.net.getsockopt upstreamFd .error) MAX_EINTR_RETRIES with
      | .ok code => pure code
      | .error e => pure e
    if soErr == 0 && uRev.pollout && !uRev.pollerr && !uRev.pollnval then
      return refEnterRelay slot events clientFd upstreamFd host port
    else
      let recErr := if soErr != 0 then soErr else Errno.ECONNREFUSED
      refCloseSysFd sys upstreamFd
      refStartNextConnect sys limits slot events clientFd host port candidates candIdx (some recErr)
  else if nowMs >= deadlineMs then
    refCloseSysFd sys upstreamFd
    refStartNextConnect sys limits slot events clientFd host port candidates candIdx (some Errno.ETIMEDOUT)
  else return (slot, events)

private def drainClosingClientRef {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (clientFd : fd) : Nat → Nat → m (Option Nat)
  | 0, drained => pure (some drained)
  | fuel + 1, drained => do
    match ← net.recvfrom clientFd 1024 { dontwait := true } with
    | .ok bs =>
      if bs.size == 0 then return none
      else
        let drained' := drained + bs.size
        if drained' >= refClosingDrainMax then return none
        else drainClosingClientRef net clientFd fuel drained'
    | .error e =>
      if e == Errno.EINTR then drainClosingClientRef net clientFd fuel drained
      else if e == Errno.EAGAIN then return some drained
      else return none

/-- Flush pending error reply bytes and `SHUT_WR` for a `.closingReply` slot. -/
def refClosingSendStep {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (cfd : fd) (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool)
    (cRev : Poll.PollEvents) : m (Option (Nat × Bool)) := do
  if !shutWr then
    if cRev.pollerr || cRev.pollhup || cRev.pollnval then return none
    else if cRev.pollout then
      match ← refFlushBytesNonblock net cfd replyBytes refMaxClosingSteps replyOff with
      | none => return none
      | some nextOff =>
        if nextOff >= replyBytes.size then
          if ← refShutdownWrClean net cfd 16 then return some (nextOff, true)
          else return none
        else return some (nextOff, false)
    else return some (replyOff, false)
  else return some (replyOff, true)

/-- Drain residual client request bytes after `SHUT_WR` for a `.closingReply` slot. -/
def refClosingDrainStep {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (cfd : fd) (shut1 : Bool) (drained : Nat)
    (cRev : Poll.PollEvents) : m (Option Nat) := do
  if shut1 && (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) then
    drainClosingClientRef net cfd refMaxClosingSteps drained
  else return some drained

end LeanSwe.ConnectProxy.SpecMutants
