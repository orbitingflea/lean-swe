import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.Dns.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.BridgeState
import LeanSwe.ConnectProxy.Model.HealthySys
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface
import LeanSwe.ConnectProxy.Relay

namespace LeanSwe.ConnectProxy.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model


export LeanSwe.ConnectProxy.Internal.SysBridge
  (MAX_EINTR_RETRIES MAX_HANDSHAKE_STEPS MAX_ACCEPT_BATCH
   dnsAddrToIpAddr? isIpv4MappedV6 ipAddrToDialSockAddr effectiveDialIp
   CProxySysOpsM SlotPhase ClientSlot SyncProxyEntry SyncProxyTable
   freshSyncHandleId PollTickOutcome SysAuditTrace liftTraceOp instrumentSysOps)

export LeanSwe.ConnectProxy.Internal.HealthySys
  (HealthySysWorld RefinesHealthyCProxySysAt RefinesHealthyCProxySys
   slotOpenFds SysBridgeTarget)

namespace ClientSlot
export LeanSwe.ConnectProxy.Internal.SysBridge.ClientSlot (isFinished)
end ClientSlot

namespace SlotPhase
export LeanSwe.ConnectProxy.Internal.SysBridge.SlotPhase (handshake dns connecting relay closingReply done)
end SlotPhase

namespace PollTickOutcome
export LeanSwe.ConnectProxy.Internal.SysBridge.PollTickOutcome (retryEintr stopOrFatal stepped)
end PollTickOutcome

namespace SysAuditTrace
export LeanSwe.ConnectProxy.Internal.SysBridge.SysAuditTrace
  (openedFds closedFds boundAddrs dnsQueries dialedAddrs recvBytes sentBytes netErrs sawZeroSend pollOutcomes)
end SysAuditTrace

namespace HealthySysWorld
export LeanSwe.ConnectProxy.Internal.HealthySys.HealthySysWorld (wf)
end HealthySysWorld

/-- Per-call byte cap when reading HTTP `CONNECT` request headers. -/
def HANDSHAKE_CHUNK_MAX : Nat := 8192

/-- Maximum unread request body bytes drained on `403`/`502` before closing (`64 KiB`). -/
def CLOSING_DRAIN_MAX : Nat := 65536

/-- Maximum drain duration in milliseconds on `403`/`502` replies before closing (`250 ms`). -/
def CLOSING_TIMEOUT_MAX_MS : Nat := 250

/-- Per-poll-tick I/O iteration bound during `CLOSING_REPLY` flush/drain. -/
def MAX_CLOSING_STEPS : Nat := 256

/-- Structural poll-loop fuel bound (`2^64`, ensuring total termination). -/
def LOOP_FUEL : Nat := UInt64.size

/-- Validate that all four `ProxyLimits` fields in `vcfg` are strictly positive. -/
def validateStartLimits (vcfg : ValidProxyConfig) : Except ProxyError ValidProxyConfig :=
  let lim := vcfg.config.limits
  if lim.maxHeaderBytes == 0 || lim.headerTimeoutMs == 0 ||
     lim.connectTimeoutMs == 0 || lim.maxConcurrentTunnels == 0 then
    .error (Model.mapRawErrorPure (.invalidArgument none "proxy limits must be positive"))
  else
    .ok vcfg

/-- Classify a Linux `Errno` into a `ConnectProxyRawError` with non-empty diagnostic detail. -/
def classifyErrno (port : UInt16) (e : Errno) : ConnectProxyRawError :=
  let detail := Errno.name e
  if e == Errno.EINVAL then
    .invalidArgument (some e) detail
  else if e == Errno.EADDRINUSE then
    .addressInUse port e detail
  else if e == Errno.EACCES || e == Errno.EPERM then
    .permissionDenied e detail
  else if e == Errno.EMFILE || e == Errno.ENFILE || e == Errno.ENOMEM ||
          e == Errno.ENOBUFS || e == Errno.EAGAIN then
    .resourceExhausted e detail
  else
    .otherError e detail

/-- Map a Linux `Errno` on `port` directly to a normalized `ProxyError`. -/
def errnoToProxyError (port : UInt16) (e : Errno) : ProxyError :=
  Model.mapRawErrorPure (classifyErrno port e)

/-- Filter `Dns.DnsAddr` records to unscoped IPv4/IPv6 `IpAddr` candidates in resolver order. -/
def filterUnscopedDnsAddrs (addrs : List Dns.DnsAddr) : Array IpAddr :=
  (addrs.filterMap dnsAddrToIpAddr?).toArray

/-- Tail-recursive `\r\n\r\n` scanner starting at byte offset `idx`. -/
def findCrlfCrlfAux (bs : ByteArray) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, idx =>
    if idx + 3 < bs.size then
      if bs[idx]! == 13 && bs[idx + 1]! == 10 && bs[idx + 2]! == 13 && bs[idx + 3]! == 10 then
        some idx
      else
        findCrlfCrlfAux bs fuel (idx + 1)
    else
      none

/-- Find the starting offset of the first `\r\n\r\n` sequence at or after `start` in `bs`. -/
def findCrlfCrlf (bs : ByteArray) (start : Nat := 0) : Option Nat :=
  if bs.size < 4 || start + 3 >= bs.size then
    none
  else
    findCrlfCrlfAux bs (bs.size - start) start

/-- Close descriptor `d` via `sys.files.close`, retrying briefly only on transient `EBUSY` pin contention. -/
def closeSysFdAux {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (d : fd) : Nat → m Unit
  | 0 => do
    let _ ← sys.files.close d
  | fuel + 1 => do
    match ← sys.files.close d with
    | .ok () => pure ()
    | .error e =>
      if e == Errno.EBUSY then
        let _ ← sys.timeRand.clock_nanosleep .monotonic false { sec := 0, nsec := 100000 }
        closeSysFdAux sys d fuel
      else
        pure ()

end LeanSwe.ConnectProxy.SysBridge

namespace LeanSwe.ConnectProxy.Internal.SysBridge

/-- Deterministically close descriptor `d` in the OS file descriptor table via `sys.files.close`. -/
def CProxySysOpsM.closeFd {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (d : fd) : m Unit :=
  LeanSwe.ConnectProxy.SysBridge.closeSysFdAux sys d 64

end LeanSwe.ConnectProxy.Internal.SysBridge

namespace LeanSwe.ConnectProxy.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model

namespace CProxySysOpsM
export LeanSwe.ConnectProxy.Internal.SysBridge.CProxySysOpsM (closeFd)
end CProxySysOpsM

/-- Query `CLOCK_MONOTONIC` in milliseconds via `sys.timeRand`, falling back to `0` on unexpected error. -/
def monoNowMs {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) : m Nat := do
  match ← retryEintr (sys.timeRand.clock_gettime .monotonic) MAX_EINTR_RETRIES with
  | .ok ts => return TimeRand.timespecToMs ts
  | .error _ => return 0

/-- Drain all pending wakeup bytes from non-blocking `wakeR`. -/
def drainWakeSocket {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (wakeR : fd) : Nat → m Unit
  | 0 => pure ()
  | fuel + 1 => do
    match ← net.recvfrom wakeR 256 { dontwait := true } with
    | .ok bs =>
      if bs.size == 0 then pure () else drainWakeSocket net wakeR fuel
    | .error e =>
      if e == Errno.EINTR then drainWakeSocket net wakeR fuel else pure ()

/-- Validate limits, bind a `127.0.0.1` loopback listener (`SO_REUSEADDR`, backlog `128`), resolve ephemeral `listenPort = 0`, and create the wakeup `socketpair`. -/
def createListener {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (vcfg : ValidProxyConfig) :
    m (Except ProxyError (fd × fd × fd × UInt16)) := do
  match validateStartLimits vcfg with
  | .error err => return .error err
  | .ok _ =>
    let reqPort := vcfg.config.listenPort
    match ← retryEintr
        (sys.net.socket .inet .stream { nonblock := true, cloexec := true } 0) MAX_EINTR_RETRIES with
    | .error e => return .error (errnoToProxyError reqPort e)
    | .ok lfd =>
      match ← retryEintr (sys.net.setsockopt lfd .reuseAddr 1) MAX_EINTR_RETRIES with
      | .error e =>
        sys.closeFd lfd
        return .error (errnoToProxyError reqPort e)
      | .ok () =>
        let bindAddr := Net.SockAddr.ipv4 Net.INADDR_LOOPBACK reqPort
        match ← retryEintr (sys.net.bind lfd bindAddr) MAX_EINTR_RETRIES with
        | .error e =>
          sys.closeFd lfd
          return .error (errnoToProxyError reqPort e)
        | .ok () =>
          match ← retryEintr (sys.net.listen lfd 128) MAX_EINTR_RETRIES with
          | .error e =>
            sys.closeFd lfd
            return .error (errnoToProxyError reqPort e)
          | .ok () =>
            match ← retryEintr (sys.net.getsockname lfd) MAX_EINTR_RETRIES with
            | .error e =>
              sys.closeFd lfd
              return .error (errnoToProxyError reqPort e)
            | .ok boundSa =>
              let boundPort? : Option UInt16 :=
                match boundSa with
                | .ipv4 ip p =>
                  if ip == Net.INADDR_LOOPBACK && p != 0 && (reqPort == 0 || p == reqPort) then
                    some p
                  else
                    none
                | _ => none
              match boundPort? with
              | none =>
                sys.closeFd lfd
                return .error (Model.mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port"))
              | some boundPort =>
                match ← retryEintr
                    (sys.net.socketpair .unix .stream { nonblock := true, cloexec := true }) MAX_EINTR_RETRIES with
                | .error e =>
                  sys.closeFd lfd
                  return .error (errnoToProxyError reqPort e)
                | .ok (wakeR, wakeW) =>
                  return .ok (lfd, wakeR, wakeW, boundPort)

/-- Record `ev` at most once for `slot`, setting `slot.eventEmitted = true`. -/
def emitSlotEvent {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (ev : ConnectEvent) : ClientSlot fd dnsJob × Array ConnectEvent :=
  if slot.eventEmitted then
    (slot, events)
  else
    ({ slot with eventEmitted := true }, events.push ev)

/-- Transition `slot` (with open `clientFd`) into `CLOSING_REPLY` (`403`, `502`, or `503`), immediately attempting a non-blocking flush and `SHUT_WR`. -/
def enterClosingReply {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob)
    (clientFd : fd)
    (statusCode : Nat) : m (ClientSlot fd dnsJob) := do
  let replyBytes :=
    if statusCode == 403 then Relay.reply403Bytes
    else if statusCode == 503 then Relay.reply503Bytes
    else Relay.reply502Bytes
  let now ← monoNowMs sys
  let closeMs := Nat.min limits.headerTimeoutMs CLOSING_TIMEOUT_MAX_MS
  let deadlineMs := now + closeMs
  let slotCleared := { slot with pipelined := ByteArray.empty }
  match ← NetRelay.flushBytesNonblock sys.net clientFd replyBytes MAX_CLOSING_STEPS 0 with
  | none =>
    sys.closeFd clientFd
    return { slotCleared with phase := .done }
  | some sentOff =>
    if sentOff >= replyBytes.size then
      if ← NetRelay.shutdownWrClean sys.net clientFd 16 then
        return { slotCleared with
          phase := .closingReply (some clientFd) replyBytes sentOff true 0 deadlineMs }
      else
        sys.closeFd clientFd
        return { slotCleared with phase := .done }
    else
      return { slotCleared with
        phase := .closingReply (some clientFd) replyBytes sentOff false 0 deadlineMs }

/-- Transition an authorized connected `(clientFd, upstreamFd)` pair into `SLOT_RELAY` and emit `.allowed`. -/
def enterRelay {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd upstreamFd : fd)
    (host : String) (port : UInt16) : ClientSlot fd dnsJob × Array ConnectEvent :=
  let (slot1, events1) :=
    emitSlotEvent slot events { host := some host, port := some port, outcome := .allowed, reason := none }
  let relaySt := Relay.RelayState.init clientFd upstreamFd slot1.pipelined
  ({ slot1 with phase := .relay relaySt, pipelined := ByteArray.empty }, events1)

/-- Step sequentially through `candidates[candIdx..]`, dialing each verified `IpAddr` via `ipAddrToDialSockAddr`. -/
def startNextConnectAux {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd : fd)
    (host : String) (port : UInt16)
    (candidates : Array IpAddr) :
    Nat → Nat → Option Errno → m (ClientSlot fd dnsJob × Array ConnectEvent)
  | 0, _, lastErr? => do
    let msg := match lastErr? with
      | some e => Errno.name e
      | none => "upstream connect failed"
    let (slot1, events1) :=
      emitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
    let slot2 ← enterClosingReply sys limits slot1 clientFd 502
    return (slot2, events1)
  | fuel + 1, candIdx, lastErr? => do
    if h : candIdx < candidates.size then
      let ip := candidates[candIdx]'h
      let sa := ipAddrToDialSockAddr ip port
      match ← retryEintr
          (sys.net.socket sa.domain .stream { nonblock := true, cloexec := true } 0) MAX_EINTR_RETRIES with
      | .error e =>
        startNextConnectAux sys limits slot events clientFd host port candidates fuel (candIdx + 1) (some e)
      | .ok ufd =>
        match ← sys.net.connect ufd sa with
        | .ok () =>
          return enterRelay slot events clientFd ufd host port
        | .error e =>
          if e == Errno.EINPROGRESS || e == Errno.EINTR then
            let now ← monoNowMs sys
            let deadline := now + limits.connectTimeoutMs
            return ({ slot with
              phase := .connecting clientFd ufd host port candidates (candIdx + 1) lastErr? deadline }, events)
          else
            sys.closeFd ufd
            startNextConnectAux sys limits slot events clientFd host port candidates fuel (candIdx + 1) (some e)
    else
      let msg := match lastErr? with
        | some e => Errno.name e
        | none => "upstream connect failed"
      let (slot1, events1) :=
        emitSlotEvent slot events { host := some host, port := some port, outcome := .failed, reason := some msg }
      let slot2 ← enterClosingReply sys limits slot1 clientFd 502
      return (slot2, events1)

/-- Start dialing verified `candidates` from index `candIdx`. -/
def startNextConnect {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd : fd)
    (host : String) (port : UInt16)
    (candidates : Array IpAddr)
    (candIdx : Nat := 0)
    (lastErr? : Option Errno := none) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) :=
  startNextConnectAux sys limits slot events clientFd host port candidates
    (candidates.size - candIdx) candIdx lastErr?

/-- Evaluate Stage-2 `onResolved` on `ips` and either deny (`403`) or dial the verified `primaryIp :: fallbackIps` snapshot. -/
def handleResolveDecision {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd : fd)
    (host : String) (port : UInt16)
    (ips : Array IpAddr) : m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  match onResolved host port ips with
  | .deny reason =>
    let msg := if reason.isEmpty then "resolved IP denied" else reason
    let (slot1, events1) :=
      emitSlotEvent slot events { host := some host, port := some port, outcome := .denied, reason := some msg }
    let slot2 ← enterClosingReply sys limits slot1 clientFd 403
    return (slot2, events1)
  | .dial primary fallbacks =>
    let cands := #[primary] ++ fallbacks
    startNextConnect sys limits slot events clientFd host port cands 0 none

/-- Evaluate Stage-1 `onHead` on `headBytes`: refuse immediately (`403`), dial literal IP directly without DNS, or invoke `startDns` for domain targets. -/
def handleCompleteHead {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd : fd)
    (headBytes pipelined : ByteArray) : m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  let slotWithPipe := { slot with pipelined := pipelined }
  match onHead headBytes with
  | .deny host? port? reason =>
    let msg := if reason.isEmpty then "request denied" else reason
    let (slot1, events1) :=
      emitSlotEvent slotWithPipe events { host := host?, port := port?, outcome := .denied, reason := some msg }
    let slot2 ← enterClosingReply sys limits slot1 clientFd 403
    return (slot2, events1)
  | .needResolve host port litIp? =>
    let slotTargeted := { slotWithPipe with target? := some (host, port) }
    match litIp? with
    | some litIp =>
      handleResolveDecision sys limits onResolved slotTargeted events clientFd host port #[litIp]
    | none =>
      startDns slotTargeted events clientFd host port

/-- Non-blocking handshake reader accumulating up to `maxHeaderBytes` and splitting on `\r\n\r\n`. -/
def stepHandshakeReadAux {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd : fd)
    (deadlineMs : Nat) :
    Nat → ByteArray → m (ClientSlot fd dnsJob × Array ConnectEvent)
  | 0, headBuf =>
    pure ({ slot with phase := .handshake clientFd headBuf deadlineMs }, events)
  | fuel + 1, headBuf => do
    let maxHead := limits.maxHeaderBytes
    if headBuf.size >= maxHead then
      let (slot1, events1) :=
        emitSlotEvent slot events { outcome := .denied, reason := some "request head exceeds maxHeaderBytes" }
      let slot2 ← enterClosingReply sys limits slot1 clientFd 403
      return (slot2, events1)
    else
      let rem := maxHead - headBuf.size
      let want := UInt32.ofNat (Nat.min rem HANDSHAKE_CHUNK_MAX)
      match ← sys.net.recvfrom clientFd want { dontwait := true } with
      | .ok chunk =>
        if chunk.size == 0 then
          let (slot1, events1) :=
            emitSlotEvent slot events
              { outcome := .denied, reason := some "client closed before completing CONNECT headers" }
          let slot2 ← enterClosingReply sys limits slot1 clientFd 403
          return (slot2, events1)
        else
          let takeN := Nat.min chunk.size want.toNat
          let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
          let scanFrom := headBuf.size - 3
          let nextBuf := if headBuf.size == 0 then part else headBuf ++ part
          match findCrlfCrlf nextBuf scanFrom with
          | some pos =>
            let headEnd := pos + 4
            let headBytes := nextBuf.extract 0 headEnd
            let pipelined :=
              if headEnd >= nextBuf.size then ByteArray.empty
              else nextBuf.extract headEnd nextBuf.size
            handleCompleteHead sys limits onHead onResolved startDns slot events clientFd headBytes pipelined
          | none =>
            if nextBuf.size >= maxHead then
              let (slot1, events1) :=
                emitSlotEvent slot events { outcome := .denied, reason := some "request head exceeds maxHeaderBytes" }
              let slot2 ← enterClosingReply sys limits slot1 clientFd 403
              return (slot2, events1)
            else
              stepHandshakeReadAux sys limits onHead onResolved startDns slot events clientFd deadlineMs fuel nextBuf
      | .error e =>
        if e == Errno.EINTR then
          stepHandshakeReadAux sys limits onHead onResolved startDns slot events clientFd deadlineMs fuel headBuf
        else if e == Errno.EAGAIN then
          return ({ slot with phase := .handshake clientFd headBuf deadlineMs }, events)
        else
          let (slot1, events1) :=
            emitSlotEvent slot events { outcome := .denied, reason := some (Errno.name e) }
          let slot2 ← enterClosingReply sys limits slot1 clientFd 403
          return (slot2, events1)

/-- Advance one poll tick for a `.handshake` slot, checking readability followed by `headerTimeoutMs` deadline. -/
def stepHandshake {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fd dnsJob → Array ConnectEvent → fd → String → UInt16 →
      m (ClientSlot fd dnsJob × Array ConnectEvent))
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd : fd) (headBuf : ByteArray) (deadlineMs : Nat)
    (cRev : Poll.PollEvents) (nowMs : Nat) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  let (slot1, events1) ←
    if cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval then
      stepHandshakeReadAux sys limits onHead onResolved startDns slot events clientFd deadlineMs
        MAX_HANDSHAKE_STEPS headBuf
    else
      pure (slot, events)
  match slot1.phase with
  | .handshake cfd _ dl =>
    if nowMs >= dl then
      let (slot2, events2) :=
        emitSlotEvent slot1 events1 { outcome := .denied, reason := some "header timeout" }
      let slot3 ← enterClosingReply sys limits slot2 cfd 403
      return (slot3, events2)
    else
      return (slot1, events1)
  | _ => return (slot1, events1)

/-- Advance one poll tick for a `.connecting` slot (`SO_ERROR` completion, fallback on failure, or `connectTimeoutMs` expiry). -/
def stepConnecting {m : Type → Type} [Monad m] {fd dnsJob : Type}
    (sys : CProxySysOpsM m fd)
    (limits : ProxyLimits)
    (slot : ClientSlot fd dnsJob)
    (events : Array ConnectEvent)
    (clientFd upstreamFd : fd)
    (host : String) (port : UInt16)
    (candidates : Array IpAddr) (candIdx : Nat) (_lastErrno? : Option Errno) (deadlineMs : Nat)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat) :
    m (ClientSlot fd dnsJob × Array ConnectEvent) := do
  if cRev.pollerr || cRev.pollhup || cRev.pollnval then
    let (slot1, events1) :=
      emitSlotEvent slot events
        { host := some host, port := some port, outcome := .failed, reason := some "client disconnected" }
    sys.closeFd upstreamFd
    sys.closeFd clientFd
    return ({ slot1 with phase := .done, pipelined := ByteArray.empty }, events1)
  else if uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval then
    let soErr : Errno ← do
      match ← retryEintr (sys.net.getsockopt upstreamFd .error) MAX_EINTR_RETRIES with
      | .ok code => pure code
      | .error e => pure e
    if soErr == 0 && uRev.pollout && !uRev.pollerr && !uRev.pollnval then
      return enterRelay slot events clientFd upstreamFd host port
    else
      let recErr := if soErr != 0 then soErr else Errno.ECONNREFUSED
      sys.closeFd upstreamFd
      startNextConnect sys limits slot events clientFd host port candidates candIdx (some recErr)
  else if nowMs >= deadlineMs then
    sys.closeFd upstreamFd
    startNextConnect sys limits slot events clientFd host port candidates candIdx (some Errno.ETIMEDOUT)
  else
    return (slot, events)

/-- Drain up to `CLOSING_DRAIN_MAX` bytes from `clientFd` after `SHUT_WR`. -/
def drainClosingClient {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (clientFd : fd) : Nat → Nat → m (Option Nat)
  | 0, drained => pure (some drained)
  | fuel + 1, drained => do
    match ← net.recvfrom clientFd 1024 { dontwait := true } with
    | .ok bs =>
      if bs.size == 0 then
        return none
      else
        let drained' := drained + bs.size
        if drained' >= CLOSING_DRAIN_MAX then
          return none
        else
          drainClosingClient net clientFd fuel drained'
    | .error e =>
      if e == Errno.EINTR then
        drainClosingClient net clientFd fuel drained
      else if e == Errno.EAGAIN then
        return some drained
      else
        return none

/-- Flush pending error reply bytes and `SHUT_WR` for a `.closingReply` slot. -/
def closingSendStep {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd)
    (cfd : fd) (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool)
    (cRev : Poll.PollEvents) : m (Option (Nat × Bool)) := do
  if !shutWr then
    if cRev.pollerr || cRev.pollhup || cRev.pollnval then
      return none
    else if cRev.pollout then
      match ← NetRelay.flushBytesNonblock net cfd replyBytes MAX_CLOSING_STEPS replyOff with
      | none => return none
      | some nextOff =>
        if nextOff >= replyBytes.size then
          if ← NetRelay.shutdownWrClean net cfd 16 then
            return some (nextOff, true)
          else
            return none
        else
          return some (nextOff, false)
    else
      return some (replyOff, false)
  else
    return some (replyOff, true)

/-- Drain residual client request bytes after `SHUT_WR` for a `.closingReply` slot. -/
def closingDrainStep {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd)
    (cfd : fd) (shut1 : Bool) (drained : Nat)
    (cRev : Poll.PollEvents) : m (Option Nat) := do
  if shut1 && (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) then
    drainClosingClient net cfd MAX_CLOSING_STEPS drained
  else
    return some drained


end LeanSwe.ConnectProxy.SysBridge
