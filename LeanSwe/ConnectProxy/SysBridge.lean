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
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface
import LeanSwe.ConnectProxy.Relay

namespace LeanSwe.ConnectProxy.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model

/-- Bounded `EINTR` retry budget per individual non-blocking or setup syscall. -/
def MAX_EINTR_RETRIES : Nat := 64

/-- Per-call byte cap when reading HTTP `CONNECT` request headers. -/
def HANDSHAKE_CHUNK_MAX : Nat := 8192

/-- Per-poll-tick read iteration cap during `CONNECT` handshake. -/
def MAX_HANDSHAKE_STEPS : Nat := 256

/-- Maximum unread request body bytes drained on `403`/`502` before closing (`64 KiB`). -/
def CLOSING_DRAIN_MAX : Nat := 65536

/-- Maximum drain duration in milliseconds on `403`/`502` replies before closing (`250 ms`). -/
def CLOSING_TIMEOUT_MAX_MS : Nat := 250

/-- Per-poll-tick I/O iteration bound during `CLOSING_REPLY` flush/drain. -/
def MAX_CLOSING_STEPS : Nat := 256

/-- Maximum client connections accepted in a single poll tick. -/
def MAX_ACCEPT_BATCH : Nat := 256

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

/-- Convert an unscoped `Dns.DnsAddr` (`scopeId == 0`) to `ConnectProxy.IpAddr`, dropping scoped IPv6 records. -/
def dnsAddrToIpAddr? : Dns.DnsAddr → Option IpAddr
  | .ipv4 b0 b1 b2 b3 =>
    let addr : UInt32 :=
      (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32
    some (.v4 addr)
  | .ipv6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 sc =>
    if sc != 0 then
      none
    else
      let hi : UInt64 :=
        (b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) |||
        (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 32) |||
        (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) |||
        (b6.toUInt64 <<< 8) ||| b7.toUInt64
      let lo : UInt64 :=
        (b8.toUInt64 <<< 56) ||| (b9.toUInt64 <<< 48) |||
        (b10.toUInt64 <<< 40) ||| (b11.toUInt64 <<< 32) |||
        (b12.toUInt64 <<< 24) ||| (b13.toUInt64 <<< 16) |||
        (b14.toUInt64 <<< 8) ||| b15.toUInt64
      some (.v6 hi lo)

/-- Filter `Dns.DnsAddr` records to unscoped IPv4/IPv6 `IpAddr` candidates in resolver order. -/
def filterUnscopedDnsAddrs (addrs : List Dns.DnsAddr) : Array IpAddr :=
  (addrs.filterMap dnsAddrToIpAddr?).toArray

/-- Return `true` iff `(hi, lo)` encodes an RFC 4291 IPv4-mapped IPv6 address (`::ffff:0:0/96`). -/
def isIpv4MappedV6 (hi lo : UInt64) : Bool :=
  hi == 0 && (lo >>> 32) == 0x0000ffff

/-- Convert a verified `IpAddr` and `port` into a concrete `Net.SockAddr`, unwrapping `::ffff:a.b.c.d` to `AF_INET`. -/
def ipAddrToDialSockAddr (ip : IpAddr) (port : UInt16) : Net.SockAddr :=
  match ip with
  | .v4 addr => .ipv4 addr port
  | .v6 hi lo =>
    if isIpv4MappedV6 hi lo then
      .ipv4 lo.toUInt32 port
    else
      .ipv6 hi lo port 0 0

/-- Recover the semantic `IpAddr` dialed by `ipAddrToDialSockAddr` (`IpAddr.v4` when unwrapped, `ip` otherwise). -/
def effectiveDialIp (ip : IpAddr) : IpAddr :=
  match ip with
  | .v4 addr => .v4 addr
  | .v6 hi lo =>
    if isIpv4MappedV6 hi lo then .v4 lo.toUInt32 else .v6 hi lo

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

/-- Generic OS syscall capability bundle consumed by `LeanSwe.ConnectProxy.SysBridge`. -/
structure CProxySysOpsM (m : Type → Type) (fd : Type) where
  /-- Curated Linux file descriptor close (`close`). -/
  files : Files.FilesOpsM m fd
  /-- Curated Linux socket syscalls (`socket`, `socketpair`, `bind`, `listen`, `accept4`, `connect`, `getsockopt`, `setsockopt`, `getsockname`, `recvfrom`, `sendto`, `shutdown`). -/
  net : Net.NetOpsM m fd
  /-- Curated Linux readiness polling (`ppoll`). -/
  poll : Poll.PollOpsM m fd
  /-- Curated DNS name resolution (`getaddrinfo`). -/
  dns : Dns.DnsOpsM m
  /-- Curated monotonic clock access (`clock_gettime`, `clock_nanosleep`). -/
  timeRand : TimeRand.TimeRandOpsM m

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

/-- Deterministically close descriptor `d` in the OS file descriptor table via `sys.files.close`. -/
def CProxySysOpsM.closeFd {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (d : fd) : m Unit :=
  closeSysFdAux sys d 64

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

/-- Per-connection state machine phases matching the 5-state proxy protocol plus terminal `.done`. -/
inductive SlotPhase (fd : Type) (dnsJob : Type) where
  /-- Accumulating HTTP `CONNECT` request headers up to `\r\n\r\n` within `maxHeaderBytes` and `deadlineMs`. -/
  | handshake (clientFd : fd) (headBuf : ByteArray) (deadlineMs : Nat)
  /-- Waiting for asynchronous DNS resolution of `(host, port)`. -/
  | dns (clientFd : fd) (host : String) (port : UInt16) (job : dnsJob)
  /-- Waiting for non-blocking TCP `connect()` completion on `upstreamFd`, with remaining `candidates[candIdx..]`. -/
  | connecting
      (clientFd : fd)
      (upstreamFd : fd)
      (host : String)
      (port : UInt16)
      (candidates : Array IpAddr)
      (candIdx : Nat)
      (lastErrno? : Option Errno)
      (deadlineMs : Nat)
  /-- Bidirectional `16 KiB` TCP relay after queuing `200 Connection Established`. -/
  | relay (st : Relay.RelayState fd)
  /-- Graceful `403`/`502` header send, `SHUT_WR`, and bounded client RX drain avoiding `TCP RST`. -/
  | closingReply
      (clientFd? : Option fd)
      (replyBytes : ByteArray)
      (replyOff : Nat)
      (shutWr : Bool)
      (drained : Nat)
      (deadlineMs : Nat)
  /-- Terminal closed slot ready for removal from the active table. -/
  | done

/-- Single active client connection slot tracked by a running proxy instance. -/
structure ClientSlot (fd : Type) (dnsJob : Type) where
  /-- Current protocol phase and owned socket descriptors. -/
  phase : SlotPhase fd dnsJob
  /-- Whether this slot has already emitted its single `ConnectEvent`. -/
  eventEmitted : Bool := false
  /-- Parsed `(host, port)` target once Stage-1 `onHead` succeeds. -/
  target? : Option (String × UInt16) := none
  /-- Coalesced tunnel payload bytes received after `\r\n\r\n` during handshake. -/
  pipelined : ByteArray := ByteArray.empty

instance {fd dnsJob : Type} : Inhabited (ClientSlot fd dnsJob) where
  default := { phase := .done }

/-- Return `true` iff `slot` owns zero open descriptors or pending DNS jobs and can be pruned. -/
def ClientSlot.isFinished {fd dnsJob : Type} (slot : ClientSlot fd dnsJob) : Bool :=
  match slot.phase with
  | .done => true
  | .relay st => st.isClosed
  | .closingReply cfd? .. => cfd?.isNone
  | _ => false

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

/-- Active synchronous proxy entry stored in `SyncProxyTable` for `mkSyncRawOps`. -/
structure SyncProxyEntry (fd : Type) where
  /-- Unique handle ID. -/
  handleId : Nat
  /-- Bound loopback port (`1..65535`). -/
  port : UInt16
  /-- Validated configuration. -/
  vcfg : ValidProxyConfig
  /-- Open listener socket. -/
  listenFd : fd
  /-- Open wakeup reader socket. -/
  wakeR : fd
  /-- Open wakeup writer socket. -/
  wakeW : fd
  /-- Active client slots. -/
  slots : Array (ClientSlot fd Unit) := #[]
  /-- Emitted audit events. -/
  events : Array ConnectEvent := #[]

/-- Pure handle table for synchronous `RawConnectProxyOpsM` execution over any `CProxySysOpsM m fd`. -/
structure SyncProxyTable (fd : Type) where
  /-- Next fresh handle ID (`≥ 1`). -/
  nextHandleId : Nat := 1
  /-- Active proxy instances (most recently started first). -/
  entries : List (SyncProxyEntry fd) := []

/-- Compute a strictly fresh handle ID greater than all active handle IDs in `entries`. -/
def freshSyncHandleId {fd : Type} (tbl : SyncProxyTable fd) : Nat :=
  Nat.max tbl.nextHandleId ((tbl.entries.foldl (fun m e => Nat.max m e.handleId) 0) + 1)

/-- Construct a synchronous, single-threaded `RawConnectProxyOpsM (StateM W)` stand-in backed purely by `sys : CProxySysOpsM (StateM W) fd`.
    Formal FD-conservation and `healthyStep` proofs verify this synchronous stand-in; the concurrent `IO` task/socketpair driver (`mkIoRawOps` / `runIoProxyLoop` / `teardownIoLoopState`) is verified separately by runtime, mutation, and stress tests. -/
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

/-- Build the `ppoll` request array, per-slot index table, and optional relative timeout for one loop tick. -/
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

/-- Outcome of one polymorphic `pollAndStepTickM` server loop iteration. -/
inductive PollTickOutcome (fd : Type) (dnsJob : Type) where
  /-- `ppoll` returned `EINTR`; caller should immediately retry the next loop iteration. -/
  | retryEintr
  /-- Stop was requested or `ppoll` returned a non-`EINTR` fatal error; caller should tear down. -/
  | stopOrFatal
  /-- Tick completed cleanly with updated active `slots` and `events`. -/
  | stepped (slots : Array (ClientSlot fd dnsJob)) (events : Array ConnectEvent)

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

/-- Observational syscall audit log for stating end-to-end invariants over any `CProxySysOpsM`. -/
structure SysAuditTrace (fd : Type) where
  /-- Descriptors returned by `net.socket`, `net.socketpair`, or `net.accept4` in allocation order. -/
  openedFds : Array fd := #[]
  /-- Descriptors passed to `files.close` in call order. -/
  closedFds : Array fd := #[]
  /-- Socket addresses passed to `net.bind` in call order. -/
  boundAddrs : Array Net.SockAddr := #[]
  /-- Hostnames passed to `dns.getaddrinfo` in call order. -/
  dnsQueries : Array String := #[]
  /-- Socket addresses passed to `net.connect` in call order. -/
  dialedAddrs : Array Net.SockAddr := #[]
  /-- Ordered bytes returned by `net.recvfrom` across calls. -/
  recvBytes : Array UInt8 := #[]
  /-- Ordered bytes accepted by `net.sendto` across calls. -/
  sentBytes : Array UInt8 := #[]
  /-- Non-`EINTR` `Errno` outcomes returned by `net.accept4`, `net.recvfrom`, or `net.sendto`. -/
  netErrs : Array Errno := #[]
  /-- Set to `true` when `net.sendto` on a non-empty buffer returns `.ok 0`. -/
  sawZeroSend : Bool := false
  /-- Per-call `poll.ppoll` outcomes (`none` on `.ok`, `some e` on `.error e`). -/
  pollOutcomes : Array (Option Errno) := #[]
  deriving BEq, DecidableEq, Inhabited

/-- Lift a `StateM W` action to `StateM (W × SysAuditTrace fd)` while updating the audit trace on result. -/
def liftTraceOp {W fd α : Type}
    (act : StateM W α)
    (upd : α → SysAuditTrace fd → SysAuditTrace fd := fun _ tr => tr) :
    StateM (W × SysAuditTrace fd) α := fun (w, tr) =>
  let (r, w') := act.run w
  (r, (w', upd r tr))

/-- Wrap any `sys : CProxySysOpsM (StateM W) fd` with pure non-interfering syscall trace recording. -/
def instrumentSysOps {W fd : Type}
    (sys : CProxySysOpsM (StateM W) fd) :
    CProxySysOpsM (StateM (W × SysAuditTrace fd)) fd :=
  { files :=
      { openat := fun d p fl m => liftTraceOp (sys.files.openat d p fl m)
        openat2 := fun d p how => liftTraceOp (sys.files.openat2 d p how)
        close := fun h => liftTraceOp (sys.files.close h) (fun _ tr => { tr with closedFds := tr.closedFds.push h })
        read := fun h n => liftTraceOp (sys.files.read h n)
        write := fun h bs => liftTraceOp (sys.files.write h bs)
        fstat := fun h => liftTraceOp (sys.files.fstat h)
        fstatat := fun d p fl => liftTraceOp (sys.files.fstatat d p fl)
        faccessat := fun d p m fl => liftTraceOp (sys.files.faccessat d p m fl)
        mkdirat := fun d p m => liftTraceOp (sys.files.mkdirat d p m)
        unlinkat := fun d p rd => liftTraceOp (sys.files.unlinkat d p rd)
        renameat2 := fun od op nd np fl => liftTraceOp (sys.files.renameat2 od op nd np fl)
        symlinkat := fun t d lp => liftTraceOp (sys.files.symlinkat t d lp)
        readlinkat := fun d p c => liftTraceOp (sys.files.readlinkat d p c)
        getdents64 := fun h c => liftTraceOp (sys.files.getdents64 h c)
        fchmodat := fun d p m => liftTraceOp (sys.files.fchmodat d p m)
        fchmod := fun h m => liftTraceOp (sys.files.fchmod h m)
        flock := fun h op => liftTraceOp (sys.files.flock h op)
        fcntl := fun h cmd => liftTraceOp (sys.files.fcntl h cmd)
        fsync := fun h => liftTraceOp (sys.files.fsync h)
        getcwd := fun c => liftTraceOp (sys.files.getcwd c)
        lseek := fun h off wh => liftTraceOp (sys.files.lseek h off wh)
        reopenReadOnly := fun h => liftTraceOp (sys.files.reopenReadOnly h)
        dupStdio := fun sl => liftTraceOp (sys.files.dupStdio sl) }
    net :=
      { socket := fun dom st fl p =>
          liftTraceOp (sys.net.socket dom st fl p) fun r tr =>
            match r with
            | .ok h => { tr with openedFds := tr.openedFds.push h }
            | .error _ => tr
        socketpair := fun dom st fl =>
          liftTraceOp (sys.net.socketpair dom st fl) fun r tr =>
            match r with
            | .ok (h0, h1) => { tr with openedFds := (tr.openedFds.push h0).push h1 }
            | .error _ => tr
        bind := fun h sa =>
          liftTraceOp (sys.net.bind h sa) fun _ tr =>
            { tr with boundAddrs := tr.boundAddrs.push sa }
        listen := fun h bl => liftTraceOp (sys.net.listen h bl)
        accept4 := fun h fl =>
          liftTraceOp (sys.net.accept4 h fl) fun r tr =>
            match r with
            | .ok (cfd, _) => { tr with openedFds := tr.openedFds.push cfd }
            | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e }
        connect := fun h sa =>
          liftTraceOp (sys.net.connect h sa) fun _ tr =>
            { tr with dialedAddrs := tr.dialedAddrs.push sa }
        getsockopt := fun h opt => liftTraceOp (sys.net.getsockopt h opt)
        setsockopt := fun h opt val => liftTraceOp (sys.net.setsockopt h opt val)
        getsockname := fun h => liftTraceOp (sys.net.getsockname h)
        recvfrom := fun h n fl =>
          liftTraceOp (sys.net.recvfrom h n fl) fun r tr =>
            match r with
            | .ok bs =>
              let k := Nat.min bs.size n.toNat
              let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
              { tr with recvBytes := tr.recvBytes ++ accepted }
            | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e }
        sendto := fun h bs fl =>
          liftTraceOp (sys.net.sendto h bs fl) fun r tr =>
            match r with
            | .ok n =>
              let k := Nat.min n.toNat bs.size
              let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
              let zeroSend := tr.sawZeroSend || (n == 0 && bs.size > 0)
              { tr with sentBytes := tr.sentBytes ++ accepted, sawZeroSend := zeroSend }
            | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e }
        shutdown := fun h how => liftTraceOp (sys.net.shutdown h how)
        sendmsg := fun h fds => liftTraceOp (sys.net.sendmsg h fds)
        recvmsg := fun h maxFds => liftTraceOp (sys.net.recvmsg h maxFds)
        ioctl := fun h req ifn => liftTraceOp (sys.net.ioctl h req ifn) }
    poll :=
      { ppoll := fun fds to? =>
          liftTraceOp (sys.poll.ppoll fds to?) fun r tr =>
            match r with
            | .ok _ => { tr with pollOutcomes := tr.pollOutcomes.push none }
            | .error e => { tr with pollOutcomes := tr.pollOutcomes.push (some e) }
        eventfd2 := fun iv fl => liftTraceOp (sys.poll.eventfd2 iv fl) }
    dns :=
      { getaddrinfo := fun host hints =>
          liftTraceOp (sys.dns.getaddrinfo host hints) fun _ tr =>
            { tr with dnsQueries := tr.dnsQueries.push host } }
    timeRand :=
      { clock_gettime := fun clk => liftTraceOp (sys.timeRand.clock_gettime clk)
        clock_nanosleep := fun clk abs ts => liftTraceOp (sys.timeRand.clock_nanosleep clk abs ts)
        getrandom := fun n fl => liftTraceOp (sys.timeRand.getrandom n fl) } }

/-- Shared state of one off-thread `IO` DNS lookup job. -/
structure IoDnsJobState where
  /-- Set to `true` when the owning client slot disconnects or the proxy tears down; the worker skips writing `result?` once cancelled. -/
  cancelled : Bool := false
  /-- Set to `true` in the worker `finally` block strictly before closing `dnsW` so loop wakeups never wait on stale `IO.hasFinished`. -/
  done : Bool := false
  /-- Completed `getaddrinfo` result (`some (.ok ips)` or `some (.error msg)`). -/
  result? : Option (Except String (Array IpAddr)) := none

/-- Handle to one off-thread `IO` DNS lookup job with a dedicated per-job one-shot wakeup socketpair (`dnsR` loop-owned, `dnsW` worker-owned). -/
structure IoDnsJob where
  /-- Shared cancellation, completion, and result state cell. -/
  stateRef : IO.Ref IoDnsJobState
  /-- Loop-owned read end of the per-job `AF_UNIX` `SOCK_STREAM` wakeup socketpair (`none` after close). -/
  dnsRRef : IO.Ref (Option RawFd)
  /-- Dedicated OS thread task exclusively owning the write end (`dnsW`), closing it inside `finally` without writing or touching proxy `wakeW`. -/
  task : Task (Except IO.Error Unit)

/-- Cooldown duration in milliseconds (`10 ms`) suppressing `listenFd` spin after `accept4` resource exhaustion. -/
def ACCEPT_EMFILE_BACKOFF_MS : Nat := 10

/-- Return `true` iff `e` indicates transient descriptor or socket-buffer exhaustion on `accept4`. -/
def isAcceptResourceErrno (e : Errno) : Bool :=
  e == Errno.EMFILE || e == Errno.ENFILE || e == Errno.ENOMEM || e == Errno.ENOBUFS

/-- Mutable state owned exclusively by one dedicated `IO` proxy server loop. -/
structure IoLoopState where
  /-- Active loopback listener socket (`none` after teardown). -/
  listenFd? : Option RawFd := none
  /-- Non-blocking shutdown wakeup reader socket (closed by `stopProxy` only after `loopTask` exits). -/
  wakeR? : Option RawFd := none
  /-- Active client slots (`slots.size + dnsTasks.size ≤ maxConcurrentTunnels`). -/
  slots : Array (ClientSlot RawFd IoDnsJob) := #[]
  /-- Detached in-flight DNS jobs whose loop-owned `dnsR` socket stays open and watched by `ppoll` until the worker closes `dnsW` (or teardown runs), keeping `maxConcurrentTunnels` bounded without sleeping forever. -/
  dnsTasks : Array IoDnsJob := #[]
  /-- Monotonic deadline until which `listenFd` `POLLIN` backs off after `accept4` resource exhaustion. -/
  acceptBackoffUntilMs : Nat := 0
  /-- Accumulated audit events in decision/completion order. -/
  events : Array ConnectEvent := #[]

/-- Entry in an `IO.Ref IoProxyTable` tracking a running concurrent `IO` proxy. -/
structure IoProxyEntry where
  /-- Unique handle identifier. -/
  handleId : Nat
  /-- Bound loopback port. -/
  port : UInt16
  /-- `true` once `stopProxy` has claimed ownership of stopping this handle. -/
  stopClaimed : Bool := false
  /-- Stop flag polled by the dedicated server loop. -/
  stopRequested : IO.Ref Bool
  /-- Shutdown wakeup reader socket closed by `stopProxy` strictly after `IO.wait loopTask`. -/
  wakeRRef : IO.Ref (Option RawFd)
  /-- Shutdown wakeup writer socket owned exclusively by `stopProxy` and closed strictly after `IO.wait loopTask`. -/
  wakeWRef : IO.Ref (Option RawFd)
  /-- Dedicated OS thread task running `runIoProxyLoop`. -/
  loopTask : Task (Except IO.Error (Array ConnectEvent))

/-- Scoped concurrent `IO` proxy handle table (allocated per session via `IO.mkRef`, zero global `@[init]`). -/
structure IoProxyTable where
  /-- Next monotonic handle ID. -/
  nextHandleId : Nat := 1
  /-- Active (undetached) proxy entries. -/
  entries : List IoProxyEntry := []

/-- Default `IO` syscall bundle backed purely by `LeanSwe.LinuxSyscall.{Files,Net,Poll,Dns,TimeRand}.defaultOps`. -/
def defaultIoSysOps : CProxySysOpsM IO RawFd :=
  { files := Files.defaultOps
    net := Net.defaultOps
    poll := Poll.defaultOps
    dns := Dns.defaultOps
    timeRand := TimeRand.defaultOps }

/-- Wrap `defaultIoSysOps` so `accept4` records transient resource exhaustion (`EMFILE`/`ENFILE`/`ENOMEM`/`ENOBUFS`) in `hitLimitRef`. -/
def ioSysOpsWithAcceptWatch (hitLimitRef : IO.Ref Bool) : CProxySysOpsM IO RawFd :=
  { defaultIoSysOps with
    net :=
      { defaultIoSysOps.net with
        accept4 := fun lfd fl => do
          let r ← defaultIoSysOps.net.accept4 lfd fl
          if let .error e := r then
            if isAcceptResourceErrno e then
              hitLimitRef.set true
          return r } }

/-- Close the loop-owned wakeup reader descriptor `dnsR` of `job` at most once (idempotent). -/
def closeDnsReadFd (job : IoDnsJob) : IO Unit := do
  match ← job.dnsRRef.modifyGet fun r => (r, none) with
  | some dnsR => defaultIoSysOps.closeFd dnsR
  | none => pure ()

/-- Mark a pending DNS job cancelled and close its loop-owned wakeup reader descriptor `dnsR` once. -/
def cancelDnsJobIo (job : IoDnsJob) : IO Unit := do
  job.stateRef.modify fun j => { j with cancelled := true }
  closeDnsReadFd job

/-- Retain only those detached DNS jobs that have not yet finished and still hold an open loop-owned `dnsR` socket, closing `dnsR` on completed jobs. -/
def pruneFinishedDnsJobs
    (jobs : Array IoDnsJob) :
    IO (Array IoDnsJob) := do
  let mut live : Array IoDnsJob := Array.emptyWithCapacity jobs.size
  for job in jobs do
    let stJob ← job.stateRef.get
    if stJob.done || (← IO.hasFinished job.task) then
      closeDnsReadFd job
    else if (← job.dnsRRef.get).isSome then
      live := live.push job
  return live

/-- Mark a running `.dns` job cancelled on mid-lookup client disconnect, keeping `dnsR` open in `dnsTasksRef` so `ppoll` wakes immediately when the worker closes `dnsW`. If already finished, closes `dnsR` immediately instead of detaching. -/
def detachDnsJobIo
    (job : IoDnsJob)
    (dnsTasksRef : IO.Ref (Array IoDnsJob)) : IO Unit := do
  let alreadyDone ← job.stateRef.modifyGet fun j => (j.done, { j with cancelled := true })
  if alreadyDone || (← IO.hasFinished job.task) then
    closeDnsReadFd job
  else if (← job.dnsRRef.get).isSome then
    dnsTasksRef.modify fun js => js.push job

/-- Spawn an off-thread `IO.asTask (prio := .dedicated)` `getaddrinfo` lookup with a private per-job wakeup `socketpair`.
    The event loop exclusively owns `dnsR`; the worker task exclusively owns `dnsW` and closes it inside `finally` after setting `done := true` (generating EOF/`POLLHUP` with zero `write`/`sendto`, zero `EPIPE`, and zero `SIGPIPE`). On `socketpair` resource exhaustion, responds with HTTP `503` without leaking descriptors. -/
def startDnsIo
    (limits : ProxyLimits)
    (slot : ClientSlot RawFd IoDnsJob)
    (events : Array ConnectEvent)
    (clientFd : RawFd)
    (host : String) (port : UInt16)
    (dnsResolve : String → IO (Except Dns.DnsError (List Dns.DnsAddr)) :=
      fun h => Dns.defaultOps.getaddrinfo h { family := .any, sockType := .stream })
    (mkWakePair : IO (Except Errno (RawFd × RawFd)) :=
      Net.defaultOps.socketpair .unix .stream { nonblock := true, cloexec := true }) :
    IO (ClientSlot RawFd IoDnsJob × Array ConnectEvent) := do
  match ← retryEintr mkWakePair MAX_EINTR_RETRIES with
  | .error e =>
    let msg := s!"dns wakeup socketpair failed: errno {e}"
    let (slot1, events1) :=
      emitSlotEvent slot events
        { host := some host, port := some port, outcome := .failed, reason := some msg }
    let slot2 ← enterClosingReply defaultIoSysOps limits slot1 clientFd 503
    return (slot2, events1)
  | .ok (dnsR, dnsW) =>
    let jobRef ← IO.mkRef ({} : IoDnsJobState)
    let dnsRRef ← IO.mkRef (some dnsR)
    let taskRes ←
      try
        let dnsTask ← IO.asTask (prio := .dedicated) do
          try
            let res ← dnsResolve host
            let mapped : Except String (Array IpAddr) :=
              match res with
              | .error dnsErr =>
                .error (if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message)
              | .ok addrs =>
                .ok (filterUnscopedDnsAddrs addrs)
            jobRef.modify fun st =>
              if st.cancelled then st else { st with result? := some mapped }
          catch err =>
            let msg := toString err
            let reason := if msg.isEmpty then "dns resolution failed" else msg
            jobRef.modify fun st =>
              if st.cancelled then st else { st with result? := some (.error reason) }
          finally
            jobRef.modify fun st =>
              let st1 :=
                if st.cancelled || st.result?.isSome then st
                else { st with result? := some (.error "dns resolution failed") }
              { st1 with done := true }
            defaultIoSysOps.closeFd dnsW
        pure (Except.ok dnsTask)
      catch err =>
        defaultIoSysOps.closeFd dnsR
        defaultIoSysOps.closeFd dnsW
        let msg := toString err
        pure (Except.error (if msg.isEmpty then "failed to spawn dns task" else msg))
    match taskRes with
    | .error msg =>
      let (slot1, events1) :=
        emitSlotEvent slot events
          { host := some host, port := some port, outcome := .failed, reason := some msg }
      let slot2 ← enterClosingReply defaultIoSysOps limits slot1 clientFd 503
      return (slot2, events1)
    | .ok dnsTask =>
      let job : IoDnsJob := { stateRef := jobRef, dnsRRef := dnsRRef, task := dnsTask }
      return ({ slot with phase := .dns clientFd host port job }, events)

/-- Tear down loop-owned resources inside `stateRef`: cancel pending `.dns` jobs and close every slot FD, active and detached per-job `dnsR`, and `listenFd` immediately without blocking on in-flight DNS tasks. The shutdown `wakeR`/`wakeW` pair is closed strictly after `loopTask` exits in `stopProxy`. -/
def teardownIoLoopState (stateRef : IO.Ref IoLoopState) : IO (Array ConnectEvent) := do
  let st ← stateRef.modifyGet fun s => (s, {})
  let finalEvents ←
    teardownAllSlotsList defaultIoSysOps cancelDnsJobIo st.slots.toList st.events
  for job in st.dnsTasks do
    cancelDnsJobIo job
  NetRelay.closeOptFd defaultIoSysOps.closeFd st.listenFd?
  return finalEvents

/-- Fuel-bounded dedicated `IO` event loop wrapping the verified generic `pollAndStepTickM` step, monitoring both active `.dns` slots and detached in-flight DNS jobs via their private wakeup sockets (`dnsR`). -/
def runIoProxyLoop
    (vcfg : ValidProxyConfig)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (stopRequested : IO.Ref Bool)
    (stateRef : IO.Ref IoLoopState)
    (fuel : Nat)
    (dnsResolve : String → IO (Except Dns.DnsError (List Dns.DnsAddr)) :=
      fun h => Dns.defaultOps.getaddrinfo h { family := .any, sockType := .stream })
    (mkWakePair : IO (Except Errno (RawFd × RawFd)) :=
      Net.defaultOps.socketpair .unix .stream { nonblock := true, cloexec := true }) :
    IO (Array ConnectEvent) := do
  match fuel with
  | 0 => teardownIoLoopState stateRef
  | fuel' + 1 =>
    if ← stopRequested.get then
      teardownIoLoopState stateRef
    else
      let st0 ← stateRef.get
      let liveDns0 ← pruneFinishedDnsJobs st0.dnsTasks
      let curBackoff :=
        if liveDns0.size < st0.dnsTasks.size then 0 else st0.acceptBackoffUntilMs
      let st := { st0 with dnsTasks := liveDns0, acceptBackoffUntilMs := curBackoff }
      stateRef.set st
      match st.listenFd?, st.wakeR? with
      | some listenFd, some wakeR =>
        let prevLoad := st.slots.size + liveDns0.size
        let mut extraDnsFds : Array RawFd := Array.emptyWithCapacity liveDns0.size
        let mut liveWithWatch : Array (IoDnsJob × Option Nat) := Array.emptyWithCapacity liveDns0.size
        for job in liveDns0 do
          match ← job.dnsRRef.get with
          | some dfd =>
            let idx := extraDnsFds.size
            extraDnsFds := extraDnsFds.push dfd
            liveWithWatch := liveWithWatch.push (job, some idx)
          | none =>
            liveWithWatch := liveWithWatch.push (job, none)
        let dnsTasksRef ← IO.mkRef liveDns0
        let hitAcceptLimitRef ← IO.mkRef false
        let tickOut ← pollAndStepTickM (ioSysOpsWithAcceptWatch hitAcceptLimitRef) vcfg.config.limits onHead onResolved
          stopRequested.get
          (fun _ => pure false)
          (fun slot evs cfd h p => startDnsIo vcfg.config.limits slot evs cfd h p dnsResolve mkWakePair)
          (fun job => do
            let stJob ← job.stateRef.get
            match stJob.result? with
            | some mapped =>
              closeDnsReadFd job
              return some mapped
            | none =>
              if stJob.done || (← IO.hasFinished job.task) || (← job.dnsRRef.get).isNone then
                closeDnsReadFd job
                return some (.error "dns resolution failed")
              else
                return none)
          (fun job => detachDnsJobIo job dnsTasksRef)
          wakeR listenFd st.slots st.events
          liveDns0.size curBackoff
          (do
            let pruned ← pruneFinishedDnsJobs (← dnsTasksRef.get)
            dnsTasksRef.set pruned
            return pruned.size)
          (fun job => job.dnsRRef.get)
          true
          extraDnsFds
          (fun extraRevs => do
            let mut kept : Array IoDnsJob := Array.emptyWithCapacity liveWithWatch.size
            for (job, idx?) in liveWithWatch do
              let signalled :=
                match idx? with
                | some i =>
                  let ev := extraRevs[i]?.getD {}
                  ev.pollin || ev.pollhup || ev.pollerr || ev.pollnval
                | none => true
              if signalled || (← job.stateRef.get).done || (← IO.hasFinished job.task) then
                closeDnsReadFd job
              else if (← job.dnsRRef.get).isSome then
                kept := kept.push job
            dnsTasksRef.set kept)
        match tickOut with
        | .retryEintr =>
          runIoProxyLoop vcfg onHead onResolved stopRequested stateRef fuel' dnsResolve mkWakePair
        | .stopOrFatal =>
          let curTasks ← dnsTasksRef.get
          stateRef.modify fun s => { s with dnsTasks := curTasks }
          teardownIoLoopState stateRef
        | .stepped acceptedSlots nextEvents =>
          let nextDnsTasks ← pruneFinishedDnsJobs (← dnsTasksRef.get)
          let hitAcceptLimit ← hitAcceptLimitRef.get
          let nowAfter ← monoNowMs defaultIoSysOps
          let postStepLoad := acceptedSlots.size + nextDnsTasks.size
          let nextBackoff : Nat :=
            if hitAcceptLimit then
              nowAfter + ACCEPT_EMFILE_BACKOFF_MS
            else if postStepLoad < prevLoad || nowAfter >= curBackoff then
              0
            else
              curBackoff
          stateRef.set
            { st with
              slots := acceptedSlots
              dnsTasks := nextDnsTasks
              acceptBackoffUntilMs := nextBackoff
              events := nextEvents }
          runIoProxyLoop vcfg onHead onResolved stopRequested stateRef fuel' dnsResolve mkWakePair
      | _, _ =>
        teardownIoLoopState stateRef

/-- Compute a fresh handle ID for `IoProxyTable`. -/
def freshIoHandleId (tbl : IoProxyTable) : Nat :=
  Nat.max tbl.nextHandleId ((tbl.entries.foldl (fun m e => Nat.max m e.handleId) 0) + 1)

/-- Build a concurrent `IO` `RawConnectProxyOps` bundle backed by an explicit `IO.Ref IoProxyTable`.
    Unlike the synchronous `mkSyncRawOps` stand-in, this driver offloads DNS resolution onto dedicated tasks communicating exclusively via per-job `socketpair` EOF/close, so `stopProxy` returns immediately without blocking on stalled lookups. -/
def mkIoRawOps (tableRef : IO.Ref IoProxyTable)
    (dnsResolve : String → IO (Except Dns.DnsError (List Dns.DnsAddr)) :=
      fun h => Dns.defaultOps.getaddrinfo h { family := .any, sockType := .stream })
    (mkWakePair : IO (Except Errno (RawFd × RawFd)) :=
      Net.defaultOps.socketpair .unix .stream { nonblock := true, cloexec := true }) :
    RawConnectProxyOps :=
  { mapRawError := Model.mapRawErrorPure
    startProxy := fun vcfg onHead onResolved => do
      try
        match ← createListener defaultIoSysOps vcfg with
        | .error err => return .error err
        | .ok (listenFd, wakeR, wakeW, boundPort) =>
          let stopRequested ← IO.mkRef false
          let wakeRRef ← IO.mkRef (some wakeR)
          let wakeWRef ← IO.mkRef (some wakeW)
          let stateRef ← IO.mkRef
            ({ listenFd? := some listenFd, wakeR? := some wakeR } : IoLoopState)
          let loopTaskRes ←
            try
              let t ← IO.asTask (prio := .dedicated) do
                try
                  runIoProxyLoop vcfg onHead onResolved stopRequested stateRef LOOP_FUEL dnsResolve mkWakePair
                catch err =>
                  let _ ← teardownIoLoopState stateRef
                  throw err
              pure (Except.ok t)
            catch err =>
              let _ ← teardownIoLoopState stateRef
              defaultIoSysOps.closeFd wakeR
              defaultIoSysOps.closeFd wakeW
              pure (Except.error err)
          match loopTaskRes with
          | .error err =>
            return .error (Model.mapRawErrorPure (.userError (toString err)))
          | .ok loopTask =>
            let hid ← tableRef.modifyGet fun tbl =>
              let h := freshIoHandleId tbl
              let entry : IoProxyEntry :=
                { handleId := h
                  port := boundPort
                  stopClaimed := false
                  stopRequested := stopRequested
                  wakeRRef := wakeRRef
                  wakeWRef := wakeWRef
                  loopTask := loopTask }
              (h, { nextHandleId := h + 1, entries := entry :: tbl.entries })
            return .ok { handleId := hid, port := boundPort }
      catch err =>
        return .error (Model.mapRawErrorPure (.userError (toString err)))
    stopProxy := fun proxy => do
      try
        let claimed? ← tableRef.modifyGet fun tbl =>
          match tbl.entries.find? (fun e => e.handleId == proxy.handleId) with
          | none => (none, tbl)
          | some entry =>
            if entry.stopClaimed then
              (none, tbl)
            else
              let entries' := tbl.entries.map fun e =>
                if e.handleId == proxy.handleId then { e with stopClaimed := true } else e
              (some entry, { tbl with entries := entries' })
        match claimed? with
        | none =>
          return .error (Model.mapRawErrorPure (.invalidArgument none "proxy handle is not active"))
        | some entry =>
          entry.stopRequested.set true
          let wakeR? ← entry.wakeRRef.modifyGet fun r => (r, none)
          let wakeW? ← entry.wakeWRef.modifyGet fun w => (w, none)
          try
            match wakeW? with
            | some w =>
              let _ ← retryEintr
                (Net.defaultOps.sendto w (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
                MAX_EINTR_RETRIES
            | none => pure ()
            let waitRes ← IO.wait entry.loopTask
            match waitRes with
            | .ok evs => return .ok evs
            | .error err =>
              return .error (Model.mapRawErrorPure (.userError (toString err)))
          finally
            NetRelay.closeOptFd defaultIoSysOps.closeFd wakeR?
            NetRelay.closeOptFd defaultIoSysOps.closeFd wakeW?
            tableRef.modify fun tbl =>
              { tbl with entries := tbl.entries.filter (fun e => e.handleId != proxy.handleId) }
      catch err =>
        return .error (Model.mapRawErrorPure (.userError (toString err)))
    activeProxyCount := do
      return (← tableRef.get).entries.length }

/-- Run a scoped `IO` `withProxy` session using a fresh session-local `IoProxyTable` (zero global `@[init]`) for an already-validated `ValidProxyConfig`. -/
def withProxyIo {α : Type} (vcfg : ValidProxyConfig)
    (action : RunningProxy → IO (Except ProxyError α)) :
    IO (Except ProxyError (α × Array ConnectEvent)) := do
  let tableRef ← IO.mkRef ({} : IoProxyTable)
  Model.withValidProxyModel (mkIoRawOps tableRef) vcfg action

end LeanSwe.ConnectProxy.SysBridge
