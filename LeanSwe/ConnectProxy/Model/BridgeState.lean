import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model.RelayState

namespace LeanSwe.ConnectProxy.Internal.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal

/-- Bounded `EINTR` retry budget per individual non-blocking or setup syscall. -/
def MAX_EINTR_RETRIES : Nat := 64

/-- Per-poll-tick read iteration cap during `CONNECT` handshake. -/
def MAX_HANDSHAKE_STEPS : Nat := 256

/-- Maximum client connections accepted in a single poll tick. -/
def MAX_ACCEPT_BATCH : Nat := 256

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

/-- Outcome of one polymorphic `pollAndStepTickM` server loop iteration. -/
inductive PollTickOutcome (fd : Type) (dnsJob : Type) where
  /-- `ppoll` returned `EINTR`; caller should immediately retry the next loop iteration. -/
  | retryEintr
  /-- Stop was requested or `ppoll` returned a non-`EINTR` fatal error; caller should tear down. -/
  | stopOrFatal
  /-- Tick completed cleanly with updated active `slots` and `events`. -/
  | stepped (slots : Array (ClientSlot fd dnsJob)) (events : Array ConnectEvent)

end LeanSwe.ConnectProxy.Internal.SysBridge
