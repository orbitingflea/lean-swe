import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Dns.Model
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.BridgeState
import LeanSwe.ConnectProxy.Model.HealthySys

namespace LeanSwe.ConnectProxy.Model

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys

/-- Unified OS capability bundle specialized to `LinuxSyscall.RawFd` for compositional `Core.ObeysStepFromConc` verification. -/
abbrev FullSysOpsM (m : Type → Type) := CProxySysOpsM m RawFd

/-- Socket syscall request over `RawFd` covering the `LinuxSyscall.Net` operations consumed by `ConnectProxy`. -/
inductive RawFdNetReq where
  /-- Create an unbound socket endpoint via `socket(2)`. -/
  | socket (dom : Net.SockDomain) (st : Net.SockType) (fl : Net.SockFlags) (proto : UInt32)
  /-- Create a connected local socket pair via `socketpair(2)`. -/
  | socketpair (dom : Net.SockDomain) (st : Net.SockType) (fl : Net.SockFlags)
  /-- Bind `fd` to `addr` via `bind(2)`. -/
  | bind (fd : RawFd) (addr : Net.SockAddr)
  /-- Mark `fd` passive with `backlog` via `listen(2)`. -/
  | listen (fd : RawFd) (backlog : UInt32)
  /-- Accept a peer socket on `fd` via `accept4(2)`. -/
  | accept4 (fd : RawFd) (fl : Net.SockFlags)
  /-- Initiate connection on `fd` to `addr` via `connect(2)`. -/
  | connect (fd : RawFd) (addr : Net.SockAddr)
  /-- Read socket option `opt` on `fd` via `getsockopt(2)`. -/
  | getsockopt (fd : RawFd) (opt : Net.SockOpt)
  /-- Set socket option `opt` on `fd` to `val` via `setsockopt(2)`. -/
  | setsockopt (fd : RawFd) (opt : Net.SetSockOpt) (val : UInt32)
  /-- Query local bound address of `fd` via `getsockname(2)`. -/
  | getsockname (fd : RawFd)
  /-- Receive up to `maxBytes` from `fd` via `recvfrom(2)`. -/
  | recvfrom (fd : RawFd) (maxBytes : UInt32) (fl : Net.MsgFlags)
  /-- Send `data` on `fd` via `sendto(2)`. -/
  | sendto (fd : RawFd) (data : ByteArray) (fl : Net.MsgFlags)
  /-- Shut down `fd` direction `how` via `shutdown(2)`. -/
  | shutdown (fd : RawFd) (how : Net.ShutHow)

/-- Map a `RawFdNetReq` into `Net.NetReq` under a handle-table projection `toHid : RawFd → Nat`. -/
def mapRawFdNetReq (toHid : RawFd → Nat) : RawFdNetReq → Net.NetReq
  | .socket dom st fl proto => .socket dom st fl proto
  | .socketpair dom st fl => .socketpair dom st fl
  | .bind d sa => .bind (toHid d) sa
  | .listen d bl => .listen (toHid d) bl
  | .accept4 d fl => .accept4 (toHid d) fl
  | .connect d sa => .connect (toHid d) sa
  | .getsockopt d opt => .getsockopt (toHid d) opt
  | .setsockopt d opt val => .setsockopt (toHid d) opt val
  | .getsockname d => .getsockname (toHid d)
  | .recvfrom d n fl => .recvfrom (toHid d) n fl
  | .sendto d bs fl => .sendto (toHid d) bs fl
  | .shutdown d how => .shutdown (toHid d) how

/-- Socket syscall outcome over `RawFd` paired with `RawFdNetReq`. -/
inductive RawFdNetOut where
  /-- `socket` succeeded returning `fd`. -/
  | opened (fd : RawFd)
  /-- `socketpair` succeeded returning `(fd0, fd1)`. -/
  | pair (fd0 fd1 : RawFd)
  /-- `accept4` succeeded returning `(fd, addr)`. -/
  | accepted (fd : RawFd) (addr : Net.SockAddr)
  /-- `getsockname` succeeded returning `addr`. -/
  | addr (addr : Net.SockAddr)
  /-- `recvfrom` succeeded returning `data`. -/
  | bytes (data : ByteArray)
  /-- `getsockopt` or `sendto` succeeded returning `val`. -/
  | u32 (val : UInt32)
  /-- Unit-returning socket syscall succeeded. -/
  | unit
  /-- Socket syscall failed with Linux `Errno`. -/
  | err (code : Errno)

/-- Relate a `RawFdNetOut` to a model `Net.NetOutcome` (preserving exact address, byte, scalar, and errno payloads). -/
def RawFdNetOut.MatchesModel : RawFdNetOut → Net.NetOutcome → Prop
  | .opened _, .opened _ => True
  | .pair _ _, .pair _ _ => True
  | .accepted _ sa, .accepted _ sa' => sa = sa'
  | .addr sa, .addr sa' => sa = sa'
  | .bytes bs, .bytes bs' => bs = bs'
  | .u32 v, .u32 v' => v = v'
  | .unit, .unit => True
  | .err e, .err e' => e = e'
  | _, _ => False

/-- Wrap `Except Errno RawFd` into `RawFdNetOut`. -/
def rawFdNetOutOfOpened : Except Errno RawFd → RawFdNetOut
  | .ok d => .opened d
  | .error e => .err e

/-- Wrap `Except Errno (RawFd × RawFd)` into `RawFdNetOut`. -/
def rawFdNetOutOfPair : Except Errno (RawFd × RawFd) → RawFdNetOut
  | .ok (d0, d1) => .pair d0 d1
  | .error e => .err e

/-- Wrap `Except Errno (RawFd × Net.SockAddr)` into `RawFdNetOut`. -/
def rawFdNetOutOfAccepted : Except Errno (RawFd × Net.SockAddr) → RawFdNetOut
  | .ok (d, sa) => .accepted d sa
  | .error e => .err e

/-- Wrap `Except Errno Net.SockAddr` into `RawFdNetOut`. -/
def rawFdNetOutOfAddr : Except Errno Net.SockAddr → RawFdNetOut
  | .ok sa => .addr sa
  | .error e => .err e

/-- Wrap `Except Errno ByteArray` into `RawFdNetOut`. -/
def rawFdNetOutOfBytes : Except Errno ByteArray → RawFdNetOut
  | .ok bs => .bytes bs
  | .error e => .err e

/-- Wrap `Except Errno UInt32` into `RawFdNetOut`. -/
def rawFdNetOutOfU32 : Except Errno UInt32 → RawFdNetOut
  | .ok v => .u32 v
  | .error e => .err e

/-- Wrap `Except Errno Unit` into `RawFdNetOut`. -/
def rawFdNetOutOfUnit : Except Errno Unit → RawFdNetOut
  | .ok () => .unit
  | .error e => .err e

/-- Wrap `Except Errno (Array Poll.PollEvents)` into `Poll.PollOutcome`. -/
def pollOutcomeOfPolled : Except Errno (Array Poll.PollEvents) → Poll.PollOutcome
  | .ok revs => .polled revs
  | .error e => .err e

/-- Execute one `RawFdNetReq` against `net : Net.NetOpsM (StateM W) RawFd`. -/
def execRawFdNetReq {W : Type} (net : Net.NetOpsM (StateM W) RawFd) :
    RawFdNetReq → StateM W RawFdNetOut
  | .socket dom st fl proto => rawFdNetOutOfOpened <$> net.socket dom st fl proto
  | .socketpair dom st fl => rawFdNetOutOfPair <$> net.socketpair dom st fl
  | .bind d sa => rawFdNetOutOfUnit <$> net.bind d sa
  | .listen d bl => rawFdNetOutOfUnit <$> net.listen d bl
  | .accept4 d fl => rawFdNetOutOfAccepted <$> net.accept4 d fl
  | .connect d sa => rawFdNetOutOfUnit <$> net.connect d sa
  | .getsockopt d opt => rawFdNetOutOfU32 <$> net.getsockopt d opt
  | .setsockopt d opt val => rawFdNetOutOfUnit <$> net.setsockopt d opt val
  | .getsockname d => rawFdNetOutOfAddr <$> net.getsockname d
  | .recvfrom d n fl => rawFdNetOutOfBytes <$> net.recvfrom d n fl
  | .sendto d bs fl => rawFdNetOutOfU32 <$> net.sendto d bs fl
  | .shutdown d how => rawFdNetOutOfUnit <$> net.shutdown d how

/-- Unified raw Linux syscall request dispatched across the 5 `LinuxSyscall` capabilities consumed by `ConnectProxy`. -/
inductive FullRawReq where
  /-- Execute a `LinuxSyscall.Dns` lookup request. -/
  | dns (req : Dns.DnsReq)
  /-- Execute a `LinuxSyscall.TimeRand` clock/sleep/random request. -/
  | timeRand (req : TimeRand.TimeRandReq)
  /-- Close file descriptor `fd` via `LinuxSyscall.Files.close`. -/
  | filesClose (fd : RawFd)
  /-- Execute a `LinuxSyscall.Net` socket request over `RawFd`. -/
  | net (req : RawFdNetReq)
  /-- Execute a `LinuxSyscall.Poll.ppoll` readiness request over `RawFd`. -/
  | pollPpoll (fds : Array (RawFd × Poll.PollEvents)) (timeout : Option Poll.Timespec)

/-- Unified raw Linux syscall outcome paired with `FullRawReq`. -/
inductive FullRawOut where
  /-- Outcome of `dns`. -/
  | dns (out : Dns.DnsOutcome)
  /-- Outcome of `timeRand`. -/
  | timeRand (out : TimeRand.TimeRandOutcome)
  /-- Outcome of `filesClose`. -/
  | filesClose (out : Files.FilesOutcome)
  /-- Outcome of `net`. -/
  | net (out : RawFdNetOut)
  /-- Outcome of `pollPpoll`. -/
  | poll (out : Poll.PollOutcome)

/-- Well-formedness guard on `HealthySysWorld` requiring all 5 Linux syscall subsystem environments to be well-formed. -/
def fullWorldWf (w : HealthySysWorld) : Bool :=
  w.wf

/-- Execute one `FullRawReq` against `sys : FullSysOpsM (StateM W)`. -/
def execFullRawStep {W : Type} (sys : FullSysOpsM (StateM W)) (req : FullRawReq) :
    StateM W FullRawOut :=
  match req with
  | .dns dreq => do
    let r ← Dns.execDnsReq sys.dns dreq
    return .dns r
  | .timeRand treq => do
    let r ← TimeRand.execTimeRandReq sys.timeRand treq
    return .timeRand r
  | .filesClose fd => do
    let r ← sys.files.close fd
    return .filesClose (Files.outcomeOfUnit r)
  | .net nreq => do
    let r ← execRawFdNetReq sys.net nreq
    return .net r
  | .pollPpoll fds to? => do
    let r ← sys.poll.ppoll fds to?
    return .poll (pollOutcomeOfPolled r)

/-- Relational step postcondition tying every `FullRawReq` directly to the canonical
    `LinuxSyscall.{Files,Net,Poll,Dns,TimeRand}.healthyStep` models while preserving `HealthySysWorld.wf`. -/
def allowedFullRawStep (w : HealthySysWorld) (req : FullRawReq)
    (out : FullRawOut) (w' : HealthySysWorld) : Prop :=
  w'.wf = true ∧
  match req, out with
  | .dns dreq, .dns do_ =>
    Dns.healthyStep w.dnsEnv dreq do_ = some w'.dnsEnv
  | .timeRand treq, .timeRand to =>
    TimeRand.healthyStep w.timeEnv treq to = some w'.timeEnv
  | .filesClose _, .filesClose fo =>
    ∃ hid : Nat, Files.healthyStep w.filesEnv (.close hid) fo = some w'.filesEnv
  | .net nreq, .net no =>
    ∃ (toHid : RawFd → Nat) (mo : Net.NetOutcome),
      RawFdNetOut.MatchesModel no mo ∧
      Net.healthyStep w.netEnv (mapRawFdNetReq toHid nreq) mo = some w'.netEnv
  | .pollPpoll fds to?, .poll po =>
    ∃ toHid : RawFd → Nat,
      Poll.healthyStep w.pollEnv (.ppoll (fds.map fun p => (toHid p.1, p.2)) to?) po = some w'.pollEnv
  | _, _ => False

/-- Project a `HealthySysWorld` into `MockProxySimState`, preserving `w.wf` via `ephemeralPort != 0`. -/
def mapFullWorldToSim (w : HealthySysWorld) : MockProxySimState :=
  { ephemeralPort := if w.wf then 49152 else 0 }

/-- End-to-end `HealthySysWorld` step postcondition for `ConnectProxyApiM.withProxy`:
    preserves `HealthySysWorld.wf`, rejects invalid configs with zero OS state change, enforces
    non-empty error messages on startup/teardown failure, and guarantees a non-zero loopback port
    honoring explicit `listenPort`, exact callback return value, and `.allowed → reason = none`
    on every returned `ConnectEvent`. -/
def allowedFullPkgStep (w : HealthySysWorld) (req : ProxyStepReq)
    (out : Except ProxyError (UInt16 × Array ConnectEvent)) (w' : HealthySysWorld) : Prop :=
  w'.wf = true ∧
  match validateConfig req.cfg with
  | .error err => out = .error err ∧ w' = w
  | .ok vcfg =>
    match out with
    | .error err => err.message ≠ ""
    | .ok (val, evs) =>
      ∃ boundPort : UInt16,
        boundPort ≠ 0 ∧
        (vcfg.config.listenPort ≠ 0 → boundPort = vcfg.config.listenPort) ∧
        val = boundPort + req.tag ∧
        ∀ ev ∈ evs.toList, (ev.outcome = .allowed → ev.reason = none)

end LeanSwe.ConnectProxy.Model
