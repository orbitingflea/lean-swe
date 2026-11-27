import LeanSweProofs.LinuxSyscall.Net.Model

/-!
# Capability-Parametric Refinement Model for `LeanSwe.LinuxSyscall.Net`

Defines portable C-ABI wire decoders, the raw `PosixNetOpsM` single-step
contract (`RawNetOpsM`, `RawNetReq`, `RawNetOut`, `execRawStep`,
`allowedRawStep`, `rawHealthyModelOps`), and package-level `HandleId`
single-step entry points (`HandleNetOpsM`, `healthyModelOps`, `execPkgStep`,
`allowedPkgStep`) over `HealthyEnv`.
-/

namespace LeanSwe.LinuxSyscall.Net.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Monad-parameterized raw C-ABI `Net` capability family specialized to `HandleId`. -/
abbrev RawNetOpsM (m : Type → Type) : Type :=
  PosixNetOpsM m HandleId

/-- Monad-parameterized public `Net` capability family specialized to `HandleId`. -/
abbrev HandleNetOpsM (m : Type → Type) : Type :=
  NetOpsM m HandleId

/-- Decode portable `SockDomain` tag (`0 = inet`, `1 = inet6`, `2 = unix`). -/
def decodeRawSockDomain? : UInt32 → Option SockDomain
  | 0 => some .inet
  | 1 => some .inet6
  | 2 => some .unix
  | _ => none

/-- Decode portable `SockType` tag (`0 = stream`, `1 = dgram`, `2 = seqpacket`). -/
def decodeRawSockType? : UInt32 → Option SockType
  | 0 => some .stream
  | 1 => some .dgram
  | 2 => some .seqpacket
  | _ => none

/-- Decode portable 2-bit `SockFlags` bitmask (`0..3`). -/
def decodeRawSockFlags? (bits : UInt32) : Option SockFlags :=
  if bits < 4 then
    some { nonblock := (bits &&& 1) != 0
           cloexec := (bits &&& 2) != 0 }
  else
    none

/-- Decode portable `SockOpt` tag (`0 = error`, `1 = reuseAddr`). -/
def decodeRawSockOpt? : UInt32 → Option SockOpt
  | 0 => some .error
  | 1 => some .reuseAddr
  | _ => none

/-- Decode portable `SetSockOpt` tag (`0 = reuseAddr`). -/
def decodeRawSetSockOpt? : UInt32 → Option SetSockOpt
  | 0 => some .reuseAddr
  | _ => none

/-- Decode portable 3-bit `MsgFlags` bitmask (`0..7`). -/
def decodeRawMsgFlags? (bits : UInt32) : Option MsgFlags :=
  if bits < 8 then
    some { nosignal := (bits &&& 1) != 0
           dontwait := (bits &&& 2) != 0
           peek := (bits &&& 4) != 0 }
  else
    none

/-- Decode portable `ShutHow` tag (`0 = rd`, `1 = wr`, `2 = rdwr`). -/
def decodeRawShutHow? : UInt32 → Option ShutHow
  | 0 => some .rd
  | 1 => some .wr
  | 2 => some .rdwr
  | _ => none

/-- Decode portable `(opTag, arg)` pair into `NetIoctlOp`. -/
def decodeRawNetIoctlOp? (tag arg : UInt32) : Option NetIoctlOp :=
  match tag with
  | 0 => if arg == 0 then some .getIfFlags else none
  | 1 => some (.setIfFlags arg)
  | _ => none

/-- Single-step request sum for `PosixNetOpsM` C-ABI syscall hooks. -/
inductive RawNetReq where
  /-- Raw `socket(domainTag, typeTag, sockFlagBits, proto)`. -/
  | socket (domainTag : UInt32) (typeTag : UInt32) (sockFlagBits : UInt32) (proto : UInt32)
  /-- Raw `socketpair(domainTag, typeTag, sockFlagBits)`. -/
  | socketpair (domainTag : UInt32) (typeTag : UInt32) (sockFlagBits : UInt32)
  /-- Raw `bind(hid, rawAddr)`. -/
  | bind (hid : HandleId) (rawAddr : RawSockAddrTuple)
  /-- Raw `listen(hid, backlog)`. -/
  | listen (hid : HandleId) (backlog : UInt32)
  /-- Raw `accept4(hid, sockFlagBits)`. -/
  | accept4 (hid : HandleId) (sockFlagBits : UInt32)
  /-- Raw `connect(hid, rawAddr)`. -/
  | connect (hid : HandleId) (rawAddr : RawSockAddrTuple)
  /-- Raw `getsockopt(hid, sockOptTag)`. -/
  | getsockopt (hid : HandleId) (sockOptTag : UInt32)
  /-- Raw `setsockopt(hid, setSockOptTag, val)`. -/
  | setsockopt (hid : HandleId) (setSockOptTag : UInt32) (val : UInt32)
  /-- Raw `getsockname(hid)`. -/
  | getsockname (hid : HandleId)
  /-- Raw `recvfrom(hid, maxBytes, msgFlagBits)`. -/
  | recvfrom (hid : HandleId) (maxBytes : UInt32) (msgFlagBits : UInt32)
  /-- Raw `sendto(hid, data, msgFlagBits)`. -/
  | sendto (hid : HandleId) (data : ByteArray) (msgFlagBits : UInt32)
  /-- Raw `shutdown(hid, shutHowTag)`. -/
  | shutdown (hid : HandleId) (shutHowTag : UInt32)
  /-- Raw `sendmsg(hid, fds)`. -/
  | sendmsg (hid : HandleId) (fds : Array HandleId)
  /-- Raw `recvmsg(hid, maxFds)`. -/
  | recvmsg (hid : HandleId) (maxFds : UInt32)
  /-- Raw `ioctl(hid, opTag, flagsArg, ifname)`. -/
  | ioctl (hid : HandleId) (opTag : UInt32) (flagsArg : UInt32) (ifname : ByteArray)
  deriving Repr, Inhabited

/-- Single-step output sum for `PosixNetOpsM` C-ABI syscall hooks. -/
inductive RawNetOut where
  /-- `socket` succeeded returning `hid`. -/
  | opened (hid : HandleId)
  /-- `socketpair` succeeded returning `(hid0, hid1)`. -/
  | pair (hid0 hid1 : HandleId)
  /-- `accept4` succeeded returning `(hid, rawSa)`. -/
  | accepted (hid : HandleId) (rawSa : RawSockAddrTuple)
  /-- `getsockname` succeeded returning `rawSa`. -/
  | rawAddr (rawSa : RawSockAddrTuple)
  /-- `recvfrom` succeeded returning `data`. -/
  | bytes (data : ByteArray)
  /-- `getsockopt`, `sendto`, or `ioctl` succeeded returning `val`. -/
  | u32 (val : UInt32)
  /-- `recvmsg` succeeded returning `handles`. -/
  | fds (handles : Array HandleId)
  /-- Unit-returning syscall succeeded. -/
  | unit
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr, Inhabited

/-- Wrap `Except Errno HandleId` into `RawNetOut`. -/
def outcomeOfRawOpened : Except Errno HandleId → RawNetOut
  | .ok h => .opened h
  | .error e => .err e

/-- Wrap `Except Errno (HandleId × HandleId)` into `RawNetOut`. -/
def outcomeOfRawPair : Except Errno (HandleId × HandleId) → RawNetOut
  | .ok (h0, h1) => .pair h0 h1
  | .error e => .err e

/-- Wrap `Except Errno (HandleId × RawSockAddrTuple)` into `RawNetOut`. -/
def outcomeOfRawAccepted : Except Errno (HandleId × RawSockAddrTuple) → RawNetOut
  | .ok (h, rawSa) => .accepted h rawSa
  | .error e => .err e

/-- Wrap `Except Errno RawSockAddrTuple` into `RawNetOut`. -/
def outcomeOfRawAddr : Except Errno RawSockAddrTuple → RawNetOut
  | .ok rawSa => .rawAddr rawSa
  | .error e => .err e

/-- Wrap `Except Errno ByteArray` into `RawNetOut`. -/
def outcomeOfRawBytes : Except Errno ByteArray → RawNetOut
  | .ok bs => .bytes bs
  | .error e => .err e

/-- Wrap `Except Errno UInt32` into `RawNetOut`. -/
def outcomeOfRawU32 : Except Errno UInt32 → RawNetOut
  | .ok v => .u32 v
  | .error e => .err e

/-- Wrap `Except Errno (Array HandleId)` into `RawNetOut`. -/
def outcomeOfRawFds : Except Errno (Array HandleId) → RawNetOut
  | .ok hs => .fds hs
  | .error e => .err e

/-- Wrap `Except Errno Unit` into `RawNetOut`. -/
def outcomeOfRawUnit : Except Errno Unit → RawNetOut
  | .ok () => .unit
  | .error e => .err e

/-- Convert a `RawNetOut` into its domain `NetOutcome`. -/
def toModelOutcome : RawNetOut → NetOutcome
  | .opened h => .opened h
  | .pair h0 h1 => .pair h0 h1
  | .accepted h rawSa => .accepted h (SockAddr.ofRawTuple rawSa)
  | .rawAddr rawSa => .addr (SockAddr.ofRawTuple rawSa)
  | .bytes bs => .bytes bs
  | .u32 v => .u32 v
  | .fds hs => .fds hs
  | .unit => .unit
  | .err e => .err e

/-- Decode a `RawNetReq` into its domain `NetReq` if all wire tags/flags are portable. -/
def decodeRawNetReq? : RawNetReq → Option NetReq
  | .socket domTag stTag flBits proto =>
    match decodeRawSockDomain? domTag, decodeRawSockType? stTag, decodeRawSockFlags? flBits with
    | some dom, some st, some fl => some (.socket dom st fl proto)
    | _, _, _ => none
  | .socketpair domTag stTag flBits =>
    match decodeRawSockDomain? domTag, decodeRawSockType? stTag, decodeRawSockFlags? flBits with
    | some dom, some st, some fl => some (.socketpair dom st fl)
    | _, _, _ => none
  | .bind hid rawSa => some (.bind hid (SockAddr.ofRawTuple rawSa))
  | .listen hid backlog => some (.listen hid backlog)
  | .accept4 hid flBits => (decodeRawSockFlags? flBits).map (NetReq.accept4 hid ·)
  | .connect hid rawSa => some (.connect hid (SockAddr.ofRawTuple rawSa))
  | .getsockopt hid optTag => (decodeRawSockOpt? optTag).map (NetReq.getsockopt hid ·)
  | .setsockopt hid optTag val =>
    (decodeRawSetSockOpt? optTag).map (NetReq.setsockopt hid · val)
  | .getsockname hid => some (.getsockname hid)
  | .recvfrom hid maxBytes mfBits =>
    (decodeRawMsgFlags? mfBits).map (NetReq.recvfrom hid maxBytes ·)
  | .sendto hid data mfBits =>
    (decodeRawMsgFlags? mfBits).map (NetReq.sendto hid data ·)
  | .shutdown hid howTag => (decodeRawShutHow? howTag).map (NetReq.shutdown hid ·)
  | .sendmsg hid fds => some (.sendmsg hid fds)
  | .recvmsg hid maxFds => some (.recvmsg hid maxFds)
  | .ioctl hid opTag arg ifn =>
    (decodeRawNetIoctlOp? opTag arg).map (NetReq.ioctl hid · ifn)

/-- Execute one `RawNetReq` against a `RawNetOpsM (StateM W)` bundle. -/
def execRawStep {W : Type} (raw : RawNetOpsM (StateM W)) :
    RawNetReq → StateM W RawNetOut
  | .socket d t fl p => outcomeOfRawOpened <$> raw.socket d t fl p
  | .socketpair d t fl => outcomeOfRawPair <$> raw.socketpair d t fl
  | .bind h sa => outcomeOfRawUnit <$> raw.bind h sa
  | .listen h bl => outcomeOfRawUnit <$> raw.listen h bl
  | .accept4 h fl => outcomeOfRawAccepted <$> raw.accept4 h fl
  | .connect h sa => outcomeOfRawUnit <$> raw.connect h sa
  | .getsockopt h opt => outcomeOfRawU32 <$> raw.getsockopt h opt
  | .setsockopt h opt val => outcomeOfRawUnit <$> raw.setsockopt h opt val
  | .getsockname h => outcomeOfRawAddr <$> raw.getsockname h
  | .recvfrom h n fl => outcomeOfRawBytes <$> raw.recvfrom h n fl
  | .sendto h bs fl => outcomeOfRawU32 <$> raw.sendto h bs fl
  | .shutdown h how => outcomeOfRawUnit <$> raw.shutdown h how
  | .sendmsg h fds => outcomeOfRawUnit <$> raw.sendmsg h fds
  | .recvmsg h maxFds => outcomeOfRawFds <$> raw.recvmsg h maxFds
  | .ioctl h tg ag ifn => outcomeOfRawU32 <$> raw.ioctl h tg ag ifn

/-- Allowed single-step relation for `PosixNetOpsM` over `HealthyEnv`. -/
def allowedRawStep (env : HealthyEnv) (req : RawNetReq) (out : RawNetOut)
    (env' : HealthyEnv) : Prop :=
  match decodeRawNetReq? req with
  | some nreq => healthyStep env nreq (toModelOutcome out) = some env'
  | none => out = .err Errno.EINVAL ∧ env' = env

/-- Chosen non-critical, non-`EINTR`, non-`soError` fallback errno (`ENOSPC` or `ENOBUFS`). -/
def chosenSockFallbackErrno (soErr : Errno) : Errno :=
  if soErr == Errno.ENOSPC then Errno.ENOBUFS else Errno.ENOSPC

/-- Non-critical, non-`EINTR` fallback errno accepted by `healthyStep` on any `NetState`. -/
def fallbackNetErrno (s : NetState) (req : NetReq) : Errno :=
  match preCheckNet req with
  | some err => err
  | none =>
    let sockErr (hid : HandleId) : Errno :=
      match lookupHandleFileId s hid with
      | none => Errno.EBADF
      | some fid =>
        match lookupFileSocket s fid with
        | .error fdErr => fdErr
        | .ok d => chosenSockFallbackErrno d.soError
    match req with
    | .socket .. | .socketpair .. => Errno.ENOSPC
    | .sendmsg hid fds =>
      match lookupHandleFileId s hid with
      | none => Errno.EBADF
      | some fid =>
        if !fds.toList.all (isLiveHandle s) then Errno.EBADF
        else
          match lookupFileSocket s fid with
          | .error fdErr => fdErr
          | .ok d => chosenSockFallbackErrno d.soError
    | .ioctl hid _ _ =>
      match lookupHandleFileId s hid with
      | none => Errno.EBADF
      | some fid =>
        match lookupFileSocket s fid with
        | .error fdErr => if fdErr == Errno.ENOTSOCK then Errno.ENOTTY else fdErr
        | .ok _ => Errno.ENOSPC
    | .bind hid _ | .listen hid _ | .accept4 hid _ | .connect hid _
    | .getsockopt hid _ | .setsockopt hid _ _ | .getsockname hid
    | .recvfrom hid _ _ | .sendto hid _ _ | .shutdown hid _
    | .recvmsg hid _ => sockErr hid

/-- Run `stepNetCore` over `HealthyEnv`, falling back to `fallbackNetErrno` if needed. -/
def runHealthyNetOp {α : Type}
    (req : NetReq)
    (pack : Except Errno α → NetOutcome)
    (unpack : NetOutcome → Option (Except Errno α)) :
    StateM HealthyEnv (Except Errno α) := fun env =>
  let fbErr := fallbackNetErrno env.state req
  let runFb (_ : Unit) : Except Errno α × HealthyEnv :=
    match healthyStep env req (.err fbErr) with
    | some envFb => (.error fbErr, envFb)
    | none => (.error fbErr, env)
  match stepNetCore env.state req none with
  | some (candOut, _) =>
    match unpack candOut with
    | some candRes =>
      match healthyStep env req (pack candRes) with
      | some env' => if env'.wf then (candRes, env') else runFb ()
      | none => runFb ()
    | none => runFb ()
  | none => runFb ()

/-- Reference `HandleNetOpsM (StateM HealthyEnv)` satisfying `healthyStep` from every well-formed `HealthyEnv`. -/
def healthyModelOps : HandleNetOpsM (StateM HealthyEnv) :=
  { socket := fun dom st fl p =>
      runHealthyNetOp (.socket dom st fl p) outcomeOfOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none)
    socketpair := fun dom st fl =>
      runHealthyNetOp (.socketpair dom st fl) outcomeOfPair
        (fun | .pair a b => some (.ok (a, b)) | .err e => some (.error e) | _ => none)
    bind := fun h sa =>
      runHealthyNetOp (.bind h sa) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    listen := fun h bl =>
      runHealthyNetOp (.listen h bl) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    accept4 := fun h fl =>
      runHealthyNetOp (.accept4 h fl) outcomeOfAccepted
        (fun | .accepted c sa => some (.ok (c, sa)) | .err e => some (.error e) | _ => none)
    connect := fun h sa =>
      runHealthyNetOp (.connect h sa) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    getsockopt := fun h opt =>
      runHealthyNetOp (.getsockopt h opt) outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    setsockopt := fun h opt val =>
      runHealthyNetOp (.setsockopt h opt val) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    getsockname := fun h =>
      runHealthyNetOp (.getsockname h) outcomeOfAddr
        (fun | .addr sa => some (.ok sa) | .err e => some (.error e) | _ => none)
    recvfrom := fun h n fl =>
      runHealthyNetOp (.recvfrom h n fl) outcomeOfBytes
        (fun | .bytes bs => some (.ok bs) | .err e => some (.error e) | _ => none)
    sendto := fun h bs fl =>
      runHealthyNetOp (.sendto h bs fl) outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    shutdown := fun h how =>
      runHealthyNetOp (.shutdown h how) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    sendmsg := fun h fds =>
      runHealthyNetOp (.sendmsg h fds) outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    recvmsg := fun h mf =>
      runHealthyNetOp (.recvmsg h mf) outcomeOfFds
        (fun | .fds fs => some (.ok fs) | .err e => some (.error e) | _ => none)
    ioctl := fun h op ifn =>
      runHealthyNetOp (.ioctl h op ifn) outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none) }

/-- Reference `RawNetOpsM (StateM HealthyEnv)` witness satisfying `allowedRawStep`. -/
def rawHealthyModelOps : RawNetOpsM (StateM HealthyEnv) :=
  { socket := fun domTag stTag flBits proto =>
      match decodeRawSockDomain? domTag, decodeRawSockType? stTag, decodeRawSockFlags? flBits with
      | some dom, some st, some fl => healthyModelOps.socket dom st fl proto
      | _, _, _ => pure (.error Errno.EINVAL)
    socketpair := fun domTag stTag flBits =>
      match decodeRawSockDomain? domTag, decodeRawSockType? stTag, decodeRawSockFlags? flBits with
      | some dom, some st, some fl => healthyModelOps.socketpair dom st fl
      | _, _, _ => pure (.error Errno.EINVAL)
    bind := fun h rawSa => healthyModelOps.bind h (SockAddr.ofRawTuple rawSa)
    listen := healthyModelOps.listen
    accept4 := fun h flBits =>
      match decodeRawSockFlags? flBits with
      | some fl => do
        match ← healthyModelOps.accept4 h fl with
        | .ok (cfd, sa) => return .ok (cfd, sa.toRawTuple)
        | .error e => return .error e
      | none => pure (.error Errno.EINVAL)
    connect := fun h rawSa => healthyModelOps.connect h (SockAddr.ofRawTuple rawSa)
    getsockopt := fun h optTag =>
      match decodeRawSockOpt? optTag with
      | some opt => healthyModelOps.getsockopt h opt
      | none => pure (.error Errno.EINVAL)
    setsockopt := fun h optTag val =>
      match decodeRawSetSockOpt? optTag with
      | some opt => healthyModelOps.setsockopt h opt val
      | none => pure (.error Errno.EINVAL)
    getsockname := fun h => do
      match ← healthyModelOps.getsockname h with
      | .ok sa => return .ok sa.toRawTuple
      | .error e => return .error e
    recvfrom := fun h maxBytes mfBits =>
      match decodeRawMsgFlags? mfBits with
      | some mf => healthyModelOps.recvfrom h maxBytes mf
      | none => pure (.error Errno.EINVAL)
    sendto := fun h data mfBits =>
      match decodeRawMsgFlags? mfBits with
      | some mf => healthyModelOps.sendto h data mf
      | none => pure (.error Errno.EINVAL)
    shutdown := fun h howTag =>
      match decodeRawShutHow? howTag with
      | some how => healthyModelOps.shutdown h how
      | none => pure (.error Errno.EINVAL)
    sendmsg := healthyModelOps.sendmsg
    recvmsg := healthyModelOps.recvmsg
    ioctl := fun h opTag arg ifn =>
      match decodeRawNetIoctlOp? opTag arg with
      | some op => healthyModelOps.ioctl h op ifn
      | none => pure (.error Errno.EINVAL) }

/-- Execute one `NetReq` against a `HandleNetOpsM (StateM W)` capability bundle. -/
def execPkgStep {W : Type} (ops : HandleNetOpsM (StateM W)) (req : NetReq) :
    StateM W NetOutcome :=
  execNetReq ops req

/-- Allowed single-step relation for `NetOpsM` over `HealthyEnv`. -/
def allowedPkgStep (env : HealthyEnv) (req : NetReq) (out : NetOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

end LeanSwe.LinuxSyscall.Net.Model
