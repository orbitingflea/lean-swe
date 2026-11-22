import LeanSwe.LinuxSyscall.Net.Model.Step

namespace LeanSwe.LinuxSyscall.Net

open LeanSwe.LinuxSyscall

/-- Convert `Except Errno HandleId` into `NetOutcome`. -/
def outcomeOfOpened : Except Errno HandleId → NetOutcome
  | .ok h => .opened h
  | .error e => .err e

/-- Convert `Except Errno (HandleId × HandleId)` into `NetOutcome`. -/
def outcomeOfPair : Except Errno (HandleId × HandleId) → NetOutcome
  | .ok (h0, h1) => .pair h0 h1
  | .error e => .err e

/-- Convert `Except Errno (HandleId × SockAddr)` into `NetOutcome`. -/
def outcomeOfAccepted : Except Errno (HandleId × SockAddr) → NetOutcome
  | .ok (h, sa) => .accepted h sa
  | .error e => .err e

/-- Convert `Except Errno SockAddr` into `NetOutcome`. -/
def outcomeOfAddr : Except Errno SockAddr → NetOutcome
  | .ok sa => .addr sa
  | .error e => .err e

/-- Convert `Except Errno ByteArray` into `NetOutcome`. -/
def outcomeOfBytes : Except Errno ByteArray → NetOutcome
  | .ok bs => .bytes bs
  | .error e => .err e

/-- Convert `Except Errno UInt32` into `NetOutcome`. -/
def outcomeOfU32 : Except Errno UInt32 → NetOutcome
  | .ok v => .u32 v
  | .error e => .err e

/-- Convert `Except Errno Unit` into `NetOutcome`. -/
def outcomeOfUnit : Except Errno Unit → NetOutcome
  | .ok () => .unit
  | .error e => .err e

/-- Convert `Except Errno (Array HandleId)` into `NetOutcome`. -/
def outcomeOfFds : Except Errno (Array HandleId) → NetOutcome
  | .ok fds => .fds fds
  | .error e => .err e

/-- Return `true` iff `out` is a curated catastrophic OS fault (`ENOMEM`, `EIO`, `ENFILE`). -/
def isCriticalFault : NetOutcome → Bool
  | .err e => Errno.isCriticalOsErrno e
  | _ => false

/-- Return `true` iff `out` is an interrupted syscall outcome (`.err Errno.EINTR`). -/
def isEintrOutcome : NetOutcome → Bool
  | .err e => e == Errno.EINTR
  | _ => false

/-- Healthy execution environment wrapping `NetState` with a finite `EINTR` interruption budget (`ambientSeccomp = false`). -/
structure HealthyEnv where
  /-- Underlying `Net` world state. -/
  state : NetState := NetState.initial
  /-- Remaining bound on `EINTR` signal interruptions (`0` forbids `EINTR`). -/
  eintrBudget : Nat := 0
  deriving DecidableEq, BEq, Inhabited

/-- Initial healthy `Net` environment with optional `eintrBudget`. -/
def HealthyEnv.initial (eintrBudget : Nat := 0) : HealthyEnv :=
  { state := NetState.initial, eintrBudget := eintrBudget }

/-- Return `true` iff `env` has no ambient `seccomp` `SECCOMP_RET_ERRNO` filter interception. -/
def HealthyEnv.wf (env : HealthyEnv) : Bool :=
  !env.state.ambientSeccomp

/-- Relational healthy-OS step checker for `LeanSwe.LinuxSyscall.Net`, excluding critical OS faults and ambient `seccomp` while bounding `EINTR` via `eintrBudget`. -/
def healthyStep (env : HealthyEnv) (req : NetReq) (out : NetOutcome) : Option HealthyEnv :=
  if !env.wf || isCriticalFault out then
    none
  else
    match allowedStep env.state req out with
    | none => none
    | some s' =>
      if isEintrOutcome out then
        if env.eintrBudget > 0 then
          some { state := s', eintrBudget := env.eintrBudget - 1 }
        else
          none
      else
        some { state := s', eintrBudget := env.eintrBudget }

/-- Execute one `NetReq` against a `NetOpsM m HandleId` capability bundle and decode its `NetOutcome`. -/
def execNetReq {m : Type → Type} [Monad m]
    (ops : NetOpsM m HandleId) : NetReq → m NetOutcome
  | .socket dom st fl p => outcomeOfOpened <$> ops.socket dom st fl p
  | .socketpair dom st fl => outcomeOfPair <$> ops.socketpair dom st fl
  | .bind h sa => outcomeOfUnit <$> ops.bind h sa
  | .listen h bl => outcomeOfUnit <$> ops.listen h bl
  | .accept4 h fl => outcomeOfAccepted <$> ops.accept4 h fl
  | .connect h sa => outcomeOfUnit <$> ops.connect h sa
  | .getsockopt h opt => outcomeOfU32 <$> ops.getsockopt h opt
  | .setsockopt h opt val => outcomeOfUnit <$> ops.setsockopt h opt val
  | .getsockname h => outcomeOfAddr <$> ops.getsockname h
  | .recvfrom h n fl => outcomeOfBytes <$> ops.recvfrom h n fl
  | .sendto h bs fl => outcomeOfU32 <$> ops.sendto h bs fl
  | .shutdown h how => outcomeOfUnit <$> ops.shutdown h how
  | .sendmsg h fds => outcomeOfUnit <$> ops.sendmsg h fds
  | .recvmsg h maxFds => outcomeOfFds <$> ops.recvmsg h maxFds
  | .ioctl h op ifn => outcomeOfU32 <$> ops.ioctl h op ifn

/-- Universal healthy-world refinement predicate over an arbitrary state `W` projected via `proj`. -/
def RefinesHealthyNetAt {W : Type} (proj : W → HealthyEnv)
    (ops : NetOpsM (StateM W) HandleId) : Prop :=
  ∀ (w : W) (req : NetReq),
    (proj w).wf = true →
    let (out, w') := (execNetReq ops req).run w
    healthyStep (proj w) req out = some (proj w')

/-- Direct healthy-world refinement predicate specialized to `StateM HealthyEnv`. -/
abbrev RefinesHealthyNet (ops : NetOpsM (StateM HealthyEnv) HandleId) : Prop :=
  RefinesHealthyNetAt id ops

end LeanSwe.LinuxSyscall.Net
