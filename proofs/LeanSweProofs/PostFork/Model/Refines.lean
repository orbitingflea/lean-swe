import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Types.Internal
import LeanSweProofs.PostFork.Model

/-!
Pure capability-refinement specification for `LeanSwe.PostFork` (`Core.ObeysStepFrom`),
relating single-syscall `PosixHostOpsM` host hooks over `HostStepState` to `PostForkOpsM`.
Contains zero `Aeneas` or `Mathlib` dependencies so `import LeanSwe` remains clean.
-/

namespace LeanSwe.PostFork.Model

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

/-- Maximum valid 31-bit signed positive Linux PID (`2147483647`). -/
def maxLinuxPid : Pid := 0x7fffffff

/-- Monadic raw host capability bundle specialized to `Nat` handles for `Core.ObeysStepFrom`. -/
abbrev RawHostOpsM (m : Type → Type) :=
  LeanSwe.PostFork.Impl.Internal.PosixHostOpsM m Nat

/-- Monadic public `PostFork` capability bundle specialized to `Nat` handles for `Core.ObeysStepFrom`. -/
abbrev PkgPostForkOpsM (m : Type → Type) :=
  PostForkOpsM m Nat

/-- Pure host step state tracking fresh `O_CLOEXEC` pipe handle allocation and PID validity. -/
structure HostStepState where
  /-- Monotonic lower bound on freshly allocated `O_CLOEXEC` pipe handle IDs (`>= 3`). -/
  nextHandle : Nat := 3
  /-- Most recently observed valid Linux PID (`1..maxLinuxPid`). -/
  lastPid : Pid := 100
  /-- Whether the host kernel environment is within the healthy non-`EFAULT` envelope. -/
  healthyHost : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Well-formedness guard on `HostStepState` for `Core.ObeysStepFrom`. -/
def rawStepWf (s : HostStepState) : Bool :=
  s.healthyHost && decide (3 ≤ s.nextHandle ∧ 1 ≤ s.lastPid ∧ s.lastPid ≤ maxLinuxPid)

/-- Single-step raw host FFI request covering all 9 fields of `PosixHostOpsM`. -/
inductive RawStepReq where
  /-- `raw.probeFdOpen fd`. -/
  | probeFdOpen (fd : Int32)
  /-- `raw.probeHandleOpen h`. -/
  | probeHandleOpen (h : Nat)
  /-- `raw.mkPipeCloexec`. -/
  | mkPipeCloexec
  /-- `raw.closeFd h`. -/
  | closeFd (h : Nat)
  /-- `raw.setpgidOnce pid pgid`. -/
  | setpgidOnce (pid : Pid) (pgid : Pid)
  /-- `raw.writeOnce h data off len`. -/
  | writeOnce (h : Nat) (data : ByteArray) (off : UInt64) (len : UInt64)
  /-- `raw.readOnce h maxBytes`. -/
  | readOnce (h : Nat) (maxBytes : UInt64)
  /-- `raw.waitOnce pid`. -/
  | waitOnce (pid : Pid)
  /-- `raw.forkRun flags forkMode syncRead? errWrite stdioRefs closeRefs keepRefs cwd path argv envEntries`. -/
  | forkRun
      (flags : UInt32) (forkMode : ForkMode) (syncRead? : Option Nat) (errWrite : Nat)
      (stdioRefs : Array (FdRef Nat)) (closeRefs : Array (FdRef Nat))
      (keepRefs : Array (FdRef Nat)) (cwd : Option String) (path : String)
      (argv : Array (ArgToken Nat)) (envEntries : Array ByteArray)
  deriving BEq, DecidableEq, Inhabited

/-- Single-step output sum for `RawStepReq` transitions in `Core.ObeysStepFrom`. -/
inductive RawStepOut where
  /-- Unit-returning raw call (`probeFdOpen`, `probeHandleOpen`, `closeFd`, `setpgidOnce`). -/
  | unit (res : Except Errno Unit)
  /-- Newly allocated `(readEnd, writeEnd)` handle pair from `mkPipeCloexec`. -/
  | pipe (res : Except Errno (Nat × Nat))
  /-- Byte-count outcome from `writeOnce`. -/
  | u64 (res : Except Errno UInt64)
  /-- Read-chunk outcome from `readOnce`. -/
  | bytes (res : Except Errno ByteArray)
  /-- Reaped child termination status from `waitOnce`. -/
  | wait (res : Except Errno ChildWaitStatus)
  /-- Forked child PID from `forkRun`. -/
  | pid (res : Except Errno Pid)
  deriving Inhabited

/-- Execute one `RawStepReq` against `raw : RawHostOpsM (StateM W)`. -/
def execRawStep {W : Type} (raw : RawHostOpsM (StateM W)) :
    RawStepReq → StateM W RawStepOut
  | .probeFdOpen fd => .unit <$> raw.probeFdOpen fd
  | .probeHandleOpen h => .unit <$> raw.probeHandleOpen h
  | .mkPipeCloexec => .pipe <$> raw.mkPipeCloexec
  | .closeFd h => .unit <$> raw.closeFd h
  | .setpgidOnce pid pgid => .unit <$> raw.setpgidOnce pid pgid
  | .writeOnce h data off len => .u64 <$> raw.writeOnce h data off len
  | .readOnce h maxBytes => .bytes <$> raw.readOnce h maxBytes
  | .waitOnce pid => .wait <$> raw.waitOnce pid
  | .forkRun flags forkMode syncRead? errWrite stdioRefs closeRefs keepRefs cwd path argv envp =>
    .pid <$> raw.forkRun flags forkMode syncRead? errWrite stdioRefs closeRefs keepRefs
      cwd path argv envp

/-- Prop-valued validity of a reaped Linux `ChildWaitStatus` (`exited 0..255` or `signaled 1..64`). -/
def validWaitStatusProp : ChildWaitStatus → Prop
  | .exited code => code ≤ 255
  | .signaled sig => 1 ≤ sig ∧ sig ≤ 64

/-- Prop-valued range check on raw Linux `Errno` values (`1..4095`). -/
def validHostErrnoProp (e : Errno) : Prop :=
  1 ≤ e.toNat ∧ e.toNat ≤ 4095

/-- Allowed healthy-host transition for a single `PosixHostOpsM` primitive call. -/
def allowedRawStep (s : HostStepState) (req : RawStepReq) (out : RawStepOut)
    (s' : HostStepState) : Prop :=
  rawStepWf s = true ∧
  rawStepWf s' = true ∧
  s.nextHandle ≤ s'.nextHandle ∧
  match req, out with
  | .probeFdOpen _, .unit (.ok ()) => True
  | .probeFdOpen _, .unit (.error e) => validHostErrnoProp e
  | .probeHandleOpen _, .unit (.ok ()) => True
  | .probeHandleOpen _, .unit (.error e) => validHostErrnoProp e
  | .mkPipeCloexec, .pipe (.ok p) =>
    p.1 ≠ p.2 ∧ s.nextHandle ≤ p.1 ∧ s.nextHandle ≤ p.2 ∧
      p.1 < s'.nextHandle ∧ p.2 < s'.nextHandle
  | .mkPipeCloexec, .pipe (.error e) => validHostErrnoProp e
  | .closeFd _, .unit (.ok ()) => True
  | .closeFd _, .unit (.error e) => validHostErrnoProp e
  | .setpgidOnce _ _, .unit (.ok ()) => True
  | .setpgidOnce _ _, .unit (.error e) => validHostErrnoProp e
  | .writeOnce _ _ _ len, .u64 (.ok n) => n.toNat ≤ len.toNat
  | .writeOnce _ _ _ _, .u64 (.error e) => validHostErrnoProp e
  | .readOnce _ maxBytes, .bytes (.ok bs) => bs.size ≤ maxBytes.toNat
  | .readOnce _ _, .bytes (.error e) => validHostErrnoProp e
  | .waitOnce _, .wait (.ok wst) => validWaitStatusProp wst
  | .waitOnce _, .wait (.error e) => validHostErrnoProp e
  | .forkRun _ _ _ _ _ _ _ _ _ _ _, .pid (.ok pid) =>
    1 ≤ pid ∧ pid ≤ maxLinuxPid ∧ s'.lastPid = pid
  | .forkRun _ _ _ _ _ _ _ _ _ _ _, .pid (.error e) => validHostErrnoProp e
  | _, _ => False

/-- Single-step request sum covering all 4 public operations of `PostForkOpsM`. -/
inductive PkgStepReq where
  /-- `ops.spawn spec`. -/
  | spawn (spec : ChildSpecM Nat)
  /-- `ops.spawnWithBarrier spec`. -/
  | spawnWithBarrier (spec : ChildSpecM Nat)
  /-- `ops.releaseBarrier pending`. -/
  | releaseBarrier (pending : PendingChildM Nat)
  /-- `ops.abortBarrier pending`. -/
  | abortBarrier (pending : PendingChildM Nat)
  deriving BEq, DecidableEq

/-- Single-step output sum for `PkgStepReq` transitions in `Core.ObeysStepFrom`. -/
inductive PkgStepOut where
  /-- Live-child outcome returned by `spawn` or `releaseBarrier`. -/
  | spawned (res : Except PostForkError SpawnedChild)
  /-- Barrier-paused child outcome returned by `spawnWithBarrier`. -/
  | pending (res : Except PostForkError (PendingChildM Nat))
  /-- Reaped barrier-abort outcome returned by `abortBarrier`. -/
  | aborted (res : Except PostForkError AbortOutcome)
  deriving Inhabited

/-- Execute one `PkgStepReq` against `ops : PkgPostForkOpsM (StateM W)`. -/
def execPkgStep {W : Type} (ops : PkgPostForkOpsM (StateM W)) :
    PkgStepReq → StateM W PkgStepOut
  | .spawn spec => .spawned <$> ops.spawn spec
  | .spawnWithBarrier spec => .pending <$> ops.spawnWithBarrier spec
  | .releaseBarrier pending => .spawned <$> ops.releaseBarrier pending
  | .abortBarrier pending => .aborted <$> ops.abortBarrier pending

/-- Compute the expected `SpawnedChild.pgid` / `PendingChildM.pgid` for `policy` and `pid`. -/
def expectedPgid (policy : ProcessGroupPolicy) (pid : Pid) : Option Pid :=
  match policy with
  | .newGroup => some pid
  | .inherit => none

/-- Prop-valued well-formedness of a pure pre-`fork` `.invalidInput` `PostForkError`. -/
def validInvalidErrProp (err : PostForkError) : Prop :=
  err.kind = .invalidInput ∧ err.errno = none ∧ err.childFailure = none ∧ !err.message.isEmpty = true

/-- Prop-valued well-formedness of a host `.sysError` `PostForkError`. -/
def validSysErrProp (err : PostForkError) : Prop :=
  err.kind = .sysError ∧ err.childFailure = none ∧ !err.message.isEmpty = true ∧
    ∃ code, err.errno = some code ∧ validHostErrnoProp code

/-- Prop-valued well-formedness of a runtime `.sysError` or reaped `.childFailed` `PostForkError`. -/
def validRuntimeErrProp (err : PostForkError) : Prop :=
  validSysErrProp err ∨
    (err.kind = .childFailed ∧ !err.message.isEmpty = true ∧
      ∃ cf wst,
        err.childFailure = some cf ∧
        err.errno = some cf.errno ∧
        cf.waitStatus = some wst ∧
        validWaitStatusProp wst ∧
        validHostErrnoProp cf.errno)

/-- Allowed healthy-host transition for all 4 public `PostForkOpsM` operations. -/
def allowedPkgStep (s : HostStepState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : HostStepState) : Prop :=
  rawStepWf s = true ∧
  rawStepWf s' = true ∧
  s.nextHandle ≤ s'.nextHandle ∧
  match req, out with
  | .spawn spec, .spawned res =>
    if !validateSpec spec then
      s' = s ∧
        match res with
        | .error err => validInvalidErrProp err
        | .ok _ => False
    else
      match res with
      | .ok ch =>
        1 ≤ ch.pid ∧ ch.pid ≤ maxLinuxPid ∧ ch.pgid = expectedPgid spec.processGroup ch.pid
      | .error err => validRuntimeErrProp err
  | .spawnWithBarrier spec, .pending res =>
    if !validateSpec spec then
      s' = s ∧
        match res with
        | .error err => validInvalidErrProp err
        | .ok _ => False
    else
      match res with
      | .ok pend =>
        1 ≤ pend.pid ∧ pend.pid ≤ maxLinuxPid ∧
          pend.pgid = expectedPgid spec.processGroup pend.pid ∧
          pend.syncWrite ≠ pend.errRead ∧
          s.nextHandle ≤ pend.errRead ∧ pend.syncWrite < s'.nextHandle
      | .error err => validSysErrProp err
  | .releaseBarrier pending, .spawned res =>
    match res with
    | .ok ch => ch.pid = pending.pid ∧ ch.pgid = pending.pgid
    | .error err => validRuntimeErrProp err
  | .abortBarrier _, .aborted res =>
    match res with
    | .ok (.aborted wst) => validWaitStatusProp wst
    | .ok (.failedBeforeBarrier cf wst) =>
      validWaitStatusProp wst ∧ cf.waitStatus = some wst ∧ validHostErrnoProp cf.errno
    | .error err => validSysErrProp err
  | _, _ => False

/-- Deterministic pure reference `RawHostOpsM (StateM HostStepState)` witnessing `allowedRawStep`. -/
def modelRawOps : RawHostOpsM (StateM HostStepState) where
  probeFdOpen fd :=
    if decide (0 ≤ fd.toInt) then pure (.ok ()) else pure (.error Errno.EBADF)
  probeHandleOpen _ := pure (.ok ())
  mkPipeCloexec := do
    let s ← get
    let rFd := s.nextHandle
    let wFd := s.nextHandle + 1
    set { s with nextHandle := s.nextHandle + 2 }
    pure (.ok (rFd, wFd))
  closeFd _ := pure (.ok ())
  setpgidOnce _ _ := pure (.ok ())
  writeOnce _ _ _ len := pure (.ok len)
  readOnce _ _ := pure (.ok ByteArray.empty)
  waitOnce _ := pure (.ok (.exited 0))
  forkRun _ _ _ _ _ _ _ _ _ _ _ := do
    let s ← get
    let pid : Pid := 100
    set { s with lastPid := pid }
    pure (.ok pid)

end LeanSwe.PostFork.Model
