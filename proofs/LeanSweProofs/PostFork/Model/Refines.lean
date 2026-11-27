import LeanSwe.PostFork.Types
import LeanSweProofs.PostFork.Model

/-!
External-boundary capability-refinement specification for `LeanSwe.PostFork` (`Core.ObeysStepFrom`),
relating the single-shot `RawSpawnOpsM` C shim hook over `HostStepState` to `PostForkOpsM`.
-/

namespace LeanSwe.PostFork.Model

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

/-- Maximum valid 31-bit signed positive Linux PID (`2147483647`). -/
def maxLinuxPid : Pid := 0x7fffffff

/-- Monadic raw spawn capability bundle specialized to `Nat` handles for `Core.ObeysStepFrom`. -/
abbrev RawHostOpsM (m : Type → Type) :=
  RawSpawnOpsM m Nat

/-- Monadic public `PostFork` capability bundle specialized to `Nat` handles for `Core.ObeysStepFrom`. -/
abbrev PkgPostForkOpsM (m : Type → Type) :=
  PostForkOpsM m Nat

/-- Pure host step state tracking the most recently spawned PID and host health. -/
structure HostStepState where
  /-- Most recently observed valid Linux PID (`1..maxLinuxPid`). -/
  lastPid : Pid := 100
  /-- Whether the host kernel environment is within the healthy non-`EFAULT` envelope. -/
  healthyHost : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Well-formedness guard on `HostStepState` for `Core.ObeysStepFrom`. -/
def rawStepWf (s : HostStepState) : Bool :=
  s.healthyHost && decide (1 ≤ s.lastPid ∧ s.lastPid ≤ maxLinuxPid)

/-- Single-step raw host FFI request covering `RawSpawnOpsM.spawnRaw`. -/
inductive RawStepReq where
  /-- `raw.spawnRaw flags sIn sOut sErr cwd path argv envEntries`. -/
  | spawnRaw
      (flags : UInt32)
      (sIn sOut sErr : FdRef Nat)
      (cwd : Option String) (path : String)
      (argv : Array String) (envEntries : Array ByteArray)
  deriving BEq, DecidableEq

/-- Single-step output sum for `RawStepReq` transitions in `Core.ObeysStepFrom`. -/
inductive RawStepOut where
  /-- Outcome returned by `spawnRaw`. -/
  | spawned (res : Except RawSpawnErr Pid)
  deriving Inhabited

/-- Execute one `RawStepReq` against `raw : RawHostOpsM (StateM W)`. -/
def execRawStep {W : Type} (raw : RawHostOpsM (StateM W)) :
    RawStepReq → StateM W RawStepOut
  | .spawnRaw flags sIn sOut sErr cwd path argv envp =>
    .spawned <$> raw.spawnRaw flags sIn sOut sErr cwd path argv envp

/-- Prop-valued validity of a reaped Linux `ChildWaitStatus` (`exited 0..255` or `signaled 1..64`). -/
def validWaitStatusProp : ChildWaitStatus → Prop
  | .exited code => code ≤ 255
  | .signaled sig => 1 ≤ sig ∧ sig ≤ 64

/-- Prop-valued range check on raw Linux `Errno` values (`1..4095`). -/
def validHostErrnoProp (e : Errno) : Prop :=
  1 ≤ e.toNat ∧ e.toNat ≤ 4095

/-- Prop-valued validity of a raw C shim error returned by `leanswe_postfork_spawn`. -/
def validRawSpawnErrProp : RawSpawnErr → Prop
  | .sys e => validHostErrnoProp e
  | .child wst _ e => validWaitStatusProp wst ∧ validHostErrnoProp e

/-- Allowed healthy-host transition for `RawSpawnOpsM.spawnRaw`. -/
def allowedRawStep (s : HostStepState) (req : RawStepReq) (out : RawStepOut)
    (s' : HostStepState) : Prop :=
  rawStepWf s = true ∧
  rawStepWf s' = true ∧
  match req, out with
  | .spawnRaw _ _ _ _ _ _ _ _, .spawned (.ok pid) =>
    1 ≤ pid ∧ pid ≤ maxLinuxPid ∧ s'.lastPid = pid
  | .spawnRaw _ _ _ _ _ _ _ _, .spawned (.error err) =>
    validRawSpawnErrProp err

/-- Single-step request sum covering the public `PostForkOpsM` operation (`spawn`). -/
inductive PkgStepReq where
  /-- `ops.spawn spec`. -/
  | spawn (spec : ChildSpecM Nat)
  deriving BEq, DecidableEq

/-- Single-step output sum for `PkgStepReq` transitions in `Core.ObeysStepFrom`. -/
inductive PkgStepOut where
  /-- Live-child or structured-error outcome returned by `spawn`. -/
  | spawned (res : Except PostForkError SpawnedChild)
  deriving Inhabited

/-- Execute one `PkgStepReq` against `ops : PkgPostForkOpsM (StateM W)`. -/
def execPkgStep {W : Type} (ops : PkgPostForkOpsM (StateM W)) :
    PkgStepReq → StateM W PkgStepOut
  | .spawn spec => .spawned <$> ops.spawn spec

/-- Compute the expected `SpawnedChild.pgid` for `policy` and `pid`. -/
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

/-- Allowed healthy-host transition for `PostForkOpsM.spawn`. -/
def allowedPkgStep (s : HostStepState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : HostStepState) : Prop :=
  rawStepWf s = true ∧
  rawStepWf s' = true ∧
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

/-- Deterministic pure reference `RawHostOpsM (StateM HostStepState)` witnessing `allowedRawStep`. -/
def modelRawOps : RawHostOpsM (StateM HostStepState) where
  spawnRaw _ _ _ _ _ _ _ _ := do
    let s ← get
    let pid : Pid := 100
    set { s with lastPid := pid }
    pure (.ok pid)

end LeanSwe.PostFork.Model
