import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.LinuxSyscall.Passwd.Model

/-!
Pure capability-refinement specification for `LeanSwe.LinuxSyscall.Passwd` (`Core.ObeysStepFrom`),
relating single-call `Internal.PosixPasswdOpsM` hooks over `HealthyEnv` to `PasswdOpsM`.
-/

namespace LeanSwe.LinuxSyscall.Passwd.Model

open LeanSwe.LinuxSyscall

/-- Single-step raw FFI request covering all fields of `Internal.PosixPasswdOpsM`. -/
inductive RawStepReq where
  /-- Single-call `getpwuidOnce uid bufBytes`. -/
  | getpwuidOnce (uid : UInt32) (bufBytes : UInt32)
  /-- Single-call `getpwnamOnce name bufBytes`. -/
  | getpwnamOnce (name : ByteArray) (bufBytes : UInt32)
  deriving DecidableEq, BEq, Inhabited

/-- Output type returned by a single `RawStepReq` hook invocation. -/
abbrev RawStepOut := Except Errno (Option Internal.RawPasswdTuple)

/-- Extract the requested scratch-buffer byte capacity from a `RawStepReq`. -/
def RawStepReq.bufBytes : RawStepReq → UInt32
  | .getpwuidOnce _ sz => sz
  | .getpwnamOnce _ sz => sz

/-- Project the logical `PasswdReq` from a single-call `RawStepReq`. -/
def RawStepReq.toPasswdReq : RawStepReq → PasswdReq
  | .getpwuidOnce uid _ => .getpwuid uid
  | .getpwnamOnce name _ => .getpwnam name

/-- Return `true` iff `bufBytes` lies within the C shim's accepted buffer range `1..65536`. -/
def validRawBufBytes (bufBytes : UInt32) : Bool :=
  decide (1 ≤ bufBytes.toNat ∧ bufBytes.toNat ≤ 65536)

/-- Convert a raw C-ABI tuple into a structured `PasswdEntry`. -/
def entryOfRawTuple (t : Internal.RawPasswdTuple) : PasswdEntry :=
  { name := t.1
    uid := t.2.1
    gid := t.2.2.1
    gecos := t.2.2.2.1
    homeDir := t.2.2.2.2.1
    shell := t.2.2.2.2.2 }

/-- Encode a structured `PasswdEntry` as a raw C-ABI tuple. -/
def tupleOfEntry (e : PasswdEntry) : Internal.RawPasswdTuple :=
  (e.name, e.uid, e.gid, e.gecos, e.homeDir, e.shell)

/-- Map a raw FFI outcome into an abstract `PasswdOutcome`. -/
def outcomeOfRawOut : RawStepOut → PasswdOutcome
  | .ok (some t) => .found (entryOfRawTuple t)
  | .ok none => .notFound
  | .error e => .err e

/-- Well-formedness guard on `HealthyEnv` for `Core.ObeysStepFrom`. -/
def rawStepWf (env : HealthyEnv) : Bool :=
  env.wf

/-- Execute one `RawStepReq` against `raw : Internal.PosixPasswdOpsM (StateM W)`. -/
def execRawStep {W : Type} (raw : Internal.PosixPasswdOpsM (StateM W)) :
    RawStepReq → StateM W RawStepOut
  | .getpwuidOnce uid bufBytes => raw.getpwuidOnce uid bufBytes
  | .getpwnamOnce name bufBytes => raw.getpwnamOnce name bufBytes

/-- Allowed healthy-host transition for a single raw `Internal.PosixPasswdOpsM` call:
    out-of-range buffer sizes (`0` or `> 65536`) reject with `Errno.EINVAL` in `passwd_shim.c`,
    and in-range buffer sizes transition according to `healthyStep`. -/
def allowedRawStep (env : HealthyEnv) (req : RawStepReq) (out : RawStepOut)
    (env' : HealthyEnv) : Prop :=
  if !validRawBufBytes req.bufBytes then
    env.wf = true ∧ env' = env ∧ out = .error Errno.EINVAL
  else
    healthyStep env req.toPasswdReq (outcomeOfRawOut out) = some env'

/-- Execute one `PasswdReq` against `ops : PasswdOpsM (StateM W)`. -/
def execPkgStep {W : Type} (ops : PasswdOpsM (StateM W))
    (req : PasswdReq) : StateM W PasswdOutcome :=
  execPasswdReq ops req

/-- Allowed healthy-host transition for a public `PasswdOpsM` operation. -/
def allowedPkgStep (env : HealthyEnv) (req : PasswdReq) (out : PasswdOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

/-- Executable reference `Internal.PosixPasswdOpsM (StateM HealthyEnv)` lifting `healthyModelOps`. -/
def modelRawOps : Internal.PosixPasswdOpsM (StateM HealthyEnv) :=
  { getpwuidOnce := fun uid bufBytes => do
      if !validRawBufBytes bufBytes then
        return .error Errno.EINVAL
      match ← healthyModelOps.getpwuid uid with
      | .ok opt => return .ok (opt.map tupleOfEntry)
      | .error e => return .error e
    getpwnamOnce := fun name bufBytes => do
      if !validRawBufBytes bufBytes then
        return .error Errno.EINVAL
      match ← healthyModelOps.getpwnam name with
      | .ok opt => return .ok (opt.map tupleOfEntry)
      | .error e => return .error e }

end LeanSwe.LinuxSyscall.Passwd.Model
