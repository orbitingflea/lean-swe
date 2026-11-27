import LeanSwe.EnvVars.Types
import LeanSweProofs.EnvVars.Model

namespace LeanSwe.EnvVars.Model

/-- Request algebra for thin `PosixRawOpsM` calls. -/
inductive PosixStepReq where
  /-- Raw `getenv(3)` byte lookup by `key`. -/
  | getEnvBytes (key : String)
  /-- Raw `environ(7)` byte-slice snapshot. -/
  | listEnvironBytes
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Output algebra for thin `PosixRawOpsM` calls. -/
inductive PosixStepOut where
  /-- Optional raw byte slice returned by `getEnvBytes`. -/
  | bytesOpt (res : Option ByteArray)
  /-- Ordered raw entry byte slices returned by `listEnvironBytes`. -/
  | entries (res : Array ByteArray)
  deriving BEq, DecidableEq, Inhabited

/-- Total well-formedness guard on `EnvironState` for `Core.ObeysStepFrom`. -/
def rawStepWf (_ : EnvironState) : Bool := true

/-- Pure `PosixRawOpsM (StateM EnvironState)` model reading `EnvironState` without mutation. -/
def modelStatePosixOps : PosixRawOpsM (StateM EnvironState) :=
  { getEnvBytes := fun key => do
      let s ← get
      return posixGetEnvBytesModel s key
    listEnvironBytes := do
      let s ← get
      return s.entries }

/-- Execute one `PosixStepReq` against an arbitrary `PosixRawOpsM (StateM W)`. -/
def execPosixStep {W : Type} (posix : PosixRawOpsM (StateM W)) :
    PosixStepReq → StateM W PosixStepOut
  | .getEnvBytes key => .bytesOpt <$> posix.getEnvBytes key
  | .listEnvironBytes => .entries <$> posix.listEnvironBytes

/-- Allowed single-step transition relation for `PosixRawOpsM` over `EnvironState`. -/
def allowedPosixStep (s : EnvironState) (req : PosixStepReq)
    (out : PosixStepOut) (s' : EnvironState) : Prop :=
  s' = s ∧
    match req, out with
    | .getEnvBytes key, .bytesOpt res => res = posixGetEnvBytesModel s key
    | .listEnvironBytes, .entries res => res = s.entries
    | _, _ => False

end LeanSwe.EnvVars.Model
