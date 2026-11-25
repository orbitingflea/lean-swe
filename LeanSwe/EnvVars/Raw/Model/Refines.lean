import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Model

namespace LeanSwe.EnvVars.Raw.Model

/-- Request algebra for `PosixRawOpsM` calls. -/
inductive PosixStepReq where
  /-- Raw `getenv(3)` byte lookup by `key`. -/
  | getEnvBytes (key : String)
  /-- Raw `environ(7)` byte-slice snapshot. -/
  | listEnvironBytes
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Output algebra for `PosixRawOpsM` calls. -/
inductive PosixStepOut where
  /-- Optional raw byte slice returned by `getEnvBytes`. -/
  | bytesOpt (res : Option ByteArray)
  /-- Ordered raw entry byte slices returned by `listEnvironBytes`. -/
  | entries (res : Array ByteArray)
  deriving BEq, DecidableEq, Inhabited

/-- Request algebra for effectful `RawEnvVarsBundleM` calls. -/
inductive PkgStepReq where
  /-- Decoded `getEnv` lookup by `key`. -/
  | getEnv (key : String)
  /-- Decoded `listEnv` snapshot. -/
  | listEnv
  /-- Raw `listEnvironBytes` byte-slice snapshot. -/
  | listEnvironBytes
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Output algebra for effectful `RawEnvVarsBundleM` calls. -/
inductive PkgStepOut where
  /-- Fallible optional UTF-8 value returned by `getEnv`. -/
  | valOpt (res : Except EnvVarsRawError (Option String))
  /-- Fallible decoded `(key, value)` array returned by `listEnv`. -/
  | pairs (res : Except EnvVarsRawError (Array (String × String)))
  /-- Ordered raw entry byte slices returned by `listEnvironBytes`. -/
  | rawEntries (res : Array ByteArray)
  deriving Inhabited

/-- Well-formedness guard on `EnvironState` for `EnvVars.Raw` single-step transitions. -/
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

/-- Execute one `PkgStepReq` against an arbitrary `RawEnvVarsBundleM (StateM W)`. -/
def execPkgStep {W : Type} (ops : RawEnvVarsBundleM (StateM W)) :
    PkgStepReq → StateM W PkgStepOut
  | .getEnv key => .valOpt <$> ops.getEnv key
  | .listEnv => .pairs <$> ops.listEnv
  | .listEnvironBytes => .rawEntries <$> ops.listEnvironBytes

/-- Allowed single-step transition relation for `RawEnvVarsBundleM` over `EnvironState`. -/
def allowedPkgStep (s : EnvironState) (req : PkgStepReq)
    (out : PkgStepOut) (s' : EnvironState) : Prop :=
  s' = s ∧
    match req, out with
    | .getEnv key, .valOpt res => res = rawGetEnvModel s key
    | .listEnv, .pairs res => res = rawListEnvModel s
    | .listEnvironBytes, .rawEntries res => res = s.entries
    | _, _ => False

end LeanSwe.EnvVars.Raw.Model
