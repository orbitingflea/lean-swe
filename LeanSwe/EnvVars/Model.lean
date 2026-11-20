import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Raw.Model

namespace LeanSwe.EnvVars.Model

/-- Tail-recursive accumulator splitting `cs` on `:` separators into character segments. -/
def splitColonAccModel (curRev : List Char) (accRev : List (List Char)) :
    List Char → List (List Char)
  | [] => (curRev.reverse :: accRev).reverse
  | c :: cs =>
    if c == ':' then
      splitColonAccModel [] (curRev.reverse :: accRev) cs
    else
      splitColonAccModel (c :: curRev) accRev cs

/-- Pure behavior model of `LeanSwe.EnvVars.splitSearchPath`. -/
def splitSearchPathModel (path : String) : Array String :=
  (((splitColonAccModel [] [] path.toList).filter fun s => !s.isEmpty).map String.ofList).toArray

/-- Pure behavior model of `LeanSwe.EnvVars.getEnv` over `Raw.Model.EnvironState`. -/
def getEnvModel (s : Raw.Model.EnvironState) (key : String) : Except EnvVarsError (Option String) :=
  if !Raw.Model.isValidPosixKeyModel key then
    .error
      { kind := .invalidKey
        key := some key
        errnoCode := none
        message := "invalid environment variable name" }
  else
    (Raw.Model.rawGetEnvModel s key).mapError Raw.Model.mapRawErrorModel

/-- Pure behavior model of `LeanSwe.EnvVars.listEnv` over `Raw.Model.EnvironState`. -/
def listEnvModel (s : Raw.Model.EnvironState) : Except EnvVarsError (Array (String × String)) :=
  (Raw.Model.rawListEnvModel s).mapError Raw.Model.mapRawErrorModel

/-- Pure behavior model of `LeanSwe.EnvVars.homeDir` over `Raw.Model.EnvironState`. -/
def homeDirModel (s : Raw.Model.EnvironState) : Except EnvVarsError String :=
  match Raw.Model.rawGetEnvModel s "HOME" with
  | .error e => .error (Raw.Model.mapRawErrorModel e)
  | .ok none =>
    .error
      { kind := .notFound
        key := some "HOME"
        errnoCode := none
        message := "HOME environment variable is not set" }
  | .ok (some "") =>
    .error
      { kind := .notFound
        key := some "HOME"
        errnoCode := none
        message := "HOME environment variable is empty" }
  | .ok (some h) => .ok h

/-- Pure `EnvVarsApiM Id` behavior model over `Raw.Model.EnvironState`. -/
def modelApi (s : Raw.Model.EnvironState) : EnvVarsApiM Id :=
  { mapRawError := Raw.Model.mapRawErrorModel
    getEnv := getEnvModel s
    listEnv := listEnvModel s
    homeDir := homeDirModel s
    splitSearchPath := splitSearchPathModel }

/-- Pure behavior model of `LeanSwe.EnvVars.mapRawError`. -/
def mapRawErrorModel (err : EnvVarsRawError) : EnvVarsError :=
  Raw.Model.mapRawErrorModel err

/-- Request sum for raw `RawEnvVarsOpsM` transitions in `Core.RefinesStepFrom`. -/
inductive RawStepReq where
  /-- Normalize a raw OS error record. -/
  | mapRawError (err : EnvVarsRawError)
  /-- Read one raw environment entry by key. -/
  | getEnv (key : String)
  /-- Snapshot all raw environment entries. -/
  | listEnv

/-- Output sum for raw `RawEnvVarsOpsM` transitions in `Core.RefinesStepFrom`. -/
inductive RawStepOut where
  /-- Result of `RawEnvVarsOpsM.mapRawError`. -/
  | mapped (err : EnvVarsError)
  /-- Result of `RawEnvVarsOpsM.getEnv`. -/
  | getEnv (res : Except EnvVarsRawError (Option String))
  /-- Result of `RawEnvVarsOpsM.listEnv`. -/
  | listEnv (res : Except EnvVarsRawError (Array (String × String)))

/-- Total well-formedness guard on `Raw.Model.EnvironState` for `Core.RefinesStepFrom`. -/
def rawStepWf (_ : Raw.Model.EnvironState) : Bool := true

/-- Execute one `RawStepReq` against an arbitrary `RawEnvVarsOpsM (StateM W)`. -/
def execRawStep {W : Type} (raw : RawEnvVarsOpsM (StateM W)) : RawStepReq → StateM W RawStepOut
  | .mapRawError err => pure (.mapped (raw.mapRawError err))
  | .getEnv key => .getEnv <$> raw.getEnv key
  | .listEnv => .listEnv <$> raw.listEnv

/-- Allowed raw single-step relation over `Raw.Model.EnvironState`. -/
def allowedRawStep (s : Raw.Model.EnvironState) (req : RawStepReq) (out : RawStepOut)
    (s' : Raw.Model.EnvironState) : Prop :=
  s' = s ∧
    match req, out with
    | .mapRawError err, .mapped res => res = Raw.Model.mapRawErrorModel err
    | .getEnv key, .getEnv res => res = Raw.Model.rawGetEnvModel s key
    | .listEnv, .listEnv res => res = Raw.Model.rawListEnvModel s
    | _, _ => False

/-- Request sum covering all effectful `EnvVarsApiM` operations (`getEnv`, `listEnv`, `homeDir`). -/
inductive PkgStepReq where
  /-- Validated `EnvVarsApiM.getEnv` request. -/
  | getEnv (key : String)
  /-- `EnvVarsApiM.listEnv` request. -/
  | listEnv
  /-- `EnvVarsApiM.homeDir` request. -/
  | homeDir

/-- Output sum for effectful `EnvVarsApiM` transitions. -/
inductive PkgStepOut where
  /-- Result of `EnvVarsApiM.getEnv`. -/
  | getEnv (res : Except EnvVarsError (Option String))
  /-- Result of `EnvVarsApiM.listEnv`. -/
  | listEnv (res : Except EnvVarsError (Array (String × String)))
  /-- Result of `EnvVarsApiM.homeDir`. -/
  | homeDir (res : Except EnvVarsError String)

/-- Execute one `PkgStepReq` against an `EnvVarsApiM (StateM W)` bundle. -/
def execPkgStep {W : Type} (api : EnvVarsApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .getEnv key => .getEnv <$> api.getEnv key
  | .listEnv => .listEnv <$> api.listEnv
  | .homeDir => .homeDir <$> api.homeDir

/-- Allowed package-level single-step relation against `getEnvModel`, `listEnvModel`, and `homeDirModel`. -/
def allowedPkgStep (s : Raw.Model.EnvironState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : Raw.Model.EnvironState) : Prop :=
  s' = s ∧
    match req, out with
    | .getEnv key, .getEnv res => res = getEnvModel s key
    | .listEnv, .listEnv res => res = listEnvModel s
    | .homeDir, .homeDir res => res = homeDirModel s
    | _, _ => False

end LeanSwe.EnvVars.Model