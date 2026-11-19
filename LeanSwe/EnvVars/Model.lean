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

end LeanSwe.EnvVars.Model