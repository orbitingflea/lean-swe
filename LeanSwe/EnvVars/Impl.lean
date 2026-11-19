import LeanSwe.EnvVars.Types

namespace LeanSwe.EnvVars.Internal

open LeanSwe.EnvVars (EnvVarsErrorKind EnvVarsError EnvVarsRawError RawEnvVarsOpsM EnvVarsApiM)

/-- Return `true` iff `cs` contains `=` or NUL (`Char.ofNat 0`). -/
def hasInvalidKeyChar : List Char → Bool
  | [] => false
  | c :: cs => c == '=' || c == Char.ofNat 0 || hasInvalidKeyChar cs

/-- Return `true` iff `key` is a valid non-empty environment variable name without `=` or NUL. -/
def isValidKey (key : String) : Bool :=
  !key.toList.isEmpty && !hasInvalidKeyChar key.toList

/-- Tail-recursive accumulator splitting `cs` on `:` separators into character segments. -/
def splitColonAcc (curRev : List Char) (accRev : List (List Char)) : List Char → List (List Char)
  | [] => (curRev.reverse :: accRev).reverse
  | c :: cs =>
    if c == ':' then
      splitColonAcc [] (curRev.reverse :: accRev) cs
    else
      splitColonAcc (c :: curRev) accRev cs

/-- Split a POSIX `:`-delimited search path into non-empty components. -/
def splitSearchPath (path : String) : Array String :=
  (((splitColonAcc [] [] path.toList).filter fun s => !s.isEmpty).map String.ofList).toArray

/-- Build `EnvVarsApiM m` from a `RawEnvVarsOpsM m` backend with zero `IO` or `@[extern]` dependencies. -/
def mkApiM {m : Type → Type} [Monad m] (raw : RawEnvVarsOpsM m) : EnvVarsApiM m :=
  { mapRawError := raw.mapRawError
    getEnv := fun key => do
      if !isValidKey key then
        return .error
          { kind := .invalidKey
            key := some key
            errnoCode := none
            message := "invalid environment variable name" }
      match ← raw.getEnv key with
      | .error err => return .error (raw.mapRawError err)
      | .ok val => return .ok val
    listEnv := do
      match ← raw.listEnv with
      | .error err => return .error (raw.mapRawError err)
      | .ok entries => return .ok entries
    homeDir := do
      match ← raw.getEnv "HOME" with
      | .error err => return .error (raw.mapRawError err)
      | .ok none =>
        return .error
          { kind := .notFound
            key := some "HOME"
            errnoCode := none
            message := "HOME environment variable is not set" }
      | .ok (some "") =>
        return .error
          { kind := .notFound
            key := some "HOME"
            errnoCode := none
            message := "HOME environment variable is empty" }
      | .ok (some h) => return .ok h
    splitSearchPath := splitSearchPath }

end LeanSwe.EnvVars.Internal
