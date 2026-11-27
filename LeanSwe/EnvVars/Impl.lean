import LeanSwe.EnvVars.Types

namespace LeanSwe.EnvVars.Internal

open LeanSwe.EnvVars (EnvVarsError EnvVarsRawError PosixRawOpsM EnvVarsApiM)

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Convert a pure `EnvVarsRawError` record into a normalized `EnvVarsError` with non-empty message. -/
def mapRawError : EnvVarsRawError → EnvVarsError
  | .invalidEncoding key? detail =>
    { kind := .invalidEncoding
      key := key?
      errnoCode := none
      message := nonEmptyMsg "invalid UTF-8 in environment" detail }
  | .invalidArgument key? code detail =>
    { kind := .invalidKey
      key := key?
      errnoCode := some code
      message := nonEmptyMsg "invalid environment variable name" detail }
  | .otherError code detail =>
    { kind := .ioError
      key := none
      errnoCode := some code
      message := nonEmptyMsg s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      key := none
      errnoCode := none
      message := nonEmptyMsg "environment error" detail }

/-- Return `true` iff `cs` contains `=` or NUL (`Char.ofNat 0`). -/
def hasInvalidKeyChar : List Char → Bool
  | [] => false
  | c :: cs => c == '=' || c == Char.ofNat 0 || hasInvalidKeyChar cs

/-- Return `true` iff `key` is a valid non-empty POSIX environment variable name without `=` or NUL. -/
def isValidKey (key : String) : Bool :=
  !key.isEmpty && !hasInvalidKeyChar key.toList

/-- Accumulator helper splitting a byte list at the first `'='` (`0x3D`) with a non-empty prefix. -/
def splitFirstEqList (revPre : List UInt8) : List UInt8 → Option (ByteArray × ByteArray)
  | [] => none
  | b :: bs =>
    if b == 0x3D then
      if revPre.isEmpty then none
      else some (ByteArray.mk revPre.reverse.toArray, ByteArray.mk bs.toArray)
    else
      splitFirstEqList (b :: revPre) bs

/-- Split a raw `NAME=VALUE` byte slice strictly at the first `'='` (`0x3D`), returning `none`
    when `'='` is absent or occurs at index `0` (empty key). -/
def splitFirstEqBytes (entry : ByteArray) : Option (ByteArray × ByteArray) :=
  splitFirstEqList [] entry.data.toList

/-- Tail-recursive accumulator decoding raw `environ(7)` byte slices in order, skipping entries
    lacking `'='` or starting with `'='`, and failing with `.invalidEncoding` on the first
    non-skipped entry containing invalid UTF-8. -/
def decodeEnvironAcc (accRev : List (String × String)) :
    List ByteArray → Except EnvVarsError (List (String × String))
  | [] => .ok accRev.reverse
  | entry :: rest =>
    match splitFirstEqBytes entry with
    | none => decodeEnvironAcc accRev rest
    | some (kBytes, vBytes) =>
      match String.fromUTF8? kBytes with
      | none => .error (mapRawError (.invalidEncoding none "invalid UTF-8 in environment key"))
      | some k =>
        match String.fromUTF8? vBytes with
        | none => .error (mapRawError (.invalidEncoding (some k) "invalid UTF-8 in environment value"))
        | some v => decodeEnvironAcc ((k, v) :: accRev) rest

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

/-- Build `EnvVarsApiM m` directly from thin `PosixRawOpsM m` byte hooks with zero `IO` or `@[extern]` dependencies. -/
def mkApiM {m : Type → Type} [Monad m] (posix : PosixRawOpsM m) : EnvVarsApiM m :=
  { mapRawError := mapRawError
    getEnv := fun key => do
      if !isValidKey key then
        return .error
          { kind := .invalidKey
            key := some key
            errnoCode := none
            message := "invalid environment variable name" }
      match ← posix.getEnvBytes key with
      | none => return .ok none
      | some bs =>
        match String.fromUTF8? bs with
        | some s => return .ok (some s)
        | none => return .error (mapRawError (.invalidEncoding (some key) "invalid UTF-8 in environment value"))
    listEnv := do
      let entries ← posix.listEnvironBytes
      return (decodeEnvironAcc [] entries.toList).map List.toArray
    homeDir := do
      match ← posix.getEnvBytes "HOME" with
      | none =>
        return .error
          { kind := .notFound
            key := some "HOME"
            errnoCode := none
            message := "HOME environment variable is not set" }
      | some bs =>
        match String.fromUTF8? bs with
        | none => return .error (mapRawError (.invalidEncoding (some "HOME") "invalid UTF-8 in environment value"))
        | some "" =>
          return .error
            { kind := .notFound
              key := some "HOME"
              errnoCode := none
              message := "HOME environment variable is empty" }
        | some h => return .ok h
    listEnvironBytes := posix.listEnvironBytes
    splitSearchPath := splitSearchPath }

end LeanSwe.EnvVars.Internal
