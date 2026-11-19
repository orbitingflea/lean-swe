import LeanSwe.EnvVars.Raw.Types

namespace LeanSwe.EnvVars.Raw.Internal

open LeanSwe.EnvVars.Raw
  (EnvVarsErrorKind EnvVarsError EnvVarsRawError PosixRawOpsM PosixRawOps RawEnvVarsOpsM RawEnvVarsOps)

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

/-- Return `true` iff `cs` contains `'='` or NUL (`Char.ofNat 0`). -/
def hasInvalidKeyChar : List Char → Bool
  | [] => false
  | c :: cs => c == '=' || c == Char.ofNat 0 || hasInvalidKeyChar cs

/-- Return `true` iff `key` is a non-empty POSIX environment variable name without `'='` or NUL. -/
def isValidPosixKey (key : String) : Bool :=
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
    List ByteArray → Except EnvVarsRawError (List (String × String))
  | [] => .ok accRev.reverse
  | entry :: rest =>
    match splitFirstEqBytes entry with
    | none => decodeEnvironAcc accRev rest
    | some (kBytes, vBytes) =>
      match String.fromUTF8? kBytes with
      | none => .error (.invalidEncoding none "invalid UTF-8 in environment key")
      | some k =>
        match String.fromUTF8? vBytes with
        | none => .error (.invalidEncoding (some k) "invalid UTF-8 in environment value")
        | some v => decodeEnvironAcc ((k, v) :: accRev) rest

/-- Build `RawEnvVarsOpsM m` from a `PosixRawOpsM m` backend. -/
def mkRawOps {m : Type → Type} [Monad m] (posix : PosixRawOpsM m) : RawEnvVarsOpsM m :=
  { mapRawError := mapRawError
    getEnv := fun key => do
      if !isValidPosixKey key then
        return .ok none
      match ← posix.getEnvBytes key with
      | none => return .ok none
      | some bs =>
        match String.fromUTF8? bs with
        | some s => return .ok (some s)
        | none => return .error (.invalidEncoding (some key) "invalid UTF-8 in environment value")
    listEnv := do
      let entries ← posix.listEnvironBytes
      return (decodeEnvironAcc [] entries.toList).map List.toArray }

end LeanSwe.EnvVars.Raw.Internal
