import LeanSwe.EnvVars.Raw.Types

namespace LeanSwe.EnvVars.Raw.Model

/-- Pure model of the POSIX process environment (`environ(7)`), storing raw NUL-free byte slices in order. -/
structure EnvironState where
  /-- Ordered raw byte slices (`NAME=VALUE`, or malformed slices) in `environ(7)`. -/
  entries : Array ByteArray := #[]
  deriving BEq, DecidableEq, Inhabited

/-- Return `true` iff `bs` contains no NUL (`0x00`) byte. -/
def isNulFreeBytes (bs : ByteArray) : Bool :=
  !(bs.data.toList.contains 0)

/-- Return `true` iff every entry in `s.entries` is NUL-free, matching C-string `environ(7)` entries. -/
def EnvironState.isWellFormed (s : EnvironState) : Bool :=
  s.entries.toList.all isNulFreeBytes

/-- Return `true` iff `cs` contains `'='` or NUL (`Char.ofNat 0`). -/
def hasInvalidKeyCharModel : List Char → Bool
  | [] => false
  | c :: cs =>
    if c == '=' || c == Char.ofNat 0 then true
    else hasInvalidKeyCharModel cs

/-- Return `true` iff `key` is a non-empty POSIX environment variable name without `'='` or NUL. -/
def isValidPosixKeyModel (key : String) : Bool :=
  !key.isEmpty && !hasInvalidKeyCharModel key.toList

/-- Return `true` iff raw byte slice `k` is non-empty and free of NUL (`0x00`) and `'='` (`0x3D`). -/
def isValidPosixKeyBytes (k : ByteArray) : Bool :=
  k.size > 0 && !(k.data.toList.contains 0) && !(k.data.toList.contains 0x3D)

/-- Tail-recursive accumulator splitting a byte list at the first `'='` (`0x3D`) with a non-empty prefix. -/
def splitFirstEqListModel (revPre : List UInt8) : List UInt8 → Option (ByteArray × ByteArray)
  | [] => none
  | b :: bs =>
    if b == 0x3D then
      if revPre.isEmpty then none
      else some (ByteArray.mk revPre.reverse.toArray, ByteArray.mk bs.toArray)
    else
      splitFirstEqListModel (b :: revPre) bs

/-- Split a raw `NAME=VALUE` byte slice strictly at the first `'='` (`0x3D`), returning `none`
    when `'='` is absent or occurs at index `0`. -/
def splitFirstEqBytesModel (entry : ByteArray) : Option (ByteArray × ByteArray) :=
  splitFirstEqListModel [] entry.data.toList

/-- Return `true` iff `entry` splits at its first `'='` with key prefix equal to `keyBytes`. -/
def entryHasKeyBytes (entry keyBytes : ByteArray) : Bool :=
  match splitFirstEqBytesModel entry with
  | some (k, _) => k == keyBytes
  | none => false

/-- Return the value bytes of the first entry in `xs` whose key prefix matches `keyBytes`. -/
def findFirstKeyValue : List ByteArray → ByteArray → Option ByteArray
  | [], _ => none
  | entry :: rest, keyBytes =>
    match splitFirstEqBytesModel entry with
    | some (k, v) =>
      if k == keyBytes then some v
      else findFirstKeyValue rest keyBytes
    | none => findFirstKeyValue rest keyBytes

/-- Return the index of the first entry in `xs` whose key prefix matches `keyBytes`. -/
def findFirstKeyIdxList (idx : Nat) : List ByteArray → ByteArray → Option Nat
  | [], _ => none
  | entry :: rest, keyBytes =>
    if entryHasKeyBytes entry keyBytes then some idx
    else findFirstKeyIdxList (idx + 1) rest keyBytes

/-- Pure model of `leanswe_envvars_getenv` over `EnvironState`: rejects invalid POSIX keys with `none`,
    and otherwise returns the value bytes of the first matching `NAME=VALUE` entry. -/
def posixGetEnvBytesModel (s : EnvironState) (key : String) : Option ByteArray :=
  if !isValidPosixKeyModel key then
    none
  else
    findFirstKeyValue s.entries.toList key.toUTF8

/-- Pure `PosixRawOpsM Id` backed by `EnvironState`. -/
def modelPosixRawOps (s : EnvironState) : PosixRawOpsM Id :=
  { getEnvBytes := posixGetEnvBytesModel s
    listEnvironBytes := s.entries }

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsgModel (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Pure total error-mapping model from `EnvVarsRawError` to `EnvVarsError`. -/
def mapRawErrorModel : EnvVarsRawError → EnvVarsError
  | .invalidEncoding key? detail =>
    { kind := .invalidEncoding
      key := key?
      errnoCode := none
      message := nonEmptyMsgModel "invalid UTF-8 in environment" detail }
  | .invalidArgument key? code detail =>
    { kind := .invalidKey
      key := key?
      errnoCode := some code
      message := nonEmptyMsgModel "invalid environment variable name" detail }
  | .otherError code detail =>
    { kind := .ioError
      key := none
      errnoCode := some code
      message := nonEmptyMsgModel s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      key := none
      errnoCode := none
      message := nonEmptyMsgModel "environment error" detail }

/-- Pure behavior model of `LeanSwe.EnvVars.Raw.getEnv` over `EnvironState`. -/
def rawGetEnvModel (s : EnvironState) (key : String) : Except EnvVarsRawError (Option String) :=
  match posixGetEnvBytesModel s key with
  | none => .ok none
  | some bs =>
    match String.fromUTF8? bs with
    | some v => .ok (some v)
    | none => .error (.invalidEncoding (some key) "invalid UTF-8 in environment value")

/-- Tail-recursive model decoder for `environ(7)` byte slices in order. -/
def decodeEnvironModelAcc (accRev : List (String × String)) :
    List ByteArray → Except EnvVarsRawError (List (String × String))
  | [] => .ok accRev.reverse
  | entry :: rest =>
    match splitFirstEqBytesModel entry with
    | none => decodeEnvironModelAcc accRev rest
    | some (kBytes, vBytes) =>
      match String.fromUTF8? kBytes with
      | none => .error (.invalidEncoding none "invalid UTF-8 in environment key")
      | some k =>
        match String.fromUTF8? vBytes with
        | none => .error (.invalidEncoding (some k) "invalid UTF-8 in environment value")
        | some v => decodeEnvironModelAcc ((k, v) :: accRev) rest

/-- Pure behavior model of `LeanSwe.EnvVars.Raw.listEnv` over `EnvironState`. -/
def rawListEnvModel (s : EnvironState) : Except EnvVarsRawError (Array (String × String)) :=
  (decodeEnvironModelAcc [] s.entries.toList).map List.toArray

/-- Pure `RawEnvVarsOpsM Id` behavior model over `EnvironState`. -/
def modelRawOps (s : EnvironState) : RawEnvVarsOpsM Id :=
  { mapRawError := mapRawErrorModel
    getEnv := rawGetEnvModel s
    listEnv := rawListEnvModel s }

/-- Pure stateful model of POSIX `setenv(3)` on byte slices, returning `22` (`EINVAL`) on invalid key or NUL value. -/
def posixSetEnvBytesModel (s : EnvironState) (k v : ByteArray) (overwrite : Bool) :
    Except UInt32 EnvironState :=
  if !isValidPosixKeyBytes k || !(isNulFreeBytes v) then
    .error 22
  else
    let kv := k ++ ByteArray.mk #[0x3D] ++ v
    match findFirstKeyIdxList 0 s.entries.toList k with
    | some i =>
      if overwrite then
        .ok { entries := s.entries.setIfInBounds i kv }
      else
        .ok s
    | none =>
      .ok { entries := s.entries.push kv }

/-- Pure stateful model of POSIX `unsetenv(3)` on byte slices, returning `22` (`EINVAL`) on invalid key. -/
def posixUnsetEnvBytesModel (s : EnvironState) (k : ByteArray) :
    Except UInt32 EnvironState :=
  if !isValidPosixKeyBytes k then
    .error 22
  else
    .ok { entries := s.entries.filter (fun e => !entryHasKeyBytes e k) }

/-- Pure stateful model of glibc `clearenv(3)`. -/
def posixClearEnvModel : EnvironState :=
  { entries := #[] }

/-- Validate and install an arbitrary raw `environ(7)` table of NUL-free byte slices. -/
def posixInstallRawTableModel (entries : Array ByteArray) : Option EnvironState :=
  if entries.toList.all isNulFreeBytes then
    some { entries }
  else
    none

end LeanSwe.EnvVars.Raw.Model