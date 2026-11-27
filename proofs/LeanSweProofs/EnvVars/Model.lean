import LeanSwe.EnvVars.Types

namespace LeanSwe.EnvVars.Model

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

/-- Tail-recursive model decoder for `environ(7)` byte slices in order. -/
def decodeEnvironModelAcc (accRev : List (String × String)) :
    List ByteArray → Except EnvVarsError (List (String × String))
  | [] => .ok accRev.reverse
  | entry :: rest =>
    match splitFirstEqBytesModel entry with
    | none => decodeEnvironModelAcc accRev rest
    | some (kBytes, vBytes) =>
      match String.fromUTF8? kBytes with
      | none => .error (mapRawErrorModel (.invalidEncoding none "invalid UTF-8 in environment key"))
      | some k =>
        match String.fromUTF8? vBytes with
        | none => .error (mapRawErrorModel (.invalidEncoding (some k) "invalid UTF-8 in environment value"))
        | some v => decodeEnvironModelAcc ((k, v) :: accRev) rest

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

/-- Pure behavior model of `LeanSwe.EnvVars.getEnv` over `EnvironState`. -/
def getEnvModel (s : EnvironState) (key : String) : Except EnvVarsError (Option String) :=
  if !isValidPosixKeyModel key then
    .error
      { kind := .invalidKey
        key := some key
        errnoCode := none
        message := "invalid environment variable name" }
  else
    match posixGetEnvBytesModel s key with
    | none => .ok none
    | some bs =>
      match String.fromUTF8? bs with
      | some v => .ok (some v)
      | none => .error (mapRawErrorModel (.invalidEncoding (some key) "invalid UTF-8 in environment value"))

/-- Pure behavior model of `LeanSwe.EnvVars.listEnv` over `EnvironState`. -/
def listEnvModel (s : EnvironState) : Except EnvVarsError (Array (String × String)) :=
  (decodeEnvironModelAcc [] s.entries.toList).map List.toArray

/-- Pure behavior model of `LeanSwe.EnvVars.homeDir` over `EnvironState`. -/
def homeDirModel (s : EnvironState) : Except EnvVarsError String :=
  match posixGetEnvBytesModel s "HOME" with
  | none =>
    .error
      { kind := .notFound
        key := some "HOME"
        errnoCode := none
        message := "HOME environment variable is not set" }
  | some bs =>
    match String.fromUTF8? bs with
    | none => .error (mapRawErrorModel (.invalidEncoding (some "HOME") "invalid UTF-8 in environment value"))
    | some "" =>
      .error
        { kind := .notFound
          key := some "HOME"
          errnoCode := none
          message := "HOME environment variable is empty" }
    | some h => .ok h

/-- Pure `EnvVarsApiM Id` behavior model over `EnvironState`. -/
def modelApi (s : EnvironState) : EnvVarsApiM Id :=
  { mapRawError := mapRawErrorModel
    getEnv := getEnvModel s
    listEnv := listEnvModel s
    homeDir := homeDirModel s
    listEnvironBytes := s.entries
    splitSearchPath := splitSearchPathModel }

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

/-- Request sum covering all effectful `EnvVarsApiM` operations (`getEnv`, `listEnv`, `homeDir`, `listEnvironBytes`). -/
inductive PkgStepReq where
  /-- Validated `EnvVarsApiM.getEnv` request. -/
  | getEnv (key : String)
  /-- `EnvVarsApiM.listEnv` request. -/
  | listEnv
  /-- `EnvVarsApiM.homeDir` request. -/
  | homeDir
  /-- Raw `EnvVarsApiM.listEnvironBytes` byte-slice snapshot. -/
  | listEnvironBytes
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Output sum for effectful `EnvVarsApiM` transitions. -/
inductive PkgStepOut where
  /-- Result of `EnvVarsApiM.getEnv`. -/
  | getEnv (res : Except EnvVarsError (Option String))
  /-- Result of `EnvVarsApiM.listEnv`. -/
  | listEnv (res : Except EnvVarsError (Array (String × String)))
  /-- Result of `EnvVarsApiM.homeDir`. -/
  | homeDir (res : Except EnvVarsError String)
  /-- Ordered raw entry byte slices returned by `EnvVarsApiM.listEnvironBytes`. -/
  | rawEntries (res : Array ByteArray)
  deriving Inhabited

/-- Execute one `PkgStepReq` against an `EnvVarsApiM (StateM W)` bundle. -/
def execPkgStep {W : Type} (api : EnvVarsApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .getEnv key => .getEnv <$> api.getEnv key
  | .listEnv => .listEnv <$> api.listEnv
  | .homeDir => .homeDir <$> api.homeDir
  | .listEnvironBytes => .rawEntries <$> api.listEnvironBytes

/-- Allowed package-level single-step relation against `getEnvModel`, `listEnvModel`, `homeDirModel`, and `s.entries`. -/
def allowedPkgStep (s : EnvironState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : EnvironState) : Prop :=
  s' = s ∧
    match req, out with
    | .getEnv key, .getEnv res => res = getEnvModel s key
    | .listEnv, .listEnv res => res = listEnvModel s
    | .homeDir, .homeDir res => res = homeDirModel s
    | .listEnvironBytes, .rawEntries res => res = s.entries
    | _, _ => False

end LeanSwe.EnvVars.Model
