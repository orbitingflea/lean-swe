import LeanSwe.PostFork.Types

namespace LeanSwe.PostFork.Impl

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

namespace Internal

/-- Child flag bit `0`: invoke `setpgid(0, 0)`. -/
def FLAG_SET_PGID_IMPL : UInt32 := 1
/-- Child flag bit `1`: reset `SIGPIPE` to `SIG_DFL` and unblock `SIGPIPE`. -/
def FLAG_RESET_SIGPIPE_IMPL : UInt32 := 2
/-- Child flag bit `2`: redirect `(stdin, stdout, stderr)` onto `(0, 1, 2)`. -/
def FLAG_REDIRECT_STDIO_IMPL : UInt32 := 4

/-- Decode a C shim stage tag (`1..7`) into `FailureStage`. -/
def failureStageOfTagImpl? (tag : UInt32) : Option FailureStage :=
  match tag.toNat with
  | 1 => some .validate
  | 2 => some .processGroup
  | 3 => some .signalReset
  | 4 => some .fdSetup
  | 5 => some .closeUnkept
  | 6 => some .chdir
  | 7 => some .execve
  | _ => none

/-- Normalize an errno value into Linux's positive `1..4095` range (`EIO` fallback). -/
def normalizeErrnoImpl (raw : Errno) : Errno :=
  if 1 ≤ raw.toNat && raw.toNat ≤ 4095 then raw else Errno.EIO

/-- Convert a raw C shim failure into a structured `PostForkError`. -/
def decodeRawSpawnErrImpl : RawSpawnErr → PostForkError
  | .sys e =>
    { kind := .sysError, errno := some (normalizeErrnoImpl e), childFailure := none,
      message := "postfork host syscall failed" }
  | .child wst tag e =>
    let stage := (failureStageOfTagImpl? tag).getD .wireTruncated
    let code := if (failureStageOfTagImpl? tag).isSome then normalizeErrnoImpl e else Errno.EIO
    { kind := .childFailed, errno := some code,
      childFailure := some { stage := stage, errno := code, waitStatus := some wst },
      message := "child setup or execve failed" }

/-- Compute the C shim child-setup bitmask for `spec`. -/
def flagsOfSpecImpl {fd : Type} (spec : ChildSpecM fd) : UInt32 :=
  let fPgid : UInt32 := match spec.processGroup with | .newGroup => FLAG_SET_PGID_IMPL | .inherit => 0
  let fSig : UInt32 := match spec.sigpipe with | .resetDefault => FLAG_RESET_SIGPIPE_IMPL | .inherit => 0
  let fStdio : UInt32 := match spec.stdio with | .redirect .. => FLAG_REDIRECT_STDIO_IMPL | .inherit => 0
  fPgid ||| fSig ||| fStdio

/-- Return `true` iff UTF-8 bytes of `s` contain an embedded NUL (`0x00`) byte. -/
def hasEmbeddedNulStrImpl (s : String) : Bool :=
  s.toUTF8.toList.any (· == (0 : UInt8))

/-- Return `true` iff `(k, v)` is a valid NUL-free `KEY=VALUE` binding (`k` non-empty, no `'='`). -/
def isValidEnvBindingImpl (kv : String × String) : Bool :=
  !kv.1.isEmpty && !kv.1.contains '=' && !hasEmbeddedNulStrImpl kv.1 && !hasEmbeddedNulStrImpl kv.2

/-- Return `true` iff raw byte slice `entry` contains no embedded NUL (`0x00`) byte. -/
def isValidRawEnvEntryImpl (entry : ByteArray) : Bool :=
  !entry.toList.any (· == (0 : UInt8))

/-- Return `true` iff raw `environ(7)` slice `entry` starts with `key ++ "="` (`0x3D`). -/
def rawEnvHasKeyImpl (key entry : ByteArray) : Bool :=
  if h : key.size < entry.size then
    entry.extract 0 key.size == key && entry[key.size] == (0x3D : UInt8)
  else
    false

/-- Encode raw NUL-free `rawEnv` slices followed by `(key, value)` bindings as NUL-terminated C strings. -/
def formatEnvEntriesBytesImpl (rawEnv : Array ByteArray) (env : Array (String × String)) : Array ByteArray :=
  let keptRaw := rawEnv.filter fun b => !env.any fun (k, _) => rawEnvHasKeyImpl k.toUTF8 b
  keptRaw.map (fun b => b.push 0) ++ env.map (fun (k, v) => s!"{k}={v}".toUTF8.push 0)

/-- Extract kept descriptor references from `FdPolicy`. -/
def keepFdsImpl {fd : Type} : FdPolicy fd → Array (FdRef fd)
  | .inheritNonCloexec ks => ks
  | .closeAllAbove2Except ks => ks

/-- Return `true` iff `ref` is either a managed handle or a non-negative `.raw` FD. -/
def fdRefIsNonnegImpl {fd : Type} : FdRef fd → Bool
  | .handle _ => true
  | .raw n => decide (n.toInt ≥ 0)

/-- Return `true` iff `r` is a raw stdio slot `0`, `1`, or `2`. -/
def fdRefIsRawStdioSlotImpl {fd : Type} : FdRef fd → Bool
  | .raw n => n == 0 || n == 1 || n == 2
  | .handle _ => false

/-- Return `true` iff two `FdRef` values have equal `.raw` numbers. -/
def fdRefSameRawImpl {fd : Type} : FdRef fd → FdRef fd → Bool
  | .raw a, .raw b => a == b
  | _, _ => false

/-- Extract literal string from an `ArgToken`. -/
def argTokenTextImpl {fd : Type} : ArgToken fd → String
  | .lit s => s

/-- Return `true` iff `tok` has a NUL-free literal string. -/
def argTokenIsValidImpl {fd : Type} : ArgToken fd → Bool
  | .lit s => !hasEmbeddedNulStrImpl s

/-- Pre-`fork` runtime validation checking string hygiene, non-negative `.raw` FDs, empty `keepFds`, and stdio safety. -/
def validateSpecImpl {fd : Type} (spec : ChildSpecM fd) : Bool :=
  let cwdOk := match spec.cwd with | some d => !hasEmbeddedNulStrImpl d | none => true
  let pathOk := !spec.path.isEmpty && !hasEmbeddedNulStrImpl spec.path
  let argvOk := spec.argv.all argTokenIsValidImpl
  let envOk := spec.env.all isValidEnvBindingImpl && spec.rawEnv.all isValidRawEnvEntryImpl
  let keepEmpty := (keepFdsImpl spec.fdPolicy).isEmpty
  let closeOk := spec.closeFds.all (fun r => fdRefIsNonnegImpl r && !fdRefIsRawStdioSlotImpl r)
  let stdioOk := match spec.stdio with
    | .inherit => true
    | .redirect sIn sOut sErr _ =>
      fdRefIsNonnegImpl sIn && fdRefIsNonnegImpl sOut && fdRefIsNonnegImpl sErr &&
      !(spec.closeFds.any (fun c => fdRefSameRawImpl c sIn || fdRefSameRawImpl c sOut || fdRefSameRawImpl c sErr))
  pathOk && cwdOk && argvOk && envOk && keepEmpty && closeOk && stdioOk

/-- Split a `FdRef` into `(Option fd, Int32)` for direct C FFI passing. -/
def splitFdRef {fd : Type} : FdRef fd → Option fd × Int32
  | .handle h => (some h, -1)
  | .raw n => (none, n)

/-- Extract the three stdio `FdRef`s (using `.raw (-1)` sentinels when `.inherit`). -/
def stdioTriple {fd : Type} : StdioPlan fd → FdRef fd × FdRef fd × FdRef fd
  | .inherit => (.raw (-1), .raw (-1), .raw (-1))
  | .redirect sIn sOut sErr _ => (sIn, sOut, sErr)

/-- Build a caller-agnostic `PostForkOpsM` from a single-shot `RawSpawnOpsM` boundary. -/
def mkHostOps {m : Type → Type} [Monad m] {fd : Type}
    (raw : RawSpawnOpsM m fd) : PostForkOpsM m fd where
  spawn spec := do
    if !validateSpecImpl spec then
      return .error { kind := .invalidInput, errno := none, childFailure := none, message := "invalid ChildSpecM" }
    let flags := flagsOfSpecImpl spec
    let (sIn, sOut, sErr) := stdioTriple spec.stdio
    let argvStrs := spec.argv.map argTokenTextImpl
    let envEntries := formatEnvEntriesBytesImpl spec.rawEnv spec.env
    match ← raw.spawnRaw flags sIn sOut sErr spec.cwd spec.path argvStrs envEntries with
    | .error rawErr => return .error (decodeRawSpawnErrImpl rawErr)
    | .ok pid =>
      let pgid? := match spec.processGroup with | .newGroup => some pid | .inherit => none
      return .ok { pid := pid, pgid := pgid? }

/-- Monadic `Nat`-specialized `PostForkOpsM` builder for `Core.ObeysStepFrom`. -/
def mkHostOpsM {m : Type → Type} [Monad m]
    (raw : RawSpawnOpsM m Nat) : PostForkOpsM m Nat :=
  mkHostOps raw

end Internal

end LeanSwe.PostFork.Impl
