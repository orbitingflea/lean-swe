import LeanSwe.PostFork.Types

namespace LeanSwe.PostFork.Model

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

/-- Wire stage tag for pre-execution validation errors (`1`). -/
def STAGE_VALIDATE : UInt32 := 1
/-- Wire stage tag for `setpgid(0, 0)` errors (`2`). -/
def STAGE_PROCESS_GROUP : UInt32 := 2
/-- Wire stage tag for `SIGPIPE` reset/unblock errors (`3`). -/
def STAGE_SIGNAL_RESET : UInt32 := 3
/-- Wire stage tag for stdio / `FD_CLOEXEC` errors (`4`). -/
def STAGE_FD_SETUP : UInt32 := 4
/-- Wire stage tag for closing inherited descriptors `>= 3` (`5`). -/
def STAGE_CLOSE_UNKEPT : UInt32 := 5
/-- Wire stage tag for `chdir` errors (`6`). -/
def STAGE_CHDIR : UInt32 := 6
/-- Wire stage tag for `execve` errors (`7`). -/
def STAGE_EXECVE : UInt32 := 7

/-- Child flag bit `0`: invoke `setpgid(0, 0)`. -/
def FLAG_SET_PGID : UInt32 := 1
/-- Child flag bit `1`: reset `SIGPIPE` to `SIG_DFL` and unblock `SIGPIPE`. -/
def FLAG_RESET_SIGPIPE : UInt32 := 2
/-- Child flag bit `2`: redirect `(stdin, stdout, stderr)` onto `(0, 1, 2)`. -/
def FLAG_REDIRECT_STDIO : UInt32 := 4

/-- Map a `FailureStage` to its C shim stage tag (`none` for host-only `.wireTruncated`). -/
def FailureStage.toTag? : FailureStage → Option UInt32
  | .validate => some STAGE_VALIDATE
  | .processGroup => some STAGE_PROCESS_GROUP
  | .signalReset => some STAGE_SIGNAL_RESET
  | .fdSetup => some STAGE_FD_SETUP
  | .closeUnkept => some STAGE_CLOSE_UNKEPT
  | .chdir => some STAGE_CHDIR
  | .execve => some STAGE_EXECVE
  | .wireTruncated => none

/-- Decode a C shim stage tag (`1..7`) into `FailureStage`. -/
def FailureStage.ofTag? (tag : UInt32) : Option FailureStage :=
  match tag.toNat with
  | 1 => some .validate
  | 2 => some .processGroup
  | 3 => some .signalReset
  | 4 => some .fdSetup
  | 5 => some .closeUnkept
  | 6 => some .chdir
  | 7 => some .execve
  | _ => none

/-- Normalize non-positive or out-of-range errnos to `Errno.EIO`. -/
def normalizeWireErrno (raw : UInt32) : Errno :=
  if 1 ≤ raw.toNat && raw.toNat ≤ 4095 then raw else Errno.EIO

/-- Pure reference decoder mapping a raw C shim error to `PostForkError`. -/
def decodeRawSpawnErr : RawSpawnErr → PostForkError
  | .sys e =>
    { kind := .sysError, errno := some (normalizeWireErrno e), childFailure := none,
      message := "postfork host syscall failed" }
  | .child wst tag e =>
    let stage := (FailureStage.ofTag? tag).getD .wireTruncated
    let code := if (FailureStage.ofTag? tag).isSome then normalizeWireErrno e else Errno.EIO
    { kind := .childFailed, errno := some code,
      childFailure := some { stage := stage, errno := code, waitStatus := some wst },
      message := "child setup or execve failed" }

/-- Compute the C shim child-setup bitmask for `spec`. -/
def flagsOfSpec {fd : Type} (spec : ChildSpecM fd) : UInt32 :=
  let fPgid : UInt32 := match spec.processGroup with | .newGroup => FLAG_SET_PGID | .inherit => 0
  let fSig : UInt32 := match spec.sigpipe with | .resetDefault => FLAG_RESET_SIGPIPE | .inherit => 0
  let fStdio : UInt32 := match spec.stdio with | .redirect .. => FLAG_REDIRECT_STDIO | .inherit => 0
  fPgid ||| fSig ||| fStdio

/-- Return `true` iff UTF-8 bytes of `s` contain an embedded NUL (`0x00`) byte. -/
def hasEmbeddedNulStr (s : String) : Bool :=
  s.toUTF8.toList.any (· == (0 : UInt8))

/-- Return `true` iff `(k, v)` is a valid NUL-free `KEY=VALUE` environment binding (`k` non-empty, no `'='`). -/
def isValidEnvBinding (kv : String × String) : Bool :=
  !kv.1.isEmpty && !kv.1.contains '=' && !hasEmbeddedNulStr kv.1 && !hasEmbeddedNulStr kv.2

/-- Return `true` iff raw byte slice `entry` contains no embedded NUL (`0x00`) byte. -/
def isValidRawEnvEntry (entry : ByteArray) : Bool :=
  !entry.toList.any (· == (0 : UInt8))

/-- Return `true` iff raw `environ(7)` slice `entry` starts with `key ++ "="` (`0x3D`). -/
def rawEnvHasKey (key entry : ByteArray) : Bool :=
  if h : key.size < entry.size then
    entry.extract 0 key.size == key && entry[key.size] == (0x3D : UInt8)
  else
    false

/-- Encode raw NUL-free `rawEnv` slices followed by formatted `(key, value)` bindings as
    NUL-terminated `ByteArray` C strings for `execve(2)`. -/
def formatEnvEntriesBytes (rawEnv : Array ByteArray) (env : Array (String × String)) : Array ByteArray :=
  let keptRaw := rawEnv.filter fun b => !env.any fun (k, _) => rawEnvHasKey k.toUTF8 b
  keptRaw.map (fun b => b.push 0) ++ env.map (fun (k, v) => s!"{k}={v}".toUTF8.push 0)

/-- Extract kept descriptor references from `FdPolicy`. -/
def FdPolicy.keepFds {fd : Type} : FdPolicy fd → Array (FdRef fd)
  | .inheritNonCloexec ks => ks
  | .closeAllAbove2Except ks => ks

/-- Return `true` iff `ref` is either a managed handle or a non-negative `.raw` FD. -/
def FdRef.isNonneg {fd : Type} : FdRef fd → Bool
  | .handle _ => true
  | .raw n => decide (n.toInt ≥ 0)

/-- Return `true` iff `r` is a raw stdio slot `0`, `1`, or `2`. -/
def FdRef.isRawStdioSlot {fd : Type} : FdRef fd → Bool
  | .raw n => n == 0 || n == 1 || n == 2
  | .handle _ => false

/-- Return `true` iff two `FdRef` values have equal `.raw` numbers. -/
def FdRef.sameRaw {fd : Type} : FdRef fd → FdRef fd → Bool
  | .raw a, .raw b => a == b
  | _, _ => false

/-- Return `true` iff `tok` has a NUL-free literal string. -/
def ArgToken.isValid {fd : Type} : ArgToken fd → Bool
  | .lit s => !hasEmbeddedNulStr s

/-- Pre-`fork` pure specification validation checking string hygiene, non-negative `.raw` FDs, empty `keepFds`, and stdio safety. -/
def validateSpec {fd : Type} (spec : ChildSpecM fd) : Bool :=
  let cwdOk := match spec.cwd with | some d => !hasEmbeddedNulStr d | none => true
  let pathOk := !spec.path.isEmpty && !hasEmbeddedNulStr spec.path
  let argvOk := spec.argv.all ArgToken.isValid
  let envOk := spec.env.all isValidEnvBinding && spec.rawEnv.all isValidRawEnvEntry
  let keepEmpty := (FdPolicy.keepFds spec.fdPolicy).isEmpty
  let closeOk := spec.closeFds.all (fun r => FdRef.isNonneg r && !FdRef.isRawStdioSlot r)
  let stdioOk := match spec.stdio with
    | .inherit => true
    | .redirect sIn sOut sErr _ =>
      FdRef.isNonneg sIn && FdRef.isNonneg sOut && FdRef.isNonneg sErr &&
      !(spec.closeFds.any (fun c => FdRef.sameRaw c sIn || FdRef.sameRaw c sOut || FdRef.sameRaw c sErr))
  pathOk && cwdOk && argvOk && envOk && keepEmpty && closeOk && stdioOk

end LeanSwe.PostFork.Model
