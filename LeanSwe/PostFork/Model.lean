import Std.Data.HashSet
import LeanSwe.PostFork.Types

namespace LeanSwe.PostFork.Model

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork

/-- Failure-wire magic byte (`0x50` = `'P'`). -/
def WIRE_MAGIC : UInt8 := 0x50

/-- Failure-wire protocol version byte (`0x01`). -/
def WIRE_VERSION : UInt8 := 0x01

/-- Wire stage tag for pre-execution validation errors (`1`). -/
def STAGE_VALIDATE : UInt8 := 1
/-- Wire stage tag for `setpgid(0, 0)` errors (`2`). -/
def STAGE_PROCESS_GROUP : UInt8 := 2
/-- Wire stage tag for `SIGPIPE` reset/unblock errors (`3`). -/
def STAGE_SIGNAL_RESET : UInt8 := 3
/-- Wire stage tag for FD probe/relocation/stdio/cloexec errors (`4`). -/
def STAGE_FD_SETUP : UInt8 := 4
/-- Wire stage tag for `close_fds_above2_except` errors (`5`). -/
def STAGE_CLOSE_UNKEPT : UInt8 := 5
/-- Wire stage tag for `chdir` errors (`6`). -/
def STAGE_CHDIR : UInt8 := 6
/-- Wire stage tag for `execve` errors (`7`). -/
def STAGE_EXECVE : UInt8 := 7

/-- Child flag bit `0`: invoke `setpgid(0, 0)`. -/
def FLAG_SET_PGID : UInt32 := 1
/-- Child flag bit `1`: reset `SIGPIPE` to `SIG_DFL` and unblock `SIGPIPE`. -/
def FLAG_RESET_SIGPIPE : UInt32 := 2
/-- Child flag bit `2`: wait for 1-byte token on `sync_r` (`_exit(125)` on EOF). -/
def FLAG_HAS_SYNC_BARRIER : UInt32 := 4
/-- Child flag bit `3`: redirect `(stdin, stdout, stderr)` onto `(0, 1, 2)` and relocate `rep_w`. -/
def FLAG_REDIRECT_STDIO : UInt32 := 8
/-- Child flag bit `4`: close unkept descriptors `> 2` via `close_range` + `/proc/self/fd`. -/
def FLAG_CLOSE_UNKEPT_ABOVE2 : UInt32 := 16
/-- Child flag bit `5`: close redirected stdio source descriptors `> 2` in `setup_stdio`. -/
def FLAG_CLOSE_STDIO_SOURCES : UInt32 := 32

/-- Map a `FailureStage` to its wire tag byte (`none` for host-only `.wireTruncated`). -/
def FailureStage.toTag? : FailureStage → Option UInt8
  | .validate => some STAGE_VALIDATE
  | .processGroup => some STAGE_PROCESS_GROUP
  | .signalReset => some STAGE_SIGNAL_RESET
  | .fdSetup => some STAGE_FD_SETUP
  | .closeUnkept => some STAGE_CLOSE_UNKEPT
  | .chdir => some STAGE_CHDIR
  | .execve => some STAGE_EXECVE
  | .wireTruncated => none

/-- Decode a wire stage tag byte (`1..7`). -/
def FailureStage.ofTag? (tag : UInt8) : Option FailureStage :=
  match tag.toNat with
  | 1 => some .validate
  | 2 => some .processGroup
  | 3 => some .signalReset
  | 4 => some .fdSetup
  | 5 => some .closeUnkept
  | 6 => some .chdir
  | 7 => some .execve
  | _ => none

/-- Total 2's-complement 32-bit signed integer comparison. -/
@[inline] def i32Le (a b : Int32) : Bool :=
  decide (a.toInt ≤ b.toInt)

/-- Construct a `ChildFailure` normalizing non-positive/out-of-range errnos to `Errno.EIO`. -/
def normalizeWireErrno (raw : UInt32) : Errno :=
  if 1 ≤ raw.toNat && raw.toNat ≤ 4095 then raw else Errno.EIO

/-- Pack a signed 32-bit integer in 4 little-endian bytes. -/
def packI32Le (v : Int32) : ByteArray :=
  let u := v.toUInt32.toNat
  ByteArray.mk #[
    UInt8.ofNat (u % 256),
    UInt8.ofNat ((u / 256) % 256),
    UInt8.ofNat ((u / 65536) % 256),
    UInt8.ofNat ((u / 16777216) % 256)
  ]

/-- Concatenate two `ByteArray` values cleanly without internal kernel wrappers. -/
def appendBytes (a b : ByteArray) : ByteArray :=
  b.foldl (fun acc x => acc.push x) a

/-- Concatenate a list of packed `Int32` values into little-endian bytes. -/
def packI32LeList (xs : List Int32) : ByteArray :=
  xs.foldl (fun acc x => appendBytes acc (packI32Le x)) ByteArray.empty

/-- Encode a child failure `(stage, errno)` into the uniform 8-byte wire frame `[0x50, 0x01, stage, 0x00, err_le32]`. -/
def encodeFailureReport (stage : FailureStage) (err : Errno) : ByteArray :=
  let tag := (FailureStage.toTag? stage).getD STAGE_EXECVE
  let e := normalizeWireErrno err
  let u := e.toNat
  ByteArray.mk #[
    WIRE_MAGIC,
    WIRE_VERSION,
    tag,
    0,
    UInt8.ofNat (u % 256),
    UInt8.ofNat ((u / 256) % 256),
    UInt8.ofNat ((u / 65536) % 256),
    UInt8.ofNat ((u / 16777216) % 256)
  ]

/-- Decode the uniform 8-byte failure report read from `repR` (`none` on 0-byte `EOF` indicating `execve` succeeded). -/
def decodeChildFailure (bs : ByteArray) : Option ChildFailure :=
  if bs.size == 0 then
    none
  else if bs.size != 8 then
    some { stage := .wireTruncated, errno := Errno.EIO }
  else
    let b0 := bs.get! 0
    let b1 := bs.get! 1
    let b2 := bs.get! 2
    let b3 := bs.get! 3
    if b0 != WIRE_MAGIC || b1 != WIRE_VERSION || b3 != 0 then
      some { stage := .wireTruncated, errno := Errno.EIO }
    else
      match FailureStage.ofTag? b2 with
      | none => some { stage := .wireTruncated, errno := Errno.EIO }
      | some stage =>
        let e0 := (bs.get! 4).toNat
        let e1 := (bs.get! 5).toNat
        let e2 := (bs.get! 6).toNat
        let e3 := (bs.get! 7).toNat
        let rawU := e0 + 256 * e1 + 65536 * e2 + 16777216 * e3
        if 1 ≤ rawU && rawU ≤ 4095 then
          some { stage := stage, errno := UInt32.ofNat rawU }
        else
          some { stage := .wireTruncated, errno := Errno.EIO }

/-- Compute the `LEANSWE_PF_FLAG_*` child setup bitmask for `(spec, withBarrier)`. -/
def flagsOfSpec {fd : Type} (spec : ChildSpecM fd) (withBarrier : Bool) : UInt32 :=
  let fPgid : UInt32 := match spec.processGroup with | .newGroup => FLAG_SET_PGID | .inherit => 0
  let fSig : UInt32 := match spec.sigpipe with | .resetDefault => FLAG_RESET_SIGPIPE | .inherit => 0
  let fSync : UInt32 := if withBarrier then FLAG_HAS_SYNC_BARRIER else 0
  let fStdio : UInt32 := match spec.stdio with | .redirect .. => FLAG_REDIRECT_STDIO | .inherit => 0
  let fClose : UInt32 := match spec.fdPolicy with | .closeAllAbove2Except _ => FLAG_CLOSE_UNKEPT_ABOVE2 | .inheritNonCloexec _ => 0
  let fCloseSrc : UInt32 := match spec.stdio, spec.fdPolicy with
    | .redirect _ _ _ true, .inheritNonCloexec _ => FLAG_CLOSE_STDIO_SOURCES
    | _, _ => 0
  fPgid ||| fSig ||| fSync ||| fStdio ||| fClose ||| fCloseSrc

/-- Return `true` iff UTF-8 bytes of `s` contain an embedded NUL (`0x00`) byte. -/
def hasEmbeddedNulStr (s : String) : Bool :=
  s.toUTF8.toList.any (· == (0 : UInt8))

/-- Return `true` iff `(k, v)` is a valid NUL-free `KEY=VALUE` environment binding (`k` non-empty, no `'='`). -/
def isValidEnvBinding (kv : String × String) : Bool :=
  !kv.1.isEmpty && !kv.1.contains '=' && !hasEmbeddedNulStr kv.1 && !hasEmbeddedNulStr kv.2

/-- Return `true` iff raw byte slice `entry` contains no embedded NUL (`0x00`) byte. -/
def isValidRawEnvEntry (entry : ByteArray) : Bool :=
  !entry.toList.any (· == (0 : UInt8))

/-- Format valid `(key, value)` bindings as `"KEY=VALUE"` C strings. -/
def formatEnvEntries (env : Array (String × String)) : Array String :=
  env.map (fun (k, v) => s!"{k}={v}")

/-- Return `true` iff raw `environ(7)` slice `entry` starts with `key ++ "="` (`0x3D`). -/
def rawEnvHasKey (key entry : ByteArray) : Bool :=
  if h : key.size < entry.size then
    entry.extract 0 key.size == key && entry[key.size] == (0x3D : UInt8)
  else
    false

/-- Encode raw NUL-free `rawEnv` slices followed by formatted `(key, value)` bindings as
    NUL-terminated `ByteArray` C strings for `execve(2)`. Entries in `rawEnv` whose key before `'='`
    matches an explicit `env` binding are filtered out so `env` takes precedence over `rawEnv`. -/
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

/-- Return `true` iff two `FdRef` values denote the exact same descriptor (`eqFd` on handles or equal `.raw`). -/
def FdRef.sameRef {fd : Type} (eqFd : fd → fd → Bool) : FdRef fd → FdRef fd → Bool
  | .handle a, .handle b => eqFd a b
  | .raw a, .raw b => a == b
  | _, _ => false

/-- Return `true` iff `tok` has NUL-free strings and non-negative `.raw` FD reference. -/
def ArgToken.isValid {fd : Type} : ArgToken fd → Bool
  | .lit s => !hasEmbeddedNulStr s
  | .fdDecimal r => FdRef.isNonneg r
  | .prefixedFd p r s => !hasEmbeddedNulStr p && !hasEmbeddedNulStr s && FdRef.isNonneg r

/-- Extract the optional `FdRef` inside an `ArgToken`. -/
def ArgToken.ref? {fd : Type} : ArgToken fd → Option (FdRef fd)
  | .lit _ => none
  | .fdDecimal r => some r
  | .prefixedFd _ r _ => some r

/-- Return `true` iff `r` is a raw stdio slot `0`, `1`, or `2`. -/
def FdRef.isRawStdioSlot {fd : Type} : FdRef fd → Bool
  | .raw n => n == 0 || n == 1 || n == 2
  | .handle _ => false

/-- Return `true` iff `closeFds` and `keepFds` share no common descriptor under `eqFd` (`O(N)` on `.raw` descriptors via `Std.HashSet`, and `O(N)` overall when `checkHandles = false`). -/
def disjointFdRefArrays {fd : Type} (eqFd : fd → fd → Bool)
    (closeFds keepFds : Array (FdRef fd)) (checkHandles : Bool := true) : Bool :=
  if closeFds.size ≤ 8 || keepFds.size ≤ 8 then
    if !checkHandles then
      !(closeFds.any (fun c => keepFds.any (FdRef.sameRef (fun _ _ => false) c)))
    else
      !(closeFds.any (fun c => keepFds.any (FdRef.sameRef eqFd c)))
  else
    let rawKeep : Std.HashSet Int32 :=
      keepFds.foldl (fun acc r => match r with | .raw n => acc.insert n | .handle _ => acc)
        (Std.HashSet.emptyWithCapacity keepFds.size)
    if closeFds.any (fun r => match r with | .raw n => rawKeep.contains n | .handle _ => false) then
      false
    else if !checkHandles then
      true
    else
      let closeHandles := closeFds.filterMap (fun r => match r with | .handle h => some h | .raw _ => none)
      let keepHandles := keepFds.filterMap (fun r => match r with | .handle h => some h | .raw _ => none)
      !(closeHandles.any (fun ch => keepHandles.any (eqFd ch)))

/-- Pre-`fork` pure specification validation parameterized by handle equality `eqFd` (`fun _ _ => false` for opaque handles). -/
def validateSpecWith {fd : Type} (eqFd : fd → fd → Bool) (spec : ChildSpecM fd)
    (checkHandles : Bool := true) : Bool :=
  let cwdOk := match spec.cwd with | some d => !hasEmbeddedNulStr d | none => true
  let pathOk := !spec.path.isEmpty && !hasEmbeddedNulStr spec.path
  let argvOk := spec.argv.all ArgToken.isValid
  let envOk := spec.env.all isValidEnvBinding && spec.rawEnv.all isValidRawEnvEntry
  let keepFds := FdPolicy.keepFds spec.fdPolicy
  let closeOk := spec.closeFds.all FdRef.isNonneg
  let keepOk := keepFds.all FdRef.isNonneg
  let stdioOk := match spec.stdio with
    | .inherit => true
    | .redirect sIn sOut sErr closeSrcs =>
      FdRef.isNonneg sIn && FdRef.isNonneg sOut && FdRef.isNonneg sErr &&
      !(keepFds.any FdRef.isRawStdioSlot) &&
      !(spec.closeFds.any (fun c => FdRef.sameRef eqFd c sIn || FdRef.sameRef eqFd c sOut || FdRef.sameRef eqFd c sErr)) &&
      match spec.fdPolicy with
      | .inheritNonCloexec _ =>
        if !closeSrcs then true
        else !(keepFds.any (fun k =>
          (!FdRef.isRawStdioSlot k) &&
          (FdRef.sameRef eqFd k sIn || FdRef.sameRef eqFd k sOut || FdRef.sameRef eqFd k sErr)))
      | .closeAllAbove2Except _ => true
  let disjointCloseKeep := disjointFdRefArrays eqFd spec.closeFds keepFds checkHandles
  pathOk && cwdOk && argvOk && envOk && closeOk && keepOk && stdioOk && disjointCloseKeep

/-- Default pure validation checking string hygiene, signs, stdio slots, and `.raw` overlaps in linear `O(N)` time. -/
def validateSpec {fd : Type} (spec : ChildSpecM fd) : Bool :=
  validateSpecWith (fun _ _ => false) spec false

end LeanSwe.PostFork.Model
