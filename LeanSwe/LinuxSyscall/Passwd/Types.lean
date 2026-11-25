import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Passwd

open LeanSwe.LinuxSyscall

/-- Maximum username byte length (`1 MiB`) enforced before copying into C `getpwnam_r`. -/
def MAX_PASSWD_NAME_BYTES : Nat := 1048576

/-- Return `true` iff `name` contains no embedded `0x00` byte. -/
def validPasswdName (name : ByteArray) : Bool :=
  !hasEmbeddedNul name

/-- Portable POSIX `<pwd.h>` entry (`struct passwd`) preserving raw C byte fields. -/
structure PasswdEntry where
  /-- Login username (`pw_name`). -/
  name : ByteArray
  /-- Numeric user ID (`pw_uid`). -/
  uid : UInt32
  /-- Primary numeric group ID (`pw_gid`). -/
  gid : UInt32
  /-- User full name / GECOS field (`pw_gecos`). -/
  gecos : ByteArray
  /-- Home directory path bytes (`pw_dir`). -/
  homeDir : ByteArray
  /-- Login shell path bytes (`pw_shell`). -/
  shell : ByteArray
  deriving DecidableEq, Inhabited

instance : BEq PasswdEntry where
  beq a b := decide (a = b)

instance : LawfulBEq PasswdEntry where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Format a `ByteArray` in `#[b0, b1, ...]` notation in `O(N)` time and `O(1)` C stack without `ByteArray.data` or `Std.Format` recursion. -/
def formatPasswdBytes (bs : ByteArray) : String := Id.run do
  let n := bs.size
  if n == 0 then
    return "#[]"
  let mut out := "#["
  for i in [0:n] do
    if i > 0 then
      out := out ++ ", "
    out := out ++ toString bs[i]!.toNat
  return out ++ "]"

/-- Format a `PasswdEntry` in `O(N)` time and `O(1)` C stack. -/
def formatPasswdEntry (e : PasswdEntry) : String :=
  "{ name := " ++ formatPasswdBytes e.name ++
  s!", uid := {e.uid}, gid := {e.gid}, gecos := " ++ formatPasswdBytes e.gecos ++
  ", homeDir := " ++ formatPasswdBytes e.homeDir ++
  ", shell := " ++ formatPasswdBytes e.shell ++ " }"

instance : Repr PasswdEntry where
  reprPrec e _ := formatPasswdEntry e

/-- Decode `PasswdEntry.name` as valid UTF-8, returning `none` if `pw_name` is non-UTF-8. -/
def PasswdEntry.nameUtf8? (e : PasswdEntry) : Option String :=
  String.fromUTF8? e.name

/-- Decode `PasswdEntry.gecos` as valid UTF-8, returning `none` if `pw_gecos` is non-UTF-8. -/
def PasswdEntry.gecosUtf8? (e : PasswdEntry) : Option String :=
  String.fromUTF8? e.gecos

/-- Decode `PasswdEntry.homeDir` as valid UTF-8, returning `none` if `pw_dir` is non-UTF-8. -/
def PasswdEntry.homeDirUtf8? (e : PasswdEntry) : Option String :=
  String.fromUTF8? e.homeDir

/-- Decode `PasswdEntry.shell` as valid UTF-8, returning `none` if `pw_shell` is non-UTF-8. -/
def PasswdEntry.shellUtf8? (e : PasswdEntry) : Option String :=
  String.fromUTF8? e.shell

/-- Return `true` iff all byte fields of `e` are free of embedded `0x00` bytes. -/
def PasswdEntry.hasNoEmbeddedNul (e : PasswdEntry) : Bool :=
  !hasEmbeddedNul e.name && !hasEmbeddedNul e.gecos &&
    !hasEmbeddedNul e.homeDir && !hasEmbeddedNul e.shell

/-- Semantic classification of `LinuxSyscall.Passwd` `Errno` outcomes for error-coverage auditing. -/
inductive PasswdErrorKind where
  /-- Invalid caller input such as an embedded NUL byte in `getpwnam` (`EINVAL`). -/
  | invalidArg
  /-- Permission or capability rejection (`EPERM`, `EACCES`). -/
  | permissionDenied
  /-- Transient or resource OS/NSS failure (`ERANGE`, `EINTR`, `EIO`, `EMFILE`, `ENFILE`, `ENOMEM`, or other OS errno). -/
  | transientOrResource
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Classify any Linux `Errno` into a `PasswdErrorKind`. -/
def PasswdErrorKind.ofErrno (e : Errno) : PasswdErrorKind :=
  if e == Errno.EINVAL then .invalidArg
  else if e == Errno.EPERM || e == Errno.EACCES then .permissionDenied
  else .transientOrResource

/-- Monadic capability bundle for POSIX `<pwd.h>` lookups, parameterized over effect monad `m`. -/
structure PasswdOpsM (m : Type → Type) where
  /-- Look up the `PasswdEntry` for numeric `uid` via reentrant `getpwuid_r(3)`. -/
  getpwuid : UInt32 → m (Except Errno (Option PasswdEntry))
  /-- Look up the `PasswdEntry` for raw username `name` via reentrant `getpwnam_r(3)`. -/
  getpwnam : ByteArray → m (Except Errno (Option PasswdEntry))

/-- Real-world `IO` specialization of `PasswdOpsM`. -/
abbrev PasswdOps := PasswdOpsM IO

/-- Raw C-ABI tuple returned by `passwd_shim.c` (`(name, uid, gid, gecos, homeDir, shell)`). -/
abbrev Internal.RawPasswdTuple :=
  ByteArray × UInt32 × UInt32 × ByteArray × ByteArray × ByteArray

/-- Internal single-call C-ABI hooks supplied by `Interface.lean` and backed by `passwd_shim.c`. -/
structure Internal.PosixPasswdOpsM (m : Type → Type) where
  /-- Single-call `getpwuid_r(3)` hook accepting `(uid, bufBytes)`. -/
  getpwuidOnce : UInt32 → UInt32 → m (Except Errno (Option Internal.RawPasswdTuple))
  /-- Single-call `getpwnam_r(3)` hook accepting `(name, bufBytes)`. -/
  getpwnamOnce : ByteArray → UInt32 → m (Except Errno (Option Internal.RawPasswdTuple))

/-- Real-world `IO` specialization of `Internal.PosixPasswdOpsM`. -/
abbrev Internal.PosixPasswdOps := Internal.PosixPasswdOpsM IO

end LeanSwe.LinuxSyscall.Passwd
