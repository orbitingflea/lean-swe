import LeanSwe.LinuxSyscall.Passwd.Types
import Std.Data.TreeMap.Basic

namespace LeanSwe.LinuxSyscall.Passwd

open LeanSwe.LinuxSyscall

/-- Abstract request modeled by `LeanSwe.LinuxSyscall.Passwd`. -/
inductive PasswdReq where
  /-- Call `getpwuid uid`. -/
  | getpwuid (uid : UInt32)
  /-- Call `getpwnam name`. -/
  | getpwnam (name : ByteArray)
  deriving DecidableEq, BEq

instance : Repr PasswdReq where
  reprPrec
    | .getpwuid uid, _ => s!"PasswdReq.getpwuid {uid}"
    | .getpwnam name, _ => "PasswdReq.getpwnam " ++ formatPasswdBytes name

/-- Abstract outcome returned by `LeanSwe.LinuxSyscall.Passwd` operations. -/
inductive PasswdOutcome where
  /-- NSS returned a matching `PasswdEntry`. -/
  | found (entry : PasswdEntry)
  /-- NSS succeeded (`rc == 0`) with `res == NULL` (no entry). -/
  | notFound
  /-- Operation returned an `Errno`. -/
  | err (errno : Errno)
  deriving DecidableEq, BEq

instance : Repr PasswdOutcome where
  reprPrec
    | .found e, _ => s!"PasswdOutcome.found {repr e}"
    | .notFound, _ => "PasswdOutcome.notFound"
    | .err e, _ => s!"PasswdOutcome.err {e}"

/-- Convert an `Except Errno (Option PasswdEntry)` into a `PasswdOutcome`. -/
def outcomeOfEntryOpt : Except Errno (Option PasswdEntry) → PasswdOutcome
  | .ok (some entry) => .found entry
  | .ok none => .notFound
  | .error e => .err e

/-- Executable stateful world model for `LinuxSyscall.Passwd` (`getpwuid`, `getpwnam`). -/
structure PasswdState where
  /-- Per-UID NSS knowledge preserving determinism across repeated `getpwuid` queries. -/
  byUid : Std.TreeMap UInt32 (Option PasswdEntry) := ∅
  /-- Per-name NSS knowledge preserving determinism across repeated `getpwnam` queries. -/
  byName : Std.TreeMap ByteArray (Option PasswdEntry) := ∅
  /-- Whether an ambient outer `seccomp` filter (`SECCOMP_RET_ERRNO`) may preempt calls before argument validation (`EFAULT` excluded) or trigger NSS `[UNAVAIL=continue]` fallback. -/
  ambientSeccomp : Bool := false
  /-- Whether transient NSS `[UNAVAIL=continue]` fallback (e.g. `EMFILE`/`ENFILE` exhausting earlier NSS backends so `nss_systemd` answers) is active. -/
  transientNssUnavail : Bool := false
  deriving Inhabited

private def formatOptPasswdEntry : Option PasswdEntry → String
  | none => "none"
  | some e => "(some " ++ formatPasswdEntry e ++ ")"

instance : Repr PasswdState where
  reprPrec s _ := Id.run do
    let (_, uidBody) := s.byUid.foldl (fun (first, acc) k v =>
      let sep := if first then "" else ", "
      (false, acc ++ sep ++ s!"({k}, {formatOptPasswdEntry v})")) (true, "")
    let (_, namBody) := s.byName.foldl (fun (first, acc) k v =>
      let sep := if first then "" else ", "
      (false, acc ++ sep ++ "(" ++ formatPasswdBytes k ++ ", " ++ formatOptPasswdEntry v ++ ")")) (true, "")
    return "{ byUid := [" ++ uidBody ++ "], byName := [" ++ namBody ++
      s!"], ambientSeccomp := {s.ambientSeccomp}, transientNssUnavail := {s.transientNssUnavail} }"

/-- Initial empty `PasswdState` (`byUid = ∅`, `byName = ∅`, `ambientSeccomp = false`, `transientNssUnavail = false`). -/
def PasswdState.initial : PasswdState :=
  { byUid := ∅, byName := ∅, ambientSeccomp := false, transientNssUnavail := false }

/-- Enable ambient outer `seccomp` `SECCOMP_RET_ERRNO` preemption on a `PasswdState`. -/
def PasswdState.withOuterSeccomp (s : PasswdState := PasswdState.initial) : PasswdState :=
  { s with ambientSeccomp := true }

/-- Enable transient NSS `[UNAVAIL=continue]` fallback (e.g. `EMFILE`/`ENFILE` causing fallback to `nss_systemd`) on a `PasswdState`. -/
def PasswdState.withTransientNssUnavail (s : PasswdState := PasswdState.initial) : PasswdState :=
  { s with transientNssUnavail := true }

/-- Look up the recorded `Option PasswdEntry` for `uid` in `db`. -/
def lookupPasswdByUid (db : Std.TreeMap UInt32 (Option PasswdEntry)) (uid : UInt32) :
    Option (Option PasswdEntry) :=
  db.get? uid

/-- Insert or replace the recorded `Option PasswdEntry` for `uid` in `db`. -/
def setPasswdByUid (db : Std.TreeMap UInt32 (Option PasswdEntry)) (uid : UInt32)
    (v : Option PasswdEntry) : Std.TreeMap UInt32 (Option PasswdEntry) :=
  db.insert uid v

/-- Look up the recorded `Option PasswdEntry` for `name` in `db`. -/
def lookupPasswdByName (db : Std.TreeMap ByteArray (Option PasswdEntry)) (name : ByteArray) :
    Option (Option PasswdEntry) :=
  db.get? name

/-- Insert or replace the recorded `Option PasswdEntry` for `name` in `db`. -/
def setPasswdByName (db : Std.TreeMap ByteArray (Option PasswdEntry)) (name : ByteArray)
    (v : Option PasswdEntry) : Std.TreeMap ByteArray (Option PasswdEntry) :=
  db.insert name v

/-- Check well-formedness of a `byUid` table entry (`uid` match and no embedded NULs). -/
def isValidUidEntry (uid : UInt32) : Option PasswdEntry → Bool
  | none => true
  | some e => e.hasNoEmbeddedNul && e.uid == uid

/-- Check well-formedness of a `byName` table entry (`validPasswdName`, length `≤ MAX_PASSWD_NAME_BYTES`, `name` match, and no embedded NULs). -/
def isValidNameEntry (name : ByteArray) : Option PasswdEntry → Bool
  | none => validPasswdName name && decide (name.size ≤ MAX_PASSWD_NAME_BYTES)
  | some e =>
    validPasswdName name && decide (name.size ≤ MAX_PASSWD_NAME_BYTES) &&
      e.hasNoEmbeddedNul && e.name == name

/-- Return `true` iff every entry in `s.byUid` and `s.byName` is well-formed. -/
def PasswdState.isWellFormed (s : PasswdState) : Bool :=
  s.byUid.foldl (fun acc k v => acc && isValidUidEntry k v) true &&
    s.byName.foldl (fun acc k v => acc && isValidNameEntry k v) true

/-- Return `true` iff `e` is an allowed OS/NSS errno from `getpwuid`/`getpwnam` (`ERANGE`, `EINTR`, `EIO`, `EMFILE`, `ENFILE`, `ENOMEM`, `EPERM`, `EACCES`, `ENOENT`, `ENXIO`, `EAGAIN`, `ENODEV`, `ENOTDIR`, `EISDIR`, `ESPIPE`, `ENAMETOOLONG`, `ELOOP`). -/
def isAllowedPasswdOsErrno (e : Errno) : Bool :=
  e == Errno.ERANGE || e == Errno.EINTR || e == Errno.EIO || e == Errno.EMFILE ||
  e == Errno.ENFILE || e == Errno.ENOMEM || e == Errno.EPERM || e == Errno.EACCES ||
  e == Errno.ENOENT || e == Errno.ENXIO || e == Errno.EAGAIN || e == Errno.ENODEV ||
  e == Errno.ENOTDIR || e == Errno.EISDIR || e == Errno.ESPIPE || e == Errno.ENAMETOOLONG ||
  e == Errno.ELOOP

/-- Core NSS step checker for `getpwuid` and `getpwnam` without outer `seccomp` preemption. -/
def allowedStepCore (s : PasswdState) (req : PasswdReq) (out : PasswdOutcome) : Option PasswdState :=
  match req with
  | .getpwuid uid =>
    match lookupPasswdByUid s.byUid uid with
    | none =>
      match out with
      | .notFound =>
        some { s with byUid := setPasswdByUid s.byUid uid none }
      | .found entry =>
        if entry.hasNoEmbeddedNul && entry.uid == uid then
          some { s with byUid := setPasswdByUid s.byUid uid (some entry) }
        else
          none
      | .err e =>
        if isAllowedPasswdOsErrno e then some s else none
    | some none =>
      match out with
      | .notFound => some s
      | .found _ => none
      | .err e => if isAllowedPasswdOsErrno e then some s else none
    | some (some expected) =>
      match out with
      | .notFound => none
      | .found entry =>
        if entry == expected && entry.hasNoEmbeddedNul && entry.uid == uid then some s else none
      | .err e => if isAllowedPasswdOsErrno e then some s else none
  | .getpwnam name =>
    if !validPasswdName name then
      match out with
      | .err e => if e == Errno.EINVAL then some s else none
      | _ => none
    else if name.size > MAX_PASSWD_NAME_BYTES then
      match out with
      | .err e => if e == Errno.ENAMETOOLONG then some s else none
      | _ => none
    else
      match lookupPasswdByName s.byName name with
      | none =>
        match out with
        | .notFound =>
          some { s with byName := setPasswdByName s.byName name none }
        | .found entry =>
          if entry.hasNoEmbeddedNul && entry.name == name then
            some { s with byName := setPasswdByName s.byName name (some entry) }
          else
            none
        | .err e =>
          if isAllowedPasswdOsErrno e then some s else none
      | some none =>
        match out with
        | .notFound => some s
        | .found _ => none
        | .err e => if isAllowedPasswdOsErrno e then some s else none
      | some (some expected) =>
        match out with
        | .notFound => none
        | .found entry =>
          if entry == expected && entry.hasNoEmbeddedNul && entry.name == name then some s else none
        | .err e => if isAllowedPasswdOsErrno e then some s else none

/-- Return `true` iff `req` is rejected in pure Lean user-space (`getpwnam` with embedded NUL or length `> MAX_PASSWD_NAME_BYTES`) before any syscall can execute. -/
def isUserspaceInvalidReq : PasswdReq → Bool
  | .getpwuid _ => false
  | .getpwnam name => !validPasswdName name || name.size > MAX_PASSWD_NAME_BYTES

/-- Return `true` iff `out` is a well-formed NSS `[UNAVAIL=continue]` fallback outcome (`.notFound` or key-consistent NUL-free `.found`) for `req`. -/
def isValidNssFallbackOutcome (req : PasswdReq) : PasswdOutcome → Bool
  | .notFound => true
  | .found entry =>
    entry.hasNoEmbeddedNul &&
      match req with
      | .getpwuid uid => entry.uid == uid
      | .getpwnam name => entry.name == name
  | .err _ => false

/-- Relational step checker for `LeanSwe.LinuxSyscall.Passwd` (`some s'` iff `out` is a legal NSS/OS outcome for `req` in state `s`). -/
def allowedStep (s : PasswdState) (req : PasswdReq) (out : PasswdOutcome) : Option PasswdState :=
  match allowedStepCore s req out with
  | some s' => some s'
  | none =>
    if !isUserspaceInvalidReq req then
      match out with
      | .err e =>
        if s.ambientSeccomp && e != Errno.EFAULT && 1 ≤ e.toNat && e.toNat ≤ 4095 then
          some s
        else
          none
      | _ =>
        if (s.ambientSeccomp || s.transientNssUnavail) && isValidNssFallbackOutcome req out then
          some s
        else
          none
    else
      none

/-- Executable reference `PasswdOpsM (StateM PasswdState)` witnessing exact `Passwd` contracts. -/
def modelOps : PasswdOpsM (StateM PasswdState) :=
  { getpwuid := fun uid => do
      let s ← get
      match lookupPasswdByUid s.byUid uid with
      | none =>
        set { s with byUid := setPasswdByUid s.byUid uid none }
        return .ok none
      | some none =>
        return .ok none
      | some (some entry) =>
        if entry.hasNoEmbeddedNul && entry.uid == uid then
          return .ok (some entry)
        else
          return .error Errno.EIO
    getpwnam := fun name => do
      if !validPasswdName name then
        return .error Errno.EINVAL
      if name.size > MAX_PASSWD_NAME_BYTES then
        return .error Errno.ENAMETOOLONG
      let s ← get
      match lookupPasswdByName s.byName name with
      | none =>
        set { s with byName := setPasswdByName s.byName name none }
        return .ok none
      | some none =>
        return .ok none
      | some (some entry) =>
        if entry.hasNoEmbeddedNul && entry.name == name then
          return .ok (some entry)
        else
          return .error Errno.EIO }

end LeanSwe.LinuxSyscall.Passwd
