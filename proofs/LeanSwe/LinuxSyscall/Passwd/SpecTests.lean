import Core.NondetTest
import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.LinuxSyscall.Passwd.Model

namespace LeanSwe.LinuxSyscall.Passwd

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

/-- `MAX_PASSWD_NAME_BYTES` equals `1048576` (`1 MiB`), `Errno.isTransientOsErrno` excludes `EFAULT`, and `PasswdErrorKind.ofErrno` classifies every `Errno` into its exact semantic bucket. -/
def test_passwd_errno_classificationAndTransient
    {runner} [NondetTest runner]
    (isTransient : Errno → Bool := Errno.isTransientOsErrno)
    (classify : Errno → PasswdErrorKind := PasswdErrorKind.ofErrno)
    (maxNameBytes : Nat := MAX_PASSWD_NAME_BYTES) : runner Unit := do
  let e ← nondet Errno
  NondetTest.assert (maxNameBytes = 1048576)
  NondetTest.assert (isTransient Errno.EFAULT = false)
  NondetTest.assert (isTransient e =
    (e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOMEM ||
     e == Errno.ENFILE || e == Errno.EMFILE || e == Errno.ENOSPC))
  NondetTest.assert (classify e =
    (if e == Errno.EINVAL then .invalidArg
     else if e == Errno.EPERM || e == Errno.EACCES then .permissionDenied
     else .transientOrResource))
  NondetTest.assert (classify Errno.EINVAL = .invalidArg)
  NondetTest.assert (classify Errno.EPERM = .permissionDenied)
  NondetTest.assert (classify Errno.EACCES = .permissionDenied)
  NondetTest.assert (classify Errno.ERANGE = .transientOrResource)
  NondetTest.assert (classify Errno.EINTR = .transientOrResource)
  NondetTest.assert (classify Errno.EIO = .transientOrResource)
  NondetTest.assert (classify Errno.EMFILE = .transientOrResource)
  NondetTest.assert (classify Errno.ENFILE = .transientOrResource)
  NondetTest.assert (classify Errno.ENOMEM = .transientOrResource)

/-- `PasswdEntry` UTF-8 accessors delegate cleanly to `String.fromUTF8?` and `hasNoEmbeddedNul` checks all four byte fields (`name`, `gecos`, `homeDir`, `shell`). -/
def test_passwd_entry_utf8Accessors
    {runner} [NondetTest runner]
    (homeDirUtf8 : PasswdEntry → Option String := PasswdEntry.homeDirUtf8?) : runner Unit := do
  let entry ← nondet PasswdEntry
  NondetTest.assert (entry.nameUtf8? = String.fromUTF8? entry.name)
  NondetTest.assert (entry.gecosUtf8? = String.fromUTF8? entry.gecos)
  NondetTest.assert (homeDirUtf8 entry = String.fromUTF8? entry.homeDir)
  NondetTest.assert (entry.shellUtf8? = String.fromUTF8? entry.shell)
  NondetTest.assert (entry.hasNoEmbeddedNul =
    (validPasswdName entry.name && validPasswdName entry.gecos &&
      validPasswdName entry.homeDir && validPasswdName entry.shell))
  let nonUtf8Dir := ByteArray.mk #[47, 0xFF, 0xFE]
  let badDirEntry : PasswdEntry :=
    { name := asciiBytes ['u']
      uid := 1000
      gid := 1000
      gecos := ByteArray.empty
      homeDir := nonUtf8Dir
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }
  NondetTest.assert (badDirEntry.hasNoEmbeddedNul = true)
  NondetTest.assert (badDirEntry.homeDirUtf8? = none)
  NondetTest.assert (outcomeOfEntryOpt (.ok (some badDirEntry)) = .found badDirEntry)

/-- `modelOps` rejects invalid (`EINVAL`) and oversized (`ENAMETOOLONG`) `getpwnam` names without mutating state, returns `.ok none` on absent UIDs/names, and deterministically returns present `PasswdEntry` records. -/
def test_passwd_ops_exactContracts
    {runner} [NondetTest runner]
    (ops : PasswdOpsM (StateM PasswdState)) : runner Unit := do
  let s₀ ← nondet PasswdState
  let uid ← nondet UInt32
  let name ← nondet ByteArray
  let badName ← nondet ByteArray
  let overCapName ← nondet ByteArray
  let entry ← nondet PasswdEntry
  assume (s₀.isWellFormed = true)
  assume (validPasswdName badName = false)
  assume (validPasswdName overCapName = true)
  assume (overCapName.size > MAX_PASSWD_NAME_BYTES)
  assume (validPasswdName name = true)
  assume (name.size ≤ MAX_PASSWD_NAME_BYTES)
  assume (entry.hasNoEmbeddedNul = true)
  assume (entry.uid = uid)
  assume (entry.name = name)
  NondetTest.assert ((ops.getpwnam badName).run s₀ = (.error Errno.EINVAL, s₀))
  NondetTest.assert ((ops.getpwnam overCapName).run s₀ = (.error Errno.ENAMETOOLONG, s₀))
  let sAbs : PasswdState :=
    { s₀ with
      byUid := setPasswdByUid s₀.byUid uid none
      byName := setPasswdByName s₀.byName name none }
  NondetTest.assert ((ops.getpwuid uid).run sAbs = (.ok none, sAbs))
  NondetTest.assert ((ops.getpwnam name).run sAbs = (.ok none, sAbs))
  let sPres : PasswdState :=
    { s₀ with
      byUid := setPasswdByUid s₀.byUid uid (some entry)
      byName := setPasswdByName s₀.byName name (some entry) }
  NondetTest.assert ((ops.getpwuid uid).run sPres = (.ok (some entry), sPres))
  NondetTest.assert ((ops.getpwnam name).run sPres = (.ok (some entry), sPres))

/-- `allowedStep` enforces embedded-NUL `EINVAL` and `> MAX_PASSWD_NAME_BYTES` `ENAMETOOLONG` validation for `getpwnam`, checks `hasNoEmbeddedNul` and key consistency on `.found`, rejects invalid errnos (`EFAULT`, `EPIPE`, `EINVAL` on `getpwuid`), accepts glibc NSS errnos (`ENOENT`, `ENXIO`, `EAGAIN`, `ENODEV`, `ENOTDIR`, `EISDIR`, `ESPIPE`, `ENAMETOOLONG`, `ELOOP`), and guarantees deterministic repeated lookups. -/
def test_passwd_allowedStep_nssSemantics
    {runner} [NondetTest runner]
    (step : PasswdState → PasswdReq → PasswdOutcome → Option PasswdState := allowedStep) :
    runner Unit := do
  let sRaw ← nondet PasswdState
  let uid ← nondet UInt32
  let overCapName ← nondet ByteArray
  assume (sRaw.isWellFormed = true)
  assume (validPasswdName overCapName = true)
  assume (overCapName.size > MAX_PASSWD_NAME_BYTES)
  let s : PasswdState := { sRaw with ambientSeccomp := false, transientNssUnavail := false, byUid := ∅, byName := ∅ }
  let rootName := asciiBytes ['r', 'o', 'o', 't']
  let otherName := asciiBytes ['o', 't', 'h', 'e', 'r']
  let badName := ByteArray.mk #[114, 0, 111]
  let entryOk : PasswdEntry :=
    { name := rootName
      uid := uid
      gid := 0
      gecos := rootName
      homeDir := asciiBytes ['/', 'r', 'o', 'o', 't']
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }
  let entryOther : PasswdEntry := { entryOk with homeDir := asciiBytes ['/', 't', 'm', 'p'] }
  let entryWrongUid : PasswdEntry := { entryOk with uid := uid + 1 }
  let entryWrongName : PasswdEntry := { entryOk with name := otherName }
  let entryWithNul : PasswdEntry := { entryOk with homeDir := ByteArray.mk #[47, 0, 120] }
  NondetTest.assert (step s (.getpwnam badName) .notFound = none)
  NondetTest.assert (step s (.getpwnam badName) (.found entryOk) = none)
  NondetTest.assert (step s (.getpwnam badName) (.err Errno.ERANGE) = none)
  NondetTest.assert (step s (.getpwnam badName) (.err Errno.EINVAL) = some s)
  NondetTest.assert (step s (.getpwnam overCapName) .notFound = none)
  NondetTest.assert (step s (.getpwnam overCapName) (.err Errno.EIO) = none)
  NondetTest.assert (step s (.getpwnam overCapName) (.err Errno.ENAMETOOLONG) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.found entryWithNul) = none)
  NondetTest.assert (step s (.getpwuid uid) (.found entryWrongUid) = none)
  NondetTest.assert (step s (.getpwnam rootName) (.found entryWrongName) = none)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.EINVAL) = none)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.EFAULT) = none)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.EPIPE) = none)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.EPIPE) = none)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.ERANGE) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.EINTR) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.EIO) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.ENOENT) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.ENXIO) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.ENXIO) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.EAGAIN) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.ENODEV) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.ENOTDIR) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.EISDIR) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.ESPIPE) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.ESPIPE) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.ENAMETOOLONG) = some s)
  NondetTest.assert (step s (.getpwnam rootName) (.err Errno.ELOOP) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.EMFILE) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.ENFILE) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.ENOMEM) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.EPERM) = some s)
  NondetTest.assert (step s (.getpwuid uid) (.err Errno.EACCES) = some s)
  match step s (.getpwuid uid) .notFound with
  | none => NondetTest.assert False
  | some sAbsUid =>
    NondetTest.assert (step sAbsUid (.getpwuid uid) .notFound = some sAbsUid)
    NondetTest.assert (step sAbsUid (.getpwuid uid) (.found entryOk) = none)
  match step s (.getpwnam rootName) .notFound with
  | none => NondetTest.assert False
  | some sAbsNam =>
    NondetTest.assert (step sAbsNam (.getpwnam rootName) .notFound = some sAbsNam)
    NondetTest.assert (step sAbsNam (.getpwnam rootName) (.found entryOk) = none)
  match step s (.getpwuid uid) (.found entryOk) with
  | none => NondetTest.assert False
  | some sFoundUid =>
    NondetTest.assert (step sFoundUid (.getpwuid uid) .notFound = none)
    NondetTest.assert (step sFoundUid (.getpwuid uid) (.found entryOther) = none)
    NondetTest.assert (step sFoundUid (.getpwuid uid) (.found entryOk) = some sFoundUid)
  match step s (.getpwnam rootName) (.found entryOk) with
  | none => NondetTest.assert False
  | some sFoundNam =>
    NondetTest.assert (step sFoundNam (.getpwnam rootName) .notFound = none)
    NondetTest.assert (step sFoundNam (.getpwnam rootName) (.found entryOther) = none)
    NondetTest.assert (step sFoundNam (.getpwnam rootName) (.found entryOk) = some sFoundNam)

/-- Under `PasswdState.withOuterSeccomp` and `PasswdState.withTransientNssUnavail`, `allowedStep` permits `SECCOMP_RET_ERRNO` (`1..4095`, excluding `EFAULT`) and well-formed `nss_systemd` `[UNAVAIL=continue]` fallback outcomes (`.notFound` or key-consistent NUL-free `.found`), while rejecting invalid outcomes and preemption of pure user-space invalid `getpwnam` names. -/
def test_passwd_allowedStep_withOuterSeccomp
    {runner} [NondetTest runner]
    (step : PasswdState → PasswdReq → PasswdOutcome → Option PasswdState := allowedStep) :
    runner Unit := do
  let sRaw ← nondet PasswdState
  let sBase : PasswdState := { sRaw with byUid := ∅, byName := ∅ }
  let uid ← nondet UInt32
  let overCapName ← nondet ByteArray
  assume (validPasswdName overCapName = true)
  assume (overCapName.size > MAX_PASSWD_NAME_BYTES)
  let rootName := asciiBytes ['r', 'o', 'o', 't']
  let badName := ByteArray.mk #[114, 0, 111]
  let entryOk : PasswdEntry :=
    { name := rootName
      uid := uid
      gid := 0
      gecos := rootName
      homeDir := asciiBytes ['/', 'r', 'o', 'o', 't']
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }
  let entryOther : PasswdEntry := { entryOk with homeDir := asciiBytes ['/', 't', 'm', 'p'] }
  let entryWrongUid : PasswdEntry := { entryOk with uid := uid + 1 }
  let entryWrongName : PasswdEntry := { entryOk with name := asciiBytes ['o', 't', 'h', 'e', 'r'] }
  let entryWithNul : PasswdEntry := { entryOk with homeDir := ByteArray.mk #[47, 0, 120] }
  let sNoSec : PasswdState := { sBase with ambientSeccomp := false, transientNssUnavail := false }
  let sSec := sNoSec.withOuterSeccomp
  let sTrans := sNoSec.withTransientNssUnavail
  NondetTest.assert (PasswdState.initial.ambientSeccomp = false)
  NondetTest.assert (PasswdState.initial.transientNssUnavail = false)
  NondetTest.assert (sSec.ambientSeccomp = true)
  NondetTest.assert (step sNoSec (.getpwuid uid) (.err Errno.ENOSYS) = none)
  NondetTest.assert (step sSec (.getpwuid uid) (.err Errno.ENOSYS) = some sSec)
  NondetTest.assert (step sSec (.getpwnam rootName) (.err Errno.EPERM) = some sSec)
  NondetTest.assert (step sSec (.getpwnam badName) (.err Errno.ENOSYS) = none)
  NondetTest.assert (step sSec (.getpwnam overCapName) (.err Errno.ENOSYS) = none)
  NondetTest.assert (step sSec (.getpwuid uid) (.err Errno.EFAULT) = none)
  NondetTest.assert (step sSec (.getpwnam rootName) (.err Errno.EFAULT) = none)
  NondetTest.assert (step sSec (.getpwuid uid) (.err 0) = none)
  NondetTest.assert (step sSec (.getpwuid uid) (.err 4096) = none)
  let sSecFound : PasswdState :=
    { sSec with
      byUid := setPasswdByUid sSec.byUid uid (some entryOther)
      byName := setPasswdByName sSec.byName rootName (some entryOther) }
  NondetTest.assert (step sSecFound (.getpwuid uid) .notFound = some sSecFound)
  NondetTest.assert (step sSecFound (.getpwuid uid) (.found entryOk) = some sSecFound)
  NondetTest.assert (step sSecFound (.getpwnam rootName) .notFound = some sSecFound)
  NondetTest.assert (step sSecFound (.getpwnam rootName) (.found entryOk) = some sSecFound)
  NondetTest.assert (step sSecFound (.getpwuid uid) (.found entryWrongUid) = none)
  NondetTest.assert (step sSecFound (.getpwnam rootName) (.found entryWrongName) = none)
  NondetTest.assert (step sSecFound (.getpwuid uid) (.found entryWithNul) = none)
  NondetTest.assert (step sSecFound (.getpwnam badName) .notFound = none)
  NondetTest.assert (step sSecFound (.getpwnam overCapName) .notFound = none)
  let sTransFound : PasswdState :=
    { sTrans with
      byUid := setPasswdByUid sTrans.byUid uid (some entryOther)
      byName := setPasswdByName sTrans.byName rootName (some entryOther) }
  NondetTest.assert (step sTransFound (.getpwuid uid) .notFound = some sTransFound)
  NondetTest.assert (step sTransFound (.getpwuid uid) (.found entryOk) = some sTransFound)
  NondetTest.assert (step sTransFound (.getpwnam rootName) .notFound = some sTransFound)
  NondetTest.assert (step sTransFound (.getpwnam rootName) (.found entryOk) = some sTransFound)
  NondetTest.assert (step sTransFound (.getpwuid uid) (.found entryWrongUid) = none)
  NondetTest.assert (step sTransFound (.getpwnam rootName) (.found entryWrongName) = none)
  NondetTest.assert (step sTransFound (.getpwuid uid) (.err Errno.EPIPE) = none)
  NondetTest.assert (step sTransFound (.getpwnam badName) .notFound = none)
  NondetTest.assert (step sTransFound (.getpwnam overCapName) .notFound = none)

/-- Every step executed by `modelOps` from any well-formed `PasswdState` produces an outcome and next state accepted by `allowedStep` and preserves `PasswdState.isWellFormed`. -/
def test_passwd_modelOps_soundAgainstAllowedStep
    {runner} [NondetTest runner]
    (ops : PasswdOpsM (StateM PasswdState))
    (step : PasswdState → PasswdReq → PasswdOutcome → Option PasswdState := allowedStep) :
    runner Unit := do
  let s ← nondet PasswdState
  let uid ← nondet UInt32
  let name ← nondet ByteArray
  assume (s.isWellFormed = true)
  let (rUid, sUid) := (ops.getpwuid uid).run s
  NondetTest.assert (step s (.getpwuid uid) (outcomeOfEntryOpt rUid) = some sUid)
  NondetTest.assert (sUid.isWellFormed = true)
  let (rNam, sNam) := (ops.getpwnam name).run s
  NondetTest.assert (step s (.getpwnam name) (outcomeOfEntryOpt rNam) = some sNam)
  NondetTest.assert (sNam.isWellFormed = true)

/-- Raw C-ABI tuple `(name, uid, gid, gecos, homeDir, shell)` returned by single-call passwd hooks. -/
abbrev RawPasswdTuple := ByteArray × UInt32 × UInt32 × ByteArray × ByteArray × ByteArray

/-- `Internal.mkPasswdOpsM raw` (and `Internal.mkPasswdOps raw`) rejects invalid (`EINVAL`) and oversized (`ENAMETOOLONG`) `getpwnam` names without mutating state and produces outcomes accepted by `allowedStep` while preserving `PasswdState.isWellFormed` whenever each raw call for `sz ∈ 4096..65536` satisfies `allowedStep` on `ERANGE`-preserving hooks. -/
def test_passwd_mkPasswdOps_soundAgainstAllowedStep
    {runner} [NondetTest runner]
    (mkOps :
      (UInt32 → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple))) →
      (ByteArray → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple))) →
      PasswdOpsM (StateM PasswdState)) : runner Unit := do
  let s ← nondet PasswdState
  let uid ← nondet UInt32
  let name ← nondet ByteArray
  let badName ← nondet ByteArray
  let overCapName ← nondet ByteArray
  let rawGetpwuidOnce ← nondet (UInt32 → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple)))
  let rawGetpwnamOnce ← nondet (ByteArray → UInt32 → StateM PasswdState (Except Errno (Option RawPasswdTuple)))
  assume (s.isWellFormed = true)
  assume (validPasswdName badName = false)
  assume (validPasswdName overCapName = true)
  assume (overCapName.size > MAX_PASSWD_NAME_BYTES)
  assume (∀ sz : UInt32, 4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 →
    let (r, s') := rawGetpwuidOnce uid sz s
    match r with
    | .error e =>
      (e == Errno.ERANGE → s' = s) ∧
      allowedStep s (.getpwuid uid) (.err e) = some s' ∧ s'.isWellFormed = true
    | .ok none =>
      allowedStep s (.getpwuid uid) .notFound = some s' ∧ s'.isWellFormed = true
    | .ok (some t) =>
      let entry : PasswdEntry :=
        { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
          homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
      (entry.hasNoEmbeddedNul && entry.uid == uid →
        allowedStep s (.getpwuid uid) (.found entry) = some s' ∧ s'.isWellFormed = true) ∧
      (!(entry.hasNoEmbeddedNul && entry.uid == uid) → s' = s))
  assume (∀ sz : UInt32, 4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 →
    validPasswdName name = true →
    name.size ≤ MAX_PASSWD_NAME_BYTES →
    let (r, s') := rawGetpwnamOnce name sz s
    match r with
    | .error e =>
      (e == Errno.ERANGE → s' = s) ∧
      allowedStep s (.getpwnam name) (.err e) = some s' ∧ s'.isWellFormed = true
    | .ok none =>
      allowedStep s (.getpwnam name) .notFound = some s' ∧ s'.isWellFormed = true
    | .ok (some t) =>
      let entry : PasswdEntry :=
        { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
          homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
      (entry.hasNoEmbeddedNul && entry.name == name →
        allowedStep s (.getpwnam name) (.found entry) = some s' ∧ s'.isWellFormed = true) ∧
      (!(entry.hasNoEmbeddedNul && entry.name == name) → s' = s))
  let ops := mkOps rawGetpwuidOnce rawGetpwnamOnce
  NondetTest.assert ((ops.getpwnam badName).run s = (.error Errno.EINVAL, s))
  NondetTest.assert ((ops.getpwnam overCapName).run s = (.error Errno.ENAMETOOLONG, s))
  let (rUid, sUid) := (ops.getpwuid uid).run s
  NondetTest.assert (allowedStep s (.getpwuid uid) (outcomeOfEntryOpt rUid) = some sUid)
  NondetTest.assert (sUid.isWellFormed = true)
  let (rNam, sNam) := (ops.getpwnam name).run s
  NondetTest.assert (allowedStep s (.getpwnam name) (outcomeOfEntryOpt rNam) = some sNam)
  NondetTest.assert (sNam.isWellFormed = true)

/-- `Internal.mkPasswdOpsM` and `Internal.mkPasswdOps` agree identically, use the exact retry sequence `[4096, 8192, 16384, 32768, 65536]`, validate names and length caps before calling `getpwnamOnce`, and execute the `ERANGE` retry doubling schedule across `4096 → 8192 → 16384 → 32768 → 65536` while validating returned entries against `hasNoEmbeddedNul` and key match (`Errno.EIO` on mismatch). -/
def test_passwd_mkPasswdOps_exactRetryAndDelegation
    {runner} [NondetTest runner]
    (mkOps :
      (UInt32 → UInt32 → Except Errno (Option RawPasswdTuple)) →
      (ByteArray → UInt32 → Except Errno (Option RawPasswdTuple)) →
      PasswdOpsM Id)
    (bufSizes : List UInt32)
    (mkOpsAlias :
      (UInt32 → UInt32 → Except Errno (Option RawPasswdTuple)) →
      (ByteArray → UInt32 → Except Errno (Option RawPasswdTuple)) →
      PasswdOpsM Id) : runner Unit := do
  let rawGetpwuid ← nondet (UInt32 → UInt32 → Except Errno (Option RawPasswdTuple))
  let rawGetpwnam ← nondet (ByteArray → UInt32 → Except Errno (Option RawPasswdTuple))
  let uid ← nondet UInt32
  let name ← nondet ByteArray
  let ops := mkOps rawGetpwuid rawGetpwnam
  let aliasOps := mkOpsAlias rawGetpwuid rawGetpwnam
  let validateTuple (pred : PasswdEntry → Bool) :
      Except Errno (Option RawPasswdTuple) →
        Except Errno (Option PasswdEntry)
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some t) =>
      let entry : PasswdEntry :=
        { name := t.1
          uid := t.2.1
          gid := t.2.2.1
          gecos := t.2.2.2.1
          homeDir := t.2.2.2.2.1
          shell := t.2.2.2.2.2 }
      if pred entry then .ok (some entry) else .error Errno.EIO
  let stepOr (pred : PasswdEntry → Bool)
      (once : UInt32 → Except Errno (Option RawPasswdTuple))
      (sz : UInt32) (next : Except Errno (Option PasswdEntry)) :
      Except Errno (Option PasswdEntry) :=
    match once sz with
    | .error e => if e == Errno.ERANGE then next else .error e
    | .ok opt => validateTuple pred (.ok opt)
  let expectedRetry (pred : PasswdEntry → Bool)
      (once : UInt32 → Except Errno (Option RawPasswdTuple)) :
      Except Errno (Option PasswdEntry) :=
    stepOr pred once 4096
      (stepOr pred once 8192
        (stepOr pred once 16384
          (stepOr pred once 32768
            (validateTuple pred (once 65536)))))
  NondetTest.assert (bufSizes = [4096, 8192, 16384, 32768, 65536])
  NondetTest.assert (aliasOps.getpwuid uid = ops.getpwuid uid)
  NondetTest.assert (aliasOps.getpwnam name = ops.getpwnam name)
  NondetTest.assert (ops.getpwuid uid =
    expectedRetry (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid) (rawGetpwuid uid))
  NondetTest.assert (ops.getpwnam name =
    if !validPasswdName name then
      .error Errno.EINVAL
    else if name.size > MAX_PASSWD_NAME_BYTES then
      .error Errno.ENAMETOOLONG
    else
      expectedRetry (fun entry => entry.hasNoEmbeddedNul && entry.name == name) (rawGetpwnam name))

/-- `Passwd.getpwuid` and `Passwd.getpwnam` delegate to `Passwd.defaultOps`, and `defaultOps.getpwnam` rejects embedded-NUL (`EINVAL`) and oversized (`> MAX_PASSWD_NAME_BYTES`, `ENAMETOOLONG`) names in pure user space. -/
def test_passwd_interface_wiringAndSoundness
    {runner} [NondetTest runner]
    (ops : PasswdOps)
    (getpwuidFn : UInt32 → IO (Except Errno (Option PasswdEntry)))
    (getpwnamFn : ByteArray → IO (Except Errno (Option PasswdEntry))) :
    runner Unit := do
  let uid ← nondet UInt32
  let name ← nondet ByteArray
  NondetTest.assert (getpwuidFn uid = ops.getpwuid uid)
  NondetTest.assert (getpwnamFn name = ops.getpwnam name)
  NondetTest.assert (validPasswdName name = false → ops.getpwnam name = pure (.error Errno.EINVAL))
  NondetTest.assert (validPasswdName name = true → name.size > MAX_PASSWD_NAME_BYTES →
    ops.getpwnam name = pure (.error Errno.ENAMETOOLONG))

/-- `healthyStep` and `healthyModelOps` preserve `HealthyEnv.wf`, accept everyday NSS errors (`EMFILE`, `ERANGE`, `ENOENT`) and `EMFILE`-induced `[UNAVAIL=continue]` fallback on `HealthyEnv.initial` (`transientNssUnavail = true`) while enforcing strict determinism under `HealthyEnv.initial _ false`, rejecting curated critical faults (`ENOMEM`, `EIO`, `ENFILE`), `EFAULT`, invalid errnos, key/NUL violations, and ambient `seccomp`, strictly decrementing `eintrBudget` on `EINTR`, and deterministically returning present `PasswdEntry` records on `healthyModelOps` without consuming `eintrBudget`. -/
def test_passwd_healthyStep_and_healthyModelOps
    {runner} [NondetTest runner]
    (ops : PasswdOpsM (StateM HealthyEnv) := healthyModelOps)
    (step : HealthyEnv → PasswdReq → PasswdOutcome → Option HealthyEnv := healthyStep) :
    runner Unit := do
  let e1 := HealthyEnv.initial 1
  let e0 := HealthyEnv.initial 0
  let eStrict1 := HealthyEnv.initial 1 false
  NondetTest.assert (e1.wf = true ∧ e0.wf = true ∧ eStrict1.wf = true)
  NondetTest.assert (step { state := PasswdState.initial.withOuterSeccomp, eintrBudget := 1 }
    (.getpwuid 0) .notFound = none)
  NondetTest.assert (step e1 (.getpwuid 0) (.err Errno.EMFILE) = some e1 ∧
    step e1 (.getpwuid 0) (.err Errno.ERANGE) = some e1 ∧
    step e1 (.getpwuid 0) (.err Errno.ENOENT) = some e1)
  NondetTest.assert (step e1 (.getpwuid 0) (.err Errno.ENOMEM) = none ∧
    step e1 (.getpwuid 0) (.err Errno.EIO) = none ∧
    step e1 (.getpwuid 0) (.err Errno.ENFILE) = none ∧
    step e1 (.getpwuid 0) (.err Errno.EFAULT) = none)
  let rootEtc : PasswdEntry :=
    { name := asciiBytes ['r', 'o', 'o', 't']
      uid := 0
      gid := 0
      gecos := asciiBytes ['r', 'o', 'o', 't']
      homeDir := asciiBytes ['/', 'r', 'o', 'o', 't']
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 'b', 'a', 's', 'h'] }
  let rootSynth : PasswdEntry :=
    { rootEtc with
      gecos := asciiBytes ['S', 'u', 'p', 'e', 'r']
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }
  let rootWrongUid : PasswdEntry := { rootSynth with uid := 1 }
  let e1Found : HealthyEnv :=
    { e1 with state := { e1.state with byUid := setPasswdByUid e1.state.byUid 0 (some rootEtc) } }
  let eStrictFound : HealthyEnv :=
    { eStrict1 with state := { eStrict1.state with byUid := setPasswdByUid eStrict1.state.byUid 0 (some rootEtc) } }
  NondetTest.assert (step e1 (.getpwuid 0) (.err Errno.EINTR) = some e0 ∧
    step e0 (.getpwuid 0) (.err Errno.EINTR) = none ∧
    step e1 (.getpwuid 0) (.found rootEtc) = some e1Found ∧
    step e1Found (.getpwuid 0) (.found rootSynth) = some e1Found ∧
    step e1Found (.getpwuid 0) .notFound = some e1Found ∧
    step e1Found (.getpwuid 0) (.found rootWrongUid) = none ∧
    step e1Found (.getpwnam (ByteArray.mk #[114, 0, 111])) .notFound = none ∧
    step eStrict1 (.getpwuid 0) (.found rootEtc) = some eStrictFound ∧
    step eStrictFound (.getpwuid 0) (.found rootSynth) = none ∧
    step eStrictFound (.getpwuid 0) .notFound = none)
  let env ← nondet HealthyEnv
  assume (env.wf = true)
  let uid ← nondet UInt32
  let name ← nondet ByteArray
  let entry ← nondet PasswdEntry
  assume (validPasswdName name = true)
  assume (name.size ≤ MAX_PASSWD_NAME_BYTES)
  assume (entry.hasNoEmbeddedNul = true)
  assume (entry.uid = uid)
  assume (entry.name = name)
  let (rUid, envUid) := (ops.getpwuid uid).run env
  let (mUid, sUid) := (modelOps.getpwuid uid).run env.state
  NondetTest.assert ((rUid, envUid) = (mUid, { env with state := sUid }) ∧
    step env (.getpwuid uid) (outcomeOfEntryOpt rUid) = some envUid ∧
    envUid.wf = true ∧ envUid.eintrBudget = env.eintrBudget)
  let (rNam, envNam) := (ops.getpwnam name).run env
  let (mNam, sNam) := (modelOps.getpwnam name).run env.state
  NondetTest.assert ((rNam, envNam) = (mNam, { env with state := sNam }) ∧
    step env (.getpwnam name) (outcomeOfEntryOpt rNam) = some envNam ∧
    envNam.wf = true ∧ envNam.eintrBudget = env.eintrBudget)
  let envPres : HealthyEnv :=
    { env with
      state := { env.state with
                 byUid := setPasswdByUid env.state.byUid uid (some entry)
                 byName := setPasswdByName env.state.byName name (some entry) } }
  NondetTest.assert ((ops.getpwuid uid).run envPres = (.ok (some entry), envPres) ∧
    (ops.getpwnam name).run envPres = (.ok (some entry), envPres))
  let rawName ← nondet ByteArray
  let (rRawNam, envRawNam) := (ops.getpwnam rawName).run env
  let (mRawNam, sRawNam) := (modelOps.getpwnam rawName).run env.state
  NondetTest.assert ((rRawNam, envRawNam) = (mRawNam, { env with state := sRawNam }) ∧
    step env (.getpwnam rawName) (outcomeOfEntryOpt rRawNam) = some envRawNam ∧
    envRawNam.wf = true ∧ envRawNam.eintrBudget = env.eintrBudget)
  let anyEnv ← nondet HealthyEnv
  let anyReq ← nondet PasswdReq
  let anyOut ← nondet PasswdOutcome
  NondetTest.assert (step anyEnv anyReq anyOut =
    if !anyEnv.wf || isCriticalFault anyOut then
      none
    else
      match allowedStep anyEnv.state anyReq anyOut with
      | none => none
      | some s' =>
        if isEintrOutcome anyOut then
          if anyEnv.eintrBudget > 0 then
            some { state := s', eintrBudget := anyEnv.eintrBudget - 1 }
          else
            none
        else
          some { state := s', eintrBudget := anyEnv.eintrBudget })

end LeanSwe.LinuxSyscall.Passwd
