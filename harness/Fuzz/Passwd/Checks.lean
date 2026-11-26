import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.Passwd.Impl
import LeanSwe.LinuxSyscall.Passwd.Interface
import LeanSwe.LinuxSyscall.Passwd.Model

namespace Fuzz.Passwd.Checks

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Passwd

private def failWith {α : Type} (msg : String) : IO α :=
  throw (IO.userError s!"Passwd.Checks: {msg}")

private def logPasswdErrHit (op : String) (e : Errno) (mode : String) : IO Unit :=
  Fuzz.Common.logErrHit s!"LeanSwe.LinuxSyscall.Passwd.{op}"
    (reprStr (PasswdErrorKind.ofErrno e)).trimAscii.toString mode

private def assertTrue (label : String) (cond : Bool) : IO Unit := do
  if !cond then
    failWith s!"assertion failed: {label}"

private def expectOk {α : Type} (label : String) (res : Except Errno α) : IO α := do
  match res with
  | .ok v => return v
  | .error e => failWith s!"{label}: unexpected error {Errno.name e} ({e})"

private def expectErr {α : Type} (label : String) (expected : Errno) (res : Except Errno α) : IO Unit := do
  match res with
  | .ok _ => failWith s!"{label}: expected {Errno.name expected}, got ok"
  | .error e =>
    if e != expected then
      failWith s!"{label}: expected {Errno.name expected} ({expected}), got {Errno.name e} ({e})"

private def readCurrentUid : IO UInt32 := do
  let txt ← IO.FS.readFile "/proc/self/status"
  for rawLine in txt.splitOn "\n" do
    if rawLine.startsWith "Uid:" then
      let parts := ((rawLine.drop 4).toString.splitOn "\t").filter (!·.isEmpty)
      let toks := parts.flatMap (fun p => (p.splitOn " ").filter (!·.isEmpty))
      match toks.head? with
      | some uidStr =>
        match uidStr.toNat? with
        | some n => return UInt32.ofNat n
        | none => failWith s!"unparseable Uid token in /proc/self/status: {uidStr}"
      | none => failWith "empty Uid line in /proc/self/status"
  failWith "missing Uid line in /proc/self/status"

private def bytesToHex (ba : ByteArray) : String := Id.run do
  let mut out := ""
  for b in ba.data do
    let hi := (b >>> 4).toNat
    let lo := (b &&& 0x0F).toNat
    let ch (n : Nat) : Char :=
      if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)
    out := out.push (ch hi)
    out := out.push (ch lo)
  return out

/-- Child-process probe helper dispatched for `--passwd-probe` by `leanswe-fuzz` and `lean-swe-mut-test`, printing raw hex `pw_dir` for `uid` under overridden environment variables (e.g. `HOME=/tmp`). -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | [uidStr] =>
    let some uidNat := uidStr.toNat?
      | do
          IO.eprintln s!"passwd-probe: invalid uid {uidStr}"
          return 2
    match ← getpwuid (UInt32.ofNat uidNat) with
    | .ok (some entry) =>
      IO.println s!"OK:{bytesToHex entry.homeDir}"
      return 0
    | .ok none =>
      IO.println "NONE"
      return 0
    | .error e =>
      IO.eprintln s!"passwd-probe: {Errno.name e} ({e})"
      return 1
  | _ =>
    IO.eprintln s!"unknown passwd probe args: {args}"
    return 2

/-- Return `true` iff `/etc/passwd` exists on disk as a regular file. -/
private def hasRegularEtcPasswd : IO Bool := do
  let p : System.FilePath := "/etc/passwd"
  try
    let md ← p.metadata
    return md.type == .file
  catch _ =>
    return false

/-- Return `true` iff regular `/etc/passwd` contains an entry matching `uid`. -/
private def etcPasswdHasUid (uid : UInt32) : IO Bool := do
  if !(← hasRegularEtcPasswd) then
    return false
  let target := toString uid.toNat
  try
    let bytes ← IO.FS.readBinFile "/etc/passwd"
    let txt := String.fromUTF8! bytes
    for line in txt.splitOn "\n" do
      let fields := line.splitOn ":"
      if fields.length ≥ 3 && fields[2]? == some target then
        return true
    return false
  catch _ =>
    return false

/-- Expect `.ok opt`, or `.error e` with a permitted non-`EINVAL` OS errno when host NSS files/daemons are absent or sandboxed. -/
private def expectOkOrAllowedOs (label : String) (res : Except Errno (Option PasswdEntry)) :
    IO (Option (Option PasswdEntry)) := do
  match res with
  | .ok opt => return some opt
  | .error e =>
    if e != Errno.EINVAL && isAllowedPasswdOsErrno e then
      return none
    else
      failWith s!"{label}: unexpected error {Errno.name e} ({e})"

/-- Verify `HOME=/tmp` child-process isolation and entry invariants for an existing `uid`. -/
private def checkExistingUidDetails (uid : UInt32) (entry : PasswdEntry) : IO Unit := do
  assertTrue "entry has no embedded NUL" entry.hasNoEmbeddedNul
  assertTrue "entry.uid == curUid" (entry.uid == uid)
  assertTrue "homeDirUtf8? consistent with fromUTF8?" (entry.homeDirUtf8? == String.fromUTF8? entry.homeDir)
  if let some cur2? ← expectOkOrAllowedOs "getpwuid(curUid) #2" (← getpwuid uid) then
    assertTrue "repeated getpwuid deterministic" (cur2? == some entry)
  if let some byNam? ← expectOkOrAllowedOs "getpwnam(entry.name)" (← getpwnam entry.name) then
    if entry.name.isEmpty then
      assertTrue "getpwnam(\"\") returns valid empty-name entry"
        (match byNam? with | some e2 => e2.name.isEmpty && e2.hasNoEmbeddedNul | none => false)
    else
      assertTrue "getpwnam(entry.name) returns matching uid"
        (match byNam? with | some e2 => e2.uid == entry.uid && e2.name == entry.name | none => false)
  let exe ← IO.appPath
  let childOut ← IO.Process.output {
    cmd := exe.toString
    args := #["--passwd-probe", toString uid.toNat]
    env := #[("HOME", some "/tmp")]
  }
  if childOut.exitCode != 0 then
    failWith s!"HOME=/tmp child probe failed exit={childOut.exitCode}: {childOut.stderr}"
  if entry.name.isEmpty then
    assertTrue "HOME=/tmp child probe returned OK"
      (childOut.stdout.trimAscii.toString.startsWith "OK:")
  else
    assertTrue "HOME=/tmp does not override NSS pw_dir"
      (childOut.stdout.trimAscii.toString == s!"OK:{bytesToHex entry.homeDir}")

/-- Verify `uid = 0` and missing `0xFFFFFFFE` `getpwuid` queries under host and empty-`/etc` NSS setups. -/
private def checkGetpwuidBoundsAndExtra (regPasswd : Bool) : IO Unit := do
  let rootInEtc ← etcPasswdHasUid 0
  let rootRes? ← expectOkOrAllowedOs "getpwuid(0)" (← getpwuid 0)
  match rootRes? with
  | some (some rootEntry) =>
    assertTrue "root uid == 0" (rootEntry.uid == 0)
    assertTrue "root entry hasNoEmbeddedNul" rootEntry.hasNoEmbeddedNul
  | some none =>
    if regPasswd && rootInEtc then
      failWith "getpwuid(0) returned none while root exists in /etc/passwd"
  | none => pure ()
  match ← getpwuid 0xFFFFFFFE with
  | .ok (some uFeEntry) =>
    assertTrue "0xFFFFFFFE entry consistent" (uFeEntry.uid == 0xFFFFFFFE && uFeEntry.hasNoEmbeddedNul)
  | .ok none => pure ()
  | .error e =>
    assertTrue s!"0xFFFFFFFE unexpected error {Errno.name e}" (isAllowedPasswdOsErrno e)

/-- Runtime verification for `LeanSwe.LinuxSyscall.Passwd.assume_passwd_getpwuid_validAndMissingAndDeterministic`. -/
private def assume_passwd_getpwuid_validAndMissingAndDeterministic : IO Unit := do
  let uid ← readCurrentUid
  let regPasswd ← hasRegularEtcPasswd
  let uidInEtc ← etcPasswdHasUid uid
  let curRes? ← expectOkOrAllowedOs "getpwuid(curUid)" (← getpwuid uid)
  match curRes? with
  | some (some entry) => checkExistingUidDetails uid entry
  | some none =>
    if regPasswd && uidInEtc then
      failWith s!"getpwuid(curUid={uid}) returned none while uid exists in /etc/passwd"
  | none => pure ()
  checkGetpwuidBoundsAndExtra regPasswd

/-- Build `4096 * 2^doublings` copies of byte `ch`. -/
private def mkRepeatedByteBlock (ch : Char) (doublings : Nat) : ByteArray := Id.run do
  let mut buf := ByteArray.mk (Array.replicate 4096 (UInt8.ofNat ch.toNat))
  for _ in [0:doublings] do
    buf := buf ++ buf
  return buf

/-- Verify `getpwnam("root")` entry invariants under host and empty-`/etc` NSS setups. -/
private def checkRootGetpwnam (rootName : ByteArray) (regPasswd rootInEtc : Bool) : IO Unit := do
  let rootRes? ← expectOkOrAllowedOs "getpwnam(root)" (← getpwnam rootName)
  match rootRes? with
  | some (some rootEntry) =>
    assertTrue "root entry.name == root" (rootEntry.name == rootName)
    assertTrue "root entry.uid == 0" (rootEntry.uid == 0)
    assertTrue "root entry hasNoEmbeddedNul" rootEntry.hasNoEmbeddedNul
  | some none =>
    if regPasswd && rootInEtc then
      failWith "getpwnam(root) returned none while root exists in /etc/passwd"
  | none => pure ()

/-- Verify missing, empty, and embedded-NUL checks for `getpwnam`. -/
private def checkBasicGetpwnamCases : IO Unit := do
  let missingName := asciiBytes ['n', 'o', '_', 's', 'u', 'c', 'h', '_', 'p', 'w']
  let missing? ← expectOkOrAllowedOs "getpwnam(no_such_pw)" (← getpwnam missingName)
  if let some someMiss := missing? then
    if let some missEntry := someMiss then
      assertTrue "missingName entry matches name" (missEntry.name == missingName && missEntry.hasNoEmbeddedNul)
  match ← getpwnam ByteArray.empty with
  | .ok none => pure ()
  | .ok (some emptyEntry) =>
    assertTrue "empty entry matches name" (emptyEntry.name == ByteArray.empty && emptyEntry.hasNoEmbeddedNul)
  | .error e =>
    assertTrue s!"empty name unexpected errno {Errno.name e}" (e != Errno.EINVAL && isAllowedPasswdOsErrno e)
  expectErr "getpwnam(embedded NUL) -> EINVAL" Errno.EINVAL (← getpwnam (ByteArray.mk #[114, 0, 111]))

/-- Verify large `> 65536`, `1048576`, `1048577`, and `140 MiB` username bounds for `getpwnam`. -/
private def checkOversizedGetpwnamCases : IO Unit := do
  let bigName := ByteArray.mk (Array.replicate 65537 (UInt8.ofNat 'a'.toNat))
  match ← getpwnam bigName with
  | .ok none => pure ()
  | .ok (some e) =>
    assertTrue "65537B name entry valid" (e.name == bigName && e.hasNoEmbeddedNul)
  | .error e =>
    assertTrue s!"65537B name unexpected errno {Errno.name e}" (e != Errno.EINVAL && isAllowedPasswdOsErrno e)
  let maxCapName := mkRepeatedByteBlock 'a' 8
  assertTrue "maxCapName is 1048576B" (maxCapName.size == 1048576)
  match ← getpwnam maxCapName with
  | .ok none => pure ()
  | .ok (some e) =>
    assertTrue "1048576B name entry valid" (e.name == maxCapName && e.hasNoEmbeddedNul)
  | .error e =>
    assertTrue s!"1048576B name unexpected errno {Errno.name e}"
      (e != Errno.EINVAL && e != Errno.ENAMETOOLONG && isAllowedPasswdOsErrno e)
  expectErr "getpwnam(1048577B) -> ENAMETOOLONG" Errno.ENAMETOOLONG
    (← getpwnam (maxCapName.push (UInt8.ofNat 'a'.toNat)))
  let hugeName := mkRepeatedByteBlock 'a' 16
  let huge140MiB := hugeName.extract 0 146800640
  assertTrue "huge140MiB is 146800640B" (huge140MiB.size == 146800640)
  expectErr "getpwnam(140 MiB NUL-free) -> ENAMETOOLONG" Errno.ENAMETOOLONG (← getpwnam huge140MiB)
  expectErr "getpwnam(140 MiB + NUL) -> EINVAL" Errno.EINVAL (← getpwnam (huge140MiB.push 0))

/-- Runtime verification for `LeanSwe.LinuxSyscall.Passwd.assume_passwd_getpwnam_validAndMissingAndInvalid`. -/
private def assume_passwd_getpwnam_validAndMissingAndInvalid : IO Unit := do
  let regPasswd ← hasRegularEtcPasswd
  let rootInEtc ← etcPasswdHasUid 0
  let rootName := asciiBytes ['r', 'o', 'o', 't']
  checkRootGetpwnam rootName regPasswd rootInEtc
  checkBasicGetpwnamCases
  checkOversizedGetpwnamCases

/-- Verify mocked `getpwuid` bounded `ERANGE` retry (`4096 → ... → 65536`), error propagation across all 3 `PasswdErrorKind` buckets, and preservation of non-UTF-8 `homeDir` bytes in `PasswdEntry`. -/
private def err_passwd_getpwuid_mocked : IO Unit := do
  for (eno, kind) in [ (Errno.EINVAL, PasswdErrorKind.invalidArg)
                     , (Errno.EPERM, PasswdErrorKind.permissionDenied)
                     , (Errno.EACCES, PasswdErrorKind.permissionDenied)
                     , (Errno.ERANGE, PasswdErrorKind.transientOrResource)
                     , (Errno.EIO, PasswdErrorKind.transientOrResource)
                     , (Errno.EINTR, PasswdErrorKind.transientOrResource)
                     , (Errno.EMFILE, PasswdErrorKind.transientOrResource)
                     , (Errno.ENFILE, PasswdErrorKind.transientOrResource)
                     , (Errno.ENOMEM, PasswdErrorKind.transientOrResource) ] do
    let calls ← IO.mkRef (#[] : Array UInt32)
    let ops := Internal.mkPasswdOps {
      getpwuidOnce := fun _ buf => do
        calls.modify (·.push buf)
        return .error eno
      getpwnamOnce := fun _ _ => return .ok none
    }
    expectErr s!"mock getpwuid {Errno.name eno}" eno (← ops.getpwuid 0)
    logPasswdErrHit "getpwuid" eno "mocked"
    assertTrue s!"kind {Errno.name eno}" (PasswdErrorKind.ofErrno eno == kind)
    let seen ← calls.get
    if eno == Errno.ERANGE then
      assertTrue "ERANGE retries 4096..65536" (seen == #[4096, 8192, 16384, 32768, 65536])
    else
      assertTrue "non-ERANGE stops at 4096" (seen == #[4096])
  let badUtf8Dir := ByteArray.mk #[0x2F, 0xFF, 0xFE]
  let opsNonUtf8 := Internal.mkPasswdOps {
    getpwuidOnce := fun uid buf =>
      if buf < 32768 then return .error Errno.ERANGE
      else
        let nm := asciiBytes ['u']
        let sh := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h']
        return .ok (some (nm, uid, 100, ByteArray.empty, badUtf8Dir, sh))
    getpwnamOnce := fun _ _ => return .ok none
  }
  let entry? ← expectOk "getpwuid retry succeeds at 32768 with non-UTF-8 homeDir" (← opsNonUtf8.getpwuid 1000)
  match entry? with
  | some e =>
    assertTrue "raw homeDir preserved" (e.homeDir == badUtf8Dir)
    assertTrue "homeDirUtf8? is none for non-UTF-8" e.homeDirUtf8?.isNone
    assertTrue "nameUtf8? is some u" (e.nameUtf8? == some "u")
  | none =>
    failWith "expected some PasswdEntry for non-UTF-8 homeDir"
  let opsUidMismatch := Internal.mkPasswdOps {
    getpwuidOnce := fun uid _ =>
      let nm := asciiBytes ['u']
      let sh := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h']
      return .ok (some (nm, uid + 1, 100, ByteArray.empty, badUtf8Dir, sh))
    getpwnamOnce := fun _ _ => return .ok none
  }
  expectErr "getpwuid uid mismatch -> EIO" Errno.EIO (← opsUidMismatch.getpwuid 1000)
  let opsUidNul := Internal.mkPasswdOps {
    getpwuidOnce := fun uid _ =>
      let nm := asciiBytes ['u']
      let sh := ByteArray.mk #[47, 0, 115]
      return .ok (some (nm, uid, 100, ByteArray.empty, badUtf8Dir, sh))
    getpwnamOnce := fun _ _ => return .ok none
  }
  expectErr "getpwuid embedded NUL -> EIO" Errno.EIO (← opsUidNul.getpwuid 1000)

/-- Verify real `getpwnam` rejects embedded NUL with `EINVAL`, accepts NUL-free `> 65536`-byte names without `EINVAL`, and rejects `> 1048576`-byte names with `ENAMETOOLONG`. -/
private def err_passwd_getpwnam_invalidArg : IO Unit := do
  expectErr "getpwnam(NUL) -> EINVAL" Errno.EINVAL (← getpwnam (ByteArray.mk #[97, 0, 98]))
  logPasswdErrHit "getpwnam" Errno.EINVAL "real"
  let big := ByteArray.mk (Array.replicate 65537 (UInt8.ofNat 'x'.toNat))
  match ← getpwnam big with
  | .error e =>
    assertTrue s!"getpwnam(65537) must not fail with EINVAL (got {Errno.name e})" (e != Errno.EINVAL)
  | .ok _ => pure ()
  let overCap := ByteArray.mk (Array.replicate 1048577 (UInt8.ofNat 'x'.toNat))
  expectErr "getpwnam(1048577) -> ENAMETOOLONG" Errno.ENAMETOOLONG (← getpwnam overCap)
  assertTrue "EINVAL is invalidArg" (PasswdErrorKind.ofErrno Errno.EINVAL == .invalidArg)

/-- Verify mocked `getpwnam` propagation for `permissionDenied` and `transientOrResource` plus `ERANGE` retry and postcondition `EIO` validation. -/
private def err_passwd_getpwnam_mocked : IO Unit := do
  for (eno, kind) in [ (Errno.EPERM, PasswdErrorKind.permissionDenied)
                     , (Errno.EACCES, PasswdErrorKind.permissionDenied)
                     , (Errno.ERANGE, PasswdErrorKind.transientOrResource)
                     , (Errno.EIO, PasswdErrorKind.transientOrResource)
                     , (Errno.EINTR, PasswdErrorKind.transientOrResource)
                     , (Errno.EMFILE, PasswdErrorKind.transientOrResource)
                     , (Errno.ENFILE, PasswdErrorKind.transientOrResource)
                     , (Errno.ENOMEM, PasswdErrorKind.transientOrResource) ] do
    let calls ← IO.mkRef (#[] : Array UInt32)
    let ops := Internal.mkPasswdOps {
      getpwuidOnce := fun _ _ => return .ok none
      getpwnamOnce := fun _ buf => do
        calls.modify (·.push buf)
        return .error eno
    }
    expectErr s!"mock getpwnam {Errno.name eno}" eno (← ops.getpwnam (asciiBytes ['r', 'o', 'o', 't']))
    logPasswdErrHit "getpwnam" eno "mocked"
    assertTrue s!"kind {Errno.name eno}" (PasswdErrorKind.ofErrno eno == kind)
    let seen ← calls.get
    if eno == Errno.ERANGE then
      assertTrue "getpwnam ERANGE retries 4096..65536" (seen == #[4096, 8192, 16384, 32768, 65536])
    else
      assertTrue "getpwnam non-ERANGE stops at 4096" (seen == #[4096])
  let opsNameMismatch := Internal.mkPasswdOps {
    getpwuidOnce := fun _ _ => return .ok none
    getpwnamOnce := fun _ _ =>
      let other := asciiBytes ['o', 't', 'h', 'e', 'r']
      let dir := asciiBytes ['/', 't', 'm', 'p']
      let sh := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h']
      return .ok (some (other, 0, 0, ByteArray.empty, dir, sh))
  }
  expectErr "getpwnam name mismatch -> EIO" Errno.EIO (← opsNameMismatch.getpwnam (asciiBytes ['r', 'o', 'o', 't']))
  let opsNameNul := Internal.mkPasswdOps {
    getpwuidOnce := fun _ _ => return .ok none
    getpwnamOnce := fun nm _ =>
      let dir := ByteArray.mk #[47, 0]
      let sh := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h']
      return .ok (some (nm, 0, 0, ByteArray.empty, dir, sh))
  }
  expectErr "getpwnam embedded NUL -> EIO" Errno.EIO (← opsNameNul.getpwnam (asciiBytes ['r', 'o', 'o', 't']))
  let opsRejectInvalid := Internal.mkPasswdOps {
    getpwuidOnce := fun _ _ => return .ok none
    getpwnamOnce := fun _ _ => return .ok none
  }
  expectErr "mock getpwnam(NUL) short-circuits -> EINVAL" Errno.EINVAL
    (← opsRejectInvalid.getpwnam (ByteArray.mk #[97, 0, 98]))

/-- Run all `Passwd` real and mocked error-path regression checks. -/
def runChecks : IO Unit := do
  assume_passwd_getpwuid_validAndMissingAndDeterministic
  assume_passwd_getpwnam_validAndMissingAndInvalid
  err_passwd_getpwuid_mocked
  err_passwd_getpwnam_invalidArg
  err_passwd_getpwnam_mocked

end Fuzz.Passwd.Checks
