import Std.Data.HashMap
import Fuzz.Common.Rng
import Fuzz.Common.Coverage
import Fuzz.Common.Shrink
import Fuzz.Common.Suite
import LeanSwe.Process.Interface
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Impl
import LeanSwe.ProcessSandbox.Interface

namespace Fuzz.ProcessSandbox

open Fuzz.Common
open LeanSwe.ProcessSandbox

private def errorKindCtor : SandboxErrorKind → String
  | .invalidInput => "LeanSwe.ProcessSandbox.SandboxErrorKind.invalidInput"
  | .unavailable => "LeanSwe.ProcessSandbox.SandboxErrorKind.unavailable"
  | .notFound => "LeanSwe.ProcessSandbox.SandboxErrorKind.notFound"
  | .permissionDenied => "LeanSwe.ProcessSandbox.SandboxErrorKind.permissionDenied"
  | .ioError => "LeanSwe.ProcessSandbox.SandboxErrorKind.ioError"

private def recordErrHit (op : String) (k : SandboxErrorKind) (mode : String := "real") : IO Unit :=
  Fuzz.Common.logErrHit s!"LeanSwe.ProcessSandbox.{op}" (errorKindCtor k) mode

private def requiredBuckets : Array CoverageBucket := #[
  bucket "isAvailable" "true",
  bucket "isAvailable" "false",
  bucket "validateSpec" "ok",
  bucket "validateSpec" "err.invalidInput",
  bucket "run" "err.invalidInput",
  bucket "run" "err.notFound",
  bucket "run" "err.notFound.tinyCap",
  bucket "run" "err.permissionDenied",
  bucket "run" "err.unavailable",
  bucket "run" "err.ioError",
  bucket "run" "ok.rwPersist",
  bucket "run" "ok.roReject",
  bucket "run" "ok.scratchDiscard",
  bucket "run" "ok.shadowedSubmount",
  bucket "run" "ok.unmountedInvisible",
  bucket "run" "ok.rootReadOnly",
  bucket "run" "ok.netClosed",
  bucket "run" "ok.netOpen",
  bucket "run" "ok.stdinAndStreams",
  bucket "run" "ok.cwdAndEnv",
  bucket "run" "ok.exitCode",
  bucket "run" "ok.timedOutNoOrphan",
  bucket "run" "ok.outputCapExact",
  bucket "run" "ok.outputCapSlackExceeded",
  bucket "run" "ok.outputCapPipeExceeded",
  bucket "run" "ok.outputCapCombinedExceeded"
]

private abbrev DirSnap := Std.HashMap String ByteArray

private def readDirSnap (dir : System.FilePath) : IO DirSnap := do
  let mut snap : DirSnap := {}
  if !(← dir.pathExists) then
    return snap
  let entries ← System.FilePath.walkDir dir
  for p in entries do
    if !(← p.isDir) then
      let bs ← IO.FS.readBinFile p
      snap := snap.insert p.toString bs
  return snap

private def dirSnapEq (a b : DirSnap) : Bool :=
  a.size == b.size &&
  a.toList.all fun (k, v) => b.get? k == some v

private def assertTrue (label : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL({label})")

private def mkChmod (mode path : String) : IO Unit := do
  match ← LeanSwe.Process.run { program := "chmod", args := #[mode, path], timeoutMs := some 5000 } with
  | .ok r =>
    if r.exitCode != 0 then
      throw (IO.userError s!"chmod {mode} {path} failed exit={r.exitCode}")
  | .error e =>
    throw (IO.userError s!"chmod {mode} {path} error: {e.message}")

private def mkEnvApi (extraEnv : Array (String × Option String)) (inherit : Bool) : ProcessSandboxApi :=
  Internal.mkApiM
    { LeanSwe.Process.defaultApi with
      run := fun req =>
        LeanSwe.Process.defaultApi.run { req with env := extraEnv ++ req.env, inheritEnv := inherit } }

private def countProcCmdlineWith (marker : String) : IO Nat := do
  let mut hits := 0
  let entries ← System.FilePath.readDir "/proc"
  for ent in entries do
    if ent.fileName.toList.all Char.isDigit && !ent.fileName.isEmpty then
      try
        let raw ← IO.FS.readBinFile (ent.path / "cmdline")
        let text := (String.fromUTF8? (ByteArray.mk (raw.data.map fun b => if b == 0 then 0x20 else b))).getD ""
        if (text.splitOn marker).length > 1 then
          hits := hits + 1
      catch _ => pure ()
  return hits

private def parseNetDevIfaces (raw : ByteArray) : List String :=
  let s := (String.fromUTF8? raw).getD ""
  let lines := s.splitOn "\n" |>.drop 2
  lines.filterMap fun ln =>
    match ln.splitOn ":" with
    | iface :: _ :: _ =>
      let t := iface.trimAscii.toString
      if t.isEmpty then none else some t
    | _ => none

private def exceptEq {ε α : Type} [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

private def checkValidateParity (label : String) (spec : BoxSpec) (tr : CoverageTracker) :
    IO CoverageTracker := do
  let got := LeanSwe.ProcessSandbox.validateSpec spec
  let exp := Model.validateSpecModel spec
  assertTrue s!"{label}.eqModel" (exceptEq got exp)
  match got with
  | .ok v =>
    let round := LeanSwe.ProcessSandbox.validateSpec (validBoxSpecToBoxSpec v)
    assertTrue s!"{label}.idempotent" (exceptEq round (.ok v))
    assertTrue s!"{label}.hasTmp" (v.mounts.toList.any (fun m => mountBoxPath m == "/tmp"))
    assertTrue s!"{label}.hasPath" (v.env.toList.any (fun kv => kv.1 == "PATH"))
    return tr.record "validateSpec" "ok"
  | .error e =>
    assertTrue s!"{label}.kindInvalid" (e.kind == .invalidInput && !e.message.isEmpty)
    recordErrHit "validateSpec" e.kind
    return tr.record "validateSpec" "err.invalidInput"

private def checkInvalidRunNoHostEffect (label : String) (root : System.FilePath)
    (spec : BoxSpec) (tr : CoverageTracker) : IO CoverageTracker := do
  let tr1 ← checkValidateParity label spec tr
  let before ← readDirSnap root
  let res ← LeanSwe.ProcessSandbox.run spec
  let after ← readDirSnap root
  assertTrue s!"{label}.hostUnchanged" (dirSnapEq before after)
  match res with
  | .ok r => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL({label}): expected invalidInput, got ok {repr r}")
  | .error e =>
    assertTrue s!"{label}.runInvalidKind" (e.kind == .invalidInput && !e.message.isEmpty)
    recordErrHit "run" e.kind
    return tr1.record "run" "err.invalidInput"

private def runDeterministicCorpus (root : System.FilePath) (tr0 : CoverageTracker) :
    IO CoverageTracker := do
  let mut tr := tr0
  let rwDir := root / "rw"
  let roDir := root / "ro"
  let secretDir := root / "secret"
  let workDir := root / "work"
  let gitDir := workDir / ".git"
  let subDir := workDir / "sub"
  for d in #[rwDir, roDir, secretDir, workDir, gitDir, subDir] do
    IO.FS.createDirAll d
  IO.FS.writeFile (roDir / "data.txt") "readonly-v1"
  IO.FS.writeFile (secretDir / "token.txt") "host-secret-42"
  IO.FS.writeFile (gitDir / "HEAD") "ref: refs/heads/main\n"
  IO.FS.writeFile (rwDir / "seed.txt") "seed-0"

  let avail ← LeanSwe.ProcessSandbox.isAvailable
  if !avail then
    let probe ← LeanSwe.Process.run Internal.mkProbeRequest
    throw (IO.userError s!"BWRAP_UNAVAILABLE_ON_HOST: isAvailable=false probe={repr probe}")
  tr := tr.record "isAvailable" "true"

  let invalidCases : Array (String × BoxSpec) := #[
    ("emptyProg", { program := "" }),
    ("nulProg", { program := "/bin/tr\x00ue" }),
    ("nulArg", { program := "/bin/true", args := #["a\x00b"] }),
    ("emptyEnvKey", { program := "/bin/true", env := #[("", "v")] }),
    ("eqEnvKey", { program := "/bin/true", env := #[("A=B", "v")] }),
    ("nulEnvKey", { program := "/bin/true", env := #[("A\x00B", "v")] }),
    ("nulEnvVal", { program := "/bin/true", env := #[("A", "v\x00w")] }),
    ("zeroTimeout", { program := "/bin/true", timeoutMs := some 0 }),
    ("zeroMaxOut", { program := "/bin/true", maxOutputBytes := some 0 }),
    ("relCwd", { program := "/bin/true", cwd := some "tmp" }),
    ("dotdotCwd", { program := "/bin/true", cwd := some "/tmp/../etc" }),
    ("nulCwd", { program := "/bin/true", cwd := some "/tmp/\x00x" }),
    ("relHostRo", { program := "/bin/true", mounts := #[.readOnly "rel" "/mnt"] }),
    ("dotdotHostRw", { program := "/bin/true", mounts := #[.readWrite "/tmp/../x" "/mnt"] }),
    ("relBox", { program := "/bin/true", mounts := #[.readOnly roDir.toString "mnt"] }),
    ("dotdotBox", { program := "/bin/true", mounts := #[.scratch "/mnt/../x"] }),
    ("reservedRoot", { program := "/bin/true", mounts := #[.scratch "/"] }),
    ("reservedUsr", { program := "/bin/true", mounts := #[.readOnly roDir.toString "/usr"] }),
    ("reservedUsrSub", { program := "/bin/true", mounts := #[.readOnly roDir.toString "/usr/local"] }),
    ("reservedBin", { program := "/bin/true", mounts := #[.scratch "/bin"] }),
    ("reservedSbin", { program := "/bin/true", mounts := #[.scratch "/sbin"] }),
    ("reservedLib", { program := "/bin/true", mounts := #[.scratch "/lib"] }),
    ("reservedLib64", { program := "/bin/true", mounts := #[.scratch "/lib64"] }),
    ("reservedEtc", { program := "/bin/true", mounts := #[.scratch "/etc"] }),
    ("reservedDev", { program := "/bin/true", mounts := #[.scratch "/dev"] }),
    ("reservedProc", { program := "/bin/true", mounts := #[.scratch "/proc"] }),
    ("dupBox", { program := "/bin/true", mounts := #[.scratch "/work", .scratch "/work/./"] }),
    ("rwAliasSame", {
      program := "/bin/true"
      mounts := #[.readWrite rwDir.toString "/a", .readWrite rwDir.toString "/b"]
    }),
    ("rwAliasChild", {
      program := "/bin/true"
      mounts := #[.readWrite workDir.toString "/work", .readOnly gitDir.toString "/other"]
    }),
    ("rwAliasParent", {
      program := "/bin/true"
      mounts := #[.readOnly workDir.toString "/work", .readWrite gitDir.toString "/other"]
    })
  ]
  for (lbl, spec) in invalidCases do
    tr ← checkInvalidRunNoHostEffect lbl root spec tr

  let missingHost := (root / "does-not-exist").toString
  for (lbl, spec, isTiny) in #[
    ("missingRoHost", ({ program := "/bin/true", mounts := #[.readOnly missingHost "/mnt"] } : BoxSpec), false),
    ("missingRwHost", ({ program := "/bin/true", mounts := #[.readWrite missingHost "/mnt"] } : BoxSpec), false),
    ("missingProg", ({ program := "/no_such_guest_prog_t115" } : BoxSpec), false),
    ("missingCwd", ({ program := "/bin/true", cwd := some "/no_such_cwd_t115" } : BoxSpec), false),
    ("missingProgTinyCap", ({ program := "/no_such_guest_prog_t115", maxOutputBytes := some 1 } : BoxSpec), true)
  ] do
    match ← LeanSwe.ProcessSandbox.run spec with
    | .error e =>
      assertTrue s!"{lbl}.kindNotFound" (e.kind == .notFound && !e.message.isEmpty)
      recordErrHit "run" e.kind
      tr := tr.record "run" "err.notFound"
      if isTiny then tr := tr.record "run" "err.notFound.tinyCap"
    | .ok r => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL({lbl}): expected notFound, got {repr r}")

  let noExecFile := root / "noexec.sh"
  IO.FS.writeFile noExecFile "#!/bin/sh\nexit 0\n"
  mkChmod "0644" noExecFile.toString
  match ← LeanSwe.ProcessSandbox.run {
    program := "/mnt/noexec.sh"
    mounts := #[.readOnly noExecFile.toString "/mnt/noexec.sh"]
  } with
  | .error e =>
    assertTrue "permNoExec.kind" (e.kind == .permissionDenied && !e.message.isEmpty)
    recordErrHit "run" e.kind
    tr := tr.record "run" "err.permissionDenied"
  | .ok r => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(permNoExec): expected permissionDenied, got {repr r}")

  let lockedDir := root / "locked_cwd"
  IO.FS.createDirAll lockedDir
  mkChmod "000" lockedDir.toString
  try
    match ← LeanSwe.ProcessSandbox.run {
      program := "/bin/true"
      cwd := some "/locked"
      mounts := #[.readOnly lockedDir.toString "/locked"]
    } with
    | .error e =>
      assertTrue "permLockedCwd.kind" (e.kind == .permissionDenied && !e.message.isEmpty)
      recordErrHit "run" e.kind
    | .ok r => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(permLockedCwd): expected permissionDenied, got {repr r}")
  finally
    mkChmod "700" lockedDir.toString

  let emptyPathDir := root / "empty_path"
  IO.FS.createDirAll emptyPathDir
  let unavailApi := mkEnvApi #[("PATH", some emptyPathDir.toString)] false
  let availFalse ← unavailApi.isAvailable
  assertTrue "unavail.isAvailableFalse" (!availFalse)
  tr := tr.record "isAvailable" "false"
  match ← unavailApi.run { program := "/bin/true" } with
  | .error e =>
    assertTrue "unavail.kind" (e.kind == .unavailable && !e.message.isEmpty)
    recordErrHit "run" e.kind
    tr := tr.record "run" "err.unavailable"
  | .ok r => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(unavail): expected unavailable, got {repr r}")

  let longPath := String.ofList (List.replicate 5000 'a')
  let ioErrApi := mkEnvApi #[("PATH", some longPath)] false
  match ← ioErrApi.run { program := "/bin/true" } with
  | .error e =>
    assertTrue "ioErr.kind" (e.kind == .ioError && !e.message.isEmpty)
    recordErrHit "run" e.kind
    tr := tr.record "run" "err.ioError"
  | .ok r => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(ioErr): expected ioError, got {repr r}")

  let shadowMounts : Array SandboxMount := #[
    .readOnly gitDir.toString "/work/.git",
    .readWrite workDir.toString "/work",
    .readOnly roDir.toString "/ro",
    .readWrite rwDir.toString "/rw",
    .scratch "/scratch"
  ]
  let shadowSpec : BoxSpec := {
    program := "/bin/sh"
    args := #["-c",
      "set -e; " ++
      "test \"$(cat /ro/data.txt)\" = 'readonly-v1'; " ++
      "(! (echo tamper > /ro/data.txt 2>/dev/null)); " ++
      "test \"$(cat /rw/seed.txt)\" = 'seed-0'; " ++
      "printf 'persisted-1' > /rw/new.txt; " ++
      "printf 'scratch-val' > /scratch/ephem.txt; " ++
      "test \"$(cat /scratch/ephem.txt)\" = 'scratch-val'; " ++
      "printf 'work-ok' > /work/out.txt; " ++
      "test \"$(cat /work/.git/HEAD)\" = 'ref: refs/heads/main'; " ++
      "(! (echo pwn > /work/.git/HEAD 2>/dev/null)); " ++
      "test ! -e " ++ secretDir.toString ++ "/token.txt; " ++
      "(! (echo rootbad > /root_evil 2>/dev/null))"]
    mounts := shadowMounts
  }
  tr ← checkValidateParity "shadowSpec" shadowSpec tr
  let hostSnapBefore : Model.FsState := fun p =>
    if p == (roDir / "data.txt").toString then some "readonly-v1".toUTF8
    else if p == (secretDir / "token.txt").toString then some "host-secret-42".toUTF8
    else if p == (gitDir / "HEAD").toString then some "ref: refs/heads/main\n".toUTF8
    else if p == (rwDir / "seed.txt").toString then some "seed-0".toUTF8
    else none
  let guestBefore := Model.projectGuestFs hostSnapBefore shadowMounts.toList (fun _ => none)
  assertTrue "model.projRo" (guestBefore "/ro/data.txt" == some "readonly-v1".toUTF8)
  assertTrue "model.projGit" (guestBefore "/work/.git/HEAD" == some "ref: refs/heads/main\n".toUTF8)
  assertTrue "model.projSecret" (guestBefore (secretDir / "token.txt").toString == none)
  let guestAfter : Model.FsState := fun p =>
    if p == "/rw/new.txt" then some "persisted-1".toUTF8
    else if p == "/work/out.txt" then some "work-ok".toUTF8
    else if p == "/work/.git/HEAD" then some "pwn\n".toUTF8
    else if p == "/ro/data.txt" then some "tamper\n".toUTF8
    else if p == "/scratch/ephem.txt" then some "scratch-val".toUTF8
    else guestBefore p
  let hostModelAfter := Model.applyWriteBack hostSnapBefore guestAfter shadowMounts.toList
  match ← LeanSwe.ProcessSandbox.run shadowSpec with
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(shadowSpec): {repr e}")
  | .ok r =>
    assertTrue "shadowSpec.exit0" (r.outcome == .exited 0)
    assertTrue "rwPersist" (some (← IO.FS.readBinFile (rwDir / "new.txt")) == hostModelAfter (rwDir / "new.txt").toString)
    assertTrue "roUnchanged" (some (← IO.FS.readBinFile (roDir / "data.txt")) == hostModelAfter (roDir / "data.txt").toString)
    assertTrue "workPersist" (some (← IO.FS.readBinFile (workDir / "out.txt")) == hostModelAfter (workDir / "out.txt").toString)
    assertTrue "gitProtected" (some (← IO.FS.readBinFile (gitDir / "HEAD")) == hostModelAfter (gitDir / "HEAD").toString)
    assertTrue "secretUnchanged" (some (← IO.FS.readBinFile (secretDir / "token.txt")) == hostModelAfter (secretDir / "token.txt").toString)
    tr := (((((tr.record "run" "ok.rwPersist")
      |>.record "run" "ok.roReject")
      |>.record "run" "ok.scratchDiscard")
      |>.record "run" "ok.shadowedSubmount")
      |>.record "run" "ok.unmountedInvisible")
      |>.record "run" "ok.rootReadOnly"

  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/sh"
    args := #["-c", "test ! -e /scratch/ephem.txt && test ! -e /tmp/ephem.txt"]
    mounts := #[.scratch "/scratch"]
  } with
  | .ok r => assertTrue "scratchFresh" (r.outcome == .exited 0)
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(scratchFresh): {repr e}")

  let hostIfaces := parseNetDevIfaces (← IO.FS.readBinFile "/proc/net/dev")
  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/cat", args := #["/proc/net/dev"], network := .closed
  } with
  | .ok r =>
    assertTrue "netClosed.exit0" (r.outcome == .exited 0)
    assertTrue "netClosed.loOnly" (parseNetDevIfaces r.stdout == ["lo"])
    tr := tr.record "run" "ok.netClosed"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(netClosed): {repr e}")

  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/cat", args := #["/proc/net/dev"], network := .«open»
  } with
  | .ok r =>
    assertTrue "netOpen.exit0" (r.outcome == .exited 0)
    assertTrue "netOpen.matchesHost" (parseNetDevIfaces r.stdout == hostIfaces)
    tr := tr.record "run" "ok.netOpen"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(netOpen): {repr e}")

  let stdinBytes := ByteArray.mk #[0x48, 0x69, 0x00, 0xFF, 0x0A]
  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/sh"
    args := #["-c", "printf 'err-tag' >&2; exec cat"]
    stdin := stdinBytes
  } with
  | .ok r =>
    assertTrue "stdinStreams.exit0" (r.outcome == .exited 0)
    assertTrue "stdinStreams.stdout" (r.stdout == stdinBytes)
    assertTrue "stdinStreams.stderr" (r.stderr == "err-tag".toUTF8)
    tr := tr.record "run" "ok.stdinAndStreams"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(stdinStreams): {repr e}")

  let hostLeakApi := mkEnvApi #[("LEANSWE_HOST_SECRET_T115", some "must-not-leak")] true
  match ← hostLeakApi.run {
    program := "/bin/sh"
    args := #["-c", "printf '%s|%s|%s|%s' \"$PWD\" \"$K\" \"$PATH\" \"${LEANSWE_HOST_SECRET_T115:-absent}\""]
    cwd := some "/work//./sub/"
    env := #[("K", "first"), ("OTHER", "x"), ("K", "second")]
    mounts := #[.readOnly workDir.toString "/work"]
  } with
  | .ok r =>
    assertTrue "cwdEnv.exit0" (r.outcome == .exited 0)
    assertTrue "cwdEnv.out" (r.stdout == "/work/sub|second|/usr/bin:/bin|absent".toUTF8)
    tr := tr.record "run" "ok.cwdAndEnv"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(cwdEnv): {repr e}")

  for code in #[0, 1, 42, 127] do
    match ← LeanSwe.ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c", s!"printf 'guest-err' >&2; exit {code}"]
    } with
    | .ok r =>
      assertTrue s!"exit.{code}" (r.outcome == .exited (Int.ofNat code) && r.stderr == "guest-err".toUTF8)
    | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(exit.{code}): {repr e}")
  tr := tr.record "run" "ok.exitCode"

  let marker := "leanswe_t115_orphan_probe_918273"
  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/sh"
    args := #["-c", s!"/bin/sh -c 'sleep 30; :' {marker} & /bin/sh -c 'sleep 30; :' {marker}; wait"]
    timeoutMs := some 150
    maxOutputBytes := some 64
  } with
  | .ok r =>
    assertTrue s!"timeout.outcome({repr r.outcome})" (r.outcome == .timedOut)
    assertTrue "timeout.cap" (r.stdout.size + r.stderr.size ≤ 64)
    let orphans ← countProcCmdlineWith marker
    assertTrue s!"timeout.noOrphans({orphans})" (orphans == 0)
    assertTrue "timeout.noActiveHandles" ((← LeanSwe.Process.activeProcessCount) == 0)
    tr := tr.record "run" "ok.timedOutNoOrphan"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(timeout): {repr e}")

  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/sh", args := #["-c", "printf '12345678'"], maxOutputBytes := some 8
  } with
  | .ok r =>
    assertTrue "capExact" (r.outcome == .exited 0 && r.stdout == "12345678".toUTF8 && r.stderr.isEmpty)
    tr := tr.record "run" "ok.outputCapExact"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(capExact): {repr e}")

  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/sh", args := #["-c", "printf '123456789'"], maxOutputBytes := some 8
  } with
  | .ok r =>
    assertTrue "capSlack" (r.outcome == .outputLimitExceeded && r.stdout.size + r.stderr.size ≤ 8)
    tr := tr.record "run" "ok.outputCapSlackExceeded"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(capSlack): {repr e}")

  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/sh", args := #["-c", "head -c 65536 /dev/zero"], maxOutputBytes := some 32
  } with
  | .ok r =>
    assertTrue "capPipe" (r.outcome == .outputLimitExceeded && r.stdout.size + r.stderr.size ≤ 32)
    tr := tr.record "run" "ok.outputCapPipeExceeded"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(capPipe): {repr e}")

  match ← LeanSwe.ProcessSandbox.run {
    program := "/bin/sh", args := #["-c", "printf '12345'; printf '67890' >&2"], maxOutputBytes := some 8
  } with
  | .ok r =>
    assertTrue "capCombined" (r.outcome == .outputLimitExceeded && r.stdout.size + r.stderr.size ≤ 8)
    tr := tr.record "run" "ok.outputCapCombinedExceeded"
  | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(capCombined): {repr e}")

  return tr

private inductive FuzzStep where
  | validateRandom (spec : BoxSpec)
  | runValidEcho (payload : ByteArray) (errTag : String) (exitCode : Nat) (cap? : Option Nat)
      (net : NetworkMode) (envPairs : Array (String × String))
  | runMountStep (writeVal : String) (reverseOrder : Bool)
  deriving BEq

private def genPath (r : Rng) (allowBad : Bool) : String × Rng :=
  let segsPool := #["work", "sub", "a", "b", "tmp", "usr", "etc", ".", "..", ""]
  let (kind, r1) := r.nextNat (if allowBad then 8 else 3)
  if kind == 0 then
    let (s1, r2) := r1.choose #["work", "data", "app", "mnt"] "work"
    let (s2, r3) := r2.choose #["sub", "x", "y", ".git"] "sub"
    (s!"/{s1}/{s2}", r3)
  else if kind == 1 then
    let (s1, r2) := r1.choose #["work", "data", "tmp"] "work"
    (s!"/{s1}//./", r2)
  else if kind == 2 then
    ("/tmp", r1)
  else if kind == 3 then
    ("rel/path", r1)
  else if kind == 4 then
    let (s, r2) := r1.choose segsPool "usr"
    (s!"/{s}/child", r2)
  else if kind == 5 then
    ("/work/../escape", r1)
  else if kind == 6 then
    ("/work/bad\x00nul", r1)
  else
    ("", r1)

private def genRandomBoxSpec (r : Rng) : BoxSpec × Rng :=
  let (progChoice, r1) := r.nextNat 5
  let (prog, r2) :=
    if progChoice == 0 then ("", r1)
    else if progChoice == 1 then ("/bin/ec\x00ho", r1)
    else ("/bin/true", r1)
  let (nMounts, r3) := r2.nextNat 4
  let (mounts, r4) := (List.range nMounts).foldl (init := (#[], r3)) fun (acc, rg) _ =>
    let (mk, rg1) := rg.nextNat 3
    let (hp, rg2) := genPath rg1 true
    let (bp, rg3) := genPath rg2 true
    let m := if mk == 0 then .readOnly hp bp else if mk == 1 then .readWrite hp bp else .scratch bp
    (acc.push m, rg3)
  let (nEnv, r5) := r4.nextNat 4
  let (env, r6) := (List.range nEnv).foldl (init := (#[], r5)) fun (acc, rg) _ =>
    let (k, rg1) := rg.choose #["K1", "K2", "PATH", "", "A=B", "N\x00K"] "K1"
    let (v, rg2) := rg1.choose #["v1", "v2", "/bin", "bad\x00v"] "v1"
    (acc.push (k, v), rg2)
  let (cwdKind, r7) := r6.nextNat 3
  let (cwd?, r8) :=
    if cwdKind == 0 then (none, r7)
    else let (p, rg') := genPath r7 true; (some p, rg')
  let (toKind, r9) := r8.nextNat 3
  let to? := if toKind == 0 then none else if toKind == 1 then some 0 else some 500
  let (capKind, r10) := r9.nextNat 3
  let cap? := if capKind == 0 then none else if capKind == 1 then some 0 else some 64
  let (netB, r11) := r10.nextBool
  ({ program := prog, env, cwd := cwd?, mounts,
     network := if netB then .«open» else .closed, timeoutMs := to?, maxOutputBytes := cap? }, r11)

private def evalRandomStep (root : System.FilePath) (step : FuzzStep) (tr : CoverageTracker) :
    IO CoverageTracker := do
  match step with
  | .validateRandom spec =>
    let tr1 ← checkValidateParity "randVal" spec tr
    match Model.validateSpecModel spec with
    | .error _ => checkInvalidRunNoHostEffect "randInvalidRun" root spec tr1
    | .ok _ => return tr1
  | .runValidEcho payload errTag exitCode cap? net envPairs =>
    let spec : BoxSpec := {
      program := "/bin/sh"
      args := #["-c", s!"printf '%s' '{errTag}' >&2; cat; exit {exitCode}"]
      stdin := payload
      env := envPairs
      network := net
      maxOutputBytes := cap?
      timeoutMs := some 5000
    }
    let tr1 ← checkValidateParity "randEcho" spec tr
    match ← LeanSwe.ProcessSandbox.run spec with
    | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(randEcho): {repr e}")
    | .ok r =>
      let rawTotal := payload.size + errTag.toUTF8.size
      match cap? with
      | some cap =>
        assertTrue "randEcho.capBound" (r.stdout.size + r.stderr.size ≤ cap)
        if rawTotal > cap then
          assertTrue "randEcho.exceeded" (r.outcome == .outputLimitExceeded)
        else
          assertTrue "randEcho.exactMatch"
            (r.outcome == .exited (Int.ofNat exitCode) && r.stdout == payload && r.stderr == errTag.toUTF8)
      | none =>
        assertTrue "randEcho.noCapMatch"
          (r.outcome == .exited (Int.ofNat exitCode) && r.stdout == payload && r.stderr == errTag.toUTF8)
      return tr1
  | .runMountStep writeVal reverseOrder =>
    let rwDir := root / "rand_rw"
    let roSub := rwDir / "ro_sub"
    let roDir := root / "rand_ro"
    IO.FS.createDirAll roSub
    IO.FS.createDirAll roDir
    IO.FS.writeFile (roSub / "pin.txt") "pinned"
    IO.FS.writeFile (roDir / "imm.txt") "immutable"
    let mounts :=
      if reverseOrder then
        #[.readOnly roSub.toString "/box/ro_sub", .readWrite rwDir.toString "/box",
          .readOnly roDir.toString "/ro", .scratch "/tmp"]
      else
        #[.readWrite rwDir.toString "/box", .readOnly roSub.toString "/box/ro_sub",
          .readOnly roDir.toString "/ro", .scratch "/tmp"]
    let spec : BoxSpec := {
      program := "/bin/sh"
      args := #["-c", s!"printf '%s' '{writeVal}' > /box/val.txt; (! (echo x > /box/ro_sub/pin.txt 2>/dev/null)); (! (echo x > /ro/imm.txt 2>/dev/null))"]
      mounts
      timeoutMs := some 5000
    }
    match ← LeanSwe.ProcessSandbox.run spec with
    | .error e => throw (IO.userError s!"PROCESSSANDBOX_FUZZ_FAIL(randMount): {repr e}")
    | .ok r =>
      assertTrue "randMount.exit0" (r.outcome == .exited 0)
      assertTrue "randMount.rw" ((← IO.FS.readFile (rwDir / "val.txt")) == writeVal)
      assertTrue "randMount.roSub" ((← IO.FS.readFile (roSub / "pin.txt")) == "pinned")
      assertTrue "randMount.ro" ((← IO.FS.readFile (roDir / "imm.txt")) == "immutable")
      return tr

private def runSeededFuzz (cfg : FuzzConfig) (totalSteps maxBwrapSpawns : Nat) : IO Unit := do
  let root ← IO.FS.createTempDir
  try
    let mut tr ← runDeterministicCorpus root CoverageTracker.empty
    let mut rng := Rng.seed cfg.seed
    let mut bwrapDone : Nat := 0
    for idx in [:totalSteps] do
      let (choice, r1) := rng.nextNat 10
      rng := r1
      let canSpawn := bwrapDone < maxBwrapSpawns && (choice < 4 || totalSteps ≤ 200)
      let step ←
        if canSpawn && choice < 2 then
          bwrapDone := bwrapDone + 1
          let (sz, r2) := rng.nextRange 0 48
          let (payload, r3) := r2.nextBytesRange 0 sz
          let (errTag, r4) := r3.choose #["", "e1", "warn-tag"] "e1"
          let (code, r5) := r4.choose #[0, 1, 2, 7, 42] 0
          let (useCap, r6) := r5.nextBool
          let (capVal, r7) := r6.choose #[1, 4, 8, 16, 64] 16
          let (netB, r8) := r7.nextBool
          let (kVal, r9) := r8.choose #["a", "b", "c"] "a"
          rng := r9
          pure (.runValidEcho payload errTag code (if useCap then some capVal else none)
            (if netB then .«open» else .closed) #[("K", "old"), ("K", kVal)])
        else if canSpawn && choice == 2 then
          bwrapDone := bwrapDone + 1
          let (rev, r2) := rng.nextBool
          rng := r2
          pure (.runMountStep s!"v-{idx}" rev)
        else
          let (spec, r2) := genRandomBoxSpec rng
          rng := r2
          pure (.validateRandom spec)
      tr ← evalRandomStep root step tr
    assertCoverage "processsandbox" tr requiredBuckets
    IO.println s!"PROCESSSANDBOX_FUZZ_OK: steps={totalSteps} bwrapSpawns={bwrapDone} buckets={requiredBuckets.size}/{requiredBuckets.size} seed={cfg.seed}"
  finally
    try IO.FS.removeDirAll root catch _ => pure ()

private def shrinkStepItem : FuzzStep → List FuzzStep
  | .runValidEcho p e c cap? net env =>
    (if p.size > 0 then [.runValidEcho ByteArray.empty e c cap? net env] else []) ++
    (if !e.isEmpty then [.runValidEcho p "" c cap? net env] else []) ++
    (if !env.isEmpty then [.runValidEcho p e c cap? net #[]] else [])
  | _ => []

private def runShrinkSelfTest (seedVal : UInt64) : IO Unit := do
  runGenericShrinkSelfTest seedVal
  let filler : FuzzStep := .validateRandom { program := "/bin/true" }
  let target : FuzzStep := .runValidEcho "abcdef".toUTF8 "err" 7 (some 8) .closed #[("A", "1")]
  let trace : Array FuzzStep := #[filler, filler, target, filler, .runMountStep "x" true, filler]
  let isFault (xs : Array FuzzStep) : IO Bool :=
    return xs.any fun
      | .runValidEcho _ _ c _ _ _ => c == 7
      | _ => false
  match ← verifyShrinker isFault trace 1 with
  | .error msg => throw (IO.userError s!"PROCESSSANDBOX_SHRINK_FAIL: {msg}")
  | .ok shrunk =>
    let elShrunk ← shrinkElements shrinkStepItem isFault shrunk
    match elShrunk.toList with
    | [.runValidEcho p e 7 (some 8) .closed env] =>
      assertTrue "shrink.minimized" (p.isEmpty && e.isEmpty && env.isEmpty)
    | other => throw (IO.userError s!"PROCESSSANDBOX_SHRINK_ELEM_FAIL: len={other.length}")
  IO.println "PROCESSSANDBOX_SHRINK_SELFTEST_OK"

/-- Registered differential fuzz suite for `LeanSwe.ProcessSandbox` against real `/usr/bin/bwrap`. -/
def suite : FuzzSuite :=
  { name := "processsandbox"
    description := "Differential fuzzer comparing LeanSwe.ProcessSandbox against Model over real bwrap"
    runSmoke := fun cfg => do
      Fuzz.Common.recordSuiteSteps 120
      runSeededFuzz cfg 120 40
    runFuzz := fun cfg => do
      Fuzz.Common.recordSuiteSteps cfg.steps
      let bwrapCap := if cfg.steps ≤ 500 then cfg.steps else 600
      runSeededFuzz cfg cfg.steps bwrapCap
    selfTestShrink := runShrinkSelfTest }

end Fuzz.ProcessSandbox
