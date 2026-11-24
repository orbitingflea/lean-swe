import Core.Assumptions
import LeanSwe.TempDir.Interface
import LeanSwe.TempDir.Impl
import LeanSwe.Process.Interface

namespace LeanSwe.TempDir.RuntimeTests

open LeanSwe
open LeanSwe.Fs (FsError)

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertTempDirOk {α : Type} (res : Except TempDirError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected TempDirError: {repr e})")

private def assertFsOk {α : Type} (res : Except FsError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected FsError: {repr e})")

private def assertTempDirErrKind {α : Type} (res : Except TempDirError α) (expected : TempDirErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected TempDirError {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def waitForFile (path : String) : IO Unit := do
  for _ in List.range 500 do
    match ← Fs.pathExists path with
    | .ok true => return ()
    | _ => IO.sleep 10
  throw (IO.userError s!"ASSERTION FAILED: timed out waiting for marker file {path}")

private def isSorted (xs : Array String) : Bool :=
  let ls := xs.toList
  (ls.zip ls.tail).all fun (a, b) => decide (a ≤ b)

private def testWithTempDirLifecycle (sandbox : String) : IO Unit := do
  let createdPathRef ← IO.mkRef ""
  let resOk ← TempDir.withTempDir (some sandbox) "wt-" fun d => do
    createdPathRef.set d
    let st ← match ← Fs.lstat d with
      | .ok s => pure s
      | .error e => return .error (Internal.mapFsError e)
    assertTrue (st.kind == .dir) "withTempDir created directory"
    assertTrue (st.mode % 0o1000 == 0o700) "withTempDir enforced mode 0o700"
    let p := Fs.join d "payload.txt"
    match ← Fs.writeText p "hello" with
    | .ok () => return .ok (42 : Nat)
    | .error e => return .error (Internal.mapFsError e)
  let v ← assertTempDirOk resOk "withTempDir ok return"
  assertTrue (v == 42) "withTempDir returned expected value"
  let createdPath ← createdPathRef.get
  assertTrue (createdPath.startsWith (Fs.join sandbox "wt-")) "withTempDir path prefix"
  match ← Fs.pathExists createdPath with
  | .ok ex => assertTrue (!ex) "withTempDir removed dir on ok exit"
  | .error e => throw (IO.userError s!"pathExists failed: {repr e}")

  let errDirRef ← IO.mkRef ""
  let expectedErr : TempDirError := { kind := .ioError, path := none, message := "action error" }
  let resErr ← TempDir.withTempDir (some sandbox) "wt-err-" fun d => do
    errDirRef.set d
    let _ ← Fs.writeText (Fs.join d "tmp.txt") "data"
    return (Except.error expectedErr : Except TempDirError Nat)
  assertTempDirErrKind resErr .ioError "withTempDir preserves action error"
  let errDir ← errDirRef.get
  match ← Fs.pathExists errDir with
  | .ok ex => assertTrue (!ex) "withTempDir removed dir on error exit"
  | .error e => throw (IO.userError s!"pathExists failed: {repr e}")

  let exDirRef ← IO.mkRef ""
  let threw ← try
    let _r : Except TempDirError Unit ← TempDir.withTempDir (some sandbox) "wt-ex-" fun d => do
      exDirRef.set d
      let _ ← Fs.writeText (Fs.join d "crash.txt") "x"
      throw (IO.userError "boom")
    pure false
  catch _ => pure true
  assertTrue threw "withTempDir propagated IO exception"
  let exDir ← exDirRef.get
  assertTrue (!exDir.isEmpty) "withTempDir entered action before throw"
  match ← Fs.pathExists exDir with
  | .ok ex => assertTrue (!ex) "withTempDir removed dir on IO exception"
  | .error e => throw (IO.userError s!"pathExists failed: {repr e}")

  for badPrefix in ["", ".", "..", ".dot", "sub/dir", String.ofList ['a', Char.ofNat 0]] do
    let r ← TempDir.withTempDir (some sandbox) badPrefix fun _ => pure (.ok () : Except TempDirError Unit)
    assertTempDirErrKind r .invalidInput s!"reject invalid prefix {repr badPrefix}"
  let rBadRoot ← TempDir.withTempDir (some "") "wt-" fun _ => pure (.ok () : Except TempDirError Unit)
  assertTempDirErrKind rBadRoot .invalidInput "reject empty explicit root"

private def testWithLockedTempDirAndRootResolution (sandbox : String) : IO Unit := do
  let lockedDirRef ← IO.mkRef ""
  let resOk ← TempDir.withLockedTempDir (some sandbox) "wl-" fun d => do
    lockedDirRef.set d
    let lockPath := Fs.join d ".lock"
    let stDir ← match ← Fs.lstat d with
      | .ok s => pure s
      | .error e => return .error (Internal.mapFsError e)
    let stLock ← match ← Fs.lstat lockPath with
      | .ok s => pure s
      | .error e => return .error (Internal.mapFsError e)
    assertTrue (stDir.kind == .dir && stDir.mode % 0o1000 == 0o700) "withLockedTempDir mode 0o700"
    assertTrue (stLock.kind == .file) "withLockedTempDir created regular .lock file"
    match ← Fs.tryWithFileLock lockPath .shared false (pure (.ok ())) with
    | .ok (some ()) => pure ()
    | other => throw (IO.userError s!"shared lock should coexist inside withLockedTempDir: {repr other}")
    match ← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok ())) with
    | .ok none => pure ()
    | other => throw (IO.userError s!"exclusive lock must block while inside withLockedTempDir: {repr other}")
    return .ok "locked-ok"
  let val ← assertTempDirOk resOk "withLockedTempDir ok"
  assertTrue (val == "locked-ok") "withLockedTempDir ok value"
  let lockedDir ← lockedDirRef.get
  match ← Fs.pathExists lockedDir with
  | .ok ex => assertTrue (!ex) "withLockedTempDir removed dir on exit"
  | .error e => throw (IO.userError s!"pathExists failed: {repr e}")

  let exLockedRef ← IO.mkRef ""
  let threw ← try
    let _r : Except TempDirError Unit ← TempDir.withLockedTempDir (some sandbox) "wl-ex-" fun d => do
      exLockedRef.set d
      throw (IO.userError "boom-locked")
    pure false
  catch _ => pure true
  assertTrue threw "withLockedTempDir propagated IO exception"
  let exLocked ← exLockedRef.get
  match ← Fs.pathExists exLocked with
  | .ok ex => assertTrue (!ex) "withLockedTempDir removed dir on exception"
  | .error e => throw (IO.userError s!"pathExists failed: {repr e}")

  let realRes ← TempDir.withTempDir none "lean-swe-tempdir-rt-" fun d => do
    match ← Fs.pathExists d with
    | .ok ex =>
      assertTrue ex "defaultApi root? := none created real dir"
      return .ok d
    | .error e => return .error (Internal.mapFsError e)
  let realPath ← assertTempDirOk realRes "defaultApi root? := none succeeded"
  match ← Fs.pathExists realPath with
  | .ok ex => assertTrue (!ex) "defaultApi root? := none cleaned up real dir"
  | .error e => throw (IO.userError s!"pathExists failed: {repr e}")

  let customEnvOk : EnvVars.EnvVarsApiM IO :=
    { EnvVars.defaultApi with getEnv := fun k => pure (.ok (if k == "TMPDIR" then some sandbox else none)) }
  let customApiOk := Internal.mkApiM Fs.defaultApi Time.defaultOps Uuid.defaultApi customEnvOk
  let customRes ← customApiOk.withTempDir none "env-ok-" fun d => pure (.ok d)
  let customPath ← assertTempDirOk customRes "TMPDIR custom env resolved"
  assertTrue (customPath.startsWith (Fs.join sandbox "env-ok-")) "TMPDIR path honored"

  let missingPath := Fs.join sandbox "does-not-exist-tmpdir"
  let customEnvMissing : EnvVars.EnvVarsApiM IO :=
    { EnvVars.defaultApi with getEnv := fun k => pure (.ok (if k == "TMPDIR" then some missingPath else none)) }
  let customApiMissing := Internal.mkApiM Fs.defaultApi Time.defaultOps Uuid.defaultApi customEnvMissing
  assertTempDirErrKind (← customApiMissing.withTempDir none "env-miss-" fun _ => pure (.ok ()))
    .notFound "missing TMPDIR fails strictly"

  let fileTmp := Fs.join sandbox "not-a-dir.txt"
  assertFsOk (← Fs.writeText fileTmp "x") "create regular file for TMPDIR non-dir check"
  let customEnvFile : EnvVars.EnvVarsApiM IO :=
    { EnvVars.defaultApi with getEnv := fun k => pure (.ok (if k == "TMPDIR" then some fileTmp else none)) }
  let customApiFile := Internal.mkApiM Fs.defaultApi Time.defaultOps Uuid.defaultApi customEnvFile
  assertTempDirErrKind (← customApiFile.withTempDir none "env-file-" fun _ => pure (.ok ()))
    .notADirectory "non-dir TMPDIR fails with notADirectory"

private def testCleanupStaleTempDirsOS (sandbox : String) : IO Unit := do
  let sweepRoot := Fs.join sandbox "sweep"
  assertFsOk (← Fs.mkdir sweepRoot false false) "create sweep root"

  let liveDir := Fs.join sweepRoot "job-live-locked"
  let liveLock := Fs.join liveDir ".lock"
  let liveReady := Fs.join sandbox "live.ready"
  let liveStop := Fs.join sandbox "live.stop"
  assertFsOk (← Fs.mkdir liveDir false false) "create liveDir"
  assertFsOk (← Fs.writeText liveLock "") "create live .lock"
  assertFsOk (← Fs.writeText (Fs.join liveDir "work.txt") "busy") "create live payload"

  let deadDir := Fs.join sweepRoot "job-crashed-locked"
  let deadLock := Fs.join deadDir ".lock"
  let deadReady := Fs.join sandbox "dead.ready"
  assertFsOk (← Fs.mkdir deadDir false false) "create deadDir"
  assertFsOk (← Fs.writeText deadLock "") "create dead .lock"
  assertFsOk (← Fs.writeText (Fs.join deadDir "stale.txt") "orphan") "create dead payload"

  let freshDir := Fs.join sweepRoot "job-fresh-unlocked"
  assertFsOk (← Fs.mkdir freshDir false false) "create freshDir"

  let oldDir := Fs.join sweepRoot "job-old-unlocked"
  assertFsOk (← Fs.mkdir oldDir false false) "create oldDir"
  assertFsOk (← Fs.writeText (Fs.join oldDir "old.txt") "bye") "create old payload"

  let otherDir := Fs.join sweepRoot "other-keep"
  assertFsOk (← Fs.mkdir otherDir false false) "create non-matching dir"

  let fileChild := Fs.join sweepRoot "job-regular-file"
  assertFsOk (← Fs.writeText fileChild "keep-file") "create matching regular file"

  let symTarget := Fs.join sandbox "symlink-target"
  assertFsOk (← Fs.mkdir symTarget false false) "create symlink target dir"
  let symChild := Fs.join sweepRoot "job-symlink"
  assertFsOk (← Fs.symlink symTarget symChild) "create matching symlink"

  let badLockDir := Fs.join sweepRoot "job-bad-lock"
  let badLockTarget := Fs.join sandbox "bad-lock-target"
  assertFsOk (← Fs.writeText badLockTarget "t") "create badLockTarget"
  assertFsOk (← Fs.mkdir badLockDir false false) "create badLockDir"
  assertFsOk (← Fs.symlink badLockTarget (Fs.join badLockDir ".lock")) "create symlink .lock"

  let holdScript :=
    "import fcntl, os, sys, time\n" ++
    "lp, rp, sp = sys.argv[1:4]\n" ++
    "fd = os.open(lp, os.O_RDONLY)\n" ++
    "fcntl.flock(fd, fcntl.LOCK_SH)\n" ++
    "open(rp, 'w').write('1')\n" ++
    "deadline = time.monotonic() + 15.0\n" ++
    "while not os.path.exists(sp) and time.monotonic() < deadline:\n" ++
    "  time.sleep(0.01)\n"
  let liveChild ← match ← Process.spawn
      { program := "python3", args := #["-c", holdScript, liveLock, liveReady, liveStop] } with
    | .ok h => pure h
    | .error e => throw (IO.userError s!"spawn liveChild failed: {repr e}")

  let deadScript :=
    "import fcntl, os, signal, sys, time\n" ++
    "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n" ++
    "lp, rp = sys.argv[1:3]\n" ++
    "fd = os.open(lp, os.O_RDONLY)\n" ++
    "fcntl.flock(fd, fcntl.LOCK_EX)\n" ++
    "open(rp, 'w').write('1')\n" ++
    "time.sleep(15.0)\n"
  let deadChild ← match ← Process.spawn
      { program := "python3", args := #["-c", deadScript, deadLock, deadReady] } with
    | .ok h => pure h
    | .error e =>
      let _ ← Fs.writeText liveStop "go"
      let _ ← Process.reap liveChild
      throw (IO.userError s!"spawn deadChild failed: {repr e}")

  try
    waitForFile liveReady
    waitForFile deadReady
    match ← Process.runCommand "kill" #["-9", toString deadChild.pid] with
    | .ok kout => assertTrue (kout.exitCode == 0) "kill -9 deadChild exitCode 0"
    | .error e => throw (IO.userError s!"kill -9 deadChild failed: {repr e}")
    let _ ← Process.reap deadChild

    let rep1 ← assertTempDirOk (← TempDir.cleanupStaleTempDirs (some sweepRoot) "job-" 3600)
      "first cleanup pass with 3600s grace window"
    assertTrue (rep1.keptLocked.toList.contains liveDir) "live locked dir kept in pass 1"
    assertTrue (!rep1.removed.toList.contains liveDir) "live locked dir not removed in pass 1"
    assertTrue (rep1.removed.toList.contains deadDir) "SIGKILL dead locked dir removed immediately"
    assertTrue (rep1.keptFresh.toList.contains freshDir) "fresh unlocked dir kept within grace window"
    assertTrue (rep1.keptFresh.toList.contains oldDir) "unlocked dir kept within 3600s window"
    assertTrue (rep1.skipped.toList.contains otherDir) "non-matching dir skipped"
    assertTrue (rep1.skipped.toList.contains fileChild) "matching regular file skipped"
    assertTrue (rep1.skipped.toList.contains symChild) "matching symlink skipped"
    assertTrue (rep1.failed.any (fun e => e.kind == .invalidInput && e.path == some (Fs.join badLockDir ".lock")))
      "symlink .lock rejected into rep.failed"
    assertTrue (isSorted rep1.removed && isSorted rep1.keptLocked && isSorted rep1.keptFresh && isSorted rep1.skipped)
      "report arrays sorted"
    assertTrue (!(← assertFsOk (← Fs.pathExists deadDir) "pathExists deadDir")) "deadDir removed from disk"
    assertTrue (← assertFsOk (← Fs.pathExists liveDir) "pathExists liveDir") "liveDir still on disk"
    assertTrue (← assertFsOk (← Fs.pathExists badLockDir) "pathExists badLockDir") "badLockDir preserved"
    assertTrue (← assertFsOk (← Fs.pathExists symTarget) "pathExists symTarget") "symlink target untouched"

    IO.sleep 1500
    let rep2 ← assertTempDirOk (← TempDir.cleanupStaleTempDirs (some sweepRoot) "job-" 0)
      "second cleanup pass with maxAgeSec = 0"
    assertTrue (rep2.keptLocked.toList.contains liveDir) "live locked dir STILL kept even when maxAgeSec = 0"
    assertTrue (!rep2.removed.toList.contains liveDir) "live locked dir not removed in pass 2"
    assertTrue (rep2.removed.toList.contains oldDir) "expired unlocked dir removed with maxAgeSec = 0"
    assertTrue (rep2.removed.toList.contains freshDir) "freshDir also expired after sleep + maxAgeSec = 0"
    assertTrue (← assertFsOk (← Fs.pathExists liveDir) "pathExists liveDir after pass 2") "liveDir intact after pass 2"
    assertTrue (!(← assertFsOk (← Fs.pathExists oldDir) "pathExists oldDir after pass 2")) "oldDir removed after pass 2"

    assertFsOk (← Fs.writeText liveStop "done") "signal liveChild stop"
    match ← Process.awaitOutput liveChild with
    | .ok (.exited out) => assertTrue (out.exitCode == 0) "liveChild exited cleanly"
    | .ok other => throw (IO.userError s!"liveChild unexpected outcome: {repr other}")
    | .error e => throw (IO.userError s!"awaitOutput liveChild failed: {repr e}")
  finally
    let _ ← Fs.writeText liveStop "done"
    let _ ← Process.reap deadChild
    let _ ← Process.reap liveChild

  assertTrue ((← Process.activeProcessCount) == 0) "all child processes reaped"

private def withTempDirErrSandbox (act : String → IO Unit) : IO Unit := do
  let res ← TempDir.withTempDir none "lean-swe-tempdir-err-" fun sandbox => do
    act sandbox
    return .ok ()
  let _ ← assertTempDirOk res "tempdir err sandbox cleanup"

private def mkCollidingUuid (root : String) (dirPrefix : String) : IO Uuid.Uuid := do
  let u ← match ← Uuid.getUuid with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"Uuid.getUuid failed: {repr e}")
  assertFsOk (← Fs.mkdir (Fs.join root (dirPrefix ++ Uuid.toString u)) false false)
    "precreate colliding temp dir"
  return u

/-- Real error test for `TempDir.withTempDir` returning `.invalidInput`. -/
def err_tempdir_withTempDir_invalidInput : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    assertTempDirErrKind (← TempDir.withTempDir (some sandbox) "" (fun _ => pure (.ok ())))
      .invalidInput "withTempDir invalidInput"

/-- Real error test for `TempDir.withTempDir` returning `.notFound`. -/
def err_tempdir_withTempDir_notFound : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    assertTempDirErrKind (← TempDir.withTempDir (some (Fs.join sandbox "missing")) "p-" (fun _ => pure (.ok ())))
      .notFound "withTempDir notFound"

/-- Mocked error test for `TempDir.withTempDir` returning `.alreadyExists`. -/
def err_tempdir_withTempDir_alreadyExists : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let u ← mkCollidingUuid sandbox "dup-"
    let fixedUuid : Uuid.UuidApi := { Uuid.defaultApi with getUuid := pure (.ok u) }
    let api := TempDir.Internal.mkApiM Fs.defaultApi Time.defaultOps fixedUuid EnvVars.defaultApi
    assertTempDirErrKind (← api.withTempDir (some sandbox) "dup-" (fun _ => pure (.ok ())))
      .alreadyExists "withTempDir alreadyExists"

/-- Real error test for `TempDir.withTempDir` returning `.permissionDenied`. -/
def err_tempdir_withTempDir_permissionDenied : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let roRoot := Fs.join sandbox "ro_root"
    assertFsOk (← Fs.mkdir roRoot false false) "create ro_root"
    assertFsOk (← Fs.chmod roRoot 0o555) "chmod 0o555 ro_root"
    try
      assertTempDirErrKind (← TempDir.withTempDir (some roRoot) "p-" (fun _ => pure (.ok ())))
        .permissionDenied "withTempDir permissionDenied"
    finally
      let _ ← Fs.chmod roRoot 0o755

/-- Real error test for `TempDir.withTempDir` returning `.notADirectory`. -/
def err_tempdir_withTempDir_notADirectory : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let regFile := Fs.join sandbox "reg_file"
    assertFsOk (← Fs.writeText regFile "x") "create reg_file"
    assertTempDirErrKind (← TempDir.withTempDir (some regFile) "p-" (fun _ => pure (.ok ())))
      .notADirectory "withTempDir notADirectory"

/-- Real error test for `TempDir.withTempDir` returning `.ioError`. -/
def err_tempdir_withTempDir_ioError : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let loopPath := Fs.join sandbox "eloop"
    assertFsOk (← Fs.symlink loopPath loopPath) "create ELOOP symlink"
    assertTempDirErrKind (← TempDir.withTempDir (some loopPath) "p-" (fun _ => pure (.ok ())))
      .ioError "withTempDir ioError"

/-- Real error test for `TempDir.withLockedTempDir` returning `.invalidInput`. -/
def err_tempdir_withLockedTempDir_invalidInput : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    assertTempDirErrKind (← TempDir.withLockedTempDir (some sandbox) "" (fun _ => pure (.ok ())))
      .invalidInput "withLockedTempDir invalidInput"

/-- Real error test for `TempDir.withLockedTempDir` returning `.notFound`. -/
def err_tempdir_withLockedTempDir_notFound : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    assertTempDirErrKind
      (← TempDir.withLockedTempDir (some (Fs.join sandbox "missing")) "p-" (fun _ => pure (.ok ())))
      .notFound "withLockedTempDir notFound"

/-- Mocked error test for `TempDir.withLockedTempDir` returning `.alreadyExists`. -/
def err_tempdir_withLockedTempDir_alreadyExists : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let u ← mkCollidingUuid sandbox "dup-"
    let fixedUuid : Uuid.UuidApi := { Uuid.defaultApi with getUuid := pure (.ok u) }
    let api := TempDir.Internal.mkApiM Fs.defaultApi Time.defaultOps fixedUuid EnvVars.defaultApi
    assertTempDirErrKind (← api.withLockedTempDir (some sandbox) "dup-" (fun _ => pure (.ok ())))
      .alreadyExists "withLockedTempDir alreadyExists"

/-- Real error test for `TempDir.withLockedTempDir` returning `.permissionDenied`. -/
def err_tempdir_withLockedTempDir_permissionDenied : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let roRoot := Fs.join sandbox "ro_root"
    assertFsOk (← Fs.mkdir roRoot false false) "create ro_root"
    assertFsOk (← Fs.chmod roRoot 0o555) "chmod 0o555 ro_root"
    try
      assertTempDirErrKind (← TempDir.withLockedTempDir (some roRoot) "p-" (fun _ => pure (.ok ())))
        .permissionDenied "withLockedTempDir permissionDenied"
    finally
      let _ ← Fs.chmod roRoot 0o755

/-- Real error test for `TempDir.withLockedTempDir` returning `.notADirectory`. -/
def err_tempdir_withLockedTempDir_notADirectory : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let regFile := Fs.join sandbox "reg_file"
    assertFsOk (← Fs.writeText regFile "x") "create reg_file"
    assertTempDirErrKind (← TempDir.withLockedTempDir (some regFile) "p-" (fun _ => pure (.ok ())))
      .notADirectory "withLockedTempDir notADirectory"

/-- Real error test for `TempDir.withLockedTempDir` returning `.ioError`. -/
def err_tempdir_withLockedTempDir_ioError : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let loopPath := Fs.join sandbox "eloop"
    assertFsOk (← Fs.symlink loopPath loopPath) "create ELOOP symlink"
    assertTempDirErrKind (← TempDir.withLockedTempDir (some loopPath) "p-" (fun _ => pure (.ok ())))
      .ioError "withLockedTempDir ioError"

/-- Real error test for `TempDir.cleanupStaleTempDirs` returning `.invalidInput`. -/
def err_tempdir_cleanupStaleTempDirs_invalidInput : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    assertTempDirErrKind (← TempDir.cleanupStaleTempDirs (some sandbox) "" 0)
      .invalidInput "cleanupStaleTempDirs invalidInput"

/-- Real error test for `TempDir.cleanupStaleTempDirs` returning `.notFound`. -/
def err_tempdir_cleanupStaleTempDirs_notFound : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    assertTempDirErrKind (← TempDir.cleanupStaleTempDirs (some (Fs.join sandbox "missing")) "p-" 0)
      .notFound "cleanupStaleTempDirs notFound"

/-- Mocked error test for `TempDir.cleanupStaleTempDirs` returning `.alreadyExists`. -/
def err_tempdir_cleanupStaleTempDirs_alreadyExists : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let fs :=
      { Fs.defaultApi with
        listDir := fun _ =>
          pure (.error { kind := .alreadyExists, path := some "/mock", message := "injected alreadyExists" }) }
    let api := TempDir.Internal.mkApiM fs Time.defaultOps Uuid.defaultApi EnvVars.defaultApi
    assertTempDirErrKind (← api.cleanupStaleTempDirs (some sandbox) "p-" 0)
      .alreadyExists "cleanupStaleTempDirs alreadyExists"

/-- Real error test for `TempDir.cleanupStaleTempDirs` returning `.permissionDenied`. -/
def err_tempdir_cleanupStaleTempDirs_permissionDenied : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let noReadRoot := Fs.join sandbox "noread_root"
    assertFsOk (← Fs.mkdir noReadRoot false false) "create noread_root"
    assertFsOk (← Fs.chmod noReadRoot 0o000) "chmod 0o000 noread_root"
    try
      assertTempDirErrKind (← TempDir.cleanupStaleTempDirs (some noReadRoot) "p-" 0)
        .permissionDenied "cleanupStaleTempDirs permissionDenied"
    finally
      let _ ← Fs.chmod noReadRoot 0o755

/-- Real error test for `TempDir.cleanupStaleTempDirs` returning `.notADirectory`. -/
def err_tempdir_cleanupStaleTempDirs_notADirectory : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let regFile := Fs.join sandbox "reg_file"
    assertFsOk (← Fs.writeText regFile "x") "create reg_file"
    assertTempDirErrKind (← TempDir.cleanupStaleTempDirs (some regFile) "p-" 0)
      .notADirectory "cleanupStaleTempDirs notADirectory"

/-- Real error test for `TempDir.cleanupStaleTempDirs` returning `.ioError`. -/
def err_tempdir_cleanupStaleTempDirs_ioError : IO Unit :=
  withTempDirErrSandbox fun sandbox => do
    let loopPath := Fs.join sandbox "eloop"
    assertFsOk (← Fs.symlink loopPath loopPath) "create ELOOP symlink"
    assertTempDirErrKind (← TempDir.cleanupStaleTempDirs (some loopPath) "p-" 0)
      .ioError "cleanupStaleTempDirs ioError"

/-- Registered error-coverage tests for `LeanSwe.TempDir.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_invalidInput"
       mode := .real, run := err_tempdir_withTempDir_invalidInput }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_notFound"
       mode := .real, run := err_tempdir_withTempDir_notFound }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_alreadyExists"
       mode := .mocked, run := err_tempdir_withTempDir_alreadyExists }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_permissionDenied"
       mode := .real, run := err_tempdir_withTempDir_permissionDenied }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_notADirectory"
       mode := .real, run := err_tempdir_withTempDir_notADirectory }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withTempDir_ioError"
       mode := .real, run := err_tempdir_withTempDir_ioError }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_invalidInput"
       mode := .real, run := err_tempdir_withLockedTempDir_invalidInput }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_notFound"
       mode := .real, run := err_tempdir_withLockedTempDir_notFound }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_alreadyExists"
       mode := .mocked, run := err_tempdir_withLockedTempDir_alreadyExists }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_permissionDenied"
       mode := .real, run := err_tempdir_withLockedTempDir_permissionDenied }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_notADirectory"
       mode := .real, run := err_tempdir_withLockedTempDir_notADirectory }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_withLockedTempDir_ioError"
       mode := .real, run := err_tempdir_withLockedTempDir_ioError }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_invalidInput"
       mode := .real, run := err_tempdir_cleanupStaleTempDirs_invalidInput }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_notFound"
       mode := .real, run := err_tempdir_cleanupStaleTempDirs_notFound }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_alreadyExists"
       mode := .mocked, run := err_tempdir_cleanupStaleTempDirs_alreadyExists }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_permissionDenied"
       mode := .real, run := err_tempdir_cleanupStaleTempDirs_permissionDenied }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_notADirectory"
       mode := .real, run := err_tempdir_cleanupStaleTempDirs_notADirectory }
   , { testName := "LeanSwe.TempDir.RuntimeTests.err_tempdir_cleanupStaleTempDirs_ioError"
       mode := .real, run := err_tempdir_cleanupStaleTempDirs_ioError } ]

private def assertTempDirInvalidInput {α : Type} (res : Except TempDirError α)
    (expectedPath : Option String) (expectedMsg? : Option String) (msg : String) : IO Unit := do
  match res with
  | .ok _ =>
    throw (IO.userError s!"ASSERTION FAILED: {msg} (expected TempDirError .invalidInput, got ok)")
  | .error e =>
    let msgOk := match expectedMsg? with
      | some m => e.message == m
      | none => !e.message.isEmpty
    if e.kind != .invalidInput || e.path != expectedPath || !msgOk then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected invalidInput path={repr expectedPath})")

private def testFsInvalidInputPreserved (sandbox : String) : IO Unit := do
  let fsStatInv : Fs.FsApi :=
    { Fs.defaultApi with
      stat := fun p => pure (.error { kind := .invalidInput, path := some p, message := "stat: EINVAL" }) }
  let apiStatInv := TempDir.mkApiM fsStatInv Time.defaultOps Uuid.defaultApi EnvVars.defaultApi
  assertTempDirInvalidInput (← apiStatInv.withTempDir (some sandbox) "p-" fun _ => pure (.ok ()))
    (some sandbox) (some "stat: EINVAL") "withTempDir preserves Fs invalidInput from stat"
  assertTempDirInvalidInput (← apiStatInv.withLockedTempDir (some sandbox) "p-" fun _ => pure (.ok ()))
    (some sandbox) (some "stat: EINVAL") "withLockedTempDir preserves Fs invalidInput from stat"
  assertTempDirInvalidInput (← apiStatInv.cleanupStaleTempDirs (some sandbox) "p-" 0)
    (some sandbox) (some "stat: EINVAL") "cleanupStaleTempDirs preserves Fs invalidInput from stat"

  let fsStatInvEmptyMsg : Fs.FsApi :=
    { Fs.defaultApi with
      stat := fun _ => pure (.error { kind := .invalidInput, path := none, message := "" }) }
  let apiStatInvEmpty := TempDir.mkApiM fsStatInvEmptyMsg Time.defaultOps Uuid.defaultApi EnvVars.defaultApi
  assertTempDirInvalidInput (← apiStatInvEmpty.withTempDir (some sandbox) "p-" fun _ => pure (.ok ()))
    none none "withTempDir preserves Fs invalidInput with non-empty fallback message"
  assertTempDirInvalidInput (← apiStatInvEmpty.withLockedTempDir (some sandbox) "p-" fun _ => pure (.ok ()))
    none none "withLockedTempDir preserves Fs invalidInput with non-empty fallback message"
  assertTempDirInvalidInput (← apiStatInvEmpty.cleanupStaleTempDirs (some sandbox) "p-" 0)
    none none "cleanupStaleTempDirs preserves Fs invalidInput with non-empty fallback message"

  let fixedU ← match ← Uuid.getUuid with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"Uuid.getUuid failed: {repr e}")
  let fixedUuid : Uuid.UuidApi := { Uuid.defaultApi with getUuid := pure (.ok fixedU) }
  let expectedDir := Fs.join sandbox ("inv-" ++ Uuid.toString fixedU)
  let expectedLock := Fs.join expectedDir ".lock"

  let fsMkdirInv : Fs.FsApi :=
    { Fs.defaultApi with
      mkdir := fun p _ _ => pure (.error { kind := .invalidInput, path := some p, message := "mkdir: ENAMETOOLONG" }) }
  let apiMkdirInv := TempDir.mkApiM fsMkdirInv Time.defaultOps fixedUuid EnvVars.defaultApi
  assertTempDirInvalidInput (← apiMkdirInv.withTempDir (some sandbox) "inv-" fun _ => pure (.ok ()))
    (some expectedDir) (some "mkdir: ENAMETOOLONG") "withTempDir preserves Fs invalidInput from mkdir"
  assertTempDirInvalidInput (← apiMkdirInv.withLockedTempDir (some sandbox) "inv-" fun _ => pure (.ok ()))
    (some expectedDir) (some "mkdir: ENAMETOOLONG") "withLockedTempDir preserves Fs invalidInput from mkdir"

  let fsChmodInv : Fs.FsApi :=
    { Fs.defaultApi with
      chmod := fun p _ => pure (.error { kind := .invalidInput, path := some p, message := "chmod: EINVAL" }) }
  let apiChmodInv := TempDir.mkApiM fsChmodInv Time.defaultOps fixedUuid EnvVars.defaultApi
  assertTempDirInvalidInput (← apiChmodInv.withTempDir (some sandbox) "inv-" fun _ => pure (.ok ()))
    (some expectedDir) (some "chmod: EINVAL") "withTempDir preserves Fs invalidInput from chmod"
  assertTrue (!(← assertFsOk (← Fs.pathExists expectedDir) "pathExists after chmod invalidInput"))
    "withTempDir rolled back dir after chmod invalidInput"

  let fsLockInv : Fs.FsApi :=
    { Fs.defaultApi with
      withFileLock := fun p _ _ _ => pure (.error { kind := .invalidInput, path := some p, message := "flock: EINVAL" }) }
  let apiLockInv := TempDir.mkApiM fsLockInv Time.defaultOps fixedUuid EnvVars.defaultApi
  assertTempDirInvalidInput (← apiLockInv.withLockedTempDir (some sandbox) "inv-" fun _ => pure (.ok ()))
    (some expectedLock) (some "flock: EINVAL") "withLockedTempDir preserves Fs invalidInput from withFileLock"
  assertTrue (!(← assertFsOk (← Fs.pathExists expectedDir) "pathExists after lock invalidInput"))
    "withLockedTempDir cleaned up dir after lock invalidInput"

  let fsRmtreeInv : Fs.FsApi :=
    { Fs.defaultApi with
      rmtree := fun p _ => pure (.error { kind := .invalidInput, path := some p, message := "rmtree: EINVAL" }) }
  let apiRmtreeInv := TempDir.mkApiM fsRmtreeInv Time.defaultOps fixedUuid EnvVars.defaultApi
  assertTempDirInvalidInput (← apiRmtreeInv.withTempDir (some sandbox) "inv-" fun _ => pure (.ok ()))
    (some expectedDir) (some "rmtree: EINVAL") "withTempDir preserves Fs invalidInput from rmtree"
  assertFsOk (← Fs.rmtree expectedDir true) "clean up dir left by mocked rmtree invalidInput"

  let fsListDirInv : Fs.FsApi :=
    { Fs.defaultApi with
      listDir := fun p => pure (.error { kind := .invalidInput, path := some p, message := "listDir: EINVAL" }) }
  let apiListDirInv := TempDir.mkApiM fsListDirInv Time.defaultOps Uuid.defaultApi EnvVars.defaultApi
  assertTempDirInvalidInput (← apiListDirInv.cleanupStaleTempDirs (some sandbox) "p-" 0)
    (some sandbox) (some "listDir: EINVAL") "cleanupStaleTempDirs preserves Fs invalidInput from listDir"

  let invSweepRoot := Fs.join sandbox "inv-sweep"
  let invChild := Fs.join invSweepRoot "inv-child"
  assertFsOk (← Fs.mkdir invSweepRoot false false) "create invSweepRoot"
  assertFsOk (← Fs.mkdir invChild false false) "create invChild"
  let fsSweepLstatInv : Fs.FsApi :=
    { Fs.defaultApi with
      lstat := fun p =>
        if p == invChild then
          pure (.error { kind := .invalidInput, path := some p, message := "lstat: EINVAL" })
        else
          Fs.defaultApi.lstat p }
  let apiSweepLstatInv := TempDir.mkApiM fsSweepLstatInv Time.defaultOps Uuid.defaultApi EnvVars.defaultApi
  let invRep ← assertTempDirOk (← apiSweepLstatInv.cleanupStaleTempDirs (some invSweepRoot) "inv-" 0)
    "cleanupStaleTempDirs records child Fs invalidInput into failed"
  assertTrue (invRep.failed == #[{ kind := .invalidInput, path := some invChild, message := "lstat: EINVAL" }])
    "cleanupStaleTempDirs preserves child Fs invalidInput kind, path, and message in report.failed"

  let longSeg := String.ofList (List.replicate 300 'a')
  assertTempDirErrKind (← TempDir.withTempDir (some sandbox) longSeg fun _ => pure (.ok ()))
    .invalidInput "withTempDir maps OS ENAMETOOLONG prefix to invalidInput"
  assertTempDirErrKind (← TempDir.withLockedTempDir (some sandbox) longSeg fun _ => pure (.ok ()))
    .invalidInput "withLockedTempDir maps OS ENAMETOOLONG prefix to invalidInput"
  let longRoot := Fs.join sandbox longSeg
  assertTempDirInvalidInput (← TempDir.withTempDir (some longRoot) "p-" fun _ => pure (.ok ()))
    (some longRoot) none "withTempDir maps OS ENAMETOOLONG root to invalidInput"
  assertTempDirInvalidInput (← TempDir.withLockedTempDir (some longRoot) "p-" fun _ => pure (.ok ()))
    (some longRoot) none "withLockedTempDir maps OS ENAMETOOLONG root to invalidInput"
  assertTempDirInvalidInput (← TempDir.cleanupStaleTempDirs (some longRoot) "p-" 0)
    (some longRoot) none "cleanupStaleTempDirs maps OS ENAMETOOLONG root to invalidInput"

/-- Execute all runtime OS tests for `LeanSwe.TempDir`. -/
def runAll : IO Unit := do
  Core.runRegisteredErrorTests registeredErrorTests
  let res ← TempDir.withTempDir none "lean-swe-tempdir-sandbox-" fun sandbox => do
    testFsInvalidInputPreserved sandbox
    testWithTempDirLifecycle sandbox
    testWithLockedTempDirAndRootResolution sandbox
    testCleanupStaleTempDirsOS sandbox
    return .ok ()
  let _ ← assertTempDirOk res "outer sandbox cleanup"
  IO.println "LEAN_SWE_TEMPDIR_RUNTIME_TESTS_PASSED"

end LeanSwe.TempDir.RuntimeTests
