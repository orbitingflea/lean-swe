import LeanSwe.Fs.Interface
import LeanSwe.Process.Interface
import LeanSwe.Process.SysBridge

namespace LeanSwe.Fs.RuntimeTests

open LeanSwe

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except FsError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertOkEq {α : Type} [BEq α] [Repr α]
    (actual : Except FsError α) (expected : α) (msg : String) : IO Unit := do
  let v ← assertOk actual msg
  if !(v == expected) then
    throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v}, expected {repr expected})")

private def assertOkBytesEq (actual : Except FsError ByteArray) (expected : ByteArray)
    (msg : String) : IO Unit := do
  let v ← assertOk actual msg
  if !(v == expected) then
    throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr v.data}, expected {repr expected.data})")

private def assertErrKind {α : Type} (res : Except FsError α) (expected : FsErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def testPurePaths : IO Unit := do
  assertTrue (Fs.normPath "/a/b/../c/./" == "/a/c") "normPath collapses . and .."
  assertTrue (Fs.normPath "a/../.." == "..") "normPath keeps relative .."
  assertTrue (Fs.normPath "/../../a" == "/a") "normPath clamps .. at root"
  assertTrue (Fs.normPath "" == "." && Fs.normPath "." == ".") "normPath empty/dot"
  assertTrue (Fs.joinMany #["/tmp", "foo/", "bar.tar.gz"] == "/tmp/foo/bar.tar.gz") "joinMany"
  assertTrue (Fs.join "/a/b" "/etc/hosts" == "/etc/hosts") "join absolute overrides"
  assertTrue (Fs.parent "/a/b/c" == some "/a/b") "parent"
  assertTrue (Fs.parent "/a" == some "/") "parent of top child"
  assertTrue (Fs.parent "/" == none) "parent of root"
  assertTrue (Fs.name "a/b/" == some "b") "name trailing slash"
  assertTrue (Fs.stem "a/b.tar.gz" == some "b.tar") "stem multi suffix"
  assertTrue (Fs.suffix "a/b.tar.gz" == ".gz") "suffix"
  assertTrue (Fs.suffixes "a/b.tar.gz" == #[".tar", ".gz"]) "suffixes"
  assertTrue (Fs.suffixes "a..b" == #[".", ".b"]) "suffixes double dot"
  assertTrue (Fs.suffixes "a." == #[]) "suffixes trailing dot"
  assertTrue (Fs.suffix ".gitignore" == "") "dotfile suffix empty"
  assertOkEq (Fs.withName "a/b.txt" "c.lean") "a/c.lean" "withName"
  assertOkEq (Fs.withSuffix "a/b.txt" ".lean") "a/b.lean" "withSuffix"
  assertOkEq (Fs.withSuffix "a/b.txt" "") "a/b" "withSuffix strip"
  assertErrKind (Fs.withName "/" "x") .invalidInput "withName root fails"
  assertErrKind (Fs.withSuffix "a/b.txt" "lean") .invalidInput "withSuffix missing dot fails"
  assertOkEq (Fs.relativeTo "/a/b/c/d.lean" "/a/b") "c/d.lean" "relativeTo subpath"
  assertErrKind (Fs.relativeTo "/x/y" "/a/b") .invalidInput "relativeTo outside fails"

private def testFilesAndDirs (tmp : String) : IO (Except FsError String) := do
  let f1 := Fs.join tmp "hello.txt"
  assertOk (← Fs.writeText f1 "hello") "writeText"
  assertOkEq (← Fs.readText f1) "hello" "readText"
  assertOk (← Fs.appendText f1 " world") "appendText"
  assertOkEq (← Fs.readText f1) "hello world" "appendText readText"
  assertOk (← Fs.atomicWriteText f1 "atomic") "atomicWriteText"
  assertOkEq (← Fs.readText f1) "atomic" "atomicWriteText readText"

  let binPath := Fs.join tmp "bytes.bin"
  let payload := ByteArray.mk #[1, 2, 3, 255]
  assertOk (← Fs.writeBytes binPath payload) "writeBytes"
  let gotBytes ← assertOk (← Fs.readBytes binPath) "readBytes"
  assertTrue (gotBytes == payload) "readBytes roundtrip"

  let touched := Fs.join tmp "touched.txt"
  assertOk (← Fs.touch touched) "touch creates missing file"
  assertErrKind (← Fs.touch touched false) .alreadyExists "touch existOk=false fails"

  let nestedDir := Fs.joinMany #[tmp, "sub", "deep"]
  assertErrKind (← Fs.mkdir nestedDir false false) .notFound "mkdir parents=false fails"
  assertOk (← Fs.mkdir nestedDir true false) "mkdir parents=true succeeds"
  assertErrKind (← Fs.mkdir nestedDir true false) .alreadyExists "mkdir parents=true existOk=false fails on existing"
  assertOk (← Fs.mkdir nestedDir false true) "mkdir existOk=true succeeds"
  assertErrKind (← Fs.mkdir nestedDir false false) .alreadyExists "mkdir existOk=false fails"
  assertOk (← Fs.writeText (Fs.join nestedDir "x.lean") "def x := 1\n") "write nested file"
  assertErrKind (← Fs.rmdir nestedDir) .notEmpty "rmdir non-empty fails"

  assertOkEq (← Fs.listDir tmp) #["bytes.bin", "hello.txt", "sub", "touched.txt"] "listDir sorted"
  assertOkEq (← Fs.glob tmp "**/*.lean") #["sub/deep/x.lean"] "glob **/*.lean"
  assertOkEq (← Fs.rglob tmp "*.lean") #["sub/deep/x.lean"] "rglob *.lean"
  let walked ← assertOk (← Fs.walk tmp) "walk"
  assertTrue (walked.size == 3) s!"expected 3 walk entries, got {walked.size}"

  let copied := Fs.join tmp "hello_copy.txt"
  assertOk (← Fs.copyFile f1 copied) "copyFile"
  assertOkEq (← Fs.readText copied) "atomic" "copyFile content"
  let moved := Fs.join tmp "moved.txt"
  assertOk (← Fs.rename copied moved) "rename"
  assertOkEq (← Fs.pathExists copied) false "renamed source gone"
  assertOkEq (← Fs.readText moved) "atomic" "renamed target readable"
  return .ok moved

private def testSymlinksAndGlobs (tmp moved : String) : IO (Except FsError Unit) := do
  let copyDir := Fs.join tmp "sub_copy"
  let nestedDir := Fs.joinMany #[tmp, "sub", "deep"]
  assertOk (← Fs.copyTree (Fs.join tmp "sub") copyDir) "copyTree"
  assertOkEq (← Fs.readText (Fs.joinMany #[copyDir, "deep", "x.lean"]))
    "def x := 1\n" "copyTree content"
  let nestedCopyDir := Fs.joinMany #[tmp, "new_parent", "sub_copy"]
  assertOk (← Fs.copyTree (Fs.join tmp "sub") nestedCopyDir) "copyTree creates missing parent dir"
  assertOkEq (← Fs.readText (Fs.joinMany #[nestedCopyDir, "deep", "x.lean"]))
    "def x := 1\n" "copyTree missing-parent content"
  assertOk (← Fs.rmtree (Fs.join tmp "new_parent")) "cleanup new_parent"

  assertOk (← Fs.chmod moved 0o750) "chmod 0o750"
  let st ← assertOk (← Fs.stat moved) "stat moved"
  assertTrue (st.kind == .file && st.byteSize == 6 && (st.mode % 512) == 0o750)
    s!"unexpected stat after chmod: {repr st}"

  let sym := Fs.join tmp "link_to_moved"
  assertOk (← Fs.symlink moved sym) "symlink"
  assertOkEq (← Fs.isSymlink sym) true "isSymlink"
  assertOkEq (← Fs.readLink sym) moved "readLink"
  assertOkEq (← Fs.readText sym) "atomic" "read through symlink"
  let symLstat ← assertOk (← Fs.lstat sym) "lstat symlink"
  assertTrue (symLstat.kind == .symlink) "lstat reports symlink"

  let dirLoop := Fs.join tmp "loop_to_tmp"
  assertOk (← Fs.symlink tmp dirLoop) "symlink to dir (cycle test)"
  let _ ← assertOk (← Fs.walk tmp) "walk safely skips symlink directory cycle"

  let loopSrc := Fs.join tmp "loop_src"
  assertOk (← Fs.mkdir loopSrc false false) "mkdir loop_src"
  assertOk (← Fs.symlink loopSrc (Fs.join loopSrc "self")) "symlink self inside loop_src"
  assertErrKind (← Fs.copyTree loopSrc (Fs.join tmp "loop_dst")) .invalidInput "copyTree rejects symlink cycle"
  assertErrKind (← Fs.copyTree loopSrc (Fs.join loopSrc "nested_dst")) .invalidInput "copyTree rejects dst inside src"
  assertOk (← Fs.rmtree (Fs.join tmp "loop_dst") true) "cleanup loop_dst"
  assertOk (← Fs.rmtree loopSrc false) "cleanup loop_src"

  let dangling := Fs.join tmp "dangling_link"
  assertOk (← Fs.symlink (Fs.join tmp "does_not_exist") dangling) "dangling symlink"
  assertOkEq (← Fs.pathExists dangling) false "dangling symlink exists=false"
  assertOkEq (← Fs.isSymlink dangling) true "dangling symlink isSymlink=true"
  assertErrKind (← Fs.stat dangling) .notFound "stat on dangling symlink fails"
  assertErrKind (← Fs.touch dangling false) .alreadyExists "touch existOk=false fails on broken symlink"

  let cwdPath ← assertOk (← Fs.cwd) "cwd"
  assertTrue (Fs.isAbsolute cwdPath) "cwd is absolute"
  let resPath ← assertOk (← Fs.resolve tmp) "resolve tmp"
  assertTrue (Fs.isAbsolute resPath) "resolve returns absolute path"

  assertOk (← Fs.unlink sym) "unlink symlink"
  assertOk (← Fs.unlink sym true) "unlink missingOk=true succeeds"
  assertErrKind (← Fs.unlink sym false) .notFound "unlink missingOk=false fails"
  assertErrKind (← Fs.unlink nestedDir false) .isADirectory "unlink dir fails"
  assertOk (← Fs.rmtree copyDir) "rmtree"
  assertOkEq (← Fs.pathExists copyDir) false "rmtree removes dir"
  assertOk (← Fs.rmtree copyDir true) "rmtree ignoreMissing=true"
  assertErrKind (← Fs.readText (Fs.join tmp "missing.txt")) .notFound "readText missing"
  assertErrKind (← Fs.readText nestedDir) .isADirectory "readText dir"
  assertErrKind (← Fs.listDir moved) .notADirectory "listDir file"
  assertErrKind (← Fs.walk (Fs.join tmp "missing_dir")) .notFound "walk missing dir"
  assertErrKind (← Fs.walk moved) .notADirectory "walk file"
  assertErrKind (← Fs.glob tmp "[unclosed") .invalidInput "glob invalid pattern"
  return .ok ()

private def waitForFile (path : String) (maxPolls : Nat := 200) : IO Unit := do
  for _ in List.range maxPolls do
    match ← Fs.pathExists path with
    | .ok true => return ()
    | _ => IO.sleep 10
  throw (IO.userError s!"ASSERTION FAILED: timed out waiting for readiness file {path}")

private def testLocksSingleProcess (tmp : String) : IO Unit := do
  let lockPath := Fs.join tmp "bracket.lock"
  let val ← assertOk (← Fs.withFileLock lockPath .exclusive true (pure (.ok 123)))
    "withFileLock ok"
  assertTrue (val == 123) "withFileLock ok value"
  assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok 1))) (some 1)
    "lock released after withFileLock ok"

  let actionErr : FsError := { kind := .permissionDenied, message := "action failed" }
  assertErrKind (← Fs.withFileLock lockPath .shared false (pure (Except.error actionErr : Except FsError Unit)))
    .permissionDenied "withFileLock propagates action error"
  assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok 2))) (some 2)
    "lock released after withFileLock action error"

  let mut threw := false
  try
    let _ ← Fs.withFileLock lockPath .exclusive false
      (throw (IO.userError "boom") : IO (Except FsError Unit))
  catch _ =>
    threw := true
  assertTrue threw "withFileLock rethrows IO error"
  assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok 3))) (some 3)
    "lock released even after IO exception"

  let nestedShared ← assertOk (← Fs.withFileLock lockPath .shared false
    (Fs.tryWithFileLock lockPath .shared false (pure (.ok "ok")))) "nested shared tryWithFileLock"
  assertTrue (nestedShared == some "ok") "nested shared succeeds"

  let marker := Fs.join tmp "conflict_marker.txt"
  let nestedEx ← assertOk (← Fs.withFileLock lockPath .shared false
    (Fs.tryWithFileLock lockPath .exclusive false (Fs.writeText marker "ran")))
    "conflicting exclusive inside shared"
  assertTrue (nestedEx == none) "conflicting tryWithFileLock returns none"
  assertOkEq (← Fs.pathExists marker) false "conflicting action did not execute"

  let missingPath := Fs.join tmp "never_created.lock"
  assertErrKind (← Fs.tryWithFileLock missingPath .exclusive false (pure (.ok 1))) .notFound
    "tryWithFileLock missing with createIfMissing=false fails with notFound"
  assertOkEq (← Fs.pathExists missingPath) false "missing lockfile not created"

  let tryActionErr ← Fs.tryWithFileLock lockPath .exclusive false
    (pure (Except.error actionErr : Except FsError Nat))
  assertErrKind tryActionErr .permissionDenied "tryWithFileLock propagates action error"
  assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok 4))) (some 4)
    "lock released after tryWithFileLock action error"

private def testLocksMultiProcess (tmp : String) : IO Unit := do
  assertTrue ((← Process.activeProcessCount) == 0) "initial activeProcessCount == 0"
  let lockPath := Fs.join tmp "mp.lock"
  assertOk (← Fs.writeText lockPath "init") "writeText mp.lock"

  let ready1 := Fs.join tmp "mp1.ready"
  let stop1 := Fs.join tmp "mp1.stop"
  let holdScript :=
    "import fcntl, os, sys, time\n" ++
    "lp, rp, sp, mode = sys.argv[1:5]\n" ++
    "fd = os.open(lp, os.O_RDONLY)\n" ++
    "fcntl.flock(fd, fcntl.LOCK_SH if mode == 'sh' else fcntl.LOCK_EX)\n" ++
    "open(rp, 'w').write('1')\n" ++
    "deadline = time.monotonic() + 5.0\n" ++
    "while not os.path.exists(sp) and time.monotonic() < deadline:\n" ++
    "  time.sleep(0.01)\n"
  let child1 ← match ← Process.SysBridge.spawn
      { program := "python3", args := #["-c", holdScript, lockPath, ready1, stop1, "ex"] } with
    | .ok h => pure h
    | .error e => throw (IO.userError s!"spawn child1 failed: {repr e}")
  try
    waitForFile ready1
    let probeMarker := Fs.join tmp "probe_skipped.txt"
    assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (Fs.writeText probeMarker "ran"))
      none "tryWithFileLock exclusive blocked by child exclusive lock"
    assertOkEq (← Fs.pathExists probeMarker) false "blocked probe did not run action"
    assertOkEq (← Fs.tryWithFileLock lockPath .shared false (pure (.ok 1)))
      none "tryWithFileLock shared blocked by child exclusive lock"

    assertOk (← Fs.writeText stop1 "go") "signal child1 to release and exit"
    let got ← assertOk (← Fs.withFileLock lockPath .exclusive false (pure (.ok "acquired")))
      "blocking withFileLock acquires once child1 exits"
    assertTrue (got == "acquired") "blocking withFileLock result"
    match ← Process.SysBridge.awaitOutput child1 with
    | .ok (.exited out) => assertTrue (out.exitCode == 0) "child1 exited 0"
    | .ok other => throw (IO.userError s!"child1 unexpected outcome: {repr other}")
    | .error e => throw (IO.userError s!"awaitOutput child1 failed: {repr e}")
  finally
    let _ ← Process.SysBridge.reap child1

  let ready2 := Fs.join tmp "mp2.ready"
  let stop2 := Fs.join tmp "mp2.stop"
  let child2 ← match ← Process.SysBridge.spawn
      { program := "python3", args := #["-c", holdScript, lockPath, ready2, stop2, "sh"] } with
    | .ok h => pure h
    | .error e => throw (IO.userError s!"spawn child2 failed: {repr e}")
  try
    waitForFile ready2
    assertOkEq (← Fs.tryWithFileLock lockPath .shared false (pure (.ok 77))) (some 77)
      "multi-process shared coexistence succeeds"
    assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok 1))) none
      "multi-process shared blocks exclusive"
    assertOk (← Fs.writeText stop2 "go") "signal child2 exit"
    match ← Process.SysBridge.awaitOutput child2 with
    | .ok (.exited out) => assertTrue (out.exitCode == 0) "child2 exited 0"
    | .ok other => throw (IO.userError s!"child2 unexpected outcome: {repr other}")
    | .error e => throw (IO.userError s!"awaitOutput child2 failed: {repr e}")
  finally
    let _ ← Process.SysBridge.reap child2

  let ready3 := Fs.join tmp "mp3.ready"
  let killScript :=
    "import fcntl, os, signal, sys, time\n" ++
    "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n" ++
    "lp, rp = sys.argv[1:3]\n" ++
    "fd = os.open(lp, os.O_RDONLY)\n" ++
    "fcntl.flock(fd, fcntl.LOCK_EX)\n" ++
    "open(rp, 'w').write('1')\n" ++
    "time.sleep(10.0)\n"
  let child3 ← match ← Process.SysBridge.spawn
      { program := "python3", args := #["-c", killScript, lockPath, ready3] } with
    | .ok h => pure h
    | .error e => throw (IO.userError s!"spawn child3 failed: {repr e}")
  try
    waitForFile ready3
    assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok 1))) none
      "child3 holds exclusive lock before SIGKILL"
    match ← Process.runCommand "kill" #["-9", toString child3.pid] with
    | .ok kout => assertTrue (kout.exitCode == 0) "kill -9 child3 exitCode 0"
    | .error e => throw (IO.userError s!"kill -9 child3 failed: {repr e}")
  finally
    let _ ← Process.SysBridge.reap child3

  assertOkEq (← Fs.tryWithFileLock lockPath .exclusive false (pure (.ok "unlocked"))) (some "unlocked")
    "OS kernel immediately releases flock on child SIGKILL"
  assertTrue ((← Process.activeProcessCount) == 0) "final activeProcessCount == 0"

private def testAmbientSafety (tmp : String) : IO Unit := do
  let workDir := Fs.join tmp "ambient_work"
  assertOk (← Fs.mkdir workDir false false) "mkdir ambient_work"

  let binTarget := Fs.join workDir "payload.bin"
  let binBytes := ByteArray.mk #[0, 42, 127, 255, 10]
  assertOk (← Fs.atomicWriteBytes binTarget binBytes) "atomicWriteBytes creates new file"
  assertOkBytesEq (← Fs.readBytes binTarget) binBytes "atomicWriteBytes exact bytes"
  assertOkEq (← Fs.listDir workDir) #["payload.bin"] "atomicWriteBytes leaves no tmp sibling"

  let updatedBytes := ByteArray.mk #[9, 8, 7, 6]
  assertOk (← Fs.atomicWriteBytes binTarget updatedBytes) "atomicWriteBytes overwrites file"
  assertOkBytesEq (← Fs.readBytes binTarget) updatedBytes "atomicWriteBytes updated bytes"

  let symVictim := Fs.join workDir "sym_victim.bin"
  assertOk (← Fs.atomicWriteBytes symVictim binBytes) "atomicWriteBytes victim"
  let symReplace := Fs.join workDir "sym_replace.bin"
  assertOk (← Fs.symlink symVictim symReplace) "symlink to victim"
  assertOk (← Fs.atomicWriteBytes symReplace updatedBytes) "atomicWriteBytes replaces symlink"
  assertOkEq (← Fs.isSymlink symReplace) false "replaced symlink is now regular file"
  assertOkBytesEq (← Fs.readBytes symReplace) updatedBytes "replaced symlink has new bytes"
  assertOkBytesEq (← Fs.readBytes symVictim) binBytes "replaced symlink target untouched"

  let symRead := Fs.join workDir "sym_read.bin"
  assertOk (← Fs.symlink binTarget symRead) "symlink for readBytes roundtrip"
  assertOkBytesEq (← Fs.readBytes symRead) updatedBytes "Fs.readBytes symlink exact bytes"

  let nulStr := String.ofList ['x', Char.ofNat 0, 'y']
  for badPath in #["", Fs.join workDir nulStr, workDir ++ "/", ".", "..", Fs.join workDir ".", Fs.join workDir ".."] do
    assertErrKind (← Fs.atomicWriteBytes badPath binBytes) .invalidInput
      s!"atomicWriteBytes invalid path rejected: {repr badPath}"
    assertErrKind (← Fs.atomicWriteText badPath "bad") .invalidInput
      s!"atomicWriteText invalid path rejected: {repr badPath}"

  assertErrKind (← Fs.atomicWriteBytes "/" binBytes) .isADirectory "atomicWriteBytes / rejected"
  assertErrKind (← Fs.atomicWriteText "/" "bad") .isADirectory "atomicWriteText / rejected"
  assertErrKind (← Fs.atomicWriteBytes workDir binBytes) .isADirectory "atomicWriteBytes dir rejected"
  assertErrKind (← Fs.atomicWriteText workDir "bad") .isADirectory "atomicWriteText dir rejected"

  assertErrKind (← Fs.readBytes "") .invalidInput "Fs.readBytes empty rejected"
  assertErrKind (← Fs.readBytes (Fs.join workDir nulStr)) .invalidInput "Fs.readBytes NUL rejected"
  assertErrKind (← Fs.readBytes (workDir ++ "/")) .invalidInput "Fs.readBytes trailing slash rejected"
  assertErrKind (← Fs.readBytes workDir) .isADirectory "Fs.readBytes dir rejected"

  let fifoPath := Fs.join workDir "fs.fifo"
  match ← Process.runCommand "mkfifo" #[fifoPath] with
  | .ok out => assertTrue (out.exitCode == 0) "mkfifo exitCode 0"
  | .error e => throw (IO.userError s!"mkfifo failed: {repr e}")
  assertErrKind (← Fs.readBytes fifoPath) .invalidInput "Fs.readBytes FIFO rejected immediately"
  assertErrKind (← Fs.readText fifoPath) .invalidInput "Fs.readText FIFO rejected immediately"

  let sockPath := Fs.join workDir "fs.sock"
  let readyPath := Fs.join workDir "fs_sock.ready"
  let stopPath := Fs.join workDir "fs_sock.stop"
  let sockScript :=
    "import os, socket, sys, time\n" ++
    "wd = sys.argv[1]\n" ++
    "os.chdir(wd)\n" ++
    "s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)\n" ++
    "s.bind('fs.sock')\n" ++
    "s.listen(1)\n" ++
    "open('fs_sock.ready', 'w').write('1')\n" ++
    "deadline = time.monotonic() + 5.0\n" ++
    "while not os.path.exists('fs_sock.stop') and time.monotonic() < deadline:\n" ++
    "  time.sleep(0.01)\n" ++
    "s.close()\n"
  let sockChild ← match ← Process.SysBridge.spawn { program := "python3", args := #["-c", sockScript, workDir] } with
    | .ok h => pure h
    | .error e => throw (IO.userError s!"spawn sockChild failed: {repr e}")
  try
    waitForFile readyPath
    assertErrKind (← Fs.readBytes sockPath) .invalidInput "Fs.readBytes Unix socket rejected"
    assertErrKind (← Fs.readText sockPath) .invalidInput "Fs.readText Unix socket rejected"
    assertOk (← Fs.writeText stopPath "go") "stop sockChild"
    match ← Process.SysBridge.awaitOutput sockChild with
    | .ok (.exited out) => assertTrue (out.exitCode == 0) "sockChild exited 0"
    | .ok other => throw (IO.userError s!"sockChild unexpected outcome: {repr other}")
    | .error e => throw (IO.userError s!"awaitOutput sockChild failed: {repr e}")
  finally
    let _ ← Process.SysBridge.reap sockChild
    let _ ← Fs.unlink sockPath true
    let _ ← Fs.unlink readyPath true
    let _ ← Fs.unlink stopPath true

  let detApi := Fs.Internal.mkApiM { Raw.defaultOps with monotonicNonce := pure 777 }
  let prePlanted := Fs.join workDir ".payload.bin.tmp.777"
  assertOk (← Fs.symlink symVictim prePlanted) "pre-plant tmp symlink"
  assertErrKind (← detApi.atomicWriteBytes binTarget (ByteArray.mk #[1, 2])) .alreadyExists
    "atomicWriteBytes rejects pre-planted tmp symlink"
  assertErrKind (← detApi.atomicWriteText binTarget "overwrite") .alreadyExists
    "atomicWriteText rejects pre-planted tmp symlink"
  assertOkBytesEq (← Fs.readBytes binTarget) updatedBytes "target preserved after pre-planted tmp rejection"
  assertOkBytesEq (← Fs.readBytes symVictim) binBytes "victim preserved after pre-planted tmp rejection"
  assertOkEq (← Fs.isSymlink prePlanted) true "pre-planted tmp symlink preserved"
  assertOk (← Fs.unlink prePlanted) "unlink prePlanted"

  let failRenameApi := Fs.Internal.mkApiM
    { Raw.defaultOps with
      monotonicNonce := pure 888
      rename := fun _ _ => pure (.error { kind := .permissionDenied, message := "injected rename error" }) }
  let expectedTmp := Fs.join workDir ".payload.bin.tmp.888"
  assertErrKind (← failRenameApi.atomicWriteBytes binTarget (ByteArray.mk #[3, 4])) .permissionDenied
    "atomicWriteBytes propagates rename error"
  assertOkEq (← Fs.pathExists expectedTmp) false "tmp cleaned up after rename failure"
  assertOkBytesEq (← Fs.readBytes binTarget) updatedBytes "target preserved after rename failure"

  assertOk (← Fs.rmtree workDir) "cleanup ambient_work"

private def testWithSubtreeExtra (root : String) : IO Unit := do
  let payload := ByteArray.mk #[1, 2, 3, 4]
  let rExtra ← Fs.withSubtree root fun sub => do
    let rUnlinkMissPre ← assertOk (Raw.RelPath.parse "no_such_dir/no_such_file") "parse no_such_dir/no_such_file"
    assertOk (← sub.unlink rUnlinkMissPre true) "unlink missing intermediate missingOk=true"
    assertErrKind (← sub.unlink rUnlinkMissPre false) .notFound "unlink missing intermediate missingOk=false"

    let rRoSub ← assertOk (Raw.RelPath.parse "ro_sub") "parse ro_sub"
    let rRoInner ← assertOk (Raw.RelPath.parse "ro_sub/entry.txt") "parse ro_sub/entry.txt"
    assertOk (← sub.mkdir rRoSub false false) "mkdir ro_sub"
    assertOk (← sub.atomicWriteBytes rRoInner payload) "write ro_sub/entry.txt"
    assertOk (← Raw.chmod (Fs.join root "ro_sub") 0o400) "chmod 0400 ro_sub"
    let roListed1 ← assertOk (← sub.listDir rRoSub) "listDir 0400 ro_sub"
    let roListed2 ← assertOk (← sub.listDir rRoSub) "listDir 0400 ro_sub twice"
    assertTrue (roListed1.map (·.val) == #["entry.txt"] && roListed2.map (·.val) == #["entry.txt"])
      "listDir succeeds on 0400 subdirectory"
    assertOk (← Raw.chmod (Fs.join root "ro_sub") 0o755) "restore chmod 0755 ro_sub"
    assertOk (← sub.rmtree rRoSub false) "cleanup ro_sub"
    return .ok ()
  assertOk rExtra "withSubtree extra checks"

private def testWithSubtree (tmp : String) : IO Unit := do
  let root := Fs.join tmp "subroot"
  assertOk (← Fs.mkdir root false false) "mkdir subroot"

  let ranRef ← IO.mkRef false
  assertErrKind (← Fs.withSubtree (Fs.join tmp "no_such_root") fun _ => do
    ranRef.set true
    return .ok ()) .notFound "withSubtree missing root"
  assertTrue (!(← ranRef.get)) "missing root never runs action"

  let fileRoot := Fs.join tmp "file_root"
  assertOk (← Fs.writeText fileRoot "hi") "create file_root"
  assertErrKind (← Fs.withSubtree fileRoot fun _ => do
    ranRef.set true
    return .ok ()) .notADirectory "withSubtree file root"
  assertTrue (!(← ranRef.get)) "file root never runs action"
  assertOk (← Fs.unlink fileRoot) "unlink file_root"

  let noExecDir := Fs.join tmp "no_exec_root"
  assertOk (← Fs.mkdir noExecDir false false) "mkdir no_exec_root"
  assertOk (← Raw.chmod noExecDir 0o400) "chmod 0400 no_exec_root"
  assertErrKind (← Fs.withSubtree noExecDir fun _ => do
    ranRef.set true
    return .ok ()) .permissionDenied "withSubtree refuses directory lacking owner search bit"
  assertTrue (!(← ranRef.get)) "0400 root never runs action"
  assertOk (← Raw.chmod noExecDir 0o755) "restore chmod 0755 no_exec_root"
  assertOk (← Fs.rmdir noExecDir) "rmdir no_exec_root"

  let escaped ← try
    let _ : Except FsError Unit ← Fs.withSubtree root fun _ => throw (IO.userError "boom")
    pure false
  catch _ =>
    pure true
  assertTrue escaped "withSubtree propagates IO exception after closing handle"

  let uidOut ← IO.Process.output { cmd := "id", args := #["-u"] }
  let isNonRoot : Bool := uidOut.exitCode == 0 && uidOut.stdout.trimAscii.toString != "0"

  let pOutside := Fs.join tmp "outside.bin"
  let outsideBytes := ByteArray.mk #[42, 43, 44]
  assertOk (← Fs.writeBytes pOutside outsideBytes) "write outside.bin"

  let rUnit ← Fs.withSubtree root fun sub => do
    let rootStat ← assertOk (← sub.lstat Raw.RelPath.root) "sub.lstat .root"
    assertTrue (rootStat.kind == .dir) "rootStat kind == .dir"
    assertOk (← sub.mkdir Raw.RelPath.root false true) "mkdir .root existOk=true"
    assertErrKind (← sub.mkdir Raw.RelPath.root false false) .alreadyExists "mkdir .root existOk=false"
    assertErrKind (← sub.readRegular Raw.RelPath.root) .isADirectory "readRegular .root"
    let payload := ByteArray.mk #[1, 2, 3, 4]
    assertErrKind (← sub.atomicWriteBytes Raw.RelPath.root payload) .invalidInput "atomicWriteBytes .root"
    assertErrKind (← sub.unlink Raw.RelPath.root true) .invalidInput "unlink .root"
    assertErrKind (← sub.rmdir Raw.RelPath.root) .invalidInput "rmdir .root"
    assertErrKind (← sub.rmtree Raw.RelPath.root true) .invalidInput "rmtree .root"
    assertErrKind (← sub.symlink "x" Raw.RelPath.root) .invalidInput "symlink .root"
    assertErrKind (← sub.withFileLock Raw.RelPath.root .exclusive true (pure (.ok ()))) .invalidInput
      "withFileLock .root"
    assertErrKind (← sub.tryWithFileLock Raw.RelPath.root .exclusive true (pure (.ok ()))) .invalidInput
      "tryWithFileLock .root"

    let rNested ← assertOk (Raw.RelPath.parse "a/b/c") "parse a/b/c"
    let rParentA ← assertOk (Raw.RelPath.parse "a") "parse a"
    let rParentB ← assertOk (Raw.RelPath.parse "a/b") "parse a/b"
    assertErrKind (← sub.mkdir rNested false false) .notFound "mkdir parents=false missing intermediate"
    assertOk (← sub.mkdir rNested true false) "mkdir parents=true nested"
    assertOk (← sub.mkdir rNested false true) "mkdir existOk=true existing dir"
    assertErrKind (← sub.mkdir rNested false false) .alreadyExists "mkdir existOk=false existing dir"

    let rData ← assertOk (Raw.RelPath.parse "a/b/c/data.bin") "parse data.bin"
    assertOk (← sub.atomicWriteBytes rData payload) "atomicWriteBytes nested"
    let got ← assertOk (← sub.readRegular rData) "readRegular nested"
    assertTrue (got == payload) "readRegular roundtrip"
    let stData ← assertOk (← sub.lstat rData) "lstat data.bin"
    assertTrue (stData.kind == .file && stData.byteSize == payload.size) "lstat data.bin metadata"
    assertErrKind (← sub.mkdir rData false true) .alreadyExists "mkdir existOk=true rejects existing regular file"

    let max255Rel ← assertOk (Raw.RelPath.parse ("a/" ++ String.ofList (List.replicate 255 'z'))) "parse 255 leaf"
    assertOk (← sub.atomicWriteBytes max255Rel payload) "atomicWriteBytes 255-byte leaf"
    assertTrue ((← assertOk (← sub.readRegular max255Rel) "readRegular 255 leaf") == payload) "readRegular 255"
    assertOk (← sub.unlink max255Rel false) "unlink 255 leaf"

    let rSymLeaf ← assertOk (Raw.RelPath.parse "sym_leaf") "parse sym_leaf"
    assertOk (← sub.symlink pOutside rSymLeaf) "symlink sym_leaf"
    let stSym ← assertOk (← sub.lstat rSymLeaf) "lstat sym_leaf"
    assertTrue (stSym.kind == .symlink) "sym_leaf is symlink"
    assertErrKind (← sub.readRegular rSymLeaf) .invalidInput "readRegular leaf symlink"
    assertErrKind (← sub.listDir rSymLeaf) .invalidInput "listDir leaf symlink"
    assertErrKind (← sub.walk rSymLeaf) .invalidInput "walk leaf symlink"
    assertErrKind (← sub.withFileLock rSymLeaf .exclusive false (pure (.ok ()))) .invalidInput "withFileLock leaf symlink"
    assertErrKind (← sub.tryWithFileLock rSymLeaf .exclusive false (pure (.ok ()))) .invalidInput
      "tryWithFileLock leaf symlink"
    assertErrKind (← sub.mkdir rSymLeaf false true) .alreadyExists "mkdir leaf symlink"
    assertErrKind (← sub.symlink "z" rSymLeaf) .alreadyExists "symlink leaf symlink"
    assertErrKind (← sub.rmdir rSymLeaf) .notADirectory "rmdir leaf symlink"
    assertErrKind (← sub.rmtree rSymLeaf true) .notADirectory "rmtree leaf symlink"
    let newBytes := ByteArray.mk #[9, 9, 9]
    assertOk (← sub.atomicWriteBytes rSymLeaf newBytes) "atomicWriteBytes replaces leaf symlink"
    assertTrue ((← assertOk (← sub.lstat rSymLeaf) "lstat replaced symlink").kind == .file)
      "replaced leaf symlink is regular file"
    assertTrue ((← assertOk (← sub.readRegular rSymLeaf) "read replaced").data == newBytes.data)
      "replaced leaf symlink content"
    assertOkBytesEq (← Fs.readBytes pOutside) outsideBytes "outside symlink target preserved after replacement"

    let rSymDir ← assertOk (Raw.RelPath.parse "sym_dir") "parse sym_dir"
    let rSymDirSub ← assertOk (Raw.RelPath.parse "sym_dir/sub") "parse sym_dir/sub"
    assertOk (← sub.symlink "a" rSymDir) "symlink sym_dir -> a"
    assertErrKind (← sub.lstat rSymDirSub) .invalidInput "lstat refuses ancestor symlink"
    assertErrKind (← sub.readRegular rSymDirSub) .invalidInput "readRegular refuses ancestor symlink"
    assertErrKind (← sub.atomicWriteBytes rSymDirSub payload) .invalidInput "atomicWriteBytes refuses ancestor symlink"
    assertErrKind (← sub.mkdir rSymDirSub true true) .invalidInput "mkdir refuses ancestor symlink"
    assertErrKind (← sub.unlink rSymDirSub true) .invalidInput "unlink refuses ancestor symlink"
    assertErrKind (← sub.rmdir rSymDirSub) .invalidInput "rmdir refuses ancestor symlink"
    assertErrKind (← sub.rmtree rSymDirSub true) .invalidInput "rmtree refuses ancestor symlink"
    assertErrKind (← sub.symlink "q" rSymDirSub) .invalidInput "symlink refuses ancestor symlink"
    assertErrKind (← sub.listDir rSymDirSub) .invalidInput "listDir refuses ancestor symlink"
    assertErrKind (← sub.walk rSymDirSub) .invalidInput "walk refuses ancestor symlink"
    assertErrKind (← sub.withFileLock rSymDirSub .exclusive true (pure (.ok ()))) .invalidInput
      "withFileLock refuses ancestor symlink"
    assertErrKind (← sub.tryWithFileLock rSymDirSub .exclusive true (pure (.ok ()))) .invalidInput
      "tryWithFileLock refuses ancestor symlink"
    assertErrKind (← sub.lstat (← assertOk (Raw.RelPath.parse "a/b/sub_missing") "parse")) .notFound
      "a/b untouched"

    let listedRoot ← assertOk (← sub.listDir Raw.RelPath.root) "listDir .root"
    assertTrue (List.Pairwise (fun x y => x.val < y.val) listedRoot.toList) "listDir strictly sorted"
    assertTrue (listedRoot.map (·.val) == #["a", "sym_dir", "sym_leaf"]) "listDir entries match"

    let walked ← assertOk (← sub.walk Raw.RelPath.root) "walk .root"
    match walked.toList with
    | e0 :: _ =>
      assertTrue (e0.root == ".") "walk starts at ."
      assertTrue (e0.dirs == #["a"] && e0.files == #["sym_dir", "sym_leaf"])
        "walk exposes symlink in files and excludes from dirs"
    | [] => assertTrue false "walk non-empty"
    assertTrue (!(walked.any fun e => e.root == "sym_dir")) "walk never descends into symlink"
    let subWalked ← assertOk (← sub.walk rParentB) "walk a/b"
    match subWalked.toList with
    | s0 :: _ => assertTrue (s0.root == "." && s0.dirs == #["c"]) "subwalk roots at ."
    | [] => assertTrue false "subWalked non-empty"
    assertErrKind (← sub.walk rData) .notADirectory "walk regular file fails notADirectory"

    assertErrKind (← sub.atomicWriteBytes rParentB payload) .isADirectory "atomicWriteBytes existing dir"
    let listedB ← assertOk (← sub.listDir rParentB) "listDir a/b after dir atomicWrite failure"
    assertTrue (listedB.map (·.val) == #["c"]) "no leaked .t temp file after EISDIR"

    let rLock ← assertOk (Raw.RelPath.parse "a/work.lock") "parse work.lock"
    let lockRes : Except FsError Unit ← sub.withFileLock rLock .exclusive true do
      let contended ← assertOk (← sub.tryWithFileLock rLock .exclusive false do
        ranRef.set true
        return .ok "should_not_run") "contended tryWithFileLock"
      assertTrue contended.isNone "contended tryWithFileLock returns none"
      return .error { kind := .ioError, message := "inner abort" }
    assertErrKind lockRes .ioError "withFileLock propagates error"
    assertTrue (!(← ranRef.get)) "contended callback never ran"
    let afterUnlock ← assertOk (← sub.tryWithFileLock rLock .exclusive false (pure (.ok 99)))
      "lock released after error"
    assertTrue (afterUnlock == some 99) "lock reacquired cleanly"

    assertOk (← sub.unlink rSymDir false) "unlink sym_dir without removing target a"
    assertTrue ((← assertOk (← sub.lstat rParentA) "a intact after unlinking sym_dir").kind == .dir) "a intact"

    assertErrKind (← sub.rmdir rParentA) .notEmpty "rmdir non-empty a"
    assertErrKind (← sub.unlink rParentA false) .isADirectory "unlink dir fails isADirectory"
    assertOk (← sub.rmtree (← assertOk (Raw.RelPath.parse "absent_dir") "parse") true) "rmtree ignoreMissing=true"
    assertErrKind (← sub.rmtree (← assertOk (Raw.RelPath.parse "absent_dir") "parse") false) .notFound
      "rmtree ignoreMissing=false"
    assertErrKind (← sub.rmtree rSymLeaf false) .notADirectory "rmtree regular file"
    assertOk (← sub.rmtree rParentA false) "rmtree a"
    assertErrKind (← sub.lstat rParentA) .notFound "a notFound after rmtree"

    if isNonRoot then
      let rPart ← assertOk (Raw.RelPath.parse "part") "parse part"
      let rPart1 ← assertOk (Raw.RelPath.parse "part/1_file") "parse part/1_file"
      let rPart2 ← assertOk (Raw.RelPath.parse "part/2_dir") "parse part/2_dir"
      assertOk (← sub.mkdir rPart false false) "mkdir part"
      assertOk (← sub.atomicWriteBytes rPart1 payload) "write part/1_file"
      assertOk (← sub.mkdir rPart2 false false) "mkdir part/2_dir"
      assertOk (← Raw.chmod (Fs.join root "part/2_dir") 0o000) "chmod 0000 part/2_dir"
      assertErrKind (← sub.rmtree rPart false) .permissionDenied "rmtree propagates child permissionDenied"
      assertErrKind (← sub.lstat rPart1) .notFound "partial sibling unlinks preserved without rollback"
      assertOk (← Raw.chmod (Fs.join root "part/2_dir") 0o755) "restore chmod part/2_dir"
      assertOk (← sub.rmtree rPart false) "cleanup part"

      let rUnrd ← assertOk (Raw.RelPath.parse "unreadable") "parse unreadable"
      assertOk (← sub.mkdir rUnrd false false) "mkdir unreadable"
      assertOk (← Raw.chmod (Fs.join root "unreadable") 0o111) "chmod 0111 unreadable"
      assertErrKind (← sub.walk rUnrd) .permissionDenied "walk propagates permissionDenied"
      assertOk (← Raw.chmod (Fs.join root "unreadable") 0o755) "restore unreadable chmod"
      assertOk (← sub.rmdir rUnrd) "cleanup unreadable"

    let movedRoot := Fs.join tmp "subroot_moved"
    assertOk (← Fs.rename root movedRoot) "external rename of open subtree root"
    let rPinnedFile ← assertOk (Raw.RelPath.parse "pinned.txt") "parse pinned.txt"
    assertOk (← sub.atomicWriteBytes rPinnedFile payload) "write inside moved subtree via pinned descriptor"
    assertOkBytesEq (← Fs.readBytes (Fs.join movedRoot "pinned.txt")) payload "read back from renamed path"

    let fifoRel ← assertOk (Raw.RelPath.parse "sub.fifo") "parse sub.fifo"
    match ← Process.runCommand "mkfifo" #[Fs.join movedRoot "sub.fifo"] with
    | .ok out => assertTrue (out.exitCode == 0) "mkfifo sub.fifo"
    | .error e => throw (IO.userError s!"mkfifo failed: {repr e}")
    assertErrKind (← sub.readRegular fifoRel) .invalidInput "sub.readRegular FIFO rejected immediately"
    assertOk (← sub.unlink fifoRel false) "unlink sub.fifo"

    return .ok ()
  let _ ← assertOk rUnit "withSubtree main checks"

  let movedRoot := Fs.join tmp "subroot_moved"
  let failRenameOps : RawDirOps :=
    { Fs.defaultDirOps with
      freshTempName := pure (Raw.EntryName.lit ".t.fail_tmp")
      renameAt := fun _ _ _ _ => pure (.error { kind := .ioError, message := "injected rename error" }) }
  let failOpener := Fs.Internal.mkSubtreeOpenerM failRenameOps
  let rInjected ← failOpener.withSubtree movedRoot fun sub => do
    sub.atomicWriteBytes (← assertOk (Raw.RelPath.parse "target.bin") "parse") (ByteArray.mk #[5])
  assertErrKind rInjected .ioError "atomicWriteBytes propagates rename error"
  assertOkEq (← Fs.pathExists (Fs.join movedRoot ".t.fail_tmp")) false "atomicWriteBytes cleans .t temp on error"

  let collideOps : RawDirOps :=
    { Fs.defaultDirOps with freshTempName := pure (Raw.EntryName.lit ".t.collide") }
  assertOk (← Fs.writeText (Fs.join movedRoot ".t.collide") "held") "plant .t.collide"
  let rCollide ← (Fs.Internal.mkSubtreeOpenerM collideOps).withSubtree movedRoot fun sub => do
    sub.atomicWriteBytes (← assertOk (Raw.RelPath.parse "never.bin") "parse") (ByteArray.mk #[5])
  assertErrKind rCollide .alreadyExists "atomicWriteBytes returns alreadyExists after 16 collisions"
  assertOkEq (← Fs.pathExists (Fs.join movedRoot "never.bin")) false "never.bin absent after collision exhaustion"

  testWithSubtreeExtra movedRoot
  assertOk (← Fs.rmtree movedRoot) "cleanup subroot_moved"
  assertOk (← Fs.unlink pOutside) "cleanup outside.bin"

private def withTempDir {α : Type} (f : String → IO α) : IO α :=
  IO.FS.withTempDir fun dir => f dir.toString

/-- Execute all pure path and real filesystem runtime checks for `LeanSwe.Fs`. -/
def runAll : IO Unit := do
  testPurePaths
  withTempDir fun tmp => do
    let moved ← assertOk (← testFilesAndDirs tmp) "testFilesAndDirs"
    assertOk (← testSymlinksAndGlobs tmp moved) "testSymlinksAndGlobs"
    testLocksSingleProcess tmp
    testLocksMultiProcess tmp
    testAmbientSafety tmp
    testWithSubtree tmp
  IO.println "PASS: LeanSwe.Fs runtime tests"

end LeanSwe.Fs.RuntimeTests
