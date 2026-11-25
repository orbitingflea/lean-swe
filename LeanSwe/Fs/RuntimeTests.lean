import Core.Assumptions
import LeanSwe.Fs.Interface
import LeanSwe.Fs.SysBridge
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.Process.Interface

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
  let child1 ← match ← Process.spawn
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
    match ← Process.awaitOutput child1 with
    | .ok (.exited out) => assertTrue (out.exitCode == 0) "child1 exited 0"
    | .ok other => throw (IO.userError s!"child1 unexpected outcome: {repr other}")
    | .error e => throw (IO.userError s!"awaitOutput child1 failed: {repr e}")
  finally
    let _ ← Process.reap child1

  let ready2 := Fs.join tmp "mp2.ready"
  let stop2 := Fs.join tmp "mp2.stop"
  let child2 ← match ← Process.spawn
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
    match ← Process.awaitOutput child2 with
    | .ok (.exited out) => assertTrue (out.exitCode == 0) "child2 exited 0"
    | .ok other => throw (IO.userError s!"child2 unexpected outcome: {repr other}")
    | .error e => throw (IO.userError s!"awaitOutput child2 failed: {repr e}")
  finally
    let _ ← Process.reap child2

  let ready3 := Fs.join tmp "mp3.ready"
  let killScript :=
    "import fcntl, os, signal, sys, time\n" ++
    "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n" ++
    "lp, rp = sys.argv[1:3]\n" ++
    "fd = os.open(lp, os.O_RDONLY)\n" ++
    "fcntl.flock(fd, fcntl.LOCK_EX)\n" ++
    "open(rp, 'w').write('1')\n" ++
    "time.sleep(10.0)\n"
  let child3 ← match ← Process.spawn
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
    let _ ← Process.reap child3

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
  let sockChild ← match ← Process.spawn { program := "python3", args := #["-c", sockScript, workDir] } with
    | .ok h => pure h
    | .error e => throw (IO.userError s!"spawn sockChild failed: {repr e}")
  try
    waitForFile readyPath
    assertErrKind (← Fs.readBytes sockPath) .invalidInput "Fs.readBytes Unix socket rejected"
    assertErrKind (← Fs.readText sockPath) .invalidInput "Fs.readText Unix socket rejected"
    assertOk (← Fs.writeText stopPath "go") "stop sockChild"
    match ← Process.awaitOutput sockChild with
    | .ok (.exited out) => assertTrue (out.exitCode == 0) "sockChild exited 0"
    | .ok other => throw (IO.userError s!"sockChild unexpected outcome: {repr other}")
    | .error e => throw (IO.userError s!"awaitOutput sockChild failed: {repr e}")
  finally
    let _ ← Process.reap sockChild
    let _ ← Fs.unlink sockPath true
    let _ ← Fs.unlink readyPath true
    let _ ← Fs.unlink stopPath true

  let detApi := Fs.Internal.mkApiM { SysBridge.defaultOps with monotonicNonce := pure 777 }
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
    { SysBridge.defaultOps with
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
    let rUnlinkMissPre ← assertOk (RelPath.parse "no_such_dir/no_such_file") "parse no_such_dir/no_such_file"
    assertOk (← sub.unlink rUnlinkMissPre true) "unlink missing intermediate missingOk=true"
    assertErrKind (← sub.unlink rUnlinkMissPre false) .notFound "unlink missing intermediate missingOk=false"

    let rRoSub ← assertOk (RelPath.parse "ro_sub") "parse ro_sub"
    let rRoInner ← assertOk (RelPath.parse "ro_sub/entry.txt") "parse ro_sub/entry.txt"
    assertOk (← sub.mkdir rRoSub false false) "mkdir ro_sub"
    assertOk (← sub.atomicWriteBytes rRoInner payload) "write ro_sub/entry.txt"
    assertOk (← Fs.chmod (Fs.join root "ro_sub") 0o400) "chmod 0400 ro_sub"
    let roListed1 ← assertOk (← sub.listDir rRoSub) "listDir 0400 ro_sub"
    let roListed2 ← assertOk (← sub.listDir rRoSub) "listDir 0400 ro_sub twice"
    assertTrue (roListed1.map (·.val) == #["entry.txt"] && roListed2.map (·.val) == #["entry.txt"])
      "listDir succeeds on 0400 subdirectory"
    assertOk (← Fs.chmod (Fs.join root "ro_sub") 0o755) "restore chmod 0755 ro_sub"
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
  assertOk (← Fs.chmod noExecDir 0o400) "chmod 0400 no_exec_root"
  assertErrKind (← Fs.withSubtree noExecDir fun _ => do
    ranRef.set true
    return .ok ()) .permissionDenied "withSubtree refuses directory lacking owner search bit"
  assertTrue (!(← ranRef.get)) "0400 root never runs action"
  assertOk (← Fs.chmod noExecDir 0o755) "restore chmod 0755 no_exec_root"
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
    let rootStat ← assertOk (← sub.lstat RelPath.root) "sub.lstat .root"
    assertTrue (rootStat.kind == .dir) "rootStat kind == .dir"
    assertOk (← sub.mkdir RelPath.root false true) "mkdir .root existOk=true"
    assertErrKind (← sub.mkdir RelPath.root false false) .alreadyExists "mkdir .root existOk=false"
    assertErrKind (← sub.readRegular RelPath.root) .isADirectory "readRegular .root"
    let payload := ByteArray.mk #[1, 2, 3, 4]
    assertErrKind (← sub.atomicWriteBytes RelPath.root payload) .invalidInput "atomicWriteBytes .root"
    assertErrKind (← sub.unlink RelPath.root true) .invalidInput "unlink .root"
    assertErrKind (← sub.rmdir RelPath.root) .invalidInput "rmdir .root"
    assertErrKind (← sub.rmtree RelPath.root true) .invalidInput "rmtree .root"
    assertErrKind (← sub.symlink "x" RelPath.root) .invalidInput "symlink .root"
    assertErrKind (← sub.withFileLock RelPath.root .exclusive true (pure (.ok ()))) .invalidInput
      "withFileLock .root"
    assertErrKind (← sub.tryWithFileLock RelPath.root .exclusive true (pure (.ok ()))) .invalidInput
      "tryWithFileLock .root"

    let rNested ← assertOk (RelPath.parse "a/b/c") "parse a/b/c"
    let rParentA ← assertOk (RelPath.parse "a") "parse a"
    let rParentB ← assertOk (RelPath.parse "a/b") "parse a/b"
    assertErrKind (← sub.mkdir rNested false false) .notFound "mkdir parents=false missing intermediate"
    assertOk (← sub.mkdir rNested true false) "mkdir parents=true nested"
    assertOk (← sub.mkdir rNested false true) "mkdir existOk=true existing dir"
    assertErrKind (← sub.mkdir rNested false false) .alreadyExists "mkdir existOk=false existing dir"

    let rData ← assertOk (RelPath.parse "a/b/c/data.bin") "parse data.bin"
    assertOk (← sub.atomicWriteBytes rData payload) "atomicWriteBytes nested"
    let got ← assertOk (← sub.readRegular rData) "readRegular nested"
    assertTrue (got == payload) "readRegular roundtrip"
    let stData ← assertOk (← sub.lstat rData) "lstat data.bin"
    assertTrue (stData.kind == .file && stData.byteSize == payload.size) "lstat data.bin metadata"
    assertErrKind (← sub.mkdir rData false true) .alreadyExists "mkdir existOk=true rejects existing regular file"

    let max255Rel ← assertOk (RelPath.parse ("a/" ++ String.ofList (List.replicate 255 'z'))) "parse 255 leaf"
    assertOk (← sub.atomicWriteBytes max255Rel payload) "atomicWriteBytes 255-byte leaf"
    assertTrue ((← assertOk (← sub.readRegular max255Rel) "readRegular 255 leaf") == payload) "readRegular 255"
    assertOk (← sub.unlink max255Rel false) "unlink 255 leaf"

    let rSymLeaf ← assertOk (RelPath.parse "sym_leaf") "parse sym_leaf"
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

    let rSymDir ← assertOk (RelPath.parse "sym_dir") "parse sym_dir"
    let rSymDirSub ← assertOk (RelPath.parse "sym_dir/sub") "parse sym_dir/sub"
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
    assertErrKind (← sub.lstat (← assertOk (RelPath.parse "a/b/sub_missing") "parse")) .notFound
      "a/b untouched"

    let listedRoot ← assertOk (← sub.listDir RelPath.root) "listDir .root"
    assertTrue (List.Pairwise (fun x y => x.val < y.val) listedRoot.toList) "listDir strictly sorted"
    assertTrue (listedRoot.map (·.val) == #["a", "sym_dir", "sym_leaf"]) "listDir entries match"

    let walked ← assertOk (← sub.walk RelPath.root) "walk .root"
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

    let rLock ← assertOk (RelPath.parse "a/work.lock") "parse work.lock"
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
    assertOk (← sub.rmtree (← assertOk (RelPath.parse "absent_dir") "parse") true) "rmtree ignoreMissing=true"
    assertErrKind (← sub.rmtree (← assertOk (RelPath.parse "absent_dir") "parse") false) .notFound
      "rmtree ignoreMissing=false"
    assertErrKind (← sub.rmtree rSymLeaf false) .notADirectory "rmtree regular file"
    assertOk (← sub.rmtree rParentA false) "rmtree a"
    assertErrKind (← sub.lstat rParentA) .notFound "a notFound after rmtree"

    if isNonRoot then
      let rPart ← assertOk (RelPath.parse "part") "parse part"
      let rPart1 ← assertOk (RelPath.parse "part/1_file") "parse part/1_file"
      let rPart2 ← assertOk (RelPath.parse "part/2_dir") "parse part/2_dir"
      assertOk (← sub.mkdir rPart false false) "mkdir part"
      assertOk (← sub.atomicWriteBytes rPart1 payload) "write part/1_file"
      assertOk (← sub.mkdir rPart2 false false) "mkdir part/2_dir"
      assertOk (← Fs.chmod (Fs.join root "part/2_dir") 0o000) "chmod 0000 part/2_dir"
      assertErrKind (← sub.rmtree rPart false) .permissionDenied "rmtree propagates child permissionDenied"
      assertErrKind (← sub.lstat rPart1) .notFound "partial sibling unlinks preserved without rollback"
      assertOk (← Fs.chmod (Fs.join root "part/2_dir") 0o755) "restore chmod part/2_dir"
      assertOk (← sub.rmtree rPart false) "cleanup part"

      let rUnrd ← assertOk (RelPath.parse "unreadable") "parse unreadable"
      assertOk (← sub.mkdir rUnrd false false) "mkdir unreadable"
      assertOk (← Fs.chmod (Fs.join root "unreadable") 0o111) "chmod 0111 unreadable"
      assertErrKind (← sub.walk rUnrd) .permissionDenied "walk propagates permissionDenied"
      assertOk (← Fs.chmod (Fs.join root "unreadable") 0o755) "restore unreadable chmod"
      assertOk (← sub.rmdir rUnrd) "cleanup unreadable"

    let movedRoot := Fs.join tmp "subroot_moved"
    assertOk (← Fs.rename root movedRoot) "external rename of open subtree root"
    let rPinnedFile ← assertOk (RelPath.parse "pinned.txt") "parse pinned.txt"
    assertOk (← sub.atomicWriteBytes rPinnedFile payload) "write inside moved subtree via pinned descriptor"
    assertOkBytesEq (← Fs.readBytes (Fs.join movedRoot "pinned.txt")) payload "read back from renamed path"

    let fifoRel ← assertOk (RelPath.parse "sub.fifo") "parse sub.fifo"
    match ← Process.runCommand "mkfifo" #[Fs.join movedRoot "sub.fifo"] with
    | .ok out => assertTrue (out.exitCode == 0) "mkfifo sub.fifo"
    | .error e => throw (IO.userError s!"mkfifo failed: {repr e}")
    assertErrKind (← sub.readRegular fifoRel) .invalidInput "sub.readRegular FIFO rejected immediately"
    assertOk (← sub.unlink fifoRel false) "unlink sub.fifo"

    return .ok ()
  let _ ← assertOk rUnit "withSubtree main checks"

  let movedRoot := Fs.join tmp "subroot_moved"
  let failRenameOps :=
    { SysBridge.defaultDirOps with
      freshTempName := pure (EntryName.lit ".t.fail_tmp")
      renameAt := fun _ _ _ _ => pure (.error { kind := .ioError, message := "injected rename error" }) }
  let failOpener := Fs.Internal.mkSubtreeOpenerM failRenameOps
  let rInjected ← failOpener.withSubtree movedRoot fun sub => do
    sub.atomicWriteBytes (← assertOk (RelPath.parse "target.bin") "parse") (ByteArray.mk #[5])
  assertErrKind rInjected .ioError "atomicWriteBytes propagates rename error"
  assertOkEq (← Fs.pathExists (Fs.join movedRoot ".t.fail_tmp")) false "atomicWriteBytes cleans .t temp on error"

  let collideOps :=
    { SysBridge.defaultDirOps with freshTempName := pure (EntryName.lit ".t.collide") }
  assertOk (← Fs.writeText (Fs.join movedRoot ".t.collide") "held") "plant .t.collide"
  let rCollide ← (Fs.Internal.mkSubtreeOpenerM collideOps).withSubtree movedRoot fun sub => do
    sub.atomicWriteBytes (← assertOk (RelPath.parse "never.bin") "parse") (ByteArray.mk #[5])
  assertErrKind rCollide .alreadyExists "atomicWriteBytes returns alreadyExists after 16 collisions"
  assertOkEq (← Fs.pathExists (Fs.join movedRoot "never.bin")) false "never.bin absent after collision exhaustion"

  testWithSubtreeExtra movedRoot
  assertOk (← Fs.rmtree movedRoot) "cleanup subroot_moved"
  assertOk (← Fs.unlink pOutside) "cleanup outside.bin"

private def mkErrFilesOps (eno : LinuxSyscall.Errno) : LinuxSyscall.Files.FilesOpsM IO Unit :=
  { openat := fun _ _ _ _ => pure (.error eno)
    openat2 := fun _ _ _ => pure (.error eno)
    close := fun _ => pure (.ok ())
    read := fun _ _ => pure (.error eno)
    write := fun _ _ => pure (.error eno)
    fstat := fun _ => pure (.error eno)
    fstatat := fun _ _ _ => pure (.error eno)
    faccessat := fun _ _ _ _ => pure (.error eno)
    mkdirat := fun _ _ _ => pure (.error eno)
    unlinkat := fun _ _ _ => pure (.error eno)
    renameat2 := fun _ _ _ _ _ => pure (.error eno)
    symlinkat := fun _ _ _ => pure (.error eno)
    readlinkat := fun _ _ _ => pure (.error eno)
    getdents64 := fun _ _ => pure (.error eno)
    fchmodat := fun _ _ _ => pure (.error eno)
    fchmod := fun _ _ => pure (.error eno)
    flock := fun _ _ => pure (.error eno)
    fcntl := fun _ _ => pure (.error eno)
    fsync := fun _ => pure (.error eno)
    getcwd := fun _ => pure (.error eno)
    lseek := fun _ _ _ => pure (.error eno)
    reopenReadOnly := fun _ => pure (.error eno)
    dupStdio := fun _ => pure (.error eno) }

private def testSysBridgeEdgeCases (tmp : String) : IO Unit := do
  for eno in #[LinuxSyscall.Errno.EMFILE, LinuxSyscall.Errno.ENFILE] do
    let mockFiles := mkErrFilesOps eno
    let rawOps := SysBridge.mkRawFsOpsM mockFiles (pure 1)
    let rawDir := SysBridge.mkRawDirOpsM mockFiles (pure 1)
    assertErrKind (← rawOps.readBytes "/x") .ioError "EMFILE/ENFILE readBytes -> .ioError"
    assertErrKind (← rawOps.createFileNew "/x" ByteArray.empty) .ioError "EMFILE/ENFILE createFileNew -> .ioError"
    assertErrKind (← rawOps.readDir "/x") .ioError "EMFILE/ENFILE readDir -> .ioError"
    assertErrKind (← rawOps.acquireLock "/x" .exclusive true true) .ioError "EMFILE/ENFILE acquireLock -> .ioError"
    assertErrKind (← rawDir.openDir "/x") .ioError "EMFILE/ENFILE openDir -> .ioError"
    assertErrKind (← rawDir.openDirAt () (EntryName.lit "a")) .ioError "EMFILE/ENFILE openDirAt -> .ioError"
    assertErrKind (← rawDir.readRegularAt () (EntryName.lit "a")) .ioError "EMFILE/ENFILE readRegularAt -> .ioError"
    assertErrKind (← rawDir.createFileAt () (EntryName.lit "a") ByteArray.empty) .ioError "EMFILE/ENFILE createFileAt -> .ioError"
    assertErrKind (← rawDir.acquireLockAt () (EntryName.lit "a") .exclusive true true) .ioError "EMFILE/ENFILE acquireLockAt -> .ioError"

  let bigBytes := ByteArray.mk (Array.replicate 140000 0xCD)
  let bigPath := Fs.join tmp "big_multichunk.bin"
  assertOk (← Fs.atomicWriteBytes bigPath bigBytes) "atomicWriteBytes 140KB"
  assertOkBytesEq (← Fs.readBytes bigPath) bigBytes "readBytes 140KB exact"
  assertOk (← Fs.unlink bigPath) "unlink big_multichunk.bin"

  let concDir := Fs.join tmp "conc_readdir"
  assertOk (← Fs.mkdir concDir) "mkdir conc_readdir"
  for i in List.range 40 do
    assertOk (← Fs.writeText (Fs.join concDir s!"f_{i}.txt") "x") s!"create f_{i}"
  let rConc ← Fs.withSubtree concDir fun sub => do
    let mut tasks : Array (Task (Except IO.Error (Except FsError (Array EntryName)))) := #[]
    for _ in List.range 8 do
      let t ← IO.asTask (prio := .dedicated) (sub.listDir RelPath.root)
      tasks := tasks.push t
    for t in tasks do
      match ← IO.wait t with
      | .error ioErr => throw ioErr
      | .ok rList =>
        let xs ← assertOk rList "concurrent sub.listDir"
        assertTrue (xs.size == 40) s!"concurrent listDir count 40 (got {xs.size})"
    return .ok ()
  assertOk rConc "concurrent readDirAt via withSubtree"
  assertOk (← Fs.rmtree concDir) "cleanup conc_readdir"

  let loopA := Fs.join tmp "loop_a"
  let loopB := Fs.join tmp "loop_b"
  assertOk (← Fs.symlink loopB loopA) "symlink loop_a -> loop_b"
  assertOk (← Fs.symlink loopA loopB) "symlink loop_b -> loop_a"
  assertErrKind (← Fs.resolve loopA) .ioError "resolve symlink loop returns ioError (ELOOP)"
  let regF := Fs.join tmp "not_a_dir.txt"
  assertOk (← Fs.writeText regF "hi") "write not_a_dir.txt"
  assertErrKind (← Fs.resolve (regF ++ "/")) .notADirectory "resolve trailing slash on file returns notADirectory"
  assertOkEq (← Fs.resolve "/") "/" "resolve root returns /"
  assertOk (← Fs.unlink regF) "unlink not_a_dir.txt"
  assertOk (← Fs.unlink loopA) "unlink loop_a"
  assertOk (← Fs.unlink loopB) "unlink loop_b"

  let n1 ← SysBridge.defaultOps.monotonicNonce
  let n2 ← SysBridge.defaultOps.monotonicNonce
  let n3 ← SysBridge.defaultOps.monotonicNonce
  assertTrue (n1 > 65536 && n1 < n2 && n2 < n3)
    s!"monotonicNonce must be strictly increasing and avoid raw low counter (got {n1}, {n2}, {n3})"
  let staleTarget := Fs.join tmp "stale_atomic.bin"
  let staleTmp1 := Fs.join tmp ".stale_atomic.bin.tmp.1"
  let staleTmp2 := Fs.join tmp ".stale_atomic.bin.tmp.2"
  assertOk (← Fs.writeText staleTmp1 "stale1") "plant stale .tmp.1"
  assertOk (← Fs.writeText staleTmp2 "stale2") "plant stale .tmp.2"
  assertOk (← Fs.atomicWriteBytes staleTarget (ByteArray.mk #[7, 8, 9])) "atomicWriteBytes ignores stale .tmp.1/.tmp.2"
  assertOkBytesEq (← Fs.readBytes staleTarget) (ByteArray.mk #[7, 8, 9]) "stale_atomic.bin bytes"
  assertOkEq (← Fs.readText staleTmp1) "stale1" "stale .tmp.1 preserved"
  assertOkEq (← Fs.readText staleTmp2) "stale2" "stale .tmp.2 preserved"
  assertOk (← Fs.unlink staleTarget) "cleanup stale_atomic.bin"
  assertOk (← Fs.unlink staleTmp1) "cleanup stale .tmp.1"
  assertOk (← Fs.unlink staleTmp2) "cleanup stale .tmp.2"
  let tn1 ← SysBridge.defaultDirOps.freshTempName
  let tn2 ← SysBridge.defaultDirOps.freshTempName
  assertTrue (tn1 != tn2 && tn1.val != ".t.1" && tn1.val != ".t.2" && tn2.val != ".t.1" && tn2.val != ".t.2")
    s!"freshTempName must be distinct and avoid raw low counter (got {tn1.val}, {tn2.val})"
  let staleSubDir := Fs.join tmp "stale_sub_root"
  assertOk (← Fs.mkdir staleSubDir) "mkdir stale_sub_root"
  assertOk (← Fs.writeText (Fs.join staleSubDir ".t.1") "stale_t1") "plant stale .t.1"
  assertOk (← Fs.writeText (Fs.join staleSubDir ".t.2") "stale_t2") "plant stale .t.2"
  let rStaleSub ← Fs.withSubtree staleSubDir fun sub => do
    let rel ← assertOk (RelPath.parse "out.bin") "parse out.bin"
    sub.atomicWriteBytes rel (ByteArray.mk #[42])
  assertOk rStaleSub "withSubtree atomicWriteBytes ignores stale .t.1/.t.2"
  assertOkBytesEq (← Fs.readBytes (Fs.join staleSubDir "out.bin")) (ByteArray.mk #[42]) "out.bin bytes"
  assertOk (← Fs.rmtree staleSubDir) "cleanup stale_sub_root"

private def withTempDir {α : Type} (f : String → IO α) : IO α :=
  IO.FS.withTempDir fun dir => f dir.toString

private def nulPath : String :=
  "a" ++ String.singleton (Char.ofNat 0) ++ "b"

private def runRealNotFound {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    assertErrKind (← act (Fs.join tmp "missing_entry")) .notFound "real notFound"

private def runRealNotFoundChild {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    assertErrKind (← act (Fs.joinMany #[tmp, "missing_dir", "child"])) .notFound "real notFound child"

private def runRealPermDeniedFile {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let f := Fs.join tmp "no_read.txt"
    assertOk (← Fs.writeText f "secret") "create no_read.txt"
    assertOk (← Fs.chmod f 0o000) "chmod 0o000 file"
    try
      assertErrKind (← act f) .permissionDenied "real permissionDenied file"
    finally
      let _ ← Fs.chmod f 0o644

private def runRealPermDeniedDir {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "no_access_dir"
    assertOk (← Fs.mkdir d false false) "create no_access_dir"
    assertOk (← Fs.chmod d 0o000) "chmod 0o000 dir"
    try
      assertErrKind (← act d) .permissionDenied "real permissionDenied dir"
    finally
      let _ ← Fs.chmod d 0o755

private def runRealPermDeniedDirWrite {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "ro_dir"
    assertOk (← Fs.mkdir d false false) "create ro_dir"
    assertOk (← Fs.chmod d 0o555) "chmod 0o555 dir"
    try
      assertErrKind (← act (Fs.join d "child")) .permissionDenied "real permissionDenied dir write"
    finally
      let _ ← Fs.chmod d 0o755

private def runRealPermDeniedDirChild {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "sealed_dir"
    let f := Fs.join d "child"
    assertOk (← Fs.mkdir d false false) "create sealed_dir"
    assertOk (← Fs.writeText f "x") "create child"
    assertOk (← Fs.chmod d 0o000) "chmod 0o000 sealed_dir"
    try
      assertErrKind (← act f) .permissionDenied "real permissionDenied dir child"
    finally
      let _ ← Fs.chmod d 0o755

private def runRealPermDeniedExistingChild {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "ro_parent"
    let f := Fs.join d "child"
    assertOk (← Fs.mkdir d false false) "create ro_parent"
    assertOk (← Fs.writeText f "x") "create child"
    assertOk (← Fs.chmod d 0o555) "chmod 0o555 ro_parent"
    try
      assertErrKind (← act f) .permissionDenied "real permissionDenied existing child"
    finally
      let _ ← Fs.chmod d 0o755

private def runRealPermDeniedExistingSubdir {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "ro_parent_sub"
    let sub := Fs.join d "sub"
    assertOk (← Fs.mkdir sub true false) "create ro_parent_sub/sub"
    assertOk (← Fs.chmod d 0o555) "chmod 0o555 ro_parent_sub"
    try
      assertErrKind (← act sub) .permissionDenied "real permissionDenied existing subdir"
    finally
      let _ ← Fs.chmod d 0o755

private def runRealPermDeniedNonEmptyDir {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "ro_tree"
    assertOk (← Fs.mkdir d false false) "create ro_tree"
    assertOk (← Fs.writeText (Fs.join d "leaf") "x") "create leaf"
    assertOk (← Fs.chmod d 0o555) "chmod 0o555 ro_tree"
    try
      assertErrKind (← act d) .permissionDenied "real permissionDenied non-empty dir"
    finally
      let _ ← Fs.chmod d 0o755

private def runRealIsADir {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "some_dir"
    assertOk (← Fs.mkdir d false false) "create some_dir"
    assertErrKind (← act d) .isADirectory "real isADirectory"

private def runRealNotADirChild {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let f := Fs.join tmp "reg_file"
    assertOk (← Fs.writeText f "x") "create reg_file"
    assertErrKind (← act (f ++ "/child")) .notADirectory "real notADirectory child"

private def runRealNotADirFile {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let f := Fs.join tmp "reg_file"
    assertOk (← Fs.writeText f "x") "create reg_file"
    assertErrKind (← act f) .notADirectory "real notADirectory file"

private def runRealInvalidNul {α : Type} (act : String → IO (Except FsError α)) : IO Unit := do
  assertErrKind (← act nulPath) .invalidInput "real invalidInput NUL"

private def runRealEloop {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let loop := Fs.join tmp "eloop"
    assertOk (← Fs.symlink loop loop) "create ELOOP symlink"
    assertErrKind (← act loop) .ioError "real ioError ELOOP"

private def runRealEloopChild {α : Type} (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let loop := Fs.join tmp "eloop"
    assertOk (← Fs.symlink loop loop) "create ELOOP symlink"
    assertErrKind (← act (loop ++ "/child")) .ioError "real ioError ELOOP child"

private def runRealExistingFileErr {α : Type} (expected : FsErrorKind)
    (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let f := Fs.join tmp "existing_file"
    assertOk (← Fs.writeText f "x") "create existing_file"
    assertErrKind (← act f) expected "real existing file err"

private def runRealExistingDirErr {α : Type} (expected : FsErrorKind)
    (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "existing_dir"
    assertOk (← Fs.mkdir d false false) "create existing_dir"
    assertErrKind (← act d) expected "real existing dir err"

private def runRealNonEmptyDirErr {α : Type} (expected : FsErrorKind)
    (act : String → IO (Except FsError α)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "nonempty_dir"
    assertOk (← Fs.mkdir d false false) "create nonempty_dir"
    assertOk (← Fs.writeText (Fs.join d "a") "x") "create a"
    assertErrKind (← act d) expected "real non-empty dir err"

private def runRealRenameFileOntoDir : IO Unit :=
  withTempDir fun tmp => do
    let f := Fs.join tmp "src_file"
    let d := Fs.join tmp "dst_dir"
    assertOk (← Fs.writeText f "x") "create src_file"
    assertOk (← Fs.mkdir d false false) "create dst_dir"
    assertErrKind (← Fs.rename f d) .isADirectory "rename file onto dir"

private def runRealRenameDirOntoFile : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "src_dir"
    let f := Fs.join tmp "dst_file"
    assertOk (← Fs.mkdir d false false) "create src_dir"
    assertOk (← Fs.writeText f "x") "create dst_file"
    assertErrKind (← Fs.rename d f) .notADirectory "rename dir onto file"

private def runRealRenameDirOntoNonEmptyDir : IO Unit :=
  withTempDir fun tmp => do
    let src := Fs.join tmp "src_dir"
    let dst := Fs.join tmp "dst_dir"
    assertOk (← Fs.mkdir src false false) "create src_dir"
    assertOk (← Fs.mkdir dst false false) "create dst_dir"
    assertOk (← Fs.writeText (Fs.join dst "keep") "x") "create keep"
    assertErrKind (← Fs.rename src dst) .notEmpty "rename dir onto non-empty dir"

private def runRealCopyTreeExistingDst : IO Unit :=
  withTempDir fun tmp => do
    let src := Fs.join tmp "src_dir"
    let dst := Fs.join tmp "dst_dir"
    assertOk (← Fs.mkdir src false false) "create src_dir"
    assertOk (← Fs.mkdir dst false false) "create dst_dir"
    assertErrKind (← Fs.copyTree src dst false) .alreadyExists "copyTree existing dst"

private def runRealPredNotFound (act : String → IO (Except FsError Bool)) : IO Unit :=
  withTempDir fun tmp => do
    assertOkEq (← act (Fs.join tmp "missing_pred")) false "real pred notFound"

private def runRealPredPermDenied (act : String → IO (Except FsError Bool)) : IO Unit :=
  withTempDir fun tmp => do
    let d := Fs.join tmp "sealed_pred_dir"
    let f := Fs.join d "child"
    assertOk (← Fs.mkdir d false false) "create sealed_pred_dir"
    assertOk (← Fs.writeText f "x") "create child"
    assertOk (← Fs.chmod d 0o000) "chmod 0o000 sealed_pred_dir"
    try
      assertOkEq (← act f) false "real pred permissionDenied"
    finally
      let _ ← Fs.chmod d 0o755

private def runRealPredNotADir (act : String → IO (Except FsError Bool)) : IO Unit :=
  withTempDir fun tmp => do
    let f := Fs.join tmp "reg_pred"
    assertOk (← Fs.writeText f "x") "create reg_pred"
    assertOkEq (← act (f ++ "/child")) false "real pred notADirectory"

private def runRealPredInvalidNul (act : String → IO (Except FsError Bool)) : IO Unit := do
  assertOkEq (← act nulPath) false "real pred invalidInput NUL"

private def runRealPredEloop (act : String → IO (Except FsError Bool)) : IO Unit :=
  withTempDir fun tmp => do
    let loop := Fs.join tmp "eloop_pred"
    assertOk (← Fs.symlink loop loop) "create ELOOP pred symlink"
    assertOkEq (← act (loop ++ "/child")) false "real pred ioError ELOOP"

private def errnoForKind : FsErrorKind → Option LinuxSyscall.Errno
  | .notFound => some LinuxSyscall.Errno.ENOENT
  | .alreadyExists => some LinuxSyscall.Errno.EEXIST
  | .permissionDenied => some LinuxSyscall.Errno.EACCES
  | .isADirectory => some LinuxSyscall.Errno.EISDIR
  | .notADirectory => some LinuxSyscall.Errno.ENOTDIR
  | .notEmpty => some LinuxSyscall.Errno.ENOTEMPTY
  | .invalidInput => some LinuxSyscall.Errno.EINVAL
  | .unsupported => some LinuxSyscall.Errno.ENOSYS
  | .wouldBlock => none
  | .ioError => some LinuxSyscall.Errno.EMFILE

private def mkErrScopedOps (kind : FsErrorKind) : Model.ScopedRawFsOpsM IO :=
  let err : FsError := { kind := kind, path := some "/mock", message := s!"injected {reprStr kind}" }
  { mapRawError := Fs.Model.mapRawError
    stat := fun _ _ => pure (.error err)
    readDir := fun _ => pure (.error err)
    createDir := fun _ => pure (.error err)
    removeDir := fun _ => pure (.error err)
    unlinkFile := fun _ => pure (.error err)
    readBytes := fun _ => pure (.error err)
    writeBytes := fun _ _ => pure (.error err)
    createFileNew := fun _ _ => pure (.error err)
    appendText := fun _ _ => pure (.error err)
    rename := fun _ _ => pure (.error err)
    chmod := fun _ _ => pure (.error err)
    symlink := fun _ _ => pure (.error err)
    readLink := fun _ => pure (.error err)
    realPath := fun _ => pure (.error err)
    cwd := pure (.error err)
    monotonicNonce := pure 1
    withFileLock := fun _ _ _ _ => pure (.error err)
    tryWithFileLock := fun _ _ _ _ =>
      if kind == .wouldBlock then pure (.ok none) else pure (.error err) }

private def mkMockApiForKind (kind : FsErrorKind) : FsApi :=
  match errnoForKind kind with
  | some eno =>
    Fs.Internal.mkApiFromScopedRawM
      (Fs.Internal.toScopedRawFsOpsM (SysBridge.mkRawFsOpsM (mkErrFilesOps eno) (pure 1)))
  | none =>
    Fs.Internal.mkApiFromScopedRawM (mkErrScopedOps kind)

private def fsErrorKindName : FsErrorKind → String
  | .notFound => "notFound"
  | .alreadyExists => "alreadyExists"
  | .permissionDenied => "permissionDenied"
  | .isADirectory => "isADirectory"
  | .notADirectory => "notADirectory"
  | .notEmpty => "notEmpty"
  | .invalidInput => "invalidInput"
  | .unsupported => "unsupported"
  | .wouldBlock => "wouldBlock"
  | .ioError => "ioError"

private def runMockErrKinds {α : Type} (kinds : Array FsErrorKind)
    (act : FsApi → IO (Except FsError α)) : IO Unit := do
  for k in kinds do
    Core.assertErrorKindPass (fsErrorKindName k) (·.kind) k
      (← act (mkMockApiForKind k)) s!"mocked {reprStr k}" (fun e => e.message != "")

private def runMockErrKindsScoped {α : Type} (kinds : Array FsErrorKind)
    (act : FsApi → IO (Except FsError α)) : IO Unit := do
  for k in kinds do
    let api := Fs.Internal.mkApiFromScopedRawM (mkErrScopedOps k)
    Core.assertErrorKindPass (fsErrorKindName k) (·.kind) k
      (← act api) s!"mocked scoped {reprStr k}" (fun e => e.message != "")

private def runMockPredKinds (kinds : Array FsErrorKind)
    (act : FsApi → IO (Except FsError Bool)) : IO Unit := do
  for k in kinds do
    Core.assertHandledErrorPass (fsErrorKindName k) false
      (← act (mkMockApiForKind k)) s!"mocked pred {reprStr k}"

private def runMockTryLockWouldBlock : IO Unit := do
  let wbErr : FsError := { kind := .wouldBlock, path := some "/mock/lock", message := "injected wouldBlock" }
  let rawContended : Model.RawFsOpsM IO Unit :=
    { SysBridge.mkRawFsOpsM (mkErrFilesOps LinuxSyscall.Errno.EIO) (pure 1) with
      acquireLock := fun _ _ _ _ => pure (.error wbErr)
      releaseLock := fun _ => pure (.ok ()) }
  let apiContended := Fs.Internal.mkApiFromScopedRawM (Fs.Internal.toScopedRawFsOpsM rawContended)
  assertOkEq (← apiContended.tryWithFileLock "/mock/lock" .exclusive false (pure (.ok ()))) none
    "tryWithFileLock contended wouldBlock returns ok none"
  let rawOk : Model.RawFsOpsM IO Unit :=
    { SysBridge.mkRawFsOpsM (mkErrFilesOps LinuxSyscall.Errno.EIO) (pure 1) with
      acquireLock := fun _ _ _ _ => pure (.ok ())
      releaseLock := fun _ => pure (.ok ()) }
  let apiOk := Fs.Internal.mkApiFromScopedRawM (Fs.Internal.toScopedRawFsOpsM rawOk)
  Core.assertErrorKindPass "wouldBlock" (·.kind) .wouldBlock
    (← apiOk.tryWithFileLock "/mock/lock" .exclusive false (pure (.error wbErr) : IO (Except FsError Unit)))
    "tryWithFileLock propagates action wouldBlock" (fun e => e.message != "")

private def runMockSubtreeKinds (kinds : Array FsErrorKind) : IO Unit := do
  for k in kinds do
    let rawDir :=
      match errnoForKind k with
      | some eno => SysBridge.mkRawDirOpsM (mkErrFilesOps eno) (pure 1)
      | none =>
        { SysBridge.mkRawDirOpsM (mkErrFilesOps LinuxSyscall.Errno.EIO) (pure 1) with
          openDir := fun _ =>
            pure (.error { kind := k, path := some "/mock/root", message := s!"injected {reprStr k}" }) }
    let opener := Fs.Internal.mkSubtreeOpenerM rawDir
    Core.assertErrorKindPass (fsErrorKindName k) (·.kind) k
      (← opener.withSubtree "/mock/root" (fun _ => pure (.ok ())))
      s!"mocked subtree {reprStr k}" (fun e => e.message != "")

/-- Real error-coverage test for `LeanSwe.Fs.withName` returning `.invalidInput`. -/
def err_fs_withName_invalidInput : IO Unit :=
  assertErrKind (Fs.withName "/" "x") .invalidInput "withName invalidInput"

/-- Real error-coverage test for `LeanSwe.Fs.withSuffix` returning `.invalidInput`. -/
def err_fs_withSuffix_invalidInput : IO Unit :=
  assertErrKind (Fs.withSuffix "a/b.txt" "lean") .invalidInput "withSuffix invalidInput"

/-- Real error-coverage test for `LeanSwe.Fs.relativeTo` returning `.invalidInput`. -/
def err_fs_relativeTo_invalidInput : IO Unit :=
  assertErrKind (Fs.relativeTo "/x/y" "/a/b") .invalidInput "relativeTo invalidInput"

/-- Real error-coverage test for `LeanSwe.Fs.readText` on `.notFound`. -/
def err_fs_readText_notFound : IO Unit :=
  runRealNotFound Fs.readText

/-- Real error-coverage test for `LeanSwe.Fs.readText` on `.permissionDenied`. -/
def err_fs_readText_permissionDenied : IO Unit :=
  runRealPermDeniedFile Fs.readText

/-- Real error-coverage test for `LeanSwe.Fs.readText` on `.isADirectory`. -/
def err_fs_readText_isADirectory : IO Unit :=
  runRealIsADir Fs.readText

/-- Real error-coverage test for `LeanSwe.Fs.readText` on `.notADirectory`. -/
def err_fs_readText_notADirectory : IO Unit :=
  runRealNotADirChild Fs.readText

/-- Real error-coverage test for `LeanSwe.Fs.readText` on `.invalidInput`. -/
def err_fs_readText_invalidInput : IO Unit :=
  runRealInvalidNul Fs.readText

/-- Real error-coverage test for `LeanSwe.Fs.readText` on `.ioError`. -/
def err_fs_readText_ioError : IO Unit :=
  runRealEloop Fs.readText

/-- Mocked error-coverage test for `LeanSwe.Fs.readText` covering remaining `FsErrorKind` values. -/
def err_fs_readText_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.readText "/mock/file")

/-- Real error-coverage test for `LeanSwe.Fs.writeText` on `.notFound`. -/
def err_fs_writeText_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.writeText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.writeText` on `.permissionDenied`. -/
def err_fs_writeText_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.writeText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.writeText` on `.isADirectory`. -/
def err_fs_writeText_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.writeText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.writeText` on `.notADirectory`. -/
def err_fs_writeText_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.writeText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.writeText` on `.invalidInput`. -/
def err_fs_writeText_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.writeText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.writeText` on `.ioError`. -/
def err_fs_writeText_ioError : IO Unit :=
  runRealEloop (fun p => Fs.writeText p "x")

/-- Mocked error-coverage test for `LeanSwe.Fs.writeText` covering remaining `FsErrorKind` values. -/
def err_fs_writeText_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.writeText "/mock/file" "x")

/-- Real error-coverage test for `LeanSwe.Fs.appendText` on `.notFound`. -/
def err_fs_appendText_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.appendText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.appendText` on `.permissionDenied`. -/
def err_fs_appendText_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.appendText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.appendText` on `.isADirectory`. -/
def err_fs_appendText_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.appendText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.appendText` on `.notADirectory`. -/
def err_fs_appendText_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.appendText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.appendText` on `.invalidInput`. -/
def err_fs_appendText_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.appendText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.appendText` on `.ioError`. -/
def err_fs_appendText_ioError : IO Unit :=
  runRealEloop (fun p => Fs.appendText p "x")

/-- Mocked error-coverage test for `LeanSwe.Fs.appendText` covering remaining `FsErrorKind` values. -/
def err_fs_appendText_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.appendText "/mock/file" "x")

/-- Real error-coverage test for `LeanSwe.Fs.readBytes` on `.notFound`. -/
def err_fs_readBytes_notFound : IO Unit :=
  runRealNotFound Fs.readBytes

/-- Real error-coverage test for `LeanSwe.Fs.readBytes` on `.permissionDenied`. -/
def err_fs_readBytes_permissionDenied : IO Unit :=
  runRealPermDeniedFile Fs.readBytes

/-- Real error-coverage test for `LeanSwe.Fs.readBytes` on `.isADirectory`. -/
def err_fs_readBytes_isADirectory : IO Unit :=
  runRealIsADir Fs.readBytes

/-- Real error-coverage test for `LeanSwe.Fs.readBytes` on `.notADirectory`. -/
def err_fs_readBytes_notADirectory : IO Unit :=
  runRealNotADirChild Fs.readBytes

/-- Real error-coverage test for `LeanSwe.Fs.readBytes` on `.invalidInput`. -/
def err_fs_readBytes_invalidInput : IO Unit :=
  runRealInvalidNul Fs.readBytes

/-- Real error-coverage test for `LeanSwe.Fs.readBytes` on `.ioError`. -/
def err_fs_readBytes_ioError : IO Unit :=
  runRealEloop Fs.readBytes

/-- Mocked error-coverage test for `LeanSwe.Fs.readBytes` covering remaining `FsErrorKind` values. -/
def err_fs_readBytes_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.readBytes "/mock/file")

/-- Real error-coverage test for `LeanSwe.Fs.writeBytes` on `.notFound`. -/
def err_fs_writeBytes_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.writeBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.writeBytes` on `.permissionDenied`. -/
def err_fs_writeBytes_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.writeBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.writeBytes` on `.isADirectory`. -/
def err_fs_writeBytes_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.writeBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.writeBytes` on `.notADirectory`. -/
def err_fs_writeBytes_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.writeBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.writeBytes` on `.invalidInput`. -/
def err_fs_writeBytes_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.writeBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.writeBytes` on `.ioError`. -/
def err_fs_writeBytes_ioError : IO Unit :=
  runRealEloop (fun p => Fs.writeBytes p (ByteArray.mk #[1]))

/-- Mocked error-coverage test for `LeanSwe.Fs.writeBytes` covering remaining `FsErrorKind` values. -/
def err_fs_writeBytes_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.writeBytes "/mock/file" (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteBytes` on `.notFound`. -/
def err_fs_atomicWriteBytes_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.atomicWriteBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteBytes` on `.permissionDenied`. -/
def err_fs_atomicWriteBytes_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.atomicWriteBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteBytes` on `.isADirectory`. -/
def err_fs_atomicWriteBytes_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.atomicWriteBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteBytes` on `.notADirectory`. -/
def err_fs_atomicWriteBytes_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.atomicWriteBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteBytes` on `.invalidInput`. -/
def err_fs_atomicWriteBytes_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.atomicWriteBytes p (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteBytes` on `.ioError`. -/
def err_fs_atomicWriteBytes_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.atomicWriteBytes p (ByteArray.mk #[1]))

/-- Mocked error-coverage test for `LeanSwe.Fs.atomicWriteBytes` covering remaining `FsErrorKind` values. -/
def err_fs_atomicWriteBytes_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.atomicWriteBytes "/mock/file" (ByteArray.mk #[1]))

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteText` on `.notFound`. -/
def err_fs_atomicWriteText_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.atomicWriteText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteText` on `.permissionDenied`. -/
def err_fs_atomicWriteText_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.atomicWriteText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteText` on `.isADirectory`. -/
def err_fs_atomicWriteText_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.atomicWriteText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteText` on `.notADirectory`. -/
def err_fs_atomicWriteText_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.atomicWriteText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteText` on `.invalidInput`. -/
def err_fs_atomicWriteText_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.atomicWriteText p "x")

/-- Real error-coverage test for `LeanSwe.Fs.atomicWriteText` on `.ioError`. -/
def err_fs_atomicWriteText_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.atomicWriteText p "x")

/-- Mocked error-coverage test for `LeanSwe.Fs.atomicWriteText` covering remaining `FsErrorKind` values. -/
def err_fs_atomicWriteText_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.atomicWriteText "/mock/file" "x")

/-- Real error-coverage test for `LeanSwe.Fs.touch` on `.notFound`. -/
def err_fs_touch_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.touch p true)

/-- Real error-coverage test for `LeanSwe.Fs.touch` on `.alreadyExists`. -/
def err_fs_touch_alreadyExists : IO Unit :=
  runRealExistingFileErr .alreadyExists (fun p => Fs.touch p false)

/-- Real error-coverage test for `LeanSwe.Fs.touch` on `.permissionDenied`. -/
def err_fs_touch_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.touch p true)

/-- Real error-coverage test for `LeanSwe.Fs.touch` on `.isADirectory`. -/
def err_fs_touch_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.touch p true)

/-- Real error-coverage test for `LeanSwe.Fs.touch` on `.notADirectory`. -/
def err_fs_touch_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.touch p true)

/-- Real error-coverage test for `LeanSwe.Fs.touch` on `.invalidInput`. -/
def err_fs_touch_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.touch p true)

/-- Real error-coverage test for `LeanSwe.Fs.touch` on `.ioError`. -/
def err_fs_touch_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.touch p true)

/-- Mocked error-coverage test for `LeanSwe.Fs.touch` covering remaining `FsErrorKind` values. -/
def err_fs_touch_mocked : IO Unit :=
  runMockErrKinds #[.notEmpty, .unsupported, .wouldBlock] (fun api => api.touch "/mock/file" false)

/-- Real error-coverage test for `LeanSwe.Fs.mkdir` on `.notFound`. -/
def err_fs_mkdir_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.mkdir p false false)

/-- Real error-coverage test for `LeanSwe.Fs.mkdir` on `.alreadyExists`. -/
def err_fs_mkdir_alreadyExists : IO Unit :=
  runRealExistingDirErr .alreadyExists (fun p => Fs.mkdir p false false)

/-- Real error-coverage test for `LeanSwe.Fs.mkdir` on `.permissionDenied`. -/
def err_fs_mkdir_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.mkdir p false false)

/-- Real error-coverage test for `LeanSwe.Fs.mkdir` on `.notADirectory`. -/
def err_fs_mkdir_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.mkdir p false false)

/-- Real error-coverage test for `LeanSwe.Fs.mkdir` on `.invalidInput`. -/
def err_fs_mkdir_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.mkdir p false false)

/-- Real error-coverage test for `LeanSwe.Fs.mkdir` on `.ioError`. -/
def err_fs_mkdir_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.mkdir p false false)

/-- Mocked error-coverage test for `LeanSwe.Fs.mkdir` covering remaining `FsErrorKind` values. -/
def err_fs_mkdir_mocked : IO Unit :=
  runMockErrKinds #[.isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.mkdir "/mock/dir" false false)

/-- Real error-coverage test for `LeanSwe.Fs.unlink` on `.notFound`. -/
def err_fs_unlink_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.unlink p false)

/-- Real error-coverage test for `LeanSwe.Fs.unlink` on `.permissionDenied`. -/
def err_fs_unlink_permissionDenied : IO Unit :=
  runRealPermDeniedExistingChild (fun p => Fs.unlink p false)

/-- Real error-coverage test for `LeanSwe.Fs.unlink` on `.isADirectory`. -/
def err_fs_unlink_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.unlink p false)

/-- Real error-coverage test for `LeanSwe.Fs.unlink` on `.notADirectory`. -/
def err_fs_unlink_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.unlink p false)

/-- Real error-coverage test for `LeanSwe.Fs.unlink` on `.invalidInput`. -/
def err_fs_unlink_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.unlink p false)

/-- Real error-coverage test for `LeanSwe.Fs.unlink` on `.ioError`. -/
def err_fs_unlink_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.unlink p false)

/-- Mocked error-coverage test for `LeanSwe.Fs.unlink` covering remaining `FsErrorKind` values. -/
def err_fs_unlink_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.unlink "/mock/file" false)

/-- Real error-coverage test for `LeanSwe.Fs.rmdir` on `.notFound`. -/
def err_fs_rmdir_notFound : IO Unit :=
  runRealNotFound Fs.rmdir

/-- Real error-coverage test for `LeanSwe.Fs.rmdir` on `.permissionDenied`. -/
def err_fs_rmdir_permissionDenied : IO Unit :=
  runRealPermDeniedExistingSubdir Fs.rmdir

/-- Real error-coverage test for `LeanSwe.Fs.rmdir` on `.notADirectory`. -/
def err_fs_rmdir_notADirectory : IO Unit :=
  runRealNotADirFile Fs.rmdir

/-- Real error-coverage test for `LeanSwe.Fs.rmdir` on `.notEmpty`. -/
def err_fs_rmdir_notEmpty : IO Unit :=
  runRealNonEmptyDirErr .notEmpty Fs.rmdir

/-- Real error-coverage test for `LeanSwe.Fs.rmdir` on `.invalidInput`. -/
def err_fs_rmdir_invalidInput : IO Unit :=
  runRealInvalidNul Fs.rmdir

/-- Real error-coverage test for `LeanSwe.Fs.rmdir` on `.ioError`. -/
def err_fs_rmdir_ioError : IO Unit :=
  runRealEloopChild Fs.rmdir

/-- Mocked error-coverage test for `LeanSwe.Fs.rmdir` covering remaining `FsErrorKind` values. -/
def err_fs_rmdir_mocked : IO Unit :=
  do
    runMockErrKinds #[.isADirectory, .unsupported] (fun api => api.rmdir "/mock/dir")
    runMockErrKindsScoped #[.alreadyExists, .wouldBlock] (fun api => api.rmdir "/mock/dir")

/-- Real error-coverage test for `LeanSwe.Fs.rmtree` on `.notFound`. -/
def err_fs_rmtree_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.rmtree p false)

/-- Real error-coverage test for `LeanSwe.Fs.rmtree` on `.permissionDenied`. -/
def err_fs_rmtree_permissionDenied : IO Unit :=
  runRealPermDeniedNonEmptyDir (fun p => Fs.rmtree p false)

/-- Real error-coverage test for `LeanSwe.Fs.rmtree` on `.notADirectory`. -/
def err_fs_rmtree_notADirectory : IO Unit :=
  runRealNotADirFile (fun p => Fs.rmtree p false)

/-- Real error-coverage test for `LeanSwe.Fs.rmtree` on `.invalidInput`. -/
def err_fs_rmtree_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.rmtree p false)

/-- Real error-coverage test for `LeanSwe.Fs.rmtree` on `.ioError`. -/
def err_fs_rmtree_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.rmtree p false)

/-- Mocked error-coverage test for `LeanSwe.Fs.rmtree` covering remaining `FsErrorKind` values. -/
def err_fs_rmtree_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.rmtree "/mock/dir" false)

/-- Real error-coverage test for `LeanSwe.Fs.rename` on `.notFound`. -/
def err_fs_rename_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.rename p (p ++ "_dst"))

/-- Real error-coverage test for `LeanSwe.Fs.rename` on `.permissionDenied`. -/
def err_fs_rename_permissionDenied : IO Unit :=
  runRealPermDeniedExistingChild (fun p => Fs.rename p (p ++ "_dst"))

/-- Real error-coverage test for `LeanSwe.Fs.rename` on `.isADirectory`. -/
def err_fs_rename_isADirectory : IO Unit :=
  runRealRenameFileOntoDir

/-- Real error-coverage test for `LeanSwe.Fs.rename` on `.notADirectory`. -/
def err_fs_rename_notADirectory : IO Unit :=
  runRealRenameDirOntoFile

/-- Real error-coverage test for `LeanSwe.Fs.rename` on `.notEmpty`. -/
def err_fs_rename_notEmpty : IO Unit :=
  runRealRenameDirOntoNonEmptyDir

/-- Real error-coverage test for `LeanSwe.Fs.rename` on `.invalidInput`. -/
def err_fs_rename_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.rename p "/tmp/unused_dst")

/-- Real error-coverage test for `LeanSwe.Fs.rename` on `.ioError`. -/
def err_fs_rename_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.rename p (p ++ "_dst"))

/-- Mocked error-coverage test for `LeanSwe.Fs.rename` covering remaining `FsErrorKind` values. -/
def err_fs_rename_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .unsupported, .wouldBlock] (fun api => api.rename "/mock/src" "/mock/dst")

/-- Real error-coverage test for `LeanSwe.Fs.copyFile` on `.notFound`. -/
def err_fs_copyFile_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.copyFile p (p ++ "_dst"))

/-- Real error-coverage test for `LeanSwe.Fs.copyFile` on `.permissionDenied`. -/
def err_fs_copyFile_permissionDenied : IO Unit :=
  runRealPermDeniedFile (fun p => Fs.copyFile p (p ++ "_dst"))

/-- Real error-coverage test for `LeanSwe.Fs.copyFile` on `.isADirectory`. -/
def err_fs_copyFile_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.copyFile p (p ++ "_dst"))

/-- Real error-coverage test for `LeanSwe.Fs.copyFile` on `.notADirectory`. -/
def err_fs_copyFile_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.copyFile p (p ++ "_dst"))

/-- Real error-coverage test for `LeanSwe.Fs.copyFile` on `.invalidInput`. -/
def err_fs_copyFile_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.copyFile p "/tmp/unused_dst")

/-- Real error-coverage test for `LeanSwe.Fs.copyFile` on `.ioError`. -/
def err_fs_copyFile_ioError : IO Unit :=
  runRealEloop (fun p => Fs.copyFile p (p ++ "_dst"))

/-- Mocked error-coverage test for `LeanSwe.Fs.copyFile` covering remaining `FsErrorKind` values. -/
def err_fs_copyFile_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock] (fun api => api.copyFile "/mock/src" "/mock/dst")

/-- Real error-coverage test for `LeanSwe.Fs.copyTree` on `.notFound`. -/
def err_fs_copyTree_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.copyTree p (p ++ "_dst") false)

/-- Real error-coverage test for `LeanSwe.Fs.copyTree` on `.alreadyExists`. -/
def err_fs_copyTree_alreadyExists : IO Unit :=
  runRealCopyTreeExistingDst

/-- Real error-coverage test for `LeanSwe.Fs.copyTree` on `.permissionDenied`. -/
def err_fs_copyTree_permissionDenied : IO Unit :=
  runRealPermDeniedDir (fun p => Fs.copyTree p (p ++ "_dst") false)

/-- Real error-coverage test for `LeanSwe.Fs.copyTree` on `.notADirectory`. -/
def err_fs_copyTree_notADirectory : IO Unit :=
  runRealNotADirFile (fun p => Fs.copyTree p (p ++ "_dst") false)

/-- Real error-coverage test for `LeanSwe.Fs.copyTree` on `.invalidInput`. -/
def err_fs_copyTree_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.copyTree p "/tmp/unused_dst" false)

/-- Real error-coverage test for `LeanSwe.Fs.copyTree` on `.ioError`. -/
def err_fs_copyTree_ioError : IO Unit :=
  runRealEloop (fun p => Fs.copyTree p (p ++ "_dst") false)

/-- Mocked error-coverage test for `LeanSwe.Fs.copyTree` covering remaining `FsErrorKind` values. -/
def err_fs_copyTree_mocked : IO Unit :=
  runMockErrKinds #[.isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.copyTree "/mock/src" "/mock/dst" false)

/-- Real error-coverage test for `LeanSwe.Fs.pathExists` on `.notFound`. -/
def err_fs_pathExists_notFound : IO Unit :=
  runRealPredNotFound Fs.pathExists

/-- Real error-coverage test for `LeanSwe.Fs.pathExists` on `.permissionDenied`. -/
def err_fs_pathExists_permissionDenied : IO Unit :=
  runRealPredPermDenied Fs.pathExists

/-- Real error-coverage test for `LeanSwe.Fs.pathExists` on `.notADirectory`. -/
def err_fs_pathExists_notADirectory : IO Unit :=
  runRealPredNotADir Fs.pathExists

/-- Real error-coverage test for `LeanSwe.Fs.pathExists` on `.invalidInput`. -/
def err_fs_pathExists_invalidInput : IO Unit :=
  runRealPredInvalidNul Fs.pathExists

/-- Real error-coverage test for `LeanSwe.Fs.pathExists` on `.ioError`. -/
def err_fs_pathExists_ioError : IO Unit :=
  runRealPredEloop Fs.pathExists

/-- Mocked error-coverage test for `LeanSwe.Fs.pathExists` covering remaining `FsErrorKind` values. -/
def err_fs_pathExists_mocked : IO Unit :=
  runMockPredKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.pathExists "/mock/path")

/-- Real error-coverage test for `LeanSwe.Fs.isFile` on `.notFound`. -/
def err_fs_isFile_notFound : IO Unit :=
  runRealPredNotFound Fs.isFile

/-- Real error-coverage test for `LeanSwe.Fs.isFile` on `.permissionDenied`. -/
def err_fs_isFile_permissionDenied : IO Unit :=
  runRealPredPermDenied Fs.isFile

/-- Real error-coverage test for `LeanSwe.Fs.isFile` on `.notADirectory`. -/
def err_fs_isFile_notADirectory : IO Unit :=
  runRealPredNotADir Fs.isFile

/-- Real error-coverage test for `LeanSwe.Fs.isFile` on `.invalidInput`. -/
def err_fs_isFile_invalidInput : IO Unit :=
  runRealPredInvalidNul Fs.isFile

/-- Real error-coverage test for `LeanSwe.Fs.isFile` on `.ioError`. -/
def err_fs_isFile_ioError : IO Unit :=
  runRealPredEloop Fs.isFile

/-- Mocked error-coverage test for `LeanSwe.Fs.isFile` covering remaining `FsErrorKind` values. -/
def err_fs_isFile_mocked : IO Unit :=
  runMockPredKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.isFile "/mock/path")

/-- Real error-coverage test for `LeanSwe.Fs.isDir` on `.notFound`. -/
def err_fs_isDir_notFound : IO Unit :=
  runRealPredNotFound Fs.isDir

/-- Real error-coverage test for `LeanSwe.Fs.isDir` on `.permissionDenied`. -/
def err_fs_isDir_permissionDenied : IO Unit :=
  runRealPredPermDenied Fs.isDir

/-- Real error-coverage test for `LeanSwe.Fs.isDir` on `.notADirectory`. -/
def err_fs_isDir_notADirectory : IO Unit :=
  runRealPredNotADir Fs.isDir

/-- Real error-coverage test for `LeanSwe.Fs.isDir` on `.invalidInput`. -/
def err_fs_isDir_invalidInput : IO Unit :=
  runRealPredInvalidNul Fs.isDir

/-- Real error-coverage test for `LeanSwe.Fs.isDir` on `.ioError`. -/
def err_fs_isDir_ioError : IO Unit :=
  runRealPredEloop Fs.isDir

/-- Mocked error-coverage test for `LeanSwe.Fs.isDir` covering remaining `FsErrorKind` values. -/
def err_fs_isDir_mocked : IO Unit :=
  runMockPredKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.isDir "/mock/path")

/-- Real error-coverage test for `LeanSwe.Fs.isSymlink` on `.notFound`. -/
def err_fs_isSymlink_notFound : IO Unit :=
  runRealPredNotFound Fs.isSymlink

/-- Real error-coverage test for `LeanSwe.Fs.isSymlink` on `.permissionDenied`. -/
def err_fs_isSymlink_permissionDenied : IO Unit :=
  runRealPredPermDenied Fs.isSymlink

/-- Real error-coverage test for `LeanSwe.Fs.isSymlink` on `.notADirectory`. -/
def err_fs_isSymlink_notADirectory : IO Unit :=
  runRealPredNotADir Fs.isSymlink

/-- Real error-coverage test for `LeanSwe.Fs.isSymlink` on `.invalidInput`. -/
def err_fs_isSymlink_invalidInput : IO Unit :=
  runRealPredInvalidNul Fs.isSymlink

/-- Real error-coverage test for `LeanSwe.Fs.isSymlink` on `.ioError`. -/
def err_fs_isSymlink_ioError : IO Unit :=
  runRealPredEloop Fs.isSymlink

/-- Mocked error-coverage test for `LeanSwe.Fs.isSymlink` covering remaining `FsErrorKind` values. -/
def err_fs_isSymlink_mocked : IO Unit :=
  runMockPredKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.isSymlink "/mock/path")

/-- Real error-coverage test for `LeanSwe.Fs.stat` on `.notFound`. -/
def err_fs_stat_notFound : IO Unit :=
  runRealNotFound Fs.stat

/-- Real error-coverage test for `LeanSwe.Fs.stat` on `.permissionDenied`. -/
def err_fs_stat_permissionDenied : IO Unit :=
  runRealPermDeniedDirChild Fs.stat

/-- Real error-coverage test for `LeanSwe.Fs.stat` on `.notADirectory`. -/
def err_fs_stat_notADirectory : IO Unit :=
  runRealNotADirChild Fs.stat

/-- Real error-coverage test for `LeanSwe.Fs.stat` on `.invalidInput`. -/
def err_fs_stat_invalidInput : IO Unit :=
  runRealInvalidNul Fs.stat

/-- Real error-coverage test for `LeanSwe.Fs.stat` on `.ioError`. -/
def err_fs_stat_ioError : IO Unit :=
  runRealEloop Fs.stat

/-- Mocked error-coverage test for `LeanSwe.Fs.stat` covering remaining `FsErrorKind` values. -/
def err_fs_stat_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.stat "/mock/path")

/-- Real error-coverage test for `LeanSwe.Fs.lstat` on `.notFound`. -/
def err_fs_lstat_notFound : IO Unit :=
  runRealNotFound Fs.lstat

/-- Real error-coverage test for `LeanSwe.Fs.lstat` on `.permissionDenied`. -/
def err_fs_lstat_permissionDenied : IO Unit :=
  runRealPermDeniedDirChild Fs.lstat

/-- Real error-coverage test for `LeanSwe.Fs.lstat` on `.notADirectory`. -/
def err_fs_lstat_notADirectory : IO Unit :=
  runRealNotADirChild Fs.lstat

/-- Real error-coverage test for `LeanSwe.Fs.lstat` on `.invalidInput`. -/
def err_fs_lstat_invalidInput : IO Unit :=
  runRealInvalidNul Fs.lstat

/-- Real error-coverage test for `LeanSwe.Fs.lstat` on `.ioError`. -/
def err_fs_lstat_ioError : IO Unit :=
  runRealEloopChild Fs.lstat

/-- Mocked error-coverage test for `LeanSwe.Fs.lstat` covering remaining `FsErrorKind` values. -/
def err_fs_lstat_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.lstat "/mock/path")

/-- Real error-coverage test for `LeanSwe.Fs.chmod` on `.notFound`. -/
def err_fs_chmod_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.chmod p 0o644)

/-- Real error-coverage test for `LeanSwe.Fs.chmod` on `.permissionDenied`. -/
def err_fs_chmod_permissionDenied : IO Unit :=
  runRealPermDeniedDirChild (fun p => Fs.chmod p 0o644)

/-- Real error-coverage test for `LeanSwe.Fs.chmod` on `.notADirectory`. -/
def err_fs_chmod_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.chmod p 0o644)

/-- Real error-coverage test for `LeanSwe.Fs.chmod` on `.invalidInput`. -/
def err_fs_chmod_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.chmod p 0o644)

/-- Real error-coverage test for `LeanSwe.Fs.chmod` on `.ioError`. -/
def err_fs_chmod_ioError : IO Unit :=
  runRealEloop (fun p => Fs.chmod p 0o644)

/-- Mocked error-coverage test for `LeanSwe.Fs.chmod` covering remaining `FsErrorKind` values. -/
def err_fs_chmod_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.chmod "/mock/path" 0o644)

/-- Real error-coverage test for `LeanSwe.Fs.symlink` on `.notFound`. -/
def err_fs_symlink_notFound : IO Unit :=
  runRealNotFoundChild (fun p => Fs.symlink "target" p)

/-- Real error-coverage test for `LeanSwe.Fs.symlink` on `.alreadyExists`. -/
def err_fs_symlink_alreadyExists : IO Unit :=
  runRealExistingFileErr .alreadyExists (fun p => Fs.symlink "target" p)

/-- Real error-coverage test for `LeanSwe.Fs.symlink` on `.permissionDenied`. -/
def err_fs_symlink_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.symlink "target" p)

/-- Real error-coverage test for `LeanSwe.Fs.symlink` on `.notADirectory`. -/
def err_fs_symlink_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.symlink "target" p)

/-- Real error-coverage test for `LeanSwe.Fs.symlink` on `.invalidInput`. -/
def err_fs_symlink_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.symlink "target" p)

/-- Real error-coverage test for `LeanSwe.Fs.symlink` on `.ioError`. -/
def err_fs_symlink_ioError : IO Unit :=
  runRealEloopChild (fun p => Fs.symlink "target" p)

/-- Mocked error-coverage test for `LeanSwe.Fs.symlink` covering remaining `FsErrorKind` values. -/
def err_fs_symlink_mocked : IO Unit :=
  runMockErrKinds #[.isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.symlink "target" "/mock/lnk")

/-- Real error-coverage test for `LeanSwe.Fs.readLink` on `.notFound`. -/
def err_fs_readLink_notFound : IO Unit :=
  runRealNotFound Fs.readLink

/-- Real error-coverage test for `LeanSwe.Fs.readLink` on `.permissionDenied`. -/
def err_fs_readLink_permissionDenied : IO Unit :=
  runRealPermDeniedDirChild Fs.readLink

/-- Real error-coverage test for `LeanSwe.Fs.readLink` on `.notADirectory`. -/
def err_fs_readLink_notADirectory : IO Unit :=
  runRealNotADirChild Fs.readLink

/-- Real error-coverage test for `LeanSwe.Fs.readLink` on `.invalidInput`. -/
def err_fs_readLink_invalidInput : IO Unit :=
  runRealExistingFileErr .invalidInput Fs.readLink

/-- Real error-coverage test for `LeanSwe.Fs.readLink` on `.ioError`. -/
def err_fs_readLink_ioError : IO Unit :=
  runRealEloopChild Fs.readLink

/-- Mocked error-coverage test for `LeanSwe.Fs.readLink` covering remaining `FsErrorKind` values. -/
def err_fs_readLink_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.readLink "/mock/lnk")

/-- Real error-coverage test for `LeanSwe.Fs.resolve` on `.notFound`. -/
def err_fs_resolve_notFound : IO Unit :=
  runRealNotFound Fs.resolve

/-- Real error-coverage test for `LeanSwe.Fs.resolve` on `.permissionDenied`. -/
def err_fs_resolve_permissionDenied : IO Unit :=
  runRealPermDeniedDirChild Fs.resolve

/-- Real error-coverage test for `LeanSwe.Fs.resolve` on `.notADirectory`. -/
def err_fs_resolve_notADirectory : IO Unit :=
  runRealNotADirChild Fs.resolve

/-- Real error-coverage test for `LeanSwe.Fs.resolve` on `.invalidInput`. -/
def err_fs_resolve_invalidInput : IO Unit :=
  runRealInvalidNul Fs.resolve

/-- Real error-coverage test for `LeanSwe.Fs.resolve` on `.ioError`. -/
def err_fs_resolve_ioError : IO Unit :=
  runRealEloop Fs.resolve

/-- Mocked error-coverage test for `LeanSwe.Fs.resolve` covering remaining `FsErrorKind` values. -/
def err_fs_resolve_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.resolve "/mock/path")

/-- Mocked error-coverage test for `LeanSwe.Fs.cwd` covering remaining `FsErrorKind` values. -/
def err_fs_cwd_mocked : IO Unit :=
  runMockErrKinds #[.notFound, .alreadyExists, .permissionDenied, .isADirectory, .notADirectory, .notEmpty, .invalidInput, .unsupported, .wouldBlock, .ioError] (fun api => api.cwd)

/-- Real error-coverage test for `LeanSwe.Fs.listDir` on `.notFound`. -/
def err_fs_listDir_notFound : IO Unit :=
  runRealNotFound Fs.listDir

/-- Real error-coverage test for `LeanSwe.Fs.listDir` on `.permissionDenied`. -/
def err_fs_listDir_permissionDenied : IO Unit :=
  runRealPermDeniedDir Fs.listDir

/-- Real error-coverage test for `LeanSwe.Fs.listDir` on `.notADirectory`. -/
def err_fs_listDir_notADirectory : IO Unit :=
  runRealNotADirFile Fs.listDir

/-- Real error-coverage test for `LeanSwe.Fs.listDir` on `.invalidInput`. -/
def err_fs_listDir_invalidInput : IO Unit :=
  runRealInvalidNul Fs.listDir

/-- Real error-coverage test for `LeanSwe.Fs.listDir` on `.ioError`. -/
def err_fs_listDir_ioError : IO Unit :=
  runRealEloop Fs.listDir

/-- Mocked error-coverage test for `LeanSwe.Fs.listDir` covering remaining `FsErrorKind` values. -/
def err_fs_listDir_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.listDir "/mock/dir")

/-- Real error-coverage test for `LeanSwe.Fs.walk` on `.notFound`. -/
def err_fs_walk_notFound : IO Unit :=
  runRealNotFound Fs.walk

/-- Real error-coverage test for `LeanSwe.Fs.walk` on `.permissionDenied`. -/
def err_fs_walk_permissionDenied : IO Unit :=
  runRealPermDeniedDir Fs.walk

/-- Real error-coverage test for `LeanSwe.Fs.walk` on `.notADirectory`. -/
def err_fs_walk_notADirectory : IO Unit :=
  runRealNotADirFile Fs.walk

/-- Real error-coverage test for `LeanSwe.Fs.walk` on `.invalidInput`. -/
def err_fs_walk_invalidInput : IO Unit :=
  runRealInvalidNul Fs.walk

/-- Real error-coverage test for `LeanSwe.Fs.walk` on `.ioError`. -/
def err_fs_walk_ioError : IO Unit :=
  runRealEloop Fs.walk

/-- Mocked error-coverage test for `LeanSwe.Fs.walk` covering remaining `FsErrorKind` values. -/
def err_fs_walk_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.walk "/mock/dir")

/-- Real error-coverage test for `LeanSwe.Fs.glob` on `.notFound`. -/
def err_fs_glob_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.glob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.glob` on `.permissionDenied`. -/
def err_fs_glob_permissionDenied : IO Unit :=
  runRealPermDeniedDir (fun p => Fs.glob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.glob` on `.notADirectory`. -/
def err_fs_glob_notADirectory : IO Unit :=
  runRealNotADirFile (fun p => Fs.glob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.glob` on `.invalidInput`. -/
def err_fs_glob_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.glob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.glob` on `.ioError`. -/
def err_fs_glob_ioError : IO Unit :=
  runRealEloop (fun p => Fs.glob p "*.txt")

/-- Mocked error-coverage test for `LeanSwe.Fs.glob` covering remaining `FsErrorKind` values. -/
def err_fs_glob_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.glob "/mock/dir" "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.rglob` on `.notFound`. -/
def err_fs_rglob_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.rglob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.rglob` on `.permissionDenied`. -/
def err_fs_rglob_permissionDenied : IO Unit :=
  runRealPermDeniedDir (fun p => Fs.rglob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.rglob` on `.notADirectory`. -/
def err_fs_rglob_notADirectory : IO Unit :=
  runRealNotADirFile (fun p => Fs.rglob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.rglob` on `.invalidInput`. -/
def err_fs_rglob_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.rglob p "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.rglob` on `.ioError`. -/
def err_fs_rglob_ioError : IO Unit :=
  runRealEloop (fun p => Fs.rglob p "*.txt")

/-- Mocked error-coverage test for `LeanSwe.Fs.rglob` covering remaining `FsErrorKind` values. -/
def err_fs_rglob_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock] (fun api => api.rglob "/mock/dir" "*.txt")

/-- Real error-coverage test for `LeanSwe.Fs.withFileLock` on `.notFound`. -/
def err_fs_withFileLock_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.withFileLock p .exclusive false (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withFileLock` on `.permissionDenied`. -/
def err_fs_withFileLock_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.withFileLock p .exclusive true (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withFileLock` on `.isADirectory`. -/
def err_fs_withFileLock_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.withFileLock p .exclusive false (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withFileLock` on `.notADirectory`. -/
def err_fs_withFileLock_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.withFileLock p .exclusive false (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withFileLock` on `.invalidInput`. -/
def err_fs_withFileLock_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.withFileLock p .exclusive false (pure (.ok ())))

/-- Mocked error-coverage test for `LeanSwe.Fs.withFileLock` covering remaining `FsErrorKind` values. -/
def err_fs_withFileLock_mocked : IO Unit :=
  runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .wouldBlock, .ioError] (fun api => api.withFileLock "/mock/lock" .exclusive false (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.tryWithFileLock` on `.notFound`. -/
def err_fs_tryWithFileLock_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.tryWithFileLock p .exclusive false (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.tryWithFileLock` on `.permissionDenied`. -/
def err_fs_tryWithFileLock_permissionDenied : IO Unit :=
  runRealPermDeniedDirWrite (fun p => Fs.tryWithFileLock p .exclusive true (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.tryWithFileLock` on `.isADirectory`. -/
def err_fs_tryWithFileLock_isADirectory : IO Unit :=
  runRealIsADir (fun p => Fs.tryWithFileLock p .exclusive false (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.tryWithFileLock` on `.notADirectory`. -/
def err_fs_tryWithFileLock_notADirectory : IO Unit :=
  runRealNotADirChild (fun p => Fs.tryWithFileLock p .exclusive false (pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.tryWithFileLock` on `.invalidInput`. -/
def err_fs_tryWithFileLock_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.tryWithFileLock p .exclusive false (pure (.ok ())))

/-- Mocked error-coverage test for `LeanSwe.Fs.tryWithFileLock` covering remaining `FsErrorKind` values. -/
def err_fs_tryWithFileLock_mocked : IO Unit :=
  do
    runMockErrKinds #[.alreadyExists, .notEmpty, .unsupported, .ioError] (fun api => api.tryWithFileLock "/mock/lock" .exclusive false (pure (.ok ())))
    runMockTryLockWouldBlock

/-- Real error-coverage test for `LeanSwe.Fs.withSubtree` on `.notFound`. -/
def err_fs_withSubtree_notFound : IO Unit :=
  runRealNotFound (fun p => Fs.withSubtree p (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withSubtree` on `.permissionDenied`. -/
def err_fs_withSubtree_permissionDenied : IO Unit :=
  runRealPermDeniedDir (fun p => Fs.withSubtree p (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withSubtree` on `.notADirectory`. -/
def err_fs_withSubtree_notADirectory : IO Unit :=
  runRealNotADirFile (fun p => Fs.withSubtree p (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withSubtree` on `.invalidInput`. -/
def err_fs_withSubtree_invalidInput : IO Unit :=
  runRealInvalidNul (fun p => Fs.withSubtree p (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Fs.withSubtree` on `.ioError`. -/
def err_fs_withSubtree_ioError : IO Unit :=
  runRealEloop (fun p => Fs.withSubtree p (fun _ => pure (.ok ())))

/-- Mocked error-coverage test for `LeanSwe.Fs.withSubtree` covering remaining `FsErrorKind` values. -/
def err_fs_withSubtree_mocked : IO Unit :=
  runMockSubtreeKinds #[.alreadyExists, .isADirectory, .notEmpty, .unsupported, .wouldBlock]

set_option maxRecDepth 2048 in
/-- Registered error-coverage tests for `LeanSwe.Fs.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  List.toArray (
    { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withName_invalidInput", mode := .real, run := err_fs_withName_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withSuffix_invalidInput", mode := .real, run := err_fs_withSuffix_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_relativeTo_invalidInput", mode := .real, run := err_fs_relativeTo_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readText_notFound", mode := .real, run := err_fs_readText_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readText_permissionDenied", mode := .real, run := err_fs_readText_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readText_isADirectory", mode := .real, run := err_fs_readText_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readText_notADirectory", mode := .real, run := err_fs_readText_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readText_invalidInput", mode := .real, run := err_fs_readText_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readText_ioError", mode := .real, run := err_fs_readText_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readText_mocked", mode := .mocked, run := err_fs_readText_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeText_notFound", mode := .real, run := err_fs_writeText_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeText_permissionDenied", mode := .real, run := err_fs_writeText_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeText_isADirectory", mode := .real, run := err_fs_writeText_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeText_notADirectory", mode := .real, run := err_fs_writeText_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeText_invalidInput", mode := .real, run := err_fs_writeText_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeText_ioError", mode := .real, run := err_fs_writeText_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeText_mocked", mode := .mocked, run := err_fs_writeText_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_appendText_notFound", mode := .real, run := err_fs_appendText_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_appendText_permissionDenied", mode := .real, run := err_fs_appendText_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_appendText_isADirectory", mode := .real, run := err_fs_appendText_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_appendText_notADirectory", mode := .real, run := err_fs_appendText_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_appendText_invalidInput", mode := .real, run := err_fs_appendText_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_appendText_ioError", mode := .real, run := err_fs_appendText_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_appendText_mocked", mode := .mocked, run := err_fs_appendText_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_notFound", mode := .real, run := err_fs_readBytes_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_permissionDenied", mode := .real, run := err_fs_readBytes_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_isADirectory", mode := .real, run := err_fs_readBytes_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_notADirectory", mode := .real, run := err_fs_readBytes_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_invalidInput", mode := .real, run := err_fs_readBytes_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_ioError", mode := .real, run := err_fs_readBytes_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_mocked", mode := .mocked, run := err_fs_readBytes_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_notFound", mode := .real, run := err_fs_writeBytes_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_permissionDenied", mode := .real, run := err_fs_writeBytes_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_isADirectory", mode := .real, run := err_fs_writeBytes_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_notADirectory", mode := .real, run := err_fs_writeBytes_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_invalidInput", mode := .real, run := err_fs_writeBytes_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_ioError", mode := .real, run := err_fs_writeBytes_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_mocked", mode := .mocked, run := err_fs_writeBytes_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_notFound", mode := .real, run := err_fs_atomicWriteBytes_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_permissionDenied", mode := .real, run := err_fs_atomicWriteBytes_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_isADirectory", mode := .real, run := err_fs_atomicWriteBytes_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_notADirectory", mode := .real, run := err_fs_atomicWriteBytes_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_invalidInput", mode := .real, run := err_fs_atomicWriteBytes_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_ioError", mode := .real, run := err_fs_atomicWriteBytes_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_mocked", mode := .mocked, run := err_fs_atomicWriteBytes_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_notFound", mode := .real, run := err_fs_atomicWriteText_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_permissionDenied", mode := .real, run := err_fs_atomicWriteText_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_isADirectory", mode := .real, run := err_fs_atomicWriteText_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_notADirectory", mode := .real, run := err_fs_atomicWriteText_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_invalidInput", mode := .real, run := err_fs_atomicWriteText_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_ioError", mode := .real, run := err_fs_atomicWriteText_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_mocked", mode := .mocked, run := err_fs_atomicWriteText_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_notFound", mode := .real, run := err_fs_touch_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_alreadyExists", mode := .real, run := err_fs_touch_alreadyExists }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_permissionDenied", mode := .real, run := err_fs_touch_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_isADirectory", mode := .real, run := err_fs_touch_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_notADirectory", mode := .real, run := err_fs_touch_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_invalidInput", mode := .real, run := err_fs_touch_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_ioError", mode := .real, run := err_fs_touch_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_touch_mocked", mode := .mocked, run := err_fs_touch_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_notFound", mode := .real, run := err_fs_mkdir_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_alreadyExists", mode := .real, run := err_fs_mkdir_alreadyExists }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_permissionDenied", mode := .real, run := err_fs_mkdir_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_notADirectory", mode := .real, run := err_fs_mkdir_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_invalidInput", mode := .real, run := err_fs_mkdir_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_ioError", mode := .real, run := err_fs_mkdir_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_mocked", mode := .mocked, run := err_fs_mkdir_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_unlink_notFound", mode := .real, run := err_fs_unlink_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_unlink_permissionDenied", mode := .real, run := err_fs_unlink_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_unlink_isADirectory", mode := .real, run := err_fs_unlink_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_unlink_notADirectory", mode := .real, run := err_fs_unlink_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_unlink_invalidInput", mode := .real, run := err_fs_unlink_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_unlink_ioError", mode := .real, run := err_fs_unlink_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_unlink_mocked", mode := .mocked, run := err_fs_unlink_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_notFound", mode := .real, run := err_fs_rmdir_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_permissionDenied", mode := .real, run := err_fs_rmdir_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_notADirectory", mode := .real, run := err_fs_rmdir_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_notEmpty", mode := .real, run := err_fs_rmdir_notEmpty }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_invalidInput", mode := .real, run := err_fs_rmdir_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_ioError", mode := .real, run := err_fs_rmdir_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_mocked", mode := .mocked, run := err_fs_rmdir_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_notFound", mode := .real, run := err_fs_rmtree_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_permissionDenied", mode := .real, run := err_fs_rmtree_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_notADirectory", mode := .real, run := err_fs_rmtree_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_invalidInput", mode := .real, run := err_fs_rmtree_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_ioError", mode := .real, run := err_fs_rmtree_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_mocked", mode := .mocked, run := err_fs_rmtree_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_notFound", mode := .real, run := err_fs_rename_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_permissionDenied", mode := .real, run := err_fs_rename_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_isADirectory", mode := .real, run := err_fs_rename_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_notADirectory", mode := .real, run := err_fs_rename_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_notEmpty", mode := .real, run := err_fs_rename_notEmpty }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_invalidInput", mode := .real, run := err_fs_rename_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_ioError", mode := .real, run := err_fs_rename_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rename_mocked", mode := .mocked, run := err_fs_rename_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_notFound", mode := .real, run := err_fs_copyFile_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_permissionDenied", mode := .real, run := err_fs_copyFile_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_isADirectory", mode := .real, run := err_fs_copyFile_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_notADirectory", mode := .real, run := err_fs_copyFile_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_invalidInput", mode := .real, run := err_fs_copyFile_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_ioError", mode := .real, run := err_fs_copyFile_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_mocked", mode := .mocked, run := err_fs_copyFile_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_notFound", mode := .real, run := err_fs_copyTree_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_alreadyExists", mode := .real, run := err_fs_copyTree_alreadyExists }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_permissionDenied", mode := .real, run := err_fs_copyTree_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_notADirectory", mode := .real, run := err_fs_copyTree_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_invalidInput", mode := .real, run := err_fs_copyTree_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_ioError", mode := .real, run := err_fs_copyTree_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_mocked", mode := .mocked, run := err_fs_copyTree_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_notFound", mode := .real, run := err_fs_pathExists_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_permissionDenied", mode := .real, run := err_fs_pathExists_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_notADirectory", mode := .real, run := err_fs_pathExists_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_invalidInput", mode := .real, run := err_fs_pathExists_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_ioError", mode := .real, run := err_fs_pathExists_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_mocked", mode := .mocked, run := err_fs_pathExists_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isFile_notFound", mode := .real, run := err_fs_isFile_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isFile_permissionDenied", mode := .real, run := err_fs_isFile_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isFile_notADirectory", mode := .real, run := err_fs_isFile_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isFile_invalidInput", mode := .real, run := err_fs_isFile_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isFile_ioError", mode := .real, run := err_fs_isFile_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isFile_mocked", mode := .mocked, run := err_fs_isFile_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isDir_notFound", mode := .real, run := err_fs_isDir_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isDir_permissionDenied", mode := .real, run := err_fs_isDir_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isDir_notADirectory", mode := .real, run := err_fs_isDir_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isDir_invalidInput", mode := .real, run := err_fs_isDir_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isDir_ioError", mode := .real, run := err_fs_isDir_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isDir_mocked", mode := .mocked, run := err_fs_isDir_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_notFound", mode := .real, run := err_fs_isSymlink_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_permissionDenied", mode := .real, run := err_fs_isSymlink_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_notADirectory", mode := .real, run := err_fs_isSymlink_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_invalidInput", mode := .real, run := err_fs_isSymlink_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_ioError", mode := .real, run := err_fs_isSymlink_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_mocked", mode := .mocked, run := err_fs_isSymlink_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_stat_notFound", mode := .real, run := err_fs_stat_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_stat_permissionDenied", mode := .real, run := err_fs_stat_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_stat_notADirectory", mode := .real, run := err_fs_stat_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_stat_invalidInput", mode := .real, run := err_fs_stat_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_stat_ioError", mode := .real, run := err_fs_stat_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_stat_mocked", mode := .mocked, run := err_fs_stat_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_lstat_notFound", mode := .real, run := err_fs_lstat_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_lstat_permissionDenied", mode := .real, run := err_fs_lstat_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_lstat_notADirectory", mode := .real, run := err_fs_lstat_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_lstat_invalidInput", mode := .real, run := err_fs_lstat_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_lstat_ioError", mode := .real, run := err_fs_lstat_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_lstat_mocked", mode := .mocked, run := err_fs_lstat_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_chmod_notFound", mode := .real, run := err_fs_chmod_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_chmod_permissionDenied", mode := .real, run := err_fs_chmod_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_chmod_notADirectory", mode := .real, run := err_fs_chmod_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_chmod_invalidInput", mode := .real, run := err_fs_chmod_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_chmod_ioError", mode := .real, run := err_fs_chmod_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_chmod_mocked", mode := .mocked, run := err_fs_chmod_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_symlink_notFound", mode := .real, run := err_fs_symlink_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_symlink_alreadyExists", mode := .real, run := err_fs_symlink_alreadyExists }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_symlink_permissionDenied", mode := .real, run := err_fs_symlink_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_symlink_notADirectory", mode := .real, run := err_fs_symlink_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_symlink_invalidInput", mode := .real, run := err_fs_symlink_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_symlink_ioError", mode := .real, run := err_fs_symlink_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_symlink_mocked", mode := .mocked, run := err_fs_symlink_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readLink_notFound", mode := .real, run := err_fs_readLink_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readLink_permissionDenied", mode := .real, run := err_fs_readLink_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readLink_notADirectory", mode := .real, run := err_fs_readLink_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readLink_invalidInput", mode := .real, run := err_fs_readLink_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readLink_ioError", mode := .real, run := err_fs_readLink_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_readLink_mocked", mode := .mocked, run := err_fs_readLink_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_resolve_notFound", mode := .real, run := err_fs_resolve_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_resolve_permissionDenied", mode := .real, run := err_fs_resolve_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_resolve_notADirectory", mode := .real, run := err_fs_resolve_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_resolve_invalidInput", mode := .real, run := err_fs_resolve_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_resolve_ioError", mode := .real, run := err_fs_resolve_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_resolve_mocked", mode := .mocked, run := err_fs_resolve_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked", mode := .mocked, run := err_fs_cwd_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_listDir_notFound", mode := .real, run := err_fs_listDir_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_listDir_permissionDenied", mode := .real, run := err_fs_listDir_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_listDir_notADirectory", mode := .real, run := err_fs_listDir_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_listDir_invalidInput", mode := .real, run := err_fs_listDir_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_listDir_ioError", mode := .real, run := err_fs_listDir_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_listDir_mocked", mode := .mocked, run := err_fs_listDir_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_walk_notFound", mode := .real, run := err_fs_walk_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_walk_permissionDenied", mode := .real, run := err_fs_walk_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_walk_notADirectory", mode := .real, run := err_fs_walk_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_walk_invalidInput", mode := .real, run := err_fs_walk_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_walk_ioError", mode := .real, run := err_fs_walk_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_walk_mocked", mode := .mocked, run := err_fs_walk_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_glob_notFound", mode := .real, run := err_fs_glob_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_glob_permissionDenied", mode := .real, run := err_fs_glob_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_glob_notADirectory", mode := .real, run := err_fs_glob_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_glob_invalidInput", mode := .real, run := err_fs_glob_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_glob_ioError", mode := .real, run := err_fs_glob_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_glob_mocked", mode := .mocked, run := err_fs_glob_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rglob_notFound", mode := .real, run := err_fs_rglob_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rglob_permissionDenied", mode := .real, run := err_fs_rglob_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rglob_notADirectory", mode := .real, run := err_fs_rglob_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rglob_invalidInput", mode := .real, run := err_fs_rglob_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rglob_ioError", mode := .real, run := err_fs_rglob_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_rglob_mocked", mode := .mocked, run := err_fs_rglob_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_notFound", mode := .real, run := err_fs_withFileLock_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_permissionDenied", mode := .real, run := err_fs_withFileLock_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_isADirectory", mode := .real, run := err_fs_withFileLock_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_notADirectory", mode := .real, run := err_fs_withFileLock_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_invalidInput", mode := .real, run := err_fs_withFileLock_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_mocked", mode := .mocked, run := err_fs_withFileLock_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_notFound", mode := .real, run := err_fs_tryWithFileLock_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_permissionDenied", mode := .real, run := err_fs_tryWithFileLock_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_isADirectory", mode := .real, run := err_fs_tryWithFileLock_isADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_notADirectory", mode := .real, run := err_fs_tryWithFileLock_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_invalidInput", mode := .real, run := err_fs_tryWithFileLock_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_mocked", mode := .mocked, run := err_fs_tryWithFileLock_mocked }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_notFound", mode := .real, run := err_fs_withSubtree_notFound }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_permissionDenied", mode := .real, run := err_fs_withSubtree_permissionDenied }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_notADirectory", mode := .real, run := err_fs_withSubtree_notADirectory }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_invalidInput", mode := .real, run := err_fs_withSubtree_invalidInput }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_ioError", mode := .real, run := err_fs_withSubtree_ioError }
    :: { testName := "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_mocked", mode := .mocked, run := err_fs_withSubtree_mocked }
    :: []
  )

private def parseOctalUmask (status : String) : Option Nat := Id.run do
  for line in status.splitOn "\n" do
    if line.startsWith "Umask:" then
      let raw := (line.drop "Umask:".length).trimAscii.toString
      if raw.isEmpty then return none
      let mut acc : Nat := 0
      for c in raw.toList do
        if '0' ≤ c && c ≤ '7' then
          acc := acc * 8 + (c.toNat - '0'.toNat)
        else
          return none
      return some acc
  return none

private def testCreationModesAndUmask (tmp : String) : IO Unit := do
  let logRef : IO.Ref (Array (String × UInt32)) ← IO.mkRef #[]
  let nonceRef : IO.Ref Nat ← IO.mkRef 1
  let base := LinuxSyscall.Files.defaultOps
  let spyFiles : LinuxSyscall.Files.FilesOpsM IO LinuxSyscall.RawFd :=
    { base with
      mkdirat := fun dir path mode => do
        logRef.modify (·.push ("mkdirat", mode))
        base.mkdirat dir path mode
      openat := fun dir path flags mode => do
        if flags.creat then
          logRef.modify (·.push ("openat", mode))
        base.openat dir path flags mode }
  let nextNonce : IO Nat := nonceRef.modifyGet fun n => (n, n + 1)
  let spyApi := Fs.Internal.mkApiM (Fs.SysBridge.mkRawFsOpsM spyFiles nextNonce)
  let spyOpener := Fs.Internal.mkSubtreeOpenerM (Fs.SysBridge.mkRawDirOpsM spyFiles nextNonce)
  let spyRoot := Fs.join tmp "mode_spy"
  assertOk (← spyApi.mkdir spyRoot false false) "spy mkdir"
  assertTrue ((← logRef.get) == #[("mkdirat", 0o777)]) "ambient mkdir passes 0o777 to mkdirat"
  logRef.set #[]
  assertOk (← spyApi.writeText (Fs.join spyRoot "wt.txt") "hello") "spy writeText"
  assertTrue ((← logRef.get) == #[("openat", 0o666)]) "ambient writeText passes 0o666 to openat"
  logRef.set #[]
  assertOk (← spyApi.writeBytes (Fs.join spyRoot "wb.bin") ("abc".toUTF8)) "spy writeBytes"
  assertTrue ((← logRef.get) == #[("openat", 0o666)]) "ambient writeBytes passes 0o666 to openat"
  logRef.set #[]
  assertOk (← spyApi.appendText (Fs.join spyRoot "ap.txt") "more") "spy appendText"
  assertTrue ((← logRef.get) == #[("openat", 0o666)]) "ambient appendText passes 0o666 to openat"
  logRef.set #[]
  assertOk (← spyApi.touch (Fs.join spyRoot "tc.txt") true) "spy touch create"
  assertTrue ((← logRef.get) == #[("openat", 0o666)]) "ambient touch create passes 0o666 to openat"
  logRef.set #[]
  assertOk (← spyApi.touch (Fs.join spyRoot "tc.txt") true) "spy touch existing"
  assertTrue ((← logRef.get) == #[("openat", 0o666)]) "ambient touch existing passes 0o666 to openat"
  logRef.set #[]
  assertOk (← spyApi.atomicWriteBytes (Fs.join spyRoot "aw.bin") ("atom".toUTF8)) "spy atomicWriteBytes"
  assertTrue ((← logRef.get) == #[("openat", 0o644)]) "ambient atomicWriteBytes preserves historical 0o644"
  logRef.set #[]
  assertOk (← spyApi.withFileLock (Fs.join spyRoot "lk.lock") .exclusive true (pure (.ok ()))) "spy withFileLock"
  assertTrue ((← logRef.get) == #[("openat", 0o644)]) "ambient withFileLock preserves historical 0o644"
  logRef.set #[]
  let rSubDir ← assertOk (RelPath.parse "subd") "parse subd"
  let rSubFile ← assertOk (RelPath.parse "subf") "parse subf"
  let rSubLock ← assertOk (RelPath.parse "subl") "parse subl"
  assertOk (← spyOpener.withSubtree spyRoot fun sub => do
    match ← sub.mkdir rSubDir false false with
    | .error e => return .error e
    | .ok () =>
      match ← sub.atomicWriteBytes rSubFile ("sub".toUTF8) with
      | .error e => return .error e
      | .ok () => sub.withFileLock rSubLock .exclusive true (pure (.ok ()))) "spy withSubtree"
  assertTrue ((← logRef.get) == #[("mkdirat", 0o755), ("openat", 0o644), ("openat", 0o644)])
    "confined subtree preserves historical 0o755/0o644 modes"
  let status ← assertOk (← Fs.readText "/proc/self/status") "read /proc/self/status for Umask"
  match parseOctalUmask status with
  | none => throw (IO.userError "ASSERTION FAILED: missing Umask field in /proc/self/status")
  | some mask =>
    let expectPerm (baseMode : Nat) : Nat := baseMode &&& (0o777 - (baseMode &&& (mask &&& 0o777)))
    let uRoot := Fs.join tmp "mode_umask"
    assertOk (← Fs.mkdir uRoot false false) "umask Fs.mkdir"
    let stDir ← assertOk (← Fs.stat uRoot) "stat uRoot"
    assertTrue ((stDir.mode &&& 0o777) == expectPerm 0o777)
      s!"Fs.mkdir perm {stDir.mode &&& 0o777} matches 0o777 & ~umask ({expectPerm 0o777})"
    let fWt := Fs.join uRoot "wt.txt"
    assertOk (← Fs.writeText fWt "x") "umask Fs.writeText"
    let stWt ← assertOk (← Fs.stat fWt) "stat fWt"
    assertTrue ((stWt.mode &&& 0o777) == expectPerm 0o666)
      s!"Fs.writeText perm {stWt.mode &&& 0o777} matches 0o666 & ~umask ({expectPerm 0o666})"
    let fAp := Fs.join uRoot "ap.txt"
    assertOk (← Fs.appendText fAp "y") "umask Fs.appendText"
    let stAp ← assertOk (← Fs.stat fAp) "stat fAp"
    assertTrue ((stAp.mode &&& 0o777) == expectPerm 0o666)
      s!"Fs.appendText perm {stAp.mode &&& 0o777} matches 0o666 & ~umask ({expectPerm 0o666})"
    let fAw := Fs.join uRoot "aw.txt"
    assertOk (← Fs.atomicWriteBytes fAw ("z".toUTF8)) "umask Fs.atomicWriteBytes"
    let stAw ← assertOk (← Fs.stat fAw) "stat fAw"
    assertTrue ((stAw.mode &&& 0o777) == expectPerm 0o644)
      s!"Fs.atomicWriteBytes perm {stAw.mode &&& 0o777} matches 0o644 & ~umask ({expectPerm 0o644})"
    let fLk := Fs.join uRoot "lk.lock"
    assertOk (← Fs.withFileLock fLk .exclusive true (pure (.ok ()))) "umask Fs.withFileLock"
    let stLk ← assertOk (← Fs.stat fLk) "stat fLk"
    assertTrue ((stLk.mode &&& 0o777) == expectPerm 0o644)
      s!"Fs.withFileLock perm {stLk.mode &&& 0o777} matches 0o644 & ~umask ({expectPerm 0o644})"
    assertOk (← Fs.withSubtree uRoot fun sub => do
      match ← sub.mkdir rSubDir false false with
      | .error e => return .error e
      | .ok () => sub.atomicWriteBytes rSubFile ("s".toUTF8)) "umask withSubtree"
    let stSubDir ← assertOk (← Fs.stat (Fs.join uRoot "subd")) "stat subd"
    assertTrue ((stSubDir.mode &&& 0o777) == expectPerm 0o755)
      s!"Subtree.mkdir perm {stSubDir.mode &&& 0o777} matches 0o755 & ~umask ({expectPerm 0o755})"
    let stSubFile ← assertOk (← Fs.stat (Fs.join uRoot "subf")) "stat subf"
    assertTrue ((stSubFile.mode &&& 0o777) == expectPerm 0o644)
      s!"Subtree.atomicWriteBytes perm {stSubFile.mode &&& 0o777} matches 0o644 & ~umask ({expectPerm 0o644})"

private def testMkdirToctouRace (tmp : String) : IO Unit := do
  let raceDir := Fs.join tmp "toctou-dir-race"
  let raceFile := Fs.join tmp "toctou-file-race"
  let statCallsRef ← IO.mkRef (0 : Nat)
  let fileStatCallsRef ← IO.mkRef (0 : Nat)
  let dirRacingOps : Model.RawFsOpsM IO LinuxSyscall.RawFd :=
    { SysBridge.defaultOps with
      stat := fun follow p => do
        if p == raceDir then
          let n ← statCallsRef.modifyGet fun c => (c, c + 1)
          if n == 0 then
            return .error { kind := .notFound, path := some p, message := "initial stat before peer mkdir" }
        else if p == raceFile then
          let n ← fileStatCallsRef.modifyGet fun c => (c, c + 1)
          if n == 0 then
            return .error { kind := .notFound, path := some p, message := "initial stat before peer file" }
        SysBridge.defaultOps.stat follow p
      createDir := fun p => do
        if p == raceDir then
          let _ ← Fs.mkdir p false false
          return .error { kind := .alreadyExists, path := some p, message := "simulated concurrent mkdir" }
        else if p == raceFile then
          let _ ← Fs.writeText p "not-a-dir"
          return .error { kind := .alreadyExists, path := some p, message := "simulated concurrent file" }
        else
          SysBridge.defaultOps.createDir p }
  let racingApi := Fs.Internal.mkApiM dirRacingOps
  assertOk (← racingApi.mkdir raceDir true true) "mkdir tolerates concurrent createDir alreadyExists on real dir"
  assertTrue ((← statCallsRef.get) == 2) "mkdir TOCTOU dir race exercised initial and recovery stat"
  assertTrue (← assertOk (← Fs.isDir raceDir) "raceDir isDir") "raceDir created as directory"
  assertErrKind (← racingApi.mkdir raceFile true true) .alreadyExists
    "mkdir rejects concurrent regular file creation on TOCTOU race"
  assertTrue ((← fileStatCallsRef.get) == 2) "mkdir TOCTOU file race exercised initial and recovery stat"

/-- Execute all pure path and real filesystem runtime checks for `LeanSwe.Fs`. -/
def runAll : IO Unit := do
  Core.runRegisteredErrorTests registeredErrorTests
  testPurePaths
  withTempDir fun tmp => do
    let moved ← assertOk (← testFilesAndDirs tmp) "testFilesAndDirs"
    assertOk (← testSymlinksAndGlobs tmp moved) "testSymlinksAndGlobs"
    testLocksSingleProcess tmp
    testLocksMultiProcess tmp
    testAmbientSafety tmp
    testWithSubtree tmp
    testSysBridgeEdgeCases tmp
    testCreationModesAndUmask tmp
    testMkdirToctouRace tmp
  IO.println "PASS: LeanSwe.Fs runtime tests"

end LeanSwe.Fs.RuntimeTests
