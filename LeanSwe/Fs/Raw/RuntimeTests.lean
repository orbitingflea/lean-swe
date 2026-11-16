import LeanSwe.Fs.Raw.Interface

namespace LeanSwe.Fs.Raw.RuntimeTests

open LeanSwe.Fs

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except Raw.FsError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except Raw.FsError α) (expected : Raw.FsErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def runLockTests (tmp : String) : IO Unit := do
  let lockMissing := tmp ++ "/missing.lock"
  assertErrKind (← Raw.acquireLock lockMissing .exclusive false true) .notFound
    "acquireLock missing with createIfMissing=false"

  let lockNew := tmp ++ "/created.lock"
  let hNew ← assertOk (← Raw.acquireLock lockNew .exclusive true true)
    "acquireLock creates missing file"
  assertTrue (hNew.handleId != 0 && hNew.path == lockNew && hNew.mode == .exclusive)
    "acquireLock handle fields"
  let stNew ← assertOk (← Raw.stat false lockNew) "stat created lockfile"
  assertTrue (stNew.kind == .file && stNew.byteSize == 0) "created lockfile is 0 bytes"
  assertErrKind (← Raw.acquireLock lockNew .exclusive false true) .wouldBlock
    "exclusive vs exclusive returns wouldBlock"
  assertErrKind (← Raw.acquireLock lockNew .shared false true) .wouldBlock
    "exclusive vs shared returns wouldBlock"
  assertOk (← Raw.releaseLock hNew) "releaseLock hNew"
  assertErrKind (← Raw.releaseLock hNew) .invalidInput "double releaseLock rejected"

  let lockData := tmp ++ "/data.lock"
  assertOk (← Raw.writeBytes lockData (ByteArray.mk #[9, 8, 7])) "writeBytes data.lock"
  assertOk (← Raw.chmod lockData 0o444) "chmod 0444 data.lock"
  let hRo ← assertOk (← Raw.acquireLock lockData .shared true true)
    "acquireLock 0444 with createIfMissing=true"
  let hRo2 ← assertOk (← Raw.acquireLock lockData .shared false true)
    "acquireLock shared coexistence on 0444"
  assertErrKind (← Raw.acquireLock lockData .exclusive false true) .wouldBlock
    "shared vs exclusive returns wouldBlock"
  assertOk (← Raw.releaseLock hRo) "releaseLock hRo"
  assertErrKind (← Raw.acquireLock lockData .exclusive false true) .wouldBlock
    "still blocked while second shared handle held"
  assertOk (← Raw.releaseLock hRo2) "releaseLock hRo2"
  let hExAfter ← assertOk (← Raw.acquireLock lockData .exclusive false true)
    "exclusive succeeds after all shared released"
  assertOk (← Raw.releaseLock hExAfter) "releaseLock hExAfter"
  let gotData ← assertOk (← Raw.readBytes lockData) "readBytes after lock preserves content"
  assertTrue (gotData == ByteArray.mk #[9, 8, 7]) "lock preserves existing bytes"

  let lockDir := tmp ++ "/lockdir"
  assertOk (← Raw.createDir lockDir) "createDir lockdir"
  assertErrKind (← Raw.acquireLock lockDir .exclusive true true) .isADirectory
    "acquireLock dir fails with isADirectory"
  assertErrKind (← Raw.acquireLock (lockDir ++ "/") .exclusive true true) .invalidInput
    "acquireLock trailing slash fails with invalidInput"
  assertErrKind (← Raw.acquireLock "" .exclusive true true) .invalidInput
    "acquireLock empty path fails with invalidInput"

  let symFile := tmp ++ "/sym_file"
  let symDir := tmp ++ "/sym_dir"
  let symDangling := tmp ++ "/sym_dangling"
  assertOk (← Raw.symlink lockData symFile) "symlink to file"
  assertOk (← Raw.symlink lockDir symDir) "symlink to dir"
  assertOk (← Raw.symlink (tmp ++ "/no_such_target") symDangling) "dangling symlink"
  assertErrKind (← Raw.acquireLock symFile .exclusive false true) .invalidInput
    "acquireLock symlink to file rejected"
  assertErrKind (← Raw.acquireLock symDir .exclusive false true) .invalidInput
    "acquireLock symlink to dir rejected"
  assertErrKind (← Raw.acquireLock (symDir ++ "/") .exclusive false true) .invalidInput
    "acquireLock symlink dir with trailing slash rejected"
  assertErrKind (← Raw.acquireLock symDangling .exclusive true true) .invalidInput
    "acquireLock dangling symlink with createIfMissing=true rejected"

  let fifoPath := tmp ++ "/test.fifo"
  let mkfifoOut ← IO.Process.output { cmd := "mkfifo", args := #[fifoPath] }
  assertTrue (mkfifoOut.exitCode == 0) "mkfifo exitCode 0"
  assertErrKind (← Raw.acquireLock fifoPath .exclusive false true) .invalidInput
    "acquireLock FIFO rejected without blocking"

  assertErrKind (← Raw.releaseLock { handleId := 0, path := lockNew, mode := .exclusive }) .invalidInput
    "releaseLock handleId 0 rejected"
  assertErrKind (← Raw.releaseLock { handleId := 999999, path := lockNew, mode := .exclusive }) .invalidInput
    "releaseLock unknown handleId rejected"
  assertErrKind (← Raw.releaseLock { handleId := 18446744073709551617, path := lockNew, mode := .exclusive }) .invalidInput
    "releaseLock out-of-range handleId rejected"

  assertOk (← Raw.unlinkFile fifoPath) "unlink fifo"
  assertOk (← Raw.unlinkFile symDangling) "unlink symDangling"
  assertOk (← Raw.unlinkFile symDir) "unlink symDir"
  assertOk (← Raw.unlinkFile symFile) "unlink symFile"
  assertOk (← Raw.removeDir lockDir) "removeDir lockDir"
  assertOk (← Raw.chmod lockData 0o644) "chmod 0644 data.lock"
  assertOk (← Raw.unlinkFile lockData) "unlink data.lock"
  assertOk (← Raw.unlinkFile lockNew) "unlink created.lock"

private def waitForFile (path : String) (maxPolls : Nat := 200) : IO Unit := do
  for _ in List.range maxPolls do
    match ← Raw.stat false path with
    | .ok _ => return ()
    | _ => IO.sleep 10
  throw (IO.userError s!"ASSERTION FAILED: timed out waiting for file {path}")

private def runAmbientSafetyTests (tmp : String) : IO Unit := do
  let newFile := tmp ++ "/new_exact.bin"
  let payload := ByteArray.mk #[0, 1, 2, 127, 128, 255]
  assertOk (← Raw.createFileNew newFile payload) "createFileNew creates missing file"
  let stNew ← assertOk (← Raw.stat false newFile) "stat created file"
  assertTrue (stNew.kind == .file && stNew.byteSize == payload.size) "created file stat"
  let gotNew ← assertOk (← Raw.readBytes newFile) "readBytes created file"
  assertTrue (gotNew == payload) "createFileNew exact bytes roundtrip"

  assertErrKind (← Raw.createFileNew newFile (ByteArray.mk #[9, 9])) .alreadyExists
    "createFileNew on existing file fails"
  assertTrue ((← assertOk (← Raw.readBytes newFile) "readBytes after EEXIST") == payload)
    "existing file bytes preserved"

  let subDir := tmp ++ "/sub_dir"
  assertOk (← Raw.createDir subDir) "createDir sub_dir"
  assertErrKind (← Raw.createFileNew subDir payload) .alreadyExists
    "createFileNew on existing dir fails"

  let symToFile := tmp ++ "/sym_to_file"
  assertOk (← Raw.symlink newFile symToFile) "symlink to file"
  assertErrKind (← Raw.createFileNew symToFile (ByteArray.mk #[8, 8])) .alreadyExists
    "createFileNew on symlink to file fails"
  assertTrue ((← assertOk (← Raw.readBytes newFile) "readBytes target after symlink EEXIST") == payload)
    "symlink target preserved"

  let danglingTarget := tmp ++ "/never_created_target"
  let symDangling := tmp ++ "/sym_dangling_cfn"
  assertOk (← Raw.symlink danglingTarget symDangling) "dangling symlink"
  assertErrKind (← Raw.createFileNew symDangling payload) .alreadyExists
    "createFileNew on dangling symlink fails"
  assertErrKind (← Raw.stat false danglingTarget) .notFound "dangling target not created"

  assertErrKind (← Raw.createFileNew "/" payload) .alreadyExists "createFileNew on / fails"
  assertErrKind (← Raw.createFileNew "." payload) .alreadyExists "createFileNew on . fails"
  assertErrKind (← Raw.createFileNew ".." payload) .alreadyExists "createFileNew on .. fails"

  let nulStr := String.ofList ['a', Char.ofNat 0, 'b']
  assertErrKind (← Raw.createFileNew "" payload) .invalidInput "createFileNew empty fails"
  assertErrKind (← Raw.createFileNew (tmp ++ "/" ++ nulStr) payload) .invalidInput
    "createFileNew embedded NUL fails"
  assertErrKind (← Raw.createFileNew (tmp ++ "/trailing/") payload) .invalidInput
    "createFileNew trailing slash fails"
  assertErrKind (← Raw.createFileNew (tmp ++ "/missing_parent/child") payload) .notFound
    "createFileNew missing parent fails"

  assertErrKind (← Raw.readBytes "") .invalidInput "readBytes empty fails"
  assertErrKind (← Raw.readBytes (tmp ++ "/" ++ nulStr)) .invalidInput "readBytes embedded NUL fails"
  assertErrKind (← Raw.readBytes (tmp ++ "/")) .invalidInput "readBytes non-root trailing slash fails"
  assertErrKind (← Raw.readBytes subDir) .isADirectory "readBytes dir fails"
  assertErrKind (← Raw.readBytes (tmp ++ "/absent.bin")) .notFound "readBytes missing fails"
  assertErrKind (← Raw.readBytes symDangling) .notFound "readBytes dangling symlink fails"

  let emptyFile := tmp ++ "/empty.bin"
  let symEmpty := tmp ++ "/sym_empty"
  assertOk (← Raw.createFileNew emptyFile ByteArray.empty) "createFileNew empty"
  assertOk (← Raw.symlink emptyFile symEmpty) "symlink empty"
  assertTrue ((← assertOk (← Raw.readBytes symEmpty) "readBytes symlink empty") == ByteArray.empty)
    "symlink empty exact bytes"
  assertTrue ((← assertOk (← Raw.readBytes symToFile) "readBytes symlink binary") == payload)
    "symlink binary exact bytes"

  let bigBytes := ByteArray.mk (Array.replicate 100000 0xAB)
  let bigFile := tmp ++ "/big.bin"
  assertOk (← Raw.createFileNew bigFile bigBytes) "createFileNew 100KB"
  assertTrue ((← assertOk (← Raw.readBytes bigFile) "readBytes 100KB") == bigBytes)
    "readBytes 100KB exact"

  let fifoPath := tmp ++ "/read_test.fifo"
  let mkfifoOut ← IO.Process.output { cmd := "mkfifo", args := #[fifoPath] }
  assertTrue (mkfifoOut.exitCode == 0) "mkfifo exitCode 0"
  assertErrKind (← Raw.readBytes fifoPath) .invalidInput "readBytes FIFO rejected immediately"
  let symFifo := tmp ++ "/sym_fifo"
  assertOk (← Raw.symlink fifoPath symFifo) "symlink to FIFO"
  assertErrKind (← Raw.readBytes symFifo) .invalidInput "readBytes symlink to FIFO rejected immediately"

  let sockPath := tmp ++ "/t.sock"
  let readyPath := tmp ++ "/sock.ready"
  let stopPath := tmp ++ "/sock.stop"
  let sockScript :=
    "import os, socket, time\n" ++
    "s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)\n" ++
    "s.bind('t.sock')\n" ++
    "s.listen(1)\n" ++
    "open('sock.ready', 'w').write('1')\n" ++
    "deadline = time.monotonic() + 5.0\n" ++
    "while not os.path.exists('sock.stop') and time.monotonic() < deadline:\n" ++
    "  time.sleep(0.01)\n" ++
    "s.close()\n"
  let child ← IO.Process.spawn
    { cmd := "python3"
      args := #["-c", sockScript]
      cwd := some (System.FilePath.mk tmp) }
  try
    waitForFile readyPath
    assertErrKind (← Raw.readBytes sockPath) .invalidInput "readBytes Unix domain socket rejected"
    let symSock := tmp ++ "/sym_sock"
    assertOk (← Raw.symlink sockPath symSock) "symlink to socket"
    assertErrKind (← Raw.readBytes symSock) .invalidInput "readBytes symlink to socket rejected"
    assertOk (← Raw.unlinkFile symSock) "unlink symSock"
  finally
    let _ ← Raw.createFileNew stopPath ByteArray.empty
    let _ ← child.wait
    let _ ← Raw.unlinkFile sockPath
    let _ ← Raw.unlinkFile readyPath
    let _ ← Raw.unlinkFile stopPath

  assertOk (← Raw.unlinkFile symFifo) "unlink symFifo"
  assertOk (← Raw.unlinkFile fifoPath) "unlink fifoPath"
  assertOk (← Raw.unlinkFile bigFile) "unlink bigFile"
  assertOk (← Raw.unlinkFile symEmpty) "unlink symEmpty"
  assertOk (← Raw.unlinkFile emptyFile) "unlink emptyFile"
  assertOk (← Raw.unlinkFile symDangling) "unlink symDangling"
  assertOk (← Raw.unlinkFile symToFile) "unlink symToFile"
  assertOk (← Raw.removeDir subDir) "removeDir subDir"
  assertOk (← Raw.unlinkFile newFile) "unlink newFile"

private def withTempDir {α : Type} (f : String → IO α) : IO α :=
  IO.FS.withTempDir fun dir => f dir.toString

private def runReadOnlyDirOpsTest (dh : Raw.DirHandle) (base : String) (payload : ByteArray) : IO Unit := do
  let roName ← assertOk (Raw.EntryName.parse "ro_dir") "name ro_dir"
  let roInner ← assertOk (Raw.EntryName.parse "inner.txt") "name inner.txt"
  assertOk (← Raw.createDirAt dh roName) "createDirAt ro_dir"
  let roTmpDh ← assertOk (← Raw.openDirAt dh roName) "openDirAt ro_dir writable"
  assertOk (← Raw.createFileAt roTmpDh roInner payload) "create inner.txt inside ro_dir"
  assertOk (← Raw.closeDir roTmpDh) "close roTmpDh"
  assertOk (← Raw.chmod (base ++ "/ro_dir") 0o400) "chmod 0400 ro_dir"
  let roDh ← assertOk (← Raw.openDir (base ++ "/ro_dir")) "openDir 0400 dir"
  let roEntries1 ← assertOk (← Raw.readDirAt roDh) "readDirAt 0400 dir first"
  assertTrue (roEntries1 == #[roInner]) "readDirAt 0400 dir returns inner.txt"
  let roEntries2 ← assertOk (← Raw.readDirAt roDh) "readDirAt 0400 dir second rewinds"
  assertTrue (roEntries2 == #[roInner]) "second readDirAt 0400 dir returns inner.txt"
  assertOk (← Raw.closeDir roDh) "closeDir roDh"
  assertOk (← Raw.chmod (base ++ "/ro_dir") 0o755) "restore chmod 0755 ro_dir"
  let roCleanDh ← assertOk (← Raw.openDirAt dh roName) "reopen ro_dir for cleanup"
  assertOk (← Raw.unlinkAt roCleanDh roInner false) "unlink inner.txt"
  assertOk (← Raw.closeDir roCleanDh) "close roCleanDh"
  assertOk (← Raw.unlinkAt dh roName true) "unlinkAt empty ro_dir"

private def runDirOpsTests (tmp : String) : IO Unit := do
  assertTrue (Raw.isValidDirHandleId 1) "isValidDirHandleId 1"
  assertTrue (Raw.isValidDirHandleId (UInt64.size - 1)) "isValidDirHandleId max u64"
  assertTrue (!Raw.isValidDirHandleId 0) "isValidDirHandleId 0 false"
  assertTrue (!Raw.isValidDirHandleId UInt64.size) "isValidDirHandleId UInt64.size false"

  let nulStr := String.ofList ['a', Char.ofNat 0, 'b']
  for bad in #["", ".", "..", "a/b", nulStr] do
    assertErrKind (Raw.EntryName.parse bad) .invalidInput s!"EntryName.parse rejects {repr bad}"
  let validName ← assertOk (Raw.EntryName.parse "ok.txt") "EntryName.parse ok"
  assertTrue (validName.val == "ok.txt") "EntryName.val"

  for badRel in #["", "/abs", "trail/", ".", "..", "a//b", "a/./b", "a/../b", nulStr] do
    assertErrKind (Raw.RelPath.parse badRel) .invalidInput s!"RelPath.parse rejects {repr badRel}"
  let parsedRoot ← assertOk (Raw.RelPath.parseRoot ".") "RelPath.parseRoot ."
  assertTrue parsedRoot.isEmpty "RelPath.parseRoot . is empty"
  let parsedSub ← assertOk (Raw.RelPath.parseRoot "a/b") "RelPath.parseRoot a/b"
  assertTrue (parsedSub.segments.map (·.val) == ["a", "b"]) "RelPath.parseRoot segments"

  let base := tmp ++ "/dirops"
  assertOk (← Raw.createDir base) "mkdir dirops"
  let dh ← assertOk (← Raw.openDir base) "openDir dirops"
  assertTrue (Raw.isValidDirHandleId dh.handleId) "opened DirHandle id valid"
  let stRoot ← assertOk (← Raw.fstatDir dh) "fstatDir root"
  assertTrue (stRoot.kind == .dir) "fstatDir kind == .dir"

  assertErrKind (← Raw.openDir (base ++ "/missing")) .notFound "openDir missing"
  let notDirFile := base ++ "/notdir"
  assertOk (← Raw.createFileNew notDirFile (ByteArray.mk #[1])) "create notdir"
  assertErrKind (← Raw.openDir notDirFile) .notADirectory "openDir regular file"

  let symRoot := tmp ++ "/sym_root_dir"
  assertOk (← Raw.symlink base symRoot) "symlink root"
  let dhSymRoot ← assertOk (← Raw.openDir symRoot) "openDir follows initial symlink rootPath"
  assertTrue ((← assertOk (← Raw.fstatDir dhSymRoot) "fstatDir symRoot").kind == .dir) "symRoot dir"
  assertOk (← Raw.closeDir dhSymRoot) "closeDir dhSymRoot"

  let childDir ← assertOk (Raw.EntryName.parse "child_dir") "name child_dir"
  let childFile ← assertOk (Raw.EntryName.parse "child_file") "name child_file"
  let symChildDir ← assertOk (Raw.EntryName.parse "sym_child_dir") "name sym_child_dir"
  let symChildFile ← assertOk (Raw.EntryName.parse "sym_child_file") "name sym_child_file"
  let symDangling ← assertOk (Raw.EntryName.parse "sym_dangling") "name sym_dangling"

  assertOk (← Raw.createDirAt dh childDir) "createDirAt childDir"
  assertErrKind (← Raw.createDirAt dh childDir) .alreadyExists "createDirAt existing dir"
  let stCd ← assertOk (← Raw.lstatAt dh childDir) "lstatAt childDir"
  assertTrue (stCd.kind == .dir) "childDir kind"

  let payload := ByteArray.mk #[10, 20, 30, 40]
  assertOk (← Raw.createFileAt dh childFile payload) "createFileAt childFile"
  assertErrKind (← Raw.createFileAt dh childFile payload) .alreadyExists "createFileAt existing file"
  assertErrKind (← Raw.createFileAt dh childDir payload) .alreadyExists "createFileAt existing dir"
  assertErrKind (← Raw.createDirAt dh childFile) .alreadyExists "createDirAt existing file"
  let gotChild ← assertOk (← Raw.readRegularAt dh childFile) "readRegularAt exact bytes"
  assertTrue (gotChild == payload) "readRegularAt payload"
  assertErrKind (← Raw.readRegularAt dh childDir) .isADirectory "readRegularAt dir"

  let max255 ← assertOk (Raw.EntryName.parse (String.ofList (List.replicate 255 'm'))) "name 255"
  let over256 ← assertOk (Raw.EntryName.parse (String.ofList (List.replicate 256 'm'))) "name 256"
  assertOk (← Raw.createFileAt dh max255 payload) "createFileAt 255-byte name"
  assertErrKind (← Raw.createFileAt dh over256 payload) .invalidInput "createFileAt 256-byte ENAMETOOLONG"
  assertOk (← Raw.unlinkAt dh max255 false) "unlinkAt 255-byte name"

  assertOk (← Raw.symlinkAt (base ++ "/child_dir") dh symChildDir) "symlinkAt symChildDir"
  assertOk (← Raw.symlinkAt (base ++ "/child_file") dh symChildFile) "symlinkAt symChildFile"
  assertOk (← Raw.symlinkAt (base ++ "/missing_target") dh symDangling) "symlinkAt symDangling"
  assertErrKind (← Raw.symlinkAt "" dh validName) .invalidInput "symlinkAt empty target"
  assertErrKind (← Raw.symlinkAt nulStr dh validName) .invalidInput "symlinkAt NUL target"
  assertErrKind (← Raw.openDirAt dh symChildDir) .invalidInput "openDirAt refuses symlink to dir"
  assertErrKind (← Raw.openDirAt dh symChildFile) .invalidInput "openDirAt refuses symlink to file"
  assertErrKind (← Raw.openDirAt dh symDangling) .invalidInput "openDirAt refuses dangling symlink"
  assertErrKind (← Raw.openDirAt dh childFile) .notADirectory "openDirAt regular file"
  assertErrKind (← Raw.readRegularAt dh symChildFile) .invalidInput "readRegularAt refuses symlink to file"
  assertErrKind (← Raw.readRegularAt dh symDangling) .invalidInput "readRegularAt refuses dangling symlink"
  assertErrKind (← Raw.createFileAt dh symChildFile payload) .alreadyExists "createFileAt refuses symlink"
  assertErrKind (← Raw.createFileAt dh symDangling payload) .alreadyExists "createFileAt refuses dangling symlink"
  assertErrKind (← Raw.createDirAt dh symDangling) .alreadyExists "createDirAt refuses dangling symlink"
  assertErrKind (← Raw.acquireLockAt dh symChildFile .exclusive false true) .invalidInput "acquireLockAt refuses symlink"
  assertErrKind (← Raw.acquireLockAt dh symDangling .exclusive true true) .invalidInput "acquireLockAt refuses dangling symlink"

  let fifoName ← assertOk (Raw.EntryName.parse "dir.fifo") "name dir.fifo"
  let mkfifoOut ← IO.Process.output { cmd := "mkfifo", args := #[base ++ "/dir.fifo"] }
  assertTrue (mkfifoOut.exitCode == 0) "mkfifo exitCode 0"
  assertErrKind (← Raw.readRegularAt dh fifoName) .invalidInput "readRegularAt FIFO rejected immediately"
  assertErrKind (← Raw.acquireLockAt dh fifoName .exclusive false true) .invalidInput "acquireLockAt FIFO rejected"
  assertOk (← Raw.unlinkAt dh fifoName false) "unlinkAt FIFO"

  let listed ← assertOk (← Raw.readDirAt dh) "readDirAt"
  assertTrue listed.toList.Nodup "readDirAt Nodup"
  assertTrue (listed.contains childDir && listed.contains childFile && listed.contains symChildDir)
    "readDirAt contains expected children"

  let subDh ← assertOk (← Raw.openDirAt dh childDir) "openDirAt childDir"
  let movedName ← assertOk (Raw.EntryName.parse "moved.bin") "name moved"
  assertOk (← Raw.renameAt dh childFile subDh movedName) "renameAt across handles"
  assertErrKind (← Raw.lstatAt dh childFile) .notFound "old location missing after renameAt"
  assertTrue ((← assertOk (← Raw.readRegularAt subDh movedName) "readRegularAt moved") == payload)
    "moved payload intact"

  assertErrKind (← Raw.unlinkAt dh childDir false) .isADirectory "unlinkAt file-flag on dir"
  assertErrKind (← Raw.unlinkAt dh childDir true) .notEmpty "unlinkAt dir-flag on non-empty dir"
  assertErrKind (← Raw.unlinkAt dh symChildDir true) .notADirectory "unlinkAt dir-flag on symlink"
  assertOk (← Raw.unlinkAt dh symChildDir false) "unlinkAt symChildDir"
  assertOk (← Raw.unlinkAt subDh movedName false) "unlinkAt movedName"
  assertOk (← Raw.closeDir subDh) "closeDir subDh"
  assertOk (← Raw.unlinkAt dh childDir true) "unlinkAt empty childDir"
  runReadOnlyDirOpsTest dh base payload

  let t1 ← Raw.freshTempName
  let t2 ← Raw.freshTempName
  assertTrue (t1 != t2) "freshTempName strictly distinct"

  let pinnedDir ← assertOk (Raw.EntryName.parse "pinned") "name pinned"
  assertOk (← Raw.createDirAt dh pinnedDir) "create pinned"
  let pinnedDh ← assertOk (← Raw.openDirAt dh pinnedDir) "open pinned"
  assertOk (← Raw.rename (base ++ "/pinned") (tmp ++ "/pinned_renamed")) "external rename of pinned dir"
  let pinnedFile ← assertOk (Raw.EntryName.parse "inside.txt") "name inside.txt"
  assertOk (← Raw.createFileAt pinnedDh pinnedFile payload) "write through renamed pinned Dh"
  let extGot ← assertOk (← Raw.readBytes (tmp ++ "/pinned_renamed/inside.txt")) "readBytes at renamed target"
  assertTrue (extGot == payload) "descriptor pinned across external rename"
  assertOk (← Raw.unlinkAt pinnedDh pinnedFile false) "unlink inside.txt"
  assertOk (← Raw.closeDir pinnedDh) "close pinnedDh"
  assertOk (← Raw.removeDir (tmp ++ "/pinned_renamed")) "removeDir pinned_renamed"

  let lockName ← assertOk (Raw.EntryName.parse "slot.lock") "name slot.lock"
  let lockDh ← assertOk (← Raw.openDir base) "openDir lockDh"
  let heldLock ← assertOk (← Raw.acquireLockAt lockDh lockName .exclusive true true) "acquire initial slot.lock"
  let waiterTask ← IO.asTask (prio := .dedicated) do
    Raw.acquireLockAt lockDh lockName .exclusive false false
  IO.sleep 50
  assertOk (← Raw.closeDir lockDh) "closeDir succeeds immediately while acquireLockAt blocks on flock"
  assertErrKind (← Raw.fstatDir lockDh) .invalidInput "closed lockDh rejected while waiter holds no DirSlot ref"
  assertOk (← Raw.releaseLock heldLock) "release heldLock"
  let waitedRes ← IO.wait waiterTask
  match waitedRes with
  | .error ioErr => throw ioErr
  | .ok lockRes =>
    let waitedLock ← assertOk lockRes "waiter acquired lock after outer release"
    assertOk (← Raw.releaseLock waitedLock) "release waiter lock"

  let forgedZero : Raw.DirHandle := { handleId := 0, rootPath := "/" }
  let forgedBig : Raw.DirHandle := { handleId := UInt64.size, rootPath := "/" }
  assertErrKind (← Raw.fstatDir forgedZero) .invalidInput "forgedZero fstatDir"
  assertErrKind (← Raw.closeDir forgedZero) .invalidInput "forgedZero closeDir"
  assertErrKind (← Raw.fstatDir forgedBig) .invalidInput "forgedBig fstatDir"
  assertErrKind (← Raw.closeDir forgedBig) .invalidInput "forgedBig closeDir"

  assertOk (← Raw.unlinkAt dh symChildFile false) "unlink symChildFile"
  assertOk (← Raw.unlinkAt dh symDangling false) "unlink symDangling"
  assertOk (← Raw.closeDir dh) "closeDir dh"
  assertErrKind (← Raw.closeDir dh) .invalidInput "double closeDir"
  assertErrKind (← Raw.fstatDir dh) .invalidInput "fstatDir after close"
  assertErrKind (← Raw.lstatAt dh validName) .invalidInput "lstatAt after close"
  assertErrKind (← Raw.readDirAt dh) .invalidInput "readDirAt after close"
  assertErrKind (← Raw.openDirAt dh validName) .invalidInput "openDirAt after close"
  assertErrKind (← Raw.createDirAt dh validName) .invalidInput "createDirAt after close"
  assertErrKind (← Raw.readRegularAt dh validName) .invalidInput "readRegularAt after close"
  assertErrKind (← Raw.createFileAt dh validName payload) .invalidInput "createFileAt after close"
  assertErrKind (← Raw.renameAt dh validName dh validName) .invalidInput "renameAt after close"
  assertErrKind (← Raw.unlinkAt dh validName false) .invalidInput "unlinkAt after close"
  assertErrKind (← Raw.symlinkAt "t" dh validName) .invalidInput "symlinkAt after close"
  assertErrKind (← Raw.acquireLockAt dh validName .exclusive false true) .invalidInput "acquireLockAt after close"

  assertOk (← Raw.unlinkFile (base ++ "/slot.lock")) "unlink slot.lock"
  assertOk (← Raw.unlinkFile notDirFile) "unlink notdir"
  assertOk (← Raw.unlinkFile symRoot) "unlink symRoot"
  assertOk (← Raw.removeDir base) "rmdir base"

/-- Execute primitive Linux syscall grounding tests for `LeanSwe.Fs.Raw`. -/
def runAll : IO Unit := do
  withTempDir fun tmp => do
    let d1 := tmp ++ "/dir1"
    assertOk (← Raw.createDir d1) "createDir d1"
    assertErrKind (← Raw.createDir d1) .alreadyExists "createDir existing fails"
    assertErrKind (← Raw.createDir (tmp ++ "/missing/sub")) .notFound "createDir missing parent fails"

    let f1 := d1 ++ "/a.bin"
    assertOk (← Raw.writeBytes f1 (ByteArray.mk #[1, 2, 3])) "writeBytes"
    assertOk (← Raw.appendText f1 "") "appendText empty"
    let got ← assertOk (← Raw.readBytes f1) "readBytes"
    assertTrue (got == ByteArray.mk #[1, 2, 3]) "readBytes content"
    assertErrKind (← Raw.removeDir d1) .notEmpty "removeDir non-empty fails"

    assertOk (← Raw.chmod f1 0o640) "chmod"
    let st ← assertOk (← Raw.stat true f1) "stat"
    assertTrue (st.kind == .file && st.byteSize == 3 && (st.mode % 512) == 0o640) "stat mode/size"

    let sym := d1 ++ "/dangling"
    assertOk (← Raw.symlink (d1 ++ "/missing") sym) "symlink"
    let lst ← assertOk (← Raw.stat false sym) "lstat dangling"
    assertTrue (lst.kind == .symlink) "lstat reports symlink"
    assertErrKind (← Raw.stat true sym) .notFound "stat follows dangling symlink"
    assertErrKind (← Raw.createDir sym) .alreadyExists "createDir on broken symlink fails"
    let tgt ← assertOk (← Raw.readLink sym) "readLink"
    assertTrue (tgt == d1 ++ "/missing") "readLink target"

    let kids ← assertOk (← Raw.readDir d1) "readDir"
    assertTrue (kids.qsort (· < ·) == #["a.bin", "dangling"]) "readDir entries"
    let cwdStr ← assertOk (← Raw.cwd) "cwd"
    assertTrue (cwdStr.startsWith "/") "cwd absolute"
    let rp ← assertOk (← Raw.realPath d1) "realPath"
    assertTrue (rp.startsWith "/") "realPath absolute"

    assertOk (← Raw.unlinkFile sym) "unlinkFile sym"
    assertOk (← Raw.unlinkFile f1) "unlinkFile f1"
    assertOk (← Raw.removeDir d1) "removeDir d1"
    runLockTests tmp
    runAmbientSafetyTests tmp
    runDirOpsTests tmp
  IO.println "PASS: LeanSwe.Fs.Raw runtime tests"

end LeanSwe.Fs.Raw.RuntimeTests
