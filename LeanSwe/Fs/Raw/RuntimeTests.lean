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

/-- Execute primitive Linux syscall grounding tests for `LeanSwe.Fs.Raw`. -/
def runAll : IO Unit := do
  let res ← Raw.withTempDir fun tmp => do
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
    return .ok ()
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"Fs.Raw RuntimeTests failed unexpectedly: {repr e}")
  IO.println "PASS: LeanSwe.Fs.Raw runtime tests"

end LeanSwe.Fs.Raw.RuntimeTests
