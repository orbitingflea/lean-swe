import LeanSwe.Fs.Raw.Interface

/-!
# Fs.Raw RuntimeTests

Concrete execution tests grounding `LeanSwe.Fs.Raw` (`createDir`, `removeDir`,
`stat`, `readDir`, `writeBytes`, `readBytes`, `unlinkFile`, `chmod`, `symlink`,
`readLink`, `realPath`, `cwd`, `withTempDir`) against real Linux OS syscalls.
-/

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
    return .ok ()
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"Fs.Raw RuntimeTests failed unexpectedly: {repr e}")
  IO.println "PASS: LeanSwe.Fs.Raw runtime tests"

end LeanSwe.Fs.Raw.RuntimeTests
