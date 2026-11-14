import LeanSwe.Fs.Interface

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

/-- Execute all pure path and real filesystem runtime checks for `LeanSwe.Fs`. -/
def runAll : IO Unit := do
  testPurePaths
  let res ← Fs.withTempDir fun tmp => do
    match ← testFilesAndDirs tmp with
    | .error e => return .error e
    | .ok moved => testSymlinksAndGlobs tmp moved
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"Fs RuntimeTests failed unexpectedly: {repr e}")
  IO.println "PASS: LeanSwe.Fs runtime tests"

end LeanSwe.Fs.RuntimeTests
