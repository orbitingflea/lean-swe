import Core.NondetTest
import LeanSwe.Fs.Raw.Types

namespace LeanSwe.Fs.Raw

open Core (NondetTest)
open Core.NondetTest

private def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

private def isSingleValidName (name : String) : Bool :=
  let cs := name.toList
  !cs.isEmpty && !('/' ∈ cs) && !(Char.ofNat 0 ∈ cs) && name != "." && name != ".."

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_fsraw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawFsOps) : runner Unit := do
  let raw ← nondet FsRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- Mapping a `.wouldBlock` raw error preserves `.wouldBlock` kind, path, errno, and non-empty message. -/
def test_fsraw_mapRawError_wouldBlock
    {runner} [NondetTest runner] (ops : RawFsOps) : runner Unit := do
  let path? ← nondet (Option String)
  let errno ← nondet UInt32
  let detail ← nondet String
  let err := ops.mapRawError (.wouldBlock path? errno detail)
  NondetTest.assert (err.kind = .wouldBlock ∧ err.path = path? ∧ err.errnoCode = some errno ∧ err.message ≠ "")

/-- Calling `ops.createFileNew` on a missing child under writable `"/"` creates a regular file with exact `bytes`. -/
def test_fsraw_createFileNew_createsMissingWithExactBytes
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  assume (∃ e, ((ops.stat false path).run s₀).1 = .error e ∧ e.kind = .notFound)
  let (res, s₁) := (ops.createFileNew path bytes).run s₀
  NondetTest.assert (res = .ok ())
  NondetTest.assert (∃ st, ((ops.stat false path).run s₁).1 = .ok st ∧
    st.kind = .file ∧ st.byteSize = bytes.size)
  NondetTest.assert (((ops.readBytes path).run s₁).1 = .ok bytes)

/-- Calling `ops.createFileNew` on any existing entry (file, directory, or symlink including dangling links) fails with `.alreadyExists` and leaves state unchanged. -/
def test_fsraw_createFileNew_existingRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let bytes ← nondet ByteArray
  assume (isValidRawPath path = true)
  assume (((ops.stat false path).run s₀).1.isOk = true)
  let (res, s₁) := (ops.createFileNew path bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)

/-- Calling `ops.createFileNew` with an empty path, embedded NUL byte, or non-root trailing `/` fails with `.invalidInput` and leaves state unchanged. -/
def test_fsraw_createFileNew_invalidPathRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let bytes ← nondet ByteArray
  assume (isValidRawPath path = false)
  let (res, s₁) := (ops.createFileNew path bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `ops.createFileNew` under a missing parent directory fails with `.notFound` without creating parent directories. -/
def test_fsraw_createFileNew_missingParentRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let d ← nondet String
  let f ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName d = true ∧ isSingleValidName f = true)
  assume (∃ e, ((ops.stat false ("/" ++ d)).run s₀).1 = .error e ∧ e.kind = .notFound)
  let (res, s₁) := (ops.createFileNew ("/" ++ d ++ "/" ++ f) bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ s₁ = s₀)

/-- Calling `ops.readBytes` on a symlink whose target is a regular file follows the symlink and returns the file bytes without mutating state. -/
def test_fsraw_readBytes_followsSymlinkToRegularFile
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = true)
  assume (∃ lst, ((ops.stat false path).run s₀).1 = .ok lst ∧ lst.kind = .symlink)
  assume (∃ st, ((ops.stat true path).run s₀).1 = .ok st ∧ st.kind = .file)
  let (res, s₁) := (ops.readBytes path).run s₀
  NondetTest.assert ((∃ bs, res = .ok bs ∧
    (∃ st, ((ops.stat true path).run s₀).1 = .ok st ∧ bs.size = st.byteSize)) ∧ s₁ = s₀)

/-- Writing `bytes` with `ops.createFileNew`, symlinking to it, and calling `ops.readBytes` on the symlink returns exact `bytes` without mutating state. -/
def test_fsraw_readBytes_roundTripsExactBytesThroughSymlink
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let tgtName ← nondet String
  let symName ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName tgtName = true ∧ isSingleValidName symName = true ∧ tgtName ≠ symName)
  let tgt := "/" ++ tgtName
  let sym := "/" ++ symName
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  assume (∃ e1, ((ops.stat false tgt).run s₀).1 = .error e1 ∧ e1.kind = .notFound)
  assume (∃ e2, ((ops.stat false sym).run s₀).1 = .error e2 ∧ e2.kind = .notFound)
  let (r1, s₁) := (ops.createFileNew tgt bytes).run s₀
  assume (r1 = .ok ())
  let (r2, s₂) := (ops.symlink tgt sym).run s₁
  assume (r2 = .ok ())
  let (r3, s₃) := (ops.readBytes sym).run s₂
  NondetTest.assert (r3 = .ok bytes ∧ s₃ = s₂)

/-- Calling `ops.readBytes` on a directory fails with `.isADirectory` and on a missing valid path preserves the `stat` error without mutating state. -/
def test_fsraw_readBytes_dirAndMissingRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = true)
  match ((ops.stat true path).run s₀).1 with
  | .error err =>
    let (res, s₁) := (ops.readBytes path).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = err.kind) ∧ s₁ = s₀)
  | .ok st =>
    if st.kind == .dir then
      let (res, s₁) := (ops.readBytes path).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)
    else
      pure ()

/-- Calling `ops.readBytes` with an empty path, embedded NUL byte, or non-root trailing `/` fails with `.invalidInput` and leaves state unchanged. -/
def test_fsraw_readBytes_invalidPathRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = false)
  let (res, s₁) := (ops.readBytes path).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- External trust boundary assumptions for `LeanSwe.Fs.Raw` C shims grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- `leanswe_fs_read_regular_bytes` opens `path` with `O_RDONLY | O_NONBLOCK | O_CLOEXEC | O_NOCTTY`, maps `ENXIO` on Unix domain sockets and unbacked special files to `.invalidInput` (preserving `.isADirectory` on directories), checks `fstat` returning `.isADirectory` on `S_ISDIR` and `.invalidInput` on `!S_ISREG` (FIFOs, sockets, device nodes), and clears `O_NONBLOCK` via `fcntl` before reading to EOF handling `EINTR`/`EAGAIN`. -/
  readBytesNonBlockingRejectsNonRegular : Prop
  /-- `leanswe_fs_read_regular_bytes` rejects `""`, embedded NUL bytes, and non-root trailing `/` with `.invalidInput` and follows symlinks to regular files (`mkfifo` FIFO and Unix domain socket grounded in `RuntimeTests.lean`). -/
  readBytesValidatesPathAndFollowsSymlinks : Prop
  /-- `leanswe_fs_create_file_new` opens with `O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC` (mode `0644` masked by `umask`), rejects `""`, embedded NUL bytes, and non-root trailing `/` with `.invalidInput`, fails with `.alreadyExists` on existing files, directories, or symlinks (including dangling links, `"/"`, `"."`, `".."`) without following symlinks (`O_EXCL | O_NOFOLLOW` and path validation grounded in `RuntimeTests.lean`), and performs best-effort `unlink(path)` on `write` or `close(fd)` failure preserving the original `errno` (audited in C shim). -/
  createFileNewExclusiveNoFollow : Prop

private def buggyEmptyErrRaw (base : RawFsOps) : RawFsOps :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyWouldBlockToInvalidRaw (base : RawFsOps) : RawFsOps :=
  { base with
    mapRawError := fun
      | .wouldBlock path? errno _ =>
        { kind := .invalidInput, path := path?, errnoCode := some errno, message := "invalid" }
      | other => base.mapRawError other }

private def stubRawOps : RawFsOps :=
  { mapRawError := fun _ => { kind := .ioError, message := "stub" }
    stat := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    readDir := fun _ => pure (.ok #[])
    createDir := fun _ => pure (.ok ())
    removeDir := fun _ => pure (.ok ())
    unlinkFile := fun _ => pure (.ok ())
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    createFileNew := fun _ _ => pure (.ok ())
    appendText := fun _ _ => pure (.ok ())
    rename := fun _ _ => pure (.ok ())
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
    realPath := fun _ => pure (.error { kind := .notFound, message := "stub" })
    cwd := pure (.ok "/")
    monotonicNonce := pure 0
    acquireLock := fun path mode _ _ => pure (.ok { handleId := 1, path := path, mode := mode })
    releaseLock := fun _ => pure (.ok ()) }

private def stubStat (kind : EntryKind) (byteSize : Nat := 0) (mode : Nat := 0o755) : FileStat :=
  { kind := kind
    byteSize := byteSize
    mode := mode
    modifiedSec := 0
    modifiedNsec := 0
    accessedSec := 0
    accessedNsec := 0 }

private def stubVfsRawOps : RawFsOpsM (StateM Unit) :=
  { mapRawError := fun _ => { kind := .ioError, message := "stub" }
    stat := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    readDir := fun _ => pure (.ok #[])
    createDir := fun _ => pure (.ok ())
    removeDir := fun _ => pure (.ok ())
    unlinkFile := fun _ => pure (.ok ())
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    createFileNew := fun _ _ => pure (.ok ())
    appendText := fun _ _ => pure (.ok ())
    rename := fun _ _ => pure (.ok ())
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
    realPath := fun _ => pure (.error { kind := .notFound, message := "stub" })
    cwd := pure (.ok "/")
    monotonicNonce := pure 0
    acquireLock := fun path mode _ _ => pure (.ok { handleId := 1, path := path, mode := mode })
    releaseLock := fun _ => pure (.ok ()) }

example : ¬ Core.AllPass (test_fsraw_mapRawError_returnsNonEmptyMessage (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrRaw, assert] at h0

example : ¬ Core.AllPass (test_fsraw_mapRawError_wouldBlock (buggyWouldBlockToInvalidRaw stubRawOps)) := by
  intro h
  have h0 := h (some "/tmp/a.lock") 11 "Resource temporarily unavailable"
  simp [buggyWouldBlockToInvalidRaw, assert] at h0

example : ¬ Core.AllPass (test_fsraw_createFileNew_createsMissingWithExactBytes
    { stubVfsRawOps with
      stat := fun _ p =>
        if p == "/" then pure (.ok (stubStat .dir))
        else pure (.error { kind := .notFound, message := "stub" })
      createFileNew := fun _ _ => pure (.error { kind := .ioError, message := "fail" }) }) := by
  intro h
  have h0 := h () "a.bin" ByteArray.empty (by decide)
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
  simp [StateT.run, bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fsraw_createFileNew_existingRejected
    { stubVfsRawOps with
      stat := fun _ _ => pure (.ok (stubStat .symlink))
      createFileNew := fun _ _ => pure (.ok ()) }) := by
  intro h
  have h0 := h () "/sym" ByteArray.empty (by decide) rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fsraw_createFileNew_invalidPathRejected stubVfsRawOps) := by
  intro h
  have h0 := h () "" ByteArray.empty (by decide)
  simp [stubVfsRawOps, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_createFileNew_missingParentRejected stubVfsRawOps) := by
  intro h
  have h0 := h () "missing" "f" ByteArray.empty (And.intro (by decide) (by decide))
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
  simp [stubVfsRawOps, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_readBytes_followsSymlinkToRegularFile
    { stubVfsRawOps with
      stat := fun follow _ =>
        if follow then pure (.ok (stubStat .file 3))
        else pure (.ok (stubStat .symlink))
      readBytes := fun _ => pure (.error { kind := .invalidInput, message := "nofollow bug" }) }) := by
  intro h
  have h0 := h () "/sym" (by decide) ⟨stubStat .symlink, rfl, rfl⟩ ⟨stubStat .file 3, rfl, rfl⟩
  simp [stubStat, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fsraw_readBytes_dirAndMissingRejected
    { stubVfsRawOps with
      stat := fun _ _ => pure (.ok (stubStat .dir))
      readBytes := fun _ => pure (.ok ByteArray.empty) }) := by
  intro h
  have h0 := h () "/dir" (by decide)
  simp [stubStat, StateT.run, pure, StateT.pure, assert] at h0
  have hDir : (EntryKind.dir == EntryKind.dir) = true := rfl
  simp [hDir] at h0

example : ¬ Core.AllPass (test_fsraw_readBytes_invalidPathRejected stubVfsRawOps) := by
  intro h
  have h0 := h () "" (by decide)
  simp [stubVfsRawOps, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_readBytes_roundTripsExactBytesThroughSymlink
    { stubVfsRawOps with
      stat := fun _ p =>
        if p == "/" then pure (.ok (stubStat .dir))
        else pure (.error { kind := .notFound, message := "stub" })
      readBytes := fun _ => pure (.ok (ByteArray.mk #[0, 0, 0])) }) := by
  intro h
  have h0 := h () "a.bin" "sym" (ByteArray.mk #[1, 2, 3]) (And.intro (by decide) (And.intro (by decide) (by decide)))
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
    rfl rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

end LeanSwe.Fs.Raw
