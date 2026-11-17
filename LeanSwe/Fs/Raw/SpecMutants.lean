import Core.NondetTest
import LeanSwe.Fs.Raw.Types
import LeanSwe.Fs.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Fs.Raw`. -/

namespace LeanSwe.Fs.Raw

open Core (NondetTest)
open Core.NondetTest

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

private def stubRawDirOps : RawDirOpsM (StateM Unit) :=
  { openDir := fun p => pure (.ok { handleId := 1, rootPath := p })
    openDirAt := fun _ n => pure (.ok { handleId := 2, rootPath := n.val })
    closeDir := fun _ => pure (.ok ())
    fstatDir := fun _ => pure (.ok (stubStat .dir))
    lstatAt := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    readDirAt := fun _ => pure (.ok #[])
    createDirAt := fun _ _ => pure (.ok ())
    readRegularAt := fun _ _ => pure (.ok ByteArray.empty)
    createFileAt := fun _ _ _ => pure (.ok ())
    renameAt := fun _ _ _ _ => pure (.ok ())
    unlinkAt := fun _ _ _ => pure (.ok ())
    symlinkAt := fun _ _ _ => pure (.ok ())
    acquireLockAt := fun _ n mode _ _ => pure (.ok { handleId := 1, path := n.val, mode := mode })
    releaseLock := fun _ => pure (.ok ())
    freshTempName := pure (EntryName.lit ".t.0") }

example : ¬ Core.AllPass (test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState
    { stubRawDirOps with
      lstatAt := fun _ _ => pure (.ok (stubStat .symlink))
      openDirAt := fun _ n => pure (.ok { handleId := 2, rootPath := n.val }) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" } (EntryName.lit "sym") ⟨stubStat .symlink, rfl, rfl⟩
  simp [StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir
    { stubRawDirOps with
      lstatAt := fun _ _ => pure (.ok (stubStat .symlink))
      readRegularAt := fun _ _ => pure (.ok ByteArray.empty) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" } (EntryName.lit "sym")
  simp [stubStat, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow
    { stubRawDirOps with
      lstatAt := fun _ _ => pure (.ok (stubStat .symlink))
      createFileAt := fun _ _ _ => pure (.ok ()) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" } (EntryName.lit "f") ByteArray.empty
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
  simp [stubStat, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting
    { stubRawDirOps with
      lstatAt := fun _ _ => pure (.ok (stubStat .symlink))
      createDirAt := fun _ _ => pure (.ok ()) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" } (EntryName.lit "d")
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
  simp [stubStat, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics
    { stubRawDirOps with
      lstatAt := fun _ _ => pure (.ok (stubStat .symlink))
      unlinkAt := fun _ _ _ => pure (.ok ()) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" } (EntryName.lit "sym")
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
  simp [stubRawDirOps, stubStat, StateT.run, Bind.bind, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_rawDirOps_closedHandleRejected stubRawDirOps) := by
  intro h
  have h0 := h () "/" (EntryName.lit "c") ByteArray.empty
  simp [stubRawDirOps, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_rawDirOps_fstatDir_validReturnsDir
    { stubRawDirOps with fstatDir := fun _ => pure (.ok (stubStat .file)) }) := by
  intro h
  have h0 := h () "/"
  simp [stubStat, StateT.run, pure, assert] at h0
  rcases h0.1 with ⟨st, hst, hkind⟩
  cases hst
  cases hkind

example : ¬ Core.AllPass (test_fsraw_rawDirOps_readDirAt_sortedUnique
    { stubRawDirOps with readDirAt := fun _ => pure (.ok #[EntryName.lit "a", EntryName.lit "a"]) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" }
  simp [StateT.run, pure, assert] at h0
  exact (List.nodup_cons.mp h0.1).1 (by simp)

example : ¬ Core.AllPass (test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch
    { stubRawDirOps with
      lstatAt := fun _ n =>
        pure (if n.val == "d" then .ok (stubStat .dir) else .ok (stubStat .file))
      renameAt := fun _ _ _ _ => pure (.ok ()) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" } (EntryName.lit "d")
    { handleId := 1, rootPath := "/" } (EntryName.lit "f")
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
  simp [stubStat, StateT.run, pure, assert, EntryName.lit] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget
    { stubRawDirOps with symlinkAt := fun _ _ _ => pure (.ok ()) }) := by
  intro h
  have h0 := h () { handleId := 1, rootPath := "/" } (EntryName.lit "s") ""
  simp [StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe
    (fun _ => .ok (EntryName.lit "fallback"))) := by
  intro h
  have h0 := h ""
  simp [assert] at h0

example : ¬ Core.AllPass (test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot
    (fun _ => .ok RelPath.root) RelPath.parseRoot) := by
  intro h
  have h0 := h "x"
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot
    (fun _ => .error { kind := .invalidInput, message := "nope" }) RelPath.parseRoot) := by
  intro h
  have h0 := h "x"
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_fsraw_rawDirOps_freshTempName_distinctAndValid stubRawDirOps) := by
  intro h
  have h0 := h ()
  simp [stubRawDirOps, StateT.run, pure, assert] at h0
  exact h0.1.2.2 rfl

example : ¬ Core.AllPass (test_fsraw_isValidDirHandleId_bounds (fun _ => true)) := by
  intro h
  have h0 := h 0
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_fsraw_isValidDirHandleId_bounds (fun id => decide (0 < id))) := by
  intro h
  have h0 := h UInt64.size
  simp [Bind.bind, assert] at h0

end LeanSwe.Fs.Raw
