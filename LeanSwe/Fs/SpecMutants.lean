import Core.NondetTest
import LeanSwe.Fs.Types
import LeanSwe.Fs.Model
import LeanSwe.Fs.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Fs`. -/

namespace LeanSwe.Fs

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Fs.Model hiding isValidRawPath

private def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

private def buggyEmptyErrApi (base : FsApi) : FsApi :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyNormApi (base : FsApi) : FsApi :=
  { base with normPath := fun p => p ++ "/a" }

private def buggyWithNameApi (base : FsApi) : FsApi :=
  { base with
    withName := fun _ _ => .ok "/wrong"
    name := fun _ => some "wrong" }

private def stubFsApi : FsApi :=
  { join := fun _ s => s
    joinMany := fun _ => ""
    normPath := fun _ => "."
    parent := fun _ => none
    name := fun _ => none
    stem := fun _ => none
    suffix := fun _ => ""
    suffixes := fun _ => #[]
    withName := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    withSuffix := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    isAbsolute := fun s => s.toList.head? == some '/'
    relativeTo := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    mapRawError := fun _ => { kind := .ioError, message := "stub" }
    readText := fun _ => pure (.ok "")
    writeText := fun _ _ => pure (.ok ())
    appendText := fun _ _ => pure (.ok ())
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    atomicWriteBytes := fun _ _ => pure (.ok ())
    atomicWriteText := fun _ _ => pure (.ok ())
    touch := fun _ _ => pure (.ok ())
    mkdir := fun _ _ _ => pure (.ok ())
    unlink := fun _ _ => pure (.ok ())
    rmdir := fun _ => pure (.ok ())
    rmtree := fun _ _ => pure (.ok ())
    rename := fun _ _ => pure (.ok ())
    copyFile := fun _ _ => pure (.ok ())
    copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun _ => pure (.ok false)
    isFile := fun _ => pure (.ok false)
    isDir := fun _ => pure (.ok false)
    isSymlink := fun _ => pure (.ok false)
    stat := fun _ => pure (.error { kind := .notFound, message := "stub" })
    lstat := fun _ => pure (.error { kind := .notFound, message := "stub" })
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
    resolve := fun _ => pure (.error { kind := .notFound, message := "stub" })
    cwd := pure (.ok ".")
    listDir := fun _ => pure (.ok #[])
    walk := fun _ => pure (.ok #[])
    glob := fun _ _ => pure (.ok #[])
    rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun _ _ _ act => act
    tryWithFileLock := fun _ _ _ act => do
      match ← act with
      | .ok a => return .ok (some a)
      | .error e => return .error e }

private def buggySuffixesApi (base : FsApi) : FsApi :=
  { base with suffixes := fun _ => #[] }

private def stubStat (kind : EntryKind) : FileStat :=
  { kind := kind
    byteSize := 0
    mode := 0o755
    modifiedSec := 0
    modifiedNsec := 0
    accessedSec := 0
    accessedNsec := 0 }

private def stubVfsApi : FsApiM (StateM Unit) :=
  { join := fun a b => if b.toList.head? == some '/' then b else if a == "" then b else a ++ "/" ++ b
    joinMany := fun _ => ""
    normPath := fun p => p
    parent := fun _ => none
    name := fun _ => none
    stem := fun _ => none
    suffix := fun _ => ""
    suffixes := fun _ => #[]
    withName := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    withSuffix := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    isAbsolute := fun s => s.toList.head? == some '/'
    relativeTo := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    mapRawError := fun _ => { kind := .ioError, message := "stub" }
    readText := fun _ => pure (.ok "")
    writeText := fun _ _ => pure (.ok ())
    appendText := fun _ _ => pure (.ok ())
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    atomicWriteBytes := fun _ _ => pure (.ok ())
    atomicWriteText := fun _ _ => pure (.ok ())
    touch := fun _ _ => pure (.ok ())
    mkdir := fun _ _ _ => pure (.ok ())
    unlink := fun _ _ => pure (.ok ())
    rmdir := fun _ => pure (.ok ())
    rmtree := fun _ _ => pure (.ok ())
    rename := fun _ _ => pure (.ok ())
    copyFile := fun _ _ => pure (.ok ())
    copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun _ => pure (.ok false)
    isFile := fun _ => pure (.ok false)
    isDir := fun _ => pure (.ok false)
    isSymlink := fun _ => pure (.ok false)
    stat := fun _ => pure (.ok (stubStat .dir))
    lstat := fun _ => pure (.ok (stubStat .symlink))
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
    resolve := fun p => pure (.ok p)
    cwd := pure (.ok "/")
    listDir := fun _ => pure (.ok #[])
    walk := fun _ => pure (.ok #[])
    glob := fun _ _ => pure (.ok #[])
    rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun _ _ _ act => act
    tryWithFileLock := fun _ _ _ act => do
      match ← act with
      | .ok a => return .ok (some a)
      | .error e => return .error e }

example : ¬ Core.AllPass (test_fs_mapRawError_returnsNonEmptyMessage (buggyEmptyErrApi stubFsApi)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrApi, assert] at h0

example : ¬ Core.AllPass (test_fs_normPath_idempotent (buggyNormApi stubFsApi)) := by
  intro h
  have h0 := h "x"
  simp [buggyNormApi, assert] at h0

example : ¬ Core.AllPass (test_fs_withName_updatesName (buggyWithNameApi stubFsApi)) := by
  intro h
  have h0 := h "/a/b" "c"
  simp [buggyWithNameApi, assert] at h0

example : ¬ Core.AllPass (test_fs_suffixes_doubleDot (buggySuffixesApi stubFsApi)) := by
  intro h
  have h0 := h "a" (by decide) (by decide) (by decide)
  simp [buggySuffixesApi, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_mkdir_existingFails stubVfsApi) := by
  intro h
  have h0 := h () "/existing" true rfl
  simp [stubVfsApi, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_touch_existingFails stubVfsApi) := by
  intro h
  have h0 := h () "/broken_symlink" rfl
  simp [stubVfsApi, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_walk_preservesStatError
    { stubVfsApi with
      stat := fun _ => pure (.error { kind := .permissionDenied, message := "EACCES" })
      walk := fun _ => pure (.error { kind := .notFound, message := "ENOENT" }) }) := by
  intro h
  have h0 := h () "/locked"
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_copyTree_selfCopyRejected stubVfsApi) := by
  intro h
  have h0 := h () "/dir" "/dir"
    ⟨stubStat .dir, rfl, rfl⟩
    ⟨"/dir", rfl, by decide, by decide, rfl, Or.inl rfl⟩
  simp [stubVfsApi, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_mkdir_parentsCreatesDir stubVfsApi) := by
  intro h
  have h0 := h () "/a/b" rfl
  simp [stubVfsApi, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_copyTree_createsMissingParents
    { stubVfsApi with
      stat := fun p =>
        if p == "/new_parent" then pure (.error { kind := .notFound, message := "stub" })
        else pure (.ok (stubStat .dir))
      lstat := fun _ => pure (.error { kind := .notFound, message := "stub" })
      isDir := fun _ => pure (.ok false)
      copyTree := fun _ _ _ => pure (.error { kind := .notFound, message := "bug" }) }) := by
  intro h
  have h0 := h () "/src"
    ⟨stubStat .dir, rfl, rfl, by decide, by decide, rfl⟩
    ⟨stubStat .dir, rfl, rfl⟩
    ⟨"/src", rfl, by decide, by decide, by decide, by decide⟩
    rfl rfl rfl rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_copyTree_loopRejected
    { stubVfsApi with
      resolve := fun p => if p == "/src/self" then pure (.ok "/src") else pure (.ok p)
      listDir := fun _ => pure (.ok #["self"])
      lstat := fun _ => pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "/src"
    ⟨stubStat .dir, rfl, rfl, by decide, by decide, rfl⟩
    ⟨stubStat .dir, rfl, rfl⟩
    ⟨"/src", rfl, by decide, by decide, by decide, rfl⟩
    rfl ⟨stubStat .dir, rfl, rfl⟩ rfl
  simp [stubVfsApi, StateT.run, pure, StateT.pure, assert] at h0

private def stubBoolFsApi : FsApiM (StateM Bool) :=
  { join := stubFsApi.join
    joinMany := stubFsApi.joinMany
    normPath := stubFsApi.normPath
    parent := stubFsApi.parent
    name := stubFsApi.name
    stem := stubFsApi.stem
    suffix := stubFsApi.suffix
    suffixes := stubFsApi.suffixes
    withName := stubFsApi.withName
    withSuffix := stubFsApi.withSuffix
    isAbsolute := stubFsApi.isAbsolute
    relativeTo := stubFsApi.relativeTo
    mapRawError := stubFsApi.mapRawError
    readText := fun _ => pure (.ok "")
    writeText := fun _ _ => pure (.ok ())
    appendText := fun _ _ => pure (.ok ())
    readBytes := fun _ s =>
      if s then (.ok ByteArray.empty, s)
      else (.ok (ByteArray.mk #[1, 2, 3]), s)
    writeBytes := fun _ _ => pure (.ok ())
    atomicWriteBytes := fun _ _ => pure (.ok ())
    atomicWriteText := fun _ _ => pure (.ok ())
    touch := fun _ _ => pure (.ok ())
    mkdir := fun _ _ _ => pure (.ok ())
    unlink := fun _ _ => pure (.ok ())
    rmdir := fun _ => pure (.ok ())
    rmtree := fun _ _ => pure (.ok ())
    rename := fun _ _ => pure (.ok ())
    copyFile := fun _ _ => pure (.ok ())
    copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun _ => pure (.ok false)
    isFile := fun _ => pure (.ok false)
    isDir := fun _ => pure (.ok false)
    isSymlink := fun _ => pure (.ok false)
    stat := fun _ => pure (.ok (stubStat .file))
    lstat := fun _ => pure (.ok (stubStat .file))
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
    resolve := fun p => pure (.ok p)
    cwd := pure (.ok "/")
    listDir := fun _ => pure (.ok #[])
    walk := fun _ => pure (.ok #[])
    glob := fun _ _ => pure (.ok #[])
    rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun _ _ _ act => act
    tryWithFileLock := fun _ _ _ act s =>
      if s then (.ok none, s)
      else
        match act s with
        | (.ok a, s') => (.ok (some a), s')
        | (.error e, s') => (.error e, s') }

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_releasesOnOk
    { stubBoolFsApi with
      withFileLock := fun {_} _ mode _ act s =>
        let s' := match mode with
          | .shared => true
          | .exclusive => s
        act s' }) := by
  intro h
  have h0 := h false "/a.lock" .shared true 7 rfl
  simp [stubBoolFsApi, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_releasesOnError
    { stubVfsApi with
      withFileLock := fun {_} _ _ _ _ => pure (.error { kind := .ioError, message := "wrong" }) }) := by
  intro h
  have h0 := h () "/a.lock" .shared false { kind := .notFound, message := "boom" } rfl
  simp [stubVfsApi, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_tryWithFileLock_sharedCoexists
    { stubVfsApi with
      tryWithFileLock := fun {_} _ _ _ _ => pure (.ok none) }) := by
  intro h
  have h0 := h () "/a.lock" 42 rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_tryWithFileLock_exclusiveRejects
    { stubVfsApi with
      lstat := fun p =>
        if p == "/a.lock" then pure (.ok (stubStat .file))
        else pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "/a.lock" "/marker" .exclusive .exclusive (Or.inl rfl) rfl rfl
  simp [stubVfsApi, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_missingNotCreated
    { stubVfsApi with
      lstat := fun _ => pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "/missing.lock" .exclusive
    (by decide) (Or.inr (by decide))
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_symlinkRejected
    { stubVfsApi with
      lstat := fun p =>
        if p == "/sym.lock" then pure (.ok (stubStat .symlink))
        else pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "/sym.lock" "/marker" .exclusive true
    (by decide) (Or.inr (by decide))
    ⟨stubStat .symlink, rfl, rfl⟩ rfl
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_dirRejected
    { stubVfsApi with
      lstat := fun p =>
        if p == "/dir" then pure (.ok (stubStat .dir))
        else pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "/dir" "/marker" .exclusive true
    (by decide) (Or.inr (by decide))
    ⟨stubStat .dir, rfl, rfl⟩ rfl
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_createsMissingFile
    { stubVfsApi with
      lstat := fun _ => pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "/missing.lock" .exclusive
    (by decide) (Or.inr (by decide))
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩ rfl
  simp [StateT.run, pure, assert] at h0
  rcases h0 with ⟨st, hst, _⟩
  cases hst

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_preservesExistingBytes
    { stubBoolFsApi with
      withFileLock := fun {_} _ _ _ act _ => act true }) := by
  intro h
  have h0 := h false "/existing.lock" .exclusive true
    (by decide) (Or.inr (by decide)) rfl
  simp [stubBoolFsApi, StateT.run, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_fs_vfs_withFileLock_invalidPathRejected
    { stubVfsApi with
      lstat := fun _ => pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "" "/marker" .exclusive true (Or.inl rfl) (by decide)
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_tryWithFileLock_releasesOnOk
    { stubBoolFsApi with
      tryWithFileLock := fun {_} _ mode _ act s =>
        if s then (.ok none, s)
        else
          let s1 := match mode with
            | .shared => true
            | .exclusive => s
          match act s1 with
          | (.ok a, s2) => (.ok (some a), s2)
          | (.error e, s2) => (.error e, s2) }) := by
  intro h
  have h0 := h false "/a.lock" .shared true 7 rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_tryWithFileLock_missingNotSwallowed
    { stubVfsApi with
      lstat := fun _ => pure (.error { kind := .notFound, message := "stub" })
      tryWithFileLock := fun {_} _ _ _ _ => pure (.ok none) }) := by
  intro h
  have h0 := h () "/missing.lock" "/marker" .exclusive
    (by decide) (Or.inr (by decide))
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩ rfl
  simp [StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_tryWithFileLock_releasesOnActionError
    { stubVfsApi with
      tryWithFileLock := fun {_} _ _ _ act => do
        match ← act with
        | .ok a => return .ok (some a)
        | .error _ => return .ok none }) := by
  intro h
  have h0 := h () "/a.lock" .shared false { kind := .notFound, message := "boom" } rfl
  simp [StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0

private def stubVfsRawOps : RawFsOpsM (StateM Unit) :=
  { mapRawError := fun _ => { kind := .ioError, message := "stub" }
    stat := fun _ p =>
      if p == "/" then pure (.ok (stubStat .dir))
      else pure (.error { kind := .notFound, message := "stub" })
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

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_writesAtomically
    (fun _ => { stubVfsApi with atomicWriteBytes := fun _ _ => pure (.error { kind := .ioError, message := "bug" }) })
    stubVfsRawOps) := by
  intro h
  have h0 := h () "a.bin" ByteArray.empty (by decide)
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    rfl (Or.inl ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩)
  simp [stubVfsApi, StateT.run, bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget
    (fun _ => { stubVfsApi with atomicWriteBytes := fun _ _ => pure (.ok ()) })
    { stubVfsRawOps with
      stat := fun _ p =>
        if p == "/" then pure (.ok (stubStat .dir))
        else pure (.ok (stubStat .symlink)) }) := by
  intro h
  have h0 := h () "a.bin" "/victim" ByteArray.empty ByteArray.empty ByteArray.empty (by decide)
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    rfl rfl rfl
  simp [stubVfsRawOps, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget
    (fun _ => { stubVfsApi with atomicWriteBytes := fun _ _ => pure (.ok ()) })
    stubVfsRawOps) := by
  intro h
  have h0 := h () "a.bin" ByteArray.empty ByteArray.empty { kind := .permissionDenied, message := "EACCES" }
    (by decide) ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩ rfl rfl
  simp [stubVfsRawOps, StateT.run, bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget
    (fun ops =>
      { stubBoolFsApi with
        atomicWriteBytes := fun _ _ => do
          let _ ← ops.createFileNew "/.a.bin.tmp.0" ByteArray.empty
          ops.rename "/.a.bin.tmp.0" "/a.bin" })
    { mapRawError := stubVfsRawOps.mapRawError
      stat := fun _ p s =>
        if p == "/" then (.ok (stubStat .dir), s)
        else if s then (.ok (stubStat .file), s)
        else (.error { kind := .notFound, message := "absent" }, s)
      readDir := fun _ => pure (.ok #[])
      createDir := fun _ => pure (.ok ())
      removeDir := fun _ => pure (.ok ())
      unlinkFile := fun _ _ => (.ok (), false)
      readBytes := fun _ => pure (.ok ByteArray.empty)
      writeBytes := fun _ _ => pure (.ok ())
      createFileNew := fun _ _ _ => (.ok (), true)
      appendText := fun _ _ => pure (.ok ())
      rename := fun _ _ => pure (.ok ())
      chmod := fun _ _ => pure (.ok ())
      symlink := fun _ _ => pure (.ok ())
      readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
      realPath := fun _ => pure (.error { kind := .notFound, message := "stub" })
      cwd := pure (.ok "/")
      monotonicNonce := pure 0
      acquireLock := fun path mode _ _ => pure (.ok { handleId := 1, path := path, mode := mode })
      releaseLock := fun _ => pure (.ok ()) }) := by
  intro h
  have h0 := h false "a.bin" ByteArray.empty ByteArray.empty { kind := .permissionDenied, message := "EACCES" }
    (by decide) ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩ rfl rfl
  simp [StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0
  split at h0 <;> simp [Except.isOk, Except.toBool] at h0

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteText_writesAtomically
    (fun _ => { stubVfsApi with atomicWriteText := fun _ _ => pure (.error { kind := .ioError, message := "bug" }) })
    stubVfsRawOps) := by
  intro h
  have h0 := h () "a.txt" "hi" (by decide)
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    rfl (Or.inl ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩)
  simp [stubVfsApi, StateT.run, bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget
    (fun _ => { stubVfsApi with atomicWriteText := fun _ _ => pure (.ok ()) })
    { stubVfsRawOps with
      stat := fun _ p =>
        if p == "/" then pure (.ok (stubStat .dir))
        else pure (.ok (stubStat .symlink)) }) := by
  intro h
  have h0 := h () "a.txt" "/victim" "new" ByteArray.empty ByteArray.empty (by decide)
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    rfl rfl rfl
  simp [stubVfsRawOps, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_invalidPathRejected
    (fun _ => stubVfsApi) stubVfsRawOps) := by
  intro h
  have h0 := h () "" ByteArray.empty (by decide)
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteText_invalidPathRejected
    (fun _ => stubVfsApi) stubVfsRawOps) := by
  intro h
  have h0 := h () "/dir/." "hi" (by decide)
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_dirRejected
    (fun _ => stubVfsApi) stubVfsRawOps) := by
  intro h
  have h0 := h () "/" ByteArray.empty (by decide) (Or.inl rfl)
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteText_dirRejected
    (fun _ => stubVfsApi) stubVfsRawOps) := by
  intro h
  have h0 := h () "/" "hi" (by decide) (Or.inl rfl)
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated
    (fun _ => stubVfsApi)
    { stubVfsRawOps with
      stat := fun _ _ => pure (.error { kind := .permissionDenied, message := "EACCES" }) }) := by
  intro h
  have h0 := h () "/locked/file" ByteArray.empty (And.intro (by decide) (by decide))
    ⟨{ kind := .permissionDenied, message := "EACCES" }, rfl, by decide⟩
  simp [stubVfsApi, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically
    (fun _ => { stubVfsApi with atomicWriteBytes := fun _ _ => pure (.error { kind := .alreadyExists, message := "bug" }) })
    { stubVfsRawOps with
      stat := fun _ p =>
        if p == "/" then pure (.ok (stubStat .dir))
        else if p == "/sym" then pure (.ok (stubStat .symlink))
        else pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "sym" ByteArray.empty (by decide)
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    rfl ⟨stubStat .symlink, rfl, rfl⟩
  simp [stubVfsApi, StateT.run, bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_atomicWriteBytes_nestedParentAndRelative
    (fun _ => { stubVfsApi with atomicWriteBytes := fun _ _ => pure (.error { kind := .ioError, message := "bug" }) })
    { stubVfsRawOps with
      stat := fun _ p =>
        if p == "/sub" then pure (.ok (stubStat .dir))
        else pure (.error { kind := .notFound, message := "stub" }) }) := by
  intro h
  have h0 := h () "sub" "f.bin" ByteArray.empty (And.intro (by decide) (by decide))
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    rfl ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
  simp [stubVfsApi, StateT.run, bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_readBytes_followsSymlinkToRegularFile
    { stubVfsApi with
      lstat := fun _ => pure (.ok (stubStat .symlink))
      stat := fun _ => pure (.ok (stubStat .file))
      readBytes := fun _ => pure (.error { kind := .invalidInput, message := "nofollow bug" }) }) := by
  intro h
  have h0 := h () "/sym" (by decide) ⟨stubStat .symlink, rfl, rfl⟩ ⟨stubStat .file, rfl, rfl⟩
  simp [StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨bs, hbs, _⟩, _⟩
  cases hbs

example : ¬ Core.AllPass (test_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink
    (fun _ => { stubVfsApi with readBytes := fun _ => pure (.ok (ByteArray.mk #[0, 0, 0])) })
    stubVfsRawOps) := by
  intro h
  have h0 := h () "a.bin" "sym" (ByteArray.mk #[1, 2, 3])
    (And.intro (by decide) (And.intro (by decide) (by decide)))
    ⟨stubStat .dir, rfl, rfl, by decide, by decide⟩
    rfl ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
    ⟨{ kind := .notFound, message := "stub" }, rfl, rfl⟩
    rfl rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_fs_vfs_readBytes_dirAndMissingRejected
    { stubVfsApi with
      stat := fun _ => pure (.ok (stubStat .dir))
      readBytes := fun _ => pure (.ok ByteArray.empty) }) := by
  intro h
  have h0 := h () "/dir" (by decide)
  simp [StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_vfs_readBytes_invalidPathRejected stubVfsApi) := by
  intro h
  have h0 := h () "" (by decide)
  simp [stubVfsApi, StateT.run, pure, assert] at h0
  rcases h0 with ⟨⟨e, he, _⟩, _⟩
  cases he

private def stubSubtree : SubtreeM (StateM VfsState) :=
  { lstat := fun _ => pure (.error { kind := .notFound, message := "stub" })
    readRegular := fun _ => pure (.error { kind := .notFound, message := "stub" })
    atomicWriteBytes := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    mkdir := fun _ _ _ => pure (.error { kind := .notFound, message := "stub" })
    unlink := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    rmdir := fun _ => pure (.error { kind := .notFound, message := "stub" })
    rmtree := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    symlink := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    listDir := fun _ => pure (.error { kind := .notFound, message := "stub" })
    walk := fun _ => pure (.error { kind := .notFound, message := "stub" })
    withFileLock := fun _ _ _ _ => pure (.error { kind := .notFound, message := "stub" })
    tryWithFileLock := fun _ _ _ _ => pure (.error { kind := .notFound, message := "stub" }) }

private def stubMkSubtree : SubtreeBuilder (StateM VfsState) :=
  fun _ _ => stubSubtree

private def stubMkOpener : SubtreeOpenerBuilder (StateM VfsState) :=
  fun _ => { withSubtree := fun _ act => act stubSubtree }

private def emptyVfsState : VfsState :=
  { tree := vfsEmptyDir 0o755
    keys := ["/"]
    cwd := "/"
    nonce := 0
    locks := []
    nextLockId := 1
    openDirs := []
    nextDirId := 1 }

private def rootHandle : DirHandle :=
  { handleId := 1, rootPath := "/" }

private def stateWithRootHandle (rootChildren : String → Option VfsTree) (keys : List String := ["/"]) : VfsState :=
  { tree := .dir 0o755 rootChildren
    keys := keys
    cwd := "/"
    nonce := 0
    locks := []
    nextLockId := 1
    openDirs := [(1, [])]
    nextDirId := 2 }

private def s51 : String :=
  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

private def str255 : String :=
  s51 ++ s51 ++ s51 ++ s51 ++ s51

private theorem str255_valid : validSeg str255 = true := by
  have h1 : s51 ≠ "" := by decide
  have h2 : '/' ∉ s51.toList := by decide
  have h3 : Char.ofNat 0 ∉ s51.toList := by decide
  have hl : s51.toList.length = 51 := by decide
  have hneDot : s51.toList ++ (s51.toList ++ (s51.toList ++ (s51.toList ++ s51.toList))) ≠ ['.'] := by
    intro he; have hc := congrArg List.length he; simp [hl] at hc
  have hneDotDot : s51.toList ++ (s51.toList ++ (s51.toList ++ (s51.toList ++ s51.toList))) ≠ ['.', '.'] := by
    intro he; have hc := congrArg List.length he; simp [hl] at hc
  simpa [validSeg, str255, String.toList_append, List.append_assoc] using
    ⟨⟨⟨⟨h1, h2⟩, h3⟩, hneDot⟩, hneDotDot⟩

private theorem str255_utf8ByteSize : str255.utf8ByteSize = 255 := by
  have h51 : s51.utf8ByteSize = 51 := by decide
  simp [str255, String.utf8ByteSize_append, h51]

private def maxName255 : EntryName :=
  { val := str255, valid := str255_valid }

example : ¬ Core.AllPass (test_fs_withSubtree_validatesRootAndAlwaysClosesHandle stubMkOpener) := by
  intro h
  have h0 := h emptyVfsState "" (.ok ()) (by intro _ _ hm; cases hm)
  simp [stubMkOpener, emptyVfsState, Model.isValidRawPath, assert] at h0
  rcases h0 with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_subtree_leafSymlink_followsExactLeafTable
    (fun _ _ => { stubSubtree with readRegular := fun _ => pure (.ok ByteArray.empty) })) := by
  intro h
  let st := stateWithRootHandle (fun s => if s == "sym" then some (.symlink "t" 0o777) else none) ["/", "/sym"]
  let h0 := h st rootHandle [] [] (EntryName.lit "sym") "t" 0o777 ByteArray.empty .exclusive false false
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    (fun k hk => ⟨0o755, by cases k <;> simp [List.take, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode], by decide, by decide⟩)
    ⟨0o755, rfl, by decide, by decide⟩ rfl rfl
  simp [stubSubtree, StateT.run, Bind.bind, pure, assert] at h0
  rcases h0 with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_subtree_rootPath_enforcesRootRules
    (fun _ _ => { stubSubtree with
      lstat := fun _ => pure (.ok (stubStat .dir))
      mkdir := fun _ _ existOk => if existOk then pure (.ok ()) else pure (.error { kind := .alreadyExists, message := "exists" })
      readRegular := fun _ => pure (.error { kind := .isADirectory, message := "dir" })
      atomicWriteBytes := fun _ _ => pure (.ok ()) })) := by
  intro h
  let st := stateWithRootHandle (fun _ => none)
  have h0 := h st rootHandle [] 0o755 ByteArray.empty .exclusive false "t"
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    rfl
  simp [stubSubtree, stubStat, st, stateWithRootHandle, StateT.run, Bind.bind, pure, assert] at h0
  rcases h0 with ⟨_, _, _, _, ⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle
    (fun s => if s == ".t.0" then some (.file ByteArray.empty 0o600) else none)
    ["/", "/.t.0"]
  have hne : maxName255.val ≠ ".t.0" := by
    intro heq
    have hlen := congrArg String.utf8ByteSize heq
    have hs : (".t.0" : String).utf8ByteSize = 4 := by decide
    rw [show maxName255.val = str255 from rfl, str255_utf8ByteSize, hs] at hlen
    cases hlen
  have hne2 : maxName255.val ≠ ".t.1" := by
    intro heq
    have hlen := congrArg String.utf8ByteSize heq
    have hs : (".t.1" : String).utf8ByteSize = 4 := by decide
    rw [show maxName255.val = str255 from rfl, str255_utf8ByteSize, hs] at hlen
    cases hlen
  have hnot : (match nodeAt st.tree [maxName255.val] with | some (.dir _) => False | _ => True) := by
    have hbeq : (maxName255.val == ".t.0") = false := beq_false_of_ne hne
    dsimp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
    rw [hbeq]
    trivial
  have heq0 : ".t." ++ Nat.repr 0 = ".t.0" := by decide
  have heq1 : ".t." ++ Nat.repr 1 = ".t.1" := by decide
  have hne1 : ".t." ++ Nat.repr 1 ≠ ".t.0" := by decide
  have h0 := h st rootHandle [] ByteArray.empty maxName255
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    str255_utf8ByteSize ⟨0o755, rfl, by decide, by decide⟩
    (by simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode, heq0])
    (by simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, hne1])
    ⟨by simpa [st, stateWithRootHandle, toString, heq0] using hne,
     by simpa [st, stateWithRootHandle, toString, heq1] using hne2⟩
    hnot
  simp only [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0
  cases h0.1

example : ¬ Core.AllPass (test_fs_subtree_mkdir_existOkPreservesExistingDir stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun s => if s == "d" then some (vfsEmptyDir 0o700) else none) ["/", "/d"]
  have h0 := h st rootHandle [] (EntryName.lit "d") 0o755 0o700 false
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    ⟨rfl, by decide⟩ (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode, vfsEmptyDir])
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun
    | "s" => some (.symlink "d" 0o777)
    | "d" => some (.dir 0o755 (fun s => if s == "c" then some (.file ByteArray.empty 0o644) else none))
    | _ => none) ["/", "/s", "/d", "/d/c"]
  have hKeys : VfsKeysComplete st := by
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, st, stateWithRootHandle]
    · by_cases ha : a = "s"
      · subst ha
        rcases r1 with _ | ⟨b, r2⟩
        · simp [pathOfSegs, st, stateWithRootHandle]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
      · by_cases had : a = "d"
        · subst had
          rcases r1 with _ | ⟨b, r2⟩
          · simp [pathOfSegs, st, stateWithRootHandle]
          · by_cases hb : b = "c"
            · subst hb
              rcases r2 with _ | ⟨c, r3⟩
              · simp [pathOfSegs, st, stateWithRootHandle]
              · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
            · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, hb]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
  have hWalkable : ∀ tsub, vfsTreeGet st.tree [] = some tsub → VfsTreeWalkable 4096 tsub := by
    intro tsub hget
    simp [st, stateWithRootHandle, vfsTreeGet] at hget
    subst hget
    refine ⟨by decide, by decide, ?_⟩
    intro name sub hch
    by_cases hn1 : name = "s"
    · subst hn1; simp at hch; subst hch; trivial
    · by_cases hn2 : name = "d"
      · subst hn2; simp at hch; subst hch
        refine ⟨by decide, by decide, ?_⟩
        intro n2 sub2 hch2
        by_cases hn3 : n2 = "c"
        · subst hn3; simp at hch2; subst hch2; trivial
        · simp [hn3] at hch2
      · simp at hch
  have h0 := h st rootHandle [] (EntryName.lit "c") (EntryName.lit "s") (EntryName.lit "d")
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    hKeys (fun _ hm => by cases hm) (by decide) hWalkable (by decide) ⟨0o755, rfl, by decide, by decide⟩ rfl rfl rfl
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun s => if s == "f" then some (.file ByteArray.empty 0o644) else none) ["/", "/f"]
  have h0 := h st rootHandle [] (EntryName.lit "f") .exclusive
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    ⟨0o755, rfl, by decide⟩ ⟨0o644, rfl⟩ (by decide)
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_sameOutside_confinesAllOps
    (fun _ _ => { stubSubtree with
      lstat := fun _ st => (.error { kind := .notFound, message := "mutated" },
        { st with tree := vfsTreeSet st.tree ["outside"] (some (.file ByteArray.empty 0o644)) }) })) := by
  intro h
  rcases h with ⟨hp, _⟩
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "sub" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/sub"]
      cwd := "/"
      nonce := 0
      locks := []
      nextLockId := 1
      openDirs := [(1, ["sub"])]
      nextDirId := 2 }
  let subDh : DirHandle := { handleId := 1, rootPath := "/sub" }
  have h0 := hp st subDh ["sub"] RelPath.root ByteArray.empty false false "t" .exclusive Unit (.ok ())
    rfl ⟨0o755, rfl⟩
  rcases h0 with ⟨hSame, _⟩
  have hout := hSame "/outside" (by decide)
  have hcanon : isCanonPath "/outside" = true := by decide
  have hsegs : vfsSplitSegs "/outside" = ["outside"] := by decide
  simp [StateT.run, VfsState.nodes, vfsTreeNodes, hcanon, hsegs, st, nodeAt, vfsTreeSet, vfsTreeGet, vfsTreeTopNode] at hout

example : ¬ Core.AllPass (test_fs_subtree_noSymlinkFollowAncestors_refusesAllOps stubMkSubtree) := by
  intro h
  rcases h with ⟨hp, _⟩
  let st := stateWithRootHandle (fun s => if s == "sym" then some (.symlink "t" 0o777) else none) ["/", "/sym"]
  have h0 := hp st rootHandle [] [EntryName.lit "sym"] [EntryName.lit "leaf"] "t" 0o777 ByteArray.empty false false "t" .exclusive Unit (.ok ())
    rfl (by decide)
    (fun k hk => ⟨0o755, by cases k <;> simp at hk; simp [List.take, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode], by decide, by decide⟩)
    ⟨0o755, rfl, by decide⟩ rfl
  rcases h0 with ⟨⟨⟨e, he, hk⟩, _⟩, _⟩
  cases he
  cases hk

example : ¬ Core.AllPass (test_fs_subtree_programSameOutsideInterleaved_confinesPrograms
    (fun _ => { withSubtree := fun _ _ st =>
      (.error { kind := .ioError, message := "escape" },
        { st with tree := vfsTreeSet st.tree ["outside"] (some (.file ByteArray.empty 0o644)) }) })) := by
  intro h
  rcases h with ⟨hp, _⟩
  let st := stateWithRootHandle (fun s => if s == "sub" then some (vfsEmptyDir 0o755) else none) ["/", "/sub"]
  have hrootNode : st.nodes "/" = some (.dir 0o755) := by
    have hc : isCanonPath "/" = true := by decide
    have hs : vfsSplitSegs "/" = [] := by decide
    simp [VfsState.nodes, vfsTreeNodes, hc, hs, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]
  have hsubNode : st.nodes "/sub" = some (.dir 0o755) := by
    have hc : isCanonPath "/sub" = true := by decide
    have hs : vfsSplitSegs "/sub" = ["sub"] := by decide
    simp [VfsState.nodes, vfsTreeNodes, hc, hs, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode, vfsEmptyDir]
  have h0 := hp Unit id "/sub" st ["sub"] 0o755 (.pure (.ok ()))
    (by intro s hs; simp at hs; subst hs; decide)
    (fun s => ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩)
    (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    (by decide)
    (by
      rw [show vfsSplitSegs (vfsAbsNorm st.cwd "/sub") = ["sub"] from by decide]
      rw [vfsResolveSegs, hrootNode]
      dsimp
      rw [vfsResolveSegs]
      rw [show vfsChildPath "/" "sub" = "/sub" from rfl, hsubNode]
      rfl)
    (by
      intro s hSame hcwd _ r hr
      have hrootOut : s.nodes "/" = st.nodes "/" := hSame "/" (by decide)
      have hsubOut : s.nodes "/sub" = st.nodes "/sub" := by
        have hc : isCanonPath "/sub" = true := by decide
        have hs : vfsSplitSegs "/sub" = ["sub"] := by decide
        have hnode : nodeAt s.tree ["sub"] = nodeAt st.tree ["sub"] := by assumption
        simp [VfsState.nodes, vfsTreeNodes, hc, hs, hnode]
      rw [show vfsAbsNorm s.cwd "/sub" = "/sub" from by rw [hcwd]; decide,
          show vfsSplitSegs "/sub" = ["sub"] from by decide,
          vfsResolveSegs, hrootOut, hrootNode] at hr
      dsimp at hr
      rw [vfsResolveSegs, show vfsChildPath "/" "sub" = "/sub" from rfl, hsubOut, hsubNode] at hr
      cases hr
      rfl)
  rcases h0 with ⟨hSame, _⟩
  have hout := hSame "/outside" (by decide)
  have hcanon : isCanonPath "/outside" = true := by decide
  have hsegs : vfsSplitSegs "/outside" = ["outside"] := by decide
  simp [VfsState.nodes, vfsTreeNodes, hcanon, hsegs, st, stateWithRootHandle, vfsTreeSet, nodeAt, vfsTreeGet, vfsTreeTopNode] at hout

example : ¬ Core.AllPass (test_fs_subtree_descriptorConservation_preservesOpenDirs
    stubMkOpener
    (fun _ _ => { stubSubtree with lstat := fun _ st => (.error { kind := .notFound, message := "leak" }, { st with openDirs := [] }) })) := by
  intro h
  rcases h with ⟨hp, _⟩
  let st := stateWithRootHandle (fun _ => none)
  have h0 := hp.1 st rootHandle RelPath.root ByteArray.empty false false "t" .exclusive Unit (.ok ())
    (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
  simp [stubSubtree, StateT.run, st, stateWithRootHandle] at h0

example : ¬ Core.AllPass (test_fs_vfsDirOps_invalidHandleRefused False) := by
  intro h
  exact h.1

example : ¬ Core.AllPass (test_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode stubMkSubtree) := by
  intro h
  rcases h with ⟨hp, _⟩
  let st := stateWithRootHandle (fun _ => none)
  have h0 := hp st rootHandle [] (EntryName.lit "f") ByteArray.empty
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    ⟨0o755, rfl, by decide, by decide⟩
    (by simp [st, stateWithRootHandle, nodeAt, vfsTreeGet])
    (by simp [st, stateWithRootHandle, nodeAt, vfsTreeGet])
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, pure] at h0

example : ¬ Core.AllPass (test_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds stubMkSubtree) := by
  intro h
  rcases h with ⟨hp, _⟩
  let st := stateWithRootHandle (fun _ => none)
  have h0 := hp.1 st rootHandle [] (EntryName.lit "d")
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    (fun _ hm => by cases hm) (by decide)
    ⟨0o755, rfl, by decide, by decide, by decide⟩
    (by simp [st, stateWithRootHandle, nodeAt, vfsTreeGet])
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, pure] at h0

example : ¬ Core.AllPass (test_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi stubMkSubtree) := by
  intro h
  rcases h with ⟨hp, _⟩
  let st := stateWithRootHandle (fun s => if s == "f" then some (.file ByteArray.empty 0o644) else none) ["/", "/f"]
  have h0 := hp st rootHandle [] { segments := [EntryName.lit "f"] } ByteArray.empty 0o644
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    (fun _ hm => by cases hm) (by intro hr; cases hr) (by decide)
    (fun k _ hk => ⟨0o755, by cases k <;> simp at hk; simp [List.take, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode], by decide, by decide⟩)
    (fun k hk => by simp at hk)
    rfl (by decide)
  rcases h0 with ⟨hread, _⟩
  have hfull : pathOfSegs [(EntryName.lit "f").val] = "/f" := rfl
  have hnorm : vfsAbsNorm st.cwd "/f" = "/f" := by decide
  have hsegs : vfsSplitSegs "/f" = ["f"] := by decide
  have hres : vfsResolveSegs st.nodes "/" ["f"] true 1024 = .ok ("/f", .file ByteArray.empty 0o644) := by
    rw [vfsResolveSegs]
    have hroot : st.nodes "/" = some (.dir 0o755) := by
      have hc : isCanonPath "/" = true := by decide
      have hs : vfsSplitSegs "/" = [] := by decide
      simp [VfsState.nodes, vfsTreeNodes, hc, hs, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]
    rw [hroot]
    dsimp
    rw [vfsResolveSegs]
    have hf : st.nodes (vfsChildPath "/" "f") = some (.file ByteArray.empty 0o644) := by
      have hc : isCanonPath "/f" = true := by decide
      have hs : vfsSplitSegs "/f" = ["f"] := by decide
      simp [vfsChildPath, VfsState.nodes, vfsTreeNodes, hc, hs, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]
    rw [hf]
    rfl
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, pure, vfsApi, vfsOps, vfsReadBytesPure, hfull, hnorm, hsegs, hres] at hread
  cases hread

example : ¬ Core.AllPass (test_fs_subtree_closedHandle_refusesAllOps
    (fun _ _ => { stubSubtree with lstat := fun _ => pure (.ok (stubStat .dir)) })) := by
  intro h
  have h0 := h emptyVfsState { handleId := 0, rootPath := "/" } (EntryName.lit "c") ByteArray.empty .exclusive false false rfl
  simp [stubSubtree, stubStat, StateT.run, pure, assert] at h0
  rcases h0.1 with ⟨⟨e, he, _⟩, _⟩
  cases he

example : ¬ Core.AllPass (test_fs_subtree_unlink_missingOkAndKindRules stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun
    | "f" => some (.file ByteArray.empty 0o644)
    | "d" => some (vfsEmptyDir 0o755)
    | _ => none) ["/", "/f", "/d"]
  have h0 := h st rootHandle [] (EntryName.lit "m") (EntryName.lit "f") (EntryName.lit "d")
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    ⟨0o755, rfl, by decide, by decide⟩
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet])
    ⟨ByteArray.empty, 0o644, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]⟩
    ⟨0o755, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode, vfsEmptyDir]⟩
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_rmdir_emptyAndErrors stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun
    | "e" => some (vfsEmptyDir 0o755)
    | "ne" => some (.dir 0o755 (fun s => if s == "c" then some (.file ByteArray.empty 0o644) else none))
    | "f" => some (.file ByteArray.empty 0o644)
    | _ => none) ["/", "/e", "/ne", "/ne/c", "/f"]
  have hKeys : VfsKeysComplete st := by
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, st, stateWithRootHandle]
    · by_cases hae : a = "e"
      · subst hae; rcases r1 with _ | ⟨b, _⟩
        · simp [pathOfSegs, st, stateWithRootHandle]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsEmptyDir]
      · by_cases han : a = "ne"
        · subst han; rcases r1 with _ | ⟨b, r2⟩
          · simp [pathOfSegs, st, stateWithRootHandle]
          · by_cases hbc : b = "c"
            · subst hbc; rcases r2 with _ | ⟨c, _⟩
              · simp [pathOfSegs, st, stateWithRootHandle]
              · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
            · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, hbc]
        · by_cases haf : a = "f"
          · subst haf; rcases r1 with _ | ⟨b, _⟩
            · simp [pathOfSegs, st, stateWithRootHandle]
            · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
          · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet] <;> split <;> contradiction
  have h0 := h st rootHandle [] (EntryName.lit "e") (EntryName.lit "ne") (EntryName.lit "c") (EntryName.lit "m") (EntryName.lit "f")
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    hKeys (fun _ hm => by cases hm) ⟨0o755, rfl, by decide, by decide⟩
    ⟨0o755, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode, vfsEmptyDir],
      fun s => by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsEmptyDir]⟩
    ⟨0o755, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]⟩
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet])
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet])
    ⟨ByteArray.empty, 0o644, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]⟩
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun
    | "f" => some (.file ByteArray.empty 0o644)
    | "p" => some (.dir 0o700 (fun
      | "a" => some (.file ByteArray.empty 0o644)
      | "b" => some (.dir 0o000 (fun _ => none))
      | _ => none))
    | _ => none) ["/", "/f", "/p", "/p/a", "/p/b"]
  have hKeys : VfsKeysComplete st := by
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, st, stateWithRootHandle]
    · by_cases haf : a = "f"
      · subst haf; rcases r1 with _ | ⟨b, _⟩
        · simp [pathOfSegs, st, stateWithRootHandle]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
      · by_cases hap : a = "p"
        · subst hap; rcases r1 with _ | ⟨b, r2⟩
          · simp [pathOfSegs, st, stateWithRootHandle]
          · by_cases hba : b = "a"
            · subst hba; rcases r2 with _ | ⟨c, _⟩
              · simp [pathOfSegs, st, stateWithRootHandle]
              · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
            · by_cases hbb : b = "b"
              · subst hbb; rcases r2 with _ | ⟨c, _⟩
                · simp [pathOfSegs, st, stateWithRootHandle]
                · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
              · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet] <;> split <;> contradiction
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet] <;> split <;> contradiction
  have h0 := h st rootHandle [] (EntryName.lit "m") (EntryName.lit "f") (EntryName.lit "p")
    (EntryName.lit "a") (EntryName.lit "b")
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    hKeys (fun _ hm => by cases hm) (by decide) ⟨0o755, rfl, by decide, by decide⟩
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet])
    ⟨ByteArray.empty, 0o644, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]⟩
    (by decide) rfl
    ⟨ByteArray.empty, 0o644, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]⟩
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode])
    (fun s h1 h2 => by
      simp [EntryName.lit] at h1 h2
      simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet])
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_mkdir_parentsAndExistOkRules stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun s => if s == "f" then some (.file ByteArray.empty 0o644) else none) ["/", "/f"]
  have h0 := h st rootHandle [] (EntryName.lit "p") (EntryName.lit "c") (EntryName.lit "f")
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    ⟨0o755, rfl, by decide, by decide, by decide⟩
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet])
    ⟨ByteArray.empty, 0o644, by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode]⟩
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_symlink_createsAndValidatesTarget stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun _ => none)
  have h0 := h st rootHandle [] (EntryName.lit "s") "" "t"
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    (Or.inl rfl) ⟨by decide, by decide⟩ ⟨0o755, rfl, by decide, by decide⟩
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet])
  simp [stubMkSubtree, stubSubtree, StateT.run, StateT.pure, Pure.pure, Bind.bind, pure, assert] at h0

example : ¬ Core.AllPass (test_fs_subtree_walk_errorsAndDepth stubMkSubtree) := by
  intro h
  let st := stateWithRootHandle (fun s => if s == "u" then some (vfsEmptyDir 0o111) else none) ["/", "/u"]
  have hKeys : VfsKeysComplete st := by
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, st, stateWithRootHandle]
    · by_cases hau : a = "u"
      · subst hau; rcases r1 with _ | ⟨b, _⟩
        · simp [pathOfSegs, st, stateWithRootHandle]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsEmptyDir]
      · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, hau]
  have h0 := h st rootHandle [] (EntryName.lit "u")
    rfl (by intro id pos hm; simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide)
    hKeys (fun _ hm => by cases hm) (by decide) ⟨0o755, rfl, by decide, by decide⟩
    (by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsTreeTopNode, vfsEmptyDir])
  simp [stubMkSubtree, stubSubtree, StateT.run, pure, assert] at h0
  rcases h0.1 with ⟨⟨e, he, hk⟩, _⟩
  cases he
  cases hk

private def buggyWouldBlockToInvalidApi (base : FsApi) : FsApi :=
  { base with
    mapRawError := fun
      | .wouldBlock path? errno _ =>
        { kind := .invalidInput, path := path?, errnoCode := some errno, message := "invalid" }
      | other => base.mapRawError other }

example : ¬ Core.AllPass (test_fsraw_mapRawError_wouldBlock (buggyWouldBlockToInvalidApi stubFsApi)) := by
  intro h
  have h0 := h (some "/tmp/a.lock") 11 "Resource temporarily unavailable"
  simp [buggyWouldBlockToInvalidApi, assert] at h0

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

example : ¬ Core.AllPass (test_fsraw_createFileNew_createsMissingWithExactBytes
    { stubVfsRawOps with
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
        if follow then pure (.ok (stubStat .file))
        else pure (.ok (stubStat .symlink))
      readBytes := fun _ => pure (.error { kind := .invalidInput, message := "nofollow bug" }) }) := by
  intro h
  have h0 := h () "/sym" (by decide) ⟨stubStat .symlink, rfl, rfl⟩ ⟨stubStat .file, rfl, rfl⟩
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

example : ¬ Core.AllPass (test_fsraw_rawDirOps_freshTempName_distinctAndValid stubRawDirOps) := by
  intro h
  have h0 := h ()
  simp [stubRawDirOps, StateT.run, pure, assert] at h0
  exact h0.1.2.2 rfl

end LeanSwe.Fs
