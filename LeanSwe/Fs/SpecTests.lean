import Core.NondetTest
import LeanSwe.Fs.Types

namespace LeanSwe.Fs

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `api.mapRawError` carries a non-empty diagnostic message. -/
def test_fs_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let raw ← nondet FsRawError
  let err := api.mapRawError raw
  assert (err.message ≠ "")

/-- Lexical normalization `api.normPath` is idempotent on all path strings. -/
def test_fs_normPath_idempotent
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  assert (api.normPath (api.normPath path) = api.normPath path)

/-- Lexical normalization `api.normPath` never returns an empty string. -/
def test_fs_normPath_neverEmpty
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  assert (api.normPath path ≠ "")

/-- Joining an absolute `sub` path overrides `base` (`Path.joinpath(base, "/x") = "/x"`). -/
def test_fs_join_absOverridesBase
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let base ← nondet String
  let sub ← nondet String
  assume (api.isAbsolute sub = true)
  assert (api.join base sub = sub)

/-- When `api.withName path newName` succeeds, the resulting path's `name` equals `newName`. -/
def test_fs_withName_updatesName
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  let newName ← nondet String
  match api.withName path newName with
  | .error _ => assume False
  | .ok updated => assert (api.name updated = some newName)

/-- When `api.withSuffix path ext` succeeds on a single-dot extension, `api.suffix` equals `ext`. -/
def test_fs_withSuffix_updatesSuffix
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  let ext ← nondet String
  assume (ext.toList.head? = some '.')
  assume (!('.' ∈ ext.toList.tail))
  match api.withSuffix path ext with
  | .error _ => assume False
  | .ok updated => assert (api.suffix updated = ext)

/-- Multi-dot filenames like `base..ext` preserve `.` segments in `api.suffixes`. -/
def test_fs_suffixes_doubleDot
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let base ← nondet String
  assume (base.toList ≠ [])
  assume ('.' ∉ base.toList)
  assume ('/' ∉ base.toList)
  let xs := api.suffixes (base ++ "..ext")
  assert (xs = #[".", ".ext"])

/-- Calling `api.mkdir path parents false` on any existing path (including symlinks) fails with `.alreadyExists` and leaves state unchanged. -/
def test_fs_vfs_mkdir_existingFails
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let parents ← nondet Bool
  assume (((api.lstat path).run s₀).1.isOk = true)
  let (res, s₁) := (api.mkdir path parents false).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)

/-- Calling `api.touch path false` on any existing entry (including broken symlinks) fails with `.alreadyExists` and leaves state unchanged. -/
def test_fs_vfs_touch_existingFails
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (((api.lstat path).run s₀).1.isOk = true)
  let (res, s₁) := (api.touch path false).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)

/-- Failing `api.stat root` propagates its exact error kind (`notFound`, `permissionDenied`) through `api.walk root`. -/
def test_fs_vfs_walk_preservesStatError
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  match ((api.stat root).run s₀).1 with
  | .error err =>
    let (res, s₁) := (api.walk root).run s₀
    assert ((∃ e, res = .error e ∧ e.kind = err.kind) ∧ s₁ = s₀)
  | .ok st =>
    if st.kind != .dir then
      let (res, s₁) := (api.walk root).run s₀
      assert ((∃ e, res = .error e ∧ e.kind = .notADirectory) ∧ s₁ = s₀)
    else
      pure ()

/-- Calling `api.copyTree src dst false` when `dst` is `src` or a missing child inside `src` fails with `.invalidInput` without modifying state. -/
def test_fs_vfs_copyTree_selfCopyRejected
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let src ← nondet String
  let dst ← nondet String
  assume (∃ st, ((api.stat src).run s₀).1 = .ok st ∧ st.kind = .dir)
  assume (∃ c, ((api.resolve src).run s₀).1 = .ok c ∧ api.isAbsolute c ∧ c ≠ "/" ∧
    (((api.resolve c).run s₀).1 = .ok c) ∧
    (dst = c ∨ ∃ child, !child.isEmpty ∧ !('/' ∈ child.toList) ∧ child != "." ∧ child != ".." ∧
      dst = c ++ "/" ++ child ∧ ((api.resolve dst).run s₀).1.isOk = false))
  let (res, s₁) := (api.copyTree src dst false).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `api.mkdir path true false` when it succeeds creates a directory at `path`. -/
def test_fs_vfs_mkdir_parentsCreatesDir
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let (res, s₁) := (api.mkdir path true false).run s₀
  assume (res = .ok ())
  assert (((api.isDir path).run s₁).1 = .ok true)

/-- Copying an empty directory to a missing nested path `"/new_parent/copy"` under writable `"/"` creates missing parents and succeeds. -/
def test_fs_vfs_copyTree_createsMissingParents
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let src ← nondet String
  let dstPar := "/new_parent"
  let dst := "/new_parent/copy"
  assume (∃ stRoot, ((api.stat "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 ∧
    ((api.resolve "/").run s₀).1 = .ok "/")
  assume (∃ stSrc, ((api.stat src).run s₀).1 = .ok stSrc ∧ stSrc.kind = .dir)
  assume (∃ c, ((api.resolve src).run s₀).1 = .ok c ∧ api.isAbsolute c ∧ c ≠ "/" ∧
    c ≠ "/new_parent" ∧ c ≠ "/new_parent/copy")
  assume (((api.listDir src).run s₀).1 = .ok #[])
  assume (((api.lstat dstPar).run s₀).1.isOk = false)
  assume (((api.stat dstPar).run s₀).1.isOk = false)
  assume (((api.lstat dst).run s₀).1.isOk = false)
  let (res, s₁) := (api.copyTree src dst false).run s₀
  assert (res = .ok () ∧ ((api.isDir dstPar).run s₁).1 = .ok true ∧ ((api.isDir dst).run s₁).1 = .ok true)

/-- Copying a directory containing a symlink back to itself fails cleanly with `.invalidInput`. -/
def test_fs_vfs_copyTree_loopRejected
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let src ← nondet String
  let dst := "/loop_dst"
  assume (∃ stRoot, ((api.stat "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 ∧
    ((api.resolve "/").run s₀).1 = .ok "/")
  assume (∃ stSrc, ((api.stat src).run s₀).1 = .ok stSrc ∧ stSrc.kind = .dir)
  assume (∃ c, ((api.resolve src).run s₀).1 = .ok c ∧ api.isAbsolute c ∧ c ≠ "/" ∧
    c ≠ "/loop_dst" ∧ ((api.resolve (api.join src "self")).run s₀).1 = .ok c)
  assume (((api.listDir src).run s₀).1 = .ok #["self"])
  assume (∃ stSelf, ((api.stat (api.join src "self")).run s₀).1 = .ok stSelf ∧ stSelf.kind = .dir)
  assume (((api.lstat dst).run s₀).1.isOk = false)
  let (res, _) := (api.copyTree src dst false).run s₀
  assert (∃ e, res = .error e ∧ e.kind = .invalidInput)

/-- Calling `api.withFileLock` on a lockable path with a pure `.ok` action returns the value and releases the lock for both `.shared` and `.exclusive` modes. -/
def test_fs_vfs_withFileLock_releasesOnOk
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  let val ← nondet Nat
  assume (((api.tryWithFileLock path .exclusive createIfMissing (pure (.ok ()))).run s₀).1 = .ok (some ()))
  let (res, s₁) := (api.withFileLock path mode createIfMissing (pure (.ok val))).run s₀
  let (probe, _) := (api.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁
  assert (res = .ok val ∧ probe = .ok (some ()))

/-- Calling `api.withFileLock` on a lockable path with a pure `.error` action returns `.error err` and releases the lock for both `.shared` and `.exclusive` modes. -/
def test_fs_vfs_withFileLock_releasesOnError
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  let err ← nondet FsError
  assume (((api.tryWithFileLock path .exclusive createIfMissing (pure (.ok ()))).run s₀).1 = .ok (some ()))
  let (res, s₁) :=
    (api.withFileLock path mode createIfMissing (pure (Except.error err : Except FsError Unit))).run s₀
  let (probe, _) := (api.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁
  assert (res = .error err ∧ probe = .ok (some ()))

/-- Inside an outer `.shared` lock, an inner `.shared` `api.tryWithFileLock` on the same path succeeds. -/
def test_fs_vfs_tryWithFileLock_sharedCoexists
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let val ← nondet Nat
  let (res, _) := (api.withFileLock path .shared true
    (api.tryWithFileLock path .shared false (pure (Except.ok val)))).run s₀
  assume (res.isOk = true)
  assert (res = .ok (some val))

/-- Inside an outer lock, a conflicting inner `api.tryWithFileLock` returns `.ok none` without running `action`, while keeping the outer lock held. -/
def test_fs_vfs_tryWithFileLock_exclusiveRejects
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let markerPath ← nondet String
  let outerMode ← nondet LockMode
  let innerMode ← nondet LockMode
  assume (outerMode = .exclusive ∨ innerMode = .exclusive)
  assume (((api.lstat path).run s₀).1.isOk = true)
  assume (((api.lstat markerPath).run s₀).1.isOk = false)
  let (res, _) := (api.withFileLock path outerMode false do
    let r1 ← api.tryWithFileLock path innerMode false (api.writeText markerPath "ran")
    let mAfter ← api.lstat markerPath
    let r2 ← api.tryWithFileLock path .exclusive false (pure (.ok ()))
    return .ok (r1, mAfter.isOk, r2)).run s₀
  match res with
  | .error _ => assume False
  | .ok (r1, mOk, r2) => assert (r1 = .ok none ∧ mOk = false ∧ r2 = .ok none)

/-- Calling `api.withFileLock` with `createIfMissing = false` on a missing path fails with `.notFound` without modifying state. -/
def test_fs_vfs_withFileLock_missingNotCreated
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let mode ← nondet LockMode
  assume (path.toList ≠ [])
  assume (path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/')
  assume (∃ e, ((api.lstat path).run s₀).1 = .error e ∧ e.kind = .notFound)
  let (res, s₁) := (api.withFileLock path mode false (pure (.ok ()))).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ s₁ = s₀)

/-- Calling `api.withFileLock` on a symbolic link fails with `.invalidInput` without running `action` or modifying state. -/
def test_fs_vfs_withFileLock_symlinkRejected
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let markerPath ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  assume (path.toList ≠ [])
  assume (path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/')
  assume (∃ st, ((api.lstat path).run s₀).1 = .ok st ∧ st.kind = .symlink)
  assume (((api.lstat markerPath).run s₀).1.isOk = false)
  let (res, s₁) := (api.withFileLock path mode createIfMissing (api.writeText markerPath "ran")).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

/-- Calling `api.withFileLock` on a directory fails with `.isADirectory` without running `action` or modifying state. -/
def test_fs_vfs_withFileLock_dirRejected
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let markerPath ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  assume (path.toList ≠ [])
  assume (path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/')
  assume (∃ st, ((api.lstat path).run s₀).1 = .ok st ∧ st.kind = .dir)
  assume (((api.lstat markerPath).run s₀).1.isOk = false)
  let (res, s₁) := (api.withFileLock path mode createIfMissing (api.writeText markerPath "ran")).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

/-- Calling `api.withFileLock` with `createIfMissing = true` on a missing path creates a zero-byte regular file when it succeeds. -/
def test_fs_vfs_withFileLock_createsMissingFile
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let mode ← nondet LockMode
  assume (path.toList ≠ [])
  assume (path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/')
  assume (∃ e, ((api.lstat path).run s₀).1 = .error e ∧ e.kind = .notFound)
  let (res, s₁) := (api.withFileLock path mode true (pure (.ok ()))).run s₀
  assume (res = .ok ())
  assert (∃ st, ((api.lstat path).run s₁).1 = .ok st ∧ st.kind = .file ∧ st.byteSize = 0)

/-- Calling `api.withFileLock` on an existing regular file preserves its exact bytes inside `action` and after release. -/
def test_fs_vfs_withFileLock_preservesExistingBytes
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  assume (path.toList ≠ [])
  assume (path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/')
  match ((api.readBytes path).run s₀).1 with
  | .error _ => assume False
  | .ok bs₀ =>
    let (res, s₁) := (api.withFileLock path mode createIfMissing (api.readBytes path)).run s₀
    assume (res.isOk = true)
    assert (res = .ok bs₀ ∧ ((api.readBytes path).run s₁).1 = .ok bs₀)

/-- Calling `api.withFileLock` on an empty path or non-root trailing `/` fails with `.invalidInput` without running `action` or modifying state. -/
def test_fs_vfs_withFileLock_invalidPathRejected
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let markerPath ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  assume (path.toList = [] ∨ (path.toList.length > 1 ∧ path.toList.getLast? = some '/'))
  assume (((api.lstat markerPath).run s₀).1.isOk = false)
  let (res, s₁) := (api.withFileLock path mode createIfMissing (api.writeText markerPath "ran")).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

/-- Calling `api.tryWithFileLock` on a lockable path with a pure `.ok` action returns `.ok (some val)` and releases the lock. -/
def test_fs_vfs_tryWithFileLock_releasesOnOk
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  let val ← nondet Nat
  assume (((api.tryWithFileLock path .exclusive createIfMissing (pure (.ok ()))).run s₀).1 = .ok (some ()))
  let (res, s₁) := (api.tryWithFileLock path mode createIfMissing (pure (Except.ok val))).run s₀
  let (probe, _) := (api.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁
  assert (res = .ok (some val) ∧ probe = .ok (some ()))

/-- Calling `api.tryWithFileLock` with `createIfMissing = false` on a missing path fails with `.notFound` without running `action` or modifying state. -/
def test_fs_vfs_tryWithFileLock_missingNotSwallowed
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let markerPath ← nondet String
  let mode ← nondet LockMode
  assume (path.toList ≠ [])
  assume (path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/')
  assume (∃ e, ((api.lstat path).run s₀).1 = .error e ∧ e.kind = .notFound)
  assume (((api.lstat markerPath).run s₀).1.isOk = false)
  let (res, s₁) := (api.tryWithFileLock path mode false (api.writeText markerPath "ran")).run s₀
  assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

/-- Calling `api.tryWithFileLock` on a lockable path when `action` returns `.error err` propagates `.error err` and releases the lock. -/
def test_fs_vfs_tryWithFileLock_releasesOnActionError
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let mode ← nondet LockMode
  let createIfMissing ← nondet Bool
  let err ← nondet FsError
  assume (((api.tryWithFileLock path .exclusive createIfMissing (pure (.ok ()))).run s₀).1 = .ok (some ()))
  let (res, s₁) :=
    (api.tryWithFileLock path mode createIfMissing (pure (Except.error err : Except FsError Unit))).run s₀
  let (probe, _) := (api.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁
  assert (res = .error err ∧ probe = .ok (some ()))

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

end LeanSwe.Fs
