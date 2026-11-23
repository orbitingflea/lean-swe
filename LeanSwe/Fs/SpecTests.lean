import Core.NondetTest
import Core.Assumptions
import LeanSwe.Fs.Types
import LeanSwe.Fs.Model

namespace LeanSwe.Fs

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Fs.Model hiding isValidRawPath

/-- Builder function assembling an `FsApiM m` from injected `RawFsOpsM m` primitives. -/
abbrev FsBuilder (m : Type → Type) :=
  RawFsOpsM m → FsApiM m

private def isSingleValidName (fileName : String) : Bool :=
  let cs := fileName.toList
  !cs.isEmpty && !('/' ∈ cs) && !(Char.ofNat 0 ∈ cs) && fileName != "." && fileName != ".."

private def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

private def hasDotFinalSegment (path : String) : Bool :=
  match path.toList.reverse with
  | ['.'] | '.' :: '/' :: _ => true
  | ['.', '.'] | '.' :: '.' :: '/' :: _ => true
  | _ => false

private def isValidAtomicTargetPath (path : String) : Bool :=
  isValidRawPath path && !hasDotFinalSegment path

/-- Every error returned by `api.mapRawError` carries a non-empty diagnostic message. -/
def test_fs_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let raw ← nondet FsRawError
  let err := api.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- Lexical normalization `api.normPath` is idempotent on all path strings. -/
def test_fs_normPath_idempotent
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  NondetTest.assert (api.normPath (api.normPath path) = api.normPath path)

/-- Lexical normalization `api.normPath` never returns an empty string. -/
def test_fs_normPath_neverEmpty
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  NondetTest.assert (api.normPath path ≠ "")

/-- Joining an absolute `sub` path overrides `base` (`Path.joinpath(base, "/x") = "/x"`). -/
def test_fs_join_absOverridesBase
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let base ← nondet String
  let sub ← nondet String
  assume (api.isAbsolute sub = true)
  NondetTest.assert (api.join base sub = sub)

/-- When `api.withName path newName` succeeds, the resulting path's `name` equals `newName`. -/
def test_fs_withName_updatesName
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  let newName ← nondet String
  match api.withName path newName with
  | .error _ => assume False
  | .ok updated => NondetTest.assert (api.name updated = some newName)

/-- When `api.withSuffix path ext` succeeds on a single-dot extension, `api.suffix` equals `ext`. -/
def test_fs_withSuffix_updatesSuffix
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  let ext ← nondet String
  assume (ext.toList.head? = some '.')
  assume (!('.' ∈ ext.toList.tail))
  match api.withSuffix path ext with
  | .error _ => assume False
  | .ok updated => NondetTest.assert (api.suffix updated = ext)

/-- Multi-dot filenames like `base..ext` preserve `.` segments in `api.suffixes`. -/
def test_fs_suffixes_doubleDot
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let base ← nondet String
  assume (base.toList ≠ [])
  assume ('.' ∉ base.toList)
  assume ('/' ∉ base.toList)
  let xs := api.suffixes (base ++ "..ext")
  NondetTest.assert (xs = #[".", ".ext"])

/-- Calling `api.mkdir path parents false` on any existing path (including symlinks) fails with `.alreadyExists` and leaves state unchanged. -/
def test_fs_vfs_mkdir_existingFails
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let parents ← nondet Bool
  assume (((api.lstat path).run s₀).1.isOk = true)
  let (res, s₁) := (api.mkdir path parents false).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)

/-- Calling `api.touch path false` on any existing entry (including broken symlinks) fails with `.alreadyExists` and leaves state unchanged. -/
def test_fs_vfs_touch_existingFails
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (((api.lstat path).run s₀).1.isOk = true)
  let (res, s₁) := (api.touch path false).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)

/-- Failing `api.stat root` propagates its exact error kind (`notFound`, `permissionDenied`) through `api.walk root`. -/
def test_fs_vfs_walk_preservesStatError
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  match ((api.stat root).run s₀).1 with
  | .error err =>
    let (res, s₁) := (api.walk root).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = err.kind) ∧ s₁ = s₀)
  | .ok st =>
    if st.kind != .dir then
      let (res, s₁) := (api.walk root).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notADirectory) ∧ s₁ = s₀)
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
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `api.mkdir path true false` when it succeeds creates a directory at `path`. -/
def test_fs_vfs_mkdir_parentsCreatesDir
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let (res, s₁) := (api.mkdir path true false).run s₀
  assume (res = .ok ())
  NondetTest.assert (((api.isDir path).run s₁).1 = .ok true)

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
  NondetTest.assert (res = .ok () ∧ ((api.isDir dstPar).run s₁).1 = .ok true ∧ ((api.isDir dst).run s₁).1 = .ok true)

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
  NondetTest.assert (∃ e, res = .error e ∧ e.kind = .invalidInput)

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
  NondetTest.assert (res = .ok val ∧ probe = .ok (some ()))

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
  NondetTest.assert (res = .error err ∧ probe = .ok (some ()))

/-- Inside an outer `.shared` lock, an inner `.shared` `api.tryWithFileLock` on the same path succeeds. -/
def test_fs_vfs_tryWithFileLock_sharedCoexists
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let val ← nondet Nat
  let (res, _) := (api.withFileLock path .shared true
    (api.tryWithFileLock path .shared false (pure (Except.ok val)))).run s₀
  assume (res.isOk = true)
  NondetTest.assert (res = .ok (some val))

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
  | .ok (r1, mOk, r2) => NondetTest.assert (r1 = .ok none ∧ mOk = false ∧ r2 = .ok none)

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
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ s₁ = s₀)

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
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

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
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

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
  NondetTest.assert (∃ st, ((api.lstat path).run s₁).1 = .ok st ∧ st.kind = .file ∧ st.byteSize = 0)

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
    NondetTest.assert (res = .ok bs₀ ∧ ((api.readBytes path).run s₁).1 = .ok bs₀)

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
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

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
  NondetTest.assert (res = .ok (some val) ∧ probe = .ok (some ()))

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
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ ((api.lstat markerPath).run s₁).1.isOk = false ∧ s₁ = s₀)

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
  NondetTest.assert (res = .error err ∧ probe = .ok (some ()))

/-- Calling `api.atomicWriteBytes` for a valid child under writable `"/"` writes exact bytes atomically without leaving a `.tmp.<nonce>` sibling. -/
def test_fs_vfs_atomicWriteBytes_writesAtomically
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce, _) := ops.monotonicNonce.run s₀
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString nonce
  assume (((ops.stat false tmpPath).run s₀).1.isOk = false)
  assume ((∃ e, ((ops.stat false path).run s₀).1 = .error e ∧ e.kind = .notFound) ∨
    (∃ st, ((ops.stat false path).run s₀).1 = .ok st ∧ st.kind ≠ .dir))
  let api := mkApi ops
  let (res, s₁) := (api.atomicWriteBytes path bytes).run s₀
  NondetTest.assert (res = .ok ())
  NondetTest.assert (((api.readBytes path).run s₁).1 = .ok bytes)
  NondetTest.assert (∃ st, ((api.lstat path).run s₁).1 = .ok st ∧ st.kind = .file ∧ st.byteSize = bytes.size)
  NondetTest.assert (((ops.stat false tmpPath).run s₁).1.isOk = false)

/-- When `.tmp.<nonce>` already exists (for instance as a pre-planted symlink), `api.atomicWriteBytes` fails with `.alreadyExists` and preserves target, symlink victim, and existing temp entry. -/
def test_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let victimPath ← nondet String
  let newBytes ← nondet ByteArray
  let origBytes ← nondet ByteArray
  let victimBytes ← nondet ByteArray
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce, _) := ops.monotonicNonce.run s₀
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString nonce
  assume (((ops.stat false tmpPath).run s₀).1.isOk = true)
  assume (((ops.readBytes path).run s₀).1 = .ok origBytes)
  assume (((ops.readBytes victimPath).run s₀).1 = .ok victimBytes)
  let (res, s₁) := ((mkApi ops).atomicWriteBytes path newBytes).run s₀
  NondetTest.assert (∃ e, res = .error e ∧ e.kind = .alreadyExists)
  NondetTest.assert (((ops.readBytes path).run s₁).1 = .ok origBytes)
  NondetTest.assert (((ops.readBytes victimPath).run s₁).1 = .ok victimBytes)
  NondetTest.assert (((ops.stat false tmpPath).run s₁).1.isOk = true)

/-- When `ops.rename` fails after `createFileNew` succeeds, `api.atomicWriteBytes` propagates the error, cleans up `.tmp.<nonce>`, and preserves original target bytes. -/
def test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let newBytes ← nondet ByteArray
  let origBytes ← nondet ByteArray
  let renameErr ← nondet FsError
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce, _) := ops.monotonicNonce.run s₀
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString nonce
  assume (((ops.stat false tmpPath).run s₀).1.isOk = false)
  assume (((ops.readBytes path).run s₀).1 = .ok origBytes)
  let opsFailRename : RawFsOpsM (StateM S) :=
    { ops with rename := fun _ _ => pure (.error renameErr) }
  let (res, s₁) := ((mkApi opsFailRename).atomicWriteBytes path newBytes).run s₀
  NondetTest.assert (res = .error renameErr)
  NondetTest.assert (((ops.stat false tmpPath).run s₁).1.isOk = false)
  NondetTest.assert (((ops.readBytes path).run s₁).1 = .ok origBytes)

/-- Calling `api.atomicWriteText` for a valid child under writable `"/"` writes exact UTF-8 bytes atomically without leaving `.tmp.<nonce>`. -/
def test_fs_vfs_atomicWriteText_writesAtomically
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let content ← nondet String
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce, _) := ops.monotonicNonce.run s₀
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString nonce
  assume (((ops.stat false tmpPath).run s₀).1.isOk = false)
  assume ((∃ e, ((ops.stat false path).run s₀).1 = .error e ∧ e.kind = .notFound) ∨
    (∃ st, ((ops.stat false path).run s₀).1 = .ok st ∧ st.kind ≠ .dir))
  let api := mkApi ops
  let (res, s₁) := (api.atomicWriteText path content).run s₀
  NondetTest.assert (res = .ok ())
  NondetTest.assert (((api.readBytes path).run s₁).1 = .ok content.toUTF8)
  NondetTest.assert (((api.readText path).run s₁).1 = .ok content)
  NondetTest.assert (((ops.stat false tmpPath).run s₁).1.isOk = false)

/-- When `.tmp.<nonce>` already exists (for instance as a pre-planted symlink), `api.atomicWriteText` fails with `.alreadyExists` and preserves target, symlink victim, and existing temp entry. -/
def test_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let victimPath ← nondet String
  let newText ← nondet String
  let origBytes ← nondet ByteArray
  let victimBytes ← nondet ByteArray
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce, _) := ops.monotonicNonce.run s₀
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString nonce
  assume (((ops.stat false tmpPath).run s₀).1.isOk = true)
  assume (((ops.readBytes path).run s₀).1 = .ok origBytes)
  assume (((ops.readBytes victimPath).run s₀).1 = .ok victimBytes)
  let (res, s₁) := ((mkApi ops).atomicWriteText path newText).run s₀
  NondetTest.assert (∃ e, res = .error e ∧ e.kind = .alreadyExists)
  NondetTest.assert (((ops.readBytes path).run s₁).1 = .ok origBytes)
  NondetTest.assert (((ops.readBytes victimPath).run s₁).1 = .ok victimBytes)
  NondetTest.assert (((ops.stat false tmpPath).run s₁).1.isOk = true)

/-- Calling `api.atomicWriteBytes` on an invalid target path (`""`, NUL, non-root trailing `/`, or raw final segment `.` / `..`) fails with `.invalidInput` upfront without calling `monotonicNonce`, creating a temp file, or mutating state. -/
def test_fs_vfs_atomicWriteBytes_invalidPathRejected
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let bytes ← nondet ByteArray
  assume (isValidAtomicTargetPath path = false)
  let (res, s₁) := ((mkApi ops).atomicWriteBytes path bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `api.atomicWriteText` on an invalid target path (`""`, NUL, non-root trailing `/`, or raw final segment `.` / `..`) fails with `.invalidInput` upfront without mutating state. -/
def test_fs_vfs_atomicWriteText_invalidPathRejected
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let content ← nondet String
  assume (isValidAtomicTargetPath path = false)
  let (res, s₁) := ((mkApi ops).atomicWriteText path content).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `api.atomicWriteBytes` on `"/"` or an existing non-symlink directory fails upfront with `.isADirectory` without creating a temp file or mutating state. -/
def test_fs_vfs_atomicWriteBytes_dirRejected
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let bytes ← nondet ByteArray
  assume (isValidAtomicTargetPath path = true)
  assume (path = "/" ∨ ∃ st, ((ops.stat false path).run s₀).1 = .ok st ∧ st.kind = .dir)
  let (res, s₁) := ((mkApi ops).atomicWriteBytes path bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)

/-- Calling `api.atomicWriteText` on `"/"` or an existing non-symlink directory fails upfront with `.isADirectory` without creating a temp file or mutating state. -/
def test_fs_vfs_atomicWriteText_dirRejected
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let content ← nondet String
  assume (isValidAtomicTargetPath path = true)
  assume (path = "/" ∨ ∃ st, ((ops.stat false path).run s₀).1 = .ok st ∧ st.kind = .dir)
  let (res, s₁) := ((mkApi ops).atomicWriteText path content).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)

/-- When upfront `ops.stat false path` returns a non-`.notFound` error on a valid non-root path, `api.atomicWriteBytes` returns that error immediately without mutating state. -/
def test_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let bytes ← nondet ByteArray
  assume (isValidAtomicTargetPath path = true ∧ path ≠ "/")
  assume (∃ stErr, ((ops.stat false path).run s₀).1 = .error stErr ∧ stErr.kind ≠ .notFound)
  let (res, s₁) := ((mkApi ops).atomicWriteBytes path bytes).run s₀
  NondetTest.assert ((∃ stErr e, ((ops.stat false path).run s₀).1 = .error stErr ∧
    res = .error e ∧ e.kind = stErr.kind) ∧ s₁ = s₀)

/-- Calling `api.atomicWriteBytes` on a symlink replaces the symlink itself with a regular file containing `bytes` without leaving `.tmp.<nonce>`. -/
def test_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce, _) := ops.monotonicNonce.run s₀
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString nonce
  assume (((ops.stat false tmpPath).run s₀).1.isOk = false)
  assume (∃ lst, ((ops.stat false path).run s₀).1 = .ok lst ∧ lst.kind = .symlink)
  let api := mkApi ops
  let (res, s₁) := (api.atomicWriteBytes path bytes).run s₀
  NondetTest.assert (res = .ok ())
  NondetTest.assert (∃ st, ((api.lstat path).run s₁).1 = .ok st ∧ st.kind = .file ∧ st.byteSize = bytes.size)
  NondetTest.assert (((api.readBytes path).run s₁).1 = .ok bytes)
  NondetTest.assert (((ops.stat false tmpPath).run s₁).1.isOk = false)

/-- Calling `api.atomicWriteBytes` on a nested path `"/dir/child"` or bare relative `"child"` (with `cwd = "/"`) exercises `parent`/`join` and leaves no `.tmp.<nonce>`. -/
def test_fs_vfs_atomicWriteBytes_nestedParentAndRelative
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dirName ← nondet String
  let child ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName dirName = true ∧ isSingleValidName child = true)
  let nestedPath := "/" ++ dirName ++ "/" ++ child
  let (nonce0, _) := ops.monotonicNonce.run s₀
  let nestedTmp := "/" ++ dirName ++ "/." ++ child ++ ".tmp." ++ toString nonce0
  assume (∃ stDir, ((ops.stat false ("/" ++ dirName)).run s₀).1 = .ok stDir ∧ stDir.kind = .dir ∧
    (stDir.mode / 128) % 2 = 1 ∧ (stDir.mode / 64) % 2 = 1)
  assume (((ops.stat false nestedTmp).run s₀).1.isOk = false)
  assume (∃ e, ((ops.stat false nestedPath).run s₀).1 = .error e ∧ e.kind = .notFound)
  let api := mkApi ops
  let (resNested, s₁) := (api.atomicWriteBytes nestedPath bytes).run s₀
  NondetTest.assert (resNested = .ok () ∧ ((api.readBytes nestedPath).run s₁).1 = .ok bytes ∧
    ((ops.stat false nestedTmp).run s₁).1.isOk = false)
  assume ((ops.cwd.run s₁).1 = .ok "/")
  assume (∃ stRoot, ((ops.stat false "/").run s₁).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce1, _) := ops.monotonicNonce.run s₁
  let relTmp := "./." ++ child ++ ".tmp." ++ toString nonce1
  assume (((ops.stat false relTmp).run s₁).1.isOk = false)
  assume (∃ e, ((ops.stat false child).run s₁).1 = .error e ∧ e.kind = .notFound)
  let (resRel, s₂) := (api.atomicWriteBytes child bytes).run s₁
  NondetTest.assert (resRel = .ok () ∧ ((api.readBytes child).run s₂).1 = .ok bytes ∧
    ((ops.stat false relTmp).run s₂).1.isOk = false)

/-- Calling `api.readBytes` on a symlink pointing to a regular file follows the symlink and returns the target bytes without modifying state. -/
def test_fs_vfs_readBytes_followsSymlinkToRegularFile
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = true)
  assume (∃ lst, ((api.lstat path).run s₀).1 = .ok lst ∧ lst.kind = .symlink)
  assume (∃ st, ((api.stat path).run s₀).1 = .ok st ∧ st.kind = .file)
  let (res, s₁) := (api.readBytes path).run s₀
  NondetTest.assert ((∃ bs, res = .ok bs ∧
    (∃ st, ((api.stat path).run s₀).1 = .ok st ∧ bs.size = st.byteSize)) ∧ s₁ = s₀)

/-- Writing `bytes` with `api.atomicWriteBytes`, creating a symlink to it, and calling `api.readBytes` on the symlink returns exact `bytes` without mutating state. -/
def test_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink
    {S : Type} {runner} [NondetTest runner]
    (mkApi : FsBuilder (StateM S)) (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let tgtName ← nondet String
  let symName ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName tgtName = true ∧ isSingleValidName symName = true ∧ tgtName ≠ symName)
  let tgt := "/" ++ tgtName
  let sym := "/" ++ symName
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  let (nonce, _) := ops.monotonicNonce.run s₀
  let tmpPath := "/." ++ tgtName ++ ".tmp." ++ toString nonce
  assume (((ops.stat false tmpPath).run s₀).1.isOk = false)
  assume (∃ e1, ((ops.stat false tgt).run s₀).1 = .error e1 ∧ e1.kind = .notFound)
  assume (∃ e2, ((ops.stat false sym).run s₀).1 = .error e2 ∧ e2.kind = .notFound)
  let api := mkApi ops
  let (r1, s₁) := (api.atomicWriteBytes tgt bytes).run s₀
  assume (r1 = .ok ())
  let (r2, s₂) := (api.symlink tgt sym).run s₁
  assume (r2 = .ok ())
  let (r3, s₃) := (api.readBytes sym).run s₂
  NondetTest.assert (r3 = .ok bytes ∧ s₃ = s₂)

/-- Calling `api.readBytes` on a directory fails with `.isADirectory` and on a missing valid path preserves the `stat` error without modifying state. -/
def test_fs_vfs_readBytes_dirAndMissingRejected
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = true)
  match ((api.stat path).run s₀).1 with
  | .error err =>
    let (res, s₁) := (api.readBytes path).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = err.kind) ∧ s₁ = s₀)
  | .ok st =>
    if st.kind == .dir then
      let (res, s₁) := (api.readBytes path).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)
    else
      pure ()

/-- Calling `api.readBytes` with an empty path, embedded NUL byte, or non-root trailing `/` fails with `.invalidInput` and leaves state unchanged. -/
def test_fs_vfs_readBytes_invalidPathRejected
    {S : Type} {runner} [NondetTest runner] (api : FsApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = false)
  let (res, s₁) := (api.readBytes path).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- `withSubtree` validates `root` (including owner read+search on directories), refuses non-directory/unreadable roots without running `action`, and always closes its handle (preserving `openDirs`) on both `.ok` and `.error`. -/
def test_fs_withSubtree_validatesRootAndAlwaysClosesHandle
    {runner} [NondetTest runner] (mkOpener : SubtreeOpenerBuilder (StateM VfsState)) : runner Unit := do
  let st₀ ← nondet VfsState
  let root ← nondet String
  let bodyRes ← nondet (Except FsError Unit)
  assume (DirHandleInvariant st₀)
  let opener := mkOpener vfsDirOps
  if !Model.isValidRawPath root then
    let (res, st₁) := (opener.withSubtree root (fun _ => pure bodyRes)).run st₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ st₁.nodes = st₀.nodes ∧ st₁.openDirs = st₀.openDirs)
  else
    let abs := vfsAbsNorm st₀.cwd root
    match vfsResolveSegs st₀.nodes "/" (vfsSplitSegs abs) true 1024 with
    | .error expectedErr =>
      let (res, st₁) := (opener.withSubtree root (fun _ => pure (.ok ()))).run st₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = expectedErr.kind) ∧ st₁.nodes = st₀.nodes ∧ st₁.openDirs = st₀.openDirs)
    | .ok (_, .dir m) =>
      if (m / 256) % 2 == 1 && (m / 64) % 2 == 1 then
        let (res, st₁) := (opener.withSubtree root (fun sub => do
          let stRoot ← sub.lstat RelPath.root
          match stRoot with
          | .error e => pure (.error e)
          | .ok info =>
            if info.kind == .dir then pure bodyRes
            else pure (.error { kind := .ioError, message := "expected dir" }))).run st₀
        NondetTest.assert (res = bodyRes ∧ st₁.openDirs = st₀.openDirs)
      else
        let (res, st₁) := (opener.withSubtree root (fun _ => pure (.ok ()))).run st₀
        NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .permissionDenied) ∧ st₁.nodes = st₀.nodes ∧ st₁.openDirs = st₀.openDirs)
    | .ok (_, _) =>
      let (res, st₁) := (opener.withSubtree root (fun _ => pure (.ok ()))).run st₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notADirectory) ∧ st₁.nodes = st₀.nodes ∧ st₁.openDirs = st₀.openDirs)

/-- Leaf symlinks follow the leaf-symlink specification rules across all 12 `SubtreeM` operations without mutating or destroying the symlink target. -/
def test_fs_subtree_leafSymlink_followsExactLeafTable
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let pre ← nondet (List EntryName)
  let leaf ← nondet EntryName
  let target ← nondet String
  let lm ← nondet Nat
  let bytes ← nondet ByteArray
  let lockMode ← nondet LockMode
  let b ← nondet Bool
  let existOk ← nondet Bool
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (∀ k ≤ pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
    (dm / 256) % 2 = 1 ∧ (dm / 64) % 2 = 1)
  let parentPos := pos ++ pre.map (·.val)
  assume (∃ pm, nodeAt st.tree parentPos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  let leafPos := parentPos ++ [leaf.val]
  assume (nodeAt st.tree leafPos = some (.symlink target lm))
  assume (nodeAt st.tree (parentPos ++ [".t." ++ toString st.nonce]) = none)
  let rel : RelPath := { segments := pre ++ [leaf] }
  let sub := mkSubtree vfsDirOps dh
  let (rRead, stRead) := (sub.readRegular rel).run st
  let (rList, stList) := (sub.listDir rel).run st
  let (rWalk, stWalk) := (sub.walk rel).run st
  let (rWLock, stWLock) := (sub.withFileLock rel lockMode b (pure (.ok ()))).run st
  let (rTLock, stTLock) := (sub.tryWithFileLock rel lockMode b (pure (.ok ()))).run st
  NondetTest.assert ((∃ e, rRead = .error e ∧ e.kind = .invalidInput) ∧ stRead.nodes = st.nodes)
  NondetTest.assert ((∃ e, rList = .error e ∧ e.kind = .invalidInput) ∧ stList.nodes = st.nodes)
  NondetTest.assert ((∃ e, rWalk = .error e ∧ e.kind = .invalidInput) ∧ stWalk.nodes = st.nodes)
  NondetTest.assert ((∃ e, rWLock = .error e ∧ e.kind = .invalidInput) ∧ stWLock.nodes = st.nodes ∧ stWLock.locks = st.locks)
  NondetTest.assert ((∃ e, rTLock = .error e ∧ e.kind = .invalidInput) ∧ stTLock.nodes = st.nodes ∧ stTLock.locks = st.locks)
  let (rMkdir, stMkdir) := (sub.mkdir rel b existOk).run st
  let (rSymlink, stSymlink) := (sub.symlink "other" rel).run st
  NondetTest.assert ((∃ e, rMkdir = .error e ∧ e.kind = .alreadyExists) ∧ stMkdir.nodes = st.nodes)
  NondetTest.assert ((∃ e, rSymlink = .error e ∧ e.kind = .alreadyExists) ∧ stSymlink.nodes = st.nodes)
  let (rRmdir, stRmdir) := (sub.rmdir rel).run st
  let (rRmtree, stRmtree) := (sub.rmtree rel b).run st
  NondetTest.assert ((∃ e, rRmdir = .error e ∧ e.kind = .notADirectory) ∧ stRmdir.nodes = st.nodes)
  NondetTest.assert ((∃ e, rRmtree = .error e ∧ e.kind = .notADirectory) ∧ stRmtree.nodes = st.nodes)
  let (rLstat, stLstat) := (sub.lstat rel).run st
  NondetTest.assert ((∃ info, rLstat = .ok info ∧ info.kind = .symlink) ∧ stLstat.nodes = st.nodes)
  let (rUnlink, stUnlink) := (sub.unlink rel b).run st
  NondetTest.assert (rUnlink = .ok () ∧ nodeAt stUnlink.tree leafPos = none ∧ SameOutside leafPos st stUnlink)
  let (rWrite, stWrite) := (sub.atomicWriteBytes rel bytes).run st
  NondetTest.assert (rWrite = .ok () ∧ nodeAt stWrite.tree leafPos = some (.file bytes 0o644) ∧ SameOutside leafPos st stWrite)

/-- `RelPath.root` rules: `lstat` matches `fstatDir`, `mkdir .root` calls `fstatDir` and honors `existOk` while preserving mode, and mutating/file ops fail upfront with `.invalidInput`. -/
def test_fs_subtree_rootPath_enforcesRootRules
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let pm ← nondet Nat
  let bytes ← nondet ByteArray
  let lockMode ← nondet LockMode
  let b1 ← nondet Bool
  let target ← nondet String
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (nodeAt st.tree pos = some (.dir pm))
  let sub := mkSubtree vfsDirOps dh
  NondetTest.assert ((sub.lstat RelPath.root |>.run st).1 = (vfsDirOps.fstatDir dh |>.run st).1)
  let (rMkFalse, stMkFalse) := (sub.mkdir RelPath.root b1 false).run st
  NondetTest.assert ((∃ e, rMkFalse = .error e ∧ e.kind = .alreadyExists) ∧ stMkFalse.nodes = st.nodes)
  let (rMkTrue, stMkTrue) := (sub.mkdir RelPath.root b1 true).run st
  NondetTest.assert (rMkTrue = .ok () ∧ nodeAt stMkTrue.tree pos = some (.dir pm) ∧ stMkTrue.nodes = st.nodes)
  let (rRead, stRead) := (sub.readRegular RelPath.root).run st
  NondetTest.assert ((∃ e, rRead = .error e ∧ e.kind = .isADirectory) ∧ stRead.nodes = st.nodes)
  let (rWrite, stWrite) := (sub.atomicWriteBytes RelPath.root bytes).run st
  let (rUnlink, stUnlink) := (sub.unlink RelPath.root b1).run st
  let (rRmdir, stRmdir) := (sub.rmdir RelPath.root).run st
  let (rRmtree, stRmtree) := (sub.rmtree RelPath.root b1).run st
  let (rSymlink, stSymlink) := (sub.symlink target RelPath.root).run st
  let (rWLock, stWLock) := (sub.withFileLock RelPath.root lockMode b1 (pure (.ok ()))).run st
  let (rTLock, stTLock) := (sub.tryWithFileLock RelPath.root lockMode b1 (pure (.ok ()))).run st
  NondetTest.assert ((∃ e, rWrite = .error e ∧ e.kind = .invalidInput) ∧ stWrite.nodes = st.nodes)
  NondetTest.assert ((∃ e, rUnlink = .error e ∧ e.kind = .invalidInput) ∧ stUnlink.nodes = st.nodes)
  NondetTest.assert ((∃ e, rRmdir = .error e ∧ e.kind = .invalidInput) ∧ stRmdir.nodes = st.nodes)
  NondetTest.assert ((∃ e, rRmtree = .error e ∧ e.kind = .invalidInput) ∧ stRmtree.nodes = st.nodes)
  NondetTest.assert ((∃ e, rSymlink = .error e ∧ e.kind = .invalidInput) ∧ stSymlink.nodes = st.nodes)
  NondetTest.assert ((∃ e, rWLock = .error e ∧ e.kind = .invalidInput) ∧ stWLock.nodes = st.nodes ∧ stWLock.locks = st.locks)
  NondetTest.assert ((∃ e, rTLock = .error e ∧ e.kind = .invalidInput) ∧ stTLock.nodes = st.nodes ∧ stTLock.locks = st.locks)
  let closedDh : DirHandle := { handleId := 0, rootPath := dh.rootPath }
  let closedSub := mkSubtree vfsDirOps closedDh
  NondetTest.assert (∃ e, (closedSub.lstat RelPath.root |>.run st).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (closedSub.mkdir RelPath.root b1 true |>.run st).1 = .error e ∧ e.kind = .invalidInput)

/-- `atomicWriteBytes` handles max-length 255-byte `EntryName` targets using `freshTempName` (`.t.<nonce>`), retries `.alreadyExists` up to 16 times (failing with `.alreadyExists` on exhaustion), and cleans up temps on `renameAt` errors including `.isADirectory`. -/
def test_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let bytes ← nondet ByteArray
  let maxLeaf ← nondet EntryName
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (maxLeaf.val.utf8ByteSize = 255)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [".t." ++ toString st.nonce]) = some (.file ByteArray.empty 0o600))
  assume (nodeAt st.tree (pos ++ [".t." ++ toString (st.nonce + 1)]) = none)
  assume (maxLeaf.val ≠ ".t." ++ toString st.nonce ∧ maxLeaf.val ≠ ".t." ++ toString (st.nonce + 1))
  assume (match nodeAt st.tree (pos ++ [maxLeaf.val]) with | some (.dir _) => False | _ => True)
  let rel : RelPath := { segments := [maxLeaf] }
  let (res, st₁) := ((mkSubtree vfsDirOps dh).atomicWriteBytes rel bytes).run st
  NondetTest.assert (res = .ok ())
  NondetTest.assert (nodeAt st₁.tree (pos ++ [maxLeaf.val]) = some (.file bytes 0o644))
  NondetTest.assert (nodeAt st₁.tree (pos ++ [".t." ++ toString st.nonce]) = some (.file ByteArray.empty 0o600))
  let dirLeaf ← nondet EntryName
  assume (dirLeaf ≠ maxLeaf)
  assume (nodeAt st.tree (pos ++ [dirLeaf.val]) = some (.dir 0o755))
  let (resDirFail, stDirFail) := ((mkSubtree vfsDirOps dh).atomicWriteBytes { segments := [dirLeaf] } bytes).run st
  NondetTest.assert (∃ e, resDirFail = .error e ∧ e.kind = .isADirectory)
  NondetTest.assert (nodeAt stDirFail.tree (pos ++ [".t." ++ toString (st.nonce + 1)]) = none)
  NondetTest.assert (nodeAt stDirFail.tree (pos ++ [dirLeaf.val]) = some (.dir 0o755))
  let failOps : RawDirOpsM (StateM VfsState) :=
    { vfsDirOps with
      renameAt := fun _ _ _ _ s => (.error { kind := .ioError, message := "injected rename failure" }, s) }
  let (resFail, stFail) := ((mkSubtree failOps dh).atomicWriteBytes { segments := [maxLeaf] } bytes).run st
  NondetTest.assert (∃ e, resFail = .error e)
  NondetTest.assert (nodeAt stFail.tree (pos ++ [".t." ++ toString st.nonce]) = some (.file ByteArray.empty 0o600))
  NondetTest.assert (nodeAt stFail.tree (pos ++ [".t." ++ toString (st.nonce + 1)]) = none)
  NondetTest.assert (stFail.openDirs = st.openDirs)
  let stExh ← nondet VfsState
  let dhExh ← nondet DirHandle
  let posExh ← nondet (List String)
  assume (lookupDir stExh dhExh = some posExh)
  assume (DirHandleInvariant stExh)
  assume (∃ pm, nodeAt stExh.tree posExh = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (∀ k < 16, nodeAt stExh.tree (posExh ++ [".t." ++ toString (stExh.nonce + k)]) = some (.file ByteArray.empty 0o600))
  let (resExh, stExh') := ((mkSubtree vfsDirOps dhExh).atomicWriteBytes { segments := [maxLeaf] } bytes).run stExh
  NondetTest.assert ((∃ e, resExh = .error e ∧ e.kind = .alreadyExists) ∧ stExh'.nodes = stExh.nodes ∧ stExh'.openDirs = stExh.openDirs)

/-- `SubtreeM.mkdir` with `existOk = true` succeeds on existing directories while preserving their permission mode. -/
def test_fs_subtree_mkdir_existOkPreservesExistingDir
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let child ← nondet EntryName
  let pm ← nondet Nat
  let cm ← nondet Nat
  let b ← nondet Bool
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (nodeAt st.tree pos = some (.dir pm) ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [child.val]) = some (.dir cm))
  let sub := mkSubtree vfsDirOps dh
  let (rMkExist, stMkExist) := (sub.mkdir { segments := [child] } b true).run st
  NondetTest.assert (rMkExist = .ok () ∧ nodeAt stMkExist.tree (pos ++ [child.val]) = some (.dir cm))

private def walkEntrySorted (e : WalkEntry) : Prop :=
  List.Pairwise (fun a b => a < b) e.dirs.toList ∧ List.Pairwise (fun a b => a < b) e.files.toList

private def vfsTreePermWalkable (t : VfsTree) : Prop :=
  ∀ (segs : List String) (m : Nat), nodeAt t segs = some (.dir m) →
    (m / 256) % 2 = 1 ∧ (m / 64) % 2 = 1

private def vfsTreePermRemovable (t : VfsTree) : Prop :=
  ∀ (segs : List String) (m : Nat), nodeAt t segs = some (.dir m) →
    (m / 256) % 2 = 1 ∧ (m / 128) % 2 = 1 ∧ (m / 64) % 2 = 1

/-- `listDir` and `walk` return sorted entries (top-down DFS with `"."` relative roots and sorted `dirs`/`files`), expose `.symlink` in `files`, never descend through symlinks, and fail `.notADirectory` on regular files. -/
def test_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let child ← nondet EntryName
  let symName ← nondet EntryName
  let dirTarget ← nondet EntryName
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (VfsKeysComplete st)
  assume (∀ s ∈ pos, validSeg s = true)
  assume (pos.length + 2 < 1024)
  assume (∀ tsub, vfsTreeGet st.tree pos = some tsub → VfsTreeWalkable 4096 tsub)
  assume (symName ≠ dirTarget)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 256) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [symName.val]) = some (.symlink dirTarget.val 0o777))
  assume (nodeAt st.tree (pos ++ [dirTarget.val]) = some (.dir 0o755))
  assume (nodeAt st.tree (pos ++ [dirTarget.val, child.val]) = some (.file ByteArray.empty 0o644))
  let sub := mkSubtree vfsDirOps dh
  let (rList, stList) := (sub.listDir RelPath.root).run st
  NondetTest.assert (∃ names, rList = .ok names ∧ symName ∈ names.toList ∧ dirTarget ∈ names.toList ∧
    (List.Pairwise (fun a b => a.val < b.val) names.toList))
  NondetTest.assert (stList.nodes = st.nodes ∧ stList.openDirs = st.openDirs)
  let (rWalk, stWalk) := (sub.walk RelPath.root).run st
  NondetTest.assert (∃ entries, rWalk = .ok entries ∧
    entries.toList.head?.map (·.root) = some "." ∧
    (entries.toList.any fun e => e.root == "." && symName.val ∈ e.files.toList && !(symName.val ∈ e.dirs.toList) && dirTarget.val ∈ e.dirs.toList) ∧
    !(entries.toList.any fun e => e.root == symName.val) ∧
    (entries.toList.foldr (fun e acc => walkEntrySorted e ∧ acc) True))
  NondetTest.assert (stWalk.nodes = st.nodes ∧ stWalk.openDirs = st.openDirs)
  let (rSubWalk, stSubWalk) := (sub.walk { segments := [dirTarget] }).run st
  NondetTest.assert (∃ entries, rSubWalk = .ok entries ∧
    entries.toList.head?.map (·.root) = some "." ∧
    (entries.toList.any fun e => e.root == "." && child.val ∈ e.files.toList) ∧
    (entries.toList.foldr (fun e acc => walkEntrySorted e ∧ acc) True))
  NondetTest.assert (stSubWalk.nodes = st.nodes ∧ stSubWalk.openDirs = st.openDirs)
  let (rFileWalk, stFileWalk) := (sub.walk { segments := [dirTarget, child] }).run st
  NondetTest.assert ((∃ e, rFileWalk = .error e ∧ e.kind = .notADirectory) ∧ stFileWalk.nodes = st.nodes ∧ stFileWalk.openDirs = st.openDirs)

/-- `withFileLock` releases its lock even on `.error` callbacks, and `tryWithFileLock` returns `.ok none` without running the callback on `.wouldBlock`. -/
def test_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let leaf ← nondet EntryName
  let lockMode ← nondet LockMode
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 64) % 2 = 1)
  assume (∃ fm, nodeAt st.tree (pos ++ [leaf.val]) = some (.file ByteArray.empty fm))
  let canon := pathOfSegs (pos ++ [leaf.val])
  assume (!hasLockConflict st.locks canon lockMode)
  let rel : RelPath := { segments := [leaf] }
  let sub := mkSubtree vfsDirOps dh
  let errVal : FsError := { kind := .ioError, message := "callback aborted" }
  let errAct : StateM VfsState (Except FsError Unit) := pure (.error errVal)
  let (rErr, stErr) := (sub.withFileLock rel lockMode false errAct).run st
  NondetTest.assert (rErr = .error errVal ∧ stErr.locks = st.locks ∧ stErr.openDirs = st.openDirs)
  let okAct : StateM VfsState (Except FsError Nat) := pure (.ok 42)
  let (rTryOk, stTryOk) := (sub.tryWithFileLock rel lockMode false okAct).run st
  NondetTest.assert (rTryOk = .ok (some 42) ∧ stTryOk.locks = st.locks ∧ stTryOk.openDirs = st.openDirs)
  let contendedSt : VfsState := { st with locks := (st.nextLockId, canon, .exclusive) :: st.locks, nextLockId := st.nextLockId + 1 }
  let (rBlocked, stBlocked) := (sub.tryWithFileLock rel lockMode false errAct).run contendedSt
  NondetTest.assert (rBlocked = .ok none ∧ stBlocked.locks = contendedSt.locks ∧ stBlocked.openDirs = contendedSt.openDirs)

/-- Closed or forged `DirHandle` values fail all 12 `SubtreeM` operations (including on `RelPath.root`) with `.invalidInput` without mutating `nodes` or `locks`. -/
def test_fs_subtree_closedHandle_refusesAllOps
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  let bytes ← nondet ByteArray
  let lockMode ← nondet LockMode
  let b1 ← nondet Bool
  let b2 ← nondet Bool
  assume (lookupDir st dh = none)
  let sub := mkSubtree vfsDirOps dh
  let rel : RelPath := { segments := [child] }
  let (rLstat, s1) := (sub.lstat RelPath.root).run st
  let (rRead, s2) := (sub.readRegular rel).run st
  let (rWrite, s3) := (sub.atomicWriteBytes rel bytes).run st
  let (rMkdir, s4) := (sub.mkdir RelPath.root b1 b2).run st
  let (rUnlink, s5) := (sub.unlink rel b1).run st
  let (rRmdir, s6) := (sub.rmdir rel).run st
  let (rRmtree, s7) := (sub.rmtree rel b1).run st
  let (rSymlink, s8) := (sub.symlink "t" rel).run st
  let (rList, s9) := (sub.listDir RelPath.root).run st
  let (rWalk, s10) := (sub.walk RelPath.root).run st
  let (rWLock, s11) := (sub.withFileLock rel lockMode b1 (pure (.ok ()))).run st
  let (rTLock, s12) := (sub.tryWithFileLock rel lockMode b1 (pure (.ok ()))).run st
  NondetTest.assert ((∃ e, rLstat = .error e ∧ e.kind = .invalidInput) ∧ s1.nodes = st.nodes)
  NondetTest.assert ((∃ e, rRead = .error e ∧ e.kind = .invalidInput) ∧ s2.nodes = st.nodes)
  NondetTest.assert ((∃ e, rWrite = .error e ∧ e.kind = .invalidInput) ∧ s3.nodes = st.nodes)
  NondetTest.assert ((∃ e, rMkdir = .error e ∧ e.kind = .invalidInput) ∧ s4.nodes = st.nodes)
  NondetTest.assert ((∃ e, rUnlink = .error e ∧ e.kind = .invalidInput) ∧ s5.nodes = st.nodes)
  NondetTest.assert ((∃ e, rRmdir = .error e ∧ e.kind = .invalidInput) ∧ s6.nodes = st.nodes)
  NondetTest.assert ((∃ e, rRmtree = .error e ∧ e.kind = .invalidInput) ∧ s7.nodes = st.nodes)
  NondetTest.assert ((∃ e, rSymlink = .error e ∧ e.kind = .invalidInput) ∧ s8.nodes = st.nodes)
  NondetTest.assert ((∃ e, rList = .error e ∧ e.kind = .invalidInput) ∧ s9.nodes = st.nodes)
  NondetTest.assert ((∃ e, rWalk = .error e ∧ e.kind = .invalidInput) ∧ s10.nodes = st.nodes)
  NondetTest.assert ((∃ e, rWLock = .error e ∧ e.kind = .invalidInput) ∧ s11.nodes = st.nodes ∧ s11.locks = st.locks)
  NondetTest.assert ((∃ e, rTLock = .error e ∧ e.kind = .invalidInput) ∧ s12.nodes = st.nodes ∧ s12.locks = st.locks)

/-- `SubtreeM.unlink` honors `missingOk`, removes regular files, and rejects directories with `.isADirectory`. -/
def test_fs_subtree_unlink_missingOkAndKindRules
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let missingLeaf ← nondet EntryName
  let fileLeaf ← nondet EntryName
  let dirLeaf ← nondet EntryName
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [missingLeaf.val]) = none)
  assume (∃ bs fm, nodeAt st.tree (pos ++ [fileLeaf.val]) = some (.file bs fm))
  assume (∃ dm, nodeAt st.tree (pos ++ [dirLeaf.val]) = some (.dir dm))
  let sub := mkSubtree vfsDirOps dh
  let (rMissOk, stMissOk) := (sub.unlink { segments := [missingLeaf] } true).run st
  NondetTest.assert (rMissOk = .ok () ∧ stMissOk.nodes = st.nodes)
  let (rMissErr, stMissErr) := (sub.unlink { segments := [missingLeaf] } false).run st
  NondetTest.assert ((∃ e, rMissErr = .error e ∧ e.kind = .notFound) ∧ stMissErr.nodes = st.nodes)
  let (rFile, stFile) := (sub.unlink { segments := [fileLeaf] } false).run st
  NondetTest.assert (rFile = .ok () ∧ nodeAt stFile.tree (pos ++ [fileLeaf.val]) = none ∧ SameOutside (pos ++ [fileLeaf.val]) st stFile)
  let (rDir, stDir) := (sub.unlink { segments := [dirLeaf] } false).run st
  NondetTest.assert ((∃ e, rDir = .error e ∧ e.kind = .isADirectory) ∧ stDir.nodes = st.nodes)

/-- `SubtreeM.rmdir` removes empty directories and rejects non-empty directories (`.notEmpty`), missing paths (`.notFound`), and files (`.notADirectory`). -/
def test_fs_subtree_rmdir_emptyAndErrors
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let emptyDir ← nondet EntryName
  let nonEmptyDir ← nondet EntryName
  let child ← nondet EntryName
  let missingLeaf ← nondet EntryName
  let fileLeaf ← nondet EntryName
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (VfsKeysComplete st)
  assume (∀ s ∈ pos, validSeg s = true)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (∃ em, nodeAt st.tree (pos ++ [emptyDir.val]) = some (.dir em) ∧
    (∀ s : String, nodeAt st.tree (pos ++ [emptyDir.val, s]) = none))
  assume (∃ nm, nodeAt st.tree (pos ++ [nonEmptyDir.val]) = some (.dir nm))
  assume (nodeAt st.tree (pos ++ [nonEmptyDir.val, child.val]) ≠ none)
  assume (nodeAt st.tree (pos ++ [missingLeaf.val]) = none)
  assume (∃ bs fm, nodeAt st.tree (pos ++ [fileLeaf.val]) = some (.file bs fm))
  let sub := mkSubtree vfsDirOps dh
  let (rOk, stOk) := (sub.rmdir { segments := [emptyDir] }).run st
  NondetTest.assert (rOk = .ok () ∧ nodeAt stOk.tree (pos ++ [emptyDir.val]) = none)
  let (rNonEmpty, stNonEmpty) := (sub.rmdir { segments := [nonEmptyDir] }).run st
  NondetTest.assert ((∃ e, rNonEmpty = .error e ∧ e.kind = .notEmpty) ∧ stNonEmpty.nodes = st.nodes)
  let (rMiss, stMiss) := (sub.rmdir { segments := [missingLeaf] }).run st
  NondetTest.assert ((∃ e, rMiss = .error e ∧ e.kind = .notFound) ∧ stMiss.nodes = st.nodes)
  let (rFile, stFile) := (sub.rmdir { segments := [fileLeaf] }).run st
  NondetTest.assert ((∃ e, rFile = .error e ∧ e.kind = .notADirectory) ∧ stFile.nodes = st.nodes)

/-- `SubtreeM.rmtree` honors `ignoreMissing`, rejects files (`.notADirectory`), propagates child permission errors without rolling back removed siblings, and fails with `.ioError` above depth `4096`. -/
def test_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let missingLeaf ← nondet EntryName
  let fileLeaf ← nondet EntryName
  let partialDir ← nondet EntryName
  let c1 ← nondet EntryName
  let c2 ← nondet EntryName
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (VfsKeysComplete st)
  assume (∀ s ∈ pos, validSeg s = true)
  assume (pos.length + 1 < 1024)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [missingLeaf.val]) = none)
  assume (∃ bs fm, nodeAt st.tree (pos ++ [fileLeaf.val]) = some (.file bs fm))
  assume (c1.val < c2.val)
  assume (nodeAt st.tree (pos ++ [partialDir.val]) = some (.dir 0o700))
  assume (∃ bs fm, nodeAt st.tree (pos ++ [partialDir.val, c1.val]) = some (.file bs fm))
  assume (nodeAt st.tree (pos ++ [partialDir.val, c2.val]) = some (.dir 0o000))
  assume (∀ s : String, s ≠ c1.val → s ≠ c2.val → nodeAt st.tree (pos ++ [partialDir.val, s]) = none)
  let sub := mkSubtree vfsDirOps dh
  let (rIgnOk, stIgnOk) := (sub.rmtree { segments := [missingLeaf] } true).run st
  NondetTest.assert (rIgnOk = .ok () ∧ stIgnOk.nodes = st.nodes)
  let (rMiss, stMiss) := (sub.rmtree { segments := [missingLeaf] } false).run st
  NondetTest.assert ((∃ e, rMiss = .error e ∧ e.kind = .notFound) ∧ stMiss.nodes = st.nodes)
  let (rFile, stFile) := (sub.rmtree { segments := [fileLeaf] } false).run st
  NondetTest.assert ((∃ e, rFile = .error e ∧ e.kind = .notADirectory) ∧ stFile.nodes = st.nodes)
  let (rPartial, stPartial) := (sub.rmtree { segments := [partialDir] } false).run st
  NondetTest.assert ((∃ e, rPartial = .error e ∧ e.kind = .permissionDenied) ∧
    nodeAt stPartial.tree (pos ++ [partialDir.val, c1.val]) = none ∧
    stPartial.openDirs = st.openDirs ∧
    SameOutside (pos ++ [partialDir.val]) st stPartial)
  let stDeep ← nondet VfsState
  let dhDeep ← nondet DirHandle
  let posDeep ← nondet (List String)
  let deepDir ← nondet EntryName
  assume (lookupDir stDeep dhDeep = some posDeep)
  assume (DirHandleInvariant stDeep)
  assume (VfsKeysComplete stDeep)
  assume (∀ s ∈ posDeep, validSeg s = true)
  assume (posDeep.length + 1 < 1024)
  assume (∃ pm, nodeAt stDeep.tree posDeep = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt stDeep.tree (posDeep ++ [deepDir.val]) = some (.dir 0o700))
  assume (∀ tsub, vfsTreeGet stDeep.tree (posDeep ++ [deepDir.val]) = some tsub →
    VfsTreeValidSegs tsub ∧ vfsTreePermRemovable tsub ∧ ¬ VfsTreeRemovable 4096 tsub)
  let (rDeep, stDeep') := ((mkSubtree vfsDirOps dhDeep).rmtree { segments := [deepDir] } false).run stDeep
  NondetTest.assert ((∃ e, rDeep = .error e ∧ e.kind = .ioError) ∧ stDeep'.openDirs = stDeep.openDirs)

/-- `SubtreeM.mkdir` creates missing parent chains when `parents = true` with `0o755`, and `existOk = true` fails `.alreadyExists` on existing regular files. -/
def test_fs_subtree_mkdir_parentsAndExistOkRules
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let pDir ← nondet EntryName
  let cDir ← nondet EntryName
  let existingFile ← nondet EntryName
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 256) % 2 = 1 ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [pDir.val]) = none)
  assume (∃ bs fm, nodeAt st.tree (pos ++ [existingFile.val]) = some (.file bs fm))
  let sub := mkSubtree vfsDirOps dh
  let (rParents, stParents) := (sub.mkdir { segments := [pDir, cDir] } true false).run st
  NondetTest.assert (rParents = .ok () ∧
    nodeAt stParents.tree (pos ++ [pDir.val]) = some (.dir 0o755) ∧
    nodeAt stParents.tree (pos ++ [pDir.val, cDir.val]) = some (.dir 0o755))
  let (rFileExist, stFileExist) := (sub.mkdir { segments := [existingFile] } false true).run st
  NondetTest.assert ((∃ e, rFileExist = .error e ∧ e.kind = .alreadyExists) ∧ stFileExist.nodes = st.nodes)

/-- `SubtreeM.symlink` rejects empty or NUL-containing `target` strings upfront with `.invalidInput` and creates `.symlink` entries on missing paths. -/
def test_fs_subtree_symlink_createsAndValidatesTarget
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let leaf ← nondet EntryName
  let badTarget ← nondet String
  let goodTarget ← nondet String
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (badTarget = "" ∨ Char.ofNat 0 ∈ badTarget.toList)
  assume (goodTarget ≠ "" ∧ Char.ofNat 0 ∉ goodTarget.toList)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [leaf.val]) = none)
  let sub := mkSubtree vfsDirOps dh
  let rel : RelPath := { segments := [leaf] }
  let (rBad, stBad) := (sub.symlink badTarget rel).run st
  NondetTest.assert ((∃ e, rBad = .error e ∧ e.kind = .invalidInput) ∧ stBad.nodes = st.nodes)
  let (rOk, stOk) := (sub.symlink goodTarget rel).run st
  NondetTest.assert (rOk = .ok () ∧ nodeAt stOk.tree (pos ++ [leaf.val]) = some (.symlink goodTarget 0o777))

/-- `SubtreeM.walk` propagates `.permissionDenied` loudly on unreadable subdirectories and fails with `.ioError` when nesting depth exceeds `4096`. -/
def test_fs_subtree_walk_errorsAndDepth
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit := do
  let st ← nondet VfsState
  let dh ← nondet DirHandle
  let pos ← nondet (List String)
  let unrd ← nondet EntryName
  assume (lookupDir st dh = some pos)
  assume (DirHandleInvariant st)
  assume (VfsKeysComplete st)
  assume (∀ s ∈ pos, validSeg s = true)
  assume (pos.length + 1 < 1024)
  assume (∃ pm, nodeAt st.tree pos = some (.dir pm) ∧ (pm / 256) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt st.tree (pos ++ [unrd.val]) = some (.dir 0o111))
  let sub := mkSubtree vfsDirOps dh
  let (rPerm, stPerm) := (sub.walk { segments := [unrd] }).run st
  NondetTest.assert ((∃ e, rPerm = .error e ∧ e.kind = .permissionDenied) ∧ stPerm.nodes = st.nodes ∧ stPerm.openDirs = st.openDirs)
  let stDeep ← nondet VfsState
  let dhDeep ← nondet DirHandle
  let posDeep ← nondet (List String)
  let deep ← nondet EntryName
  assume (lookupDir stDeep dhDeep = some posDeep)
  assume (DirHandleInvariant stDeep)
  assume (VfsKeysComplete stDeep)
  assume (∀ s ∈ posDeep, validSeg s = true)
  assume (posDeep.length + 1 < 1024)
  assume (∃ pm, nodeAt stDeep.tree posDeep = some (.dir pm) ∧ (pm / 256) % 2 = 1 ∧ (pm / 64) % 2 = 1)
  assume (nodeAt stDeep.tree (posDeep ++ [deep.val]) = some (.dir 0o555))
  assume (∀ tsub, vfsTreeGet stDeep.tree (posDeep ++ [deep.val]) = some tsub →
    VfsTreeValidSegs tsub ∧ vfsTreePermWalkable tsub ∧ ¬ VfsTreeWalkable 4096 tsub)
  let (rDeep, stDeep') := ((mkSubtree vfsDirOps dhDeep).walk { segments := [deep] }).run stDeep
  NondetTest.assert ((∃ e, rDeep = .error e ∧ e.kind = .ioError) ∧ stDeep'.nodes = stDeep.nodes ∧ stDeep'.openDirs = stDeep.openDirs)

/-- All 12 `SubtreeM` operations confine mutations strictly within `pos` (`SpecSubtreeSameOutside`). -/
def test_fs_subtree_sameOutside_confinesAllOps
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit :=
  NondetTest.assert (SpecSubtreeSameOutside mkSubtree)

/-- Ancestor symlinks always fail all 12 `SubtreeM` operations with `.invalidInput` without mutating `nodes` (`SpecNoSymlinkFollowAncestors`). -/
def test_fs_subtree_noSymlinkFollowAncestors_refusesAllOps
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit :=
  NondetTest.assert (SpecNoSymlinkFollowAncestors mkSubtree)

/-- Arbitrary `SubtreeProg` programs interleaved with `EnvInside` external mutations preserve `SameOutside pos`, `openDirs`, and `locks` (`SpecSubtreeProgramSameOutsideInterleaved`). -/
def test_fs_subtree_programSameOutsideInterleaved_confinesPrograms
    {runner} [NondetTest runner] (mkOpener : SubtreeOpenerBuilder (StateM VfsState)) : runner Unit :=
  NondetTest.assert (SpecSubtreeProgramSameOutsideInterleaved mkOpener)

/-- Every `SubtreeM` operation and `withSubtree` preserves `openDirs` (`SpecDescriptorConservation`). -/
def test_fs_subtree_descriptorConservation_preservesOpenDirs
    {runner} [NondetTest runner]
    (mkOpener : SubtreeOpenerBuilder (StateM VfsState))
    (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit :=
  NondetTest.assert (SpecDescriptorConservation mkOpener mkSubtree)

/-- Every `DirHandle`-taking `vfsDirOps` primitive refuses invalid/closed handles with `.invalidInput` (`SpecInvalidHandleRefused`). -/
def test_fs_vfsDirOps_invalidHandleRefused
    {runner} [NondetTest runner] (spec : Prop := SpecInvalidHandleRefused) : runner Unit :=
  NondetTest.assert spec

/-- `atomicWriteBytes` followed by `readRegular` and `lstat` preserves written bytes and `0o644` mode (`SpecAtomicWriteReadRegularRoundTrip`). -/
def test_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit :=
  NondetTest.assert (SpecAtomicWriteReadRegularRoundTrip mkSubtree)

/-- `mkdir` entries appear in `listDir` and `rmtree` targets become `.notFound` (`SpecMkdirVisibleAndRmtreeNotFound`). -/
def test_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit :=
  NondetTest.assert (SpecMkdirVisibleAndRmtreeNotFound mkSubtree)

/-- On symlink-free traversable subtrees, `SubtreeM.readRegular` and `SubtreeM.lstat` match ambient `vfsOps` (`SpecSubtreeAgreesWithAmbientOnSymlinkFree`). -/
def test_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi
    {runner} [NondetTest runner] (mkSubtree : SubtreeBuilder (StateM VfsState)) : runner Unit :=
  NondetTest.assert (SpecSubtreeAgreesWithAmbientOnSymlinkFree mkSubtree)

/-- Mapping a `.wouldBlock` raw error preserves `.wouldBlock` kind, path, errno, and non-empty message. -/
def test_fsraw_mapRawError_wouldBlock
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path? ← nondet (Option String)
  let errno ← nondet UInt32
  let detail ← nondet String
  let err := api.mapRawError (.wouldBlock path? errno detail)
  NondetTest.assert (err.kind = .wouldBlock ∧ err.path = path? ∧ err.errnoCode = some errno ∧ err.message ≠ "")

/-- `EntryName.parse s` succeeds iff `validSeg s = true` and otherwise fails with `.invalidInput` and non-empty message. -/
def test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe
    {runner} [NondetTest runner]
    (parseName : String → Except FsError EntryName := EntryName.parse) : runner Unit := do
  let s ← nondet String
  match parseName s with
  | .ok n => NondetTest.assert (validSeg s = true ∧ n.val = s)
  | .error e => NondetTest.assert (validSeg s = false ∧ e.kind = .invalidInput ∧ e.message ≠ "")

/-- `RelPath.parse` rejects `""`, leading `/`, trailing `/`, `//`, `.`, `..`, and NUL with `.invalidInput`, accepts valid multi-segment paths like `"a/b"`, and `RelPath.parseRoot "."` returns `RelPath.root`. -/
def test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot
    {runner} [NondetTest runner]
    (parseRel : String → Except FsError RelPath := RelPath.parse)
    (parseRelRoot : String → Except FsError RelPath := RelPath.parseRoot) : runner Unit := do
  let seg ← nondet String
  let bads := ["", "/" ++ seg, seg ++ "/", ".", "..", "a//b", "a/./b", "a/../b", "a" ++ String.ofList [Char.ofNat 0] ++ "b"]
  NondetTest.assert (bads.all fun p =>
    match parseRel p with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match parseRel "a/b" with
    | .ok rel => rel.segments.map (·.val) == ["a", "b"]
    | .error _ => false)
  NondetTest.assert (parseRelRoot "." = .ok RelPath.root)
  NondetTest.assert (seg = "." ∨ parseRelRoot seg = parseRel seg)

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

/-- Calling `ops.openDirAt dh child` when `lstatAt dh child` is a symlink fails with `.invalidInput` and preserves state. -/
def test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  assume (∃ st, ((ops.lstatAt dh child).run s₀).1 = .ok st ∧ st.kind = .symlink)
  let (res, s₁) := (ops.openDirAt dh child).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `ops.readRegularAt dh child` on a symlink fails with `.invalidInput` and on a directory fails with `.isADirectory`, leaving state unchanged. -/
def test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  match ((ops.lstatAt dh child).run s₀).1 with
  | .error _ => pure ()
  | .ok st =>
    if st.kind == .symlink then
      let (res, s₁) := (ops.readRegularAt dh child).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)
    else if st.kind == .dir then
      let (res, s₁) := (ops.readRegularAt dh child).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)
    else
      pure ()

/-- Calling `ops.createFileAt` rejects existing entries (including symlinks) with `.alreadyExists` and creates missing regular files with exact bytes and mode `0o644`. -/
def test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  let bytes ← nondet ByteArray
  assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt dh child).run s₀).1 with
  | .ok _ =>
    let (res, s₁) := (ops.createFileAt dh child bytes).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)
  | .error err =>
    assume (err.kind = .notFound)
    let (res, s₁) := (ops.createFileAt dh child bytes).run s₀
    NondetTest.assert (res = .ok ())
    NondetTest.assert (∃ st, ((ops.lstatAt dh child).run s₁).1 = .ok st ∧
      st.kind = .file ∧ st.byteSize = bytes.size ∧ st.mode = 0o644)
    NondetTest.assert (((ops.readRegularAt dh child).run s₁).1 = .ok bytes)

/-- Calling `ops.createDirAt` rejects existing entries (including symlinks) with `.alreadyExists` and creates missing directories with mode `0o755`. -/
def test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt dh child).run s₀).1 with
  | .ok _ =>
    let (res, s₁) := (ops.createDirAt dh child).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)
  | .error err =>
    assume (err.kind = .notFound)
    let (res, s₁) := (ops.createDirAt dh child).run s₀
    NondetTest.assert (res = .ok ())
    NondetTest.assert (∃ st, ((ops.lstatAt dh child).run s₁).1 = .ok st ∧
      st.kind = .dir ∧ st.mode = 0o755)

/-- Calling `ops.unlinkAt` checks symlink vs directory flags, enforces empty-dir removal vs non-empty `.notEmpty`, and reports `.notFound` on missing entries. -/
def test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt dh child).run s₀).1 with
  | .ok st =>
    if st.kind == .symlink then
      let (rDir, sDir) := (ops.unlinkAt dh child true).run s₀
      NondetTest.assert ((∃ e, rDir = .error e ∧ e.kind = .notADirectory) ∧ sDir = s₀)
      let (rUnlink, sUnlink) := (ops.unlinkAt dh child false).run s₀
      NondetTest.assert (rUnlink = .ok () ∧
        ∃ e, ((ops.lstatAt dh child).run sUnlink).1 = .error e ∧ e.kind = .notFound)
    else if st.kind == .dir then
      let (rFile, sFile) := (ops.unlinkAt dh child false).run s₀
      NondetTest.assert ((∃ e, rFile = .error e ∧ e.kind = .isADirectory) ∧ sFile = s₀)
    else
      pure ()
  | .error lErr =>
    if lErr.kind == .notFound then
      let (rFile, sFile) := (ops.unlinkAt dh child false).run s₀
      NondetTest.assert ((∃ e, rFile = .error e ∧ e.kind = .notFound) ∧ sFile = s₀)
      let (rDir, sDir) := (ops.unlinkAt dh child true).run s₀
      NondetTest.assert ((∃ e, rDir = .error e ∧ e.kind = .notFound) ∧ sDir = s₀)
    else
      pure ()
  let (openRes, sRoot) := (ops.openDir "/").run s₀
  match openRes with
  | .error _ => pure ()
  | .ok rootDh =>
    let inner ← nondet EntryName
    match ((ops.fstatDir rootDh).run sRoot).1, ((ops.lstatAt rootDh child).run sRoot).1 with
    | .ok rSt, .error mErr =>
      if rSt.kind == .dir && (rSt.mode / 128) % 2 == 1 && (rSt.mode / 64) % 2 == 1 && mErr.kind == .notFound then
        let (rMk1, s₁) := (ops.createDirAt rootDh child).run sRoot
        NondetTest.assert (rMk1 = .ok ())
        let (rRmEmpty, s₂) := (ops.unlinkAt rootDh child true).run s₁
        NondetTest.assert (rRmEmpty = .ok () ∧
          ∃ e, ((ops.lstatAt rootDh child).run s₂).1 = .error e ∧ e.kind = .notFound)
        let (rMk2, s₃) := (ops.createDirAt rootDh child).run sRoot
        NondetTest.assert (rMk2 = .ok ())
        let (rOpen, s₄) := (ops.openDirAt rootDh child).run s₃
        match rOpen with
        | .error _ =>
          let _ := (ops.closeDir rootDh).run s₄
          NondetTest.assert False
        | .ok childDh =>
          let (rCf, s₅) := (ops.createFileAt childDh inner ByteArray.empty).run s₄
          NondetTest.assert (rCf = .ok ())
          let (rCl, s₆) := (ops.closeDir childDh).run s₅
          NondetTest.assert (rCl = .ok ())
          let (rNotEmpty, s₇) := (ops.unlinkAt rootDh child true).run s₆
          let _ := (ops.closeDir rootDh).run s₇
          NondetTest.assert ((∃ e, rNotEmpty = .error e ∧ e.kind = .notEmpty) ∧ s₇ = s₆)
      else
        let _ := (ops.closeDir rootDh).run sRoot
        pure ()
    | _, _ =>
      let _ := (ops.closeDir rootDh).run sRoot
      pure ()

/-- Closing an opened `DirHandle` via `ops.closeDir` invalidates it for all subsequent `*at` primitives (including asymmetric `renameAt` arguments) and zero-ID handles are rejected with `.invalidInput`. -/
def test_fsraw_rawDirOps_closedHandleRejected
    {S : Type} {runner} [NondetTest runner]
    (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let child ← nondet EntryName
  let bytes ← nondet ByteArray
  let forgedZero : DirHandle := { handleId := 0, rootPath := "/" }
  NondetTest.assert (∃ e, (ops.fstatDir forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.closeDir forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  let (openRes, s₁) := (ops.openDir root).run s₀
  match openRes with
  | .error _ => pure ()
  | .ok dh =>
    let (liveRes, s₁') := (ops.openDir root).run s₁
    let (closeRes, s₂) := (ops.closeDir dh).run s₁'
    NondetTest.assert (closeRes = .ok ())
    NondetTest.assert (∃ e, (ops.fstatDir dh |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.lstatAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.readDirAt dh |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.openDirAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.createDirAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.readRegularAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.createFileAt dh child bytes |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.renameAt dh child dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.unlinkAt dh child false |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.symlinkAt "t" dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.acquireLockAt dh child .exclusive false true |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.closeDir dh |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    match liveRes with
    | .ok liveDh =>
      if liveDh.handleId != dh.handleId then
        NondetTest.assert (∃ e, (ops.renameAt dh child liveDh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
        NondetTest.assert (∃ e, (ops.renameAt liveDh child dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
      else
        pure ()
    | .error _ => pure ()

/-- Calling `ops.fstatDir` on an opened directory handle succeeds with `kind = .dir` and does not mutate state. -/
def test_fsraw_rawDirOps_fstatDir_validReturnsDir
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let (openRes, s₁) := (ops.openDir root).run s₀
  match openRes with
  | .error _ => pure ()
  | .ok dh =>
    let (res, s₂) := (ops.fstatDir dh).run s₁
    let _ := (ops.closeDir dh).run s₂
    NondetTest.assert ((∃ st, res = .ok st ∧ st.kind = .dir) ∧ s₂ = s₁)

/-- Calling `ops.readDirAt` returns duplicate-free (`Nodup`) `EntryName` entries and leaves state unchanged. -/
def test_fsraw_rawDirOps_readDirAt_sortedUnique
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let (res, s₁) := (ops.readDirAt dh).run s₀
  match res with
  | .error _ => NondetTest.assert (s₁ = s₀)
  | .ok entries =>
    NondetTest.assert (entries.toList.Nodup ∧ s₁ = s₀)

/-- Calling `ops.renameAt` moves regular files across open handles, rejects missing sources with `.notFound`, and rejects file/directory kind mismatches (and directory-into-descendant `.invalidInput`). -/
def test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch
    {S : Type} {runner} [NondetTest runner]
    (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let srcDh ← nondet DirHandle
  let srcName ← nondet EntryName
  let dstDh ← nondet DirHandle
  let dstName ← nondet EntryName
  assume (∃ dSt, ((ops.fstatDir srcDh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  assume (∃ dSt, ((ops.fstatDir dstDh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt srcDh srcName).run s₀).1 with
  | .error sErr =>
    if sErr.kind == .notFound then
      let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ s₁ = s₀)
    else
      pure ()
  | .ok srcSt =>
    match ((ops.lstatAt dstDh dstName).run s₀).1 with
    | .ok dstSt =>
      if srcSt.kind == .dir && dstSt.kind == .file then
        let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
        if srcDh.handleId == dstDh.handleId then
          NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notADirectory) ∧ s₁ = s₀)
        else
          NondetTest.assert ((∃ e, res = .error e ∧ (e.kind = .notADirectory ∨ e.kind = .invalidInput)) ∧ s₁ = s₀)
      else if srcSt.kind == .file && dstSt.kind == .dir then
        let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
        NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)
      else
        pure ()
    | .error dErr =>
      if dErr.kind == .notFound && srcSt.kind == .file && (srcDh.handleId != dstDh.handleId || srcName != dstName) then
        let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
        NondetTest.assert (res = .ok ())
        NondetTest.assert (∃ st, ((ops.lstatAt dstDh dstName).run s₁).1 = .ok st ∧ st.kind = .file)
        NondetTest.assert (∃ e, ((ops.lstatAt srcDh srcName).run s₁).1 = .error e ∧ e.kind = .notFound)
      else
        pure ()

/-- Calling `ops.symlinkAt` rejects empty or NUL-containing `target` strings with `.invalidInput` and creates a `.symlink` entry when missing and writable. -/
def test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  let target ← nondet String
  if target.isEmpty || target.contains (Char.ofNat 0) then
    let (res, s₁) := (ops.symlinkAt target dh child).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)
  else
    assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
      (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
    match ((ops.lstatAt dh child).run s₀).1 with
    | .error err =>
      if err.kind == .notFound then
        let (res, s₁) := (ops.symlinkAt target dh child).run s₀
        NondetTest.assert (res = .ok () ∧
          ∃ st, ((ops.lstatAt dh child).run s₁).1 = .ok st ∧ st.kind = .symlink)
      else
        pure ()
    | .ok _ => pure ()

/-- Successive calls to `ops.freshTempName` produce distinct valid `EntryName` values. -/
def test_fsraw_rawDirOps_freshTempName_distinctAndValid
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let (n₁, s₁) := ops.freshTempName.run s₀
  let (n₂, _) := ops.freshTempName.run s₁
  NondetTest.assert (validSeg n₁.val = true ∧ validSeg n₂.val = true ∧ n₁ ≠ n₂)


set_option maxRecDepth 2048 in
/-- Complete `36 × 10` `(request, errorKind)` coverage matrix across all 36 fallible `LeanSwe.Fs` entrypoints (`FsErrorKind`). -/
def errorCoverage : List (Core.ErrorObligation FsErrorKind) :=
  (
    { request := "LeanSwe.Fs.withName", errorKind := .notFound, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_notFound" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .alreadyExists, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_alreadyExists" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .permissionDenied, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_permissionDenied" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .isADirectory, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_isADirectory" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .notADirectory, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_notADirectory" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .notEmpty, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_notEmpty" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withName_invalidInput" .real }
    :: { request := "LeanSwe.Fs.withName", errorKind := .unsupported, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_unsupported" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .wouldBlock, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_wouldBlock" }
    :: { request := "LeanSwe.Fs.withName", errorKind := .ioError, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withName_never_ioError" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .notFound, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_notFound" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .alreadyExists, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_alreadyExists" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .permissionDenied, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_permissionDenied" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .isADirectory, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_isADirectory" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .notADirectory, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_notADirectory" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .notEmpty, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_notEmpty" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSuffix_invalidInput" .real }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .unsupported, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_unsupported" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .wouldBlock, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_wouldBlock" }
    :: { request := "LeanSwe.Fs.withSuffix", errorKind := .ioError, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_withSuffix_never_ioError" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .notFound, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_notFound" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .alreadyExists, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_alreadyExists" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .permissionDenied, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_permissionDenied" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .isADirectory, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_isADirectory" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .notADirectory, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_notADirectory" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .notEmpty, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_notEmpty" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_relativeTo_invalidInput" .real }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .unsupported, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_unsupported" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .wouldBlock, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_wouldBlock" }
    :: { request := "LeanSwe.Fs.relativeTo", errorKind := .ioError, justification := .provedImpossible "LeanSwe.Fs.Proofs.fs_relativeTo_never_ioError" }
    :: { request := "LeanSwe.Fs.readText", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_notFound" .real }
    :: { request := "LeanSwe.Fs.readText", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readText", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.readText", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_isADirectory" .real }
    :: { request := "LeanSwe.Fs.readText", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_notADirectory" .real }
    :: { request := "LeanSwe.Fs.readText", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readText", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_invalidInput" .real }
    :: { request := "LeanSwe.Fs.readText", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readText", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readText", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readText_ioError" .real }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_notFound" .real }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_isADirectory" .real }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_notADirectory" .real }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_invalidInput" .real }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeText", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeText_ioError" .real }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_notFound" .real }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_isADirectory" .real }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_notADirectory" .real }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_invalidInput" .real }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.appendText", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_appendText_ioError" .real }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_notFound" .real }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_isADirectory" .real }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_notADirectory" .real }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_invalidInput" .real }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readBytes", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readBytes_ioError" .real }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_notFound" .real }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_isADirectory" .real }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_notADirectory" .real }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_invalidInput" .real }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.writeBytes", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_writeBytes_ioError" .real }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_notFound" .real }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_isADirectory" .real }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_notADirectory" .real }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_invalidInput" .real }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteBytes", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteBytes_ioError" .real }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_notFound" .real }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_isADirectory" .real }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_notADirectory" .real }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_invalidInput" .real }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_mocked" .mocked }
    :: { request := "LeanSwe.Fs.atomicWriteText", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_atomicWriteText_ioError" .real }
    :: { request := "LeanSwe.Fs.touch", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_notFound" .real }
    :: { request := "LeanSwe.Fs.touch", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_alreadyExists" .real }
    :: { request := "LeanSwe.Fs.touch", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.touch", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_isADirectory" .real }
    :: { request := "LeanSwe.Fs.touch", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_notADirectory" .real }
    :: { request := "LeanSwe.Fs.touch", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_mocked" .mocked }
    :: { request := "LeanSwe.Fs.touch", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_invalidInput" .real }
    :: { request := "LeanSwe.Fs.touch", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_mocked" .mocked }
    :: { request := "LeanSwe.Fs.touch", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_mocked" .mocked }
    :: { request := "LeanSwe.Fs.touch", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_touch_ioError" .real }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_notFound" .real }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_alreadyExists" .real }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_notADirectory" .real }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_invalidInput" .real }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.mkdir", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_mkdir_ioError" .real }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_notFound" .real }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_isADirectory" .real }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_notADirectory" .real }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_invalidInput" .real }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.unlink", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_unlink_ioError" .real }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_notFound" .real }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_notADirectory" .real }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_notEmpty" .real }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_invalidInput" .real }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmdir", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmdir_ioError" .real }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_notFound" .real }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_notADirectory" .real }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_invalidInput" .real }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rmtree", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rmtree_ioError" .real }
    :: { request := "LeanSwe.Fs.rename", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_notFound" .real }
    :: { request := "LeanSwe.Fs.rename", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rename", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.rename", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_isADirectory" .real }
    :: { request := "LeanSwe.Fs.rename", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_notADirectory" .real }
    :: { request := "LeanSwe.Fs.rename", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_notEmpty" .real }
    :: { request := "LeanSwe.Fs.rename", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_invalidInput" .real }
    :: { request := "LeanSwe.Fs.rename", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rename", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rename", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rename_ioError" .real }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_notFound" .real }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_isADirectory" .real }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_notADirectory" .real }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_invalidInput" .real }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyFile", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyFile_ioError" .real }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_notFound" .real }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_alreadyExists" .real }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_notADirectory" .real }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_invalidInput" .real }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.copyTree", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_copyTree_ioError" .real }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_notFound" .real }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_mocked" .mocked }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_mocked" .mocked }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_notADirectory" .real }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_mocked" .mocked }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_invalidInput" .real }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_mocked" .mocked }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_mocked" .mocked }
    :: { request := "LeanSwe.Fs.pathExists", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_pathExists_ioError" .real }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_notFound" .real }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_notADirectory" .real }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_invalidInput" .real }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isFile", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isFile_ioError" .real }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_notFound" .real }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_notADirectory" .real }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_invalidInput" .real }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isDir", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isDir_ioError" .real }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_notFound" .real }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_notADirectory" .real }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_invalidInput" .real }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.isSymlink", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_isSymlink_ioError" .real }
    :: { request := "LeanSwe.Fs.stat", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_notFound" .real }
    :: { request := "LeanSwe.Fs.stat", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.stat", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.stat", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.stat", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_notADirectory" .real }
    :: { request := "LeanSwe.Fs.stat", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.stat", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_invalidInput" .real }
    :: { request := "LeanSwe.Fs.stat", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.stat", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.stat", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_stat_ioError" .real }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_notFound" .real }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_notADirectory" .real }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_invalidInput" .real }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_mocked" .mocked }
    :: { request := "LeanSwe.Fs.lstat", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_lstat_ioError" .real }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_notFound" .real }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_mocked" .mocked }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_mocked" .mocked }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_notADirectory" .real }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_mocked" .mocked }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_invalidInput" .real }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_mocked" .mocked }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_mocked" .mocked }
    :: { request := "LeanSwe.Fs.chmod", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_chmod_ioError" .real }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_notFound" .real }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_alreadyExists" .real }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_notADirectory" .real }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_invalidInput" .real }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.symlink", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_symlink_ioError" .real }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_notFound" .real }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_notADirectory" .real }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_invalidInput" .real }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_mocked" .mocked }
    :: { request := "LeanSwe.Fs.readLink", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_readLink_ioError" .real }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_notFound" .real }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_mocked" .mocked }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_mocked" .mocked }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_notADirectory" .real }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_mocked" .mocked }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_invalidInput" .real }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_mocked" .mocked }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_mocked" .mocked }
    :: { request := "LeanSwe.Fs.resolve", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_resolve_ioError" .real }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.cwd", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_cwd_mocked" .mocked }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_notFound" .real }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_notADirectory" .real }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_invalidInput" .real }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_mocked" .mocked }
    :: { request := "LeanSwe.Fs.listDir", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_listDir_ioError" .real }
    :: { request := "LeanSwe.Fs.walk", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_notFound" .real }
    :: { request := "LeanSwe.Fs.walk", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_mocked" .mocked }
    :: { request := "LeanSwe.Fs.walk", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.walk", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_mocked" .mocked }
    :: { request := "LeanSwe.Fs.walk", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_notADirectory" .real }
    :: { request := "LeanSwe.Fs.walk", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_mocked" .mocked }
    :: { request := "LeanSwe.Fs.walk", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_invalidInput" .real }
    :: { request := "LeanSwe.Fs.walk", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_mocked" .mocked }
    :: { request := "LeanSwe.Fs.walk", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_mocked" .mocked }
    :: { request := "LeanSwe.Fs.walk", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_walk_ioError" .real }
    :: { request := "LeanSwe.Fs.glob", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_notFound" .real }
    :: { request := "LeanSwe.Fs.glob", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.glob", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.glob", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.glob", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_notADirectory" .real }
    :: { request := "LeanSwe.Fs.glob", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.glob", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_invalidInput" .real }
    :: { request := "LeanSwe.Fs.glob", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.glob", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.glob", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_glob_ioError" .real }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_notFound" .real }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_notADirectory" .real }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_invalidInput" .real }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_mocked" .mocked }
    :: { request := "LeanSwe.Fs.rglob", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_rglob_ioError" .real }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_notFound" .real }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_isADirectory" .real }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_notADirectory" .real }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_invalidInput" .real }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withFileLock", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_notFound" .real }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_isADirectory" .real }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_notADirectory" .real }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_invalidInput" .real }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.tryWithFileLock", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_tryWithFileLock_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .notFound, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_notFound" .real }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .alreadyExists, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .permissionDenied, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_permissionDenied" .real }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .isADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .notADirectory, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_notADirectory" .real }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .notEmpty, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .invalidInput, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_invalidInput" .real }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .unsupported, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .wouldBlock, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_mocked" .mocked }
    :: { request := "LeanSwe.Fs.withSubtree", errorKind := .ioError, justification := .tested "LeanSwe.Fs.RuntimeTests.err_fs_withSubtree_ioError" .real }
    :: []
  )

end LeanSwe.Fs
