import LeanSwe.Fs.Impl.Ambient
import LeanSwe.Fs.Impl.Subtree

namespace LeanSwe.Fs.Internal

open LeanSwe.Fs
  (FsErrorKind FsError EntryKind FileStat WalkEntry FsRawError LockMode FsApi FsApiM
   EntryName RelPath SubtreeM SubtreeOpenerM)

/-- Build a generic `FsApiM m` from handle-free `ScopedRawFsOpsM m` primitives. -/
def mkApiFromScopedRawM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : ScopedRawFsOpsM m) : FsApiM m :=
  let base := ops.toNonLockFsOpsM
  { join := join
    joinMany := joinMany
    normPath := normPath
    parent := parent
    name := name
    stem := stem
    suffix := suffix
    suffixes := suffixes
    withName := withName
    withSuffix := withSuffix
    isAbsolute := isAbsolute
    relativeTo := relativeTo
    mapRawError := base.mapRawError
    readText := readTextImplM base
    writeText := fun p c => base.writeBytes p c.toUTF8
    appendText := base.appendText
    readBytes := base.readBytes
    writeBytes := base.writeBytes
    atomicWriteBytes := atomicWriteBytesImplM base
    atomicWriteText := atomicWriteTextImplM base
    touch := touchImplM base
    mkdir := mkdirImplM base
    unlink := unlinkImplM base
    rmdir := base.removeDir
    rmtree := rmtreeImplM base
    rename := base.rename
    copyFile := copyFileImplM base
    copyTree := copyTreeImplM base
    pathExists := fun p => do
      match ← base.stat true p with
      | .ok _ => return .ok true
      | .error _ => return .ok false
    isFile := fun p => do
      match ← base.stat true p with
      | .ok st => return .ok (st.kind == .file)
      | .error _ => return .ok false
    isDir := fun p => do
      match ← base.stat true p with
      | .ok st => return .ok (st.kind == .dir)
      | .error _ => return .ok false
    isSymlink := fun p => do
      match ← base.stat false p with
      | .ok st => return .ok (st.kind == .symlink)
      | .error _ => return .ok false
    stat := base.stat true
    lstat := base.stat false
    chmod := base.chmod
    symlink := base.symlink
    readLink := base.readLink
    resolve := base.realPath
    cwd := base.cwd
    listDir := listDirSortedM base
    walk := walkImplM base
    glob := globImplM base
    rglob := rglobImplM base
    withFileLock := ops.withFileLock
    tryWithFileLock := ops.tryWithFileLock }

/-- Build a generic `FsApiM m` from `ScopedRawFsOpsM m` with bounded sibling temp-collision retry on `atomicWriteBytes`/`atomicWriteText`. -/
def mkApiFromScopedRawRetryM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : ScopedRawFsOpsM m) : FsApiM m :=
  let base := ops.toNonLockFsOpsM
  { mkApiFromScopedRawM ops with
    atomicWriteBytes := fun p b => atomicWriteBytesRetryM base p b 16
    atomicWriteText := fun p c => atomicWriteBytesRetryM base p c.toUTF8 16 }

/-- Build a generic `FsApiM m` from injected single-step `RawFsOpsM m` primitives. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m] {lockH : Type} (ops : RawFsOpsM m lockH) : FsApiM m :=
  mkApiFromScopedRawM (toScopedRawFsOpsM ops)

/-- Open `rootPath` once via `ops.openDir`, validate it is a directory with owner read+search (`0o500`), execute `action`, and always close the handle on exit. -/
def withSubtreeM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (rootPath : String)
    (action : SubtreeM m → m (Except FsError α)) : m (Except FsError α) := do
  match ← ops.openDir rootPath with
  | .error e => pure (.error e)
  | .ok dh =>
    bracketCloseDirM ops dh do
      match ← ops.fstatDir dh with
      | .error e => pure (.error e)
      | .ok info =>
        if info.kind != .dir then
          pure (.error { kind := .notADirectory, path := some rootPath, message := s!"not a directory: {rootPath}" })
        else if (info.mode / 256) % 2 == 0 || (info.mode / 64) % 2 == 0 then
          pure (.error { kind := .permissionDenied, path := some rootPath, message := s!"permission denied: {rootPath}" })
        else
          action (subtreeOpsM ops dh)

/-- Build a `SubtreeOpenerM m` backed by `ops`. -/
def mkSubtreeOpenerM {m : Type → Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) : SubtreeOpenerM m :=
  { withSubtree := withSubtreeM ops }

end LeanSwe.Fs.Internal
