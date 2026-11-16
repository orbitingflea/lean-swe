import LeanSwe.Fs.Raw.Types
import LeanSwe.Fs.Raw.Impl

namespace LeanSwe.Fs.Raw

@[extern "leanswe_fs_chmod"]
private opaque rawChmod : @& String → UInt32 → IO Unit

@[extern "leanswe_fs_symlink"]
private opaque rawSymlink : @& String → @& String → IO Unit

@[extern "leanswe_fs_readlink"]
private opaque rawReadLink : @& String → IO String

@[extern "leanswe_fs_stat_mode"]
private opaque rawStatMode : @& String → Bool → IO UInt32

@[extern "leanswe_fs_acquire_lock"]
private opaque rawAcquireLock : @& String → UInt8 → Bool → Bool → IO (UInt8 × UInt64 × UInt32)

@[extern "leanswe_fs_release_lock"]
private opaque rawReleaseLock : UInt64 → @& String → IO Unit

@[extern "leanswe_fs_read_regular_bytes"]
private opaque rawReadRegularBytes : @& String → IO ByteArray

@[extern "leanswe_fs_create_file_new"]
private opaque rawCreateFileNew : @& String → @& ByteArray → IO Unit

private def posixRawOps : Internal.PosixRawOps :=
  { chmod := rawChmod
    symlink := rawSymlink
    readLink := rawReadLink
    statMode := rawStatMode
    acquireLock := rawAcquireLock
    releaseLock := rawReleaseLock
    readRegularBytes := rawReadRegularBytes
    createFileNew := rawCreateFileNew }

/-- Default minimal OS primitive operations backed by `IO.FS` and `c/fs_shim.c`. -/
def defaultOps : RawFsOps :=
  Internal.mkRawOps posixRawOps

/-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
@[inline] def mapRawError (err : FsRawError) : FsError :=
  defaultOps.mapRawError err

/-- Inspect metadata (`follow = true` follows symlinks; `false` inspects links). -/
@[inline] def stat (follow : Bool) (path : String) : IO (Except FsError FileStat) :=
  defaultOps.stat follow path

/-- List unsorted immediate entry names in directory. -/
@[inline] def readDir (path : String) : IO (Except FsError (Array String)) :=
  defaultOps.readDir path

/-- Create a single directory (`mkdir`). -/
@[inline] def createDir (path : String) : IO (Except FsError Unit) :=
  defaultOps.createDir path

/-- Remove an empty directory (`rmdir`). -/
@[inline] def removeDir (path : String) : IO (Except FsError Unit) :=
  defaultOps.removeDir path

/-- Remove a file or symbolic link (`unlink`). -/
@[inline] def unlinkFile (path : String) : IO (Except FsError Unit) :=
  defaultOps.unlinkFile path

/-- Read entire binary file. -/
@[inline] def readBytes (path : String) : IO (Except FsError ByteArray) :=
  defaultOps.readBytes path

/-- Write or overwrite binary file. -/
@[inline] def writeBytes (path : String) (bytes : ByteArray) : IO (Except FsError Unit) :=
  defaultOps.writeBytes path bytes

/-- Atomically create a new regular file without following symlinks (`O_CREAT | O_EXCL | O_NOFOLLOW`). -/
@[inline] def createFileNew (path : String) (bytes : ByteArray) : IO (Except FsError Unit) :=
  defaultOps.createFileNew path bytes

/-- Append UTF-8 text to a file, creating it if absent. -/
@[inline] def appendText (path content : String) : IO (Except FsError Unit) :=
  defaultOps.appendText path content

/-- Rename or replace a file or directory. -/
@[inline] def rename (src dst : String) : IO (Except FsError Unit) :=
  defaultOps.rename src dst

/-- Set POSIX permission mode bits (`os.chmod`). -/
@[inline] def chmod (path : String) (mode : Nat) : IO (Except FsError Unit) :=
  defaultOps.chmod path mode

/-- Create symbolic link at `linkPath` pointing to `target`. -/
@[inline] def symlink (target linkPath : String) : IO (Except FsError Unit) :=
  defaultOps.symlink target linkPath

/-- Read symbolic link target path. -/
@[inline] def readLink (path : String) : IO (Except FsError String) :=
  defaultOps.readLink path

/-- Resolve symlinks and return canonical absolute path. -/
@[inline] def realPath (path : String) : IO (Except FsError String) :=
  defaultOps.realPath path

/-- Return current working directory. -/
@[inline] def cwd : IO (Except FsError String) :=
  defaultOps.cwd

/-- Acquire an OS advisory file lock on `path`. -/
@[inline] def acquireLock (path : String) (mode : LockMode := .exclusive)
    (createIfMissing : Bool := true) (nonBlocking : Bool := false) : IO (Except FsError LockHandle) :=
  defaultOps.acquireLock path mode createIfMissing nonBlocking

/-- Release a previously acquired OS advisory file lock handle. -/
@[inline] def releaseLock (handle : LockHandle) : IO (Except FsError Unit) :=
  defaultOps.releaseLock handle

@[extern "leanswe_fs_open_dir"]
private opaque rawOpenDir : @& String → IO UInt64

@[extern "leanswe_fs_open_dir_at"]
private opaque rawOpenDirAt : UInt64 → @& String → IO UInt64

@[extern "leanswe_fs_close_dir"]
private opaque rawCloseDir : UInt64 → @& String → IO Unit

@[extern "leanswe_fs_fstat_dir"]
private opaque rawFstatDir : UInt64 → @& String → IO (UInt8 × UInt64 × UInt32 × Int × UInt32 × Int × UInt32)

@[extern "leanswe_fs_lstat_at"]
private opaque rawLstatAt : UInt64 → @& String → IO (UInt8 × UInt64 × UInt32 × Int × UInt32 × Int × UInt32)

@[extern "leanswe_fs_read_dir_at"]
private opaque rawReadDirAt : UInt64 → @& String → IO (Array String)

@[extern "leanswe_fs_create_dir_at"]
private opaque rawCreateDirAt : UInt64 → @& String → IO Unit

@[extern "leanswe_fs_read_regular_at"]
private opaque rawReadRegularAt : UInt64 → @& String → IO ByteArray

@[extern "leanswe_fs_create_file_at"]
private opaque rawCreateFileAt : UInt64 → @& String → @& ByteArray → IO Unit

@[extern "leanswe_fs_rename_at"]
private opaque rawRenameAt : UInt64 → @& String → UInt64 → @& String → IO Unit

@[extern "leanswe_fs_unlink_at"]
private opaque rawUnlinkAt : UInt64 → @& String → Bool → IO Unit

@[extern "leanswe_fs_symlink_at"]
private opaque rawSymlinkAt : @& String → UInt64 → @& String → IO Unit

@[extern "leanswe_fs_acquire_lock_at"]
private opaque rawAcquireLockAt : UInt64 → @& String → UInt8 → Bool → Bool → IO (UInt8 × UInt64 × UInt32)

@[extern "leanswe_fs_fresh_temp_nonce"]
private opaque rawFreshTempNonce : IO UInt64

private def posixDirOps : Internal.PosixDirOps :=
  { openDir := rawOpenDir
    openDirAt := rawOpenDirAt
    closeDir := rawCloseDir
    fstatDir := rawFstatDir
    lstatAt := rawLstatAt
    readDirAt := rawReadDirAt
    createDirAt := rawCreateDirAt
    readRegularAt := rawReadRegularAt
    createFileAt := rawCreateFileAt
    renameAt := rawRenameAt
    unlinkAt := rawUnlinkAt
    symlinkAt := rawSymlinkAt
    acquireLockAt := rawAcquireLockAt
    releaseLock := rawReleaseLock
    freshTempNonce := rawFreshTempNonce }

/-- Default single-step directory-descriptor primitives backed by `c/fs_shim.c`. -/
def defaultDirOps : RawDirOps :=
  Internal.mkRawDirOps posixDirOps

/-- Open `rootPath` directory returning a pinned `DirHandle`. -/
@[inline] def openDir (rootPath : String) : IO (Except FsError DirHandle) :=
  defaultDirOps.openDir rootPath

/-- Open immediate child directory `name` under `dh` without following symlinks. -/
@[inline] def openDirAt (dh : DirHandle) (name : EntryName) : IO (Except FsError DirHandle) :=
  defaultDirOps.openDirAt dh name

/-- Close an open `DirHandle`. -/
@[inline] def closeDir (dh : DirHandle) : IO (Except FsError Unit) :=
  defaultDirOps.closeDir dh

/-- Inspect metadata of the open directory referenced by `dh` (`fstat`). -/
@[inline] def fstatDir (dh : DirHandle) : IO (Except FsError FileStat) :=
  defaultDirOps.fstatDir dh

/-- Inspect metadata of immediate child `name` under `dh` without following symlinks. -/
@[inline] def lstatAt (dh : DirHandle) (name : EntryName) : IO (Except FsError FileStat) :=
  defaultDirOps.lstatAt dh name

/-- List unsorted immediate entry names inside `dh` (excluding `.` and `..`). -/
@[inline] def readDirAt (dh : DirHandle) : IO (Except FsError (Array EntryName)) :=
  defaultDirOps.readDirAt dh

/-- Create immediate child directory `name` under `dh` (`0o755`). -/
@[inline] def createDirAt (dh : DirHandle) (name : EntryName) : IO (Except FsError Unit) :=
  defaultDirOps.createDirAt dh name

/-- Read entire regular file `name` under `dh` without following symlinks or blocking. -/
@[inline] def readRegularAt (dh : DirHandle) (name : EntryName) : IO (Except FsError ByteArray) :=
  defaultDirOps.readRegularAt dh name

/-- Atomically create a new regular file `name` under `dh` (`O_CREAT | O_EXCL | O_NOFOLLOW`, `0o644`). -/
@[inline] def createFileAt (dh : DirHandle) (name : EntryName) (bytes : ByteArray) : IO (Except FsError Unit) :=
  defaultDirOps.createFileAt dh name bytes

/-- Atomically rename `(srcDh, srcName)` to `(dstDh, dstName)`. -/
@[inline] def renameAt (srcDh : DirHandle) (srcName : EntryName) (dstDh : DirHandle) (dstName : EntryName) :
    IO (Except FsError Unit) :=
  defaultDirOps.renameAt srcDh srcName dstDh dstName

/-- Remove child entry (`isDir = false`) or empty child directory (`isDir = true`) under `dh`. -/
@[inline] def unlinkAt (dh : DirHandle) (name : EntryName) (isDir : Bool) : IO (Except FsError Unit) :=
  defaultDirOps.unlinkAt dh name isDir

/-- Create symbolic link `(target, linkDh, linkName)`. -/
@[inline] def symlinkAt (target : String) (linkDh : DirHandle) (linkName : EntryName) :
    IO (Except FsError Unit) :=
  defaultDirOps.symlinkAt target linkDh linkName

/-- Acquire an advisory `flock(2)` lock on child `name` under `dh` without following symlinks. -/
@[inline] def acquireLockAt (dh : DirHandle) (name : EntryName) (mode : LockMode := .exclusive)
    (createIfMissing : Bool := true) (nonBlocking : Bool := false) : IO (Except FsError LockHandle) :=
  defaultDirOps.acquireLockAt dh name mode createIfMissing nonBlocking

/-- Generate a short target-independent temporary sibling `EntryName`. -/
@[inline] def freshTempName : IO EntryName :=
  defaultDirOps.freshTempName

end LeanSwe.Fs.Raw
