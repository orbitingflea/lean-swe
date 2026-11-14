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

private def posixRawOps : Internal.PosixRawOps :=
  { chmod := rawChmod
    symlink := rawSymlink
    readLink := rawReadLink
    statMode := rawStatMode
    acquireLock := rawAcquireLock
    releaseLock := rawReleaseLock }

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

/-- Execute `f` with a fresh temporary directory cleaned up afterward. -/
@[inline] def withTempDir {α : Type} (f : String → IO (Except FsError α)) : IO (Except FsError α) :=
  Internal.withTempDir f

/-- Acquire an OS advisory file lock on `path`. -/
@[inline] def acquireLock (path : String) (mode : LockMode := .exclusive)
    (createIfMissing : Bool := true) (nonBlocking : Bool := false) : IO (Except FsError LockHandle) :=
  defaultOps.acquireLock path mode createIfMissing nonBlocking

/-- Release a previously acquired OS advisory file lock handle. -/
@[inline] def releaseLock (handle : LockHandle) : IO (Except FsError Unit) :=
  defaultOps.releaseLock handle

end LeanSwe.Fs.Raw
