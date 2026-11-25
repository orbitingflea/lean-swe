import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.Fs.Types
import LeanSwe.Fs.Model.HealthyStep
import LeanSwe.Fs.Impl
import LeanSwe.Fs.SysBridge

namespace LeanSwe.Fs

namespace Internal

/-- Build a generic `FsApiM m` directly over a `FsSysCapsM m` (`LinuxSyscall.Files` + `LinuxSyscall.TimeRand`) capability bundle. -/
def mkApiFromCapsM {m : Type → Type} [Monad m] [MonadFinally m]
    (caps : Model.FsSysCapsM m) : FsApiM m :=
  mkApiFromScopedRawRetryM
    (toScopedRawFsOpsM (SysBridge.mkRawFsOpsM caps.files (SysBridge.nextTimeRandNonce caps.timeRand)))

/-- Construct a `SubtreeOpenerM m` directly over a `FsSysCapsM m` (`LinuxSyscall.Files` + `LinuxSyscall.TimeRand`) capability bundle. -/
def mkSubtreeOpenerFromCapsM {m : Type → Type} [Monad m] [MonadFinally m]
    (caps : Model.FsSysCapsM m) : SubtreeOpenerM m :=
  mkSubtreeOpenerM (SysBridge.mkRawDirOpsM caps.files (SysBridge.nextTimeRandNonce caps.timeRand))

end Internal

/-- Default `SubtreeOpener` backed directly by `LinuxSyscall.Files.defaultOps` and `LinuxSyscall.TimeRand.defaultOps`. -/
def defaultOps : SubtreeOpener :=
  Internal.mkSubtreeOpenerFromCapsM
    { files := LinuxSyscall.Files.defaultOps
    , timeRand := LinuxSyscall.TimeRand.defaultOps }

/-- Default `FsApi` backed directly by `LinuxSyscall.Files.defaultOps` and `LinuxSyscall.TimeRand.defaultOps`. -/
def defaultApi : FsApi :=
  Internal.mkApiFromCapsM
    { files := LinuxSyscall.Files.defaultOps
    , timeRand := LinuxSyscall.TimeRand.defaultOps }

/-- Join two paths using `/` (`Path.joinpath`). -/
@[inline] def join (base sub : String) : String :=
  defaultApi.join base sub

/-- Join an array of path segments left-to-right. -/
@[inline] def joinMany (parts : Array String) : String :=
  defaultApi.joinMany parts

/-- Lexically normalize `.` and `..` segments and redundant `/` separators (`os.path.normpath`). -/
@[inline] def normPath (path : String) : String :=
  defaultApi.normPath path

/-- Return parent directory path, or `none` when at root or single component. -/
@[inline] def parent (path : String) : Option String :=
  defaultApi.parent path

/-- Return the final path component name, if present. -/
@[inline] def name (path : String) : Option String :=
  defaultApi.name path

/-- Return the final path component without its last suffix (`Path.stem`). -/
@[inline] def stem (path : String) : Option String :=
  defaultApi.stem path

/-- Return the final `.ext` suffix of filename, or `""` when none (`Path.suffix`). -/
@[inline] def suffix (path : String) : String :=
  defaultApi.suffix path

/-- Return all `.ext` suffixes of filename (`Path.suffixes`). -/
@[inline] def suffixes (path : String) : Array String :=
  defaultApi.suffixes path

/-- Replace the final path component (`Path.with_name`). -/
@[inline] def withName (path newName : String) : Except FsError String :=
  defaultApi.withName path newName

/-- Replace or strip the last suffix (`Path.with_suffix`). -/
@[inline] def withSuffix (path newSuffix : String) : Except FsError String :=
  defaultApi.withSuffix path newSuffix

/-- Return `true` iff `path` begins with `/`. -/
@[inline] def isAbsolute (path : String) : Bool :=
  defaultApi.isAbsolute path

/-- Compute lexical path of `path` relative to `base` (`Path.relative_to`). -/
@[inline] def relativeTo (path base : String) : Except FsError String :=
  defaultApi.relativeTo path base

/-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
@[inline] def mapRawError (err : FsRawError) : FsError :=
  defaultApi.mapRawError err

/-- Read entire UTF-8 text file (`Path.read_text`). -/
@[inline] def readText (path : String) : IO (Except FsError String) :=
  defaultApi.readText path

/-- Write or overwrite UTF-8 text file (`Path.write_text`). -/
@[inline] def writeText (path content : String) : IO (Except FsError Unit) :=
  defaultApi.writeText path content

/-- Append UTF-8 text to file, creating it if absent. -/
@[inline] def appendText (path content : String) : IO (Except FsError Unit) :=
  defaultApi.appendText path content

/-- Read entire binary file (`Path.read_bytes`). -/
@[inline] def readBytes (path : String) : IO (Except FsError ByteArray) :=
  defaultApi.readBytes path

/-- Write or overwrite binary file (`Path.write_bytes`). -/
@[inline] def writeBytes (path : String) (content : ByteArray) : IO (Except FsError Unit) :=
  defaultApi.writeBytes path content

/-- Atomically write binary bytes via a sibling exclusive temporary file and `rename`. -/
@[inline] def atomicWriteBytes (path : String) (content : ByteArray) : IO (Except FsError Unit) :=
  defaultApi.atomicWriteBytes path content

/-- Atomically write text via a sibling temporary file and `rename`. -/
@[inline] def atomicWriteText (path content : String) : IO (Except FsError Unit) :=
  defaultApi.atomicWriteText path content

/-- Create an empty file if absent, failing if `existOk = false` and present (`Path.touch`). -/
@[inline] def touch (path : String) (existOk : Bool := true) : IO (Except FsError Unit) :=
  defaultApi.touch path existOk

/-- Create a directory (`Path.mkdir(parents=..., exist_ok=...)`). -/
@[inline] def mkdir (path : String) (parents : Bool := false) (existOk : Bool := false) :
    IO (Except FsError Unit) :=
  defaultApi.mkdir path parents existOk

/-- Remove a file or symbolic link (`Path.unlink(missing_ok=...)`). -/
@[inline] def unlink (path : String) (missingOk : Bool := false) : IO (Except FsError Unit) :=
  defaultApi.unlink path missingOk

/-- Remove an empty directory (`Path.rmdir`). -/
@[inline] def rmdir (path : String) : IO (Except FsError Unit) :=
  defaultApi.rmdir path

/-- Recursively delete a directory tree (`shutil.rmtree`). -/
@[inline] def rmtree (path : String) (ignoreMissing : Bool := false) : IO (Except FsError Unit) :=
  defaultApi.rmtree path ignoreMissing

/-- Rename or replace a file or directory (`os.replace`). -/
@[inline] def rename (src dst : String) : IO (Except FsError Unit) :=
  defaultApi.rename src dst

/-- Copy file contents from `src` to `dst` (`shutil.copyfile`). -/
@[inline] def copyFile (src dst : String) : IO (Except FsError Unit) :=
  defaultApi.copyFile src dst

/-- Recursively copy a directory tree (`shutil.copytree`). -/
@[inline] def copyTree (src dst : String) (dirsExistOk : Bool := false) :
    IO (Except FsError Unit) :=
  defaultApi.copyTree src dst dirsExistOk

/-- Check whether `path` exists, following symlinks (`Path.exists`). -/
@[inline] def pathExists (path : String) : IO (Except FsError Bool) :=
  defaultApi.pathExists path

/-- Check whether `path` refers to a regular file (`Path.is_file`). -/
@[inline] def isFile (path : String) : IO (Except FsError Bool) :=
  defaultApi.isFile path

/-- Check whether `path` refers to a directory (`Path.is_dir`). -/
@[inline] def isDir (path : String) : IO (Except FsError Bool) :=
  defaultApi.isDir path

/-- Check whether `path` itself is a symbolic link (`Path.is_symlink`). -/
@[inline] def isSymlink (path : String) : IO (Except FsError Bool) :=
  defaultApi.isSymlink path

/-- Inspect metadata following symlinks (`os.stat`). -/
@[inline] def stat (path : String) : IO (Except FsError FileStat) :=
  defaultApi.stat path

/-- Inspect metadata without following symlinks (`os.lstat`). -/
@[inline] def lstat (path : String) : IO (Except FsError FileStat) :=
  defaultApi.lstat path

/-- Set POSIX permission mode bits (`os.chmod`). -/
@[inline] def chmod (path : String) (mode : Nat) : IO (Except FsError Unit) :=
  defaultApi.chmod path mode

/-- Create symbolic link at `linkPath` pointing to `target` (`os.symlink`). -/
@[inline] def symlink (target linkPath : String) : IO (Except FsError Unit) :=
  defaultApi.symlink target linkPath

/-- Read symbolic link target (`os.readlink`). -/
@[inline] def readLink (path : String) : IO (Except FsError String) :=
  defaultApi.readLink path

/-- Resolve symlinks and return canonical absolute path (`Path.resolve`). -/
@[inline] def resolve (path : String) : IO (Except FsError String) :=
  defaultApi.resolve path

/-- Return current working directory (`os.getcwd`). -/
@[inline] def cwd : IO (Except FsError String) :=
  defaultApi.cwd

/-- Return sorted immediate child names in directory (`os.listdir`). -/
@[inline] def listDir (path : String) : IO (Except FsError (Array String)) :=
  defaultApi.listDir path

/-- Top-down directory walk yielding sorted children (`os.walk`). -/
@[inline] def walk (root : String) : IO (Except FsError (Array WalkEntry)) :=
  defaultApi.walk root

/-- Find sorted relative paths under `root` matching glob `pattern` (`Path.glob`). -/
@[inline] def glob (root pattern : String) : IO (Except FsError (Array String)) :=
  defaultApi.glob root pattern

/-- Recursively match glob `pattern` under `root` (`Path.rglob`). -/
@[inline] def rglob (root pattern : String) : IO (Except FsError (Array String)) :=
  defaultApi.rglob root pattern

/-- Acquire an advisory `mode` lock on `path`, execute `action`, and always unlock/close afterward. -/
@[inline] def withFileLock {α : Type} (path : String) (mode : LockMode := .exclusive)
    (createIfMissing : Bool := true) (action : IO (Except FsError α)) : IO (Except FsError α) :=
  defaultApi.withFileLock path mode createIfMissing action

/-- Try a non-blocking `mode` advisory lock on `path`; returns `.ok none` if contended. -/
@[inline] def tryWithFileLock {α : Type} (path : String) (mode : LockMode := .exclusive)
    (createIfMissing : Bool := true) (action : IO (Except FsError α)) :
    IO (Except FsError (Option α)) :=
  defaultApi.tryWithFileLock path mode createIfMissing action

/-- Open `rootPath` once as a confined directory handle, execute `action`, and always close the handle on exit. -/
@[inline] def withSubtree {α : Type} (rootPath : String)
    (action : Subtree → IO (Except FsError α)) : IO (Except FsError α) :=
  defaultOps.withSubtree rootPath action

end LeanSwe.Fs
