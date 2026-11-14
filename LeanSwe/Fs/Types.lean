/-!
# Fs Package Types

Public data structs, error enums, and `FsApi` bundle for `LeanSwe.Fs`.
Kept free of OS and implementation internals so specifications in `SpecTests`
depend only on this module.
-/

namespace LeanSwe.Fs

/-- Classification of filesystem and path errors modeled after Python `OSError` subclasses. -/
inductive FsErrorKind where
  /-- Target path or parent directory does not exist (`FileNotFoundError`). -/
  | notFound
  /-- Target path already exists (`FileExistsError`). -/
  | alreadyExists
  /-- Insufficient permissions or disallowed operation (`PermissionError`). -/
  | permissionDenied
  /-- Expected a regular file or non-directory, found a directory (`IsADirectoryError`). -/
  | isADirectory
  /-- Expected a directory, found a non-directory (`NotADirectoryError`). -/
  | notADirectory
  /-- Directory is not empty on `rmdir` (`ENOTEMPTY`). -/
  | notEmpty
  /-- Invalid path, suffix, filename, glob pattern, or encoding (`ValueError` / `EINVAL`). -/
  | invalidInput
  /-- Operation not supported on the current platform or filesystem. -/
  | unsupported
  /-- Other OS-level I/O failure (`OSError`). -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Typed filesystem error returned by `LeanSwe.Fs` operations. -/
structure FsError where
  /-- Machine-checkable error category. -/
  kind : FsErrorKind
  /-- Path associated with the error, when available. -/
  path : Option String := none
  /-- Underlying OS `errno` code, when available. -/
  errnoCode : Option UInt32 := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Directory entry file type returned by `stat` and `lstat`. -/
inductive EntryKind where
  /-- Regular file. -/
  | file
  /-- Directory. -/
  | dir
  /-- Symbolic link (visible under `lstat`). -/
  | symlink
  /-- Socket, FIFO, device, or other special entry. -/
  | other
  deriving Repr, BEq, DecidableEq

/-- File status metadata modeled after Python `os.stat_result`. -/
structure FileStat where
  /-- Kind of filesystem entry. -/
  kind : EntryKind
  /-- Size in bytes. -/
  byteSize : Nat
  /-- POSIX permission bits (`st_mode & 0o7777`). -/
  mode : Nat
  /-- Last modification timestamp (seconds). -/
  modifiedSec : Int
  /-- Last modification timestamp (nanoseconds). -/
  modifiedNsec : Nat
  /-- Last access timestamp (seconds). -/
  accessedSec : Int
  /-- Last access timestamp (nanoseconds). -/
  accessedNsec : Nat
  deriving Repr, BEq, DecidableEq

/-- Single yielded directory node from `walk` (analogous to Python `os.walk` triples). -/
structure WalkEntry where
  /-- Directory path relative to walk root (`"."` for the walk root itself). -/
  root : String
  /-- Sorted immediate child directory names. -/
  dirs : Array String
  /-- Sorted immediate child non-directory entry names. -/
  files : Array String
  deriving Repr, BEq, DecidableEq

/-- Pure representation of raw OS error inputs for total error-mapping specs. -/
inductive FsRawError where
  /-- Path or parent directory missing (`ENOENT`). -/
  | noFileOrDirectory (path : String) (errno : UInt32) (detail : String)
  /-- Destination already exists (`EEXIST`). -/
  | alreadyExists (path? : Option String) (errno : UInt32) (detail : String)
  /-- Permission denied (`EACCES` / `EPERM`). -/
  | permissionDenied (path? : Option String) (errno : UInt32) (detail : String)
  /-- Inappropriate file type (`EISDIR` / `ENOTDIR` / `ENOTEMPTY`). -/
  | inappropriateType (path? : Option String) (errno : UInt32) (detail : String)
  /-- Invalid argument (`EINVAL` / `ENAMETOOLONG`). -/
  | invalidArgument (path? : Option String) (errno : UInt32) (detail : String)
  /-- Unsupported platform operation. -/
  | unsupportedOperation (errno : UInt32) (detail : String)
  /-- Generic numeric OS error. -/
  | otherError (errno : UInt32) (detail : String)
  /-- Generic user-constructed error string. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- Public operations exported by `LeanSwe.Fs`, modeled after Python `pathlib`/`os`/`shutil`. -/
structure FsApi where
  /-- Join two paths using `/` (`Path.joinpath`). -/
  join : String → String → String
  /-- Join an array of path segments left-to-right. -/
  joinMany : Array String → String
  /-- Lexically normalize `.` and `..` segments and redundant `/` separators (`os.path.normpath`). -/
  normPath : String → String
  /-- Return parent directory path, or `none` when at root or single component. -/
  parent : String → Option String
  /-- Return final path component name, if present. -/
  name : String → Option String
  /-- Return final path component without its last suffix (`Path.stem`). -/
  stem : String → Option String
  /-- Return final `.ext` suffix of filename (`Path.suffix`), or `""` when none. -/
  suffix : String → String
  /-- Return all `.ext` suffixes of filename (`Path.suffixes`). -/
  suffixes : String → Array String
  /-- Replace the final path component (`Path.with_name`). -/
  withName : String → String → Except FsError String
  /-- Replace or strip the last suffix (`Path.with_suffix`). -/
  withSuffix : String → String → Except FsError String
  /-- Return `true` iff `path` begins with `/`. -/
  isAbsolute : String → Bool
  /-- Compute lexical path of `path` relative to `base` (`Path.relative_to`). -/
  relativeTo : String → String → Except FsError String
  /-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
  mapRawError : FsRawError → FsError
  /-- Read entire UTF-8 text file (`Path.read_text`). -/
  readText : String → IO (Except FsError String)
  /-- Write or overwrite UTF-8 text file (`Path.write_text`). -/
  writeText : String → String → IO (Except FsError Unit)
  /-- Append UTF-8 text to file, creating it if absent. -/
  appendText : String → String → IO (Except FsError Unit)
  /-- Read entire binary file (`Path.read_bytes`). -/
  readBytes : String → IO (Except FsError ByteArray)
  /-- Write or overwrite binary file (`Path.write_bytes`). -/
  writeBytes : String → ByteArray → IO (Except FsError Unit)
  /-- Atomically write text via a sibling temporary file and `rename`. -/
  atomicWriteText : String → String → IO (Except FsError Unit)
  /-- Create empty file if missing (`Path.touch`). -/
  touch : String → Bool → IO (Except FsError Unit)
  /-- Create directory, optionally creating parents or succeeding if present (`Path.mkdir`). -/
  mkdir : String → Bool → Bool → IO (Except FsError Unit)
  /-- Remove file or symlink (`Path.unlink`). -/
  unlink : String → Bool → IO (Except FsError Unit)
  /-- Remove empty directory (`Path.rmdir`). -/
  rmdir : String → IO (Except FsError Unit)
  /-- Recursively delete directory tree (`shutil.rmtree`). -/
  rmtree : String → Bool → IO (Except FsError Unit)
  /-- Rename or replace file/directory (`os.replace`). -/
  rename : String → String → IO (Except FsError Unit)
  /-- Copy file contents (`shutil.copyfile`). -/
  copyFile : String → String → IO (Except FsError Unit)
  /-- Recursively copy directory tree (`shutil.copytree`). -/
  copyTree : String → String → Bool → IO (Except FsError Unit)
  /-- Check whether `path` exists, following symlinks (`Path.exists`). -/
  pathExists : String → IO (Except FsError Bool)
  /-- Check whether `path` refers to a regular file, following symlinks (`Path.is_file`). -/
  isFile : String → IO (Except FsError Bool)
  /-- Check whether `path` refers to a directory, following symlinks (`Path.is_dir`). -/
  isDir : String → IO (Except FsError Bool)
  /-- Check whether `path` itself is a symbolic link (`Path.is_symlink`). -/
  isSymlink : String → IO (Except FsError Bool)
  /-- Inspect metadata following symlinks (`os.stat`). -/
  stat : String → IO (Except FsError FileStat)
  /-- Inspect metadata without following symlinks (`os.lstat`). -/
  lstat : String → IO (Except FsError FileStat)
  /-- Set POSIX permission mode bits (`os.chmod`). -/
  chmod : String → Nat → IO (Except FsError Unit)
  /-- Create symbolic link at `linkPath` pointing to `target` (`os.symlink`). -/
  symlink : String → String → IO (Except FsError Unit)
  /-- Read symbolic link target (`os.readlink`). -/
  readLink : String → IO (Except FsError String)
  /-- Resolve symlinks and return canonical absolute path (`Path.resolve`). -/
  resolve : String → IO (Except FsError String)
  /-- Return current working directory (`os.getcwd`). -/
  cwd : IO (Except FsError String)
  /-- Return sorted immediate child names in directory (`os.listdir`). -/
  listDir : String → IO (Except FsError (Array String))
  /-- Top-down directory walk yielding sorted children (`os.walk`). -/
  walk : String → IO (Except FsError (Array WalkEntry))
  /-- Find sorted relative paths under `root` matching glob `pattern` (`Path.glob`). -/
  glob : String → String → IO (Except FsError (Array String))
  /-- Recursively match glob `pattern` under `root` (`Path.rglob`). -/
  rglob : String → String → IO (Except FsError (Array String))

end LeanSwe.Fs
