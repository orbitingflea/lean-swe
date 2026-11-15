namespace LeanSwe.Fs.Raw

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
  /-- Non-blocking `flock` would block because a conflicting lock is held (`EWOULDBLOCK` / `EAGAIN`). -/
  | wouldBlock
  /-- Other OS-level I/O failure (`OSError`). -/
  | ioError
  deriving Repr, BEq, DecidableEq

/-- Advisory `flock(2)` lock mode. -/
inductive LockMode where
  /-- Shared (read) advisory lock (`LOCK_SH`). -/
  | shared
  /-- Exclusive (write) advisory lock (`LOCK_EX`). -/
  | exclusive
  deriving Repr, BEq, DecidableEq

/-- Opaque handle to an open file descriptor holding an advisory `flock(2)` lock. -/
structure LockHandle where
  /-- Opaque C slot-table or VFS lock identifier managed by `RawFsOpsM`. -/
  handleId : Nat
  /-- Target lock file path passed to `acquireLock`. -/
  path : String
  /-- Advisory lock mode held by this handle. -/
  mode : LockMode
  deriving Repr, BEq, DecidableEq

/-- Typed filesystem error returned by `LeanSwe.Fs.Raw` and `LeanSwe.Fs` operations. -/
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
  /-- Non-blocking `flock` contended (`EWOULDBLOCK` / `EAGAIN`). -/
  | wouldBlock (path? : Option String) (errno : UInt32) (detail : String)
  /-- Generic numeric OS error. -/
  | otherError (errno : UInt32) (detail : String)
  /-- Generic user-constructed error string. -/
  | userError (detail : String)
  deriving Repr, BEq, DecidableEq

/-- Minimal single-step filesystem primitives parameterized over effect monad `m`. -/
structure RawFsOpsM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
  mapRawError : FsRawError → FsError
  /-- Inspect metadata (`follow = true` follows symlinks; `false` inspects links). -/
  stat : Bool → String → m (Except FsError FileStat)
  /-- List immediate entry names inside a directory. -/
  readDir : String → m (Except FsError (Array String))
  /-- Create a single directory, failing if parent is absent or path exists. -/
  createDir : String → m (Except FsError Unit)
  /-- Remove an empty directory. -/
  removeDir : String → m (Except FsError Unit)
  /-- Remove a file or symbolic link. -/
  unlinkFile : String → m (Except FsError Unit)
  /-- Read entire binary file (regular files only; rejects directories, FIFOs, and special files). -/
  readBytes : String → m (Except FsError ByteArray)
  /-- Write or overwrite binary file. -/
  writeBytes : String → ByteArray → m (Except FsError Unit)
  /-- Atomically create a new regular file without following symlinks (`O_CREAT | O_EXCL | O_NOFOLLOW`), failing with `.alreadyExists` if any entry exists. -/
  createFileNew : String → ByteArray → m (Except FsError Unit)
  /-- Append UTF-8 text to a file, creating it if absent. -/
  appendText : String → String → m (Except FsError Unit)
  /-- Rename or replace a file or directory. -/
  rename : String → String → m (Except FsError Unit)
  /-- Set POSIX permission mode bits (`chmod`). -/
  chmod : String → Nat → m (Except FsError Unit)
  /-- Create symbolic link `(target, linkPath)`. -/
  symlink : String → String → m (Except FsError Unit)
  /-- Read symbolic link target path. -/
  readLink : String → m (Except FsError String)
  /-- Resolve canonical absolute path. -/
  realPath : String → m (Except FsError String)
  /-- Return current working directory. -/
  cwd : m (Except FsError String)
  /-- Return a monotonic nonce for temporary sibling filenames. -/
  monotonicNonce : m Nat
  /-- Open `path` and acquire an advisory `flock(2)` lock (`shared` or `exclusive`). -/
  acquireLock : String → LockMode → Bool → Bool → m (Except FsError LockHandle)
  /-- Unlock and close an acquired `LockHandle`. -/
  releaseLock : LockHandle → m (Except FsError Unit)

/-- Concrete `IO` thin-wrapper API bundle exported by `LeanSwe.Fs.Raw`. -/
abbrev RawFsOps := RawFsOpsM IO

end LeanSwe.Fs.Raw
