import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.Fs.Types

/-!
Internal capability record shapes shared across `LeanSwe.Fs.Impl`,
`LeanSwe.Fs.SysBridge`, `LeanSwe.Fs.Interface`, and `LeanSwe.Fs.Model`.
-/

namespace LeanSwe.Fs.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs

/-- Minimal single-step non-lock filesystem primitives parameterized over effect monad `m`. -/
structure NonLockFsOpsM (m : Type → Type) where
  /-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
  mapRawError : FsRawError → FsError
  /-- Inspect metadata (`follow = true` follows symlinks; `false` inspects links). -/
  stat : Bool → String → m (Except FsError FileStat)
  /-- List immediate entry names inside a directory. -/
  readDir : String → m (Except FsError (Array String))
  /-- Create a single directory (`0o777` subject to process `umask`), failing if parent is absent or path exists. -/
  createDir : String → m (Except FsError Unit)
  /-- Remove an empty directory. -/
  removeDir : String → m (Except FsError Unit)
  /-- Remove a file or symbolic link. -/
  unlinkFile : String → m (Except FsError Unit)
  /-- Read entire binary file (regular files only; rejects directories, FIFOs, and special files). -/
  readBytes : String → m (Except FsError ByteArray)
  /-- Write or overwrite binary file (`0o666` subject to process `umask` when created). -/
  writeBytes : String → ByteArray → m (Except FsError Unit)
  /-- Atomically create a new regular file without following symlinks (`O_CREAT | O_EXCL | O_NOFOLLOW`, `0o644` subject to process `umask`), failing with `.alreadyExists` if any entry exists. -/
  createFileNew : String → ByteArray → m (Except FsError Unit)
  /-- Append UTF-8 text to a file, creating it if absent (`0o666` subject to process `umask`). -/
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

/-- Minimal single-step filesystem primitives parameterized over effect monad `m` and lock handle type `lockH`. -/
structure RawFsOpsM (m : Type → Type) (lockH : Type) extends NonLockFsOpsM m where
  /-- Open `path` and acquire an advisory `flock(2)` lock (`shared` or `exclusive`, `0o644` subject to process `umask` when created). -/
  acquireLock : String → LockMode → Bool → Bool → m (Except FsError lockH)
  /-- Unlock and close an acquired lock handle. -/
  releaseLock : lockH → m (Except FsError Unit)

instance {m : Type → Type} {lockH : Type} : CoeOut (RawFsOpsM m lockH) (NonLockFsOpsM m) where
  coe := RawFsOpsM.toNonLockFsOpsM

/-- Scoped single-step filesystem primitive bundle replacing raw `acquireLock`/`releaseLock` with bracketed lock operations (no exposed handle parameter). -/
structure ScopedRawFsOpsM (m : Type → Type) extends NonLockFsOpsM m where
  /-- Acquire an advisory `flock`, execute `action`, and release the lock on exit. -/
  withFileLock : {α : Type} → String → LockMode → Bool → m (Except FsError α) → m (Except FsError α)
  /-- Non-blocking `withFileLock`, returning `.ok none` without running `action` when blocked. -/
  tryWithFileLock :
    {α : Type} → String → LockMode → Bool → m (Except FsError α) → m (Except FsError (Option α))

/-- Single-step directory-descriptor (`*at`) primitives refusing symlinks, parameterized over effect monad `m` and handle types `dirH`, `lockH`. -/
structure RawDirOpsM (m : Type → Type) (dirH : Type) (lockH : Type) where
  /-- Open `root` directory (`O_RDONLY | O_DIRECTORY | O_CLOEXEC`) returning a pinned directory handle. -/
  openDir : String → m (Except FsError dirH)
  /-- Open immediate child directory `name` under `dh` without following symlinks (`O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC`). -/
  openDirAt : dirH → EntryName → m (Except FsError dirH)
  /-- Close an open directory handle. -/
  closeDir : dirH → m (Except FsError Unit)
  /-- Inspect metadata of the open directory referenced by `dh` (`fstat`). -/
  fstatDir : dirH → m (Except FsError FileStat)
  /-- Inspect metadata of immediate child `name` under `dh` without following symlinks (`fstatat(..., AT_SYMLINK_NOFOLLOW)`). -/
  lstatAt : dirH → EntryName → m (Except FsError FileStat)
  /-- List unsorted immediate entry names inside `dh` (excluding `.` and `..`). -/
  readDirAt : dirH → m (Except FsError (Array EntryName))
  /-- Create immediate child directory `name` under `dh` (`0o755` subject to process `umask`). -/
  createDirAt : dirH → EntryName → m (Except FsError Unit)
  /-- Read entire regular file `name` under `dh` without following symlinks or blocking on special files. -/
  readRegularAt : dirH → EntryName → m (Except FsError ByteArray)
  /-- Atomically create a new regular file `name` under `dh` (`O_CREAT | O_EXCL | O_NOFOLLOW`, `0o644` subject to process `umask`). -/
  createFileAt : dirH → EntryName → ByteArray → m (Except FsError Unit)
  /-- Atomically rename `(srcDh, srcName)` to `(dstDh, dstName)` (`renameat`). -/
  renameAt : dirH → EntryName → dirH → EntryName → m (Except FsError Unit)
  /-- Remove child entry (`isDir = false`) or empty child directory (`isDir = true` via `AT_REMOVEDIR`) under `dh`. -/
  unlinkAt : dirH → EntryName → Bool → m (Except FsError Unit)
  /-- Create symbolic link `(target, linkDh, linkName)` (`symlinkat`). -/
  symlinkAt : String → dirH → EntryName → m (Except FsError Unit)
  /-- Open child `name` under `dh` without following symlinks and acquire an advisory `flock(2)` lock (`0o644` if created). -/
  acquireLockAt : dirH → EntryName → LockMode → Bool → Bool → m (Except FsError lockH)
  /-- Unlock and close an acquired lock handle. -/
  releaseLock : lockH → m (Except FsError Unit)
  /-- Generate a short target-independent temporary sibling `EntryName` (such as `.t.<nonce>`). -/
  freshTempName : m EntryName

/-- Canonical lower-layer syscall capability bundle for `LeanSwe.Fs` over `LinuxSyscall.Files` and `LinuxSyscall.TimeRand`. -/
structure FsSysCapsM (m : Type → Type) where
  /-- Verified `LinuxSyscall.Files` syscall bundle over `RawFd`. -/
  files : FilesOpsM m RawFd
  /-- Verified `LinuxSyscall.TimeRand` syscall bundle for stateless temp-nonce generation. -/
  timeRand : TimeRand.TimeRandOpsM m

end LeanSwe.Fs.Internal
