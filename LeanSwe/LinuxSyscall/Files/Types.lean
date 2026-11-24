import LeanSwe.LinuxSyscall.Common.Types

namespace LeanSwe.LinuxSyscall.Files

open LeanSwe.LinuxSyscall

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

/-- Portable symbolic file access mode (translated in C to `O_RDONLY` / `O_WRONLY` / `O_RDWR`). -/
inductive AccessMode where
  /-- Read-only access (`O_RDONLY`). -/
  | rdonly
  /-- Write-only access (`O_WRONLY`). -/
  | wronly
  /-- Read-write access (`O_RDWR`). -/
  | rdwr
  deriving Repr, DecidableEq, BEq

/-- Portable symbolic `openat` / `openat2` flags translated via host Linux `<fcntl.h>` constants. -/
structure OpenFlags where
  /-- File access mode (`O_RDONLY`, `O_WRONLY`, `O_RDWR`). -/
  access : AccessMode := .rdonly
  /-- Create file if it does not exist (`O_CREAT`). -/
  creat : Bool := false
  /-- Fail with `EEXIST` if file already exists when combined with `creat` (`O_EXCL`). -/
  excl : Bool := false
  /-- Truncate existing regular file to length `0` (`O_TRUNC`). -/
  trunc : Bool := false
  /-- Open in append mode (`O_APPEND`). -/
  append : Bool := false
  /-- Do not follow a trailing symbolic link (`O_NOFOLLOW`). -/
  nofollow : Bool := false
  /-- Fail with `ENOTDIR` if target is not a directory (`O_DIRECTORY`). -/
  directory : Bool := false
  /-- Open in non-blocking mode (`O_NONBLOCK`). -/
  nonblock : Bool := false
  /-- Set close-on-exec descriptor flag (`O_CLOEXEC`). -/
  cloexec : Bool := true
  /-- Do not assign a controlling terminal if target is a TTY device (`O_NOCTTY`). -/
  noctty : Bool := false
  /-- Obtain a path-only reference descriptor (`O_PATH`) without opening the underlying file or checking file read/write perms. -/
  path : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `OpenFlags` into a portable bitmask decoded by `files_shim.c`. -/
def OpenFlags.toBits (f : OpenFlags) : UInt32 :=
  let acc : UInt32 := match f.access with
    | .rdonly => 0
    | .wronly => 1
    | .rdwr => 2
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  acc ||| bit f.creat 2 ||| bit f.excl 3 ||| bit f.trunc 4 ||| bit f.append 5
      ||| bit f.nofollow 6 ||| bit f.directory 7 ||| bit f.nonblock 8 ||| bit f.cloexec 9
      ||| bit f.noctty 10 ||| bit f.path 11

/-- Portable symbolic `openat2` path-resolution flags (`struct open_how.resolve`). -/
structure ResolveFlags where
  /-- Disallow crossing mount points (`RESOLVE_NO_XDEV`). -/
  noXdev : Bool := false
  /-- Disallow traversal of magic links such as `/proc/*/fd/*` (`RESOLVE_NO_MAGICLINKS`). -/
  noMagiclinks : Bool := false
  /-- Disallow traversal of any symbolic link (`RESOLVE_NO_SYMLINKS`). -/
  noSymlinks : Bool := false
  /-- Restrict resolution strictly beneath `dirfd` (`RESOLVE_BENEATH`). -/
  beneath : Bool := false
  /-- Treat `dirfd` as the filesystem root during resolution (`RESOLVE_IN_ROOT`). -/
  inRoot : Bool := false
  /-- Fail with `EAGAIN` unless resolution can complete from kernel caches (`RESOLVE_CACHED`). -/
  cached : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `ResolveFlags` into a portable bitmask decoded by `files_shim.c`. -/
def ResolveFlags.toBits (r : ResolveFlags) : UInt64 :=
  let bit (b : Bool) (shift : UInt64) : UInt64 := if b then (1 <<< shift) else 0
  bit r.noXdev 0 ||| bit r.noMagiclinks 1 ||| bit r.noSymlinks 2
    ||| bit r.beneath 3 ||| bit r.inRoot 4 ||| bit r.cached 5

/-- Structured arguments for Linux `openat2(2)` (`struct open_how`). -/
structure OpenHow where
  /-- Symbolic open flags. -/
  flags : OpenFlags := {}
  /-- File mode bits (must be `0` unless `flags.creat` is `true` on Linux `openat2`). -/
  mode : Mode := 0
  /-- Symbolic `RESOLVE_*` constraints. -/
  resolve : ResolveFlags := {}
  deriving Repr, DecidableEq, BEq

/-- Portable `*at` lookup flags (`AT_SYMLINK_NOFOLLOW`, `AT_EMPTY_PATH`, `AT_EACCESS`; `faccessat` passes non-zero flags via Linux `faccessat2(2)`, `__NR_faccessat2 = 439`). -/
structure AtFlags where
  /-- Inspect the symbolic link itself rather than following it (`AT_SYMLINK_NOFOLLOW`). -/
  symlinkNofollow : Bool := false
  /-- Operate on `dirfd` itself when `path` is empty (`AT_EMPTY_PATH`). -/
  emptyPath : Bool := false
  /-- Use effective UID/GID for `faccessat2` (`AT_EACCESS`; rejected with `EINVAL` by `fstatat`). -/
  eaccess : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `AtFlags` into a portable bitmask decoded by `files_shim.c`. -/
def AtFlags.toBits (f : AtFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.symlinkNofollow 0 ||| bit f.emptyPath 1 ||| bit f.eaccess 2

/-- Portable access permission mask for `faccessat(2)` (all `false` encodes `F_OK`). -/
structure AccessModeMask where
  /-- Check read permission (`R_OK`). -/
  read : Bool := false
  /-- Check write permission (`W_OK`). -/
  write : Bool := false
  /-- Check execute/search permission (`X_OK`). -/
  exec : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `AccessModeMask` into a portable bitmask decoded by `files_shim.c` (`0` = `F_OK`). -/
def AccessModeMask.toBits (m : AccessModeMask) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit m.read 0 ||| bit m.write 1 ||| bit m.exec 2

/-- Portable flags for Linux `renameat2(2)`. -/
structure RenameFlags where
  /-- Do not overwrite an existing target (`RENAME_NOREPLACE`). -/
  noreplace : Bool := false
  /-- Atomically exchange source and destination (`RENAME_EXCHANGE`). -/
  exchange : Bool := false
  /-- Create a whiteout object at source (`RENAME_WHITEOUT`). -/
  whiteout : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Encode `RenameFlags` into a portable bitmask decoded by `files_shim.c`. -/
def RenameFlags.toBits (f : RenameFlags) : UInt32 :=
  let bit (b : Bool) (shift : UInt32) : UInt32 := if b then (1 <<< shift) else 0
  bit f.noreplace 0 ||| bit f.exchange 1 ||| bit f.whiteout 2

/-- File kind decoded from `struct stat.st_mode & S_IFMT`. -/
inductive FileKind where
  /-- Regular file (`S_IFREG`). -/
  | reg
  /-- Directory (`S_IFDIR`). -/
  | dir
  /-- Symbolic link (`S_IFLNK`). -/
  | symlink
  /-- Named pipe (`S_IFIFO`). -/
  | fifo
  /-- Unix domain socket (`S_IFSOCK`). -/
  | socket
  /-- Character device (`S_IFCHR`). -/
  | charDev
  /-- Block device (`S_IFBLK`). -/
  | blockDev
  /-- Any other kernel file type. -/
  | other
  deriving Repr, DecidableEq, BEq

/-- Architecture-independent metadata decoded from `struct stat` (`fstat` / `fstatat`). -/
structure StatInfo where
  /-- Decoded file kind. -/
  kind : FileKind
  /-- File size in bytes (`st_size`). -/
  size : Nat
  /-- Lower 12 permission and special mode bits (`st_mode & 0o7777`). -/
  mode : Mode
  /-- Inode number (`st_ino`). -/
  ino : UInt64
  /-- Device ID (`st_dev`). -/
  dev : UInt64
  /-- Hard-link count (`st_nlink`). -/
  nlink : Nat
  /-- Modification time seconds (`st_mtim.tv_sec`). -/
  mtimeSec : Int
  /-- Modification time nanoseconds (`st_mtim.tv_nsec`). -/
  mtimeNsec : UInt32
  /-- Access time seconds (`st_atim.tv_sec`). -/
  atimeSec : Int
  /-- Access time nanoseconds (`st_atim.tv_nsec`). -/
  atimeNsec : UInt32
  deriving Repr, DecidableEq, BEq

/-- Raw C-ABI tuple returned by `leanswe_sys_fstat` and `leanswe_sys_fstatat`. -/
abbrev RawStatTuple :=
  UInt8 × UInt64 × UInt32 × UInt64 × UInt64 × UInt64 × Int × UInt32 × Int × UInt32

/-- Decode a `RawStatTuple` returned by `files_shim.c` into `StatInfo`. -/
def StatInfo.ofRawTuple (t : RawStatTuple) : StatInfo :=
  let (k, sz, m, ino, dev, nlink, mSec, mNsec, aSec, aNsec) := t
  let kind := match k.toNat with
    | 0 => .reg
    | 1 => .dir
    | 2 => .symlink
    | 3 => .fifo
    | 4 => .socket
    | 5 => .charDev
    | 6 => .blockDev
    | _ => .other
  { kind, size := sz.toNat, mode := m &&& 0o7777, ino, dev, nlink := nlink.toNat,
    mtimeSec := mSec, mtimeNsec := mNsec, atimeSec := aSec, atimeNsec := aNsec }

/-- Portable advisory lock operation for `flock(2)`. -/
inductive FlockOp where
  /-- Acquire a shared lock (`LOCK_SH`, optionally with `LOCK_NB`). -/
  | shared (nonBlocking : Bool := false)
  /-- Acquire an exclusive lock (`LOCK_EX`, optionally with `LOCK_NB`). -/
  | exclusive (nonBlocking : Bool := false)
  /-- Release an existing lock (`LOCK_UN`). -/
  | unlock
  deriving Repr, DecidableEq, BEq

/-- Encode `FlockOp` into a portable bitmask decoded by `files_shim.c`. -/
def FlockOp.toBits : FlockOp → UInt32
  | .shared false => 1
  | .shared true => 1 ||| 8
  | .exclusive false => 2
  | .exclusive true => 2 ||| 8
  | .unlock => 4

/-- Curated portable commands for `fcntl(2)`. -/
inductive FcntlCmd where
  /-- Read open file status flags (`F_GETFL`, decoded specifically to portable `(access, append, nonblock)` bits `0..1`, `5`, `8`). -/
  | getFl
  /-- Update mutable open file status flags (`F_SETFL`, `O_NONBLOCK` and `O_APPEND`). -/
  | setFl (nonblock : Bool) (append : Bool)
  /-- Read file descriptor flags (`F_GETFD`, bit 0 = `FD_CLOEXEC`). -/
  | getFd
  /-- Set file descriptor flags (`F_SETFD`, `FD_CLOEXEC`). -/
  | setFd (cloexec : Bool)
  /-- Add `memfd` seals (`F_ADD_SEALS`). -/
  | addSeals (seals : UInt32)
  /-- Query `memfd` seals (`F_GET_SEALS`). -/
  | getSeals
  deriving Repr, DecidableEq, BEq

/-- Seek origin for `lseek(2)`. -/
inductive SeekWhence where
  /-- Set file offset to `offset` (`SEEK_SET`). -/
  | seekSet
  /-- Set file offset to current position plus `offset` (`SEEK_CUR`). -/
  | seekCur
  /-- Set file offset to file size plus `offset` (`SEEK_END`). -/
  | seekEnd
  deriving Repr, DecidableEq, BEq

/-- Encode `SeekWhence` into a portable tag decoded by `files_shim.c`. -/
def SeekWhence.toRaw : SeekWhence → UInt32
  | .seekSet => 0
  | .seekCur => 1
  | .seekEnd => 2

/-- Standard file descriptor slot for `dupStdio`. -/
inductive StdioFd where
  /-- Standard input descriptor (`0`). -/
  | stdin
  /-- Standard output descriptor (`1`). -/
  | stdout
  /-- Standard error descriptor (`2`). -/
  | stderr
  deriving Repr, DecidableEq, BEq

/-- Encode `StdioFd` into its POSIX descriptor slot (`0`, `1`, `2`). -/
def StdioFd.toRaw : StdioFd → UInt32
  | .stdin => 0
  | .stdout => 1
  | .stderr => 2

/-- Encode `FcntlCmd` into `(cmdTag, arg)` for `leanswe_sys_fcntl`. -/
def FcntlCmd.toRaw : FcntlCmd → UInt32 × UInt32
  | .getFl => (0, 0)
  | .setFl nb ap =>
    let arg : UInt32 := (if nb then 1 else 0) ||| (if ap then 2 else 0)
    (1, arg)
  | .getFd => (2, 0)
  | .setFd clo => (3, if clo then 1 else 0)
  | .addSeals seals => (4, seals)
  | .getSeals => (5, 0)

/-- Semantic classification of Linux file-syscall `Errno` outcomes for error-coverage auditing. -/
inductive FilesErrorKind where
  /-- Missing path component or empty path (`ENOENT`). -/
  | notFound
  /-- Bad, closed, or wrong-mode file descriptor (`EBADF`). -/
  | badFd
  /-- Invalid flag combination, embedded NUL, invalid argument, or boundary error (`EINVAL`, `ENAMETOOLONG`, `ERANGE`, `EXDEV`, `EOPNOTSUPP`, `ENOSYS`). -/
  | invalidArg
  /-- Entry conflict or type/directory state mismatch (`EEXIST`, `ENOTDIR`, `EISDIR`, `ENOTEMPTY`, `ELOOP`, `EBUSY`, `EAGAIN`). -/
  | stateConflict
  /-- Permission or read-only rejection (`EACCES`, `EPERM`, `EROFS`). -/
  | permissionDenied
  /-- Transient kernel, I/O, or resource exhaustion fault (`EINTR`, `EIO`, `ENOMEM`, `ENFILE`, `EMFILE`, `ENOSPC`, or other OS errno). -/
  | transientOrResource
  deriving Repr, DecidableEq, BEq

/-- Classify any Linux `Errno` into a `FilesErrorKind`. -/
def FilesErrorKind.ofErrno (e : Errno) : FilesErrorKind :=
  if e == Errno.ENOENT then .notFound
  else if e == Errno.EBADF then .badFd
  else if e == Errno.EINVAL || e == Errno.ENAMETOOLONG || e == Errno.ERANGE ||
      e == Errno.EXDEV || e == Errno.EOPNOTSUPP || e == Errno.ENOSYS then .invalidArg
  else if e == Errno.EEXIST || e == Errno.ENOTDIR || e == Errno.EISDIR ||
      e == Errno.ENOTEMPTY || e == Errno.ELOOP || e == Errno.EBUSY || e == Errno.EAGAIN then .stateConflict
  else if e == Errno.EACCES || e == Errno.EPERM || e == Errno.EROFS then .permissionDenied
  else .transientOrResource

/-- Monadic capability bundle for all 23 curated Linux `Files` syscalls, parameterized over monad `m` and descriptor type `fd`. -/
structure FilesOpsM (m : Type → Type) (fd : Type := RawFd) where
  /-- Open or create a file relative to `dir` (`AT_FDCWD` when `none`) via `openat(2)`. -/
  openat : Option fd → ByteArray → OpenFlags → Mode → m (Except Errno fd)
  /-- Open or create a file with strict `RESOLVE_*` constraints via `openat2(2)`. -/
  openat2 : Option fd → ByteArray → OpenHow → m (Except Errno fd)
  /-- Close an open file descriptor via `close(2)`. -/
  close : fd → m (Except Errno Unit)
  /-- Read up to `min maxBytes MAX_READ_BYTES` bytes via `read(2)`. -/
  read : fd → UInt32 → m (Except Errno ByteArray)
  /-- Write a non-empty prefix (or 0 for empty input) of `data` via `write(2)`. -/
  write : fd → ByteArray → m (Except Errno UInt32)
  /-- Query metadata of an open file descriptor via `fstat(2)`. -/
  fstat : fd → m (Except Errno StatInfo)
  /-- Query metadata of a path relative to `dir` via `newfstatat(2)` / `fstatat(2)`. -/
  fstatat : Option fd → ByteArray → AtFlags → m (Except Errno StatInfo)
  /-- Check access permissions of a path relative to `dir` via Linux `faccessat2(2)` (`__NR_faccessat2 = 439` on `x86_64` and `aarch64`, honoring `AtFlags`). -/
  faccessat : Option fd → ByteArray → AccessModeMask → AtFlags → m (Except Errno Unit)
  /-- Create a directory relative to `dir` via `mkdirat(2)`. -/
  mkdirat : Option fd → ByteArray → Mode → m (Except Errno Unit)
  /-- Remove a file/symlink (`removeDir = false`) or empty directory (`removeDir = true`) via `unlinkat(2)`. -/
  unlinkat : Option fd → ByteArray → Bool → m (Except Errno Unit)
  /-- Rename or exchange entries via `renameat2(2)`. -/
  renameat2 : Option fd → ByteArray → Option fd → ByteArray → RenameFlags → m (Except Errno Unit)
  /-- Create a symbolic link via `symlinkat(2)`. -/
  symlinkat : ByteArray → Option fd → ByteArray → m (Except Errno Unit)
  /-- Read raw symbolic link target bytes via `readlinkat(2)`. -/
  readlinkat : Option fd → ByteArray → UInt32 → m (Except Errno ByteArray)
  /-- Read raw `linux_dirent64` records from a directory descriptor via `getdents64(2)`. -/
  getdents64 : fd → UInt32 → m (Except Errno ByteArray)
  /-- Change file mode bits of a path relative to `dir` via `fchmodat(2)`. -/
  fchmodat : Option fd → ByteArray → Mode → m (Except Errno Unit)
  /-- Change file mode bits of an open file descriptor via `fchmod(2)`. -/
  fchmod : fd → Mode → m (Except Errno Unit)
  /-- Apply or remove an advisory lock on an open file descriptor via `flock(2)`. -/
  flock : fd → FlockOp → m (Except Errno Unit)
  /-- Manipulate open file descriptor or status flags/seals via `fcntl(2)`. -/
  fcntl : fd → FcntlCmd → m (Except Errno UInt32)
  /-- Synchronize an open file descriptor's state to storage via `fsync(2)`. -/
  fsync : fd → m (Except Errno Unit)
  /-- Return the current working directory byte path via `getcwd(2)`. -/
  getcwd : UInt32 → m (Except Errno ByteArray)
  /-- Reposition read/write file offset or directory cursor via `lseek(2)`. -/
  lseek : fd → Int64 → SeekWhence → m (Except Errno UInt64)
  /-- Reopen an open descriptor read-only with `O_CLOEXEC` via `/proc/thread-self/fd/%d` after procfs and inode checks. -/
  reopenReadOnly : fd → m (Except Errno fd)
  /-- Duplicate a standard descriptor slot (`0`/`1`/`2`) with `FD_CLOEXEC` (`>= 3`) via `fcntl(F_DUPFD_CLOEXEC, 3)`. -/
  dupStdio : StdioFd → m (Except Errno fd)

/-- Real-world `IO` specialization of `FilesOpsM` using ABA-safe `RawFd` handles. -/
abbrev FilesOps := FilesOpsM IO RawFd

/-- Logical handle identifier used by the relational world model and fuzzer traces. -/
abbrev HandleId := Nat

/-- One syscall request in a `Files` world-model trace (covers all 23 curated syscalls). -/
inductive FilesReq where
  /-- `openat(dir, path, flags, mode)`. -/
  | openat (dir : Option HandleId) (path : ByteArray) (flags : OpenFlags) (mode : Mode)
  /-- `openat2(dir, path, how)`. -/
  | openat2 (dir : Option HandleId) (path : ByteArray) (how : OpenHow)
  /-- `close(hid)`. -/
  | close (hid : HandleId)
  /-- `read(hid, maxBytes)`. -/
  | read (hid : HandleId) (maxBytes : UInt32)
  /-- `write(hid, data)`. -/
  | write (hid : HandleId) (data : ByteArray)
  /-- `fstat(hid)`. -/
  | fstat (hid : HandleId)
  /-- `fstatat(dir, path, flags)`. -/
  | fstatat (dir : Option HandleId) (path : ByteArray) (flags : AtFlags)
  /-- `faccessat(dir, path, mask, flags)`. -/
  | faccessat (dir : Option HandleId) (path : ByteArray) (mask : AccessModeMask) (flags : AtFlags)
  /-- `mkdirat(dir, path, mode)`. -/
  | mkdirat (dir : Option HandleId) (path : ByteArray) (mode : Mode)
  /-- `unlinkat(dir, path, removeDir)`. -/
  | unlinkat (dir : Option HandleId) (path : ByteArray) (removeDir : Bool)
  /-- `renameat2(oldDir, oldPath, newDir, newPath, flags)`. -/
  | renameat2 (oldDir : Option HandleId) (oldPath : ByteArray) (newDir : Option HandleId)
      (newPath : ByteArray) (flags : RenameFlags)
  /-- `symlinkat(target, dir, linkPath)`. -/
  | symlinkat (target : ByteArray) (dir : Option HandleId) (linkPath : ByteArray)
  /-- `readlinkat(dir, path, cap)`. -/
  | readlinkat (dir : Option HandleId) (path : ByteArray) (cap : UInt32)
  /-- `getdents64(hid, bufBytes)`. -/
  | getdents64 (hid : HandleId) (bufBytes : UInt32)
  /-- `fchmodat(dir, path, mode)`. -/
  | fchmodat (dir : Option HandleId) (path : ByteArray) (mode : Mode)
  /-- `fchmod(hid, mode)`. -/
  | fchmod (hid : HandleId) (mode : Mode)
  /-- `flock(hid, op)`. -/
  | flock (hid : HandleId) (op : FlockOp)
  /-- `fcntl(hid, cmd)`. -/
  | fcntl (hid : HandleId) (cmd : FcntlCmd)
  /-- `fsync(hid)`. -/
  | fsync (hid : HandleId)
  /-- `getcwd(cap)`. -/
  | getcwd (cap : UInt32)
  /-- `lseek(hid, offset, whence)`. -/
  | lseek (hid : HandleId) (offset : Int64) (whence : SeekWhence)
  /-- `reopenReadOnly(hid)`. -/
  | reopenReadOnly (hid : HandleId)
  /-- `dupStdio(slot)`. -/
  | dupStdio (slot : StdioFd)
  deriving Repr

/-- Raw kernel outcome observed for one `FilesReq`. -/
inductive FilesOutcome where
  /-- Descriptor-opening syscall succeeded and allocated `hid`. -/
  | opened (hid : HandleId)
  /-- Unit-returning syscall succeeded (`close`, `faccessat`, `mkdirat`, `unlinkat`, `renameat2`, `symlinkat`, `fchmodat`, `fchmod`, `flock`, `fsync`). -/
  | unit
  /-- Byte-returning syscall succeeded (`read`, `readlinkat`, `getdents64`, `getcwd`). -/
  | bytes (data : ByteArray)
  /-- `UInt32`-returning syscall succeeded (`write` byte count or `fcntl` return value). -/
  | u32 (val : UInt32)
  /-- `UInt64`-returning syscall succeeded (`lseek` resulting offset). -/
  | u64 (val : UInt64)
  /-- Stat-returning syscall succeeded (`fstat`, `fstatat`). -/
  | statted (st : StatInfo)
  /-- Syscall failed with Linux `Errno`. -/
  | err (code : Errno)
  deriving Repr

namespace Internal

/-- Low-level C-ABI syscall hooks parameterized over monad `m` and descriptor type `fd`. -/
structure PosixFilesOpsM (m : Type → Type) (fd : Type) where
  /-- Raw `openat(2)` hook accepting portable flag bits. -/
  openat : Option fd → ByteArray → UInt32 → Mode → m (Except Errno fd)
  /-- Raw `openat2(2)` hook accepting portable flag bits, mode, and resolve bits. -/
  openat2 : Option fd → ByteArray → UInt32 → Mode → UInt64 → m (Except Errno fd)
  /-- Raw `close(2)` hook. -/
  close : fd → m (Except Errno Unit)
  /-- Raw `read(2)` hook. -/
  read : fd → UInt32 → m (Except Errno ByteArray)
  /-- Raw `write(2)` hook. -/
  write : fd → ByteArray → m (Except Errno UInt32)
  /-- Raw `fstat(2)` hook returning `RawStatTuple`. -/
  fstat : fd → m (Except Errno RawStatTuple)
  /-- Raw `newfstatat(2)` hook returning `RawStatTuple`. -/
  fstatat : Option fd → ByteArray → UInt32 → m (Except Errno RawStatTuple)
  /-- Raw `faccessat2(2)` (`__NR_faccessat2 = 439`) hook accepting portable mode mask and `AtFlags` bits. -/
  faccessat : Option fd → ByteArray → UInt32 → UInt32 → m (Except Errno Unit)
  /-- Raw `mkdirat(2)` hook. -/
  mkdirat : Option fd → ByteArray → Mode → m (Except Errno Unit)
  /-- Raw `unlinkat(2)` hook (`removeDir` as `UInt8`: `0` or `1`). -/
  unlinkat : Option fd → ByteArray → UInt8 → m (Except Errno Unit)
  /-- Raw `renameat2(2)` hook accepting portable `RenameFlags` bits. -/
  renameat2 : Option fd → ByteArray → Option fd → ByteArray → UInt32 → m (Except Errno Unit)
  /-- Raw `symlinkat(2)` hook. -/
  symlinkat : ByteArray → Option fd → ByteArray → m (Except Errno Unit)
  /-- Raw `readlinkat(2)` hook. -/
  readlinkat : Option fd → ByteArray → UInt32 → m (Except Errno ByteArray)
  /-- Raw `getdents64(2)` hook. -/
  getdents64 : fd → UInt32 → m (Except Errno ByteArray)
  /-- Raw `fchmodat(2)` hook. -/
  fchmodat : Option fd → ByteArray → Mode → m (Except Errno Unit)
  /-- Raw `fchmod(2)` hook. -/
  fchmod : fd → Mode → m (Except Errno Unit)
  /-- Raw `flock(2)` hook accepting portable `FlockOp` bits. -/
  flock : fd → UInt32 → m (Except Errno Unit)
  /-- Raw `fcntl(2)` hook accepting `(cmdTag, arg)`. -/
  fcntl : fd → UInt32 → UInt32 → m (Except Errno UInt32)
  /-- Raw `fsync(2)` hook. -/
  fsync : fd → m (Except Errno Unit)
  /-- Raw `getcwd(2)` hook. -/
  getcwd : UInt32 → m (Except Errno ByteArray)
  /-- Raw `lseek(2)` hook accepting signed `Int64` offset and `SeekWhence` tag. -/
  lseek : fd → Int64 → UInt32 → m (Except Errno UInt64)
  /-- Raw `/proc/thread-self/fd/%d` read-only reopen hook (verified against procfs and inode identity). -/
  reopenReadOnly : fd → m (Except Errno fd)
  /-- Raw `fcntl(slot, F_DUPFD_CLOEXEC, 3)` stdio duplicate hook. -/
  dupStdio : UInt32 → m (Except Errno fd)

/-- Low-level C-ABI syscall hooks supplied by `Interface.lean` and backed by `files_shim.c`. -/
abbrev PosixFilesOps := PosixFilesOpsM IO RawFd

end Internal

end LeanSwe.LinuxSyscall.Files
