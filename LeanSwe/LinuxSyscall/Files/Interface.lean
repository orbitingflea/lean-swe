import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Impl

namespace LeanSwe.LinuxSyscall.Files

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_openat"]
private opaque rawOpenat :
    @& Option RawFd → @& ByteArray → UInt32 → Mode → IO (Except Errno RawFd)

@[extern "leanswe_sys_openat2"]
private opaque rawOpenat2 :
    @& Option RawFd → @& ByteArray → UInt32 → Mode → UInt64 → IO (Except Errno RawFd)

@[extern "leanswe_sys_close"]
private opaque rawClose : @& RawFd → IO (Except Errno Unit)

@[extern "leanswe_sys_read"]
private opaque rawRead : @& RawFd → UInt32 → IO (Except Errno ByteArray)

@[extern "leanswe_sys_write"]
private opaque rawWrite : @& RawFd → @& ByteArray → IO (Except Errno UInt32)

@[extern "leanswe_sys_fstat"]
private opaque rawFstat : @& RawFd → IO (Except Errno RawStatTuple)

@[extern "leanswe_sys_fstatat"]
private opaque rawFstatat :
    @& Option RawFd → @& ByteArray → UInt32 → IO (Except Errno RawStatTuple)

@[extern "leanswe_sys_faccessat"]
private opaque rawFaccessat :
    @& Option RawFd → @& ByteArray → UInt32 → UInt32 → IO (Except Errno Unit)

@[extern "leanswe_sys_mkdirat"]
private opaque rawMkdirat :
    @& Option RawFd → @& ByteArray → Mode → IO (Except Errno Unit)

@[extern "leanswe_sys_unlinkat"]
private opaque rawUnlinkat :
    @& Option RawFd → @& ByteArray → UInt8 → IO (Except Errno Unit)

@[extern "leanswe_sys_renameat2"]
private opaque rawRenameat2 :
    @& Option RawFd → @& ByteArray → @& Option RawFd → @& ByteArray → UInt32 → IO (Except Errno Unit)

@[extern "leanswe_sys_symlinkat"]
private opaque rawSymlinkat :
    @& ByteArray → @& Option RawFd → @& ByteArray → IO (Except Errno Unit)

@[extern "leanswe_sys_readlinkat"]
private opaque rawReadlinkat :
    @& Option RawFd → @& ByteArray → UInt32 → IO (Except Errno ByteArray)

@[extern "leanswe_sys_getdents64"]
private opaque rawGetdents64 : @& RawFd → UInt32 → IO (Except Errno ByteArray)

@[extern "leanswe_sys_fchmodat"]
private opaque rawFchmodat :
    @& Option RawFd → @& ByteArray → Mode → IO (Except Errno Unit)

@[extern "leanswe_sys_fchmod"]
private opaque rawFchmod : @& RawFd → Mode → IO (Except Errno Unit)

@[extern "leanswe_sys_flock"]
private opaque rawFlock : @& RawFd → UInt32 → IO (Except Errno Unit)

@[extern "leanswe_sys_fcntl"]
private opaque rawFcntl : @& RawFd → UInt32 → UInt32 → IO (Except Errno UInt32)

@[extern "leanswe_sys_fsync"]
private opaque rawFsync : @& RawFd → IO (Except Errno Unit)

@[extern "leanswe_sys_getcwd"]
private opaque rawGetcwd : UInt32 → IO (Except Errno ByteArray)

@[extern "leanswe_sys_lseek"]
private opaque rawLseek : @& RawFd → Int64 → UInt32 → IO (Except Errno UInt64)

@[extern "leanswe_sys_reopen_readonly"]
private opaque rawReopenReadOnly : @& RawFd → IO (Except Errno RawFd)

@[extern "leanswe_sys_dup_stdio"]
private opaque rawDupStdio : UInt32 → IO (Except Errno RawFd)

private def posixFilesOps : Internal.PosixFilesOps :=
  { openat := rawOpenat
    openat2 := rawOpenat2
    close := rawClose
    read := rawRead
    write := rawWrite
    fstat := rawFstat
    fstatat := rawFstatat
    faccessat := rawFaccessat
    mkdirat := rawMkdirat
    unlinkat := rawUnlinkat
    renameat2 := rawRenameat2
    symlinkat := rawSymlinkat
    readlinkat := rawReadlinkat
    getdents64 := rawGetdents64
    fchmodat := rawFchmodat
    fchmod := rawFchmod
    flock := rawFlock
    fcntl := rawFcntl
    fsync := rawFsync
    getcwd := rawGetcwd
    lseek := rawLseek
    reopenReadOnly := rawReopenReadOnly
    dupStdio := rawDupStdio }

/-- Default Linux `Files` syscall bundle backed by `LeanSwe/LinuxSyscall/c/files_shim.c`. -/
def defaultOps : FilesOps :=
  Internal.mkFilesOps posixFilesOps

/-- Open or create a file relative to `dir` (`AT_FDCWD` when `none`) via Linux `openat(2)`. -/
@[inline] def openat (dir : Option RawFd) (path : ByteArray) (flags : OpenFlags) (mode : Mode := 0o644) :
    IO (Except Errno RawFd) :=
  defaultOps.openat dir path flags mode

/-- Open or create a file with strict `RESOLVE_*` constraints via Linux `openat2(2)`. -/
@[inline] def openat2 (dir : Option RawFd) (path : ByteArray) (how : OpenHow) :
    IO (Except Errno RawFd) :=
  defaultOps.openat2 dir path how

/-- Close an open `RawFd` handle via Linux `close(2)` (returns `EBUSY` if pinned, `EBADF` if already closed). -/
@[inline] def close (fd : RawFd) : IO (Except Errno Unit) :=
  defaultOps.close fd

/-- Read up to `min maxBytes MAX_READ_BYTES` bytes from `fd` via Linux `read(2)`. -/
@[inline] def read (fd : RawFd) (maxBytes : UInt32) : IO (Except Errno ByteArray) :=
  defaultOps.read fd maxBytes

/-- Write a non-empty prefix (or 0 for empty `data`) to `fd` via Linux `write(2)`. -/
@[inline] def write (fd : RawFd) (data : ByteArray) : IO (Except Errno UInt32) :=
  defaultOps.write fd data

/-- Query metadata of an open `RawFd` via Linux `fstat(2)`. -/
@[inline] def fstat (fd : RawFd) : IO (Except Errno StatInfo) :=
  defaultOps.fstat fd

/-- Query metadata of `path` relative to `dir` via Linux `newfstatat(2)` / `fstatat(2)`. -/
@[inline] def fstatat (dir : Option RawFd) (path : ByteArray) (flags : AtFlags := {}) :
    IO (Except Errno StatInfo) :=
  defaultOps.fstatat dir path flags

/-- Check access permissions of `path` relative to `dir` via Linux `faccessat2(2)` (`__NR_faccessat2 = 439` on `x86_64` and `aarch64`, honoring `AtFlags`). -/
@[inline] def faccessat (dir : Option RawFd) (path : ByteArray) (mask : AccessModeMask := {})
    (flags : AtFlags := {}) : IO (Except Errno Unit) :=
  defaultOps.faccessat dir path mask flags

/-- Create a directory at `path` relative to `dir` via Linux `mkdirat(2)`. -/
@[inline] def mkdirat (dir : Option RawFd) (path : ByteArray) (mode : Mode := 0o755) :
    IO (Except Errno Unit) :=
  defaultOps.mkdirat dir path mode

/-- Remove a file/symlink (`removeDir = false`) or empty directory (`removeDir = true`) via Linux `unlinkat(2)`. -/
@[inline] def unlinkat (dir : Option RawFd) (path : ByteArray) (removeDir : Bool := false) :
    IO (Except Errno Unit) :=
  defaultOps.unlinkat dir path removeDir

/-- Rename or exchange entries via Linux `renameat2(2)`. -/
@[inline] def renameat2 (oldDir : Option RawFd) (oldPath : ByteArray)
    (newDir : Option RawFd) (newPath : ByteArray) (flags : RenameFlags := {}) :
    IO (Except Errno Unit) :=
  defaultOps.renameat2 oldDir oldPath newDir newPath flags

/-- Create a symbolic link at `(dir, linkPath)` pointing to `target` via Linux `symlinkat(2)`. -/
@[inline] def symlinkat (target : ByteArray) (dir : Option RawFd) (linkPath : ByteArray) :
    IO (Except Errno Unit) :=
  defaultOps.symlinkat target dir linkPath

/-- Read up to `min cap MAX_READ_BYTES` raw symbolic link target bytes via Linux `readlinkat(2)`. -/
@[inline] def readlinkat (dir : Option RawFd) (path : ByteArray) (cap : UInt32 := 4096) :
    IO (Except Errno ByteArray) :=
  defaultOps.readlinkat dir path cap

/-- Read up to `min bufBytes MAX_READ_BYTES` bytes of raw `linux_dirent64` records from directory `fd` via Linux `getdents64(2)`. -/
@[inline] def getdents64 (fd : RawFd) (bufBytes : UInt32 := 8192) : IO (Except Errno ByteArray) :=
  defaultOps.getdents64 fd bufBytes

/-- Change permission mode bits of `path` relative to `dir` via Linux `fchmodat(2)`. -/
@[inline] def fchmodat (dir : Option RawFd) (path : ByteArray) (mode : Mode) :
    IO (Except Errno Unit) :=
  defaultOps.fchmodat dir path mode

/-- Change permission mode bits of an open `RawFd` via Linux `fchmod(2)`. -/
@[inline] def fchmod (fd : RawFd) (mode : Mode) : IO (Except Errno Unit) :=
  defaultOps.fchmod fd mode

/-- Apply or release an advisory lock on `fd` via Linux `flock(2)`. -/
@[inline] def flock (fd : RawFd) (op : FlockOp) : IO (Except Errno Unit) :=
  defaultOps.flock fd op

/-- Manipulate descriptor flags, open file status flags (`F_GETFL` decodes portable `(access, append, nonblock)` bits), or `memfd` seals via Linux `fcntl(2)`. -/
@[inline] def fcntl (fd : RawFd) (cmd : FcntlCmd) : IO (Except Errno UInt32) :=
  defaultOps.fcntl fd cmd

/-- Synchronize an open file descriptor's data and metadata to storage via Linux `fsync(2)`. -/
@[inline] def fsync (fd : RawFd) : IO (Except Errno Unit) :=
  defaultOps.fsync fd

/-- Query the current working directory byte path (clamped to `min cap MAX_READ_BYTES`) via Linux `getcwd(2)`. -/
@[inline] def getcwd (cap : UInt32 := 4096) : IO (Except Errno ByteArray) :=
  defaultOps.getcwd cap

/-- Reposition read/write file offset or directory cursor via Linux `lseek(2)`. -/
@[inline] def lseek (fd : RawFd) (offset : Int64) (whence : SeekWhence := .seekSet) :
    IO (Except Errno UInt64) :=
  defaultOps.lseek fd offset whence

/-- Reopen an open descriptor read-only with `O_CLOEXEC` via `/proc/thread-self/fd/%d` after procfs and inode checks. -/
@[inline] def reopenReadOnly (fd : RawFd) : IO (Except Errno RawFd) :=
  defaultOps.reopenReadOnly fd

/-- Duplicate a standard descriptor slot (`0`/`1`/`2`) with `FD_CLOEXEC` (`>= 3`) via `fcntl(F_DUPFD_CLOEXEC, 3)`. -/
@[inline] def dupStdio (slot : StdioFd) : IO (Except Errno RawFd) :=
  defaultOps.dupStdio slot

end LeanSwe.LinuxSyscall.Files
