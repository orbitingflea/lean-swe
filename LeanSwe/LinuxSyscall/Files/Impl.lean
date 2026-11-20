import LeanSwe.LinuxSyscall.Files.Types

namespace LeanSwe.LinuxSyscall.Files

open LeanSwe.LinuxSyscall

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

/-- Construct a `FilesOpsM m fd` capability record from low-level `PosixFilesOpsM m fd` hooks, enforcing embedded-NUL and flag guards directly in Lean. -/
def mkFilesOpsM {m : Type → Type} [Monad m] {fd : Type} (raw : PosixFilesOpsM m fd) : FilesOpsM m fd :=
  { openat := fun dir path flags mode =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.openat dir path flags.toBits mode
    openat2 := fun dir path how =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.openat2 dir path how.flags.toBits how.mode how.resolve.toBits
    close := raw.close
    read := raw.read
    write := raw.write
    fstat := fun fd => do
      match ← raw.fstat fd with
      | .ok t => return .ok (StatInfo.ofRawTuple t)
      | .error e => return .error e
    fstatat := fun dir path flags =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else if flags.eaccess then pure (.error Errno.EINVAL)
      else do
        match ← raw.fstatat dir path flags.toBits with
        | .ok t => return .ok (StatInfo.ofRawTuple t)
        | .error e => return .error e
    faccessat := fun dir path mask flags =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.faccessat dir path mask.toBits flags.toBits
    mkdirat := fun dir path mode =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.mkdirat dir path mode
    unlinkat := fun dir path removeDir =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.unlinkat dir path (if removeDir then 1 else 0)
    renameat2 := fun oldDir oldPath newDir newPath flags =>
      if hasEmbeddedNul oldPath || hasEmbeddedNul newPath then pure (.error Errno.EINVAL)
      else raw.renameat2 oldDir oldPath newDir newPath flags.toBits
    symlinkat := fun target dir linkPath =>
      if hasEmbeddedNul target || hasEmbeddedNul linkPath then pure (.error Errno.EINVAL)
      else raw.symlinkat target dir linkPath
    readlinkat := fun dir path cap =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.readlinkat dir path cap
    getdents64 := raw.getdents64
    fchmodat := fun dir path mode =>
      if hasEmbeddedNul path then pure (.error Errno.EINVAL)
      else raw.fchmodat dir path mode
    fchmod := raw.fchmod
    flock := fun fd op => raw.flock fd op.toBits
    fcntl := fun fd cmd =>
      let (tag, arg) := cmd.toRaw
      raw.fcntl fd tag arg
    fsync := raw.fsync
    getcwd := raw.getcwd
    lseek := fun fd off w => raw.lseek fd off w.toRaw
    reopenReadOnly := raw.reopenReadOnly
    dupStdio := fun slot => raw.dupStdio slot.toRaw }

/-- Construct the public `FilesOps` capability record from low-level `PosixFilesOps` hooks. -/
def mkFilesOps (raw : PosixFilesOps) : FilesOps :=
  mkFilesOpsM raw

end Internal

end LeanSwe.LinuxSyscall.Files
