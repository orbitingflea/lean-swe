import LeanSwe.LinuxSyscall.Files.Types

namespace LeanSwe.LinuxSyscall.Files

open LeanSwe.LinuxSyscall

namespace Internal

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
