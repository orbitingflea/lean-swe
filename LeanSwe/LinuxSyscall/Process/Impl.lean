import LeanSwe.LinuxSyscall.Process.Types

namespace LeanSwe.LinuxSyscall.Process

namespace Internal

/-- Construct the public `ProcessOpsM` capability bundle from low-level `PosixProcessOpsM` hooks, encoding portable flags/signals and decoding `wait4` status words in pure Lean. -/
def mkProcessOps {m : Type → Type} [Monad m] {fd : Type} (raw : PosixProcessOpsM m fd) :
    ProcessOpsM m fd :=
  { pipe2 := fun flags =>
      raw.pipe2 flags.toBits
    waitpid := fun pid flags => do
      match ← raw.waitpid pid flags.toBits with
      | .ok t => return .ok (WaitResult.ofRawWait4 t)
      | .error e => return .error e
    kill := fun pidOrNegPgid sig =>
      if sig.isNptlReserved then
        pure (.error Errno.EINVAL)
      else
        let (tag, arg) := sig.toRaw
        raw.kill pidOrNegPgid tag arg
    pidfd_open := fun pid flags =>
      raw.pidfd_open pid flags.toBits
    pidfd_send_signal := fun pidfd sig flags =>
      if sig.isNptlReserved then
        pure (.error Errno.EINVAL)
      else
        let (tag, arg) := sig.toRaw
        raw.pidfd_send_signal pidfd tag arg flags.toBits
    getpid := raw.getpid
    getuid := raw.getuid }

end Internal

end LeanSwe.LinuxSyscall.Process
