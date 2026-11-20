import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Impl

namespace LeanSwe.LinuxSyscall.Process

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_pipe2"]
private opaque rawPipe2 : UInt64 → IO (Except Errno (RawFd × RawFd))

@[extern "leanswe_sys_waitpid"]
private opaque rawWaitpid : Int32 → UInt64 → IO (Except Errno RawWaitTuple)

@[extern "leanswe_sys_kill"]
private opaque rawKill : Int32 → UInt8 → Int32 → IO (Except Errno Unit)

@[extern "leanswe_sys_pidfd_open"]
private opaque rawPidfdOpen : UInt32 → UInt64 → IO (Except Errno RawFd)

@[extern "leanswe_sys_pidfd_send_signal"]
private opaque rawPidfdSendSignal :
    @& RawFd → UInt8 → Int32 → UInt64 → IO (Except Errno Unit)

@[extern "leanswe_sys_getpid"]
private opaque rawGetpid : IO (Except Errno UInt32)

@[extern "leanswe_sys_getuid"]
private opaque rawGetuid : IO (Except Errno UInt32)

private def posixProcessOps : PosixProcessOps :=
  { pipe2 := rawPipe2
    waitpid := rawWaitpid
    kill := rawKill
    pidfd_open := rawPidfdOpen
    pidfd_send_signal := rawPidfdSendSignal
    getpid := rawGetpid
    getuid := rawGetuid }

/-- Default Linux `Process` syscall bundle backed by `LeanSwe/LinuxSyscall/c/process_shim.c`. -/
def defaultOps : ProcessOps :=
  Internal.mkProcessOps posixProcessOps

/-- Create a unidirectional pipe pair `(readFd, writeFd)` with atomic flags via Linux `pipe2(2)`. -/
@[inline] def pipe2 (flags : PipeFlags := {}) : IO (Except Errno (RawFd × RawFd)) :=
  defaultOps.pipe2 flags

/-- Wait for child process state changes via Linux `wait4(pid, &status, opts, NULL)`. -/
@[inline] def waitpid (pid : Int32) (flags : WaitFlags := {}) : IO (Except Errno WaitResult) :=
  defaultOps.waitpid pid flags

/-- Send symbolic `sig` (`Signal.sigzero` for existence/permission probe) to `pidOrNegPgid` via Linux `kill(2)`. -/
@[inline] def kill (pidOrNegPgid : Int32) (sig : Signal) : IO (Except Errno Unit) :=
  defaultOps.kill pidOrNegPgid sig

/-- Open a race-free process file descriptor (`FD_CLOEXEC` always set) for thread-group leader `pid` via Linux `pidfd_open(2)` (`__NR_pidfd_open = 434`). -/
@[inline] def pidfd_open (pid : UInt32) (flags : PidfdOpenFlags := {}) : IO (Except Errno RawFd) :=
  defaultOps.pidfd_open pid flags

/-- Send symbolic `sig` to the process referenced by `pidfd` via Linux `pidfd_send_signal(2)` (`__NR_pidfd_send_signal = 424`). -/
@[inline] def pidfd_send_signal (pidfd : RawFd) (sig : Signal) (flags : PidfdSignalFlags := {}) :
    IO (Except Errno Unit) :=
  defaultOps.pidfd_send_signal pidfd sig flags

/-- Query the calling process's thread-group ID (`PID > 0`, or seccomp `Errno`) via Linux `getpid(2)`. -/
@[inline] def getpid : IO (Except Errno UInt32) :=
  defaultOps.getpid

/-- Query the calling process's real user ID (or seccomp `Errno`) via Linux `getuid(2)`. -/
@[inline] def getuid : IO (Except Errno UInt32) :=
  defaultOps.getuid

end LeanSwe.LinuxSyscall.Process
