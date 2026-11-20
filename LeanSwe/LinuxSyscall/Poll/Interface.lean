import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Poll.Impl

namespace LeanSwe.LinuxSyscall.Poll

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_ppoll"]
private opaque rawPpoll :
    @& Array RawFd → @& ByteArray → UInt8 → UInt64 → UInt32 → IO (Except Errno ByteArray)

@[extern "leanswe_sys_eventfd2"]
private opaque rawEventfd2 : UInt32 → UInt32 → IO (Except Errno RawFd)

private def posixPollOps : Internal.PosixPollOps :=
  { ppoll := rawPpoll
    eventfd2 := rawEventfd2 }

/-- Default Linux `Poll` syscall bundle backed by `LeanSwe/LinuxSyscall/c/poll_shim.c`. -/
def defaultOps : PollOps :=
  Internal.mkPollOps posixPollOps

/-- Wait for readiness events across `fds` with optional relative `timeout` (`none` = block indefinitely) via Linux `ppoll(2)`. -/
@[inline] def ppoll (fds : Array (RawFd × PollEvents)) (timeout : Option Timespec := none) :
    IO (Except Errno (Array PollEvents)) :=
  defaultOps.ppoll fds timeout

/-- Create an `eventfd` counter object initialized to `initval` with `flags` via Linux `eventfd2(2)`. -/
@[inline] def eventfd2 (initval : UInt32 := 0) (flags : EventFdFlags := {}) :
    IO (Except Errno RawFd) :=
  defaultOps.eventfd2 initval flags

end LeanSwe.LinuxSyscall.Poll
