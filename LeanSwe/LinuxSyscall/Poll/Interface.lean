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

/-- Return `true` iff a `ppoll(2)` `revents` entry signals readiness, hangup, error, or invalid descriptor. -/
def pollEvReady (wantOut : Bool) (ev : PollEvents) : Bool :=
  (if wantOut then ev.pollout else ev.pollin) || ev.pollhup || ev.pollerr || ev.pollnval

/-- Convert a relative timeout in milliseconds to a valid `Poll.Timespec` (`0 ≤ sec ≤ Int64.max`, `nsec < 1_000_000_000`). -/
def msToPollTimespec (ms : Nat) : Timespec :=
  let clampedSec := Nat.min (ms / 1000) 9223372036854775807
  let remNs := (ms % 1000) * 1000000
  { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }

end LeanSwe.LinuxSyscall.Poll
