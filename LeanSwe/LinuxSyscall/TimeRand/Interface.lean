import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Impl

namespace LeanSwe.LinuxSyscall.TimeRand

open LeanSwe.LinuxSyscall

@[extern "leanswe_sys_clock_gettime"]
private opaque rawClockGettime : UInt32 → BaseIO (Except Errno (Int64 × UInt32))

@[extern "leanswe_sys_clock_nanosleep"]
private opaque rawClockNanosleep : UInt32 → UInt8 → Int64 → UInt32 → BaseIO (Except Errno Unit)

@[extern "leanswe_sys_getrandom"]
private opaque rawGetrandom : UInt32 → UInt32 → BaseIO (Except Errno ByteArray)

private def posixTimeRandOps : Internal.PosixTimeRandOps :=
  { clock_gettime := fun clk => liftM (rawClockGettime clk)
    clock_nanosleep := fun clk abs sec nsec => liftM (rawClockNanosleep clk abs sec nsec)
    getrandom := fun len flags => liftM (rawGetrandom len flags) }

/-- Default Linux `TimeRand` syscall bundle backed by `LeanSwe/LinuxSyscall/c/timerand_shim.c`. -/
def defaultOps : TimeRandOps :=
  Internal.mkTimeRandOps posixTimeRandOps

/-- Read the current value of `clk` (`CLOCK_REALTIME` or `CLOCK_MONOTONIC`) via Linux `clock_gettime(2)`. -/
@[inline] def clock_gettime (clk : ClockId) : IO (Except Errno Timespec) :=
  defaultOps.clock_gettime clk

/-- Sleep on `clk` for relative duration `req` (`abstime = false`) or until `TIMER_ABSTIME` deadline `req` (`abstime = true`) via Linux `clock_nanosleep(2)` (`SYS_clock_nanosleep`; returns `EINTR` normally without retrying). -/
@[inline] def clock_nanosleep (clk : ClockId) (abstime : Bool) (req : Timespec) :
    IO (Except Errno Unit) :=
  defaultOps.clock_nanosleep clk abstime req

/-- Read up to `min len MAX_READ_BYTES` random bytes via Linux `getrandom(2)` (`SYS_getrandom`; returns exact `len` bytes when `len ≤ 256` and `0` bytes when `len = 0`). -/
@[inline] def getrandom (len : UInt32) (flags : GrndFlags := {}) : IO (Except Errno ByteArray) :=
  defaultOps.getrandom len flags

end LeanSwe.LinuxSyscall.TimeRand
