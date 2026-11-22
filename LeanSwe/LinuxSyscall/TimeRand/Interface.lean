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

/-- Convert a non-negative `TimeRand.Timespec` reading to milliseconds. -/
def timespecToMs (ts : Timespec) : Nat :=
  ts.sec.toInt.toNat * 1000 + ts.nsec.toNat / 1000000

/-- Read `CLOCK_MONOTONIC` in milliseconds via `timeRand.clock_gettime`. -/
def monoNowMs {m : Type → Type} [Monad m] (timeRand : TimeRandOpsM m) : m (Except Errno Nat) := do
  match ← timeRand.clock_gettime .monotonic with
  | .ok ts => return .ok (timespecToMs ts)
  | .error e => return .error e

/-- Check whether optional deadline `timeoutMs?` has expired relative to `startMs` (`(expired, remainingMs)`). -/
def checkTimedOut {m : Type → Type} [Monad m]
    (timeRand : TimeRandOpsM m) (startMs : Nat) :
    Option Nat → m (Except Errno (Bool × Nat))
  | none => pure (.ok (false, 0))
  | some timeoutMs => do
    match ← monoNowMs timeRand with
    | .error e => return .error e
    | .ok nowMs =>
      let elapsed := nowMs - startMs
      if elapsed ≥ timeoutMs then
        return .ok (true, 0)
      else
        return .ok (false, timeoutMs - elapsed)

/-- Sleep on `CLOCK_MONOTONIC` for `ms` milliseconds, returning on `EINTR` without retrying. -/
def sleepMonoMs {m : Type → Type} [Monad m]
    (timeRand : TimeRandOpsM m) (ms : Nat) : m Unit := do
  let clampedSec := Nat.min (ms / 1000) MAX_TIMESPEC_SEC
  let remNs := (ms % 1000) * 1000000
  let _ ← timeRand.clock_nanosleep .monotonic false
    { sec := Int64.ofInt (Int.ofNat clampedSec), nsec := UInt32.ofNat remNs }
  pure ()

end LeanSwe.LinuxSyscall.TimeRand
