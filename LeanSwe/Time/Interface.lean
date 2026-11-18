import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.Time.Types
import LeanSwe.Time.Impl

namespace LeanSwe.Time

/-- Build a `TimeOpsM m` capability bundle purely over `LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m`. -/
@[inline] def mkTimeOps {m : Type → Type} [Monad m]
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m) : TimeOpsM m :=
  Internal.mkTimeOps sys

/-- Default `TimeOps` backed by `LeanSwe.LinuxSyscall.TimeRand.defaultOps` (`CLOCK_REALTIME`, `CLOCK_MONOTONIC`, and `TIMER_ABSTIME` `clock_nanosleep` with bounded `EINTR` retry). -/
def defaultOps : TimeOps :=
  Internal.mkTimeOps LeanSwe.LinuxSyscall.TimeRand.defaultOps

/-- Default `TimeApi` backed by `defaultOps`. -/
def defaultApi : TimeApi :=
  Internal.mkApiM defaultOps

/-- Deterministic `TimeOpsM (StateM FakeClock)` for fast fake-clock tests and proofs. -/
def fakeOps : TimeOpsM (StateM FakeClock) :=
  Internal.fakeOps

/-- Deterministic `TimeApiM (StateM FakeClock)` backed by `fakeOps`. -/
def fakeApi : TimeApiM (StateM FakeClock) :=
  Internal.fakeApi

/-- Build a `TimeApiM m` over any custom `TimeOpsM m` effect implementation. -/
@[inline] def mkApiM {m : Type → Type} [Monad m] (ops : TimeOpsM m) : TimeApiM m :=
  Internal.mkApiM ops

/-- Read current UTC wall-clock timestamp. -/
@[inline] def nowTimestamp : IO Std.Time.Timestamp :=
  defaultApi.nowTimestamp

/-- Read current monotonic clock in nanoseconds. -/
@[inline] def monoNanosNow : IO Nat :=
  defaultApi.monoNanosNow

/-- Sleep for `ms` milliseconds, chunking values exceeding `UInt32.max`. -/
@[inline] def sleepMs (ms : Nat) : IO Unit :=
  defaultApi.sleepMs ms

/-- Sleep for a `Std.Time.Duration`, clamping non-positive durations to zero and rounding positive sub-millisecond durations up to at least 1 ms. -/
@[inline] def sleepDuration (d : Std.Time.Duration) : IO Unit :=
  defaultApi.sleepDuration d

/-- Execute `act` and return its result alongside elapsed monotonic `Std.Time.Duration`. -/
@[inline] def measure {α : Type} (act : IO α) : IO (α × Std.Time.Duration) :=
  defaultApi.measure act

/-- Compute non-negative elapsed `Std.Time.Duration` between monotonic nanosecond readings `(startMono, stopMono)`. -/
@[inline] def elapsedDuration (startMono stopMono : Nat) : Std.Time.Duration :=
  defaultApi.elapsedDuration startMono stopMono

/-- Compute monotonic nanosecond deadline `startMono + max 0 limit.toNanoseconds`. -/
@[inline] def deadlineNanos (startMono : Nat) (limit : Std.Time.Duration) : Nat :=
  defaultApi.deadlineNanos startMono limit

/-- Return `true` iff `deadlineMono ≤ nowMono` given `(nowMono, deadlineMono)`. -/
@[inline] def isMonoExpired (nowMono deadlineMono : Nat) : Bool :=
  defaultApi.isMonoExpired nowMono deadlineMono

/-- Format a `Std.Time.Timestamp` in UTC ISO 8601 (`YYYY-MM-DDTHH:MM:SS.nnnnnnnnnZ`). -/
@[inline] def formatUtcIso8601 (ts : Std.Time.Timestamp) : String :=
  defaultApi.formatUtcIso8601 ts

/-- Parse an ISO 8601 timestamp string (with `Z` or `±HH:MM` offset, with or without nanoseconds) into a UTC `Std.Time.Timestamp`. -/
@[inline] def parseUtcIso8601 (raw : String) : Except TimeError Std.Time.Timestamp :=
  defaultApi.parseUtcIso8601 raw

/-- Format a `Std.Time.Timestamp` as compact UTC stamp `YYYYMMDDTHHMMSSZ`. -/
@[inline] def formatUtcCompact (ts : Std.Time.Timestamp) : String :=
  defaultApi.formatUtcCompact ts

/-- Format a `Std.Time.PlainDate` as `YYYY-MM-DD`. -/
@[inline] def formatUtcDate (d : Std.Time.PlainDate) : String :=
  defaultApi.formatUtcDate d

/-- Parse a `YYYY-MM-DD` date string into `Std.Time.PlainDate`. -/
@[inline] def parseUtcDate (raw : String) : Except TimeError Std.Time.PlainDate :=
  defaultApi.parseUtcDate raw

/-- Convert a `Std.Time.Timestamp` to its UTC calendar `Std.Time.PlainDate`. -/
@[inline] def utcDateOfTimestamp (ts : Std.Time.Timestamp) : Std.Time.PlainDate :=
  defaultApi.utcDateOfTimestamp ts

/-- Convert a UTC `Std.Time.PlainDate` to the midnight `Std.Time.Timestamp` at start of that UTC day. -/
@[inline] def timestampOfUtcDate (d : Std.Time.PlainDate) : Std.Time.Timestamp :=
  defaultApi.timestampOfUtcDate d

end LeanSwe.Time
