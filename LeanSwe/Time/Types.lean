import Std.Time

namespace LeanSwe.Time

/-- Classification of failures in `LeanSwe.Time`. -/
inductive TimeErrorKind where
  /-- Input string did not match expected UTC ISO 8601 or `YYYY-MM-DD` format. -/
  | invalidFormat
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.Time` parsing operations. -/
structure TimeError where
  /-- Machine-checkable error category. -/
  kind : TimeErrorKind
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Deterministic fake-clock state for testing and proofs over `TimeOpsM (StateM FakeClock)`. -/
structure FakeClock where
  /-- Simulated UTC wall-clock timestamp. -/
  wall : Std.Time.Timestamp
  /-- Simulated monotonic clock in nanoseconds. -/
  monoNanos : Nat
  /-- Recorded sequence of `UInt32` millisecond chunks passed to `TimeOpsM.sleep`. -/
  sleepLog : Array UInt32 := #[]
  deriving Repr, DecidableEq, Inhabited

/-- Minimal effect interface wrapping the three real-clock and `sleep` `IO` entry points. -/
structure TimeOpsM (m : Type → Type) where
  /-- Read current UTC wall-clock timestamp (`Std.Time.Timestamp.now`). -/
  nowTimestamp : m Std.Time.Timestamp
  /-- Read current monotonic clock in nanoseconds (`IO.monoNanosNow`). -/
  monoNanosNow : m Nat
  /-- Sleep for `ms` milliseconds (`IO.sleep`). -/
  sleep : UInt32 → m Unit

/-- Concrete `IO` time operations bundle backed by `Std.Time.Timestamp.now`, `IO.monoNanosNow`, and `IO.sleep`. -/
abbrev TimeOps := TimeOpsM IO

/-- Public operations exported by `LeanSwe.Time`, parameterized over effect monad `m`. -/
structure TimeApiM (m : Type → Type) where
  /-- Read current UTC wall-clock timestamp. -/
  nowTimestamp : m Std.Time.Timestamp
  /-- Read current monotonic clock in nanoseconds. -/
  monoNanosNow : m Nat
  /-- Sleep for `ms` milliseconds, chunking values exceeding `UInt32.max`. -/
  sleepMs : Nat → m Unit
  /-- Sleep for a `Std.Time.Duration`, clamping non-positive durations to zero and rounding positive sub-millisecond durations up to at least 1 ms. -/
  sleepDuration : Std.Time.Duration → m Unit
  /-- Execute `act` and return its result alongside elapsed monotonic `Std.Time.Duration`. -/
  measure : {α : Type} → m α → m (α × Std.Time.Duration)
  /-- Compute non-negative elapsed `Std.Time.Duration` between monotonic nanosecond readings `(startMono, stopMono)`. -/
  elapsedDuration : Nat → Nat → Std.Time.Duration
  /-- Compute monotonic nanosecond deadline `startMono + max 0 limit.toNanoseconds`. -/
  deadlineNanos : Nat → Std.Time.Duration → Nat
  /-- Return `true` iff `deadlineMono ≤ nowMono` given `(nowMono, deadlineMono)`. -/
  isMonoExpired : Nat → Nat → Bool
  /-- Format a `Std.Time.Timestamp` in UTC ISO 8601 (`YYYY-MM-DDTHH:MM:SS.nnnnnnnnnZ`). -/
  formatUtcIso8601 : Std.Time.Timestamp → String
  /-- Parse an ISO 8601 timestamp string (with `Z` or `±HH:MM` offset, with or without nanoseconds) into a UTC `Std.Time.Timestamp`. -/
  parseUtcIso8601 : String → Except TimeError Std.Time.Timestamp
  /-- Format a `Std.Time.Timestamp` as compact UTC stamp `YYYYMMDDTHHMMSSZ`. -/
  formatUtcCompact : Std.Time.Timestamp → String
  /-- Format a `Std.Time.PlainDate` as `YYYY-MM-DD`. -/
  formatUtcDate : Std.Time.PlainDate → String
  /-- Parse a `YYYY-MM-DD` date string into `Std.Time.PlainDate`. -/
  parseUtcDate : String → Except TimeError Std.Time.PlainDate
  /-- Convert a `Std.Time.Timestamp` to its UTC calendar `Std.Time.PlainDate`. -/
  utcDateOfTimestamp : Std.Time.Timestamp → Std.Time.PlainDate
  /-- Convert a UTC `Std.Time.PlainDate` to the midnight `Std.Time.Timestamp` at start of that UTC day. -/
  timestampOfUtcDate : Std.Time.PlainDate → Std.Time.Timestamp

/-- Concrete `IO` time API bundle exported by `LeanSwe.Time`. -/
abbrev TimeApi := TimeApiM IO

end LeanSwe.Time
