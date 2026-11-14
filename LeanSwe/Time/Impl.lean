import LeanSwe.Time.Types

namespace LeanSwe.Time.Internal

private def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

open Std.Time in
private def compactUtcFormat : Std.Time.GenericFormat (.only .GMT) :=
  datespec("uuuuMMdd'T'HHmmss'Z'")

/-- Sleep `ms` milliseconds via `ops.sleep`, splitting durations larger than `UInt32.max` into sequential `UInt32` chunks. -/
def sleepMs {m : Type → Type} [Monad m] (ops : TimeOpsM m) (ms : Nat) : m Unit :=
  if ms = 0 then
    pure ()
  else
    let chunkNat := min ms (UInt32.size - 1)
    do
      ops.sleep (UInt32.ofNat chunkNat)
      sleepMs ops (ms - chunkNat)
termination_by ms
decreasing_by
  have hpos : 0 < ms := Nat.pos_of_ne_zero ‹_›
  have hc : 0 < min ms (UInt32.size - 1) := Nat.lt_min.mpr ⟨hpos, by decide⟩
  omega

/-- Convert a `Std.Time.Duration` to sleep milliseconds (non-positive clamps to 0; positive sub-millisecond durations round up to 1 ms). -/
def sleepDurationMs (d : Std.Time.Duration) : Nat :=
  if d.toNanoseconds.val ≤ 0 then 0
  else (d.toNanoseconds.val.toNat + 999999) / 1000000

/-- Sleep for `d` via `sleepMs`, clamping non-positive durations to zero and rounding positive sub-millisecond durations up to at least 1 ms. -/
def sleepDuration {m : Type → Type} [Monad m] (ops : TimeOpsM m) (d : Std.Time.Duration) : m Unit :=
  sleepMs ops (sleepDurationMs d)

/-- Compute non-negative elapsed `Std.Time.Duration` between monotonic nanosecond readings `(startMono, stopMono)`. -/
def elapsedDuration (startMono stopMono : Nat) : Std.Time.Duration :=
  if startMono ≤ stopMono then
    Std.Time.Duration.ofNanoseconds (Std.Time.Nanosecond.Offset.ofNat (stopMono - startMono))
  else
    0

/-- Execute `act` and return its result alongside elapsed monotonic `Std.Time.Duration`. -/
def measure {m : Type → Type} [Monad m] (ops : TimeOpsM m) {α : Type} (act : m α) :
    m (α × Std.Time.Duration) := do
  let startMono ← ops.monoNanosNow
  let out ← act
  let stopMono ← ops.monoNanosNow
  pure (out, elapsedDuration startMono stopMono)

/-- Compute monotonic nanosecond deadline `startMono + max 0 limit.toNanoseconds`. -/
def deadlineNanos (startMono : Nat) (limit : Std.Time.Duration) : Nat :=
  if limit.toNanoseconds.val ≥ 0 then startMono + limit.toNanoseconds.val.toNat else startMono

/-- Return `true` iff `deadlineMono ≤ nowMono` given `(nowMono, deadlineMono)`. -/
def isMonoExpired (nowMono deadlineMono : Nat) : Bool :=
  decide (deadlineMono ≤ nowMono)

/-- Format a `Std.Time.Timestamp` in UTC ISO 8601 (`YYYY-MM-DDTHH:MM:SS.nnnnnnnnnZ`). -/
def formatUtcIso8601 (ts : Std.Time.Timestamp) : String :=
  (Std.Time.DateTime.ofTimestamp ts .UTC).toLeanDateTimeWithZoneString

/-- Parse an ISO 8601 timestamp string (with `Z` or `±HH:MM` offset, with or without nanoseconds) into a UTC `Std.Time.Timestamp`. -/
def parseUtcIso8601 (raw : String) : Except TimeError Std.Time.Timestamp :=
  match Std.Time.DateTime.fromLeanDateTimeWithZoneString raw with
  | .ok dt => .ok dt.toTimestamp
  | .error err => .error { kind := .invalidFormat, message := nonEmptyMsg "invalid UTC ISO 8601 timestamp" err }

/-- Format a `Std.Time.Timestamp` as compact UTC stamp `YYYYMMDDTHHMMSSZ`. -/
def formatUtcCompact (ts : Std.Time.Timestamp) : String :=
  compactUtcFormat.format (Std.Time.DateTime.ofTimestamp ts .UTC)

/-- Format a `Std.Time.PlainDate` as `YYYY-MM-DD`. -/
def formatUtcDate (d : Std.Time.PlainDate) : String :=
  d.toLeanDateString

/-- Parse a `YYYY-MM-DD` date string into `Std.Time.PlainDate`. -/
def parseUtcDate (raw : String) : Except TimeError Std.Time.PlainDate :=
  match Std.Time.PlainDate.fromLeanDateString raw with
  | .ok d => .ok d
  | .error err => .error { kind := .invalidFormat, message := nonEmptyMsg "invalid UTC date" err }

/-- Convert a `Std.Time.Timestamp` to its UTC calendar `Std.Time.PlainDate`. -/
def utcDateOfTimestamp (ts : Std.Time.Timestamp) : Std.Time.PlainDate :=
  (Std.Time.DateTime.ofTimestamp ts .UTC).toPlainDate

/-- Convert a UTC `Std.Time.PlainDate` to the midnight `Std.Time.Timestamp` at start of that UTC day. -/
def timestampOfUtcDate (d : Std.Time.PlainDate) : Std.Time.Timestamp :=
  d.toTimestamp .UTC

/-- Assemble a `TimeApiM m` record over a `TimeOpsM m` effect implementation. -/
def mkApiM {m : Type → Type} [Monad m] (ops : TimeOpsM m) : TimeApiM m :=
  { nowTimestamp := ops.nowTimestamp
    monoNanosNow := ops.monoNanosNow
    sleepMs := sleepMs ops
    sleepDuration := sleepDuration ops
    measure := measure ops
    elapsedDuration := elapsedDuration
    deadlineNanos := deadlineNanos
    isMonoExpired := isMonoExpired
    formatUtcIso8601 := formatUtcIso8601
    parseUtcIso8601 := parseUtcIso8601
    formatUtcCompact := formatUtcCompact
    formatUtcDate := formatUtcDate
    parseUtcDate := parseUtcDate
    utcDateOfTimestamp := utcDateOfTimestamp
    timestampOfUtcDate := timestampOfUtcDate }

/-- Deterministic `TimeOpsM (StateM FakeClock)` advancing `wall`, `monoNanos`, and `sleepLog` on `sleep`. -/
def fakeOps : TimeOpsM (StateM FakeClock) :=
  { nowTimestamp := do
      let s ← get
      pure s.wall
    monoNanosNow := do
      let s ← get
      pure s.monoNanos
    sleep := fun ms =>
      modify fun s =>
        { wall := s.wall + Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofNat ms.toNat)
          monoNanos := s.monoNanos + ms.toNat * 1000000
          sleepLog := s.sleepLog.push ms } }

/-- Deterministic `TimeApiM (StateM FakeClock)` backed by `fakeOps`. -/
def fakeApi : TimeApiM (StateM FakeClock) :=
  mkApiM fakeOps

end LeanSwe.Time.Internal
