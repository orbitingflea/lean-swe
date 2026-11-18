import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.Time.Types

namespace LeanSwe.Time

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand
  (ClockId Timespec TimeRandOpsM TimeRandState MAX_TIMESPEC_NANOS)

/-- Trace state recording `TimeRandOpsM` calls made by `mkTimeOps` during `EINTR` and sleep tests. -/
structure SleepTraceState where
  /-- Monotonic `Timespec` returned by `clock_gettime .monotonic` when `gettimeErr? = none`. -/
  monoNow : Timespec := { sec := 0, nsec := 0 }
  /-- Optional `Errno` returned by `clock_gettime` to exercise error-fallback paths. -/
  gettimeErr? : Option Errno := none
  /-- Queued `clock_nanosleep` responses popped in order (defaulting to `.ok ()` once empty). -/
  sleepResponses : List (Except Errno Unit) := []
  /-- Number of `clock_gettime` calls observed. -/
  gettimeCalls : Nat := 0
  /-- Recorded `(clk, abstime, req)` arguments passed to `clock_nanosleep` (most recent first). -/
  nanosleepLog : List (ClockId × Bool × Timespec) := []
  deriving Repr, Inhabited

/-- Scripted `TimeRandOpsM (StateM SleepTraceState)` logging `clock_gettime` and `clock_nanosleep` invocations. -/
def scriptedSleepSysOps (fallback : Except Errno Unit := .ok ()) :
    TimeRandOpsM (StateM SleepTraceState) :=
  { clock_gettime := fun _ => do
      let s ← get
      let r := match s.gettimeErr? with
        | some e => .error e
        | none => .ok s.monoNow
      set { s with gettimeCalls := s.gettimeCalls + 1 }
      return r
    clock_nanosleep := fun clk abstime req => do
      let s ← get
      let log' := (clk, abstime, req) :: s.nanosleepLog
      let r := match s.sleepResponses with
        | [] => fallback
        | x :: _ => x
      set { s with sleepResponses := s.sleepResponses.tail, nanosleepLog := log' }
      return r
    getrandom := fun _ _ => pure (.error Errno.ENOSYS) }

/-- Adding then subtracting the same `Std.Time.Duration` recovers the original `Std.Time.Duration`. -/
def test_time_duration_addSubInverse
    {runner} [NondetTest runner] : runner Unit := do
  let d1 ← nondet Std.Time.Duration
  let d2 ← nondet Std.Time.Duration
  NondetTest.assert ((d1 + d2) - d2 = d1)

/-- Adding then subtracting a `Std.Time.Duration` on a `Std.Time.Timestamp` recovers the original timestamp, and subtracting the base timestamp recovers the duration. -/
def test_time_timestamp_addSubInverse
    {runner} [NondetTest runner] : runner Unit := do
  let t ← nondet Std.Time.Timestamp
  let d ← nondet Std.Time.Duration
  NondetTest.assert ((t + d) - d = t ∧ (t + d) - t = d)

/-- `Timestamp` ordering `t1 ≤ t2` holds iff the difference `t2 - t1` has non-negative nanoseconds. -/
def test_time_timestamp_le_iff_diffNonneg
    {runner} [NondetTest runner] : runner Unit := do
  let t1 ← nondet Std.Time.Timestamp
  let t2 ← nondet Std.Time.Timestamp
  NondetTest.assert (t1 ≤ t2 ↔ (0 : Std.Time.Duration) ≤ (t2 - t1))

/-- Constructing a `Std.Time.Duration` from integer milliseconds and converting back to milliseconds is exact. -/
def test_time_duration_msRoundTrip
    {runner} [NondetTest runner] : runner Unit := do
  let ms ← nondet Int
  let d := Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofInt ms)
  NondetTest.assert (d.toMilliseconds.val = ms)

/-- Monotonic `deadlineNanos`, `isMonoExpired`, and `elapsedDuration` agree across positive/negative limits and arbitrary monotonic readings. -/
def test_time_mono_deadlineAndElapsed
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let startMono ← nondet Nat
  let limit ← nondet Std.Time.Duration
  let nowMono ← nondet Nat
  let stopMono ← nondet Nat
  let dl := api.deadlineNanos startMono limit
  NondetTest.assert (dl = if limit.toNanoseconds.val ≥ 0 then startMono + limit.toNanoseconds.val.toNat else startMono)
  NondetTest.assert (api.isMonoExpired nowMono dl = decide (dl ≤ nowMono))
  let elapsed := api.elapsedDuration startMono stopMono
  NondetTest.assert (if startMono ≤ stopMono
    then elapsed = Std.Time.Duration.ofNanoseconds (Std.Time.Nanosecond.Offset.ofNat (stopMono - startMono))
    else elapsed = 0)

/-- Reading `nowTimestamp` on `FakeClock` returns `wall` without modifying either clock or `sleepLog`. -/
def test_time_fakeClock_nowTimestamp_readsWithoutMutating
    {runner} [NondetTest runner] (api : TimeApiM (StateM FakeClock)) : runner Unit := do
  let s₀ ← nondet FakeClock
  let (ts, s₁) := api.nowTimestamp.run s₀
  NondetTest.assert (ts = s₀.wall ∧ s₁ = s₀)

/-- Reading `monoNanosNow` on `FakeClock` returns `monoNanos` without modifying either clock or `sleepLog`. -/
def test_time_fakeClock_monoNanosNow_readsWithoutMutating
    {runner} [NondetTest runner] (api : TimeApiM (StateM FakeClock)) : runner Unit := do
  let s₀ ← nondet FakeClock
  let (ns, s₁) := api.monoNanosNow.run s₀
  NondetTest.assert (ns = s₀.monoNanos ∧ s₁ = s₀)

/-- `sleepMs ms` advances both fake clocks deterministically and chunks `ms` into positive `UInt32` sleep calls summing to `ms`. -/
def test_time_fakeClock_sleepMs_advancesAndChunks
    {runner} [NondetTest runner] (api : TimeApiM (StateM FakeClock)) : runner Unit := do
  let s₀ ← nondet FakeClock
  let ms ← nondet Nat
  let ((), s₁) := (api.sleepMs ms).run s₀
  let added := s₁.sleepLog.toList.drop s₀.sleepLog.toList.length
  NondetTest.assert (s₁.monoNanos = s₀.monoNanos + ms * 1000000)
  NondetTest.assert (s₁.wall = s₀.wall + Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofNat ms))
  NondetTest.assert (s₁.sleepLog.toList.take s₀.sleepLog.toList.length = s₀.sleepLog.toList)
  NondetTest.assert (added.all (fun c => c.toNat > 0) = true)
  NondetTest.assert ((added.foldl (fun acc c => acc + c.toNat) 0) = ms)

/-- `sleepDuration d` is a no-op for non-positive durations and sleeps at least `d` (rounded up to 1 ms) for positive durations. -/
def test_time_fakeClock_sleepDuration_clampsAndRoundsUp
    {runner} [NondetTest runner] (api : TimeApiM (StateM FakeClock)) : runner Unit := do
  let s₀ ← nondet FakeClock
  let d ← nondet Std.Time.Duration
  let ((), s₁) := (api.sleepDuration d).run s₀
  if d.toNanoseconds.val ≤ 0 then
    NondetTest.assert (s₁ = s₀)
  else
    NondetTest.assert (s₀.monoNanos + d.toNanoseconds.val.toNat ≤ s₁.monoNanos ∧
      s₁.monoNanos < s₀.monoNanos + d.toNanoseconds.val.toNat + 1000000)

/-- `measure` returns the inner action's value together with the exact monotonic elapsed duration. -/
def test_time_fakeClock_measure_returnsValueAndElapsed
    {runner} [NondetTest runner] (api : TimeApiM (StateM FakeClock)) : runner Unit := do
  let s₀ ← nondet FakeClock
  let ms ← nondet Nat
  let ((res, elapsed), s₁) := (api.measure (do api.sleepMs ms; pure ms)).run s₀
  NondetTest.assert (res = ms)
  NondetTest.assert (elapsed = Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofNat ms))
  NondetTest.assert (s₁.monoNanos = s₀.monoNanos + ms * 1000000)

/-- Formatting any 4-digit UTC year (`0000`..`9999`) `Timestamp` as ISO 8601 and parsing it back yields the exact `Timestamp`, and `±HH:MM` offset timestamps normalize to the exact UTC instant. -/
def test_time_utcIso8601_roundTrip
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let ts ← nondet Std.Time.Timestamp
  assume (-62167219200000000000 ≤ ts.toNanosecondsSinceUnixEpoch.val ∧
    ts.toNanosecondsSinceUnixEpoch.val ≤ 253402300799999999999)
  let s := api.formatUtcIso8601 ts
  NondetTest.assert (api.parseUtcIso8601 s = .ok ts)
  NondetTest.assert (api.parseUtcIso8601 "2026-11-14T20:15:00+02:00" =
    api.parseUtcIso8601 "2026-11-14T18:15:00Z")
  NondetTest.assert (api.parseUtcIso8601 "2026-11-14T12:45:00-05:30" =
    api.parseUtcIso8601 "2026-11-14T18:15:00Z")

/-- Every `parseUtcIso8601` failure carries `.invalidFormat` and a non-empty message, and malformed inputs (empty, invalid calendar day, missing timezone, or out-of-range hour) are rejected. -/
def test_time_utcIso8601_invalidReturnsNonEmptyError
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let raw ← nondet String
  match api.parseUtcIso8601 raw with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "")
  NondetTest.assert ((api.parseUtcIso8601 "").isOk = false)
  NondetTest.assert ((api.parseUtcIso8601 "2024-02-30T00:00:00Z").isOk = false)
  NondetTest.assert ((api.parseUtcIso8601 "2026-11-14T18:15:00").isOk = false)
  NondetTest.assert ((api.parseUtcIso8601 "2026-11-14T25:00:00Z").isOk = false)

/-- Formatting any 4-digit year (`0000`..`9999`) `PlainDate` as `YYYY-MM-DD` and parsing it back yields the exact `PlainDate`. -/
def test_time_utcDate_roundTrip
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let d ← nondet Std.Time.PlainDate
  assume (0 ≤ d.year.toInt ∧ d.year.toInt ≤ 9999)
  let s := api.formatUtcDate d
  NondetTest.assert (api.parseUtcDate s = .ok d)

/-- Every `parseUtcDate` failure carries `.invalidFormat` and a non-empty message, and malformed dates (empty, invalid leap day, invalid month, slash separator, or trailing junk) are rejected. -/
def test_time_utcDate_invalidReturnsNonEmptyError
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let raw ← nondet String
  match api.parseUtcDate raw with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "")
  NondetTest.assert ((api.parseUtcDate "").isOk = false)
  NondetTest.assert ((api.parseUtcDate "2024-02-30").isOk = false)
  NondetTest.assert ((api.parseUtcDate "2026-13-01").isOk = false)
  NondetTest.assert ((api.parseUtcDate "2026/11/14").isOk = false)
  NondetTest.assert ((api.parseUtcDate "2026-11-14Z").isOk = false)

/-- Converting any `PlainDate` to UTC midnight `Timestamp` and back recovers the same `PlainDate`, and timestamps 1 ns before midnight belong to an earlier UTC day. -/
def test_time_utcDate_timestampRoundTrip
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let d ← nondet Std.Time.PlainDate
  let midnight := api.timestampOfUtcDate d
  NondetTest.assert (api.utcDateOfTimestamp midnight = d)
  NondetTest.assert (compare (api.utcDateOfTimestamp (midnight - Std.Time.Duration.ofNanoseconds 1)) d = .lt)

/-- `formatUtcCompact` emits 16-char `YYYYMMDDTHHMMSSZ` strings matching the exact date and time digits of `formatUtcIso8601` for 4-digit UTC years (`0000`..`9999`). -/
def test_time_utcCompact_formatShape
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let ts ← nondet Std.Time.Timestamp
  assume (-62167219200000000000 ≤ ts.toNanosecondsSinceUnixEpoch.val ∧
    ts.toNanosecondsSinceUnixEpoch.val ≤ 253402300799999999999)
  let cs := (api.formatUtcCompact ts).toList
  let iso := (api.formatUtcIso8601 ts).toList
  let expected :=
    iso.take 4 ++ (iso.drop 5).take 2 ++ (iso.drop 8).take 2 ++ ['T'] ++
    (iso.drop 11).take 2 ++ (iso.drop 14).take 2 ++ (iso.drop 17).take 2 ++ ['Z']
  NondetTest.assert (cs.length = 16 ∧ cs = expected)

/-- `mkTimeOps` reads `CLOCK_REALTIME` (including pre-1970 negative `sec`) into `Std.Time.Timestamp` and `CLOCK_MONOTONIC` into `Nat` nanoseconds, falling back cleanly to `0` on syscall error. -/
def test_time_mkTimeOps_readsRealtimeAndMonotonic
    {runner} [NondetTest runner]
    (mkOps : TimeRandOpsM Id → TimeOpsM Id) : runner Unit := do
  let realTs ← nondet Timespec
  let monoTs ← nondet Timespec
  let errCode ← nondet Errno
  assume (monoTs.isValid = true)
  let okSys : TimeRandOpsM Id :=
    { clock_gettime := fun
        | .realtime => .ok realTs
        | .monotonic => .ok monoTs
      clock_nanosleep := fun _ _ _ => .ok ()
      getrandom := fun _ _ => .ok ByteArray.empty }
  let opsOk := mkOps okSys
  NondetTest.assert (opsOk.nowTimestamp =
    Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
      (Std.Time.Nanosecond.Offset.ofInt realTs.toEpochNanos))
  NondetTest.assert (opsOk.monoNanosNow = monoTs.toNanosNat)
  let errSys : TimeRandOpsM Id :=
    { clock_gettime := fun _ => .error errCode
      clock_nanosleep := fun _ _ _ => .error errCode
      getrandom := fun _ _ => .error errCode }
  let opsErr := mkOps errSys
  NondetTest.assert (opsErr.nowTimestamp = Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
  NondetTest.assert (opsErr.monoNanosNow = 0)

/-- Over `TimeRand.modelOps`, `(mkOpsTrace sys).sleep 0` performs zero syscalls and `(mkApiFn (mkOpsModel modelOps)).sleepMs ms` / `measure` advance monotonic nanoseconds by exact `ms * 1_000_000` (including multi-chunk `ms > UInt32.max`). -/
def test_time_mkTimeOps_sleepZeroAndModelSleepMs
    {runner} [NondetTest runner]
    (mkOpsTrace : TimeRandOpsM (StateM SleepTraceState) → TimeOpsM (StateM SleepTraceState))
    (mkOpsModel : TimeRandOpsM (StateM TimeRandState) → TimeOpsM (StateM TimeRandState))
    (mkApiFn : TimeOpsM (StateM TimeRandState) → TimeApiM (StateM TimeRandState)) : runner Unit := do
  let traceInit ← nondet SleepTraceState
  let s₀ ← nondet TimeRandState
  let ms ← nondet Nat
  assume (s₀.monoLowerBoundNs + ms * 1000000 ≤ MAX_TIMESPEC_NANOS)
  let ((), traceAfterZero) := ((mkOpsTrace (scriptedSleepSysOps)).sleep 0).run traceInit
  NondetTest.assert (traceAfterZero.gettimeCalls = traceInit.gettimeCalls ∧
    traceAfterZero.nanosleepLog = traceInit.nanosleepLog)
  let api := mkApiFn (mkOpsModel LeanSwe.LinuxSyscall.TimeRand.modelOps)
  let ((val, elapsed), s₁) := (api.measure (do api.sleepMs ms; pure ms)).run s₀
  NondetTest.assert (val = ms)
  NondetTest.assert (s₁.monoLowerBoundNs = s₀.monoLowerBoundNs + ms * 1000000)
  NondetTest.assert (elapsed = Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofNat ms))

/-- `(mkOps sys).sleep ms` (`ms > 0`) computes the `TIMER_ABSTIME` monotonic deadline once, retries `Errno.EINTR` without deadline drift, stops after 1 call on non-`EINTR` errnos, terminates within `MAX_EINTR_RETRIES + 1` attempts under persistent `EINTR`, and falls back to a single relative `clock_nanosleep .monotonic false` of `ms * 1_000_000` ns when `clock_gettime` fails, returns negative `sec`, or overflows `MAX_TIMESPEC_NANOS`. -/
def test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift
    {runner} [NondetTest runner]
    (mkOps : TimeRandOpsM (StateM SleepTraceState) → TimeOpsM (StateM SleepTraceState)) : runner Unit := do
  let startMono ← nondet Timespec
  let ms ← nondet UInt32
  let eintrCount ← nondet Nat
  let fatalErr ← nondet Errno
  assume (startMono.isValid = true)
  assume (ms > 0)
  assume (startMono.toNanosNat + ms.toNat * 1000000 ≤ MAX_TIMESPEC_NANOS)
  assume (eintrCount ≤ 4)
  assume (fatalErr ≠ Errno.EINTR)
  let initEintr : SleepTraceState :=
    { monoNow := startMono
      sleepResponses := List.replicate eintrCount (.error Errno.EINTR) ++ [.ok ()] }
  let stAfterEintr := (((mkOps (scriptedSleepSysOps)).sleep ms).run initEintr).2
  NondetTest.assert (stAfterEintr.gettimeCalls = 1)
  NondetTest.assert (stAfterEintr.nanosleepLog.length = eintrCount + 1)
  NondetTest.assert (stAfterEintr.nanosleepLog.all (fun (clk, abs, req) =>
    clk == .monotonic && abs == true && req.isValid &&
    req.toNanosNat == startMono.toNanosNat + ms.toNat * 1000000) = true)
  let initFatal : SleepTraceState :=
    { monoNow := startMono
      sleepResponses := [.error fatalErr, .ok ()] }
  let stAfterFatal := (((mkOps (scriptedSleepSysOps)).sleep ms).run initFatal).2
  NondetTest.assert (stAfterFatal.gettimeCalls = 1 ∧ stAfterFatal.nanosleepLog.length = 1)
  let initStorm : SleepTraceState := { monoNow := startMono }
  let stAfterStorm := (((mkOps (scriptedSleepSysOps (.error Errno.EINTR))).sleep ms).run initStorm).2
  NondetTest.assert (stAfterStorm.gettimeCalls = 1 ∧
    stAfterStorm.nanosleepLog.length = MAX_EINTR_RETRIES + 1)
  let isExpectedRelCall : ClockId × Bool × Timespec → Bool := fun (clk, abs, req) =>
    clk == .monotonic && abs == false && req.isValid && req.toNanosNat == ms.toNat * 1000000
  let initGetErr : SleepTraceState :=
    { gettimeErr? := some fatalErr
      sleepResponses := [.error Errno.EINTR, .ok ()] }
  let stAfterGetErr := (((mkOps (scriptedSleepSysOps)).sleep ms).run initGetErr).2
  NondetTest.assert (stAfterGetErr.gettimeCalls = 1 ∧ stAfterGetErr.nanosleepLog.length = 1 ∧
    stAfterGetErr.nanosleepLog.all isExpectedRelCall = true)
  let initOverflow : SleepTraceState :=
    { monoNow := { sec := 9223372036854775807, nsec := 999999999 }
      sleepResponses := [.error Errno.EINTR, .ok ()] }
  let stAfterOverflow := (((mkOps (scriptedSleepSysOps)).sleep ms).run initOverflow).2
  NondetTest.assert (stAfterOverflow.gettimeCalls = 1 ∧ stAfterOverflow.nanosleepLog.length = 1 ∧
    stAfterOverflow.nanosleepLog.all isExpectedRelCall = true)
  let initNegSec : SleepTraceState :=
    { monoNow := { sec := -1, nsec := 0 }
      sleepResponses := [.error Errno.EINTR, .ok ()] }
  let stAfterNegSec := (((mkOps (scriptedSleepSysOps)).sleep ms).run initNegSec).2
  NondetTest.assert (stAfterNegSec.gettimeCalls = 1 ∧ stAfterNegSec.nanosleepLog.length = 1 ∧
    stAfterNegSec.nanosleepLog.all isExpectedRelCall = true)

/-- Declared error-coverage matrix for pure helper package `LeanSwe.Time` (`TimeErrorKind`, covering `parseUtcIso8601` and `parseUtcDate`). -/
def errorCoverage : List (ErrorObligation TimeErrorKind) :=
  [ { request := "LeanSwe.Time.parseUtcIso8601"
      errorKind := .invalidFormat
      justification := .tested "LeanSwe.Time.RuntimeTests.err_time_parseUtcIso8601_invalidFormat" .real }
  , { request := "LeanSwe.Time.parseUtcDate"
      errorKind := .invalidFormat
      justification := .tested "LeanSwe.Time.RuntimeTests.err_time_parseUtcDate_invalidFormat" .real } ]

end LeanSwe.Time
