import Core.NondetTest
import LeanSwe.Time.Types

namespace LeanSwe.Time

open Core (NondetTest)
open Core.NondetTest

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

/-- Empirical contract (grounded in `RuntimeTests.lean`): formatting any 4-digit UTC year (`0000`..`9999`) `Timestamp` as ISO 8601 and parsing it back yields the exact `Timestamp`. -/
def empirical_time_utcIso8601_roundTrip
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let ts ← nondet Std.Time.Timestamp
  assume (-62167219200000000000 ≤ ts.toNanosecondsSinceUnixEpoch.val ∧
    ts.toNanosecondsSinceUnixEpoch.val ≤ 253402300799999999999)
  let s := api.formatUtcIso8601 ts
  NondetTest.assert (api.parseUtcIso8601 s = .ok ts)

/-- Empirical contract (grounded in `RuntimeTests.lean`): `parseUtcIso8601` returns `.error` with a non-empty message on invalid input. -/
def empirical_time_utcIso8601_invalidReturnsNonEmptyError
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let raw ← nondet String
  match api.parseUtcIso8601 raw with
  | .ok _ => assume False
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "")

/-- Empirical contract (grounded in `RuntimeTests.lean`): formatting any 4-digit year (`0000`..`9999`) `PlainDate` as `YYYY-MM-DD` and parsing it back yields the exact `PlainDate`. -/
def empirical_time_utcDate_roundTrip
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let d ← nondet Std.Time.PlainDate
  assume (0 ≤ d.year.toInt ∧ d.year.toInt ≤ 9999)
  let s := api.formatUtcDate d
  NondetTest.assert (api.parseUtcDate s = .ok d)

/-- Empirical contract (grounded in `RuntimeTests.lean`): `parseUtcDate` returns `.error` with `.invalidFormat` and a non-empty message on invalid input. -/
def empirical_time_utcDate_invalidReturnsNonEmptyError
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let raw ← nondet String
  match api.parseUtcDate raw with
  | .ok _ => assume False
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "")

/-- Empirical contract (grounded in `RuntimeTests.lean`): converting any `PlainDate` to UTC midnight `Timestamp` and back recovers the same `PlainDate`, and timestamps strictly before midnight belong to an earlier UTC day. -/
def empirical_time_utcDate_timestampRoundTrip
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let d ← nondet Std.Time.PlainDate
  let midnight := api.timestampOfUtcDate d
  NondetTest.assert (api.utcDateOfTimestamp midnight = d)
  NondetTest.assert (compare (api.utcDateOfTimestamp (midnight - Std.Time.Duration.ofNanoseconds 1)) d = .lt)

/-- Empirical contract (grounded in `RuntimeTests.lean`): `formatUtcCompact` emits 16-char `YYYYMMDDTHHMMSSZ` strings for 4-digit UTC years (`0000`..`9999`). -/
def empirical_time_utcCompact_formatShape
    {runner} [NondetTest runner] (api : TimeApi) : runner Unit := do
  let ts ← nondet Std.Time.Timestamp
  assume (-62167219200000000000 ≤ ts.toNanosecondsSinceUnixEpoch.val ∧
    ts.toNanosecondsSinceUnixEpoch.val ≤ 253402300799999999999)
  let s := api.formatUtcCompact ts
  NondetTest.assert (s.length = 16 ∧ s.endsWith "Z" = true)

private def stubTimeApiAt {m : Type → Type} [Monad m] : TimeApiM m :=
  { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
    monoNanosNow := pure 0
    sleepMs := fun _ => pure ()
    sleepDuration := fun _ => pure ()
    measure := fun act => do
      let a ← act
      pure (a, 0)
    elapsedDuration := fun _ _ => 0
    deadlineNanos := fun start _ => start
    isMonoExpired := fun _ _ => false
    formatUtcIso8601 := fun _ => ""
    parseUtcIso8601 := fun _ => .error { kind := .invalidFormat, message := "stub" }
    formatUtcCompact := fun _ => ""
    formatUtcDate := fun _ => ""
    parseUtcDate := fun _ => .error { kind := .invalidFormat, message := "stub" }
    utcDateOfTimestamp := fun _ => Std.Time.PlainDate.ofEpochDay 0
    timestampOfUtcDate := fun _ => Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0 }

example : ¬ Core.AllPass (test_time_mono_deadlineAndElapsed stubTimeApiAt) := by
  intro h
  have h0 := h 10 (Std.Time.Duration.ofSeconds 5) 20 20
  dsimp [test_time_mono_deadlineAndElapsed, Core.NondetTest.assert, Bind.bind, stubTimeApiAt] at h0
  exact absurd h0.1 (by decide)

private def buggyExpiredEqOnlyApi : TimeApi :=
  { stubTimeApiAt with
    deadlineNanos := fun start limit =>
      if limit.toNanoseconds.val ≥ 0 then start + limit.toNanoseconds.val.toNat else start
    isMonoExpired := fun nowMono dl => nowMono == dl }

example : ¬ Core.AllPass (test_time_mono_deadlineAndElapsed buggyExpiredEqOnlyApi) := by
  intro h
  have h0 := h 10 (Std.Time.Duration.ofSeconds 5) 5000000020 20
  dsimp [test_time_mono_deadlineAndElapsed, Core.NondetTest.assert, Bind.bind, buggyExpiredEqOnlyApi] at h0
  exact absurd h0.2.1 (by decide)

private def buggySleepTruncatesUInt32Api : TimeApiM (StateM FakeClock) :=
  { (stubTimeApiAt (m := StateM FakeClock)) with
    nowTimestamp := do
      let s ← get
      pure s.wall
    monoNanosNow := do
      let s ← get
      pure s.monoNanos
    sleepMs := fun ms => do
      let c := UInt32.ofNat ms
      modify fun s =>
        { wall := s.wall + Std.Time.Duration.ofMillisecond (Std.Time.Millisecond.Offset.ofNat c.toNat)
          monoNanos := s.monoNanos + c.toNat * 1000000
          sleepLog := s.sleepLog.push c } }

example : ¬ Core.AllPass (test_time_fakeClock_sleepMs_advancesAndChunks buggySleepTruncatesUInt32Api) := by
  intro h
  have h0 := h ⟨0, 0, #[]⟩ 4294967296
  dsimp [test_time_fakeClock_sleepMs_advancesAndChunks, buggySleepTruncatesUInt32Api,
    Core.NondetTest.assert, Bind.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, StateT.pure] at h0
  exact absurd h0.1 (by decide)

private def buggySleepDurationNegApi : TimeApiM (StateM FakeClock) :=
  { (stubTimeApiAt (m := StateM FakeClock)) with
    sleepDuration := fun _ =>
      modify fun s => { s with monoNanos := s.monoNanos + 1000000 } }

example : ¬ Core.AllPass (test_time_fakeClock_sleepDuration_clampsAndRoundsUp buggySleepDurationNegApi) := by
  intro h
  have h0 := h ⟨0, 0, #[]⟩ (Std.Time.Duration.ofSeconds (-1))
  dsimp [test_time_fakeClock_sleepDuration_clampsAndRoundsUp, buggySleepDurationNegApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_time_fakeClock_measure_returnsValueAndElapsed stubTimeApiAt) := by
  intro h
  have h0 := h ⟨0, 0, #[]⟩ 5
  simp [stubTimeApiAt, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_time_fakeClock_nowTimestamp_readsWithoutMutating stubTimeApiAt) := by
  intro h
  have h0 := h ⟨Std.Time.Timestamp.ofSecondsSinceUnixEpoch 42, 0, #[]⟩
  simp [stubTimeApiAt, StateT.run, pure, StateT.pure, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_time_fakeClock_monoNanosNow_readsWithoutMutating stubTimeApiAt) := by
  intro h
  have h0 := h ⟨0, 77, #[]⟩
  simp [stubTimeApiAt, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (empirical_time_utcIso8601_roundTrip stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) (by decide)
  simp [stubTimeApiAt, assert] at h0

example : ¬ Core.AllPass (empirical_time_utcIso8601_invalidReturnsNonEmptyError
    { stubTimeApiAt with parseUtcIso8601 := fun _ => .error { kind := .invalidFormat, message := "" } }) := by
  intro h
  have h0 := h "bad"
  simp [assert] at h0

example : ¬ Core.AllPass (empirical_time_utcDate_roundTrip stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.PlainDate.ofEpochDay 0) (by decide)
  simp [stubTimeApiAt, assert] at h0

example : ¬ Core.AllPass (empirical_time_utcDate_invalidReturnsNonEmptyError
    { stubTimeApiAt with parseUtcDate := fun _ => .error { kind := .invalidFormat, message := "" } }) := by
  intro h
  have h0 := h "bad"
  simp [assert] at h0

example : ¬ Core.AllPass (empirical_time_utcDate_timestampRoundTrip stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.PlainDate.ofEpochDay 1)
  simp [stubTimeApiAt, assert] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (empirical_time_utcCompact_formatShape stubTimeApiAt) := by
  intro h
  have h0 := h (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) (by decide)
  simp [stubTimeApiAt, assert] at h0

end LeanSwe.Time
