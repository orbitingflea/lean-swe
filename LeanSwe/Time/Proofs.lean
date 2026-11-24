import LeanSwe.Time.Interface
import LeanSwe.Time.Model
import LeanSwe.Time.SpecTests
import LeanSwe.Time.Proofs.EpochBaseProofs
import LeanSwe.Time.Proofs.HinnantProofs
import LeanSwe.Time.Proofs.HinnantRoundTripProofs
import LeanSwe.Time.Proofs.HinnantRangeProofs
import LeanSwe.Time.Proofs.CalendarProofs
import LeanSwe.Time.Proofs.FormatParseProofs
import LeanSwe.Time.Proofs.SleepOpsProofs
import LeanSwe.Time.Proofs.FakeClockProofs
import LeanSwe.Time.Proofs.RefinesModel

namespace LeanSwe.Time.Proofs

open Core
open Core.NondetTest
open Std.Time
open LeanSwe.Time.SleepModelProofs (toNanoseconds_ofNanoseconds toNanoseconds_inj)

private theorem toNanoseconds_neg (d : Duration) :
    d.neg.toNanoseconds.val = -d.toNanoseconds.val := by
  rcases d with ⟨⟨s⟩, ⟨n, _⟩, _⟩
  change (-s) * 1000000000 + (-n) = -(s * 1000000000 + n)
  omega

private theorem toNanoseconds_add (a b : Duration) :
    (a + b).toNanoseconds.val = a.toNanoseconds.val + b.toNanoseconds.val := by
  change (Duration.ofNanoseconds (a.toNanoseconds + b.toNanoseconds)).toNanoseconds.val = _
  rw [toNanoseconds_ofNanoseconds]
  rfl

private theorem toNanoseconds_sub (a b : Duration) :
    (a - b).toNanoseconds.val = a.toNanoseconds.val - b.toNanoseconds.val := by
  change (Duration.ofNanoseconds (a.toNanoseconds + b.neg.toNanoseconds)).toNanoseconds.val = _
  rw [toNanoseconds_ofNanoseconds]
  have h := toNanoseconds_neg b
  change a.toNanoseconds.val + b.neg.toNanoseconds.val = a.toNanoseconds.val - b.toNanoseconds.val
  omega

private theorem bounded_ediv_val {lo hi : Int} (b : Internal.Bounded.LE lo hi)
    (num : Int) (h : num > 0) :
    (b.ediv num h).val = b.val.ediv num := by
  rcases b with ⟨v, ⟨hl, hr⟩⟩
  simp [Internal.Bounded.LE.ediv]

private theorem toMilliseconds_ofMillisecond (ms : Millisecond.Offset) :
    (Duration.ofMillisecond ms).toMilliseconds = ms := by
  apply Internal.UnitVal.ext
  have hval : (Duration.ofMillisecond ms).toNanoseconds.val = ms.val * 1000000 := by
    change (Duration.ofNanoseconds ms.toNanoseconds).toNanoseconds.val = ms.val * 1000000
    rw [toNanoseconds_ofNanoseconds]
    rfl
  generalize Duration.ofMillisecond ms = d at hval ⊢
  rcases d with ⟨sec, nsec, hsign⟩
  change sec.val * 1000000000 + nsec.val = ms.val * 1000000 at hval
  have hed_val : (nsec.ediv 1000000 (by decide)).val = nsec.val.ediv 1000000 :=
    bounded_ediv_val nsec 1000000 (by decide)
  have hmsec : (Duration.mk sec nsec hsign).toMilliseconds.val =
      sec.val * 1000 + nsec.val.ediv 1000000 :=
    Eq.trans
      (rfl : (Duration.mk sec nsec hsign).toMilliseconds.val =
        sec.val * 1000 + (nsec.ediv 1000000 (by decide)).val)
      (congrArg (sec.val * 1000 + ·) hed_val)
  refine Eq.trans hmsec ?_
  have hdiv : nsec.val.ediv 1000000 = nsec.val / 1000000 := rfl
  have hed : 1000000 * (nsec.val / 1000000) + nsec.val % 1000000 = nsec.val :=
    Int.mul_ediv_add_emod nsec.val 1000000
  have hn' := nsec.property
  omega

/-- Proof of `test_time_duration_addSubInverse`. -/
theorem proof_time_duration_addSubInverse :
    AllPass test_time_duration_addSubInverse := by
  intro d1 d2
  simp only [assert]
  refine ⟨?_, trivial⟩
  apply toNanoseconds_inj
  apply Internal.UnitVal.ext
  rw [toNanoseconds_sub, toNanoseconds_add]
  omega

/-- Non-vacuity `CanReach` witness for `test_time_duration_addSubInverse`. -/
theorem reach_time_duration_addSubInverse :
    CanReach test_time_duration_addSubInverse :=
  ⟨0, 0, proof_time_duration_addSubInverse 0 0⟩

/-- Proof of `test_time_timestamp_addSubInverse`. -/
theorem proof_time_timestamp_addSubInverse :
    AllPass test_time_timestamp_addSubInverse := by
  intro t d
  simp only [assert]
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · apply Timestamp.ext
    apply toNanoseconds_inj
    apply Internal.UnitVal.ext
    change ((t.val + d) - d).toNanoseconds.val = t.val.toNanoseconds.val
    rw [toNanoseconds_sub, toNanoseconds_add]
    omega
  · apply toNanoseconds_inj
    apply Internal.UnitVal.ext
    change ((t.val + d) - t.val).toNanoseconds.val = d.toNanoseconds.val
    rw [toNanoseconds_sub, toNanoseconds_add]
    omega

/-- Non-vacuity `CanReach` witness for `test_time_timestamp_addSubInverse`. -/
theorem reach_time_timestamp_addSubInverse :
    CanReach test_time_timestamp_addSubInverse :=
  ⟨0, 0, proof_time_timestamp_addSubInverse 0 0⟩

/-- Proof of `test_time_timestamp_le_iff_diffNonneg`. -/
theorem proof_time_timestamp_le_iff_diffNonneg :
    AllPass test_time_timestamp_le_iff_diffNonneg := by
  intro t1 t2
  simp only [assert]
  refine ⟨?_, trivial⟩
  change t1.val.toNanoseconds.val ≤ t2.val.toNanoseconds.val ↔
    (0 : Duration).toNanoseconds.val ≤ (t2.val - t1.val).toNanoseconds.val
  rw [toNanoseconds_sub]
  have hz : (0 : Duration).toNanoseconds.val = 0 := by decide
  omega

/-- Non-vacuity `CanReach` witness for `test_time_timestamp_le_iff_diffNonneg`. -/
theorem reach_time_timestamp_le_iff_diffNonneg :
    CanReach test_time_timestamp_le_iff_diffNonneg :=
  ⟨0, 0, proof_time_timestamp_le_iff_diffNonneg 0 0⟩

/-- Proof of `test_time_duration_msRoundTrip`. -/
theorem proof_time_duration_msRoundTrip :
    AllPass test_time_duration_msRoundTrip := by
  intro ms
  simp only [assert]
  refine ⟨?_, trivial⟩
  exact congrArg Internal.UnitVal.val (toMilliseconds_ofMillisecond (Millisecond.Offset.ofInt ms))

/-- Non-vacuity `CanReach` witness for `test_time_duration_msRoundTrip`. -/
theorem reach_time_duration_msRoundTrip :
    CanReach test_time_duration_msRoundTrip :=
  ⟨0, proof_time_duration_msRoundTrip 0⟩

/-- Proof of `test_time_mono_deadlineAndElapsed` for `defaultApi`. -/
theorem proof_time_mono_deadlineAndElapsed :
    AllPass (test_time_mono_deadlineAndElapsed defaultApi) := by
  intro startMono limit nowMono stopMono
  dsimp [test_time_mono_deadlineAndElapsed, defaultApi, Internal.mkApiM,
    Internal.deadlineNanos, Internal.isMonoExpired, Internal.elapsedDuration,
    Core.NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, ?_, trivial⟩
  split <;> rfl

/-- Non-vacuity `CanReach` witness for `test_time_mono_deadlineAndElapsed` on `defaultApi`. -/
theorem reach_time_mono_deadlineAndElapsed :
    CanReach (test_time_mono_deadlineAndElapsed defaultApi) :=
  ⟨0, 0, 0, 0, proof_time_mono_deadlineAndElapsed 0 0 0 0⟩

/-- Proof of `test_time_fakeClock_nowTimestamp_readsWithoutMutating` for `Internal.fakeApi`. -/
theorem proof_time_fakeClock_nowTimestamp_readsWithoutMutating :
    AllPass (test_time_fakeClock_nowTimestamp_readsWithoutMutating Internal.fakeApi) :=
  LeanSwe.Time.FakeClockProofs.fakeClock_nowTimestamp_readsWithoutMutating_impl

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_nowTimestamp_readsWithoutMutating`. -/
theorem reach_time_fakeClock_nowTimestamp_readsWithoutMutating :
    CanReach (test_time_fakeClock_nowTimestamp_readsWithoutMutating Internal.fakeApi) :=
  ⟨default, proof_time_fakeClock_nowTimestamp_readsWithoutMutating default⟩

/-- Proof of `test_time_fakeClock_monoNanosNow_readsWithoutMutating` for `Internal.fakeApi`. -/
theorem proof_time_fakeClock_monoNanosNow_readsWithoutMutating :
    AllPass (test_time_fakeClock_monoNanosNow_readsWithoutMutating Internal.fakeApi) :=
  LeanSwe.Time.FakeClockProofs.fakeClock_monoNanosNow_readsWithoutMutating_impl

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_monoNanosNow_readsWithoutMutating`. -/
theorem reach_time_fakeClock_monoNanosNow_readsWithoutMutating :
    CanReach (test_time_fakeClock_monoNanosNow_readsWithoutMutating Internal.fakeApi) :=
  ⟨default, proof_time_fakeClock_monoNanosNow_readsWithoutMutating default⟩

/-- Proof of `test_time_fakeClock_sleepMs_advancesAndChunks` for `Internal.fakeApi`. -/
theorem proof_time_fakeClock_sleepMs_advancesAndChunks :
    AllPass (test_time_fakeClock_sleepMs_advancesAndChunks Internal.fakeApi) :=
  LeanSwe.Time.FakeClockProofs.fakeClock_sleepMs_advancesAndChunks_impl

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_sleepMs_advancesAndChunks`. -/
theorem reach_time_fakeClock_sleepMs_advancesAndChunks :
    CanReach (test_time_fakeClock_sleepMs_advancesAndChunks Internal.fakeApi) :=
  ⟨default, 5, proof_time_fakeClock_sleepMs_advancesAndChunks default 5⟩

/-- Proof of `test_time_fakeClock_sleepDuration_clampsAndRoundsUp` for `Internal.fakeApi`. -/
theorem proof_time_fakeClock_sleepDuration_clampsAndRoundsUp :
    AllPass (test_time_fakeClock_sleepDuration_clampsAndRoundsUp Internal.fakeApi) :=
  LeanSwe.Time.FakeClockProofs.fakeClock_sleepDuration_clampsAndRoundsUp_impl

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_sleepDuration_clampsAndRoundsUp`. -/
theorem reach_time_fakeClock_sleepDuration_clampsAndRoundsUp :
    CanReach (test_time_fakeClock_sleepDuration_clampsAndRoundsUp Internal.fakeApi) :=
  ⟨default, Duration.ofMillisecond 5,
    proof_time_fakeClock_sleepDuration_clampsAndRoundsUp default (Duration.ofMillisecond 5)⟩

/-- Proof of `test_time_fakeClock_measure_returnsValueAndElapsed` for `Internal.fakeApi`. -/
theorem proof_time_fakeClock_measure_returnsValueAndElapsed :
    AllPass (test_time_fakeClock_measure_returnsValueAndElapsed Internal.fakeApi) :=
  LeanSwe.Time.FakeClockProofs.fakeClock_measure_returnsValueAndElapsed_impl

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_measure_returnsValueAndElapsed`. -/
theorem reach_time_fakeClock_measure_returnsValueAndElapsed :
    CanReach (test_time_fakeClock_measure_returnsValueAndElapsed Internal.fakeApi) :=
  ⟨default, 5, proof_time_fakeClock_measure_returnsValueAndElapsed default 5⟩

private theorem parseDateHead_2026_11_14 (rest : List Char) :
    Internal.parseDateHead ('2' :: '0' :: '2' :: '6' :: '-' :: '1' :: '1' :: '-' :: '1' :: '4' :: rest) =
      .ok (PlainDate.ofEpochDay (Day.Offset.ofInt 20771), rest) := by
  have hfmt : Internal.formatUtcDateChars (PlainDate.ofEpochDay (Day.Offset.ofInt 20771)) =
      ['2', '0', '2', '6', '-', '1', '1', '-', '1', '4'] := by decide
  have hlo : (0 : Int) ≤ (PlainDate.ofEpochDay (Day.Offset.ofInt 20771)).year.toInt := by decide
  have hhi : (PlainDate.ofEpochDay (Day.Offset.ofInt 20771)).year.toInt ≤ 9999 := by decide
  simpa [hfmt] using
    parseDateHead_formatUtcDateChars (PlainDate.ofEpochDay (Day.Offset.ofInt 20771)) hlo hhi rest

/-- Proof of `test_time_utcIso8601_roundTrip` for `defaultApi`. -/
theorem proof_time_utcIso8601_roundTrip :
    AllPass (test_time_utcIso8601_roundTrip defaultApi) := by
  intro ts hbound
  dsimp [test_time_utcIso8601_roundTrip, defaultApi, Internal.mkApiM,
    Internal.formatUtcIso8601, Internal.utcSplitTimestamp,
    Core.NondetTest.assert, Bind.bind, Except.bind]
  have hparse : Internal.parseUtcIso8601 (String.ofList (Internal.formatUtcDateChars
      (PlainDate.ofEpochDay (Day.Offset.ofInt ((ts.toNanosecondsSinceUnixEpoch.val.ediv 1000000000).ediv 86400))) ++
      'T' :: Internal.twoDigitsChars (((ts.toNanosecondsSinceUnixEpoch.val.ediv 1000000000).emod 86400).toNat / 3600) ++
      ':' :: Internal.twoDigitsChars ((((ts.toNanosecondsSinceUnixEpoch.val.ediv 1000000000).emod 86400).toNat % 3600) / 60) ++
      ':' :: Internal.twoDigitsChars (((ts.toNanosecondsSinceUnixEpoch.val.ediv 1000000000).emod 86400).toNat % 60) ++
      '.' :: Internal.nineDigitsChars (ts.toNanosecondsSinceUnixEpoch.val.emod 1000000000).toNat ++ ['Z'])) = .ok ts := by
    let ns := ts.toNanosecondsSinceUnixEpoch.val
    let sec := ns.ediv 1000000000
    let nano := (ns.emod 1000000000).toNat
    let day := sec.ediv 86400
    let sod := (sec.emod 86400).toNat
    have hns_b : -62167219200000000000 ≤ ns ∧ ns ≤ 253402300799999999999 := hbound
    have hsec_e : sec = ns / 1000000000 := rfl
    have hday_e : day = (ns / 1000000000) / 86400 := rfl
    have hday_lo : -719528 ≤ day := by rw [hday_e]; omega
    have hday_hi : day ≤ 2932896 := by rw [hday_e]; omega
    have hy_range := ofEpochDay_year_range (Day.Offset.ofInt day) hday_lo hday_hi
    dsimp [Internal.parseUtcIso8601, Bind.bind, Except.bind]
    rw [String.toList_ofList]
    simp only [List.append_assoc, List.cons_append]
    rw [parseDateHead_formatUtcDateChars _ hy_range.1 hy_range.2]
    dsimp [Internal.pop1?]
    have hsod_e : sod = ((ns / 1000000000) % 86400).toNat := rfl
    have hsod_b : sod < 86400 := by rw [hsod_e]; omega
    have hhh : sod / 3600 < 24 := by omega
    have hmm : (sod % 3600) / 60 < 60 := by omega
    have hss : sod % 60 < 60 := by omega
    rw [popTwoDigitsNat?_twoDigitsChars (sod / 3600) (by omega)]
    dsimp [Internal.pop1?]
    rw [popTwoDigitsNat?_twoDigitsChars ((sod % 3600) / 60) (by omega)]
    dsimp [Internal.pop1?]
    rw [popTwoDigitsNat?_twoDigitsChars (sod % 60) (by omega)]
    dsimp
    have hrange_ok : (sod / 3600 ≤ 23 && (sod % 3600) / 60 ≤ 59 && sod % 60 ≤ 59) = true := by
      simp [show sod / 3600 ≤ 23 by omega, show (sod % 3600) / 60 ≤ 59 by omega, show sod % 60 ≤ 59 by omega]
    simp only [hrange_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [splitLeadingDigits_nineDigitsChars nano ['Z'] (by decide)]
    dsimp
    have hlen : (Internal.nineDigitsChars nano).isEmpty = false ∧ (Internal.nineDigitsChars nano).length ≤ 9 := by
      simp [Internal.nineDigitsChars]
    have hflag : ((Internal.nineDigitsChars nano).isEmpty || decide ((Internal.nineDigitsChars nano).length > 9)) = false := by
      simp [hlen.1, hlen.2]
    simp only [hflag, Bool.false_eq_true, ↓reduceIte]
    have hnano_e : nano = (ns % 1000000000).toNat := rfl
    have hnano_b : nano < 1000000000 := by rw [hnano_e]; omega
    rw [fracDigitsToNanos9_nineDigitsChars nano hnano_b]
    have hoff : Internal.parseOffsetSeconds ['Z'] = .ok 0 := by
      dsimp [Internal.parseOffsetSeconds, Internal.pop1?, List.isEmpty]
    rw [hoff]
    dsimp
    rw [toEpochDay_ofEpochDay (Day.Offset.ofInt day)]
    congr 1
    apply Timestamp.ext
    apply toNanoseconds_inj
    apply Internal.UnitVal.ext
    change (Duration.ofNanoseconds (Nanosecond.Offset.ofInt (((Day.Offset.ofInt day).val * 86400 +
        Int.ofNat (sod / 3600 * 3600 + (sod % 3600) / 60 * 60 + sod % 60) - 0) * 1000000000 +
        Int.ofNat nano))).toNanoseconds.val = ts.toNanosecondsSinceUnixEpoch.val
    rw [toNanoseconds_ofNanoseconds]
    change ((Day.Offset.ofInt day).val * 86400 +
        Int.ofNat (sod / 3600 * 3600 + (sod % 3600) / 60 * 60 + sod % 60) - 0) * 1000000000 +
        Int.ofNat nano = ts.toNanosecondsSinceUnixEpoch.val
    have hday_v : (Day.Offset.ofInt day).val = day := rfl
    rw [hday_v, hday_e, hsod_e, hnano_e]
    dsimp [ns]
    omega
  rw [hparse]
  have hparseZ : Internal.parseUtcIso8601 "2026-11-14T18:15:00Z" =
      .ok (Timestamp.ofNanosecondsSinceUnixEpoch (Nanosecond.Offset.ofInt
          ((Day.Offset.ofInt 20771).val * 86400000000000 + 65700000000000))) := by
    dsimp [Internal.parseUtcIso8601, Bind.bind, Except.bind]
    rw [parseDateHead_2026_11_14]
    dsimp only [Internal.pop1?, Internal.popTwoDigitsNat?, Internal.pop2?, Internal.twoDigitsNat?,
      Internal.isAsciiDigit, Internal.digitVal, Internal.parseOffsetSeconds, List.isEmpty,
      Bind.bind, Except.bind]
    rw [toEpochDay_ofEpochDay (Day.Offset.ofInt 20771)]
    congr 3
  have hplus2 : Internal.parseUtcIso8601 "2026-11-14T20:15:00+02:00" =
      Internal.parseUtcIso8601 "2026-11-14T18:15:00Z" := by
    rw [hparseZ]
    dsimp [Internal.parseUtcIso8601, Bind.bind, Except.bind]
    rw [parseDateHead_2026_11_14]
    dsimp only [Internal.pop1?, Internal.popTwoDigitsNat?, Internal.pop2?, Internal.twoDigitsNat?,
      Internal.isAsciiDigit, Internal.digitVal, Internal.parseOffsetSeconds, List.isEmpty,
      Bind.bind, Except.bind]
    rw [toEpochDay_ofEpochDay (Day.Offset.ofInt 20771)]
    apply congrArg Except.ok
    apply congrArg Timestamp.ofNanosecondsSinceUnixEpoch
    apply congrArg Nanosecond.Offset.ofInt
    have hv : (Day.Offset.ofInt 20771).val = 20771 := rfl
    rw [hv]; decide
  have hminus530 : Internal.parseUtcIso8601 "2026-11-14T12:45:00-05:30" =
      Internal.parseUtcIso8601 "2026-11-14T18:15:00Z" := by
    rw [hparseZ]
    dsimp [Internal.parseUtcIso8601, Bind.bind, Except.bind]
    rw [parseDateHead_2026_11_14]
    dsimp only [Internal.pop1?, Internal.popTwoDigitsNat?, Internal.pop2?, Internal.twoDigitsNat?,
      Internal.isAsciiDigit, Internal.digitVal, Internal.parseOffsetSeconds, List.isEmpty,
      Bind.bind, Except.bind]
    rw [toEpochDay_ofEpochDay (Day.Offset.ofInt 20771)]
    congr 3
  exact ⟨rfl, hplus2, hminus530, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_time_utcIso8601_roundTrip` on `defaultApi`. -/
theorem reach_time_utcIso8601_roundTrip :
    CanReach (test_time_utcIso8601_roundTrip defaultApi) :=
  ⟨Timestamp.ofSecondsSinceUnixEpoch 0, ⟨by decide, by decide⟩,
    proof_time_utcIso8601_roundTrip (Timestamp.ofSecondsSinceUnixEpoch 0) ⟨by decide, by decide⟩⟩

/-- Proof of `test_time_utcIso8601_invalidReturnsNonEmptyError` for `defaultApi`. -/
theorem proof_time_utcIso8601_invalidReturnsNonEmptyError :
    AllPass (test_time_utcIso8601_invalidReturnsNonEmptyError defaultApi) := by
  intro raw
  dsimp [test_time_utcIso8601_invalidReturnsNonEmptyError, defaultApi, Internal.mkApiM,
    Core.NondetTest.assert, Bind.bind]
  cases h : Internal.parseUtcIso8601 raw with
  | ok _ =>
    dsimp; refine ⟨trivial, by decide, by decide, by decide, by decide, trivial⟩
  | error e =>
    dsimp; refine ⟨parseUtcIso8601_err raw h, by decide, by decide, by decide, by decide, trivial⟩

/-- Proof of `test_time_utcDate_roundTrip` for `defaultApi`. -/
theorem proof_time_utcDate_roundTrip :
    AllPass (test_time_utcDate_roundTrip defaultApi) := by
  intro d hbound
  dsimp [test_time_utcDate_roundTrip, defaultApi, Internal.mkApiM,
    Internal.formatUtcDate, Internal.parseUtcDate,
    Core.NondetTest.assert, Bind.bind, Except.bind]
  rw [String.toList_ofList]
  have h1 := parseDateHead_formatUtcDateChars d hbound.1 hbound.2 []
  rw [List.append_nil] at h1
  rw [h1]
  simp

/-- Non-vacuity `CanReach` witness for `test_time_utcDate_roundTrip` on `defaultApi`. -/
theorem reach_time_utcDate_roundTrip :
    CanReach (test_time_utcDate_roundTrip defaultApi) :=
  ⟨default, ⟨by decide, by decide⟩, proof_time_utcDate_roundTrip default ⟨by decide, by decide⟩⟩

/-- Proof of `test_time_utcDate_invalidReturnsNonEmptyError` for `defaultApi`. -/
theorem proof_time_utcDate_invalidReturnsNonEmptyError :
    AllPass (test_time_utcDate_invalidReturnsNonEmptyError defaultApi) := by
  intro raw
  dsimp [test_time_utcDate_invalidReturnsNonEmptyError, defaultApi, Internal.mkApiM,
    Core.NondetTest.assert, Bind.bind]
  cases h : Internal.parseUtcDate raw with
  | ok _ =>
    dsimp; refine ⟨trivial, by decide, by decide, by decide, by decide, by decide, trivial⟩
  | error e =>
    dsimp; refine ⟨parseUtcDate_err raw h, by decide, by decide, by decide, by decide, by decide, trivial⟩

/-- Proof of `test_time_utcDate_timestampRoundTrip` for `defaultApi`. -/
theorem proof_time_utcDate_timestampRoundTrip :
    AllPass (test_time_utcDate_timestampRoundTrip defaultApi) := by
  intro d
  dsimp [test_time_utcDate_timestampRoundTrip, defaultApi, Internal.mkApiM,
    Internal.timestampOfUtcDate, Internal.utcDateOfTimestamp, Internal.utcSplitTimestamp,
    Core.NondetTest.assert, Bind.bind]
  refine ⟨?_, ?_, trivial⟩
  · have hdiv : ((d.toEpochDay.val * 86400000000000).ediv 1000000000).ediv 86400 = d.toEpochDay.val := by
      change ((d.toEpochDay.val * 86400000000000) / 1000000000) / 86400 = d.toEpochDay.val
      omega
    have hts : (Timestamp.ofNanosecondsSinceUnixEpoch
        (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).toNanosecondsSinceUnixEpoch.val =
        d.toEpochDay.val * 86400000000000 :=
      congrArg Internal.UnitVal.val
        (toNanoseconds_ofNanoseconds (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000)))
    rw [hts, hdiv]
    exact ofEpochDay_toEpochDay d
  · let x := PlainDate.ofEpochDay (Day.Offset.ofInt (d.toEpochDay.val - 1))
    have hprev : Internal.utcDateOfTimestamp
        (Internal.timestampOfUtcDate d - Duration.ofNanoseconds 1) = x := by
      dsimp [Internal.utcDateOfTimestamp, Internal.utcSplitTimestamp, Internal.timestampOfUtcDate]
      have hsub : (Timestamp.ofNanosecondsSinceUnixEpoch
          (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000)) -
          Duration.ofNanoseconds 1).toNanosecondsSinceUnixEpoch.val =
          d.toEpochDay.val * 86400000000000 - 1 := by
        have h1 : (Timestamp.ofNanosecondsSinceUnixEpoch
            (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).val.toNanoseconds.val =
            d.toEpochDay.val * 86400000000000 :=
          congrArg Internal.UnitVal.val
            (toNanoseconds_ofNanoseconds (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000)))
        have h2 : (Duration.ofNanoseconds 1).toNanoseconds.val = 1 := by decide
        have h3 := toNanoseconds_sub
          (Timestamp.ofNanosecondsSinceUnixEpoch
            (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).val
          (Duration.ofNanoseconds 1)
        change ((Timestamp.ofNanosecondsSinceUnixEpoch
            (Nanosecond.Offset.ofInt (d.toEpochDay.val * 86400000000000))).val -
            Duration.ofNanoseconds 1).toNanoseconds.val = _
        rw [h3, h1, h2]
      rw [hsub]
      have hdiv : ((d.toEpochDay.val * 86400000000000 - 1).ediv 1000000000).ediv 86400 = d.toEpochDay.val - 1 := by
        change ((d.toEpochDay.val * 86400000000000 - 1) / 1000000000) / 86400 = d.toEpochDay.val - 1
        omega
      rw [hdiv]
    change compare (Internal.utcDateOfTimestamp (Internal.timestampOfUtcDate d - Duration.ofNanoseconds 1)) d = .lt
    rw [hprev]
    have hx_ep : x.toEpochDay.val = d.toEpochDay.val - 1 := by
      dsimp [x]
      rw [toEpochDay_ofEpochDay]
      rfl
    cases hcmp : compare x d with
    | lt => rfl
    | eq =>
      have heq := Std.LawfulEqOrd.eq_of_compare hcmp
      rw [heq] at hx_ep
      omega
    | gt =>
      have hsw : compare d x = (compare x d).swap := Std.OrientedCmp.eq_swap
      have hlt : compare d x = .lt := by rw [hsw, hcmp]; rfl
      have hlt_ep := plainDate_toEpochDay_lt_of_compare_lt hlt
      omega

/-- Proof of `test_time_utcCompact_formatShape` for `defaultApi`. -/
theorem proof_time_utcCompact_formatShape :
    AllPass (test_time_utcCompact_formatShape defaultApi) := by
  intro ts hbound
  dsimp [test_time_utcCompact_formatShape, defaultApi, Internal.mkApiM,
    Internal.formatUtcCompact, Internal.formatUtcIso8601, Internal.utcSplitTimestamp,
    Internal.formatUtcDateChars, Core.NondetTest.assert, Bind.bind]
  let ns := ts.toNanosecondsSinceUnixEpoch.val
  let sec := ns.ediv 1000000000
  let nano := (ns.emod 1000000000).toNat
  let day := sec.ediv 86400
  let sod := (sec.emod 86400).toNat
  have hns_b : -62167219200000000000 ≤ ns ∧ ns ≤ 253402300799999999999 := hbound
  have hday_e : day = (ns / 1000000000) / 86400 := rfl
  have hday_lo : -719528 ≤ day := by rw [hday_e]; omega
  have hday_hi : day ≤ 2932896 := by rw [hday_e]; omega
  have hy_range := ofEpochDay_year_range (Day.Offset.ofInt day) hday_lo hday_hi
  have hfmt_y : Internal.formatYearChars (PlainDate.ofEpochDay (Day.Offset.ofInt day)).year.toInt =
      Internal.fourDigitsChars (PlainDate.ofEpochDay (Day.Offset.ofInt day)).year.toInt.toNat := by
    simp only [Internal.formatYearChars, hy_range.1, hy_range.2, and_self, ↓reduceIte]
  rw [String.toList_ofList, String.toList_ofList, hfmt_y]
  refine ⟨?_, trivial⟩
  simp [Internal.fourDigitsChars, Internal.twoDigitsChars]

/-- Non-vacuity `CanReach` witness for `test_time_utcCompact_formatShape` on `defaultApi`. -/
theorem reach_time_utcCompact_formatShape :
    CanReach (test_time_utcCompact_formatShape defaultApi) :=
  ⟨Timestamp.ofSecondsSinceUnixEpoch 0, ⟨by decide, by decide⟩,
    proof_time_utcCompact_formatShape (Timestamp.ofSecondsSinceUnixEpoch 0) ⟨by decide, by decide⟩⟩

/-- Proof of `test_time_mkTimeOps_readsRealtimeAndMonotonic` for `Internal.mkTimeOps`. -/
theorem proof_time_mkTimeOps_readsRealtimeAndMonotonic :
    AllPass (test_time_mkTimeOps_readsRealtimeAndMonotonic Internal.mkTimeOps) := by
  intro realTs monoTs errCode hmono
  dsimp [test_time_mkTimeOps_readsRealtimeAndMonotonic, Internal.mkTimeOps,
    Pure.pure, Bind.bind, Core.NondetTest.assert]
  have hsec : 0 ≤ monoTs.sec.toInt := by
    dsimp [LeanSwe.LinuxSyscall.TimeRand.Timespec.isValid] at hmono
    simp at hmono; exact hmono.1
  refine ⟨rfl, ?_, rfl, rfl, trivial⟩
  simp [hsec]

/-- Non-vacuity `CanReach` witness for `test_time_mkTimeOps_readsRealtimeAndMonotonic`. -/
theorem reach_time_mkTimeOps_readsRealtimeAndMonotonic :
    CanReach (test_time_mkTimeOps_readsRealtimeAndMonotonic Internal.mkTimeOps) :=
  ⟨{ sec := 0, nsec := 0 }, { sec := 0, nsec := 0 }, LeanSwe.LinuxSyscall.Errno.EIO, by decide,
    proof_time_mkTimeOps_readsRealtimeAndMonotonic { sec := 0, nsec := 0 } { sec := 0, nsec := 0 } LeanSwe.LinuxSyscall.Errno.EIO (by decide)⟩

/-- Proof of `test_time_mkTimeOps_sleepZeroAndModelSleepMs`. -/
theorem proof_time_mkTimeOps_sleepZeroAndModelSleepMs :
    AllPass (test_time_mkTimeOps_sleepZeroAndModelSleepMs Internal.mkTimeOps Internal.mkTimeOps Internal.mkApiM) :=
  LeanSwe.Time.SleepOpsProofs.sleepZeroAndModelSleepMs_impl

/-- Non-vacuity `CanReach` witness for `test_time_mkTimeOps_sleepZeroAndModelSleepMs`. -/
theorem reach_time_mkTimeOps_sleepZeroAndModelSleepMs :
    CanReach (test_time_mkTimeOps_sleepZeroAndModelSleepMs Internal.mkTimeOps Internal.mkTimeOps Internal.mkApiM) :=
  ⟨default, default, 0, by decide,
    proof_time_mkTimeOps_sleepZeroAndModelSleepMs default default 0 (by decide)⟩

/-- Proof of `test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift` for `Internal.mkTimeOps`. -/
theorem proof_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift :
    AllPass (test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift Internal.mkTimeOps) :=
  LeanSwe.Time.SleepOpsProofs.sleepAbstimeRetriesEintrWithoutDrift_impl

/-- Non-vacuity `CanReach` witness for `test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift`. -/
theorem reach_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift :
    CanReach (test_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift Internal.mkTimeOps) :=
  ⟨{ sec := 0, nsec := 0 }, 1, 0, LeanSwe.LinuxSyscall.Errno.EIO, by decide, by decide, by decide, by decide, by decide,
    proof_time_mkTimeOps_sleepAbstimeRetriesEintrWithoutDrift
      { sec := 0, nsec := 0 } 1 0 LeanSwe.LinuxSyscall.Errno.EIO (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- Full public `Interface` refinement of `LeanSwe.Time` against `LeanSwe.Time.Model`. -/
theorem refines_model :
    Core.RefinesPureEq2 LeanSwe.Time.elapsedDuration Model.elapsedDuration ∧
    Core.RefinesPureEq2 LeanSwe.Time.deadlineNanos Model.deadlineNanos ∧
    Core.RefinesPureEq2 LeanSwe.Time.isMonoExpired Model.isMonoExpired ∧
    Core.RefinesPureEq LeanSwe.Time.formatUtcIso8601 Model.formatUtcIso8601 ∧
    Core.RefinesPureEq LeanSwe.Time.parseUtcIso8601 Model.parseUtcIso8601 ∧
    Core.RefinesPureEq LeanSwe.Time.formatUtcCompact Model.formatUtcCompact ∧
    Core.RefinesPureEq LeanSwe.Time.formatUtcDate Model.formatUtcDate ∧
    Core.RefinesPureEq LeanSwe.Time.parseUtcDate Model.parseUtcDate ∧
    Core.RefinesPureEq LeanSwe.Time.utcDateOfTimestamp Model.utcDateOfTimestamp ∧
    Core.RefinesPureEq LeanSwe.Time.timestampOfUtcDate Model.timestampOfUtcDate ∧
    Core.RefinesStepFrom id Model.healthyWf Model.execRawStep Model.allowedRawStep
      Model.healthyWf Internal.mkTimeOps Model.execTimeOpsStep Model.allowedTimeOpsStep ∧
    Core.RefinesStepFromFinally id Model.healthyWf Model.execTimeOpsStep Model.allowedTimeOpsStep
      Model.healthyWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  LeanSwe.Time.Proofs.RefinesModel.refines_model_impl

end LeanSwe.Time.Proofs
