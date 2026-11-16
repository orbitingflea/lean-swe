import LeanSwe.Time.Interface
import LeanSwe.Time.SpecTests

namespace LeanSwe.Time.Proofs

open Core
open Core.NondetTest
open Std.Time

private theorem toNanoseconds_ofNanoseconds (n : Nanosecond.Offset) :
    (Duration.ofNanoseconds n).toNanoseconds = n := by
  apply Internal.UnitVal.ext
  change (n.val.tdiv 1000000000) * 1000000000 + (n.val.tmod 1000000000) = n.val
  have h := Int.mul_tdiv_add_tmod n.val 1000000000
  omega

private theorem toNanoseconds_inj {a b : Duration}
    (h : a.toNanoseconds = b.toNanoseconds) : a = b := by
  have heq : a.toNanoseconds.val = b.toNanoseconds.val := congrArg Internal.UnitVal.val h
  rcases a with ⟨⟨sa⟩, ⟨na, hna⟩, hpa⟩
  rcases b with ⟨⟨sb⟩, ⟨nb, hnb⟩, hpb⟩
  change sa * 1000000000 + na = sb * 1000000000 + nb at heq
  have hna' : -999999999 ≤ na ∧ na ≤ 999999999 := hna
  have hnb' : -999999999 ≤ nb ∧ nb ≤ 999999999 := hnb
  have hpa' : (sa ≥ 0 ∧ na ≥ 0) ∨ (sa ≤ 0 ∧ na ≤ 0) := hpa
  have hpb' : (sb ≥ 0 ∧ nb ≥ 0) ∨ (sb ≤ 0 ∧ nb ≤ 0) := hpb
  have hs : sa = sb := by omega
  subst hs
  have hn : na = nb := by omega
  subst hn
  rfl

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

/-- Proof of `test_time_fakeClock_nowTimestamp_readsWithoutMutating` for `fakeApi`. -/
theorem proof_time_fakeClock_nowTimestamp_readsWithoutMutating :
    AllPass (test_time_fakeClock_nowTimestamp_readsWithoutMutating fakeApi) := by
  intro s0
  simp [fakeApi, Internal.fakeApi, Internal.mkApiM, Internal.fakeOps, StateT.run,
    Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, assert]

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_nowTimestamp_readsWithoutMutating`. -/
theorem reach_time_fakeClock_nowTimestamp_readsWithoutMutating :
    CanReach (test_time_fakeClock_nowTimestamp_readsWithoutMutating fakeApi) :=
  ⟨default, proof_time_fakeClock_nowTimestamp_readsWithoutMutating default⟩

/-- Proof of `test_time_fakeClock_monoNanosNow_readsWithoutMutating` for `fakeApi`. -/
theorem proof_time_fakeClock_monoNanosNow_readsWithoutMutating :
    AllPass (test_time_fakeClock_monoNanosNow_readsWithoutMutating fakeApi) := by
  intro s0
  simp [fakeApi, Internal.fakeApi, Internal.mkApiM, Internal.fakeOps, StateT.run,
    Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, assert]

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_monoNanosNow_readsWithoutMutating`. -/
theorem reach_time_fakeClock_monoNanosNow_readsWithoutMutating :
    CanReach (test_time_fakeClock_monoNanosNow_readsWithoutMutating fakeApi) :=
  ⟨default, proof_time_fakeClock_monoNanosNow_readsWithoutMutating default⟩

private theorem timestamp_add_assoc_ms (w : Timestamp) (a b : Nat) :
    (w + Duration.ofMillisecond (Millisecond.Offset.ofNat a)) +
        Duration.ofMillisecond (Millisecond.Offset.ofNat b) =
      w + Duration.ofMillisecond (Millisecond.Offset.ofNat (a + b)) := by
  apply Timestamp.ext
  apply toNanoseconds_inj
  apply Internal.UnitVal.ext
  change ((w.val + Duration.ofMillisecond (Millisecond.Offset.ofNat a)) +
      Duration.ofMillisecond (Millisecond.Offset.ofNat b)).toNanoseconds.val =
    (w.val + Duration.ofMillisecond (Millisecond.Offset.ofNat (a + b))).toNanoseconds.val
  rw [toNanoseconds_add, toNanoseconds_add, toNanoseconds_add]
  have hms : ∀ k : Nat, (Duration.ofMillisecond (Millisecond.Offset.ofNat k)).toNanoseconds.val =
      (k : Int) * 1000000 := by
    intro k
    change (Duration.ofNanoseconds (Millisecond.Offset.ofNat k).toNanoseconds).toNanoseconds.val = _
    rw [toNanoseconds_ofNanoseconds]
    rfl
  rw [hms a, hms b, hms (a + b)]
  omega

private theorem fakeSleepMs_spec (ms : Nat) (s0 : FakeClock) :
    let s1 := ((Internal.sleepMs Internal.fakeOps ms).run s0).2
    s1.monoNanos = s0.monoNanos + ms * 1000000 ∧
    s1.wall = s0.wall + Duration.ofMillisecond (Millisecond.Offset.ofNat ms) ∧
    (∃ added : List UInt32,
      s1.sleepLog.toList = s0.sleepLog.toList ++ added ∧
      added.all (fun c => decide (c.toNat > 0)) = true ∧
      added.foldl (fun acc c => acc + c.toNat) 0 = ms) := by
  induction ms using Nat.strongRecOn generalizing s0 with
  | _ ms ih =>
    by_cases h0 : ms = 0
    · subst h0
      rw [Internal.sleepMs]
      simp only [↓reduceIte, StateT.run, pure, StateT.pure]
      refine ⟨by omega, ?_, ⟨[], by simp⟩⟩
      apply Timestamp.ext
      apply toNanoseconds_inj
      apply Internal.UnitVal.ext
      change s0.wall.val.toNanoseconds.val =
        (s0.wall.val + Duration.ofMillisecond (Millisecond.Offset.ofNat 0)).toNanoseconds.val
      rw [toNanoseconds_add]
      have hz : (Duration.ofMillisecond (Millisecond.Offset.ofNat 0)).toNanoseconds.val = 0 := by decide
      omega
    · rw [Internal.sleepMs]
      simp only [h0, ↓reduceIte]
      let chunkNat := min ms (UInt32.size - 1)
      have hpos : 0 < ms := Nat.pos_of_ne_zero h0
      have hmax : chunkNat ≤ UInt32.size - 1 := Nat.min_le_right _ _
      have hcpos : 0 < chunkNat := Nat.lt_min.mpr ⟨hpos, by decide⟩
      have hcle : chunkNat ≤ ms := Nat.min_le_left _ _
      have hlt : ms - chunkNat < ms := by omega
      have hcval : (UInt32.ofNat chunkNat).toNat = chunkNat := by
        simp [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : chunkNat < UInt32.size)]
      let c := UInt32.ofNat chunkNat
      let sMid : FakeClock :=
        { wall := s0.wall + Duration.ofMillisecond (Millisecond.Offset.ofNat c.toNat)
          monoNanos := s0.monoNanos + c.toNat * 1000000
          sleepLog := s0.sleepLog.push c }
      have hrec := ih (ms - chunkNat) hlt sMid
      have hstep : ((do
            Internal.fakeOps.sleep c
            Internal.sleepMs Internal.fakeOps (ms - chunkNat)).run s0).2 =
          ((Internal.sleepMs Internal.fakeOps (ms - chunkNat)).run sMid).2 := by
        simp [Bind.bind, StateT.bind, StateT.run, pure, Pure.pure,
          Internal.fakeOps, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, sMid, c]
      dsimp only at hrec ⊢
      rw [hstep]
      rcases hrec with ⟨hmono, hwall, ⟨added, hlog, hall, hsum⟩⟩
      refine ⟨?_, ?_, ⟨c :: added, ?_, ?_, ?_⟩⟩
      · rw [hmono]
        simp only [sMid, c, hcval]
        omega
      · rw [hwall]
        simp only [sMid, c, hcval, timestamp_add_assoc_ms]
        have hadd : chunkNat + (ms - chunkNat) = ms := by omega
        rw [hadd]
      · rw [hlog]
        simp [sMid, Array.toList_push, List.append_assoc]
      · simp [List.all_cons, c, hcval, hcpos, hall]
      · simp only [List.foldl_cons, Nat.zero_add, c, hcval]
        have hfold : ∀ (xs : List UInt32) (init : Nat),
            xs.foldl (fun acc x => acc + x.toNat) init =
              init + xs.foldl (fun acc x => acc + x.toNat) 0 := by
          intro xs
          induction xs with
          | nil => intro init; simp
          | cons x xs ihx =>
            intro init
            simp only [List.foldl_cons, Nat.zero_add]
            rw [ihx (init + x.toNat), ihx x.toNat]
            omega
        rw [hfold added chunkNat, hsum]
        omega

/-- Proof of `test_time_fakeClock_sleepMs_advancesAndChunks` for `fakeApi`. -/
theorem proof_time_fakeClock_sleepMs_advancesAndChunks :
    AllPass (test_time_fakeClock_sleepMs_advancesAndChunks fakeApi) := by
  intro s0 ms
  have h := fakeSleepMs_spec ms s0
  dsimp only at h
  rcases h with ⟨hmono, hwall, ⟨added, hlog, hall, hsum⟩⟩
  dsimp [test_time_fakeClock_sleepMs_advancesAndChunks, fakeApi, Internal.fakeApi,
    Internal.mkApiM, Core.NondetTest.assert, Bind.bind]
  rcases heq : StateT.run (Internal.sleepMs Internal.fakeOps ms) s0 with ⟨u, s₁⟩
  rw [heq] at hmono hwall hlog
  dsimp only at hmono hwall hlog ⊢
  simp only [← Array.length_toList]
  have hadded : s₁.sleepLog.toList.drop s0.sleepLog.toList.length = added := by
    rw [hlog, List.drop_left]
  have htake : s₁.sleepLog.toList.take s0.sleepLog.toList.length = s0.sleepLog.toList := by
    rw [hlog, List.take_left]
  rw [hadded, htake]
  exact ⟨hmono, hwall, rfl, hall, hsum, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_sleepMs_advancesAndChunks`. -/
theorem reach_time_fakeClock_sleepMs_advancesAndChunks :
    CanReach (test_time_fakeClock_sleepMs_advancesAndChunks fakeApi) :=
  ⟨default, 5, proof_time_fakeClock_sleepMs_advancesAndChunks default 5⟩

private theorem fakeSleepMs_zero (s0 : FakeClock) :
    (Internal.sleepMs Internal.fakeOps 0).run s0 = ((), s0) := by
  rw [Internal.sleepMs]
  rfl

private theorem fakeSleepDuration_mono (s0 : FakeClock) (d : Duration) (hle : ¬ d.toNanoseconds.val ≤ 0) :
    let s1 := ((Internal.sleepDuration Internal.fakeOps d).run s0).2
    s0.monoNanos + d.toNanoseconds.val.toNat ≤ s1.monoNanos ∧
      s1.monoNanos < s0.monoNanos + d.toNanoseconds.val.toNat + 1000000 := by
  dsimp only [Internal.sleepDuration, Internal.sleepDurationMs]
  simp only [hle, ↓reduceIte]
  generalize hms : (d.toNanoseconds.val.toNat + 999999) / 1000000 = ms
  have hmono := (fakeSleepMs_spec ms s0).1
  rw [hmono]
  have hdiv : d.toNanoseconds.val.toNat ≤ ms * 1000000 ∧
      ms * 1000000 < d.toNanoseconds.val.toNat + 1000000 := by
    rw [← hms]
    omega
  exact ⟨by omega, by omega⟩

/-- Proof of `test_time_fakeClock_sleepDuration_clampsAndRoundsUp` for `fakeApi`. -/
theorem proof_time_fakeClock_sleepDuration_clampsAndRoundsUp :
    AllPass (test_time_fakeClock_sleepDuration_clampsAndRoundsUp fakeApi) := by
  intro s0 d
  dsimp only [test_time_fakeClock_sleepDuration_clampsAndRoundsUp, Core.NondetTest.assert]
  have hSleepEq : fakeApi.sleepDuration d = Internal.sleepDuration Internal.fakeOps d := rfl
  rw [hSleepEq]
  by_cases hle : d.toNanoseconds.val ≤ 0
  · simp only [hle, ↓reduceIte]
    have h0 : ((Internal.sleepDuration Internal.fakeOps d).run s0).2 = s0 := by
      dsimp only [Internal.sleepDuration, Internal.sleepDurationMs]
      simp only [hle, ↓reduceIte]
      exact congrArg Prod.snd (fakeSleepMs_zero s0)
    exact ⟨h0, trivial⟩
  · simp only [hle, ↓reduceIte]
    exact ⟨fakeSleepDuration_mono s0 d hle, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_sleepDuration_clampsAndRoundsUp`. -/
theorem reach_time_fakeClock_sleepDuration_clampsAndRoundsUp :
    CanReach (test_time_fakeClock_sleepDuration_clampsAndRoundsUp fakeApi) :=
  ⟨default, Duration.ofMillisecond 5,
    proof_time_fakeClock_sleepDuration_clampsAndRoundsUp default (Duration.ofMillisecond 5)⟩

/-- Proof of `test_time_fakeClock_measure_returnsValueAndElapsed` for `fakeApi`. -/
theorem proof_time_fakeClock_measure_returnsValueAndElapsed :
    AllPass (test_time_fakeClock_measure_returnsValueAndElapsed fakeApi) := by
  intro s0 ms
  have hmono := (fakeSleepMs_spec ms s0).1
  dsimp [test_time_fakeClock_measure_returnsValueAndElapsed, fakeApi, Internal.fakeApi,
    Internal.mkApiM, Internal.measure, Core.NondetTest.assert]
  simp only [StateT.run, Bind.bind, StateT.bind, pure, StateT.pure, Internal.fakeOps,
    get, getThe, MonadStateOf.get, StateT.get]
  dsimp only [StateT.run, Internal.fakeOps, Bind.bind, StateT.bind, pure, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get] at hmono
  rcases heq : Internal.sleepMs Internal.fakeOps ms s0 with ⟨u, s₁⟩
  dsimp only [Internal.fakeOps, Bind.bind, StateT.bind, pure, StateT.pure,
    get, getThe, MonadStateOf.get, StateT.get] at heq
  rw [heq] at hmono ⊢
  dsimp only [Internal.elapsedDuration] at hmono ⊢
  rw [hmono]
  simp only [show s0.monoNanos ≤ s0.monoNanos + ms * 1000000 by omega, ↓reduceIte]
  have hdiff : s0.monoNanos + ms * 1000000 - s0.monoNanos = ms * 1000000 := by omega
  rw [hdiff]
  refine ⟨trivial, ?_, trivial, trivial⟩
  apply toNanoseconds_inj
  apply Internal.UnitVal.ext
  have hl : (Duration.ofNanoseconds (Nanosecond.Offset.ofNat (ms * 1000000))).toNanoseconds.val =
      (ms : Int) * 1000000 := by
    rw [toNanoseconds_ofNanoseconds]
    rfl
  have hr : (Duration.ofMillisecond (Millisecond.Offset.ofNat ms)).toNanoseconds.val =
      (ms : Int) * 1000000 := by
    change (Duration.ofNanoseconds (Millisecond.Offset.ofNat ms).toNanoseconds).toNanoseconds.val = _
    rw [toNanoseconds_ofNanoseconds]
    rfl
  rw [hl, hr]

/-- Non-vacuity `CanReach` witness for `test_time_fakeClock_measure_returnsValueAndElapsed`. -/
theorem reach_time_fakeClock_measure_returnsValueAndElapsed :
    CanReach (test_time_fakeClock_measure_returnsValueAndElapsed fakeApi) :=
  ⟨default, 5, proof_time_fakeClock_measure_returnsValueAndElapsed default 5⟩

end LeanSwe.Time.Proofs
