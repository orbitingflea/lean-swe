import LeanSwe.Time.Interface
import LeanSwe.Time.SpecTests
import LeanSwe.Time.Proofs.SleepModelProofs

/-!
# FakeClock Specification Proofs for `LeanSwe.Time`

Proves the deterministic `FakeClock` read, chunked `sleepMs`, `sleepDuration`,
and `measure` specifications over `Internal.fakeApi`.
-/

namespace LeanSwe.Time.FakeClockProofs

open Core
open Core.NondetTest
open Std.Time
open LeanSwe.Time.SleepModelProofs (toNanoseconds_ofNanoseconds toNanoseconds_inj)

private theorem toNanoseconds_add (a b : Duration) :
    (a + b).toNanoseconds.val = a.toNanoseconds.val + b.toNanoseconds.val := by
  change (Duration.ofNanoseconds (a.toNanoseconds + b.toNanoseconds)).toNanoseconds.val = _
  rw [toNanoseconds_ofNanoseconds]
  rfl

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

/-- Proof of `test_time_fakeClock_nowTimestamp_readsWithoutMutating` for `Internal.fakeApi`. -/
theorem fakeClock_nowTimestamp_readsWithoutMutating_impl :
    AllPass (test_time_fakeClock_nowTimestamp_readsWithoutMutating Internal.fakeApi) := by
  intro s0
  simp [Internal.fakeApi, Internal.mkApiM, Internal.fakeOps, StateT.run,
    Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, assert]

/-- Proof of `test_time_fakeClock_monoNanosNow_readsWithoutMutating` for `Internal.fakeApi`. -/
theorem fakeClock_monoNanosNow_readsWithoutMutating_impl :
    AllPass (test_time_fakeClock_monoNanosNow_readsWithoutMutating Internal.fakeApi) := by
  intro s0
  simp [Internal.fakeApi, Internal.mkApiM, Internal.fakeOps, StateT.run,
    Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, assert]

/-- Proof of `test_time_fakeClock_sleepMs_advancesAndChunks` for `Internal.fakeApi`. -/
theorem fakeClock_sleepMs_advancesAndChunks_impl :
    AllPass (test_time_fakeClock_sleepMs_advancesAndChunks Internal.fakeApi) := by
  intro s0 ms
  have h := fakeSleepMs_spec ms s0
  dsimp only at h
  rcases h with ⟨hmono, hwall, ⟨added, hlog, hall, hsum⟩⟩
  dsimp [test_time_fakeClock_sleepMs_advancesAndChunks, Internal.fakeApi,
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

/-- Proof of `test_time_fakeClock_sleepDuration_clampsAndRoundsUp` for `Internal.fakeApi`. -/
theorem fakeClock_sleepDuration_clampsAndRoundsUp_impl :
    AllPass (test_time_fakeClock_sleepDuration_clampsAndRoundsUp Internal.fakeApi) := by
  intro s0 d
  dsimp only [test_time_fakeClock_sleepDuration_clampsAndRoundsUp, Core.NondetTest.assert]
  have hSleepEq : Internal.fakeApi.sleepDuration d = Internal.sleepDuration Internal.fakeOps d := rfl
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

/-- Proof of `test_time_fakeClock_measure_returnsValueAndElapsed` for `Internal.fakeApi`. -/
theorem fakeClock_measure_returnsValueAndElapsed_impl :
    AllPass (test_time_fakeClock_measure_returnsValueAndElapsed Internal.fakeApi) := by
  intro s0 ms
  have hmono := (fakeSleepMs_spec ms s0).1
  dsimp [test_time_fakeClock_measure_returnsValueAndElapsed, Internal.fakeApi,
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

end LeanSwe.Time.FakeClockProofs
