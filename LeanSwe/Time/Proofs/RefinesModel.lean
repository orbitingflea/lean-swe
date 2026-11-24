import Core.Refines
import LeanSwe.Time.Model
import LeanSwe.Time.Interface
import LeanSwe.Time.Proofs.RefinesPure
import LeanSwe.Time.Proofs.RefinesTimeOps

/-!
# `TimeApiM` Model Refinement Proofs for `LeanSwe.Time`

Lifts `TimeOpsM` single-step refinement through `Internal.mkApiM` and assembles
`LeanSwe.Time.Proofs.RefinesModel.refines_model_impl`.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open Std.Time
open LeanSwe.LinuxSyscall.TimeRand (HealthyEnv MAX_TIMESPEC_NANOS)
open LeanSwe.Time

private theorem toNanoseconds_ofNanoseconds' (n : Nanosecond.Offset) :
    (Duration.ofNanoseconds n).toNanoseconds = n := by
  apply Internal.UnitVal.ext
  change (n.val.tdiv 1000000000) * 1000000000 + (n.val.tmod 1000000000) = n.val
  have h := Int.mul_tdiv_add_tmod n.val 1000000000
  omega

private theorem stateM_map_run' {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

private theorem stateM_pure_run' {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

private theorem stateM_bind_run' {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

private theorem sleepMs_healthy {W : Type}
    (proj : W → HealthyEnv) (ops : TimeOpsM (StateM W))
    (hOps : Core.RefinesStep proj Model.healthyWf (Model.execTimeOpsStep ops) Model.allowedTimeOpsStep) :
    ∀ (ms : Nat) (w : W), (proj w).wf = true →
      Model.sleepEnvRel (proj w) (ms * 1000000) (proj ((Internal.sleepMs ops ms).run w).2) := by
  intro ms
  induction ms using Nat.strongRecOn with
  | _ ms ih =>
    intro w hw
    by_cases h0 : ms = 0
    · subst h0
      rw [Internal.sleepMs]
      simp only [↓reduceIte, StateT.run, pure, StateT.pure, Nat.zero_mul]
      exact ⟨hw, Nat.le_refl _, rfl, rfl, rfl, Nat.le_refl _, fun _ => Nat.min_le_right _ _⟩
    · rw [Internal.sleepMs]
      simp only [h0, ↓reduceIte]
      let chunkNat := min ms (UInt32.size - 1)
      have hpos : 0 < ms := Nat.pos_of_ne_zero h0
      have hmax : chunkNat ≤ UInt32.size - 1 := Nat.min_le_right _ _
      have hcpos : 0 < chunkNat := Nat.lt_min.mpr ⟨hpos, by decide⟩
      have hcLe : chunkNat ≤ ms := Nat.min_le_left _ _
      have hlt : ms - chunkNat < ms := Nat.sub_lt hpos hcpos
      have hcToNat : (UInt32.ofNat chunkNat).toNat = chunkNat := by
        rw [UInt32.toNat_ofNat']
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hmax (by decide))
      rw [stateM_bind_run']
      have hStep := hOps w (.sleep (UInt32.ofNat chunkNat)) hw
      dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStep
      rw [stateM_bind_run'] at hStep
      cases hsl : (ops.sleep (UInt32.ofNat chunkNat)).run w with
      | mk u w1 =>
        rw [hsl] at hStep
        dsimp only [Pure.pure, StateT.pure, StateT.run, Model.sleepEnvRel] at hStep ⊢
        rcases hStep with ⟨hwf1, hmono1, hreal1, hcrng1, hdraws1, hbud1, hsucc1⟩
        have hih := ih (ms - chunkNat) hlt w1 hwf1
        dsimp only [Model.sleepEnvRel] at hih
        rcases hih with ⟨hwf2, hmono2, hreal2, hcrng2, hdraws2, hbud2, hsucc2⟩
        refine ⟨hwf2, Nat.le_trans hmono1 hmono2, hreal2.trans hreal1,
          hcrng2.trans hcrng1, hdraws2.trans hdraws1, Nat.le_trans hbud2 hbud1, fun hEq => ?_⟩
        have hEq' : (proj ((Internal.sleepMs ops (ms - chunkNat)).run w1).2).eintrBudget = (proj w).eintrBudget :=
          hEq
        have hEq1 : (proj w1).eintrBudget = (proj w).eintrBudget :=
          Nat.le_antisymm hbud1 (by rw [← hEq']; exact hbud2)
        have hEq2 : (proj ((Internal.sleepMs ops (ms - chunkNat)).run w1).2).eintrBudget = (proj w1).eintrBudget :=
          Nat.le_antisymm hbud2 (by rw [hEq']; exact hbud1)
        have hs1 := hsucc1 hEq1
        have hs2 := hsucc2 hEq2
        rw [hcToNat] at hs1
        have hmul : chunkNat * 1000000 + (ms - chunkNat) * 1000000 = ms * 1000000 := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hcLe]
        by_cases hC1 : MAX_TIMESPEC_NANOS ≤ (proj w).state.monoLowerBoundNs + chunkNat * 1000000
        · have h1m : MAX_TIMESPEC_NANOS ≤ (proj w1).state.monoLowerBoundNs := by
            rw [Nat.min_eq_left hC1] at hs1; exact hs1
          have h2m : MAX_TIMESPEC_NANOS ≤ (proj ((Internal.sleepMs ops (ms - chunkNat)).run w1).2).state.monoLowerBoundNs :=
            Nat.le_trans h1m hmono2
          exact Nat.le_trans (Nat.min_le_left _ _) h2m
        · have h1m : (proj w).state.monoLowerBoundNs + chunkNat * 1000000 ≤ (proj w1).state.monoLowerBoundNs := by
            rw [Nat.min_eq_right (Nat.le_of_not_ge hC1)] at hs1; exact hs1
          have hadd : (proj w).state.monoLowerBoundNs + ms * 1000000 ≤
              (proj w1).state.monoLowerBoundNs + (ms - chunkNat) * 1000000 := by
            rw [← hmul, ← Nat.add_assoc]
            exact Nat.add_le_add_right h1m _
          exact Nat.le_trans (Nat.le_min.mpr ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) hadd⟩) hs2

/-- Compositional single-step refinement of `Internal.mkApiM` over `TimeOpsM` healthy worlds. -/
theorem refinesStepFrom_mkApiM :
    Core.RefinesStepFromFinally id Model.healthyWf Model.execTimeOpsStep Model.allowedTimeOpsStep
      Model.healthyWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj ops hOps w req hw
  cases req with
  | nowTimestamp =>
    have hStep := hOps w .nowTimestamp hw
    dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStep
    rw [stateM_map_run'] at hStep
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp, id]
    rw [stateM_map_run']
    cases hrun : ops.nowTimestamp.run w with
    | mk ts w' =>
      rw [hrun] at hStep
      exact hStep
  | monoNanosNow =>
    have hStep := hOps w .monoNanosNow hw
    dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStep
    rw [stateM_map_run'] at hStep
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp, id]
    rw [stateM_map_run']
    cases hrun : ops.monoNanosNow.run w with
    | mk ns w' =>
      rw [hrun] at hStep
      exact hStep
  | sleepMs ms =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp, id]
    rw [stateM_bind_run', stateM_pure_run']
    dsimp only
    exact sleepMs_healthy proj ops hOps ms w hw
  | sleepDuration d =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.sleepDuration,
      Model.allowedPkgStep, Function.comp, id]
    rw [stateM_bind_run', stateM_pure_run']
    dsimp only
    have hsl : Internal.sleepDurationMs d = Model.sleepDurationMs d := rfl
    rw [hsl]
    exact sleepMs_healthy proj ops hOps (Model.sleepDurationMs d) w hw
  | measure act =>
    dsimp only [Model.execPkgStep, Function.comp, id]
    change Model.allowedPkgStep (proj w) (.measure act)
      ((Model.PkgStepOut.measured <$>
        (do
          let startMono ← ops.monoNanosNow
          let out ← Model.execMeasureAction (Internal.mkApiM ops) act
          let stopMono ← ops.monoNanosNow
          pure (out, Internal.elapsedDuration startMono stopMono))).run w).1
      (proj
        ((Model.PkgStepOut.measured <$>
          (do
            let startMono ← ops.monoNanosNow
            let out ← Model.execMeasureAction (Internal.mkApiM ops) act
            let stopMono ← ops.monoNanosNow
            pure (out, Internal.elapsedDuration startMono stopMono))).run w).2)
    rw [stateM_map_run', stateM_bind_run']
    have hStart := hOps w .monoNanosNow hw
    dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStart
    rw [stateM_map_run'] at hStart
    cases hrun1 : ops.monoNanosNow.run w with
    | mk startMono w1 =>
      rw [hrun1] at hStart
      dsimp only at hStart ⊢
      rcases hStart with ⟨_, hStartLe, hwf1, hmono1, hreal1, hcrng1, hdraws1, hbud1⟩
      have hAct : let (val, w2) := (Model.execMeasureAction (Internal.mkApiM ops) act).run w1
          val = Model.measureActionResult act ∧
          (proj w2).wf = true ∧
          (proj w1).state.monoLowerBoundNs ≤ (proj w2).state.monoLowerBoundNs ∧
          (proj w2).state.realtimeNs = (proj w1).state.realtimeNs ∧
          (proj w2).state.crngReady = (proj w1).state.crngReady ∧
          (proj w2).state.entropyDraws = (proj w1).state.entropyDraws ∧
          (proj w2).eintrBudget ≤ (proj w1).eintrBudget := by
        cases act with
        | pureNat val =>
          dsimp only [Model.execMeasureAction, Model.measureActionResult]
          rw [stateM_pure_run']
          exact ⟨rfl, hwf1, Nat.le_refl _, rfl, rfl, rfl, Nat.le_refl _⟩
        | sleepMsNat ms val =>
          dsimp only [Model.execMeasureAction, Model.measureActionResult, Internal.mkApiM]
          rw [stateM_bind_run', stateM_pure_run']
          have hs := sleepMs_healthy proj ops hOps ms w1 hwf1
          cases hsr : (Internal.sleepMs ops ms).run w1 with
          | mk u w2 =>
            rw [hsr] at hs
            dsimp only [Model.sleepEnvRel] at hs ⊢
            rcases hs with ⟨hwf2, hmono2, hreal2, hcrng2, hdraws2, hbud2, _⟩
            exact ⟨rfl, hwf2, hmono2, hreal2, hcrng2, hdraws2, hbud2⟩
      rw [stateM_bind_run']
      cases hrunAct : (Model.execMeasureAction (Internal.mkApiM ops) act).run w1 with
      | mk val w2 =>
        rw [hrunAct] at hAct
        dsimp only at hAct ⊢
        rcases hAct with ⟨hvalEq, hwf2, hmono2, hreal2, hcrng2, hdraws2, hbud2⟩
        rw [stateM_bind_run']
        have hStop := hOps w2 .monoNanosNow hwf2
        dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStop
        rw [stateM_map_run'] at hStop
        cases hrun3 : ops.monoNanosNow.run w2 with
        | mk stopMono w3 =>
          rw [hrun3] at hStop
          rw [stateM_pure_run']
          dsimp only [Model.allowedPkgStep, id] at hStop ⊢
          rcases hStop with ⟨hStopLb, _, hwf3, hmono3, hreal3, hcrng3, hdraws3, hbud3⟩
          have hStartLeStop : startMono ≤ stopMono := by
            have h1 : startMono ≤ (proj w1).state.monoLowerBoundNs := by
              rw [hmono1]; exact Nat.le_max_right _ _
            have h2 : startMono ≤ (proj w2).state.monoLowerBoundNs := Nat.le_trans h1 hmono2
            exact Nat.le_trans (Nat.le_min.mpr ⟨h2, hStartLe⟩) hStopLb
          have hElNonneg : 0 ≤ (Internal.elapsedDuration startMono stopMono).toNanoseconds.val := by
            dsimp only [Internal.elapsedDuration]
            simp only [hStartLeStop, ↓reduceIte]
            change 0 ≤ (Duration.ofNanoseconds (Nanosecond.Offset.ofNat (stopMono - startMono))).toNanoseconds.val
            rw [toNanoseconds_ofNanoseconds']
            exact Int.natCast_nonneg _
          refine ⟨hvalEq, hElNonneg, hwf3, ?_, ?_, ?_, ?_, ?_⟩
          · have h1 : (proj w).state.monoLowerBoundNs ≤ (proj w1).state.monoLowerBoundNs := by
              rw [hmono1]; exact Nat.le_max_left _ _
            have h3 : (proj w2).state.monoLowerBoundNs ≤ (proj w3).state.monoLowerBoundNs := by
              rw [hmono3]; exact Nat.le_max_left _ _
            exact Nat.le_trans h1 (Nat.le_trans hmono2 h3)
          · rw [hreal3, hreal2, hreal1]
          · rw [hcrng3, hcrng2, hcrng1]
          · rw [hdraws3, hdraws2, hdraws1]
          · exact Nat.le_trans (Nat.le_of_eq hbud3) (Nat.le_trans hbud2 (Nat.le_of_eq hbud1))

/-- Full public `Interface` refinement of `LeanSwe.Time` against `LeanSwe.Time.Model`. -/
theorem refines_model_impl :
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
  ⟨refines_elapsedDuration,
   refines_deadlineNanos,
   refines_isMonoExpired,
   refines_formatUtcIso8601,
   refines_parseUtcIso8601,
   refines_formatUtcCompact,
   refines_formatUtcDate,
   refines_parseUtcDate,
   refines_utcDateOfTimestamp,
   refines_timestampOfUtcDate,
   refinesStepFrom_mkTimeOps,
   refinesStepFrom_mkApiM⟩

end LeanSwe.Time.Proofs.RefinesModel
