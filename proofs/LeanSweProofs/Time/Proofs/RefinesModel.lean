import Core.Obeys
import LeanSweProofs.Time.Model
import LeanSweProofs.Time.Model.Refines
import LeanSwe.Time.Interface
import LeanSweProofs.Time.Proofs.RefinesPure
import LeanSweProofs.Time.Proofs.RefinesTimeOps

/-!
# `TimeApiM` Model Refinement Proofs for `LeanSwe.Time`

Lifts `Model.allowedTimeOpsStep` single-step refinement through `Internal.mkApiM`
to `Model.allowedPkgStep` and assembles `LeanSwe.Time.Proofs.RefinesModel.refines_model_impl`.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open Std.Time
open LeanSwe.Time

private theorem stateM_map_run' {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

private theorem stateM_pure_run' {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

private theorem stateM_bind_run'' {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

private theorem sleepMs_obeys {W : Type}
    (proj : W → Model.TimeModelState) (ops : TimeOpsM (StateM W))
    (hOps : Core.ObeysStep proj Model.pkgWf (Model.execTimeOpsStep ops) Model.allowedTimeOpsStep) :
    ∀ (ms : Nat) (w : W), Model.pkgWf (proj w) = true →
      min Model.maxMonoNanos ((proj w).monoNanos + ms * 1000000) ≤
        (proj ((Internal.sleepMs ops ms).run w).2).monoNanos ∧
      Model.isValidMonoNanos (proj ((Internal.sleepMs ops ms).run w).2).monoNanos = true ∧
      (proj w).wallNanos ≤ (proj ((Internal.sleepMs ops ms).run w).2).wallNanos ∧
      Model.isValidTimestampNanos (proj ((Internal.sleepMs ops ms).run w).2).wallNanos = true := by
  intro ms
  induction ms using Nat.strongRecOn with
  | _ ms ih =>
    intro w hw
    by_cases h0 : ms = 0
    · subst h0
      rw [Internal.sleepMs]
      simp only [↓reduceIte, StateT.run, pure, StateT.pure, Nat.zero_mul, Nat.add_zero]
      exact ⟨Nat.min_le_right _ _, pkgWf_mono hw, Int.le_refl _, pkgWf_wall hw⟩
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
      rw [stateM_bind_run'']
      have hStep := hOps w (.sleep (UInt32.ofNat chunkNat)) hw
      dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStep
      rw [stateM_bind_run''] at hStep
      cases hsl : (ops.sleep (UInt32.ofNat chunkNat)).run w with
      | mk u w1 =>
        rw [hsl] at hStep
        dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep ⊢
        rcases hStep with ⟨hmLe1, hmVal1, hwLe1, hwVal1⟩
        rw [hcToNat] at hmLe1
        have hwf1 : Model.pkgWf (proj w1) = true := pkgWf_mk hwVal1 hmVal1
        rcases ih (ms - chunkNat) hlt w1 hwf1 with ⟨hmLe2, hmVal2, hwLe2, hwVal2⟩
        refine ⟨?_, hmVal2, Int.le_trans hwLe1 hwLe2, hwVal2⟩
        have hmul : chunkNat * 1000000 + (ms - chunkNat) * 1000000 = ms * 1000000 := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hcLe]
        by_cases hC1 : Model.maxMonoNanos ≤ (proj w).monoNanos + chunkNat * 1000000
        · have h1m : Model.maxMonoNanos ≤ (proj w1).monoNanos := by
            rw [Nat.min_eq_left hC1] at hmLe1; exact hmLe1
          have hC2 : Model.maxMonoNanos ≤ (proj w1).monoNanos + (ms - chunkNat) * 1000000 :=
            Nat.le_trans h1m (Nat.le_add_right _ _)
          rw [Nat.min_eq_left hC2] at hmLe2
          exact Nat.le_trans (Nat.min_le_left _ _) hmLe2
        · have h1m : (proj w).monoNanos + chunkNat * 1000000 ≤ (proj w1).monoNanos := by
            rw [Nat.min_eq_right (Nat.le_of_not_ge hC1)] at hmLe1; exact hmLe1
          have hadd : (proj w).monoNanos + ms * 1000000 ≤
              (proj w1).monoNanos + (ms - chunkNat) * 1000000 := by
            rw [← hmul, ← Nat.add_assoc]
            exact Nat.add_le_add_right h1m _
          exact Nat.le_trans
            (Nat.le_min.mpr ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) hadd⟩)
            hmLe2

private theorem sleepDuration_lowerBound_le (d : Duration) :
    Model.sleepNanosLowerBound d ≤ Internal.sleepDurationMs d * 1000000 := by
  unfold Model.sleepNanosLowerBound Internal.sleepDurationMs
  by_cases h : d.toNanoseconds.val ≤ 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    omega

private theorem sleepDuration_obeys {W : Type}
    (proj : W → Model.TimeModelState) (ops : TimeOpsM (StateM W))
    (hOps : Core.ObeysStep proj Model.pkgWf (Model.execTimeOpsStep ops) Model.allowedTimeOpsStep)
    (d : Duration) (w : W) (hw : Model.pkgWf (proj w) = true) :
    min Model.maxMonoNanos ((proj w).monoNanos + Model.sleepNanosLowerBound d) ≤
      (proj ((Internal.sleepDuration ops d).run w).2).monoNanos ∧
    Model.isValidMonoNanos (proj ((Internal.sleepDuration ops d).run w).2).monoNanos = true ∧
    (proj w).wallNanos ≤ (proj ((Internal.sleepDuration ops d).run w).2).wallNanos ∧
    Model.isValidTimestampNanos (proj ((Internal.sleepDuration ops d).run w).2).wallNanos = true := by
  rcases sleepMs_obeys proj ops hOps (Internal.sleepDurationMs d) w hw with
    ⟨hmLe, hmVal, hwLe, hwVal⟩
  have hlb := sleepDuration_lowerBound_le d
  have hmin :
      min Model.maxMonoNanos ((proj w).monoNanos + Model.sleepNanosLowerBound d) ≤
      min Model.maxMonoNanos ((proj w).monoNanos + Internal.sleepDurationMs d * 1000000) :=
    Nat.le_min.mpr ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) (Nat.add_le_add_left hlb _)⟩
  exact ⟨Nat.le_trans hmin hmLe, hmVal, hwLe, hwVal⟩

private theorem execStepAction_obeys {W : Type}
    (proj : W → Model.TimeModelState) (ops : TimeOpsM (StateM W))
    (hOps : Core.ObeysStep proj Model.pkgWf (Model.execTimeOpsStep ops) Model.allowedTimeOpsStep)
    (act : Model.StepAction) :
    ∀ (w : W), Model.pkgWf (proj w) = true →
      let r := (Model.execStepAction (Internal.mkApiM ops) act).run w
      Model.allowedStepAction (proj w) act r.1 (proj r.2) ∧
      Model.pkgWf (proj r.2) = true := by
  induction act with
  | pureNat val =>
    intro w hw
    dsimp only [Model.execStepAction, Model.allowedStepAction]
    rw [stateM_pure_run']
    exact ⟨⟨rfl, rfl⟩, hw⟩
  | sleepMsNat ms val =>
    intro w hw
    dsimp only [Model.execStepAction, Internal.mkApiM, Model.allowedStepAction]
    rw [stateM_bind_run'', stateM_pure_run']
    rcases sleepMs_obeys proj ops hOps ms w hw with ⟨hmLe, hmVal, hwLe, hwVal⟩
    exact ⟨⟨rfl, hmLe, hmVal, hwLe, hwVal⟩, pkgWf_mk hwVal hmVal⟩
  | sleepDurationNat d val =>
    intro w hw
    dsimp only [Model.execStepAction, Internal.mkApiM, Model.allowedStepAction]
    rw [stateM_bind_run'', stateM_pure_run']
    rcases sleepDuration_obeys proj ops hOps d w hw with ⟨hmLe, hmVal, hwLe, hwVal⟩
    exact ⟨⟨rfl, hmLe, hmVal, hwLe, hwVal⟩, pkgWf_mk hwVal hmVal⟩
  | readMono =>
    intro w hw
    have hStep := hOps w .monoNanosNow hw
    dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStep
    rw [stateM_map_run'] at hStep
    dsimp only [Model.execStepAction, Internal.mkApiM, Model.allowedStepAction]
    cases hr : ops.monoNanosNow.run w with
    | mk ns w' =>
      rw [hr] at hStep
      rcases hStep with ⟨hmLe, hmVal, hEq, hwLe, hwVal⟩
      exact ⟨⟨hmLe, hmVal, hEq, hwLe, hwVal⟩, pkgWf_mk hwVal hmVal⟩
  | readWallNat val =>
    intro w hw
    have hStep := hOps w .nowTimestamp hw
    dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStep
    rw [stateM_map_run'] at hStep
    dsimp only [Model.execStepAction, Internal.mkApiM, Model.allowedStepAction]
    rw [stateM_bind_run'']
    cases hr : ops.nowTimestamp.run w with
    | mk ts w' =>
      rw [hr] at hStep
      rw [stateM_pure_run']
      rcases hStep with ⟨hwLe, hwVal, _, hmLe, hmVal⟩
      exact ⟨⟨rfl, hwLe, hwVal, hmLe, hmVal⟩, pkgWf_mk hwVal hmVal⟩
  | seq first second ihFirst ihSecond =>
    intro w hw
    dsimp only [Model.execStepAction, Model.allowedStepAction]
    rw [stateM_bind_run'']
    have h1 := ihFirst w hw
    cases r1 : (Model.execStepAction (Internal.mkApiM ops) first).run w with
    | mk v1 w1 =>
      rw [r1] at h1
      have h2 := ihSecond w1 h1.2
      cases r2 : (Model.execStepAction (Internal.mkApiM ops) second).run w1 with
      | mk v2 w2 =>
        rw [r2] at h2
        exact ⟨⟨v1, proj w1, h1.1, h2.1⟩, h2.2⟩

/-- Compositional single-step refinement of `Internal.mkApiM` over `Model.allowedTimeOpsStep`. -/
theorem refinesStepFrom_mkApiM :
    Core.ObeysStepFromFinally id Model.pkgWf Model.execTimeOpsStep Model.allowedTimeOpsStep
      Model.pkgWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
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
    rw [stateM_bind_run'', stateM_pure_run']
    exact sleepMs_obeys proj ops hOps ms w hw
  | sleepDuration d =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Model.allowedPkgStep, Function.comp, id]
    rw [stateM_bind_run'', stateM_pure_run']
    exact sleepDuration_obeys proj ops hOps d w hw
  | measure act =>
    dsimp only [Model.execPkgStep, Function.comp, id]
    change Model.allowedPkgStep (proj w) (.measure act)
      ((Model.PkgStepOut.measured <$>
        (do
          let startMono ← ops.monoNanosNow
          let out ← Model.execStepAction (Internal.mkApiM ops) act
          let stopMono ← ops.monoNanosNow
          pure (out, Internal.elapsedDuration startMono stopMono))).run w).1
      (proj
        ((Model.PkgStepOut.measured <$>
          (do
            let startMono ← ops.monoNanosNow
            let out ← Model.execStepAction (Internal.mkApiM ops) act
            let stopMono ← ops.monoNanosNow
            pure (out, Internal.elapsedDuration startMono stopMono))).run w).2)
    rw [stateM_map_run', stateM_bind_run'']
    have hStart := hOps w .monoNanosNow hw
    dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStart
    rw [stateM_map_run'] at hStart
    cases hrun1 : ops.monoNanosNow.run w with
    | mk startMono w1 =>
      rw [hrun1] at hStart
      rcases hStart with ⟨hmLe1, hmVal1, hStartEq, hwLe1, hwVal1⟩
      have hwf1 : Model.pkgWf (proj w1) = true := pkgWf_mk hwVal1 hmVal1
      rw [stateM_bind_run'']
      have hAct := execStepAction_obeys proj ops hOps act w1 hwf1
      cases hrunAct : (Model.execStepAction (Internal.mkApiM ops) act).run w1 with
      | mk val w2 =>
        rw [hrunAct] at hAct
        rcases hAct with ⟨hActRel, hwf2⟩
        rw [stateM_bind_run'']
        have hStop := hOps w2 .monoNanosNow hwf2
        dsimp only [Model.execTimeOpsStep, Model.allowedTimeOpsStep] at hStop
        rw [stateM_map_run'] at hStop
        cases hrun3 : ops.monoNanosNow.run w2 with
        | mk stopMono w3 =>
          rw [hrun3] at hStop
          rw [stateM_pure_run']
          rcases hStop with ⟨hmLe3, hmVal3, hStopEq, hwLe3, hwVal3⟩
          dsimp only [Model.allowedPkgStep]
          refine ⟨proj w1, proj w2, hmLe1, hmVal1, hwLe1, hwVal1,
            hActRel, hmLe3, hmVal3, hwLe3, hwVal3, ?_⟩
          dsimp only at hStartEq hStopEq
          rw [hStartEq, hStopEq]
          rfl

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.Time` against `LeanSwe.Time.Model`. -/
theorem refines_model_impl :
    Core.ObeysPureEq2 LeanSwe.Time.elapsedDuration Model.elapsedDuration ∧
    Core.ObeysPureEq2 LeanSwe.Time.deadlineNanos Model.deadlineNanos ∧
    Core.ObeysPureEq2 LeanSwe.Time.isMonoExpired Model.isMonoExpired ∧
    Core.ObeysPureEq LeanSwe.Time.formatUtcIso8601 Model.formatUtcIso8601 ∧
    Core.ObeysPureEq LeanSwe.Time.parseUtcIso8601 Model.parseUtcIso8601 ∧
    Core.ObeysPureEq LeanSwe.Time.formatUtcCompact Model.formatUtcCompact ∧
    Core.ObeysPureEq LeanSwe.Time.formatUtcDate Model.formatUtcDate ∧
    Core.ObeysPureEq LeanSwe.Time.parseUtcDate Model.parseUtcDate ∧
    Core.ObeysPureEq LeanSwe.Time.utcDateOfTimestamp Model.utcDateOfTimestamp ∧
    Core.ObeysPureEq LeanSwe.Time.timestampOfUtcDate Model.timestampOfUtcDate ∧
    Core.ObeysStepFrom Model.toModelState Model.rawWf Model.execRawStep Model.allowedRawStep
      Model.pkgWf Internal.mkTimeOps Model.execTimeOpsStep Model.allowedTimeOpsStep ∧
    Core.ObeysStepFromFinally id Model.pkgWf Model.execTimeOpsStep Model.allowedTimeOpsStep
      Model.pkgWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
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
