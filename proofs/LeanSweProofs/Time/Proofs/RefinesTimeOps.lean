import Core.Obeys
import LeanSweProofs.Time.Model
import LeanSweProofs.Time.Model.Refines
import LeanSwe.Time.Interface
import LeanSweProofs.Time.Proofs.RefinesTimeRandHelpers

/-!
# `TimeOpsM` Model Refinement Proofs for `LeanSwe.Time`

Lifts `Model.allowedRawStep` transitions (including bounded `Errno.EINTR`
interruption and fixed-deadline `TIMER_ABSTIME` retries up to `MAX_EINTR_RETRIES`)
through `Internal.mkTimeOps` to `Model.allowedTimeOpsStep` via `Core.ObeysStepFrom`.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open Std.Time
open LeanSwe.LinuxSyscall.TimeRand (Timespec TimeRandOpsM)
open LeanSwe.Time

private theorem stateM_map_run {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

private theorem stateM_bind_run' {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

private theorem stateM_pure_run {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α).run s = (a, s) := rfl

/-- Inductive verification of the full `Internal.sleepAbstimeRetry` loop across up to
    `fuel` `Errno.EINTR` interruptions against a fixed valid `TIMER_ABSTIME` deadline `targetTs`. -/
theorem sleepAbstimeRetry_raw {W : Type}
    (proj : W → Model.TimeRawState) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawWf (Model.execRawStep sys) Model.allowedRawStep)
    (targetTs : Timespec) (htValid : targetTs.isValid = true) :
    ∀ (fuel : Nat) (w : W),
      Model.rawWf (proj w) = true →
      (proj w).eintrBudget.val ≤ fuel →
      let w' := (Internal.sleepAbstimeRetry sys targetTs fuel).run w |>.2
      max (proj w).monoNanos targetTs.toNanosNat ≤ (proj w').monoNanos ∧
      Model.isValidMonoNanos (proj w').monoNanos = true ∧
      (proj w).wallNanos ≤ (proj w').wallNanos ∧
      Model.isValidTimestampNanos (proj w').wallNanos = true
  | 0, w, hw, hbud => by
    dsimp only [Internal.sleepAbstimeRetry]
    rw [stateM_bind_run', stateM_pure_run]
    rcases clock_nanosleep_monotonic_abs_raw proj sys hRaw targetTs htValid w hw with
      ⟨_, hmLe, hmVal, hwLe, hwVal⟩ | ⟨_, hlt, _, _, _, _⟩
    · exact ⟨hmLe, hmVal, hwLe, hwVal⟩
    · omega
  | fuel' + 1, w, hw, hbud => by
    dsimp only [Internal.sleepAbstimeRetry]
    rw [stateM_bind_run']
    have hstep := clock_nanosleep_monotonic_abs_raw proj sys hRaw targetTs htValid w hw
    cases hcn : (sys.clock_nanosleep .monotonic true targetTs).run w with
    | mk res w1 =>
      rw [hcn] at hstep
      dsimp only at hstep ⊢
      rcases hstep with ⟨hok, hmLe, hmVal, hwLe, hwVal⟩ | ⟨herr, hlt, hmLe1, hmVal1, hwLe1, hwVal1⟩
      · subst hok
        rw [stateM_pure_run]
        exact ⟨hmLe, hmVal, hwLe, hwVal⟩
      · subst herr
        simp only [beq_self_eq_true, ↓reduceIte]
        have hw1 : Model.rawWf (proj w1) = true := pkgWf_mk hwVal1 hmVal1
        have hbud1 : (proj w1).eintrBudget.val ≤ fuel' := by omega
        obtain ⟨hmLe2, hmVal2, hwLe2, hwVal2⟩ :=
          sleepAbstimeRetry_raw proj sys hRaw targetTs htValid fuel' w1 hw1 hbud1
        refine ⟨Nat.le_trans ?_ hmLe2, hmVal2, Int.le_trans hwLe1 hwLe2, hwVal2⟩
        exact Nat.max_le.mpr ⟨Nat.le_trans hmLe1 (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

/-- Compositional single-step refinement of `Internal.mkTimeOps` over `Model.allowedRawStep`. -/
theorem refinesStepFrom_mkTimeOps :
    Core.ObeysStepFrom Model.toModelState Model.rawWf Model.execRawStep Model.allowedRawStep
      Model.pkgWf Internal.mkTimeOps Model.execTimeOpsStep Model.allowedTimeOpsStep := by
  intro W proj sys hRaw w req hw
  cases req with
  | nowTimestamp =>
    dsimp only [Model.execTimeOpsStep, Internal.mkTimeOps, Function.comp, Model.toModelState]
    rw [stateM_map_run, stateM_bind_run']
    obtain ⟨ts, hcg, hwLe, hwVal, hEq, hmLe, hmVal⟩ := clock_gettime_realtime_raw proj sys hRaw w hw
    rw [hcg]
    dsimp only [Pure.pure, StateT.pure, StateT.run, Model.allowedTimeOpsStep]
    have hval :
        (Timestamp.ofNanosecondsSinceUnixEpoch
          (Nanosecond.Offset.ofInt ts.toEpochNanos)).toNanosecondsSinceUnixEpoch.val =
        ts.toEpochNanos :=
      congrArg Internal.UnitVal.val (toNanoseconds_ofNanoseconds (Nanosecond.Offset.ofInt ts.toEpochNanos))
    rw [hval]
    exact ⟨hwLe, hwVal, hEq, hmLe, hmVal⟩
  | monoNanosNow =>
    dsimp only [Model.execTimeOpsStep, Internal.mkTimeOps, Function.comp, Model.toModelState]
    rw [stateM_map_run, stateM_bind_run']
    obtain ⟨ts, hcg, hval, hmLe, hmVal, hEq, hwLe, hwVal⟩ :=
      clock_gettime_monotonic_raw proj sys hRaw w hw
    rw [hcg]
    dsimp only [Pure.pure, StateT.pure, StateT.run, Model.allowedTimeOpsStep]
    obtain ⟨hsec0, _, _⟩ := timespec_valid_toNanosNat_le hval
    rw [decide_eq_true hsec0]
    simp only [↓reduceIte]
    exact ⟨hmLe, hmVal, hEq, hwLe, hwVal⟩
  | sleep ms =>
    dsimp only [Model.execTimeOpsStep, Internal.mkTimeOps, Function.comp, Model.toModelState]
    rw [stateM_bind_run']
    by_cases h0 : ms = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [stateM_pure_run]
      dsimp only [Model.allowedTimeOpsStep]
      simp only [UInt32.toNat_zero, Nat.zero_mul, Nat.add_zero]
      exact ⟨Nat.min_le_right _ _, pkgWf_mono hw, Int.le_refl _, pkgWf_wall hw⟩
    · simp only [beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run']
      obtain ⟨nowTs, hcg, hval, hmLe1, hmVal1, hEq1, hwLe1, hwVal1⟩ :=
        clock_gettime_monotonic_raw proj sys hRaw w hw
      rw [hcg]
      dsimp only
      obtain ⟨hsec0, _, _⟩ := timespec_valid_toNanosNat_le hval
      rw [decide_eq_true hsec0]
      simp only [↓reduceIte]
      have hwf1 : Model.rawWf (proj ((sys.clock_gettime .monotonic).run w).2) = true :=
        pkgWf_mk hwVal1 hmVal1
      cases hopt : Timespec.ofNanosNat? (nowTs.toNanosNat + ms.toNat * 1000000) with
      | some targetTs =>
        obtain ⟨htValid, htNs⟩ := ofNanosNat?_some_props hopt
        have hbud : (proj ((sys.clock_gettime .monotonic).run w).2).eintrBudget.val ≤
            Internal.MAX_EINTR_RETRIES :=
          Nat.le_of_lt_succ (proj ((sys.clock_gettime .monotonic).run w).2).eintrBudget.isLt
        obtain ⟨hmLe2, hmVal2, hwLe2, hwVal2⟩ :=
          sleepAbstimeRetry_raw proj sys hRaw targetTs htValid Internal.MAX_EINTR_RETRIES
            ((sys.clock_gettime .monotonic).run w).2 hwf1 hbud
        dsimp only
        rw [stateM_pure_run]
        dsimp only [Model.allowedTimeOpsStep]
        have hTarget : (proj w).monoNanos + ms.toNat * 1000000 ≤ targetTs.toNanosNat := by
          rw [htNs, hEq1]
          exact Nat.add_le_add_right hmLe1 _
        exact ⟨Nat.le_trans (Nat.min_le_right _ _)
            (Nat.le_trans hTarget (Nat.le_trans (Nat.le_max_right _ _) hmLe2)),
          hmVal2, Int.le_trans hwLe1 hwLe2, hwVal2⟩
      | none =>
        obtain ⟨hrValid, hrNs⟩ := relativeTimespecOfMs_valid ms
        have hcn := clock_nanosleep_monotonic_rel_raw proj sys hRaw (Internal.relativeTimespecOfMs ms)
          hrValid ((sys.clock_gettime .monotonic).run w).2 hwf1
        rcases hcn with ⟨hcnRun, hmLe2, hmVal2, hwLe2, hwVal2⟩
        rw [hrNs] at hmLe2
        dsimp only
        rw [stateM_bind_run', hcnRun, stateM_pure_run, stateM_pure_run]
        dsimp only [Model.allowedTimeOpsStep]
        have hMinLe :
            min Model.maxMonoNanos ((proj w).monoNanos + ms.toNat * 1000000) ≤
            min Model.maxMonoNanos ((proj ((sys.clock_gettime .monotonic).run w).2).monoNanos + ms.toNat * 1000000) := by
          apply Nat.le_min.mpr
          exact ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) (Nat.add_le_add_right hmLe1 _)⟩
        exact ⟨Nat.le_trans hMinLe hmLe2, hmVal2, Int.le_trans hwLe1 hwLe2, hwVal2⟩

end LeanSwe.Time.Proofs.RefinesModel
