import Core.Refines
import LeanSwe.Time.Model
import LeanSwe.Time.Interface
import LeanSwe.Time.Proofs.RefinesTimeRandHelpers

/-!
# `TimeOpsM` Model Refinement Proofs for `LeanSwe.Time`

Lifts healthy `LeanSwe.LinuxSyscall.TimeRand.Model` transitions through
`Internal.mkTimeOps` via `Core.RefinesStepFrom`.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open Std.Time
open LeanSwe.LinuxSyscall.TimeRand
  (Timespec TimeRandOpsM HealthyEnv
   NSEC_PER_SEC MIN_TIMESPEC_SEC_INT MAX_TIMESPEC_SEC MAX_TIMESPEC_NANOS)
open LeanSwe.Time

private theorem stateM_map_run {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

private theorem stateM_bind_run' {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

/-- Compositional single-step refinement of `Internal.mkTimeOps` over `TimeRand` healthy worlds. -/
theorem refinesStepFrom_mkTimeOps :
    Core.RefinesStepFrom id Model.healthyWf Model.execRawStep Model.allowedRawStep
      Model.healthyWf Internal.mkTimeOps Model.execTimeOpsStep Model.allowedTimeOpsStep := by
  intro W proj sys hRaw w req hw
  cases req with
  | nowTimestamp =>
    dsimp only [Model.execTimeOpsStep, Internal.mkTimeOps]
    rw [stateM_map_run, stateM_bind_run']
    obtain ⟨ts, hcg, hvn, hproj⟩ := clock_gettime_realtime_healthy proj sys hRaw w hw
    rw [hcg]
    dsimp only [Pure.pure, StateT.pure, StateT.run, Model.allowedTimeOpsStep, Function.comp, id]
    have hval : (Timestamp.ofNanosecondsSinceUnixEpoch (Nanosecond.Offset.ofInt ts.toEpochNanos)).toNanosecondsSinceUnixEpoch.val =
        ts.toEpochNanos :=
      congrArg Internal.UnitVal.val (toNanoseconds_ofNanoseconds (Nanosecond.Offset.ofInt ts.toEpochNanos))
    have hb := int64_toInt_bounds ts.sec
    have hlo0 : (-9223372036854775808 : Int) ≤ ts.sec.toInt := hb.1
    have hhi0 : ts.sec.toInt ≤ 9223372036854775807 := hb.2
    have hn : ts.nsec.toNat < 1000000000 := of_decide_eq_true hvn
    have hepoch : ts.toEpochNanos = ts.sec.toInt * 1000000000 + Int.ofNat ts.nsec.toNat := rfl
    have hn0 : (0 : Int) ≤ Int.ofNat ts.nsec.toNat := Int.natCast_nonneg _
    have hn1 : Int.ofNat ts.nsec.toNat ≤ 999999999 := by
      change Int.ofNat ts.nsec.toNat ≤ Int.ofNat 999999999
      exact Int.ofNat_le.mpr (Nat.le_sub_one_of_lt hn)
    have hlo : MIN_TIMESPEC_SEC_INT * 1000000000 ≤ ts.toEpochNanos := by
      rw [hepoch]
      change (-9223372036854775808 : Int) * 1000000000 ≤ ts.sec.toInt * 1000000000 + Int.ofNat ts.nsec.toNat
      have hm : (-9223372036854775808 : Int) * 1000000000 ≤ ts.sec.toInt * 1000000000 :=
        Int.mul_le_mul_of_nonneg_right hlo0 (by decide)
      exact Int.le_trans hm (Int.le_add_of_nonneg_right hn0)
    have hhi : ts.toEpochNanos ≤ Int.ofNat MAX_TIMESPEC_NANOS := by
      rw [hepoch]
      change ts.sec.toInt * 1000000000 + Int.ofNat ts.nsec.toNat ≤ 9223372036854775807 * 1000000000 + 999999999
      have hm : ts.sec.toInt * 1000000000 ≤ 9223372036854775807 * 1000000000 :=
        Int.mul_le_mul_of_nonneg_right hhi0 (by decide)
      exact Int.add_le_add hm hn1
    rw [hval]
    exact ⟨hlo, hhi, hproj⟩
  | monoNanosNow =>
    dsimp only [Model.execTimeOpsStep, Internal.mkTimeOps]
    rw [stateM_map_run, stateM_bind_run']
    obtain ⟨ts, hcg, hval, hlb, hproj⟩ := clock_gettime_monotonic_healthy proj sys hRaw w hw
    rw [hcg]
    dsimp only [Pure.pure, StateT.pure, StateT.run, Model.allowedTimeOpsStep, Function.comp, id]
    dsimp only [StateT.run] at hproj
    obtain ⟨hsec0, _, hleMax⟩ := timespec_valid_toNanosNat_le hval
    rw [decide_eq_true hsec0]
    simp only [↓reduceIte]
    have hwf' : (proj ((sys.clock_gettime .monotonic).run w).2).wf = true := by
      dsimp only [StateT.run]
      rw [hproj]
      exact hw
    refine ⟨hlb, hleMax, hwf', ?_, ?_, ?_, ?_, ?_⟩
    all_goals rw [hproj]
  | sleep ms =>
    dsimp only [Model.execTimeOpsStep, Internal.mkTimeOps, Model.allowedTimeOpsStep, Model.sleepEnvRel, Function.comp, id]
    rw [stateM_bind_run']
    by_cases h0 : ms = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte]
      dsimp only [Pure.pure, StateT.pure, StateT.run]
      refine ⟨hw, Nat.le_refl _, rfl, rfl, rfl, Nat.le_refl _, fun _ => ?_⟩
      simp only [UInt32.toNat_zero, Nat.zero_mul, Nat.add_zero]
      exact Nat.min_le_right _ _
    · simp only [beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run']
      obtain ⟨nowTs, hcg, hval, hlb, hproj1⟩ := clock_gettime_monotonic_healthy proj sys hRaw w hw
      rw [hcg]
      dsimp only
      obtain ⟨hsec0, _, _⟩ := timespec_valid_toNanosNat_le hval
      rw [decide_eq_true hsec0]
      simp only [↓reduceIte]
      have hwf1 : (proj ((sys.clock_gettime .monotonic).run w).2).wf = true := by
        rw [hproj1]
        exact hw
      cases hopt : Timespec.ofNanosNat? (nowTs.toNanosNat + ms.toNat * 1000000) with
      | some targetTs =>
        obtain ⟨htValid, htNs⟩ := ofNanosNat?_some_props hopt
        have hret := sleepAbstimeRetry_healthy proj sys hRaw targetTs htValid Internal.MAX_EINTR_RETRIES
          ((sys.clock_gettime .monotonic).run w).2 hwf1
        dsimp only at hret
        rcases hret with ⟨hwf2, hmono2, hreal2, hcrng2, hdraws2, hbud2, hmonoSucc⟩
        dsimp only [Pure.pure, StateT.pure, StateT.run]
        dsimp only [StateT.run] at hproj1 hwf2 hmono2 hreal2 hcrng2 hdraws2 hbud2 hmonoSucc
        refine ⟨hwf2, ?_, ?_, ?_, ?_, ?_, fun hEq => ?_⟩
        · rw [hproj1] at hmono2; dsimp only at hmono2
          exact Nat.le_trans (Nat.le_max_left _ _) hmono2
        · rw [hreal2, hproj1]
        · rw [hcrng2, hproj1]
        · rw [hdraws2, hproj1]
        · rw [hproj1] at hbud2; exact hbud2
        · have hEq1 : (proj ((Internal.sleepAbstimeRetry sys targetTs Internal.MAX_EINTR_RETRIES).run
              ((sys.clock_gettime .monotonic).run w).2).2).eintrBudget =
              (proj ((sys.clock_gettime .monotonic).run w).2).eintrBudget := by
            dsimp only [StateT.run]
            rw [hproj1]; exact hEq
          have hsuc := hmonoSucc hEq1
          rw [hproj1, htNs] at hsuc
          dsimp only at hsuc
          have hTarget : nowTs.toNanosNat + ms.toNat * 1000000 ≤
              (proj (Internal.sleepAbstimeRetry sys targetTs Internal.MAX_EINTR_RETRIES
                (sys.clock_gettime .monotonic w).snd).snd).state.monoLowerBoundNs :=
            Nat.le_trans (Nat.le_max_right _ _) hsuc
          by_cases hMax : (proj w).state.monoLowerBoundNs ≤ MAX_TIMESPEC_NANOS
          · have hminEq : min (proj w).state.monoLowerBoundNs MAX_TIMESPEC_NANOS = (proj w).state.monoLowerBoundNs :=
              Nat.min_eq_left hMax
            rw [hminEq] at hlb
            exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.add_le_add_right hlb _) hTarget)
          · have hMaxLt : MAX_TIMESPEC_NANOS ≤ (proj w).state.monoLowerBoundNs := by
              cases Nat.le_total (proj w).state.monoLowerBoundNs MAX_TIMESPEC_NANOS with
              | inl hle => exact absurd hle hMax
              | inr hge => exact hge
            have hminEq : min (proj w).state.monoLowerBoundNs MAX_TIMESPEC_NANOS = MAX_TIMESPEC_NANOS :=
              Nat.min_eq_right hMaxLt
            rw [hminEq] at hlb
            have hmono1 : MAX_TIMESPEC_NANOS ≤
                (proj ((sys.clock_gettime .monotonic).run w).2).state.monoLowerBoundNs := by
              dsimp only [StateT.run]
              rw [hproj1]; exact Nat.le_trans hlb (Nat.le_max_right _ _)
            dsimp only [StateT.run] at hmono1 hmono2
            exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans hmono1 hmono2)
      | none =>
        have ⟨hrValid, hrNs⟩ := relativeTimespecOfMs_valid ms
        have hcn := clock_nanosleep_monotonic_healthy proj sys hRaw false (Internal.relativeTimespecOfMs ms) hrValid
          ((sys.clock_gettime .monotonic).run w).2 hwf1
        rw [stateM_bind_run']
        cases hcnRun : (sys.clock_nanosleep .monotonic false (Internal.relativeTimespecOfMs ms)).run
            ((sys.clock_gettime .monotonic).run w).2 with
        | mk res w2 =>
          rw [hcnRun] at hcn
          dsimp only [Pure.pure, StateT.pure, StateT.run] at hcn ⊢
          dsimp only [StateT.run] at hproj1
          cases res with
          | ok u =>
            cases u
            rcases hcn with ⟨hwf2, hmono2, hreal2, hcrng2, hdraws2, hbud2⟩
            rw [hproj1] at hmono2 hreal2 hcrng2 hdraws2 hbud2
            dsimp only at hmono2 hreal2 hcrng2 hdraws2 hbud2
            simp only [Bool.false_eq_true, ↓reduceIte] at hmono2
            refine ⟨hwf2, ?_, hreal2, hcrng2, hdraws2, Nat.le_of_eq hbud2, fun _ => ?_⟩
            · rw [hmono2]
              exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
            · rw [hmono2, hrNs]
              have hmonoLe : (proj w).state.monoLowerBoundNs ≤
                  max (proj w).state.monoLowerBoundNs nowTs.toNanosNat :=
                Nat.le_max_left _ _
              have hle1 : min MAX_TIMESPEC_NANOS ((proj w).state.monoLowerBoundNs + ms.toNat * 1000000) ≤
                  min MAX_TIMESPEC_NANOS (max (proj w).state.monoLowerBoundNs nowTs.toNanosNat + ms.toNat * 1000000) := by
                by_cases h1 : max (proj w).state.monoLowerBoundNs nowTs.toNanosNat + ms.toNat * 1000000 ≤ MAX_TIMESPEC_NANOS
                · have h0' : (proj w).state.monoLowerBoundNs + ms.toNat * 1000000 ≤ MAX_TIMESPEC_NANOS :=
                    Nat.le_trans (Nat.add_le_add_right hmonoLe _) h1
                  rw [Nat.min_eq_right h0', Nat.min_eq_right h1]
                  exact Nat.add_le_add_right hmonoLe _
                · have hge : MAX_TIMESPEC_NANOS ≤ max (proj w).state.monoLowerBoundNs nowTs.toNanosNat + ms.toNat * 1000000 :=
                    Nat.le_of_not_ge h1
                  rw [Nat.min_eq_left hge]
                  exact Nat.min_le_left _ _
              exact Nat.le_trans hle1 (Nat.le_max_right _ _)
          | error e =>
            rcases hcn with ⟨_, hwf2, hbudPos, hst2, hbud2⟩
            rw [hproj1] at hbudPos hst2 hbud2
            dsimp only at hbudPos hst2 hbud2
            refine ⟨hwf2, ?_, ?_, ?_, ?_, by omega, fun hEq => ?_⟩
            · rw [hst2]; exact Nat.le_max_left _ _
            · rw [hst2]
            · rw [hst2]
            · rw [hst2]
            · clear hst2 hwf2 hwf1 hcnRun hopt hval hlb hproj1
              omega

end LeanSwe.Time.Proofs.RefinesModel
