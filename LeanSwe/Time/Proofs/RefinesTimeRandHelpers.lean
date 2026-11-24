import Core.Refines
import LeanSwe.Time.Model
import LeanSwe.Time.Interface

/-!
# `TimeRand` Healthy-Step Helpers for `LeanSwe.Time`

Small helper lemmas extracting healthy-step postconditions for
`clock_gettime`, `clock_nanosleep`, and `sleepAbstimeRetry` over
`LeanSwe.LinuxSyscall.TimeRand.Model`.
-/

namespace LeanSwe.Time.Proofs.RefinesModel

open Core
open Std.Time
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand
  (ClockId Timespec TimeRandOpsM TimeRandReq TimeRandOutcome HealthyEnv
   NSEC_PER_SEC MIN_TIMESPEC_SEC_INT MAX_TIMESPEC_SEC MAX_TIMESPEC_NANOS
   execTimeRandReq healthyStep allowedStep allowedStepCore)
open LeanSwe.Time

/-- Conversion of `Nanosecond.Offset` round-trips through `Duration.ofNanoseconds`. -/
theorem toNanoseconds_ofNanoseconds (n : Nanosecond.Offset) :
    (Duration.ofNanoseconds n).toNanoseconds = n := by
  apply Internal.UnitVal.ext
  change (n.val.tdiv 1000000000) * 1000000000 + (n.val.tmod 1000000000) = n.val
  have h := Int.mul_tdiv_add_tmod n.val 1000000000
  omega

/-- Small `Nat` values round-trip through `Int64.ofInt` without wraparound. -/
theorem int64_toInt_ofNat (n : Nat) (hn : n < 2 ^ 63) :
    (Int64.ofInt (n : Int)).toInt = (n : Int) := by
  rw [Int64.toInt_ofInt]
  have hn' : n < 9223372036854775808 := hn
  have h1 : (n : Int) < (9223372036854775808 : Int) := Int.ofNat_lt.mpr hn'
  change (if (n : Int) % (18446744073709551616 : Int) < (9223372036854775808 : Int) then
      (n : Int) % (18446744073709551616 : Int)
    else (n : Int) % (18446744073709551616 : Int) - (18446744073709551616 : Int)) = (n : Int)
  have hm : (n : Int) % (18446744073709551616 : Int) = (n : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg n) (by omega)
  rw [hm]
  simp [h1]

/-- Signed `Int64.toInt` bounds matching `MIN_TIMESPEC_SEC_INT` and `MAX_TIMESPEC_SEC`. -/
theorem int64_toInt_bounds (x : Int64) :
    MIN_TIMESPEC_SEC_INT ≤ x.toInt ∧ x.toInt ≤ Int.ofNat MAX_TIMESPEC_SEC := by
  have hge : -(2 ^ 63 : Int) ≤ x.toBitVec.toInt := BitVec.le_toInt x.toBitVec
  have hlt : x.toBitVec.toInt < (2 ^ 63 : Int) := @BitVec.toInt_lt 64 x.toBitVec
  change -9223372036854775808 ≤ x.toBitVec.toInt ∧ x.toBitVec.toInt ≤ 9223372036854775807
  omega

/-- Valid `Timespec` values satisfy `toNanosNat ≤ MAX_TIMESPEC_NANOS`. -/
theorem timespec_valid_toNanosNat_le {ts : Timespec} (hv : ts.isValid = true) :
    0 ≤ ts.sec.toInt ∧ ts.nsec.toNat < NSEC_PER_SEC ∧ ts.toNanosNat ≤ MAX_TIMESPEC_NANOS := by
  simp only [Timespec.isValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hsec0 : 0 ≤ ts.sec.toInt := hv.1
  have hnsec : ts.nsec.toNat < NSEC_PER_SEC := hv.2
  have hhi := (int64_toInt_bounds ts.sec).2
  change ts.sec.toInt ≤ 9223372036854775807 at hhi
  have hsecNat : ts.sec.toInt.toNat ≤ MAX_TIMESPEC_SEC := by
    change ts.sec.toInt.toNat ≤ 9223372036854775807
    omega
  dsimp only [Timespec.toNanosNat, MAX_TIMESPEC_NANOS]
  refine ⟨hsec0, hnsec, ?_⟩
  have hmul : ts.sec.toInt.toNat * NSEC_PER_SEC ≤ MAX_TIMESPEC_SEC * NSEC_PER_SEC :=
    Nat.mul_le_mul_right NSEC_PER_SEC hsecNat
  have hns : ts.nsec.toNat ≤ NSEC_PER_SEC - 1 := Nat.le_sub_one_of_lt hnsec
  exact Nat.add_le_add hmul hns

/-- Successful `Timespec.ofNanosNat?` yields a valid `Timespec` with exact nanoseconds. -/
theorem ofNanosNat?_some_props {ns : Nat} {ts : Timespec}
    (h : Timespec.ofNanosNat? ns = some ts) :
    ts.isValid = true ∧ ts.toNanosNat = ns := by
  dsimp only [Timespec.ofNanosNat?] at h
  by_cases hle : ns.ble MAX_TIMESPEC_NANOS = true
  · simp only [hle, ↓reduceIte, Option.some.injEq] at h
    subst h
    have hleNat : ns ≤ 9223372036854775807999999999 := Nat.ble_eq.mp hle
    have hnsLt : ns / NSEC_PER_SEC < 2 ^ 63 := by
      change ns / 1000000000 < 9223372036854775808
      omega
    have hsec : (Int64.ofInt (Int.ofNat (ns / NSEC_PER_SEC))).toInt =
        Int.ofNat (ns / NSEC_PER_SEC) :=
      int64_toInt_ofNat _ hnsLt
    have hrem : ns % NSEC_PER_SEC < NSEC_PER_SEC := Nat.mod_lt ns (by decide)
    have hnsec : (UInt32.ofNat (ns % NSEC_PER_SEC)).toNat = ns % NSEC_PER_SEC := by
      rw [UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_trans hrem (by decide))
    refine ⟨?_, ?_⟩
    · simp only [Timespec.isValid, hsec, hnsec, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Int.natCast_nonneg _, hrem⟩
    · dsimp only [Timespec.toNanosNat]
      rw [hsec, hnsec]
      change (ns / NSEC_PER_SEC) * NSEC_PER_SEC + ns % NSEC_PER_SEC = ns
      exact Nat.div_add_mod' ns NSEC_PER_SEC
  · simp [hle] at h

/-- `Internal.relativeTimespecOfMs ms` is valid and equals `ms.toNat * 1_000_000` ns. -/
theorem relativeTimespecOfMs_valid (ms : UInt32) :
    (Internal.relativeTimespecOfMs ms).isValid = true ∧
      (Internal.relativeTimespecOfMs ms).toNanosNat = ms.toNat * 1000000 := by
  have hms_lt : ms.toNat < 4294967296 := ms.toBitVec.isLt
  have hsecLt : ms.toNat / 1000 < 2 ^ 63 := by
    change ms.toNat / 1000 < 9223372036854775808
    omega
  have hsec0 : (Int64.ofInt (Int.ofNat (ms.toNat / 1000))).toInt = ((ms.toNat / 1000 : Nat) : Int) :=
    int64_toInt_ofNat _ hsecLt
  have hrem : ms.toNat % 1000 * 1000000 < 1000000000 := by omega
  have hnsec0 : (UInt32.ofNat (ms.toNat % 1000 * 1000000)).toNat = ms.toNat % 1000 * 1000000 := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_trans hrem (by decide))
  simp only [Timespec.isValid, Timespec.toNanosNat, NSEC_PER_SEC,
    Internal.relativeTimespecOfMs, hsec0, hnsec0]
  constructor
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, hrem⟩
  · rw [Int.toNat_natCast]
    calc ms.toNat / 1000 * 1000000000 + ms.toNat % 1000 * 1000000
      _ = (ms.toNat / 1000 * 1000 + ms.toNat % 1000) * 1000000 := by
        rw [Nat.add_mul, Nat.mul_assoc]
      _ = ms.toNat * 1000000 := by
        rw [Nat.div_add_mod']

private theorem stateM_bind_run {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

private theorem ambientSeccomp_false_of_wf {env : HealthyEnv} (hw : env.wf = true) :
    env.state.ambientSeccomp = false := by
  cases hb : env.state.ambientSeccomp
  · rfl
  · simp [HealthyEnv.wf, hb] at hw

/-- Healthy `clock_gettime .realtime` always returns `.ok ts` with `ts.hasValidNsec` and unchanged state. -/
theorem clock_gettime_realtime_healthy {W : Type}
    (proj : W → HealthyEnv) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.RefinesStep proj Model.healthyWf (Model.execRawStep sys) Model.allowedRawStep)
    (w : W) (hw : (proj w).wf = true) :
    ∃ ts : Timespec,
      (sys.clock_gettime .realtime).run w = (.ok ts, ((sys.clock_gettime .realtime).run w).2) ∧
      ts.hasValidNsec = true ∧
      proj ((sys.clock_gettime .realtime).run w).2 = proj w := by
  have hStep := hRaw w (.clock_gettime .realtime) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep,
    healthyStep, LeanSwe.LinuxSyscall.TimeRand.isCriticalFault,
    LeanSwe.LinuxSyscall.TimeRand.isEintrOutcome] at hStep
  rw [stateM_bind_run] at hStep
  have hns := ambientSeccomp_false_of_wf hw
  have hwfF : (!HealthyEnv.wf (proj w)) = false := by
    have : HealthyEnv.wf (proj w) = true := hw
    simp [this]
  cases hcg : (sys.clock_gettime .realtime).run w with
  | mk res w' =>
    rw [hcg] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep
    rw [hwfF] at hStep
    cases res with
    | error e =>
      dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfTimespec, allowedStep, allowedStepCore] at hStep
      rw [hns] at hStep
      by_cases hcrit : LeanSwe.LinuxSyscall.Errno.isCriticalOsErrno e = true
      · simp [hcrit] at hStep
      · simp [hcrit] at hStep
    | ok ts =>
      dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfTimespec,
        LeanSwe.LinuxSyscall.Errno.isCriticalOsErrno, allowedStep, allowedStepCore] at hStep
      rw [hns] at hStep
      simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hStep
      by_cases hvn : ts.hasValidNsec = true
      · simp only [hvn, ↓reduceIte] at hStep
        injection hStep with hProj
        exact ⟨ts, rfl, hvn, hProj.symm⟩
      · simp [hvn] at hStep

/-- Healthy `clock_gettime .monotonic` always returns `.ok ts` above `monoLowerBoundNs`. -/
theorem clock_gettime_monotonic_healthy {W : Type}
    (proj : W → HealthyEnv) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.RefinesStep proj Model.healthyWf (Model.execRawStep sys) Model.allowedRawStep)
    (w : W) (hw : (proj w).wf = true) :
    ∃ ts : Timespec,
      (sys.clock_gettime .monotonic).run w = (.ok ts, ((sys.clock_gettime .monotonic).run w).2) ∧
      ts.isValid = true ∧
      min (proj w).state.monoLowerBoundNs MAX_TIMESPEC_NANOS ≤ ts.toNanosNat ∧
      proj ((sys.clock_gettime .monotonic).run w).2 =
        { state := { (proj w).state with monoLowerBoundNs := max (proj w).state.monoLowerBoundNs ts.toNanosNat }
          eintrBudget := (proj w).eintrBudget } := by
  have hStep := hRaw w (.clock_gettime .monotonic) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep,
    healthyStep, LeanSwe.LinuxSyscall.TimeRand.isCriticalFault,
    LeanSwe.LinuxSyscall.TimeRand.isEintrOutcome] at hStep
  rw [stateM_bind_run] at hStep
  have hns := ambientSeccomp_false_of_wf hw
  have hwfF : (!HealthyEnv.wf (proj w)) = false := by
    have : HealthyEnv.wf (proj w) = true := hw
    simp [this]
  cases hcg : (sys.clock_gettime .monotonic).run w with
  | mk res w' =>
    rw [hcg] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run] at hStep
    rw [hwfF] at hStep
    cases res with
    | error e =>
      dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfTimespec, allowedStep, allowedStepCore] at hStep
      rw [hns] at hStep
      by_cases hcrit : LeanSwe.LinuxSyscall.Errno.isCriticalOsErrno e = true
      · simp [hcrit] at hStep
      · simp [hcrit] at hStep
    | ok ts =>
      dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfTimespec,
        LeanSwe.LinuxSyscall.Errno.isCriticalOsErrno, allowedStep, allowedStepCore] at hStep
      rw [hns] at hStep
      simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hStep
      by_cases hcond : (ts.isValid && decide (min (proj w).state.monoLowerBoundNs MAX_TIMESPEC_NANOS ≤ ts.toNanosNat)) = true
      · rw [hcond] at hStep
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        injection hStep with hProj
        refine ⟨ts, rfl, hcond.1, hcond.2, ?_⟩
        rw [← hProj]
        cases hst : (proj w).state
        simp only [hst] at hns
        subst hns
        rfl
      · have hcondF : (ts.isValid && decide (min (proj w).state.monoLowerBoundNs MAX_TIMESPEC_NANOS ≤ ts.toNanosNat)) = false := by
          cases hb : (ts.isValid && decide (min (proj w).state.monoLowerBoundNs MAX_TIMESPEC_NANOS ≤ ts.toNanosNat))
          · rfl
          · exact absurd hb hcond
        rw [hcondF] at hStep
        simp at hStep

private theorem healthyStep_clock_nanosleep_ok
    (env env' : HealthyEnv) (hwf : env.wf = true)
    (abstime : Bool) (reqTs : Timespec) (hvalid : reqTs.isValid = true)
    (h : healthyStep env (.clock_nanosleep .monotonic abstime reqTs) .unit = some env') :
    env'.wf = true ∧
      env'.state.monoLowerBoundNs =
        max env.state.monoLowerBoundNs
          (if abstime then reqTs.toNanosNat else min MAX_TIMESPEC_NANOS (env.state.monoLowerBoundNs + reqTs.toNanosNat)) ∧
      env'.state.realtimeNs = env.state.realtimeNs ∧
      env'.state.crngReady = env.state.crngReady ∧
      env'.state.entropyDraws = env.state.entropyDraws ∧
      env'.eintrBudget = env.eintrBudget := by
  rcases env with ⟨⟨mono, real, crng, draws, amb⟩, bud⟩
  cases amb
  · unfold healthyStep at h
    simp only [hwf, Bool.not_true, LeanSwe.LinuxSyscall.TimeRand.isCriticalFault,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, allowedStep, allowedStepCore,
      hvalid, LeanSwe.LinuxSyscall.TimeRand.isEintrOutcome] at h
    injection h with hEq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hEq]; rfl
    · rw [← hEq]
      cases abstime
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
    · rw [← hEq]
    · rw [← hEq]
    · rw [← hEq]
    · rw [← hEq]
  · simp [HealthyEnv.wf] at hwf

private theorem healthyStep_clock_nanosleep_err
    (env env' : HealthyEnv) (hwf : env.wf = true)
    (abstime : Bool) (reqTs : Timespec) (hvalid : reqTs.isValid = true)
    (e : Errno)
    (h : healthyStep env (.clock_nanosleep .monotonic abstime reqTs) (.err e) = some env') :
    e = Errno.EINTR ∧
      env'.wf = true ∧
      0 < env.eintrBudget ∧
      env'.state = env.state ∧
      env'.eintrBudget = env.eintrBudget - 1 := by
  rcases env with ⟨⟨mono, real, crng, draws, amb⟩, bud⟩
  cases amb
  · unfold healthyStep at h
    simp only [hwf, Bool.not_true, LeanSwe.LinuxSyscall.TimeRand.isCriticalFault,
      Bool.false_or, allowedStep, allowedStepCore,
      hvalid, LeanSwe.LinuxSyscall.TimeRand.isEintrOutcome] at h
    by_cases hcrit : LeanSwe.LinuxSyscall.Errno.isCriticalOsErrno e = true
    · simp [hcrit] at h
    · simp only [hcrit, Bool.false_eq_true, ↓reduceIte] at h
      by_cases he : e = Errno.EINTR
      · subst he
        simp only [beq_self_eq_true, ↓reduceIte] at h
        by_cases hbud : bud > 0
        · simp only [hbud, ↓reduceIte] at h
          injection h with hEq
          subst hEq
          exact ⟨rfl, rfl, hbud, rfl, rfl⟩
        · simp [hbud] at h
      · simp [he] at h
  · simp [HealthyEnv.wf] at hwf

/-- Healthy `clock_nanosleep .monotonic` either succeeds advancing `monoLowerBoundNs` or returns `EINTR` spending 1 budget. -/
theorem clock_nanosleep_monotonic_healthy {W : Type}
    (proj : W → HealthyEnv) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.RefinesStep proj Model.healthyWf (Model.execRawStep sys) Model.allowedRawStep)
    (abstime : Bool) (reqTs : Timespec) (hvalid : reqTs.isValid = true)
    (w : W) (hw : (proj w).wf = true) :
    let (res, w') := (sys.clock_nanosleep .monotonic abstime reqTs).run w
    match res with
    | .ok () =>
      (proj w').wf = true ∧
      (proj w').state.monoLowerBoundNs =
        max (proj w).state.monoLowerBoundNs
          (if abstime then reqTs.toNanosNat else min MAX_TIMESPEC_NANOS ((proj w).state.monoLowerBoundNs + reqTs.toNanosNat)) ∧
      (proj w').state.realtimeNs = (proj w).state.realtimeNs ∧
      (proj w').state.crngReady = (proj w).state.crngReady ∧
      (proj w').state.entropyDraws = (proj w).state.entropyDraws ∧
      (proj w').eintrBudget = (proj w).eintrBudget
    | .error e =>
      e = Errno.EINTR ∧
      (proj w').wf = true ∧
      0 < (proj w).eintrBudget ∧
      (proj w').state = (proj w).state ∧
      (proj w').eintrBudget = (proj w).eintrBudget - 1 := by
  have hStep := hRaw w (.clock_nanosleep .monotonic abstime reqTs) hw
  dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep] at hStep
  rw [stateM_bind_run] at hStep
  cases hcn : (sys.clock_nanosleep .monotonic abstime reqTs).run w with
  | mk res w' =>
    rw [hcn] at hStep
    dsimp only [Pure.pure, StateT.pure, StateT.run, LeanSwe.LinuxSyscall.TimeRand.outcomeOfUnit] at hStep ⊢
    cases res with
    | ok u =>
      cases u
      exact healthyStep_clock_nanosleep_ok (proj w) (proj w') hw abstime reqTs hvalid hStep
    | error e =>
      exact healthyStep_clock_nanosleep_err (proj w) (proj w') hw abstime reqTs hvalid e hStep

/-- Bounded `TIMER_ABSTIME` retry loop preserves healthy invariants and advances `monoLowerBoundNs` when un-interrupted. -/
theorem sleepAbstimeRetry_healthy {W : Type}
    (proj : W → HealthyEnv) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.RefinesStep proj Model.healthyWf (Model.execRawStep sys) Model.allowedRawStep)
    (targetTs : Timespec) (hvalid : targetTs.isValid = true) :
    ∀ (fuel : Nat) (w : W),
      (proj w).wf = true →
      let w' := ((Internal.sleepAbstimeRetry sys targetTs fuel).run w).2
      (proj w').wf = true ∧
      (proj w).state.monoLowerBoundNs ≤ (proj w').state.monoLowerBoundNs ∧
      (proj w').state.realtimeNs = (proj w).state.realtimeNs ∧
      (proj w').state.crngReady = (proj w).state.crngReady ∧
      (proj w').state.entropyDraws = (proj w).state.entropyDraws ∧
      (proj w').eintrBudget ≤ (proj w).eintrBudget ∧
      ((proj w').eintrBudget = (proj w).eintrBudget →
        max (proj w).state.monoLowerBoundNs targetTs.toNanosNat ≤ (proj w').state.monoLowerBoundNs) := by
  intro fuel
  induction fuel with
  | zero =>
    intro w hw
    dsimp only [Internal.sleepAbstimeRetry]
    rw [stateM_bind_run]
    have hcn := clock_nanosleep_monotonic_healthy proj sys hRaw true targetTs hvalid w hw
    cases hrun : (sys.clock_nanosleep .monotonic true targetTs).run w with
    | mk res w1 =>
      rw [hrun] at hcn
      dsimp only [Pure.pure, StateT.pure, StateT.run] at hcn ⊢
      cases res with
      | ok u =>
        cases u
        rcases hcn with ⟨hwf1, hmono1, hreal1, hcrng1, hdraws1, hbud1⟩
        simp only [↓reduceIte] at hmono1
        exact ⟨hwf1, by omega, hreal1, hcrng1, hdraws1, Nat.le_of_eq hbud1, fun _ => by omega⟩
      | error e =>
        rcases hcn with ⟨_, hwf1, hbudPos, hst1, hbud1⟩
        refine ⟨hwf1, by rw [hst1]; exact Nat.le_refl _, by rw [hst1], by rw [hst1], by rw [hst1], ?_, fun hEq => ?_⟩
        · rw [hbud1]; exact Nat.sub_le _ _
        · exfalso
          clear hst1 hwf1
          omega
  | succ fuel' ih =>
    intro w hw
    dsimp only [Internal.sleepAbstimeRetry]
    rw [stateM_bind_run]
    have hcn := clock_nanosleep_monotonic_healthy proj sys hRaw true targetTs hvalid w hw
    cases hrun : (sys.clock_nanosleep .monotonic true targetTs).run w with
    | mk res w1 =>
      rw [hrun] at hcn
      dsimp only at hcn ⊢
      cases res with
      | ok u =>
        cases u
        rcases hcn with ⟨hwf1, hmono1, hreal1, hcrng1, hdraws1, hbud1⟩
        simp only [↓reduceIte] at hmono1
        dsimp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hwf1, by omega, hreal1, hcrng1, hdraws1, Nat.le_of_eq hbud1, fun _ => by omega⟩
      | error e =>
        rcases hcn with ⟨he, hwf1, hbudPos, hst1, hbud1⟩
        subst he
        have hif : (if (Errno.EINTR == Errno.EINTR) = true then Internal.sleepAbstimeRetry sys targetTs fuel' else pure ()) =
            Internal.sleepAbstimeRetry sys targetTs fuel' := by
          simp
        dsimp only
        rw [hif]
        have hih := ih w1 hwf1
        dsimp only at hih
        rcases hih with ⟨hwf2, hmono2, hreal2, hcrng2, hdraws2, hbud2, _⟩
        refine ⟨hwf2, ?_, ?_, ?_, ?_, ?_, fun hEq => ?_⟩
        · rw [hst1] at hmono2; exact hmono2
        · rw [hreal2, hst1]
        · rw [hcrng2, hst1]
        · rw [hdraws2, hst1]
        · exact Nat.le_trans hbud2 (by rw [hbud1]; exact Nat.sub_le _ _)
        · exfalso
          clear hst1 hreal2 hcrng2 hdraws2 hmono2 hwf2 hwf1 ih hrun hif
          omega

end LeanSwe.Time.Proofs.RefinesModel
