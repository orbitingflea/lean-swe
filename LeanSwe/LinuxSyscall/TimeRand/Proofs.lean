import Core.Obeys
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.LinuxSyscall.TimeRand.Model.Refines
import LeanSwe.LinuxSyscall.TimeRand.SpecTests
import LeanSwe.LinuxSyscall.TimeRand.Proofs.OpsProofs
import LeanSwe.LinuxSyscall.TimeRand.Proofs.StepProofs

namespace LeanSwe.LinuxSyscall.TimeRand.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

/-- Initial healthy `TimeRand` environments satisfy `HealthyEnv.wf`. -/
theorem healthyEnv_initial_wf (budget : Nat) (realtimeNs : Int) (crngReady : Bool) :
    (HealthyEnv.initial budget realtimeNs crngReady).wf = true :=
  rfl

/-- Tightness by construction: every `allowedStep` transition from a healthy `TimeRand` environment without curated critical faults (and with positive `eintrBudget` on `EINTR`) is accepted by `healthyStep`. -/
theorem allowedStep_healthy_tight
    (env : HealthyEnv) (req : TimeRandReq) (out : TimeRandOutcome) (s' : TimeRandState)
    (hStep : allowedStep env.state req out = some s')
    (hWf : env.wf = true)
    (hBudget : isEintrOutcome out = true → 0 < env.eintrBudget)
    (hNoCrit : isCriticalFault out = false) :
    healthyStep env req out =
      some { state := s',
             eintrBudget := if isEintrOutcome out then env.eintrBudget - 1 else env.eintrBudget } := by
  unfold healthyStep
  have hGuard : (!env.wf || isCriticalFault out) = false := by simp [hWf, hNoCrit]
  simp only [hGuard, Bool.false_eq_true, ↓reduceIte, hStep]
  cases hEi : isEintrOutcome out
  · simp
  · have hb : env.eintrBudget > 0 := hBudget hEi
    simp [hb]

/-- Soundness of `healthyStep` with respect to `allowedStep`: every `healthyStep` transition is a valid `allowedStep` transition, preserves `HealthyEnv.wf`, excludes curated critical OS faults, and strictly decreases `eintrBudget` on `EINTR`. -/
theorem healthyStep_implies_allowedStep
    (env env' : HealthyEnv) (req : TimeRandReq) (out : TimeRandOutcome)
    (h : healthyStep env req out = some env') :
    allowedStep env.state req out = some env'.state ∧
    env.wf = true ∧
    env'.wf = true ∧
    isCriticalFault out = false ∧
    env'.eintrBudget ≤ env.eintrBudget ∧
    (isEintrOutcome out = true → env'.eintrBudget < env.eintrBudget) := by
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault out) = true
  · simp [hBad] at h
  · have hWf : env.wf = true := by
      cases hw : env.wf <;> simp_all
    have hNoCrit : isCriticalFault out = false := by
      cases hc : isCriticalFault out <;> simp_all
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => rw [hAl] at h; contradiction
    | some s' =>
      rw [hAl] at h
      dsimp only at h
      have hSecF : env.state.ambientSeccomp = false := by
        unfold HealthyEnv.wf at hWf
        cases hb : env.state.ambientSeccomp <;> simp_all
      have hCore : allowedStepCore env.state req out = some s' := by
        simpa [allowedStep, hSecF] using hAl
      have hSec' : s'.ambientSeccomp = false := by
        rw [allowedStepCore_preserves_ambientSeccomp _ _ _ _ hCore, hSecF]
      cases hEi : isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        dsimp only
        exact ⟨rfl, hWf, by simp [HealthyEnv.wf, hSec'], hNoCrit, Nat.le_refl _, fun hc => by cases hc⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hb : env.eintrBudget > 0
        · simp only [hb, ↓reduceIte, Option.some.injEq] at h
          subst h
          dsimp only
          exact ⟨rfl, hWf, by simp [HealthyEnv.wf, hSec'], hNoCrit, Nat.sub_le _ _, fun _ => by omega⟩
        · simp [hb] at h

/-- Reference `healthyModelOps` refines `healthyStep` universally across all requests. -/
theorem healthyModelOps_refinesHealthyTimeRand :
    RefinesHealthyTimeRand healthyModelOps := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  have hSound := proof_timerand_modelOps_soundAgainstAllowedStep env.state
  have hSecF : env.state.ambientSeccomp = false := by
    unfold HealthyEnv.wf at hWf
    cases hb : env.state.ambientSeccomp <;> simp_all
  cases req with
  | clock_gettime clk =>
    have h1 := (hSound clk false default 0 {}).1
    have hCore : allowedStepCore env.state (.clock_gettime clk)
        (outcomeOfTimespec (modelOps.clock_gettime clk env.state).1) =
        some (modelOps.clock_gettime clk env.state).2 := by
      simpa [allowedStep, hSecF] using h1
    have hNoCrit := allowedStepCore_not_critical _ _ _ _ hCore
    have hNoEi : isEintrOutcome (outcomeOfTimespec (modelOps.clock_gettime clk env.state).1) = false := by
      cases clk
      · rw [modelOps_clock_gettime_realtime]
        cases Timespec.ofEpochNanos? env.state.realtimeNs <;> rfl
      · rw [modelOps_clock_gettime_monotonic]
        cases Timespec.ofNanosNat? env.state.monoLowerBoundNs <;> rfl
    have hTight := allowedStep_healthy_tight env (.clock_gettime clk) _ _ h1 hWf (by simp [hNoEi]) hNoCrit
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execTimeRandReq, healthyModelOps, TimeRandOpsM.clock_gettime, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight
  | clock_nanosleep clk abstime reqTs =>
    have h2 := (hSound clk abstime reqTs 0 {}).2.1
    have hCore : allowedStepCore env.state (.clock_nanosleep clk abstime reqTs)
        (outcomeOfUnit (modelOps.clock_nanosleep clk abstime reqTs env.state).1) =
        some (modelOps.clock_nanosleep clk abstime reqTs env.state).2 := by
      simpa [allowedStep, hSecF] using h2
    have hNoCrit := allowedStepCore_not_critical _ _ _ _ hCore
    have hNoEi : isEintrOutcome (outcomeOfUnit (modelOps.clock_nanosleep clk abstime reqTs env.state).1) = false := by
      rw [modelOps_clock_nanosleep]
      split
      · dsimp only; decide
      · cases clk <;> rfl
    have hTight := allowedStep_healthy_tight env (.clock_nanosleep clk abstime reqTs) _ _ h2 hWf (by simp [hNoEi]) hNoCrit
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execTimeRandReq, healthyModelOps, TimeRandOpsM.clock_nanosleep, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight
  | getrandom len flags =>
    have h3 := (hSound .realtime false default len flags).2.2.1
    have hCore : allowedStepCore env.state (.getrandom len flags)
        (outcomeOfBytes (modelOps.getrandom len flags env.state).1) =
        some (modelOps.getrandom len flags env.state).2 := by
      simpa [allowedStep, hSecF] using h3
    have hNoCrit := allowedStepCore_not_critical _ _ _ _ hCore
    have hNoEi : isEintrOutcome (outcomeOfBytes (modelOps.getrandom len flags env.state).1) = false := by
      rw [modelOps_getrandom]
      by_cases h1 : flags.isInvalid = true
      · simp [h1]; decide
      · by_cases h2 : (!env.state.crngReady && flags.nonblock && !flags.insecure) = true
        · simp [h1, h2]; decide
        · simp [h1, h2, outcomeOfBytes, isEintrOutcome]
    have hTight := allowedStep_healthy_tight env (.getrandom len flags) _ _ h3 hWf (by simp [hNoEi]) hNoCrit
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    dsimp only [execTimeRandReq, healthyModelOps, TimeRandOpsM.getrandom, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      set, MonadStateOf.set, StateT.set]
    exact hTight

/-- Over any `ops` satisfying `RefinesHealthyTimeRandAt proj ops`, `clock_gettime` succeeds unconditionally without consuming `eintrBudget`. -/
theorem refinesHealthy_clock_gettime_ok
    {W : Type} {proj : W → HealthyEnv} {ops : TimeRandOpsM (StateM W)}
    (hRef : RefinesHealthyTimeRandAt proj ops)
    (w : W) (clk : ClockId) (hWf : (proj w).wf = true) :
    ∃ ts w', (ops.clock_gettime clk).run w = (.ok ts, w') ∧
      (proj w').wf = true ∧
      (proj w').eintrBudget = (proj w).eintrBudget ∧
      allowedStepCore (proj w).state (.clock_gettime clk) (.timespec ts) = some (proj w').state := by
  have hStep := hRef w (.clock_gettime clk) hWf
  dsimp only [execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
  cases hRun : (ops.clock_gettime clk).run w with
  | mk res w' =>
    change (ops.clock_gettime clk) w = (res, w') at hRun
    rw [hRun] at hStep
    dsimp only at hStep
    rcases healthyStep_implies_allowedStep (proj w) (proj w') (.clock_gettime clk)
      (outcomeOfTimespec res) hStep with ⟨hAl, _, hWf', _, _, _⟩
    have hSecF : (proj w).state.ambientSeccomp = false := by
      unfold HealthyEnv.wf at hWf
      cases hb : (proj w).state.ambientSeccomp <;> simp_all
    have hCore : allowedStepCore (proj w).state (.clock_gettime clk) (outcomeOfTimespec res) =
        some (proj w').state := by
      simpa [allowedStep, hSecF] using hAl
    cases res with
    | error e =>
      simp [outcomeOfTimespec, allowedStepCore] at hCore
    | ok ts =>
      have hBud : (proj w').eintrBudget = (proj w).eintrBudget := by
        unfold healthyStep at hStep
        rw [hAl] at hStep
        simp only [hWf, Bool.not_true, isCriticalFault, outcomeOfTimespec, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte, isEintrOutcome, Option.some.injEq] at hStep
        exact (congrArg HealthyEnv.eintrBudget hStep).symm
      exact ⟨ts, w', rfl, hWf', hBud, hCore⟩

/-- Lens-lifting composition theorem: lifting any `ops` satisfying `RefinesHealthyTimeRand` along `(getEnv, setEnv)` with `∀ w e, getEnv (setEnv w e) = e` satisfies `RefinesHealthyTimeRandAt getEnv`. -/
theorem refinesHealthyTimeRandAt_of_lens
    {W : Type} (getEnv : W → HealthyEnv) (setEnv : W → HealthyEnv → W)
    (hGetSet : ∀ (w : W) (e : HealthyEnv), getEnv (setEnv w e) = e)
    {ops : TimeRandOpsM (StateM HealthyEnv)} (hRef : RefinesHealthyTimeRand ops) :
    RefinesHealthyTimeRandAt getEnv
      { clock_gettime := fun clk w =>
          let (res, e') := (ops.clock_gettime clk).run (getEnv w); (res, setEnv w e')
        clock_nanosleep := fun clk abstime reqTs w =>
          let (res, e') := (ops.clock_nanosleep clk abstime reqTs).run (getEnv w); (res, setEnv w e')
        getrandom := fun len flags w =>
          let (res, e') := (ops.getrandom len flags).run (getEnv w); (res, setEnv w e') } := by
  intro w req hWf
  have hStep := hRef (getEnv w) req hWf
  cases req with
  | clock_gettime clk =>
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.clock_gettime clk (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep
  | clock_nanosleep clk abstime reqTs =>
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.clock_nanosleep clk abstime reqTs (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep
  | getrandom len flags =>
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    cases hC : ops.getrandom len flags (getEnv w) with
    | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep

/-- Proof of `test_timerand_healthyStep_and_healthyModelOps`. -/
theorem proof_timerand_healthyStep_and_healthyModelOps :
    AllPass test_timerand_healthyStep_and_healthyModelOps := by
  dsimp only [test_timerand_healthyStep_and_healthyModelOps, NondetTest.assert, Bind.bind, Pure.pure]
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro env hWf clk abstime sleepTs len flags
    obtain ⟨ts, envGet, hRunGet, hWfGet, hBudGet, _⟩ :=
      refinesHealthy_clock_gettime_ok healthyModelOps_refinesHealthyTimeRand env clk hWf
    have hStepGet := healthyModelOps_refinesHealthyTimeRand env (.clock_gettime clk) hWf
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepGet
    have hStepSleep := healthyModelOps_refinesHealthyTimeRand env (.clock_nanosleep clk abstime sleepTs) hWf
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepSleep
    have hStepRand := healthyModelOps_refinesHealthyTimeRand env (.getrandom len flags) hWf
    dsimp only [id, execTimeRandReq, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStepRand
    refine ⟨?_, ?_, ?_, fun _ _ _ => ⟨rfl, trivial⟩⟩
    · have hLiftG : (healthyModelOps.clock_gettime clk).run env =
          (let (mGet, sGet) := (modelOps.clock_gettime clk).run env.state; (mGet, { env with state := sGet })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.clock_gettime clk).run env.state <;> rfl
      show (healthyModelOps.clock_gettime clk).run env =
          (let (mGet, sGet) := (modelOps.clock_gettime clk).run env.state; (mGet, { env with state := sGet })) ∧
        (∃ ts, (healthyModelOps.clock_gettime clk env).1 = .ok ts) ∧
        healthyStep env (.clock_gettime clk) (outcomeOfTimespec (healthyModelOps.clock_gettime clk env).1) =
          some (healthyModelOps.clock_gettime clk env).2 ∧
        (healthyModelOps.clock_gettime clk env).2.wf = true ∧
        (healthyModelOps.clock_gettime clk env).2.eintrBudget = env.eintrBudget
      change healthyModelOps.clock_gettime clk env = (.ok ts, envGet) at hRunGet
      refine ⟨hLiftG, ?_⟩
      rw [hRunGet] at hStepGet ⊢
      dsimp only at hStepGet ⊢
      exact ⟨⟨ts, rfl⟩, hStepGet, hWfGet, hBudGet⟩
    · have hLiftS : (healthyModelOps.clock_nanosleep clk abstime sleepTs).run env =
          (let (mSleep, sSleep) := (modelOps.clock_nanosleep clk abstime sleepTs).run env.state; (mSleep, { env with state := sSleep })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.clock_nanosleep clk abstime sleepTs).run env.state <;> rfl
      show (healthyModelOps.clock_nanosleep clk abstime sleepTs).run env =
          (let (mSleep, sSleep) := (modelOps.clock_nanosleep clk abstime sleepTs).run env.state; (mSleep, { env with state := sSleep })) ∧
        healthyStep env (.clock_nanosleep clk abstime sleepTs)
          (outcomeOfUnit (healthyModelOps.clock_nanosleep clk abstime sleepTs env).1) =
          some (healthyModelOps.clock_nanosleep clk abstime sleepTs env).2 ∧
        (healthyModelOps.clock_nanosleep clk abstime sleepTs env).2.wf = true ∧
        (healthyModelOps.clock_nanosleep clk abstime sleepTs env).2.eintrBudget = env.eintrBudget
      refine ⟨hLiftS, ?_⟩
      cases hS : healthyModelOps.clock_nanosleep clk abstime sleepTs env with
      | mk rSleep envSleep =>
        rw [hS] at hStepSleep
        dsimp only at hStepSleep ⊢
        have hWfS := (healthyStep_implies_allowedStep env envSleep _ _ hStepSleep).2.2.1
        have hBudS : envSleep.eintrBudget = env.eintrBudget := by
          dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
            get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set] at hS
          cases modelOps.clock_nanosleep clk abstime sleepTs env.state with
          | mk r0 s0 =>
            injection hS with _ hEnvEq
            rw [← hEnvEq]
        exact ⟨hStepSleep, hWfS, hBudS⟩
    · have hLiftR : (healthyModelOps.getrandom len flags).run env =
          (let (mRand, sRand) := (modelOps.getrandom len flags).run env.state; (mRand, { env with state := sRand })) := by
        dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
          get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set]
        cases (modelOps.getrandom len flags).run env.state <;> rfl
      show (healthyModelOps.getrandom len flags).run env =
          (let (mRand, sRand) := (modelOps.getrandom len flags).run env.state; (mRand, { env with state := sRand })) ∧
        healthyStep env (.getrandom len flags)
          (outcomeOfBytes (healthyModelOps.getrandom len flags env).1) =
          some (healthyModelOps.getrandom len flags env).2 ∧
        (healthyModelOps.getrandom len flags env).2.wf = true ∧
        (healthyModelOps.getrandom len flags env).2.eintrBudget = env.eintrBudget
      refine ⟨hLiftR, ?_⟩
      cases hR : healthyModelOps.getrandom len flags env with
      | mk rRand envRand =>
        rw [hR] at hStepRand
        dsimp only at hStepRand ⊢
        have hWfR := (healthyStep_implies_allowedStep env envRand _ _ hStepRand).2.2.1
        have hBudR : envRand.eintrBudget = env.eintrBudget := by
          dsimp only [healthyModelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure,
            get, MonadStateOf.get, getThe, StateT.get, set, MonadStateOf.set, StateT.set] at hR
          cases modelOps.getrandom len flags env.state with
          | mk r0 s0 =>
            injection hR with _ hEnvEq
            rw [← hEnvEq]
        exact ⟨hStepRand, hWfR, hBudR⟩

/-- Reachability witness for `test_timerand_healthyStep_and_healthyModelOps`. -/
theorem reach_timerand_healthyStep_and_healthyModelOps :
    CanReach test_timerand_healthyStep_and_healthyModelOps := by
  have hAll := proof_timerand_healthyStep_and_healthyModelOps
  have hRest := hAll.2.2.2.2.2 (HealthyEnv.initial 1 0 false) rfl .monotonic false { sec := 0, nsec := 0 } 0 {}
  refine ⟨hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1, hAll.2.2.2.2.1,
    HealthyEnv.initial 1 0 false, rfl, .monotonic, false, { sec := 0, nsec := 0 }, 0, {},
    hRest.1, hRest.2.1, hRest.2.2.1,
    HealthyEnv.initial 1 0 false, .clock_gettime .monotonic, .timespec { sec := 0, nsec := 0 }, ?_⟩
  exact hRest.2.2.2 (HealthyEnv.initial 1 0 false) (.clock_gettime .monotonic) (.timespec { sec := 0, nsec := 0 })

private theorem decodeRawClockId?_toRaw (clk : ClockId) :
    Model.decodeRawClockId? clk.toRaw = some clk := by
  cases clk <;> rfl

private theorem decodeRawAbstime?_ite (b : Bool) :
    Model.decodeRawAbstime? (if b then 1 else 0) = some b := by
  cases b <;> rfl

private theorem decodeRawGrndFlags?_toBits (f : GrndFlags) :
    Model.decodeRawGrndFlags? f.toBits = some f := by
  rcases f with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

@[simp] private theorem stateT_bind_eq {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    StateT.bind x f w = f (x w).1 (x w).2 := rfl

@[simp] private theorem stateT_pure_eq {W α : Type} (a : α) (w : W) :
    StateT.pure (m := Id) a w = (a, w) := rfl

@[simp] private theorem stateT_map_eq {W α β : Type} (g : α → β) (x : StateM W α) (w : W) :
    StateT.map g x w = (g (x w).1, (x w).2) := rfl

private theorem mkTimeRandOps_obeysStepFrom :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkTimeRandOps Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases req with
  | clock_gettime clk =>
    have hStep := hRaw w (.clock_gettime clk.toRaw) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.execPkgStep, execTimeRandReq,
      Internal.mkTimeRandOps, Internal.mkTimeRandOpsM, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep,
      decodeRawClockId?_toRaw] at hStep ⊢
    rcases hCall : raw.clock_gettime clk.toRaw w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res with
    | ok pair =>
      rcases pair with ⟨sec, nsec⟩
      simpa [Model.outcomeOfRawGettime, Model.toModelOutcome, outcomeOfTimespec] using hStep
    | error e =>
      simpa [Model.outcomeOfRawGettime, Model.toModelOutcome, outcomeOfTimespec] using hStep
  | clock_nanosleep clk abstime reqTs =>
    rcases reqTs with ⟨sec, nsec⟩
    have hStep := hRaw w (.clock_nanosleep clk.toRaw (if abstime then 1 else 0) sec nsec) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.execPkgStep, execTimeRandReq,
      Internal.mkTimeRandOps, Internal.mkTimeRandOpsM, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep,
      decodeRawClockId?_toRaw, decodeRawAbstime?_ite] at hStep ⊢
    rcases hCall : raw.clock_nanosleep clk.toRaw (if abstime then 1 else 0) sec nsec w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getrandom len flags =>
    have hStep := hRaw w (.getrandom len flags.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.execPkgStep, execTimeRandReq,
      Internal.mkTimeRandOps, Internal.mkTimeRandOpsM, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedPkgStep,
      decodeRawGrndFlags?_toBits] at hStep ⊢
    rcases hCall : raw.getrandom len flags.toBits w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep

private theorem rawHealthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  cases req with
  | clock_gettime clkRaw =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.rawHealthyModelOps,
      Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_map_eq]
    cases hDec : Model.decodeRawClockId? clkRaw with
    | none => simp [Model.outcomeOfRawGettime]
    | some clk =>
      simp only [stateT_bind_eq]
      have hStep := healthyModelOps_refinesHealthyTimeRand env (.clock_gettime clk) hWf
      simp only [id, execTimeRandReq, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq] at hStep
      rcases hCall : healthyModelOps.clock_gettime clk env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res with
      | ok ts =>
        rcases ts with ⟨sec, nsec⟩
        simpa [Model.outcomeOfRawGettime, Model.toModelOutcome, outcomeOfTimespec] using hStep
      | error e =>
        simpa [Model.outcomeOfRawGettime, Model.toModelOutcome, outcomeOfTimespec] using hStep
  | clock_nanosleep clkRaw absRaw sec nsec =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.rawHealthyModelOps,
      Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_map_eq]
    cases hClk : Model.decodeRawClockId? clkRaw with
    | none => simp [Model.outcomeOfRawUnit]
    | some clk =>
      cases hAbs : Model.decodeRawAbstime? absRaw with
      | none => simp [Model.outcomeOfRawUnit]
      | some abstime =>
        dsimp only
        have hStep := healthyModelOps_refinesHealthyTimeRand env
          (.clock_nanosleep clk abstime { sec := sec, nsec := nsec }) hWf
        simp only [id, execTimeRandReq, Bind.bind, Pure.pure,
          StateT.run, stateT_bind_eq, stateT_pure_eq] at hStep
        rcases hCall : healthyModelOps.clock_nanosleep clk abstime { sec := sec, nsec := nsec } env with ⟨res, env'⟩
        rw [hCall] at hStep
        cases res <;>
          simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getrandom len flagsBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.rawHealthyModelOps,
      Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_map_eq]
    cases hFlg : Model.decodeRawGrndFlags? flagsBits with
    | none => simp [Model.outcomeOfRawBytes]
    | some flags =>
      dsimp only
      have hStep := healthyModelOps_refinesHealthyTimeRand env (.getrandom len flags) hWf
      simp only [id, execTimeRandReq, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq] at hStep
      rcases hCall : healthyModelOps.getrandom len flags env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep

private theorem sleepMonoTimespec_isValid (ms : Nat) :
    (Model.sleepMonoTimespec ms).isValid = true := by
  unfold Model.sleepMonoTimespec Timespec.isValid NSEC_PER_SEC MAX_TIMESPEC_SEC
  dsimp only
  have hCl : Nat.min (ms / 1000) 9223372036854775807 ≤ 9223372036854775807 := Nat.min_le_right _ _
  rw [Bool.and_eq_true]
  simp only [decide_eq_true_eq, Int.ofNat_eq_natCast]
  constructor
  · rw [Int64.toInt_ofInt, Int.bmod_eq_of_le]
    · omega
    · change -9223372036854775808 ≤ (↑(Nat.min (ms / 1000) 9223372036854775807) : Int); omega
    · change (↑(Nat.min (ms / 1000) 9223372036854775807) : Int) < 9223372036854775808; omega
  · have hMod : ms % 1000 < 1000 := Nat.mod_lt ms (by decide)
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by change ms % 1000 * 1000000 < 4294967296; omega)]
    omega

private theorem monoNowMs_obeysStepFrom :
    Core.ObeysStepFrom (PkgApi := Model.MonoNowMsAct)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.TimeRand.monoNowMs
      Model.execMonoNowMs Model.allowedMonoNowMs := by
  intro W proj ops hOps w _ hWf
  dsimp only [Function.comp, id] at hWf ⊢
  obtain ⟨ts, w', hRun, _, _, _⟩ := refinesHealthy_clock_gettime_ok hOps w .monotonic hWf
  have hStep := hOps w (.clock_gettime .monotonic) hWf
  change ops.clock_gettime .monotonic w = (.ok ts, w') at hRun
  simp only [Model.execPkgStep, execTimeRandReq, Model.allowedPkgStep,
    Model.execMonoNowMs, LeanSwe.LinuxSyscall.TimeRand.monoNowMs,
    Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq,
    hRun, outcomeOfTimespec] at hStep ⊢
  exact ⟨ts, rfl, hStep⟩

private theorem checkTimedOut_obeysStepFrom :
    Core.ObeysStepFrom (PkgApi := Model.CheckTimedOutFn)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.TimeRand.checkTimedOut
      Model.execCheckTimedOut Model.allowedCheckTimedOut := by
  intro W proj ops hOps w req hWf
  dsimp only [Function.comp, id] at hWf ⊢
  rcases req with ⟨startMs, timeoutMs?⟩
  cases timeoutMs? with
  | none =>
    simp [Model.execCheckTimedOut, LeanSwe.LinuxSyscall.TimeRand.checkTimedOut,
      Model.allowedCheckTimedOut, Pure.pure, StateT.run, stateT_pure_eq, hWf]
  | some timeoutMs =>
    obtain ⟨ts, w', hRun, _, _, _⟩ := refinesHealthy_clock_gettime_ok hOps w .monotonic hWf
    have hStep := hOps w (.clock_gettime .monotonic) hWf
    change ops.clock_gettime .monotonic w = (.ok ts, w') at hRun
    simp only [Model.execPkgStep, execTimeRandReq, Model.allowedPkgStep,
      Model.execCheckTimedOut, LeanSwe.LinuxSyscall.TimeRand.checkTimedOut,
      LeanSwe.LinuxSyscall.TimeRand.monoNowMs, Model.allowedCheckTimedOut,
      Model.checkTimedOutFromNow, LeanSwe.LinuxSyscall.TimeRand.timespecToMs, Model.timespecToMs,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq,
      hRun, outcomeOfTimespec] at hStep ⊢
    by_cases hGe : ts.sec.toInt.toNat * 1000 + ts.nsec.toNat / 1000000 - startMs ≥ timeoutMs <;>
      simp only [hGe, ↓reduceIte, stateT_pure_eq] <;>
      exact ⟨ts, by simp only [hGe, ↓reduceIte], hStep⟩

private theorem sleepMonoMs_obeysStepFrom :
    Core.ObeysStepFrom (PkgApi := Model.SleepMonoMsFn)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.TimeRand.sleepMonoMs
      Model.execSleepMonoMs Model.allowedSleepMonoMs := by
  intro W proj ops hOps w ms hWf
  dsimp only [Function.comp, id] at hWf ⊢
  have hStep := hOps w (.clock_nanosleep .monotonic false (Model.sleepMonoTimespec ms)) hWf
  simp only [Model.execPkgStep, execTimeRandReq, Model.allowedPkgStep,
    Model.execSleepMonoMs, LeanSwe.LinuxSyscall.TimeRand.sleepMonoMs,
    Model.sleepMonoTimespec, Model.allowedSleepMonoMs, Bind.bind, Pure.pure,
    StateT.run, stateT_bind_eq, stateT_pure_eq] at hStep ⊢
  rcases hCall :
    ops.clock_nanosleep .monotonic false
      { sec := Int64.ofInt (Int.ofNat (Nat.min (ms / 1000) MAX_TIMESPEC_SEC))
        nsec := UInt32.ofNat (ms % 1000 * 1000000) } w with ⟨res, w'⟩
  rw [hCall] at hStep
  cases res with
  | ok u =>
    cases u
    exact Or.inl hStep
  | error e =>
    rcases healthyStep_implies_allowedStep (proj w) (proj w')
      (.clock_nanosleep .monotonic false (Model.sleepMonoTimespec ms)) (.err e) hStep
      with ⟨hAl, _, _, _, _, _⟩
    have hSecF : (proj w).state.ambientSeccomp = false := by
      unfold HealthyEnv.wf at hWf
      cases hb : (proj w).state.ambientSeccomp <;> simp_all
    have hCore : allowedStepCore (proj w).state
        (.clock_nanosleep .monotonic false (Model.sleepMonoTimespec ms)) (.err e) =
        some (proj w').state := by
      simpa [allowedStep, hSecF] using hAl
    have hVal := sleepMonoTimespec_isValid ms
    simp only [allowedStepCore, hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCore
    by_cases hEq : e = Errno.EINTR
    · subst hEq
      exact Or.inr hStep
    · have hNe : (e == Errno.EINTR) = false := beq_false_of_ne hEq
      simp [hNe] at hCore

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.LinuxSyscall.TimeRand` against `Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.LinuxSyscall.TimeRand.timespecToMs Model.timespecToMs ∧
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkTimeRandOps Model.execPkgStep Model.allowedPkgStep ∧
    Core.ObeysStepFrom (PkgApi := Model.MonoNowMsAct)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.TimeRand.monoNowMs
      Model.execMonoNowMs Model.allowedMonoNowMs ∧
    Core.ObeysStepFrom (PkgApi := Model.CheckTimedOutFn)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.TimeRand.checkTimedOut
      Model.execCheckTimedOut Model.allowedCheckTimedOut ∧
    Core.ObeysStepFrom (PkgApi := Model.SleepMonoMsFn)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.TimeRand.sleepMonoMs
      Model.execSleepMonoMs Model.allowedSleepMonoMs :=
  ⟨fun _ => rfl,
   mkTimeRandOps_obeysStepFrom,
   monoNowMs_obeysStepFrom,
   checkTimedOut_obeysStepFrom,
   sleepMonoMs_obeysStepFrom⟩

/-- Non-vacuity witness for `LeanSwe.LinuxSyscall.TimeRand` `obeys_model` (`HealthyEnv.wf`, `allowedRawStep`, `allowedPkgStep`, and all combinator step relations are simultaneously inhabited). -/
theorem obeys_model_nonvacuous :
    (∃ env₀ : HealthyEnv, HealthyEnv.wf env₀ = true) ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep healthyModelOps) Model.allowedPkgStep ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execMonoNowMs (LeanSwe.LinuxSyscall.TimeRand.monoNowMs healthyModelOps))
      Model.allowedMonoNowMs ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execCheckTimedOut (LeanSwe.LinuxSyscall.TimeRand.checkTimedOut healthyModelOps))
      Model.allowedCheckTimedOut ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execSleepMonoMs (LeanSwe.LinuxSyscall.TimeRand.sleepMonoMs healthyModelOps))
      Model.allowedSleepMonoMs :=
  ⟨⟨HealthyEnv.initial, rfl⟩,
   rawHealthyModelOps_obeysStep,
   healthyModelOps_refinesHealthyTimeRand,
   monoNowMs_obeysStepFrom id healthyModelOps healthyModelOps_refinesHealthyTimeRand,
   checkTimedOut_obeysStepFrom id healthyModelOps healthyModelOps_refinesHealthyTimeRand,
   sleepMonoMs_obeysStepFrom id healthyModelOps healthyModelOps_refinesHealthyTimeRand⟩

end LeanSwe.LinuxSyscall.TimeRand.Proofs
