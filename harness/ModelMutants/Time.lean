import Core.Obeys
import LeanSwe.Time.Types
import LeanSwe.Time.Model

/-!
# Targeted Dummy Mutants and Satisfiability Witness for `LeanSwe.Time.Model`

Proves that broken `TimeApiM` implementations (`constZeroClockApi`,
`zeroElapsedMeasureApi`, `noOpSleepApi`) fail `LeanSwe.Time.Model.allowedPkgStep`
under `Core.ObeysStep`, and proves `LeanSwe.Time.Model.allowedTimeOpsStep` and
`LeanSwe.Time.Model.allowedPkgStep` are satisfiable via reference implementations
`refTimeOps` and `refTimeApi`.
-/

namespace ModelMutants.Time

open LeanSwe.Time
open LeanSwe.Time.Model

private theorem stateM_map_run {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

private theorem stateM_bind_run {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    (x >>= f).run w = (f (x.run w).1).run (x.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

private theorem stateM_get_run {W : Type} (w : W) :
    (get : StateM W W).run w = (w, w) := rfl

private theorem stateM_modify_run {W : Type} (f : W → W) (w : W) :
    (modify f : StateM W Unit).run w = ((), f w) := rfl

private theorem toNanoseconds_ofNanoseconds (n : Std.Time.Nanosecond.Offset) :
    (Std.Time.Duration.ofNanoseconds n).toNanoseconds = n := by
  apply Std.Time.Internal.UnitVal.ext
  change (n.val.tdiv 1000000000) * 1000000000 + (n.val.tmod 1000000000) = n.val
  have h := Int.mul_tdiv_add_tmod n.val 1000000000
  omega

private theorem toNanoseconds_timestampOfNanos (ns : Int) :
    (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
      (Std.Time.Nanosecond.Offset.ofInt ns)).toNanosecondsSinceUnixEpoch.val = ns := by
  exact congrArg Std.Time.Internal.UnitVal.val
    (toNanoseconds_ofNanoseconds (Std.Time.Nanosecond.Offset.ofInt ns))

/-- Reference `TimeOpsM (StateM TimeModelState)` satisfying `allowedTimeOpsStep`. -/
def refTimeOps : TimeOpsM (StateM TimeModelState) :=
  { nowTimestamp := do
      let s ← get
      pure (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
        (Std.Time.Nanosecond.Offset.ofInt s.wallNanos))
    monoNanosNow := do
      let s ← get
      pure s.monoNanos
    sleep := fun ms =>
      modify fun s => { s with monoNanos := s.monoNanos + ms.toNat * 1000000 } }

/-- Reference `TimeApiM (StateM TimeModelState)` satisfying `allowedPkgStep`. -/
def refTimeApi : TimeApiM (StateM TimeModelState) :=
  { nowTimestamp := refTimeOps.nowTimestamp
    monoNanosNow := refTimeOps.monoNanosNow
    sleepMs := fun ms =>
      modify fun s => { s with monoNanos := s.monoNanos + ms * 1000000 }
    sleepDuration := fun d =>
      modify fun s => { s with monoNanos := s.monoNanos + sleepNanosLowerBound d }
    measure := fun act => do
      let startMono ← refTimeOps.monoNanosNow
      let out ← act
      let stopMono ← refTimeOps.monoNanosNow
      pure (out, elapsedDuration startMono stopMono)
    elapsedDuration := elapsedDuration
    deadlineNanos := deadlineNanos
    isMonoExpired := isMonoExpired
    formatUtcIso8601 := formatUtcIso8601
    parseUtcIso8601 := parseUtcIso8601
    formatUtcCompact := formatUtcCompact
    formatUtcDate := formatUtcDate
    parseUtcDate := parseUtcDate
    utcDateOfTimestamp := utcDateOfTimestamp
    timestampOfUtcDate := timestampOfUtcDate }

/-- Broken dummy `TimeApiM` whose `nowTimestamp` always returns epoch `0` and whose `monoNanosNow` always returns `0`. -/
def constZeroClockApi : TimeApiM (StateM TimeModelState) :=
  { refTimeApi with
    nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
    monoNanosNow := pure 0 }

/-- Broken dummy `TimeApiM` whose `measure` ignores elapsed time and always returns `elapsed = 0`. -/
def zeroElapsedMeasureApi : TimeApiM (StateM TimeModelState) :=
  { refTimeApi with
    measure := fun act => do
      let out ← act
      pure (out, 0) }

/-- Broken dummy `TimeApiM` whose `sleepMs` and `sleepDuration` are no-ops that never advance time. -/
def noOpSleepApi : TimeApiM (StateM TimeModelState) :=
  { refTimeApi with
    sleepMs := fun _ => pure ()
    sleepDuration := fun _ => pure () }

/-- No `TimeApiM (StateM W)` whose `monoNanosNow` always returns `0` can satisfy `allowedPkgStep`
    from any well-formed state `w0` (sleeping 1 ms advances monotonic time past `0`). -/
theorem any_constZeroMonoClock_fails_model {W : Type} (proj : W → TimeModelState)
    (api : TimeApiM (StateM W))
    (hZero : ∀ w : W, (api.monoNanosNow.run w).1 = 0)
    (w0 : W) (hw0 : pkgWf (proj w0) = true) :
    ¬ Core.ObeysStep proj pkgWf (execPkgStep api) allowedPkgStep := by
  intro hObeys
  have hSleep := hObeys w0 (.sleepMs 1) hw0
  dsimp only [execPkgStep] at hSleep
  rw [stateM_bind_run, stateM_pure_run] at hSleep
  cases hs : (api.sleepMs 1).run w0 with
  | mk u w1 =>
    rw [hs] at hSleep
    dsimp only [allowedPkgStep] at hSleep
    rcases hSleep with ⟨hMono1, _, hVal1⟩
    have hw1 : pkgWf (proj w1) = true := hVal1
    have hRead := hObeys w1 .monoNanosNow hw1
    dsimp only [execPkgStep] at hRead
    rw [stateM_map_run] at hRead
    cases hr : api.monoNanosNow.run w1 with
    | mk ns w2 =>
      have hns : ns = 0 := by
        have hz := hZero w1
        rw [hr] at hz
        exact hz
      subst hns
      rw [hr] at hRead
      dsimp only [allowedPkgStep] at hRead
      rcases hRead with ⟨hMono2, hEq, _, _⟩
      omega

/-- `constZeroClockApi` fails `allowedPkgStep` under `Core.ObeysStepId`. -/
theorem constZeroClockApi_fails_model_id :
    ¬ Core.ObeysStepId pkgWf (execPkgStep constZeroClockApi) allowedPkgStep :=
  any_constZeroMonoClock_fails_model id constZeroClockApi (fun _ => rfl) {} (by decide)

/-- A `TimeApiM` whose `nowTimestamp` always returns epoch `0` also fails `allowedPkgStep` at any post-epoch state. -/
theorem constZeroWallClock_fails_model_id :
    ¬ Core.ObeysStepId pkgWf
      (execPkgStep { refTimeApi with nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) })
      allowedPkgStep := by
  intro hObeys
  have hStep := hObeys { wallNanos := 1, monoNanos := 0 } .nowTimestamp (by decide)
  have hRun : (execPkgStep { refTimeApi with nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0) } .nowTimestamp).run
      { wallNanos := 1, monoNanos := 0 } =
      (.nowTimestamp (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0), { wallNanos := 1, monoNanos := 0 }) := rfl
  rw [hRun] at hStep
  dsimp only [allowedPkgStep, id] at hStep
  rcases hStep with ⟨_, _, hEq, _⟩
  have hz : (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0).toNanosecondsSinceUnixEpoch.val = 0 := by
    decide
  rw [hz] at hEq
  omega

/-- No `TimeApiM (StateM W)` whose `measure` always returns `elapsed = 0` can satisfy `allowedPkgStep`
    from any well-formed state `w0` (measuring a 1 ms sleep requires `elapsed ≥ 1_000_000 ns`). -/
theorem any_zeroElapsedMeasure_fails_model {W : Type} (proj : W → TimeModelState)
    (api : TimeApiM (StateM W))
    (hZero : ∀ w : W, ((api.measure (execStepAction api (.sleepMsNat 1 0))).run w).1.2 = 0)
    (w0 : W) (hw0 : pkgWf (proj w0) = true) :
    ¬ Core.ObeysStep proj pkgWf (execPkgStep api) allowedPkgStep := by
  intro hObeys
  have hStep := hObeys w0 (.measure (.sleepMsNat 1 0)) hw0
  dsimp only [execPkgStep] at hStep
  rw [stateM_map_run] at hStep
  cases hm : (api.measure (execStepAction api (.sleepMsNat 1 0))).run w0 with
  | mk res w1 =>
    cases res with
    | mk val elapsed =>
      have hel : elapsed = 0 := by
        have hz := hZero w0
        rw [hm] at hz
        exact hz
      subst hel
      rw [hm] at hStep
      dsimp only [allowedPkgStep] at hStep
      rcases hStep with ⟨sBefore, sMid, _, _, _, hAct, hMidLe, _, _, hElEq⟩
      dsimp only [allowedStepAction] at hAct
      rcases hAct with ⟨_, hSleepLe, _, _⟩
      have hLe : sBefore.monoNanos ≤ (proj w1).monoNanos := by omega
      have hPos : 1000000 ≤ (proj w1).monoNanos - sBefore.monoNanos := by omega
      dsimp only [elapsedDuration] at hElEq
      simp only [hLe, ↓reduceIte] at hElEq
      have hVal := congrArg (fun d : Std.Time.Duration => d.toNanoseconds.val) hElEq
      have hZeroNs : (0 : Std.Time.Duration).toNanoseconds.val = 0 := by decide
      have hDiffNs : (Std.Time.Duration.ofNanoseconds
          (Std.Time.Nanosecond.Offset.ofNat ((proj w1).monoNanos - sBefore.monoNanos))).toNanoseconds.val =
          Int.ofNat ((proj w1).monoNanos - sBefore.monoNanos) :=
        congrArg Std.Time.Internal.UnitVal.val
          (toNanoseconds_ofNanoseconds (Std.Time.Nanosecond.Offset.ofNat ((proj w1).monoNanos - sBefore.monoNanos)))
      rw [hZeroNs, hDiffNs] at hVal
      have hSubZero : (proj w1).monoNanos - sBefore.monoNanos = 0 := Int.ofNat.inj hVal.symm
      omega

/-- `zeroElapsedMeasureApi` fails `allowedPkgStep` under `Core.ObeysStepId`. -/
theorem zeroElapsedMeasureApi_fails_model_id :
    ¬ Core.ObeysStepId pkgWf (execPkgStep zeroElapsedMeasureApi) allowedPkgStep :=
  any_zeroElapsedMeasure_fails_model id zeroElapsedMeasureApi (fun _ => rfl) {} (by decide)

/-- No `TimeApiM (StateM W)` whose `sleepMs 1` leaves `monoNanos` unchanged can satisfy `allowedPkgStep`
    from any well-formed state `w0`. -/
theorem any_noOpSleep_fails_model {W : Type} (proj : W → TimeModelState)
    (api : TimeApiM (StateM W))
    (hNoOp : ∀ w : W, (proj ((api.sleepMs 1).run w).2).monoNanos = (proj w).monoNanos)
    (w0 : W) (hw0 : pkgWf (proj w0) = true) :
    ¬ Core.ObeysStep proj pkgWf (execPkgStep api) allowedPkgStep := by
  intro hObeys
  have hStep := hObeys w0 (.sleepMs 1) hw0
  dsimp only [execPkgStep] at hStep
  rw [stateM_bind_run, stateM_pure_run] at hStep
  cases hs : (api.sleepMs 1).run w0 with
  | mk u w1 =>
    have hSame : (proj w1).monoNanos = (proj w0).monoNanos := by
      have hn := hNoOp w0
      rw [hs] at hn
      exact hn
    rw [hs] at hStep
    dsimp only [allowedPkgStep] at hStep
    rcases hStep with ⟨hAdv, _, _⟩
    omega

/-- `noOpSleepApi` fails `allowedPkgStep` under `Core.ObeysStepId`. -/
theorem noOpSleepApi_fails_model_id :
    ¬ Core.ObeysStepId pkgWf (execPkgStep noOpSleepApi) allowedPkgStep :=
  any_noOpSleep_fails_model id noOpSleepApi (fun _ => rfl) {} (by decide)

private theorem refTimeOps_now_run (s : TimeModelState) :
    refTimeOps.nowTimestamp.run s =
      (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
        (Std.Time.Nanosecond.Offset.ofInt s.wallNanos), s) := by
  dsimp only [refTimeOps]
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run]

private theorem refTimeOps_mono_run (s : TimeModelState) :
    refTimeOps.monoNanosNow.run s = (s.monoNanos, s) := by
  dsimp only [refTimeOps]
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run]

private theorem refTimeOps_sleep_run (ms : UInt32) (s : TimeModelState) :
    (refTimeOps.sleep ms).run s = ((), { s with monoNanos := s.monoNanos + ms.toNat * 1000000 }) := by
  dsimp only [refTimeOps]
  rw [stateM_modify_run]

private theorem obeysStepId_of_eq {S Req Out : Type}
    {wf : S → Bool} {exec : Req → StateM S Out} {allowed : S → Req → Out → S → Prop}
    (h : ∀ s req, wf s = true → ∃ out s', (exec req).run s = (out, s') ∧ allowed s req out s') :
    Core.ObeysStepId wf exec allowed := by
  intro s req hwf
  rcases h s req hwf with ⟨out, s', hEq, hAllow⟩
  have h1 : ((exec req).run s).1 = out := congrArg Prod.fst hEq
  have h2 : ((exec req).run s).2 = s' := congrArg Prod.snd hEq
  change allowed s req ((exec req).run s).1 ((exec req).run s).2
  rw [h1, h2]
  exact hAllow

/-- `refTimeOps` satisfies `LeanSwe.Time.Model.allowedTimeOpsStep` under `Core.ObeysStepId`. -/
theorem refTimeOps_obeys_model :
    Core.ObeysStepId pkgWf (execTimeOpsStep refTimeOps) allowedTimeOpsStep := by
  apply obeysStepId_of_eq
  intro s req hwf
  cases req with
  | nowTimestamp =>
    refine ⟨.nowTimestamp (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
        (Std.Time.Nanosecond.Offset.ofInt s.wallNanos)), s, ?_,
      ⟨Int.le_refl s.wallNanos, hwf, toNanoseconds_timestampOfNanos s.wallNanos, Nat.le_refl s.monoNanos⟩⟩
    dsimp only [execTimeOpsStep]
    rw [stateM_map_run, refTimeOps_now_run]
  | monoNanosNow =>
    refine ⟨.monoNanosNow s.monoNanos, s, ?_,
      ⟨Nat.le_refl s.monoNanos, rfl, Int.le_refl s.wallNanos, hwf⟩⟩
    dsimp only [execTimeOpsStep]
    rw [stateM_map_run, refTimeOps_mono_run]
  | sleep ms =>
    refine ⟨.sleep, { s with monoNanos := s.monoNanos + ms.toNat * 1000000 }, ?_,
      ⟨Nat.le_refl _, Int.le_refl s.wallNanos, hwf⟩⟩
    dsimp only [execTimeOpsStep]
    rw [stateM_bind_run, refTimeOps_sleep_run, stateM_pure_run]

private theorem refTimeApi_now_run (s : TimeModelState) :
    refTimeApi.nowTimestamp.run s =
      (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
        (Std.Time.Nanosecond.Offset.ofInt s.wallNanos), s) :=
  refTimeOps_now_run s

private theorem refTimeApi_mono_run (s : TimeModelState) :
    refTimeApi.monoNanosNow.run s = (s.monoNanos, s) :=
  refTimeOps_mono_run s

private theorem refTimeApi_sleepMs_run (ms : Nat) (s : TimeModelState) :
    (refTimeApi.sleepMs ms).run s = ((), { s with monoNanos := s.monoNanos + ms * 1000000 }) := by
  dsimp only [refTimeApi]
  rw [stateM_modify_run]

private theorem refTimeApi_sleepDuration_run (d : Std.Time.Duration) (s : TimeModelState) :
    (refTimeApi.sleepDuration d).run s =
      ((), { s with monoNanos := s.monoNanos + sleepNanosLowerBound d }) := by
  dsimp only [refTimeApi]
  rw [stateM_modify_run]

private theorem pkgWf_with_mono (s : TimeModelState) (m : Nat) (hwf : pkgWf s = true) :
    pkgWf { s with monoNanos := m } = true := by
  dsimp only [pkgWf]
  exact hwf

private theorem refTimeApi_execStepAction (act : StepAction) :
    ∀ (s : TimeModelState), pkgWf s = true →
      ∃ (v : Nat) (s' : TimeModelState),
        (execStepAction refTimeApi act).run s = (v, s') ∧
        allowedStepAction s act v s' ∧
        pkgWf s' = true := by
  induction act with
  | pureNat val =>
    intro s hwf
    refine ⟨val, s, ?_, ⟨rfl, rfl⟩, hwf⟩
    dsimp only [execStepAction]
    exact stateM_pure_run val s
  | sleepMsNat ms val =>
    intro s hwf
    refine ⟨val, { s with monoNanos := s.monoNanos + ms * 1000000 }, ?_,
      ⟨rfl, Nat.le_refl _, Int.le_refl s.wallNanos, hwf⟩, pkgWf_with_mono s _ hwf⟩
    dsimp only [execStepAction]
    rw [stateM_bind_run, refTimeApi_sleepMs_run, stateM_pure_run]
  | sleepDurationNat d val =>
    intro s hwf
    refine ⟨val, { s with monoNanos := s.monoNanos + sleepNanosLowerBound d }, ?_,
      ⟨rfl, Nat.le_refl _, Int.le_refl s.wallNanos, hwf⟩, pkgWf_with_mono s _ hwf⟩
    dsimp only [execStepAction]
    rw [stateM_bind_run, refTimeApi_sleepDuration_run, stateM_pure_run]
  | readMono =>
    intro s hwf
    refine ⟨s.monoNanos, s, ?_,
      ⟨Nat.le_refl s.monoNanos, rfl, Int.le_refl s.wallNanos, hwf⟩, hwf⟩
    dsimp only [execStepAction]
    exact refTimeApi_mono_run s
  | readWallNat val =>
    intro s hwf
    refine ⟨val, s, ?_,
      ⟨rfl, Int.le_refl s.wallNanos, hwf, Nat.le_refl s.monoNanos⟩, hwf⟩
    dsimp only [execStepAction]
    rw [stateM_bind_run, refTimeApi_now_run, stateM_pure_run]
  | seq first second ihFirst ihSecond =>
    intro s hwf
    rcases ihFirst s hwf with ⟨v1, sMid, hRun1, hAct1, hWfMid⟩
    rcases ihSecond sMid hWfMid with ⟨v2, sEnd, hRun2, hAct2, hWfEnd⟩
    refine ⟨v2, sEnd, ?_, ⟨v1, sMid, hAct1, hAct2⟩, hWfEnd⟩
    dsimp only [execStepAction]
    rw [stateM_bind_run, hRun1, hRun2]

private theorem refTimeApi_measure_run {α : Type} (act : StateM TimeModelState α) (s : TimeModelState) :
    (refTimeApi.measure act).run s =
      (((act.run s).1, elapsedDuration s.monoNanos (act.run s).2.monoNanos), (act.run s).2) := by
  change (do
    let startMono ← refTimeOps.monoNanosNow
    let out ← act
    let stopMono ← refTimeOps.monoNanosNow
    pure (out, elapsedDuration startMono stopMono)).run s = _
  rw [stateM_bind_run, refTimeOps_mono_run]
  dsimp only
  rw [stateM_bind_run]
  cases ha : act.run s with
  | mk out sMid =>
    dsimp only
    rw [stateM_bind_run, refTimeOps_mono_run]
    dsimp only
    rw [stateM_pure_run]

/-- `refTimeApi` satisfies `LeanSwe.Time.Model.allowedPkgStep` under `Core.ObeysStepId`. -/
theorem refTimeApi_obeys_model :
    Core.ObeysStepId pkgWf (execPkgStep refTimeApi) allowedPkgStep := by
  apply obeysStepId_of_eq
  intro s req hwf
  cases req with
  | nowTimestamp =>
    refine ⟨.nowTimestamp (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch
        (Std.Time.Nanosecond.Offset.ofInt s.wallNanos)), s, ?_,
      ⟨Int.le_refl s.wallNanos, hwf, toNanoseconds_timestampOfNanos s.wallNanos, Nat.le_refl s.monoNanos⟩⟩
    dsimp only [execPkgStep]
    rw [stateM_map_run, refTimeApi_now_run]
  | monoNanosNow =>
    refine ⟨.monoNanosNow s.monoNanos, s, ?_,
      ⟨Nat.le_refl s.monoNanos, rfl, Int.le_refl s.wallNanos, hwf⟩⟩
    dsimp only [execPkgStep]
    rw [stateM_map_run, refTimeApi_mono_run]
  | sleepMs ms =>
    refine ⟨.unit, { s with monoNanos := s.monoNanos + ms * 1000000 }, ?_,
      ⟨Nat.le_refl _, Int.le_refl s.wallNanos, hwf⟩⟩
    dsimp only [execPkgStep]
    rw [stateM_bind_run, refTimeApi_sleepMs_run, stateM_pure_run]
  | sleepDuration d =>
    refine ⟨.unit, { s with monoNanos := s.monoNanos + sleepNanosLowerBound d }, ?_,
      ⟨Nat.le_refl _, Int.le_refl s.wallNanos, hwf⟩⟩
    dsimp only [execPkgStep]
    rw [stateM_bind_run, refTimeApi_sleepDuration_run, stateM_pure_run]
  | measure act =>
    rcases refTimeApi_execStepAction act s hwf with ⟨val, sMid, hRun, hAct, hMidWf⟩
    refine ⟨.measured (val, elapsedDuration s.monoNanos sMid.monoNanos), sMid, ?_,
      ⟨s, sMid, Nat.le_refl s.monoNanos, Int.le_refl s.wallNanos, hwf, hAct,
        Nat.le_refl sMid.monoNanos, Int.le_refl sMid.wallNanos, hMidWf, rfl⟩⟩
    dsimp only [execPkgStep]
    rw [stateM_map_run, refTimeApi_measure_run, hRun]

/-- Satisfiability witness confirming `LeanSwe.Time.Model.allowedPkgStep` is inhabited. -/
theorem time_model_satisfiable :
    ∃ api : TimeApiM (StateM TimeModelState),
      Core.ObeysStepId pkgWf (execPkgStep api) allowedPkgStep :=
  ⟨refTimeApi, refTimeApi_obeys_model⟩

end ModelMutants.Time
