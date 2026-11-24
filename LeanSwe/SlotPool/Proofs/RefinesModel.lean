import Core.Refines
import LeanSwe.SlotPool.Impl
import LeanSwe.SlotPool.Interface
import LeanSwe.SlotPool.Model.Refines
import LeanSwe.SlotPool.Proofs.SimLemmas

/-!
Package-level single-step refinement proofs relating `LeanSwe.SlotPool.mkApiM` to the pure
domain transitions (`specWithSlot`, `specPollWaitUpTo`, `specPollForever`, `specScanSlots`)
in `LeanSwe.SlotPool.Model.Refines`.
-/

namespace LeanSwe.SlotPool.Proofs

open LeanSwe.Fs (FsApiM FsError LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Model

private theorem if_true_eq {α : Type} {c : Prop} [Decidable c] (a b : α) (h : c) :
    (if c then a else b) = a := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem if_false_eq {α : Type} {c : Prop} [Decidable c] (a b : α) (h : ¬ c) :
    (if c then a else b) = b := by
  cases ‹Decidable c› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

private theorem stateM_map_run {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = let r := x.run w; (f r.1, r.2) := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

private theorem execFsStep_mkdir_eq {W : Type} (fs : FsApiM (StateM W))
    (p : String) (par ex : Bool) (w : W) :
    (execFsStep fs (.mkdir p par ex)).run w =
      let r := (fs.mkdir p par ex).run w; (.mkdirRes r.1, r.2) := rfl

private theorem execFsStep_tryLock_eq {W : Type} (fs : FsApiM (StateM W))
    (p : String) (m : LockMode) (c : Bool) (res : Except SlotPoolError Nat) (w : W) :
    (execFsStep fs (.tryLockRet p m c res)).run w =
      let r := (fs.tryWithFileLock p m c (pure (.ok res))).run w; (.tryLockRes r.1, r.2) := rfl

/-- Concrete witness that `Model.simFs` satisfies `allowedFsStep` over `PoolSimState`. -/
theorem simFs_refines_allowedFsStep :
    Core.RefinesStep id slotPoolStepWf (execFsStep simFs) allowedFsStep := by
  intro s req _
  cases req with
  | join base sub =>
    dsimp only [execFsStep, allowedFsStep, evalFsStep, id]
    rw [stateM_pure_run, show simFs.join = simJoin from rfl]
    exact ⟨rfl, rfl⟩
  | mkdir path parents existOk =>
    dsimp only [allowedFsStep, evalFsStep, specMkdir, id]
    rw [execFsStep_mkdir_eq, simFs_mkdir_run]
    cases simMkdirPure s path parents existOk <;> exact ⟨rfl, rfl⟩
  | tryLockRet path mode createIfMissing res =>
    dsimp only [allowedFsStep, evalFsStep, specTryLockRet, id]
    rw [execFsStep_tryLock_eq, simFs_tryWithFileLock_run]
    cases simTryAcquirePure s path mode createIfMissing with
    | error _ => exact ⟨rfl, rfl⟩
    | ok opt =>
      cases opt with
      | none => exact ⟨rfl, rfl⟩
      | some _ => exact ⟨rfl, rfl⟩

/-- Concrete witness that `Model.simTime` satisfies `allowedTimeStep` over `PoolSimState`. -/
theorem simTime_refines_allowedTimeStep :
    Core.RefinesStep id slotPoolStepWf (execTimeStep simTime) allowedTimeStep := by
  intro s req _
  cases req with
  | monoNanosNow => exact ⟨rfl, rfl⟩
  | sleep ms => exact ⟨rfl, rfl⟩

private theorem raw_fsJoin_eq {W : Type} (proj : W → PoolSimState) (fs : FsApiM (StateM W))
    (hFs : Core.RefinesStep proj slotPoolStepWf (execFsStep fs) allowedFsStep)
    (w : W) (base sub : String) :
    fs.join base sub = simJoin base sub :=
  FsStepOut.path.inj (hFs w (.join base sub) rfl).1

private theorem raw_fsMkdir_eq {W : Type} (proj : W → PoolSimState) (fs : FsApiM (StateM W))
    (hFs : Core.RefinesStep proj slotPoolStepWf (execFsStep fs) allowedFsStep)
    (w : W) (s : PoolSimState) (hs : proj w = s) (path : String) (parents existOk : Bool) :
    let r := (fs.mkdir path parents existOk).run w
    let sp := specMkdir s path parents existOk
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  subst hs
  have h := hFs w (.mkdir path parents existOk) rfl
  dsimp only [execFsStep, allowedFsStep, evalFsStep] at h
  rw [stateM_map_run] at h
  exact ⟨FsStepOut.mkdirRes.inj h.1, h.2⟩

private theorem raw_fsTryLockRet_eq {W : Type} (proj : W → PoolSimState) (fs : FsApiM (StateM W))
    (hFs : Core.RefinesStep proj slotPoolStepWf (execFsStep fs) allowedFsStep)
    (w : W) (s : PoolSimState) (hs : proj w = s) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (res : Except SlotPoolError Nat) :
    let r := (fs.tryWithFileLock path mode createIfMissing (pure (.ok res))).run w
    let sp := specTryLockRet s path mode createIfMissing res
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  subst hs
  have h := hFs w (.tryLockRet path mode createIfMissing res) rfl
  dsimp only [execFsStep, allowedFsStep, evalFsStep] at h
  rw [stateM_map_run] at h
  exact ⟨FsStepOut.tryLockRes.inj h.1, h.2⟩

private theorem raw_timeMonoNanos_eq {W : Type} (proj : W → PoolSimState) (time : TimeOpsM (StateM W))
    (hTime : Core.RefinesStep proj slotPoolStepWf (execTimeStep time) allowedTimeStep)
    (w : W) (s : PoolSimState) (hs : proj w = s) :
    let r := time.monoNanosNow.run w
    r.1 = s.monoNanos ∧ proj r.2 = s := by
  subst hs
  have h := hTime w .monoNanosNow rfl
  dsimp only [execTimeStep, allowedTimeStep, evalTimeStep] at h
  rw [stateM_map_run] at h
  exact ⟨TimeStepOut.nanos.inj h.1, h.2⟩

private theorem execTimeStep_sleep_snd {W : Type} (time : TimeOpsM (StateM W))
    (ms : UInt32) (w : W) :
    ((execTimeStep time (.sleep ms)).run w).2 = ((time.sleep ms).run w).2 := by
  dsimp only [execTimeStep]
  rw [stateM_bind_run]
  cases (time.sleep ms).run w
  rfl

private theorem raw_timeSleep_eq {W : Type} (proj : W → PoolSimState) (time : TimeOpsM (StateM W))
    (hTime : Core.RefinesStep proj slotPoolStepWf (execTimeStep time) allowedTimeStep)
    (w : W) (s : PoolSimState) (hs : proj w = s) (ms : UInt32) :
    proj ((time.sleep ms).run w).2 = specSleepStep s ms := by
  subst hs
  exact (congrArg proj (execTimeStep_sleep_snd time ms w)).symm.trans (hTime w (.sleep ms) rfl).2

private theorem runSleepChunks_cons_snd {W : Type} (time : TimeOpsM (StateM W))
    (c : UInt32) (rest : List UInt32) (w : W) :
    ((runSleepChunks time (c :: rest)).run w).2 =
      ((runSleepChunks time rest).run ((time.sleep c).run w).2).2 := by
  change (let (a, s') := (time.sleep c).run w; (runSleepChunks time rest).run s').2 = _
  cases (time.sleep c).run w
  rfl

private theorem simTime_sleep_snd (c : UInt32) (s : PoolSimState) :
    ((simTime.sleep c).run s).2 = specSleepStep s c := rfl

private theorem runSleepChunks_proj_eq_simTime {W : Type} (proj : W → PoolSimState)
    (time : TimeOpsM (StateM W))
    (hTime : Core.RefinesStep proj slotPoolStepWf (execTimeStep time) allowedTimeStep)
    (cs : List UInt32) :
    ∀ (w : W) (s : PoolSimState),
      proj w = s →
      proj ((runSleepChunks time cs).run w).2 = ((runSleepChunks simTime cs).run s).2 := by
  induction cs with
  | nil =>
    intro _ _ hs
    exact hs
  | cons c rest ih =>
    intro w s hs
    rw [runSleepChunks_cons_snd time c rest w,
      runSleepChunks_cons_snd simTime c rest s,
      simTime_sleep_snd c s]
    exact ih ((time.sleep c).run w).2 (specSleepStep s c)
      (raw_timeSleep_eq proj time hTime w s hs c)

private theorem runSleepChunks_refines_duration {W : Type} (proj : W → PoolSimState)
    (time : TimeOpsM (StateM W))
    (hTime : Core.RefinesStep proj slotPoolStepWf (execTimeStep time) allowedTimeStep)
    (durMs : Nat) (w : W) (s : PoolSimState) (hs : proj w = s) :
    proj ((runSleepChunks time (sleepChunks durMs)).run w).2 =
      specSleepDuration s durMs := by
  rw [runSleepChunks_proj_eq_simTime proj time hTime (sleepChunks durMs) w s hs,
    runSleepChunks_simTime_sleepChunks durMs s]
  rfl

private def scanOutcomeToExcept : Internal.ScanOutcome Nat → Except SlotPoolError (LeaseOutcome Nat)
  | .leased idx val => .ok (.leased idx val)
  | .err e => .error e
  | .allBusy => .ok .noSlot

private theorem scanSlotsM_refines_spec {W : Type} (proj : W → PoolSimState)
    (fs : FsApiM (StateM W))
    (hFs : Core.RefinesStep proj slotPoolStepWf (execFsStep fs) allowedFsStep)
    (poolDir : String) (act : StepAction) (rem : Nat) :
    ∀ (nextIdx : Nat) (w : W) (s : PoolSimState),
      proj w = s →
      let r := (Internal.scanSlotsM fs poolDir nextIdx rem (fun idx => pure (evalStepAction idx act))).run w
      let sp := specScanSlots s poolDir act nextIdx rem
      scanOutcomeToExcept r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  induction rem with
  | zero =>
    intro _ _ _ hs
    exact ⟨rfl, hs⟩
  | succ rem ih =>
    intro nextIdx w s hs
    dsimp only [Internal.scanSlotsM, specScanSlots]
    have hLp : slotLockPath fs.join poolDir nextIdx = slotLockPath simJoin poolDir nextIdx :=
      raw_fsJoin_eq proj fs hFs w poolDir (slotFileName nextIdx)
    have hCb : (do return Except.ok (← (pure (evalStepAction nextIdx act) : StateM W (Except SlotPoolError Nat)))) =
        (pure (.ok (evalStepAction nextIdx act)) : StateM W (Except FsError (Except SlotPoolError Nat))) := rfl
    rw [stateM_bind_run, hLp, hCb]
    let lp := slotLockPath simJoin poolDir nextIdx
    have hTry := raw_fsTryLockRet_eq proj fs hFs w s hs lp .exclusive true (evalStepAction nextIdx act)
    cases hTRun : (fs.tryWithFileLock lp .exclusive true (pure (.ok (evalStepAction nextIdx act)))).run w with
    | mk rTry w1 =>
      rw [hTRun] at hTry
      dsimp only [specTryLockRet] at hTry
      cases hAcq : simTryAcquirePure s lp .exclusive true with
      | error fe =>
        rw [hAcq] at hTry; rw [hTry.1]; exact ⟨rfl, hTry.2⟩
      | ok opt =>
        cases opt with
        | none =>
          rw [hAcq] at hTry; rw [hTry.1]
          exact ih (nextIdx + 1) w1 s hTry.2
        | some sLocked =>
          rw [hAcq] at hTry; rw [hTry.1]
          cases evalStepAction nextIdx act <;> exact ⟨rfl, hTry.2⟩

private theorem pollWaitUpToM_refines_spec {W : Type} (proj : W → PoolSimState)
    (fs : FsApiM (StateM W)) (time : TimeOpsM (StateM W))
    (hFs : Core.RefinesStep proj slotPoolStepWf (execFsStep fs) allowedFsStep)
    (hTime : Core.RefinesStep proj slotPoolStepWf (execTimeStep time) allowedTimeStep)
    (cfg : PoolConfig) (deadlineNs : Nat) (act : StepAction) (fuel : Nat) :
    ∀ (w : W) (s : PoolSimState),
      proj w = s →
      let r := (Internal.pollWaitUpToM fs time cfg deadlineNs
        (fun idx => pure (evalStepAction idx act)) fuel).run w
      let sp := specPollWaitUpTo s cfg deadlineNs act fuel
      r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  induction fuel with
  | zero =>
    intro _ _ hs
    exact ⟨rfl, hs⟩
  | succ fuel ih =>
    intro w s hs
    dsimp only [Internal.pollWaitUpToM, specPollWaitUpTo]
    rw [stateM_bind_run]
    have hSc := scanSlotsM_refines_spec proj fs hFs cfg.poolDir act cfg.totalSlots 0 w s hs
    cases hSRun : (Internal.scanSlotsM fs cfg.poolDir 0 cfg.totalSlots
        (fun idx => pure (evalStepAction idx act))).run w with
    | mk outSc wSc =>
      rw [hSRun] at hSc
      dsimp only at hSc
      cases hSp : specScanSlots s cfg.poolDir act 0 cfg.totalSlots with
      | mk outSp sSc =>
        rw [hSp] at hSc
        dsimp only at hSc
        cases outSc with
        | leased idx val =>
          dsimp only [scanOutcomeToExcept] at hSc
          rw [← hSc.1]
          exact ⟨rfl, hSc.2⟩
        | err e =>
          dsimp only [scanOutcomeToExcept] at hSc
          rw [← hSc.1]
          exact ⟨rfl, hSc.2⟩
        | allBusy =>
          dsimp only [scanOutcomeToExcept] at hSc
          rw [← hSc.1]
          dsimp only
          rw [stateM_bind_run]
          have hNow := raw_timeMonoNanos_eq proj time hTime wSc sSc hSc.2
          cases hNRun : time.monoNanosNow.run wSc with
          | mk nowNs wNow =>
            rw [hNRun] at hNow
            rcases hNow with ⟨rfl, hNow2⟩
            dsimp only at hNow2 ⊢
            by_cases hGe : sSc.monoNanos ≥ deadlineNs
            · rw [if_true_eq _ _ hGe, if_true_eq _ _ hGe]
              exact ⟨rfl, hNow2⟩
            · rw [if_false_eq _ _ hGe, if_false_eq _ _ hGe]
              rw [stateM_bind_run]
              let dur := nextSleepMs cfg.pollIntervalMs sSc.monoNanos deadlineNs
              have hSlp := runSleepChunks_refines_duration proj time hTime dur wNow sSc hNow2
              cases hSlpRun : (runSleepChunks time (sleepChunks dur)).run wNow with
              | mk _ wSlept =>
                rw [hSlpRun] at hSlp
                exact ih wSlept (specSleepDuration sSc dur) hSlp

private theorem pollForeverM_refines_spec {W : Type} (proj : W → PoolSimState)
    (fs : FsApiM (StateM W)) (time : TimeOpsM (StateM W))
    (hFs : Core.RefinesStep proj slotPoolStepWf (execFsStep fs) allowedFsStep)
    (hTime : Core.RefinesStep proj slotPoolStepWf (execTimeStep time) allowedTimeStep)
    (cfg : PoolConfig) (act : StepAction) (fuel : Nat) :
    ∀ (w : W) (s : PoolSimState),
      proj w = s →
      let r := (Internal.pollForeverM fs time cfg
        (fun idx => pure (evalStepAction idx act)) fuel).run w
      let sp := specPollForever s cfg act fuel
      r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  induction fuel with
  | zero =>
    intro _ _ hs
    exact ⟨rfl, hs⟩
  | succ fuel ih =>
    intro w s hs
    dsimp only [Internal.pollForeverM, specPollForever]
    rw [stateM_bind_run]
    have hSc := scanSlotsM_refines_spec proj fs hFs cfg.poolDir act cfg.totalSlots 0 w s hs
    cases hSRun : (Internal.scanSlotsM fs cfg.poolDir 0 cfg.totalSlots
        (fun idx => pure (evalStepAction idx act))).run w with
    | mk outSc wSc =>
      rw [hSRun] at hSc
      dsimp only at hSc
      cases hSp : specScanSlots s cfg.poolDir act 0 cfg.totalSlots with
      | mk outSp sSc =>
        rw [hSp] at hSc
        dsimp only at hSc
        cases outSc with
        | leased idx val =>
          dsimp only [scanOutcomeToExcept] at hSc
          rw [← hSc.1]
          exact ⟨rfl, hSc.2⟩
        | err e =>
          dsimp only [scanOutcomeToExcept] at hSc
          rw [← hSc.1]
          exact ⟨rfl, hSc.2⟩
        | allBusy =>
          dsimp only [scanOutcomeToExcept] at hSc
          rw [← hSc.1]
          dsimp only
          rw [stateM_bind_run]
          have hSlp := runSleepChunks_refines_duration proj time hTime cfg.pollIntervalMs wSc sSc hSc.2
          cases hSlpRun : (runSleepChunks time (sleepChunks cfg.pollIntervalMs)).run wSc with
          | mk _ wSlept =>
            rw [hSlpRun] at hSlp
            exact ih wSlept (specSleepDuration sSc cfg.pollIntervalMs) hSlp

private theorem withSlotM_refines_spec {W : Type} (proj : W → PoolSimState)
    (fs : FsApiM (StateM W)) (time : TimeOpsM (StateM W))
    (hFs : Core.RefinesStep proj slotPoolStepWf (execFsStep fs) allowedFsStep)
    (hTime : Core.RefinesStep proj slotPoolStepWf (execTimeStep time) allowedTimeStep)
    (cfg : PoolConfig) (policy : WaitPolicy) (act : StepAction) (w : W) :
    let r := (Internal.withSlotM fs time cfg policy
      (fun idx => pure (evalStepAction idx act))).run w
    let sp := specWithSlot (proj w) cfg policy act
    r.1 = sp.1 ∧ proj r.2 = sp.2 := by
  dsimp only [Internal.withSlotM, specWithSlot]
  cases validatePoolConfig cfg with
  | error e => exact ⟨rfl, rfl⟩
  | ok _ =>
    dsimp only
    rw [stateM_bind_run]
    have hMk := raw_fsMkdir_eq proj fs hFs w (proj w) rfl cfg.poolDir true true
    cases hMRun : (fs.mkdir cfg.poolDir true true).run w with
    | mk rMk w1 =>
      rw [hMRun] at hMk
      dsimp only [specMkdir] at hMk
      cases hPureMk : simMkdirPure (proj w) cfg.poolDir true true with
      | error fe =>
        rw [hPureMk] at hMk
        rcases hMk with ⟨rfl, hMk2⟩
        exact ⟨rfl, hMk2⟩
      | ok s1 =>
        rw [hPureMk] at hMk
        rcases hMk with ⟨rfl, hMk2⟩
        dsimp only
        cases policy with
        | noWait =>
          rw [stateM_bind_run]
          have hSc := scanSlotsM_refines_spec proj fs hFs cfg.poolDir act cfg.totalSlots 0 w1 s1 hMk2
          cases hSRun : (Internal.scanSlotsM fs cfg.poolDir 0 cfg.totalSlots
              (fun idx => pure (evalStepAction idx act))).run w1 with
          | mk outSc wSc =>
            rw [hSRun] at hSc
            cases outSc <;> exact ⟨hSc.1, hSc.2⟩
        | waitUpTo timeoutMs =>
          rw [stateM_bind_run]
          have hNow := raw_timeMonoNanos_eq proj time hTime w1 s1 hMk2
          cases hNRun : time.monoNanosNow.run w1 with
          | mk startNs w2 =>
            rw [hNRun] at hNow
            rcases hNow with ⟨rfl, hNow2⟩
            exact pollWaitUpToM_refines_spec proj fs time hFs hTime cfg
              (deadlineNanos s1.monoNanos timeoutMs) act maxForeverPolls w2 s1 hNow2
        | waitForever =>
          exact pollForeverM_refines_spec proj fs time hFs hTime cfg act maxForeverPolls w1 s1 hMk2

/-- Compositional single-step refinement lemma for `LeanSwe.SlotPool.mkApiM`. -/
theorem refinesStepFrom2_mkApiM :
    Core.RefinesStepFrom2 id slotPoolStepWf
      execFsStep allowedFsStep
      execTimeStep allowedTimeStep
      slotPoolStepWf LeanSwe.SlotPool.mkApiM
      execPkgStep allowedPkgStep := by
  intro W proj fs time hFs hTime w req _
  cases req with
  | withSlot cfg policy act =>
    dsimp only [execPkgStep, allowedPkgStep, evalPkgStep, LeanSwe.SlotPool.mkApiM,
      Internal.mkApiM, Function.comp_apply, id]
    rw [stateM_map_run]
    have h := withSlotM_refines_spec proj fs time hFs hTime cfg policy act w
    exact ⟨congrArg PkgStepOut.leaseRes h.1, h.2⟩

/-- End-to-end non-vacuity witness instantiating `refinesStepFrom2_mkApiM` with `simFs` and `simTime`. -/
theorem simSlotPool_refines_allowedPkgStep :
    Core.RefinesStep id slotPoolStepWf
      (execPkgStep (LeanSwe.SlotPool.mkApiM simFs simTime)) allowedPkgStep :=
  Eq.mp
    (congrArg
      (fun p => Core.RefinesStep p slotPoolStepWf
        (execPkgStep (LeanSwe.SlotPool.mkApiM simFs simTime)) allowedPkgStep)
      (rfl : (id ∘ id : PoolSimState → PoolSimState) = id))
    (refinesStepFrom2_mkApiM id simFs simTime
      simFs_refines_allowedFsStep simTime_refines_allowedTimeStep)

end LeanSwe.SlotPool.Proofs
