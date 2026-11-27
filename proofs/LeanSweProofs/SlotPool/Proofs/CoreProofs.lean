import LeanSwe.SlotPool.Types
import LeanSweProofs.SlotPool.Model
import LeanSwe.SlotPool.Impl
import LeanSwe.SlotPool.Interface
import LeanSweProofs.SlotPool.SpecTests
import LeanSweProofs.SlotPool.Proofs.SimLemmas

namespace LeanSwe.SlotPool.Proofs

open Core Core.NondetTest LeanSwe.SlotPool.Model
open LeanSwe.Fs (FsApiM FsError LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Internal (ScanOutcome scanSlotsM pollWaitUpToM pollForeverM withSlotM)
open LeanSwe.SlotPool (mkApiM)

private abbrev probeRun {S α : Type} (fs : FsApiM (StateM S)) (p : String) (cb : Nat → StateM S (Except SlotPoolError α)) (k : Nat) (st : S) :=
  (fs.tryWithFileLock (slotLockPath fs.join p k) .exclusive true (do return .ok (← cb k))).run st
private abbrev AllBusyFs {S α : Type} (fs : FsApiM (StateM S)) (p : String) (cb : Nat → StateM S (Except SlotPoolError α)) : Prop := ∀ st k, probeRun fs p cb k st = (.ok none, st)
private theorem maxForeverPolls_eq_succ2 : maxForeverPolls = ((2 ^ 64 - 2) + 1) + 1 := by decide
local macro "unfold_st" : tactic => `(tactic| dsimp only [probeRun, liftFsFirst, StateT.run, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Pure.pure, StateT.pure])
private theorem withSlot_after_mkdir {S α : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) (cfg : PoolConfig) (policy : WaitPolicy) (cb : Nat → StateM S (Except SlotPoolError α)) {s₀ s₁ : S}
    (hVal : validatePoolConfig cfg = .ok cfg) (hMk : (fs.mkdir cfg.poolDir true true).run s₀ = (.ok (), s₁)) :
    ((mkApiM fs time).withSlot cfg policy cb).run s₀ = match policy with
      | .noWait => match (scanSlotsM fs cfg.poolDir 0 cfg.totalSlots cb).run s₁ with | (.leased i v, s) => (.ok (.leased i v), s) | (.err e, s) => (.error e, s) | (.allBusy, s) => (.ok .noSlot, s)
      | .waitUpTo t => let (startNs, s₂) := time.monoNanosNow.run s₁; (pollWaitUpToM fs time cfg (deadlineNanos startNs t) cb maxForeverPolls).run s₂
      | .waitForever => (pollForeverM fs time cfg cb maxForeverPolls).run s₁ := by
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]; rw [internal_validatePoolConfig_eq, hVal]; dsimp only; rw [stateM_bind_run, hMk]; dsimp only
  cases policy with
  | noWait => rw [stateM_bind_run]; cases (scanSlotsM fs cfg.poolDir 0 cfg.totalSlots cb).run s₁ with | mk r _ => cases r <;> rfl
  | waitUpTo _ => rw [stateM_bind_run]; rfl
  | waitForever => rfl
private theorem scanSlotsM_skip {S α : Type} (fs : FsApiM (StateM S)) (p : String) (cb : Nat → StateM S (Except SlotPoolError α)) (st : Nat → S) :
    ∀ n r, (∀ k, n ≤ k → k < n + r → probeRun fs p cb k (st k) = (.ok none, st (k + 1))) → (scanSlotsM fs p n r cb).run (st n) = (.allBusy, st (n + r))
  | _, 0, _ => rfl
  | n, r + 1, hB => by unfold scanSlotsM; rw [stateM_bind_run, internal_slotLockPath_eq]; dsimp only [probeRun] at hB; rw [hB n (Nat.le_refl _) (by omega)]; dsimp only; rw [scanSlotsM_skip fs p cb st (n + 1) r (fun k _ _ => hB k (by omega) (by omega)), show n + 1 + r = n + (r + 1) by omega]
private theorem scanSlotsM_err {S α : Type} (fs : FsApiM (StateM S)) (p : String) (cb : Nat → StateM S (Except SlotPoolError α)) (st : Nat → S) (errIdx : Nat) (fe : FsError) (sEnd : S) :
    ∀ n r, n ≤ errIdx → errIdx < n + r → (∀ k, n ≤ k → k < errIdx → probeRun fs p cb k (st k) = (.ok none, st (k + 1))) → probeRun fs p cb errIdx (st errIdx) = (.error fe, sEnd) → (scanSlotsM fs p n r cb).run (st n) = (.err (mapFsError fe), sEnd)
  | _, 0, _, _, _, _ => by omega
  | n, r + 1, _, _, hB, hE => by
    unfold scanSlotsM; rw [stateM_bind_run, internal_slotLockPath_eq]; by_cases hlt : n < errIdx
    · have hb := hB n (Nat.le_refl _) hlt; dsimp only [probeRun] at hb; rw [hb]; dsimp only; exact scanSlotsM_err fs p cb st errIdx fe sEnd (n + 1) r (by omega) (by omega) (fun k _ h2 => hB k (by omega) h2) hE
    · obtain rfl : n = errIdx := (by omega); dsimp only [probeRun] at hE; rw [hE]; dsimp only; rw [internal_mapFsError_eq]; rfl
private theorem expectedSlotPaths_snoc (join : String → String → String) (p : String) : ∀ n k, expectedSlotPaths join p n (k + 1) = expectedSlotPaths join p n k ++ [slotLockPath join p (n + k)]
  | _, 0 => by simp [expectedSlotPaths]
  | n, k + 1 => by unfold expectedSlotPaths; rw [expectedSlotPaths_snoc join p (n + 1) k, show n + 1 + k = n + (k + 1) by omega]; rfl
private theorem pollWaitUpToM_busy_step {S α : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) (cfg : PoolConfig) (dl : Nat) (cb : Nat → StateM S (Except SlotPoolError α)) (hL : AllBusyFs fs cfg.poolDir cb) (fuel : Nat) (s : S) :
    (pollWaitUpToM fs time cfg dl cb (fuel + 1)).run s = let (nowNs, s1) := time.monoNanosNow.run s; if nowNs ≥ dl then (.ok .noSlot, s1) else let (_, s2) := (runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs nowNs dl))).run s1; (pollWaitUpToM fs time cfg dl cb fuel).run s2 := by
  have hSc := scanSlotsM_skip fs cfg.poolDir cb (fun _ => s) 0 cfg.totalSlots (fun k _ _ => hL s k); conv => lhs; unfold pollWaitUpToM
  rw [stateM_bind_run, hSc]; dsimp only; rw [stateM_bind_run]; cases time.monoNanosNow.run s with | mk nowNs s1 => dsimp only; split; rfl; rw [stateM_bind_run, internal_runSleepChunks_eq, internal_sleepChunks_eq, internal_nextSleepMs_eq]; cases (runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs nowNs dl))).run s1 with | mk _ _ => rfl
private theorem nextSleepMs_bounds {poll nowNs dl : Nat} (hPoll : 1 ≤ poll) (hLt : ¬ nowNs ≥ dl) : 1 ≤ nextSleepMs poll nowNs dl ∧ nextSleepMs poll nowNs dl ≤ poll := by dsimp [nextSleepMs, remainingWaitMs, nanosecondsPerMs]; simp only [hLt, ↓reduceIte]; exact ⟨Nat.le_min.mpr ⟨hPoll, by omega⟩, Nat.min_le_left _ _⟩
/-- Specification 1 (`AllPass`): `defaultTimingModelOps` satisfies exact deadline arithmetic, ceiling sub-ms rounding, clamping, and positive `UInt32` chunk sums. -/
theorem proof_model_timingAndSleepChunks : AllPass (test_slotpool_model_timingAndSleepChunks_exactAndChunked defaultTimingModelOps) := by
  intro startNs timeoutMs nowNs pollIntervalMs ms hPoll; dsimp only [test_slotpool_model_timingAndSleepChunks_exactAndChunked, defaultTimingModelOps, AllPass]; rw [allPass_assert]; refine ⟨rfl, ?_⟩; obtain ⟨hAll, hSum⟩ := sleepChunks_spec ms
  by_cases hge : nowNs ≥ deadlineNanos startNs timeoutMs
  · simp only [hge, ↓reduceIte, allPass_assert, allPass_assert_end, remainingWaitMs, nextSleepMs]; exact ⟨⟨trivial, Nat.min_zero _⟩, hAll, hSum, trivial⟩
  · simp only [hge, ↓reduceIte, allPass_assert, allPass_assert_end]; dsimp only [remainingWaitMs, nextSleepMs, deadlineNanos, nanosecondsPerMs] at hge ⊢; simp only [hge, ↓reduceIte]; have h1 : 1 ≤ (startNs + timeoutMs * 1000000 - nowNs + 999999) / 1000000 := by omega
    exact ⟨⟨h1, by omega, by omega⟩, ⟨Nat.le_min.mpr ⟨hPoll, h1⟩, Nat.min_le_left _ _, Nat.min_le_right _ _, trivial⟩, hAll, hSum, trivial⟩
section
variable {S : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
/-- Specification 2 (`AllPass`): invalid `PoolConfig` values are rejected with `.invalidInput` before any filesystem, clock, or callback effect. -/
theorem proof_validation_invalidConfig_rejectedBeforeEffects : AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects mkApiM fs time) := by
  intro s₀ cfg policy markerPath hInvalid; obtain ⟨e, hVal, hKind, hPath, hMsg⟩ := validatePoolConfig_of_false cfg hInvalid; dsimp only [test_slotpool_validation_invalidConfig_rejectedBeforeEffects, AllPass]; rw [allPass_assert_end]
  rw [show ((mkApiM fs time).withSlot cfg policy fun _ => do let _ ← fs.writeText markerPath "ran"; return (.ok 1 : Except SlotPoolError Nat)).run s₀ = (.error e, s₀) by dsimp only [mkApiM, Internal.mkApiM, withSlotM]; rw [internal_validatePoolConfig_eq, hVal]; rfl]; exact ⟨⟨⟨e, rfl, hKind, hPath, hMsg⟩, rfl⟩, trivial⟩
/-- Specification 3 (`AllPass`): `fs.mkdir` failures map to `SlotPoolError` with preserved `path` and non-empty message before polling or callbacks. -/
theorem proof_mkdir_fsError_propagatedBeforePolling : AllPass (test_slotpool_mkdir_fsError_propagatedBeforePolling mkApiM fs time) := by
  intro s₀ cfg policy markerPath hValid; obtain ⟨hVal, _, _, _⟩ := validatePoolConfig_of_true cfg hValid; dsimp only [test_slotpool_mkdir_fsError_propagatedBeforePolling, AllPass]; cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with | mk mkRes sAfterMk =>
  cases mkRes with | ok _ => intro h; cases h | error fe => dsimp only; rw [allPass_assert_end]; rw [show ((mkApiM fs time).withSlot cfg policy fun _ => do let _ ← fs.writeText markerPath "ran"; return (.ok 1 : Except SlotPoolError Nat)).run s₀ = (.error (mapFsError fe), sAfterMk) by dsimp only [mkApiM, Internal.mkApiM, withSlotM]; rw [internal_validatePoolConfig_eq, hVal]; dsimp only; rw [stateM_bind_run, hMk]; dsimp only; rw [internal_mapFsError_eq]; rfl]; exact ⟨⟨⟨mapFsError fe, rfl, rfl, rfl, mapFsError_nonEmpty fe⟩, rfl⟩, trivial⟩
/-- Specification 4 (`AllPass`): under `WaitPolicy.noWait`, a saturated pool probes every slot once in ascending order and returns `.ok .noSlot` without sleeping or running `action`. -/
theorem proof_noWait_allBusy_returnsNoSlotWithoutSleepOrAction : AllPass (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction mkApiM fs time) := by
  intro s₀ cfg markerPath hValid hMkOk hMarker; obtain ⟨hVal, _, _, _⟩ := validatePoolConfig_of_true cfg hValid; dsimp only [test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction, AllPass]; rw [allPass_assert_end]
  cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with | mk mkRes sAfterMk =>
  obtain rfl : mkRes = .ok () := (by rw [hMk] at hMkOk; exact hMkOk); have hMarker' : ((fs.lstat markerPath).run sAfterMk).1.isOk = false := by rw [hMk] at hMarker; exact hMarker
  have hRun : ∀ (fsB : FsApiM (StateM (S × List String))) (cb : Nat → StateM (S × List String) (Except SlotPoolError Nat)), fsB.join = fs.join → (fsB.mkdir cfg.poolDir true true).run (s₀, []) = (.ok (), (sAfterMk, [])) → (∀ k acc, probeRun fsB cfg.poolDir cb k (sAfterMk, acc) = (.ok none, (sAfterMk, acc ++ [slotLockPath fs.join cfg.poolDir k]))) →
      ((mkApiM fsB (liftTimeFirst time)).withSlot cfg .noWait cb).run (s₀, []) = (.ok .noSlot, (sAfterMk, expectedSlotPaths fs.join cfg.poolDir 0 cfg.totalSlots)) := fun fsB cb hJ hMkL hStep => by
    rw [withSlot_after_mkdir fsB _ cfg .noWait cb hVal hMkL]; have hSc := scanSlotsM_skip fsB cfg.poolDir cb (fun k => (sAfterMk, expectedSlotPaths fs.join cfg.poolDir 0 k)) 0 cfg.totalSlots (fun k _ _ => by rw [hStep, expectedSlotPaths_snoc]; simp); simp only [expectedSlotPaths, Nat.zero_add] at hSc; rw [hSc]
  rw [hRun _ _ rfl (by change (let (a, s') := (fs.mkdir cfg.poolDir true true).run s₀; (a, (s', []))) = _; rw [hMk]) (fun _ _ => rfl)]; exact ⟨⟨rfl, rfl, hMarker'⟩, trivial⟩
/-- Specification 5 (`AllPass`): `tryWithFileLock` errors fail fast without scanning higher slots or running `action` across initial and retry scans. -/
theorem proof_tryLock_fsError_propagatedWithoutRunningAction : AllPass (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction mkApiM fs time) := by
  intro s₀ cfg errIdx retryPoll policy lockFsErr markerPath ⟨hValid, hErrLt⟩ hMkOk hMonoPure hMarker; obtain ⟨hVal, _, _, hPoll⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_tryLock_fsError_propagatedWithoutRunningAction, AllPass]; cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with | mk mkRes sAfterMk =>
  obtain rfl : mkRes = .ok () := (by rw [hMk] at hMkOk; exact hMkOk); have hMono' : (time.monoNanosNow.run sAfterMk).2 = sAfterMk := by rw [hMk] at hMonoPure; exact hMonoPure
  have hMkL : ∀ (fs0 : FsApiM (StateM (S × Nat))), fs0.mkdir = (liftFsFirst (Aux := Nat) fs).mkdir → (fs0.mkdir cfg.poolDir true true).run (s₀, 0) = (.ok (), (sAfterMk, 0)) := fun fs0 h => by rw [h]; change (let (a, s') := (fs.mkdir cfg.poolDir true true).run s₀; (a, (s', 0))) = _; rw [hMk]
  have hMonoLift : ∀ n, ∃ ns, (liftTimeFirst (Aux := Nat) time).monoNanosNow.run (sAfterMk, n) = (ns, (sAfterMk, n)) ∧ ns = (time.monoNanosNow.run sAfterMk).1 := fun n => by
    cases hm : time.monoNanosNow.run sAfterMk with | mk ns sM => have : sM = sAfterMk := (by rw [hm] at hMono'; exact hMono'); subst sM; exact ⟨ns, by change (let (a, s') := time.monoNanosNow.run sAfterMk; (a, (s', n))) = _; rw [hm], rfl⟩
  have hEx : (LockMode.exclusive == LockMode.exclusive) = true := rfl; cases retryPoll with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, allPass_assert_end]
    have hRun : ∀ (fs0 : FsApiM (StateM (S × Nat))) (cb : Nat → StateM (S × Nat) (Except SlotPoolError Nat)), (fs0.mkdir cfg.poolDir true true).run (s₀, 0) = (.ok (), (sAfterMk, 0)) →
        (scanSlotsM fs0 cfg.poolDir 0 cfg.totalSlots cb).run (sAfterMk, 0) = (.err (mapFsError lockFsErr), (sAfterMk, errIdx + 1)) → ((mkApiM fs0 (liftTimeFirst (Aux := Nat) time)).withSlot cfg policy cb).run (s₀, 0) = (.error (mapFsError lockFsErr), (sAfterMk, errIdx + 1)) := fun fs0 cb hM hSc => by
      rw [withSlot_after_mkdir fs0 _ cfg policy cb hVal hM]; cases policy with | noWait => dsimp only; rw [hSc] | waitUpTo _ => dsimp only; obtain ⟨_, hML, _⟩ := hMonoLift 0; rw [hML]; dsimp only; rw [maxForeverPolls_eq_succ2]; unfold pollWaitUpToM; rw [stateM_bind_run, hSc]; rfl | waitForever => dsimp only; rw [maxForeverPolls_eq_succ2]; unfold pollForeverM; rw [stateM_bind_run, hSc]; rfl
    rw [hRun]; · exact ⟨⟨⟨mapFsError lockFsErr, rfl, rfl, rfl, mapFsError_nonEmpty lockFsErr⟩, rfl, by rw [hMk] at hMarker; exact hMarker⟩, trivial⟩
    · exact hMkL _ rfl
    · exact scanSlotsM_err _ cfg.poolDir _ (fun k => (sAfterMk, k)) errIdx lockFsErr (sAfterMk, errIdx + 1) 0 cfg.totalSlots (Nat.zero_le _) (by omega)
        (fun k _ hk => by unfold_st; simp only [beq_self_eq_true, hEx, Bool.and_self, ↓reduceIte, hk]; rfl) (by unfold_st; simp only [beq_self_eq_true, hEx, Bool.and_self, ↓reduceIte, Nat.lt_irrefl]; rfl)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; dsimp only [Bind.bind, NondetTest.assume]; intro hMarkerAfter; rw [allPass_assert_end]
    cases hSleep : (runSleepChunks time (sleepChunks cfg.pollIntervalMs)).run sAfterMk with | mk _ sAfterSleep =>
    have hSleepL : (runSleepChunks (liftTimeFirst (Aux := Nat) time) (sleepChunks cfg.pollIntervalMs)).run (sAfterMk, cfg.totalSlots) = ((), (sAfterSleep, cfg.totalSlots)) := by rw [runSleepChunks_liftTimeFirst, hSleep]
    have hRun1 : ∀ (fs1 : FsApiM (StateM (S × Nat))) (cb : Nat → StateM (S × Nat) (Except SlotPoolError Nat)), (fs1.mkdir cfg.poolDir true true).run (s₀, 0) = (.ok (), (sAfterMk, 0)) →
        (scanSlotsM fs1 cfg.poolDir 0 cfg.totalSlots cb).run (sAfterMk, 0) = (.allBusy, (sAfterMk, cfg.totalSlots)) → (scanSlotsM fs1 cfg.poolDir 0 cfg.totalSlots cb).run (sAfterSleep, cfg.totalSlots) = (.err (mapFsError lockFsErr), (sAfterSleep, cfg.totalSlots + errIdx + 1)) →
        ((mkApiM fs1 (liftTimeFirst (Aux := Nat) time)).withSlot cfg (if policy == .noWait then .waitForever else .waitUpTo cfg.pollIntervalMs) cb).run (s₀, 0) = (.error (mapFsError lockFsErr), (sAfterSleep, cfg.totalSlots + errIdx + 1)) := fun fs1 cb hM hP0 hP1 => by
      rw [withSlot_after_mkdir fs1 _ cfg _ cb hVal hM]; cases (policy == .noWait)
      · simp only [Bool.false_eq_true, ↓reduceIte]; obtain ⟨ns0, hML0, hEq0⟩ := hMonoLift 0; obtain ⟨ns1, hML1, hEq1⟩ := hMonoLift cfg.totalSlots; rw [hEq1.trans hEq0.symm] at hML1; rw [hML0, maxForeverPolls_eq_succ2]; dsimp only; unfold pollWaitUpToM; rw [stateM_bind_run, hP0]; dsimp only; rw [stateM_bind_run, hML1]; dsimp only
        have hNotGe : ¬ (ns0 ≥ deadlineNanos ns0 cfg.pollIntervalMs) := by dsimp [deadlineNanos, nanosecondsPerMs]; omega
        have hNext : nextSleepMs cfg.pollIntervalMs ns0 (deadlineNanos ns0 cfg.pollIntervalMs) = cfg.pollIntervalMs := by dsimp [nextSleepMs, remainingWaitMs]; simp only [hNotGe, ↓reduceIte]; dsimp [deadlineNanos, nanosecondsPerMs]; apply Nat.min_eq_left; omega
        simp only [hNotGe, ↓reduceIte]; rw [internal_nextSleepMs_eq, hNext, stateM_bind_run, internal_runSleepChunks_eq, internal_sleepChunks_eq, hSleepL]; dsimp only; unfold pollWaitUpToM; rw [stateM_bind_run, hP1]; rfl
      · simp only [↓reduceIte]; rw [maxForeverPolls_eq_succ2]; unfold pollForeverM; rw [stateM_bind_run, hP0]; dsimp only; rw [stateM_bind_run, internal_runSleepChunks_eq, internal_sleepChunks_eq, hSleepL]; dsimp only; unfold pollForeverM; rw [stateM_bind_run, hP1]; rfl
    rw [hRun1]; · exact ⟨⟨⟨mapFsError lockFsErr, rfl, rfl, rfl, mapFsError_nonEmpty lockFsErr⟩, rfl, by rw [hSleep] at hMarkerAfter; exact hMarkerAfter⟩, trivial⟩
    · exact hMkL _ rfl
    · rw [show (sAfterMk, cfg.totalSlots) = (sAfterMk, 0 + cfg.totalSlots) by rw [Nat.zero_add]]
      exact scanSlotsM_skip _ cfg.poolDir _ (fun k => (sAfterMk, k)) 0 cfg.totalSlots (fun k _ hk => by have h1 : k < cfg.totalSlots := (by omega); have h2 : k < cfg.totalSlots + errIdx := (by omega); unfold_st; simp only [h1, ↓reduceIte, beq_self_eq_true, hEx, Bool.and_self, h2]; rfl)
    · exact scanSlotsM_err _ cfg.poolDir _ (fun k => (sAfterSleep, cfg.totalSlots + k)) errIdx lockFsErr (sAfterSleep, cfg.totalSlots + errIdx + 1) 0 cfg.totalSlots (Nat.zero_le _) (by omega)
        (fun k _ hk => by have h1 : ¬ cfg.totalSlots + k < cfg.totalSlots := (by omega); have h2 : cfg.totalSlots + k < cfg.totalSlots + errIdx := (by omega); unfold_st; simp only [h1, ↓reduceIte, Nat.add_sub_cancel_left, beq_self_eq_true, hEx, Bool.and_self, h2, Nat.add_assoc]; rfl)
        (by have h1 : ¬ cfg.totalSlots + errIdx < cfg.totalSlots := (by omega); unfold_st; simp only [h1, ↓reduceIte, Nat.add_sub_cancel_left, beq_self_eq_true, hEx, Bool.and_self, Nat.lt_irrefl]; rfl)
/-- Specification 6 (`AllPass`): over arbitrary monotonic `TimeOpsM (StateM S)`, `WaitPolicy.waitUpTo` enforces immediate expiry, sub-ms ceiling rounding, budget clamping, and `UInt32` chunking. -/
theorem proof_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep : AllPass (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep mkApiM fs time) := by
  intro s₀ cfg timeoutMs hValid _ hMkOk _; obtain ⟨hVal, _, _, hPoll⟩ := validatePoolConfig_of_true cfg hValid; dsimp only [test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep, AllPass]; cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with | mk mkRes s₁ =>
  obtain rfl : mkRes = .ok () := (by rw [hMk] at hMkOk; exact hMkOk); dsimp only; cases hStart : time.monoNanosNow.run s₁ with | mk startNs s₂ =>
  let dl := deadlineNanos startNs timeoutMs; obtain ⟨f, hF⟩ : ∃ f, maxForeverPolls = f + 1 + 1 + 1 := ⟨2 ^ 64 - 3, by decide⟩
  have hWrap : ∀ (sEnd : S), (∀ (fsB : FsApiM (StateM S)) (cb : Nat → StateM S (Except SlotPoolError Nat)), AllBusyFs fsB cfg.poolDir cb → (pollWaitUpToM fsB time cfg dl cb maxForeverPolls).run s₂ = (.ok .noSlot, sEnd)) →
      ∀ (fsB : FsApiM (StateM S)) (cb : Nat → StateM S (Except SlotPoolError Nat)), AllBusyFs fsB cfg.poolDir cb → (fsB.mkdir cfg.poolDir true true).run s₀ = (.ok (), s₁) →
      ((mkApiM fsB time).withSlot cfg (.waitUpTo timeoutMs) cb).run s₀ = (.ok .noSlot, sEnd) := fun _ hP fsB cb hL hM => by rw [withSlot_after_mkdir fsB time cfg (.waitUpTo timeoutMs) cb hVal hM, hStart]; exact hP fsB cb hL
  dsimp only; cases hNow1 : time.monoNanosNow.run s₂ with
  | mk nowNs₁ s₃ =>
    dsimp only; by_cases hExp1 : nowNs₁ ≥ dl
    · simp only [dl, hExp1, ↓reduceIte, allPass_assert_end]; rw [hWrap s₃ (fun fsB cb hL => by rw [hF, pollWaitUpToM_busy_step fsB time cfg dl cb hL, hNow1]; simp [hExp1])]; exact ⟨⟨rfl, rfl⟩, trivial⟩; exact fun _ _ => rfl; exact hMk
    · simp only [dl, hExp1, ↓reduceIte]; have hB1 := nextSleepMs_bounds hPoll hExp1; cases hSleep1 : (runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs nowNs₁ dl))).run s₃ with
      | mk _ s₄ =>
        dsimp only; cases hNow2 : time.monoNanosNow.run s₄ with
        | mk nowNs₂ s₅ =>
          dsimp only; by_cases hExp2 : nowNs₂ ≥ dl
          · simp only [dl, hExp2, ↓reduceIte, allPass_assert_end]; rw [hWrap s₅ (fun fsB cb hL => by rw [hF, pollWaitUpToM_busy_step fsB time cfg dl cb hL, hNow1]; simp only [hExp1, ↓reduceIte]; rw [hSleep1]; dsimp only; rw [pollWaitUpToM_busy_step fsB time cfg dl cb hL, hNow2]; simp [hExp2])]; exact ⟨⟨hB1.1, hB1.2, rfl, rfl⟩, trivial⟩; exact fun _ _ => rfl; exact hMk
          · simp only [dl, hExp2, ↓reduceIte]; dsimp only [Bind.bind, NondetTest.assume]; have hB2 := nextSleepMs_bounds hPoll hExp2; cases hSleep2 : (runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs nowNs₂ dl))).run s₅ with
            | mk _ s₆ =>
              dsimp only; cases hNow3 : time.monoNanosNow.run s₆ with
              | mk nowNs₃ s₇ =>
                dsimp only; intro hExp3; rw [allPass_assert_end]; have hExp3' : nowNs₃ ≥ dl := hExp3; rw [hWrap s₇ (fun fsB cb hL => by rw [hF, pollWaitUpToM_busy_step fsB time cfg dl cb hL, hNow1]; simp only [hExp1, ↓reduceIte]; rw [hSleep1]; dsimp only; rw [pollWaitUpToM_busy_step fsB time cfg dl cb hL, hNow2]; simp only [hExp2, ↓reduceIte]; rw [hSleep2]; dsimp only; rw [pollWaitUpToM_busy_step fsB time cfg dl cb hL, hNow3]; simp [hExp3'])]; exact ⟨⟨hB1.1, hB1.2, hB2.1, hB2.2, rfl, rfl⟩, trivial⟩; exact fun _ _ => rfl; exact hMk
end
private abbrev pc (d : String) (s m : Nat) : PoolConfig := { poolDir := d, totalSlots := s, pollIntervalMs := m }
/-- Witness 1 (`CanReach`): `test_slotpool_model_timingAndSleepChunks_exactAndChunked` is reachable for `defaultTimingModelOps`. -/
theorem reach_model_timingAndSleepChunks : CanReach (test_slotpool_model_timingAndSleepChunks_exactAndChunked defaultTimingModelOps) := ⟨0, 20, 500000, 50, 1, by decide, proof_model_timingAndSleepChunks 0 20 500000 50 1 (by decide)⟩
/-- Witness 2 (`CanReach`): `test_slotpool_validation_invalidConfig_rejectedBeforeEffects` is reachable for `mkApiM`. -/
theorem reach_validation_invalidConfig_rejectedBeforeEffects : CanReach (test_slotpool_validation_invalidConfig_rejectedBeforeEffects mkApiM simFs simTime) := ⟨{}, pc "" 0 50, .noWait, "marker.txt", by decide, proof_validation_invalidConfig_rejectedBeforeEffects simFs simTime {} (pc "" 0 50) .noWait "marker.txt" (by decide)⟩
/-- Witness 3 (`CanReach`): `test_slotpool_mkdir_fsError_propagatedBeforePolling` is reachable for `mkApiM`. -/
theorem reach_mkdir_fsError_propagatedBeforePolling : CanReach (test_slotpool_mkdir_fsError_propagatedBeforePolling mkApiM simFs simTime) := ⟨{ files := [("pool", "blocking")] }, pc "pool" 1 50, .noWait, "marker.txt", by decide, proof_mkdir_fsError_propagatedBeforePolling simFs simTime { files := [("pool", "blocking")] } (pc "pool" 1 50) .noWait "marker.txt" (by decide)⟩
/-- Witness 4 (`CanReach`): `test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction` is reachable for `mkApiM`. -/
theorem reach_noWait_allBusy_returnsNoSlotWithoutSleepOrAction : CanReach (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction mkApiM simFs simTime) := ⟨{}, pc "pool" 2 50, "marker.txt", by decide, rfl, rfl, proof_noWait_allBusy_returnsNoSlotWithoutSleepOrAction simFs simTime {} (pc "pool" 2 50) "marker.txt" (by decide) rfl rfl⟩
/-- Witness 5 (`CanReach`): `test_slotpool_tryLock_fsError_propagatedWithoutRunningAction` is reachable for `mkApiM`. -/
theorem reach_tryLock_fsError_propagatedWithoutRunningAction : CanReach (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction mkApiM simFs simTime) :=
  ⟨{}, pc "pool" 2 50, 1, true, .waitForever, { kind := .permissionDenied, path := some "pool/slot-1.lock", message := "denied" }, "marker.txt", by decide, rfl, rfl, rfl, ⟨rfl, proof_tryLock_fsError_propagatedWithoutRunningAction simFs simTime {} (pc "pool" 2 50) 1 true .waitForever { kind := .permissionDenied, path := some "pool/slot-1.lock", message := "denied" } "marker.txt" (by decide) rfl rfl rfl rfl⟩⟩
/-- Witness 6 (`CanReach`): `test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep` is reachable along the 2-sleep path for `mkApiM`. -/
theorem reach_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep : CanReach (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep mkApiM simFs simTime) := by
  have hMk0 : (simFs.mkdir "pool" true true).run {} = (.ok (), { dirs := ["pool"] }) := rfl
  refine ⟨{}, pc "pool" 1 10, 20, by decide, by decide, rfl, by rw [hMk0]; decide, ?_⟩; have hp := proof_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep simFs simTime {} (pc "pool" 1 10) 20 (by decide) (by decide) rfl (by rw [hMk0]; decide)
  dsimp only [test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep, AllPass, CanReach, Bind.bind, NondetTest.assume, NondetTest.assert] at hp ⊢; rw [hMk0] at hp ⊢; dsimp only at hp ⊢
  let sP : PoolSimState := { dirs := ["pool"] }; let sA := (simTime.monoNanosNow.run sP).2; let dl := deadlineNanos (simTime.monoNanosNow.run sP).1 20
  have h1 : ¬ ((simTime.monoNanosNow.run sA).1 ≥ dl) := (by decide); have h2 : ¬ ((simTime.monoNanosNow.run ((runSleepChunks simTime (sleepChunks (nextSleepMs 10 (simTime.monoNanosNow.run sA).1 dl))).run (simTime.monoNanosNow.run sA).2).2).1 ≥ dl) := (by decide)
  dsimp only [sP, sA, dl] at h1 h2; simp only [h1, h2, ↓reduceIte] at hp ⊢; exact ⟨by decide, hp (by decide)⟩
end LeanSwe.SlotPool.Proofs
