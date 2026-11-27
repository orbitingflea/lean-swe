import LeanSwe.SlotPool.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Impl
import LeanSwe.SlotPool.Interface
import LeanSwe.SlotPool.SpecTests
import LeanSwe.SlotPool.Proofs.SimLemmas

namespace LeanSwe.SlotPool.Proofs

open Core Core.NondetTest LeanSwe.SlotPool.Model
open LeanSwe.Fs (FsApiM LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Internal (ScanOutcome scanSlotsM pollWaitUpToM pollForeverM withSlotM)
open LeanSwe.SlotPool (mkApiM)

local notation "lpJoin" => slotLockPath simFs.join
local notation "busyEx" s:arg p:arg k:arg => hasSimLockConflict s (slotLockPath simFs.join p k) LockMode.exclusive
private abbrev withF (s : PoolSimState) (lp : String) : PoolSimState := { s with files := (lp, "") :: s.files }
private abbrev withL (s : PoolSimState) (lp : String) : PoolSimState := { s with files := (lp, "") :: s.files, heldLocks := (lp, .exclusive) :: s.heldLocks }
private abbrev CleanSim (p : String) (s : PoolSimState) : Prop := validPoolDir p = true ∧ s.files = [] ∧ s.symlinks = [] ∧ s.heldLocks = [] ∧ normSimPath p ∈ s.dirs ∧ ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath p).toList.length
private abbrev pc (d : String) (s m : Nat) : PoolConfig := { poolDir := d, totalSlots := s, pollIntervalMs := m }
private def outScan {α : Type} (i : Nat) : Except SlotPoolError α → ScanOutcome α | .error e => .err e | .ok v => .leased i v
private def outLease {α : Type} (i : Nat) : Except SlotPoolError α → Except SlotPoolError (LeaseOutcome α) | .error e => .error e | .ok v => .ok (.leased i v)
private theorem maxForeverPolls_succ : maxForeverPolls = (2 ^ 64 - 1) + 1 := by decide
private theorem log_append_eq (a : Array UInt32) (b c : List UInt32) : a ++ b.toArray ++ c.toArray = a ++ (b ++ c).toArray := Array.ext' (by simp)
private theorem simMkdir_clean_eq (s : PoolSimState) (p : String) (hFail : s.failMkdirWith = none) (hF : s.files = []) (hSy : s.symlinks = []) (hH : s.heldLocks = []) (hV : validPoolDir p = true) (hD : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath p).toList.length) :
    ∃ ds, (simFs.mkdir p true true).run s = (.ok (), { s with dirs := ds }) ∧ CleanSim p { s with dirs := ds } := by
  obtain ⟨s', hMk, _, _, _, _, _, _, _, hPar, hD'⟩ := simMkdir_clean s p hFail hF hSy hV hD; have : s' = { s with dirs := s'.dirs } := (by cases s; cases s'; simp_all); exact ⟨s'.dirs, this ▸ hMk, hV, hF, hSy, hH, hPar, hD'⟩
private theorem simMkdir_empty (p : String) (hV : validPoolDir p = true) (ext : List (String × Nat)) (mono : Nat := 0) :
    let s : PoolSimState := { externalLeases := ext, monoNanos := mono }; ∃ ds, (simFs.mkdir p true true).run s = (.ok (), { s with dirs := ds }) ∧ CleanSim p { s with dirs := ds } := simMkdir_clean_eq { externalLeases := ext, monoNanos := mono } p rfl rfl rfl rfl hV (fun _ h => nomatch h)
section
variable {p : String} {s : PoolSimState}
private theorem scan_allBusy {α : Type} (hc : CleanSim p s) (act : Nat → StateM PoolSimState (Except SlotPoolError α)) : ∀ n r, (∀ k, n ≤ k → k < n + r → busyEx s p k = true) → (scanSlotsM simFs p n r act).run s = (.allBusy, s)
  | _, 0, _ => rfl
  | n, r + 1, hB => by unfold scanSlotsM; rw [stateM_bind_run, internal_slotLockPath_eq, simFs_tryWithFileLock_run, simTryAcquire_busy s p hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.2.2 n hc.2.2.2.2.1 (hB n (Nat.le_refl _) (by omega))]; exact scan_allBusy hc act (n + 1) r (fun k _ _ => hB k (by omega) (by omega))
private theorem scan_acq {α : Type} (hc : CleanSim p s) (act : Nat → StateM PoolSimState (Except SlotPoolError α)) (i : Nat) (res : Except SlotPoolError α) (hFree : busyEx s p i = false) (hAct : (act i).run (withL s (lpJoin p i)) = (res, withL s (lpJoin p i))) :
    ∀ n r, n ≤ i → i < n + r → (∀ k, n ≤ k → k < i → busyEx s p k = true) → (scanSlotsM simFs p n r act).run s = (outScan i res, withF s (lpJoin p i))
  | _, 0, _, _, _ => by omega
  | n, r + 1, _, _, hB => by
    unfold scanSlotsM; rw [stateM_bind_run, internal_slotLockPath_eq, simFs_tryWithFileLock_run]; by_cases hlt : n < i
    · rw [simTryAcquire_busy s p hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.2.2 n hc.2.2.2.2.1 (hB n (Nat.le_refl _) hlt)]; exact scan_acq hc act i res hFree hAct (n + 1) r (by omega) (by omega) (fun k _ h2 => hB k (by omega) h2)
    · obtain rfl : n = i := (by omega); rw [simTryAcquire_free s p hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.2.2 n hc.2.2.2.2.1 hFree]; dsimp only; rw [stateM_bind_run, hAct]; dsimp only [StateT.run, Pure.pure, StateT.pure]; rw [(slotLockPath_props hc.1 n).1, removeFirstSimLock_cons_self]; cases res <;> rfl
private theorem scan_ex_throw (hc : CleanSim p s) (act : Nat → ExceptT String (StateM PoolSimState) (Except SlotPoolError Unit)) (i : Nat) (hFree : busyEx s p i = false) (hAct : (ExceptT.run (act i)).run (withL s (lpJoin p i)) = (.error "boom", withL s (lpJoin p i))) :
    ∀ n r, n ≤ i → i < n + r → (∀ k, n ≤ k → k < i → busyEx s p k = true) → (ExceptT.run (scanSlotsM simFsEx p n r act)).run s = (.error "boom", withF s (lpJoin p i))
  | _, 0, _, _, _ => by omega
  | n, r + 1, _, _, hB => by
    unfold scanSlotsM; rw [exceptT_bind_run, internal_slotLockPath_eq, show simFsEx.join = simFs.join from rfl, simFsEx_tryWithFileLock_run]; by_cases hlt : n < i
    · rw [simTryAcquire_busy s p hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.2.2 n hc.2.2.2.2.1 (hB n (Nat.le_refl _) hlt)]; exact scan_ex_throw hc act i hFree hAct (n + 1) r (by omega) (by omega) (fun k _ h2 => hB k (by omega) h2)
    · obtain rfl : n = i := (by omega); rw [simTryAcquire_free s p hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.2.2 n hc.2.2.2.2.1 hFree]; dsimp only; rw [exceptT_bind_run, hAct]; dsimp only [ExceptT.run, ExceptT.mk, StateT.run, Pure.pure, StateT.pure]; rw [(slotLockPath_props hc.1 n).1, removeFirstSimLock_cons_self]
private theorem shared_acq_pure (hc : CleanSim p s) (i : Nat) : simTryAcquirePure (withL s (lpJoin p i)) (lpJoin p i) .shared false = .ok none := by
  obtain ⟨hNorm, hV, _, hLen, _, _⟩ := slotLockPath_props hc.1 i; have hEx : (LockMode.exclusive == LockMode.exclusive) = true := rfl
  have hC : hasSimLockConflict (withL s (lpJoin p i)) (lpJoin p i) .shared = true := by unfold hasSimLockConflict; exact Bool.or_eq_true_iff.mpr (Or.inl (List.any_eq_true.mpr ⟨(_, .exclusive), List.mem_cons_self, by simp [hEx]⟩))
  have hND : ¬ (lpJoin p i ∈ s.dirs) := fun h => by have := hc.2.2.2.2.2 _ h; omega
  unfold simTryAcquirePure; rw [hNorm]; simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hND, hc.2.2.1, List.not_mem_nil, hasSimFile, List.any_cons, beq_self_eq_true, Bool.true_or, hC]
private theorem shared_acq (hc : CleanSim p s) (i : Nat) : (simFs.tryWithFileLock (lpJoin p i) .shared false (pure (.ok ()))).run (withL s (lpJoin p i)) = (.ok none, withL s (lpJoin p i)) := by rw [simFs_tryWithFileLock_run, shared_acq_pure hc i]
private theorem post_ok (hc : CleanSim p s) (i : Nat) (hFree : busyEx (withF s (lpJoin p i)) p i = false) : (simFs.tryWithFileLock (lpJoin p i) .exclusive false (pure (.ok ()))).run (withF s (lpJoin p i)) = (.ok (some ()), withF s (lpJoin p i)) := by
  obtain ⟨hNorm, hV, _, _, _, _⟩ := slotLockPath_props hc.1 i; rw [simFs_postProbe_ok hV hNorm (fun h => by have := hc.2.2.2.2.2 _ h; omega) (by simp [hc.2.2.1]) (by simp [hasSimFile]) hFree, removeFirstSimLock_cons_self]
private theorem next_absent (hc : CleanSim p s) (i : Nat) : hasSimFile (withF s (lpJoin p i)) (normSimPath (lpJoin p (i + 1))) = false := by
  rw [(slotLockPath_props hc.1 (i + 1)).1]; simp only [hasSimFile, hc.2.1, List.any_cons, List.any_nil, Bool.or_false]; exact beq_false_of_ne fun e => by have := slotLockPath_inj hc.1 e; omega
end
private theorem allBusy_until {p : String} {s : PoolSimState} (hV : validPoolDir p = true) {i tr lu n : Nat} (hExt : s.externalLeases = leasesBeforeSlotUntil simFs.join p i tr lu n) (hLtT : s.monoNanos < tr) (hLtL : tr ≤ lu) : ∀ k, 0 ≤ k → k < 0 + n → busyEx s p k = true := by
  obtain ⟨hLt, hGe, _⟩ := leasesBeforeSlotUntil_conflict hV hExt; intro k _ hk; by_cases h : k < i; exact hLt k (by omega) h (Nat.lt_of_lt_of_le hLtT hLtL); exact hGe k (by omega) (Nat.not_lt.mp h) hLtT
private theorem poll_step_w {α : Type} (cfg : PoolConfig) (dl : Nat) (act : Nat → StateM PoolSimState (Except SlotPoolError α)) (f : Nat) {s : PoolSimState} (hSc : (scanSlotsM simFs cfg.poolDir 0 cfg.totalSlots act).run s = (.allBusy, s)) (hNotGe : ¬ s.monoNanos ≥ dl) :
    (pollWaitUpToM simFs simTime cfg dl act (f + 1)).run s = let d := nextSleepMs cfg.pollIntervalMs s.monoNanos dl; (pollWaitUpToM simFs simTime cfg dl act f).run { s with monoNanos := s.monoNanos + d * nanosecondsPerMs, sleepLog := s.sleepLog ++ (sleepChunks d).toArray } := by
  conv => lhs; unfold pollWaitUpToM; rw [stateM_bind_run, hSc]; dsimp only; rw [stateM_bind_run, show simTime.monoNanosNow.run s = (s.monoNanos, s) from rfl]; dsimp only; simp only [hNotGe, ↓reduceIte]; rw [stateM_bind_run, internal_runSleepChunks_eq, internal_sleepChunks_eq, internal_nextSleepMs_eq, runSleepChunks_simTime_sleepChunks]
private theorem withSlot_sim_firstScan {α : Type} {cfg : PoolConfig} (pol : WaitPolicy) {s₀ : PoolSimState} {ds : List String} (hV : validPoolConfig cfg = true) (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), { s₀ with dirs := ds })) (hc : CleanSim cfg.poolDir { s₀ with dirs := ds })
    (i : Nat) (hLt : i < cfg.totalSlots) (hB : ∀ k, 0 ≤ k → k < i → busyEx { s₀ with dirs := ds } cfg.poolDir k = true) (hF : busyEx { s₀ with dirs := ds } cfg.poolDir i = false) (res : Except SlotPoolError α) (act : Nat → StateM PoolSimState (Except SlotPoolError α))
    (hAct : (act i).run (withL { s₀ with dirs := ds } (lpJoin cfg.poolDir i)) = (res, withL { s₀ with dirs := ds } (lpJoin cfg.poolDir i))) :
    ((mkApiM simFs simTime).withSlot cfg pol act).run s₀ = (outLease i res, withF { s₀ with dirs := ds } (lpJoin cfg.poolDir i)) := by
  have hSc := scan_acq hc act i res hF hAct 0 cfg.totalSlots (Nat.zero_le _) (by omega) hB; dsimp only [mkApiM, Internal.mkApiM, withSlotM]; rw [internal_validatePoolConfig_eq, (validatePoolConfig_of_true cfg hV).1]; dsimp only; rw [stateM_bind_run, hMk]; dsimp only
  cases pol with
  | noWait => rw [stateM_bind_run, hSc]; cases res <;> rfl
  | waitUpTo _ => rw [stateM_bind_run, show simTime.monoNanosNow.run { s₀ with dirs := ds } = (s₀.monoNanos, { s₀ with dirs := ds }) from rfl]; dsimp only; rw [internal_maxForeverPolls_eq, maxForeverPolls_succ]; unfold pollWaitUpToM; rw [stateM_bind_run, hSc]; cases res <;> rfl
  | waitForever => rw [internal_maxForeverPolls_eq, maxForeverPolls_succ]; unfold pollForeverM; rw [stateM_bind_run, hSc]; cases res <;> rfl
private theorem poll_advance_rounds {α : Type} (isF : Bool) (cfg : PoolConfig) (hV : validPoolConfig cfg = true) (i tr lu dl : Nat) (hLeDl : isF = false → tr ≤ dl) (hLtL : tr ≤ lu) (act : Nat → StateM PoolSimState (Except SlotPoolError α)) :
    ∀ k fuel (s : PoolSimState), k < fuel → CleanSim cfg.poolDir s → s.externalLeases = leasesBeforeSlotUntil simFs.join cfg.poolDir i tr lu cfg.totalSlots → s.monoNanos + k * cfg.pollIntervalMs * nanosecondsPerMs = tr →
      ∃ rf, rf ≥ 1 ∧ (if isF then pollForeverM simFs simTime cfg act fuel else pollWaitUpToM simFs simTime cfg dl act fuel).run s = (if isF then pollForeverM simFs simTime cfg act rf else pollWaitUpToM simFs simTime cfg dl act rf).run { s with monoNanos := tr, sleepLog := s.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray }
  | 0, fuel, s, hLt, _, _, hM => by rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero] at hM; subst hM; exact ⟨fuel, hLt, by simp [repeatSleepChunks]⟩
  | _ + 1, 0, _, _, _, _, _ => by omega
  | k + 1, f + 1, s, hLt, hc, hExt, hM => by
    have hPos : 0 < cfg.pollIntervalMs * nanosecondsPerMs := Nat.mul_pos (validatePoolConfig_of_true cfg hV).2.2.2 (by decide); have hDist : (k + 1) * cfg.pollIntervalMs * nanosecondsPerMs = cfg.pollIntervalMs * nanosecondsPerMs + k * cfg.pollIntervalMs * nanosecondsPerMs := by rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hSc := scan_allBusy hc act 0 cfg.totalSlots (allBusy_until hc.1 hExt (by omega) hLtL); let s1 : PoolSimState := { s with monoNanos := s.monoNanos + cfg.pollIntervalMs * nanosecondsPerMs, sleepLog := s.sleepLog ++ (sleepChunks cfg.pollIntervalMs).toArray }
    have hStep : (if isF then pollForeverM simFs simTime cfg act (f + 1) else pollWaitUpToM simFs simTime cfg dl act (f + 1)).run s = (if isF then pollForeverM simFs simTime cfg act f else pollWaitUpToM simFs simTime cfg dl act f).run s1 := by
      cases isF with
      | true => simp only [↓reduceIte]; conv => lhs; unfold pollForeverM; rw [stateM_bind_run, hSc]; dsimp only; rw [stateM_bind_run, internal_runSleepChunks_eq, internal_sleepChunks_eq, runSleepChunks_simTime_sleepChunks]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]; have hDl := hLeDl rfl; have hNotGe : ¬ s.monoNanos ≥ dl := (by omega)
        have hNext : nextSleepMs cfg.pollIntervalMs s.monoNanos dl = cfg.pollIntervalMs := (by dsimp [nextSleepMs, remainingWaitMs]; simp only [hNotGe, ↓reduceIte]; apply Nat.min_eq_left; dsimp [nanosecondsPerMs] at hDist hM ⊢; omega); rw [poll_step_w cfg dl act f hSc hNotGe]; dsimp only; rw [hNext]
    obtain ⟨rf, hrf, hRec⟩ := poll_advance_rounds isF cfg hV i tr lu dl hLeDl hLtL act k f s1 (by omega) hc hExt (by dsimp [s1]; omega); exact ⟨rf, hrf, by rw [hStep, hRec, log_append_eq]; rfl⟩
private theorem pollWaitUpToM_advance_dl {α : Type} (cfg : PoolConfig) (hV : validPoolConfig cfg = true) (dl : Nat) (act : Nat → StateM PoolSimState (Except SlotPoolError α)) :
    ∀ remMs fuel cf (s : PoolSimState), remMs < fuel → remMs < cf → CleanSim cfg.poolDir s → (∀ t < dl, ∀ k < cfg.totalSlots, busyEx { s with monoNanos := t } cfg.poolDir k = true) → s.monoNanos + remMs * nanosecondsPerMs = dl →
      ∃ rf, rf ≥ 1 ∧ (pollWaitUpToM simFs simTime cfg dl act fuel).run s = (pollWaitUpToM simFs simTime cfg dl act rf).run { s with monoNanos := dl, sleepLog := s.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs cf remMs).toArray } := by
  intro remMs; induction remMs using Nat.strongRecOn with | ind remMs ih =>
  intro fuel cf s hF hCF hc hAll hM; cases cf with | zero => omega | succ cf => cases remMs with
  | zero => rw [Nat.zero_mul, Nat.add_zero] at hM; subst hM; exact ⟨fuel, hF, by simp [expectedWaitUpToChunks]⟩
  | succ r =>
    cases fuel with | zero => omega | succ f =>
    have hPos : 0 < (r + 1) * nanosecondsPerMs := Nat.mul_pos (Nat.succ_pos r) (by decide); have hNotGe : ¬ s.monoNanos ≥ dl := (by omega)
    have hSc := scan_allBusy hc act 0 cfg.totalSlots (fun k _ hk => by simpa using hAll s.monoNanos (by omega) k (by omega)); let d := Nat.min cfg.pollIntervalMs (r + 1)
    have hNext : nextSleepMs cfg.pollIntervalMs s.monoNanos dl = d := by dsimp [nextSleepMs, remainingWaitMs, nanosecondsPerMs] at hM ⊢; simp only [hNotGe, ↓reduceIte]; congr 1; omega
    let s1 : PoolSimState := { s with monoNanos := s.monoNanos + d * nanosecondsPerMs, sleepLog := s.sleepLog ++ (sleepChunks d).toArray }; have hDurPos : 1 ≤ d := Nat.le_min.mpr ⟨(validatePoolConfig_of_true cfg hV).2.2.2, Nat.succ_pos r⟩; have hDurLe : d ≤ r + 1 := Nat.min_le_right _ _
    have hM1 : s1.monoNanos + (r + 1 - d) * nanosecondsPerMs = dl := by dsimp [s1]; have : d * nanosecondsPerMs + (r + 1 - d) * nanosecondsPerMs = (r + 1) * nanosecondsPerMs := (by rw [← Nat.add_mul, Nat.add_sub_cancel' hDurLe]); omega
    obtain ⟨rf, hrf, hRec⟩ := ih (r + 1 - d) (by omega) f cf s1 (by omega) (by omega) hc (fun t ht k hk => hAll t ht k hk) hM1; exact ⟨rf, hrf, by rw [poll_step_w cfg dl act f hSc hNotGe]; dsimp only; rw [hNext, hRec, log_append_eq]; rfl⟩
private theorem withSlot_sim_waitRounds {α : Type} {cfg : PoolConfig} {i k : Nat} {s₀ : PoolSimState} {ds : List String} (isF : Bool) (tMs tr lu : Nat) {pol : WaitPolicy} (hPol : pol = if isF then .waitForever else .waitUpTo tMs)
    (hV : validPoolConfig cfg = true) (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), { s₀ with dirs := ds })) (hc : CleanSim cfg.poolDir { s₀ with dirs := ds })
    (hExt : s₀.externalLeases = leasesBeforeSlotUntil simFs.join cfg.poolDir i tr lu cfg.totalSlots) (hLeDl : isF = false → tr ≤ deadlineNanos s₀.monoNanos tMs) (hLocked : tr < lu) (hR : k < maxForeverPolls) (hMono : s₀.monoNanos + k * cfg.pollIntervalMs * nanosecondsPerMs = tr) (hLt : i < cfg.totalSlots) (res : Except SlotPoolError α) (act : Nat → StateM PoolSimState (Except SlotPoolError α))
    (hAct : (act i).run (withL { s₀ with dirs := ds, monoNanos := tr, sleepLog := s₀.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } (lpJoin cfg.poolDir i)) = (res, withL { s₀ with dirs := ds, monoNanos := tr, sleepLog := s₀.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } (lpJoin cfg.poolDir i))) :
    ((mkApiM simFs simTime).withSlot cfg pol act).run s₀ = (outLease i res, withF { s₀ with dirs := ds, monoNanos := tr, sleepLog := s₀.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } (lpJoin cfg.poolDir i)) := by
  subst hPol; let sT : PoolSimState := { s₀ with dirs := ds, monoNanos := tr, sleepLog := s₀.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray }; obtain ⟨hBLt, _, hFreeAt⟩ := leasesBeforeSlotUntil_conflict (s := sT) hc.1 hExt
  have hSc := scan_acq (s := sT) hc act i res (hFreeAt hc.2.2.2.1 hLt (Nat.le_refl _)) hAct 0 cfg.totalSlots (Nat.zero_le _) (by omega) (fun j _ hlt => hBLt j (by omega) hlt hLocked)
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]; rw [internal_validatePoolConfig_eq, (validatePoolConfig_of_true cfg hV).1]; dsimp only; rw [stateM_bind_run, hMk]; dsimp only
  obtain ⟨rf, hrf, hReach⟩ := poll_advance_rounds isF cfg hV i tr lu (deadlineNanos s₀.monoNanos tMs) hLeDl (Nat.le_of_lt hLocked) act k maxForeverPolls { s₀ with dirs := ds } hR hc hExt hMono; obtain ⟨f', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrf)
  cases isF with
  | true =>
    simp only [↓reduceIte] at hReach ⊢; rw [internal_maxForeverPolls_eq, hReach]; conv => lhs; unfold pollForeverM
    rw [stateM_bind_run, hSc]; cases res <;> rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hReach ⊢; rw [stateM_bind_run, show simTime.monoNanosNow.run { s₀ with dirs := ds } = (s₀.monoNanos, { s₀ with dirs := ds }) from rfl]; dsimp only; rw [internal_deadlineNanos_eq, internal_maxForeverPolls_eq, hReach]; conv => lhs; unfold pollWaitUpToM
    rw [stateM_bind_run, hSc]; cases res <;> rfl
private theorem withSlot_sim_waitUpTo_at_dl {α : Type} {cfg : PoolConfig} {tMs : Nat} {s₀ : PoolSimState} {ds : List String} (hV : validPoolConfig cfg = true) (hTM : tMs < maxForeverPolls)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), { s₀ with dirs := ds })) (hc : CleanSim cfg.poolDir { s₀ with dirs := ds })
    (hAll : ∀ t < deadlineNanos s₀.monoNanos tMs, ∀ k < cfg.totalSlots, busyEx { s₀ with dirs := ds, monoNanos := t } cfg.poolDir k = true) (act : Nat → StateM PoolSimState (Except SlotPoolError α)) {out : ScanOutcome α} {s' : PoolSimState}
    (hMono' : s'.monoNanos ≥ deadlineNanos s₀.monoNanos tMs)
    (hSc : (scanSlotsM simFs cfg.poolDir 0 cfg.totalSlots act).run { s₀ with dirs := ds, monoNanos := deadlineNanos s₀.monoNanos tMs, sleepLog := s₀.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (tMs + 1) tMs).toArray } = (out, s')) :
    ((mkApiM simFs simTime).withSlot cfg (.waitUpTo tMs) act).run s₀ = match out with | .leased i v => (.ok (.leased i v), s') | .err e => (.error e, s') | .allBusy => (.ok .noSlot, s') := by
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]; rw [internal_validatePoolConfig_eq, (validatePoolConfig_of_true cfg hV).1]; dsimp only; rw [stateM_bind_run, hMk]; dsimp only; rw [stateM_bind_run, show simTime.monoNanosNow.run { s₀ with dirs := ds } = (s₀.monoNanos, { s₀ with dirs := ds }) from rfl]; dsimp only
  obtain ⟨rf, hrf, hReach⟩ := pollWaitUpToM_advance_dl cfg hV (deadlineNanos s₀.monoNanos tMs) act tMs maxForeverPolls (tMs + 1) { s₀ with dirs := ds } hTM (Nat.lt_succ_self _) hc hAll rfl
  obtain ⟨f', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrf); rw [internal_deadlineNanos_eq, internal_maxForeverPolls_eq, hReach]; conv => lhs; unfold pollWaitUpToM; rw [stateM_bind_run, hSc]; dsimp only
  cases out with | leased _ _ => rfl | err _ => rfl | allBusy => rw [stateM_bind_run, show simTime.monoNanosNow.run s' = (s'.monoNanos, s') from rfl]; dsimp only; simp only [hMono', ↓reduceIte]; rfl
private theorem allPass_ite_assert (c : Prop) [Decidable c] (p : Prop) (rest : AllPassRun Unit) : ((if c then (NondetTest.assert p >>= fun _ => rest) else (NondetTest.assert True >>= fun _ => rest)) (fun _ => True)) = ((c → p) ∧ (rest fun _ => True)) := by by_cases hc : c <;> simp [hc, allPass_assert]
/-- Specification 7 (`AllPass`): `withSlot` creates `cfg.poolDir`, scans ascending from slot `0`, acquires the lowest free slot `.exclusive` with `createIfMissing = true`, and releases it on `.ok` while keeping the lock file on disk. -/
theorem proof_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock : AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock mkApiM) := by
  intro cfg freeIdx val policy dirPreExists startMono ⟨hV, hLt⟩; have hDV := (validatePoolConfig_of_true cfg hV).2.1; dsimp only [test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock, AllPass]; rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  let s₀ : PoolSimState := { dirs := if dirPreExists then [normSimPath cfg.poolDir] else [], externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (startMono + 1000000000) freeIdx, monoNanos := startMono }
  obtain ⟨ds, hMk, hc⟩ := simMkdir_clean_eq s₀ cfg.poolDir rfl rfl rfl rfl hDV (fun d hd => by cases dirPreExists <;> simp_all [s₀]); obtain ⟨hB, hF⟩ := leasesBeforeSlot_conflict (s := { s₀ with dirs := ds }) hDV rfl
  rw [withSlot_sim_firstScan policy hV hMk hc freeIdx hLt (fun k _ hlt => hB k hlt (by dsimp [s₀]; omega)) (hF rfl) (.ok val) _ (by rw [stateM_bind_run, shared_acq hc freeIdx]; dsimp only; simp [hLt]; rfl), post_ok hc freeIdx ((leasesBeforeSlot_conflict (s := withF { s₀ with dirs := ds } _) hDV rfl).2 rfl)]
  exact ⟨⟨rfl, hLt⟩, ⟨rfl, rfl⟩, Or.inr (next_absent hc freeIdx), ⟨rfl, rfl⟩, trivial⟩
/-- Specification 8 (`AllPass`): callback `.error` on an acquired slot releases the lock, preserves the file on disk, stops scanning higher slots, and returns the error verbatim on both initial and retry scans. -/
theorem proof_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan : AllPass (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan mkApiM) := by
  intro cfg freeIdx retryRounds callbackErr policy ⟨hV, hLt, _, hRMax⟩; obtain ⟨_, hDV, _, hPoll⟩ := validatePoolConfig_of_true cfg hV; dsimp only [test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan, AllPass]; rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  let freePath := lpJoin cfg.poolDir freeIdx; let s₀ : PoolSimState := { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx }; obtain ⟨d0, hMk0, hc0⟩ := simMkdir_empty cfg.poolDir hDV (leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx)
  obtain ⟨hB0, hF0⟩ := leasesBeforeSlot_conflict (s := { s₀ with dirs := d0 }) hDV rfl; let tr := retryRounds * cfg.pollIntervalMs * nanosecondsPerMs; let lu := tr + cfg.pollIntervalMs * nanosecondsPerMs
  have hLocked : tr < lu := (by have : 0 < cfg.pollIntervalMs * nanosecondsPerMs := Nat.mul_pos hPoll (by decide); omega); let sR : PoolSimState := { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx tr lu cfg.totalSlots }
  obtain ⟨dR, hMkR, hcR⟩ := simMkdir_empty cfg.poolDir hDV (leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx tr lu cfg.totalSlots); let sT : PoolSimState := { sR with dirs := dR, monoNanos := tr, sleepLog := sR.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs retryRounds).toArray }
  rw [withSlot_sim_firstScan policy hV hMk0 hc0 freeIdx hLt (fun k _ hlt => hB0 k hlt (by dsimp [s₀]; omega)) (hF0 rfl) (.error callbackErr)]
  · rw [withSlot_sim_waitRounds (s₀ := sR) (ds := dR) (policy == .noWait) (retryRounds * cfg.pollIntervalMs) tr lu rfl hV hMkR hcR rfl (fun _ => by dsimp [deadlineNanos, sR, tr]; omega) hLocked hRMax (by dsimp [sR, tr]; omega) hLt (.error callbackErr)]
    · rw [post_ok hc0 freeIdx ((leasesBeforeSlot_conflict (s := withF { s₀ with dirs := d0 } freePath) hDV rfl).2 rfl), post_ok (s := sT) hcR freeIdx ((leasesBeforeSlotUntil_conflict (s := withF sT freePath) hDV rfl).2.2 rfl hLt (Nat.le_refl _))]
      have hNo : ∀ s : PoolSimState, s.files = [] → hasSimFile (withF s freePath) "ran-other" = false := fun s hf => by simp only [hasSimFile, hf, List.any_cons, List.any_nil, Bool.or_false]; exact beq_false_of_ne (slotLockPath_props hDV freeIdx).2.2.2.2.1
      exact ⟨rfl, ⟨rfl, rfl⟩, ⟨hNo _ rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨hNo _ rfl, rfl⟩, trivial⟩
    · simp only [beq_self_eq_true, ↓reduceIte]; rw [stateM_bind_run, shared_acq (s := sT) hcR freeIdx]; rfl
  · simp only [beq_self_eq_true, ↓reduceIte]; rw [stateM_bind_run, shared_acq hc0 freeIdx]; rfl
/-- Specification 9 (`AllPass`): an uncaught monadic exception in `ExceptT String (StateM PoolSimState)` releases the held lock via `MonadFinally`, preserves the lock file on disk, and propagates the exception. -/
theorem proof_monadFinally_uncaughtException_releasesLockAndPropagates : AllPass (test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates mkApiM) := by
  intro cfg freeIdx policy ⟨hV, hLt⟩; obtain ⟨hVal, hDV, _, _⟩ := validatePoolConfig_of_true cfg hV; dsimp only [test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates, AllPass]; rw [allPass_assert_end]
  let s₀ : PoolSimState := { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx }; obtain ⟨ds, hMk, hc⟩ := simMkdir_empty cfg.poolDir hDV (leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx); obtain ⟨hB, hF⟩ := leasesBeforeSlot_conflict (s := { s₀ with dirs := ds }) hDV rfl
  have hRun : ∀ act : Nat → ExceptT String (StateM PoolSimState) (Except SlotPoolError Unit), (ExceptT.run (act freeIdx)).run (withL { s₀ with dirs := ds } (lpJoin cfg.poolDir freeIdx)) = (.error "boom", withL { s₀ with dirs := ds } (lpJoin cfg.poolDir freeIdx)) → (ExceptT.run ((mkApiM simFsEx simTimeEx).withSlot cfg policy act)).run s₀ = (.error "boom", withF { s₀ with dirs := ds } (lpJoin cfg.poolDir freeIdx)) := fun act hAct => by
    have hSc := scan_ex_throw hc act freeIdx (hF rfl) hAct 0 cfg.totalSlots (Nat.zero_le _) (by omega) (fun k _ hlt => hB k hlt (by dsimp [s₀]; omega))
    dsimp only [mkApiM, Internal.mkApiM, withSlotM]; rw [internal_validatePoolConfig_eq, hVal]; dsimp only; rw [exceptT_bind_run, simFsEx_mkdir_run, hMk]; dsimp only
    cases policy with
    | noWait => rw [exceptT_bind_run, hSc]
    | waitUpTo _ => rw [exceptT_bind_run, show (ExceptT.run simTimeEx.monoNanosNow).run { s₀ with dirs := ds } = (.ok 0, { s₀ with dirs := ds }) from rfl]; dsimp only; rw [internal_maxForeverPolls_eq, maxForeverPolls_succ]; unfold pollWaitUpToM; rw [exceptT_bind_run, hSc]
    | waitForever => rw [internal_maxForeverPolls_eq, maxForeverPolls_succ]; unfold pollForeverM; rw [exceptT_bind_run, hSc]
  rw [hRun]; · rw [post_ok hc freeIdx ((leasesBeforeSlot_conflict (s := withF { s₀ with dirs := ds } _) hDV rfl).2 rfl)]; exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩
  · rw [exceptT_bind_run, show simFsEx.join = simFs.join from rfl, simFsEx_tryWithFileLock_run, shared_acq_pure hc freeIdx]; dsimp only; simp only [beq_self_eq_true, ↓reduceIte]; rfl
/-- Specification 10 (`AllPass`): `WaitPolicy.waitUpTo` emits `expectedPollSleepLog`, expires cleanly at `deadlineNs`, and acquires the lowest freed slot on full-interval and clamped-remainder polls. -/
theorem proof_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline : AllPass (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline mkApiM) := by
  intro cfg freeIdx rounds timeoutMs val startMono ⟨hV, hLt, hTM⟩; obtain ⟨_, hDV, _, hPoll⟩ := validatePoolConfig_of_true cfg hV; dsimp only [test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline, AllPass]; rw [allPass_assert, allPass_assert]
  let dl := deadlineNanos startMono timeoutMs; let sE : PoolSimState := { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots, monoNanos := startMono }; obtain ⟨dE, hMkE, hcE⟩ := simMkdir_empty cfg.poolDir hDV (leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots) startMono
  let sDl : PoolSimState := { sE with dirs := dE, monoNanos := dl, sleepLog := sE.sleepLog ++ (expectedPollSleepLog cfg.pollIntervalMs timeoutMs).toArray }
  have hExpRun : ∀ act : Nat → StateM PoolSimState (Except SlotPoolError Nat), ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) act).run sE = (.ok .noSlot, sDl) := fun act =>
    withSlot_sim_waitUpTo_at_dl hV hTM hMkE hcE (fun t ht k hk => (leasesBeforeSlot_conflict (s := { sE with dirs := dE, monoNanos := t }) hDV rfl).1 k hk (Nat.lt_succ_of_lt ht)) act (Nat.le_refl dl) (scan_allBusy (s := sDl) hcE act 0 cfg.totalSlots (fun k _ hk => (leasesBeforeSlot_conflict (s := sDl) hDV rfl).1 k (by omega) (Nat.lt_succ_self dl)))
  refine ⟨by rw [hExpRun]; exact ⟨rfl, rfl, rfl⟩, by rw [hExpRun]; exact ⟨rfl, by simp [sDl, sE]⟩, ?_⟩
  rw [allPass_ite_assert]; refine ⟨fun ⟨_, hRB⟩ => ?_, ?_⟩
  · let tr := startMono + rounds * cfg.pollIntervalMs * nanosecondsPerMs; have hLeDl : tr ≤ dl := (by dsimp [tr, dl, deadlineNanos]; have := Nat.mul_le_mul_right nanosecondsPerMs hRB; omega)
    let sA : PoolSimState := { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx tr (dl + 1) cfg.totalSlots, monoNanos := startMono }; obtain ⟨dA, hMkA, hcA⟩ := simMkdir_empty cfg.poolDir hDV (leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx tr (dl + 1) cfg.totalSlots) startMono
    let sTA : PoolSimState := { sA with dirs := dA, monoNanos := tr, sleepLog := sA.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs rounds).toArray }; have hRLt : rounds < maxForeverPolls := (by have := Nat.le_mul_of_pos_right rounds hPoll; omega)
    rw [withSlot_sim_waitRounds (s₀ := sA) (ds := dA) (pol := .waitUpTo timeoutMs) false timeoutMs tr (dl + 1) rfl hV hMkA hcA rfl (fun _ => hLeDl) (Nat.lt_succ_of_le hLeDl) hRLt rfl hLt (.ok val)]
    · exact ⟨rfl, rfl, rfl, hLeDl, Or.inr (next_absent (s := sTA) hcA freeIdx)⟩
    · rw [stateM_bind_run, shared_acq (s := sTA) hcA freeIdx]; dsimp only; simp; rfl
  · by_cases hT : 1 ≤ timeoutMs
    · simp only [hT, ↓reduceIte, allPass_assert_end]; let sD : PoolSimState := { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx dl (dl + 1) cfg.totalSlots, monoNanos := startMono }
      obtain ⟨dD, hMkD, hcD⟩ := simMkdir_empty cfg.poolDir hDV (leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx dl (dl + 1) cfg.totalSlots) startMono; let sTD : PoolSimState := { sD with dirs := dD, monoNanos := dl, sleepLog := sD.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (timeoutMs + 1) timeoutMs).toArray }
      have hRunD : ∀ vAct : Nat → StateM PoolSimState (Except SlotPoolError Nat), (vAct freeIdx).run (withL sTD (lpJoin cfg.poolDir freeIdx)) = (.ok val, withL sTD (lpJoin cfg.poolDir freeIdx)) → ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) vAct).run sD = (.ok (.leased freeIdx val), withF sTD (lpJoin cfg.poolDir freeIdx)) := fun vAct hAct => by
        obtain ⟨hBLt, _, hFreeAt⟩ := leasesBeforeSlotUntil_conflict (s := sTD) hDV rfl
        exact withSlot_sim_waitUpTo_at_dl hV hTM hMkD hcD (fun t ht k hk => allBusy_until (s := { sD with dirs := dD, monoNanos := t }) hDV rfl ht (Nat.le_succ dl) k (Nat.zero_le _) (by omega)) vAct (Nat.le_refl dl) (scan_acq (s := sTD) hcD vAct freeIdx (.ok val) (hFreeAt rfl hLt (Nat.le_refl _)) hAct 0 cfg.totalSlots (Nat.zero_le _) (by omega) (fun k _ hlt => hBLt k (by omega) hlt (Nat.lt_succ_self dl)))
      rw [hRunD]; · exact ⟨⟨rfl, rfl, rfl, Or.inr (next_absent (s := sTD) hcD freeIdx)⟩, trivial⟩
      · rw [stateM_bind_run, shared_acq (s := sTD) hcD freeIdx]; dsimp only; simp; rfl
    · simp only [hT, ↓reduceIte, allPass_assert_end]; exact ⟨trivial, trivial⟩
/-- Specification 11 (`AllPass`): `WaitPolicy.waitForever` emits `repeatSleepChunks cfg.pollIntervalMs rounds`, acquires the lowest freed slot `.exclusive` without touching higher slots, and releases it on exit. -/
theorem proof_waitForever_contendedPool_pollsUntilSlotFree : AllPass (test_slotpool_waitForever_contendedPool_pollsUntilSlotFree mkApiM) := by
  intro cfg freeIdx rounds val startMono ⟨hV, hLt, _, hRMax⟩; obtain ⟨_, hDV, _, hPoll⟩ := validatePoolConfig_of_true cfg hV; dsimp only [test_slotpool_waitForever_contendedPool_pollsUntilSlotFree, AllPass]; rw [allPass_assert, allPass_assert, allPass_assert_end]
  let tr := startMono + rounds * cfg.pollIntervalMs * nanosecondsPerMs; let otherRel := tr + cfg.pollIntervalMs * nanosecondsPerMs; have hLocked : tr < otherRel := (by have : 0 < cfg.pollIntervalMs * nanosecondsPerMs := Nat.mul_pos hPoll (by decide); omega)
  let s₀ : PoolSimState := { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx tr otherRel cfg.totalSlots, monoNanos := startMono }; obtain ⟨ds, hMk, hc⟩ := simMkdir_empty cfg.poolDir hDV (leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx tr otherRel cfg.totalSlots) startMono
  let sT : PoolSimState := { s₀ with dirs := ds, monoNanos := tr, sleepLog := s₀.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs rounds).toArray }
  rw [withSlot_sim_waitRounds (s₀ := s₀) (ds := ds) (pol := .waitForever) true 0 tr otherRel rfl hV hMk hc rfl (fun h => nomatch h) hLocked hRMax rfl hLt (.ok val)]
  · exact ⟨⟨rfl, rfl⟩, Or.inr (next_absent (s := sT) hc freeIdx), ⟨rfl, by simp [s₀]⟩, trivial⟩
  · rw [stateM_bind_run, shared_acq (s := sT) hc freeIdx]; dsimp only; simp; rfl
/-- Witness 7 (`CanReach`): `test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock` is reachable for `mkApiM`. -/
theorem reach_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock : CanReach (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock mkApiM) := ⟨pc "pool/" 2 50, 1, 77, .waitUpTo 0, false, 123, by decide, proof_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock (pc "pool/" 2 50) 1 77 (.waitUpTo 0) false 123 (by decide)⟩
/-- Witness 8 (`CanReach`): `test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan` is reachable for `mkApiM`. -/
theorem reach_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan : CanReach (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan mkApiM) := ⟨pc "pool" 2 2, 0, 1, { kind := .ioError, path := none, message := "" }, .noWait, by decide, proof_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan (pc "pool" 2 2) 0 1 { kind := .ioError, path := none, message := "" } .noWait (by decide)⟩
/-- Witness 9 (`CanReach`): `test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates` is reachable for `mkApiM`. -/
theorem reach_monadFinally_uncaughtException_releasesLockAndPropagates : CanReach (test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates mkApiM) := ⟨pc "pool" 1 50, 0, .noWait, by decide, proof_monadFinally_uncaughtException_releasesLockAndPropagates (pc "pool" 1 50) 0 .noWait (by decide)⟩
/-- Witness 10 (`CanReach`): `test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline` is reachable for `mkApiM`. -/
theorem reach_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline : CanReach (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline mkApiM) := ⟨pc "pool" 2 2, 0, 1, 3, 99, 0, by decide, proof_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline (pc "pool" 2 2) 0 1 3 99 0 (by decide)⟩
/-- Witness 11 (`CanReach`): `test_slotpool_waitForever_contendedPool_pollsUntilSlotFree` is reachable for `mkApiM`. -/
theorem reach_waitForever_contendedPool_pollsUntilSlotFree : CanReach (test_slotpool_waitForever_contendedPool_pollsUntilSlotFree mkApiM) := ⟨pc "pool" 3 50, 1, 3, 88, 500, by decide, proof_waitForever_contendedPool_pollsUntilSlotFree (pc "pool" 3 50) 1 3 88 500 (by decide)⟩
end LeanSwe.SlotPool.Proofs
