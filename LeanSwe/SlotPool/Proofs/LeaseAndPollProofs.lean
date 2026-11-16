import LeanSwe.SlotPool.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Impl
import LeanSwe.SlotPool.Interface
import LeanSwe.SlotPool.SpecTests
import LeanSwe.SlotPool.Proofs.SimLemmas

set_option Elab.async false

namespace LeanSwe.SlotPool.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Model
open LeanSwe.SlotPool.Internal (ScanOutcome scanSlotsM pollWaitUpToM pollForeverM withSlotM)
open LeanSwe.SlotPool (mkApiM)

private def outcomeOfExcept {α : Type} (idx : Nat) : Except SlotPoolError α → ScanOutcome α
  | .error e => .err e
  | .ok v => .leased idx v

private def outcomeOfLease {α : Type} (idx : Nat) : Except SlotPoolError α → Except SlotPoolError (LeaseOutcome α)
  | .error e => .error e
  | .ok v => .ok (.leased idx v)

private theorem scanSlotsM_simFs_allBusy {α : Type} (s : PoolSimState) (poolDir : String)
    (hValid : validPoolDir poolDir = true) (hFiles : s.files = []) (hSyms : s.symlinks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (hPar : normSimPath poolDir ∈ s.dirs)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (nextIdx rem : Nat)
    (hBusy : ∀ k, nextIdx ≤ k → k < nextIdx + rem →
      hasSimLockConflict s (slotLockPath simFs.join poolDir k) .exclusive = true) :
    (scanSlotsM simFs poolDir nextIdx rem action).run s = (.allBusy, s) := by
  induction rem generalizing nextIdx with
  | zero => rfl
  | succ r ih =>
    unfold scanSlotsM
    rw [stateM_bind_run, simFs_tryWithFileLock_run]
    have hConf := hBusy nextIdx (Nat.le_refl _) (by omega)
    rw [simTryAcquire_busy s poolDir hValid hFiles hSyms hDirsLen nextIdx hPar hConf]
    dsimp only
    exact ih (nextIdx + 1) (fun k hk1 hk2 => hBusy k (by omega) (by omega))

private theorem scanSlotsM_simFs_acquires {α : Type} (s : PoolSimState) (poolDir : String)
    (hValid : validPoolDir poolDir = true) (hFiles : s.files = []) (hSyms : s.symlinks = [])
    (hHeld : s.heldLocks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (hPar : normSimPath poolDir ∈ s.dirs)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (nextIdx rem freeIdx : Nat) (hLe : nextIdx ≤ freeIdx) (hLt : freeIdx < nextIdx + rem)
    (hBusy : ∀ k, nextIdx ≤ k → k < freeIdx →
      hasSimLockConflict s (slotLockPath simFs.join poolDir k) .exclusive = true)
    (hFree : hasSimLockConflict s (slotLockPath simFs.join poolDir freeIdx) .exclusive = false)
    (res : Except SlotPoolError α)
    (hAct : (action freeIdx).run { s with
        files := (slotLockPath simFs.join poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir freeIdx, .exclusive) :: s.heldLocks } =
      (res, { s with
        files := (slotLockPath simFs.join poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir freeIdx, .exclusive) :: s.heldLocks })) :
    (scanSlotsM simFs poolDir nextIdx rem action).run s =
      (outcomeOfExcept freeIdx res,
       { s with files := (slotLockPath simFs.join poolDir freeIdx, "") :: s.files }) := by
  induction rem generalizing nextIdx with
  | zero => omega
  | succ r ih =>
    unfold scanSlotsM
    rw [stateM_bind_run, simFs_tryWithFileLock_run]
    by_cases hlt : nextIdx < freeIdx
    · have hConf := hBusy nextIdx (Nat.le_refl _) hlt
      rw [simTryAcquire_busy s poolDir hValid hFiles hSyms hDirsLen nextIdx hPar hConf]
      dsimp only
      exact ih (nextIdx + 1) (by omega) (by omega) (fun k hk1 hk2 => hBusy k (by omega) hk2)
    · have hEq : nextIdx = freeIdx := by omega
      subst hEq
      rw [simTryAcquire_free s poolDir hValid hFiles hSyms hDirsLen nextIdx hPar hFree]
      dsimp only
      rw [stateM_bind_run, hAct]
      dsimp only [StateT.run, Pure.pure, StateT.pure]
      have hLpNorm := (slotLockPath_props hValid nextIdx).1
      rw [hLpNorm, removeFirstSimLock_cons_self, hHeld]
      cases res <;> rfl

private theorem simFs_sharedProbe_on_acquired (s : PoolSimState) (poolDir : String)
    (hValid : validPoolDir poolDir = true) (hSyms : s.symlinks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (idx : Nat) :
    let lp := slotLockPath simFs.join poolDir idx
    let sLocked : PoolSimState :=
      { s with files := (lp, "") :: s.files, heldLocks := (lp, .exclusive) :: s.heldLocks }
    (simFs.tryWithFileLock lp .shared false (pure (.ok ()))).run sLocked = (.ok none, sLocked) := by
  obtain ⟨hNorm, hLpValid, _, hLen, _, _⟩ := slotLockPath_props hValid idx
  apply simFs_sharedProbe_held hLpValid hNorm
  · intro hIn
    have hLe := hDirsLen _ hIn
    omega
  · simp [hSyms]
  · simp [hasSimFile]
  · exact List.mem_cons_self

private theorem simFsEx_sharedProbe_on_acquired (s : PoolSimState) (poolDir : String)
    (hValid : validPoolDir poolDir = true) (hSyms : s.symlinks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (idx : Nat) :
    let lp := slotLockPath simFs.join poolDir idx
    let sLocked : PoolSimState :=
      { s with files := (lp, "") :: s.files, heldLocks := (lp, .exclusive) :: s.heldLocks }
    (ExceptT.run (simFsEx.tryWithFileLock lp .shared false (pure (.ok ())))).run sLocked =
      (.ok (.ok none), sLocked) := by
  obtain ⟨hNorm, hLpValid, _, hLen, _, _⟩ := slotLockPath_props hValid idx
  dsimp only
  rw [simFsEx_tryWithFileLock_run]
  have hConf : hasSimLockConflict
      { s with
        files := (slotLockPath simFs.join poolDir idx, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir idx, .exclusive) :: s.heldLocks }
      (slotLockPath simFs.join poolDir idx) .shared = true := by
    unfold hasSimLockConflict
    have h2 : (LockMode.exclusive == LockMode.exclusive) = true := rfl
    have hAny :
        ((slotLockPath simFs.join poolDir idx, LockMode.exclusive) :: s.heldLocks).any
          (fun (p, m) =>
            p == slotLockPath simFs.join poolDir idx && (LockMode.shared == .exclusive || m == .exclusive)) = true :=
      List.any_eq_true.mpr ⟨(slotLockPath simFs.join poolDir idx, .exclusive), List.mem_cons_self, by simp [h2]⟩
    simp [hAny]
  have hNotDir : ¬ (slotLockPath simFs.join poolDir idx ∈ s.dirs) := by
    intro hIn
    have hLe := hDirsLen _ hIn
    omega
  have hNotSym : ¬ (slotLockPath simFs.join poolDir idx ∈ s.symlinks) := by simp [hSyms]
  have hFile : hasSimFile
      { s with
        files := (slotLockPath simFs.join poolDir idx, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir idx, .exclusive) :: s.heldLocks }
      (slotLockPath simFs.join poolDir idx) = true := by simp [hasSimFile]
  have hAcqNone : simTryAcquirePure
      { s with
        files := (slotLockPath simFs.join poolDir idx, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir idx, .exclusive) :: s.heldLocks }
      (slotLockPath simFs.join poolDir idx) .shared false = .ok none := by
    unfold simTryAcquirePure
    rw [hNorm]
    simp only [hLpValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hNotDir, hNotSym, hFile, hConf]
  rw [hAcqNone]

private theorem scanSlotsM_simFsEx_throws (s : PoolSimState) (poolDir : String)
    (hValid : validPoolDir poolDir = true) (hFiles : s.files = []) (hSyms : s.symlinks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (hPar : normSimPath poolDir ∈ s.dirs)
    (action : Nat → ExceptT String (StateM PoolSimState) (Except SlotPoolError Unit))
    (nextIdx rem freeIdx : Nat) (hLe : nextIdx ≤ freeIdx) (hLt : freeIdx < nextIdx + rem)
    (hBusy : ∀ k, nextIdx ≤ k → k < freeIdx →
      hasSimLockConflict s (slotLockPath simFs.join poolDir k) .exclusive = true)
    (hFree : hasSimLockConflict s (slotLockPath simFs.join poolDir freeIdx) .exclusive = false)
    (hAct : (ExceptT.run (action freeIdx)).run { s with
        files := (slotLockPath simFs.join poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir freeIdx, .exclusive) :: s.heldLocks } =
      (.error "boom", { s with
        files := (slotLockPath simFs.join poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join poolDir freeIdx, .exclusive) :: s.heldLocks })) :
    (ExceptT.run (scanSlotsM simFsEx poolDir nextIdx rem action)).run s =
      (.error "boom", { s with files := (slotLockPath simFs.join poolDir freeIdx, "") :: s.files }) := by
  induction rem generalizing nextIdx with
  | zero => omega
  | succ r ih =>
    unfold scanSlotsM
    rw [exceptT_bind_run]
    have hJoin : simFsEx.join = simFs.join := rfl
    rw [hJoin, simFsEx_tryWithFileLock_run]
    by_cases hlt : nextIdx < freeIdx
    · have hConf := hBusy nextIdx (Nat.le_refl _) hlt
      rw [simTryAcquire_busy s poolDir hValid hFiles hSyms hDirsLen nextIdx hPar hConf]
      dsimp only
      exact ih (nextIdx + 1) (by omega) (by omega) (fun k hk1 hk2 => hBusy k (by omega) hk2)
    · have hEq : nextIdx = freeIdx := by omega
      subst hEq
      rw [simTryAcquire_free s poolDir hValid hFiles hSyms hDirsLen nextIdx hPar hFree]
      dsimp only
      rw [exceptT_bind_run, hAct]
      dsimp only [ExceptT.run, ExceptT.mk, StateT.run, Pure.pure, StateT.pure]
      have hLpNorm := (slotLockPath_props hValid nextIdx).1
      rw [hLpNorm, removeFirstSimLock_cons_self]

private theorem postProbe_on_endState (s : PoolSimState) (poolDir : String)
    (hValid : validPoolDir poolDir = true) (hSyms : s.symlinks = [])
    (hDirsLen : ∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath poolDir).toList.length)
    (idx : Nat)
    (hFree : hasSimLockConflict { s with files := (slotLockPath simFs.join poolDir idx, "") :: s.files }
      (slotLockPath simFs.join poolDir idx) .exclusive = false) :
    (simFs.tryWithFileLock (slotLockPath simFs.join poolDir idx) .exclusive false (pure (.ok ()))).run
      { s with files := (slotLockPath simFs.join poolDir idx, "") :: s.files } =
      (.ok (some ()), { s with files := (slotLockPath simFs.join poolDir idx, "") :: s.files }) := by
  obtain ⟨hNorm, hLpValid, _, hLen, _, _⟩ := slotLockPath_props hValid idx
  have hRes := simFs_postProbe_ok (s := { s with files := (slotLockPath simFs.join poolDir idx, "") :: s.files })
    hLpValid hNorm
    (fun hIn => by have hLe := hDirsLen _ hIn; omega)
    (by simp [hSyms])
    (by simp [hasSimFile])
    hFree
  rw [hRes, removeFirstSimLock_cons_self]

private theorem nextPath_not_in_single_file (poolDir : String) (hValid : validPoolDir poolDir = true)
    (idx : Nat) :
    hasSimFile ({ files := [(slotLockPath simFs.join poolDir idx, "")] } : PoolSimState)
      (normSimPath (slotLockPath simFs.join poolDir (idx + 1))) = false := by
  rw [(slotLockPath_props hValid (idx + 1)).1]
  simp only [hasSimFile, List.any_cons, List.any_nil, Bool.or_false]
  exact beq_false_of_ne (fun hEq => by have := slotLockPath_inj hValid hEq; omega)

private theorem hasSimFile_cons_same_fields (s : PoolSimState) (fp p : String) (hFiles : s.files = []) :
    hasSimFile { s with files := (fp, "") :: s.files } p =
      hasSimFile ({ files := [(fp, "")] } : PoolSimState) p := by
  simp [hasSimFile, hFiles]

private theorem dispatch_first_scan_state {α : Type} (fs : FsApiM (StateM PoolSimState))
    (time : TimeOpsM (StateM PoolSimState)) (cfg : PoolConfig) (policy : WaitPolicy)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (sAfterMk : PoolSimState) (res : Except SlotPoolError (LeaseOutcome α)) (sEnd : PoolSimState)
    (hTimeMono : time.monoNanosNow.run sAfterMk = (sAfterMk.monoNanos, sAfterMk))
    (hNonBusy : (∃ idx val, (scanSlotsM fs cfg.poolDir 0 cfg.totalSlots action).run sAfterMk = (.leased idx val, sEnd) ∧
        res = .ok (.leased idx val)) ∨
      (∃ e, (scanSlotsM fs cfg.poolDir 0 cfg.totalSlots action).run sAfterMk = (.err e, sEnd) ∧
        res = .error e)) :
    (do match policy with
      | .noWait =>
        match ← scanSlotsM fs cfg.poolDir 0 cfg.totalSlots action with
        | .leased idx val => return (Except.ok (.leased idx val) : Except SlotPoolError (LeaseOutcome α))
        | .err e => return (Except.error e : Except SlotPoolError (LeaseOutcome α))
        | .allBusy => return (Except.ok .noSlot : Except SlotPoolError (LeaseOutcome α))
      | .waitUpTo timeoutMs =>
        let startNs ← time.monoNanosNow
        let dl := deadlineNanos startNs timeoutMs
        pollWaitUpToM fs time cfg dl action maxForeverPolls
      | .waitForever =>
        pollForeverM fs time cfg action maxForeverPolls).run sAfterMk = (res, sEnd) := by
  have hF : maxForeverPolls = (2 ^ 64 - 1) + 1 := by decide
  cases policy with
  | noWait =>
    dsimp only
    rw [stateM_bind_run]
    rcases hNonBusy with ⟨idx, val, hScan, hRes⟩ | ⟨e, hScan, hRes⟩
    · rw [hScan, hRes]; rfl
    · rw [hScan, hRes]; rfl
  | waitUpTo timeoutMs =>
    dsimp only
    rw [stateM_bind_run, hTimeMono]
    dsimp only
    rw [hF]
    unfold pollWaitUpToM
    rw [stateM_bind_run]
    rcases hNonBusy with ⟨idx, val, hScan, hRes⟩ | ⟨e, hScan, hRes⟩
    · rw [hScan, hRes]; rfl
    · rw [hScan, hRes]; rfl
  | waitForever =>
    dsimp only
    rw [hF]
    unfold pollForeverM
    rw [stateM_bind_run]
    rcases hNonBusy with ⟨idx, val, hScan, hRes⟩ | ⟨e, hScan, hRes⟩
    · rw [hScan, hRes]; rfl
    · rw [hScan, hRes]; rfl

private theorem withSlot_sim_firstScan_res {α : Type}
    (cfg : PoolConfig) (policy : WaitPolicy) (s₀ sAfterMk : PoolSimState)
    (hValid : validPoolConfig cfg = true)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), sAfterMk))
    (hFiles : sAfterMk.files = []) (hSyms : sAfterMk.symlinks = [])
    (hHeld : sAfterMk.heldLocks = [])
    (hDirsLen : ∀ d ∈ sAfterMk.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length)
    (hPar : normSimPath cfg.poolDir ∈ sAfterMk.dirs)
    (freeIdx : Nat) (hFreeLt : freeIdx < cfg.totalSlots)
    (hBusy : ∀ k, 0 ≤ k → k < freeIdx →
      hasSimLockConflict sAfterMk (slotLockPath simFs.join cfg.poolDir k) .exclusive = true)
    (hFree : hasSimLockConflict sAfterMk (slotLockPath simFs.join cfg.poolDir freeIdx) .exclusive = false)
    (res : Except SlotPoolError α)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (hAct : (action freeIdx).run { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks } =
      (res, { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks })) :
    ((mkApiM simFs simTime).withSlot cfg policy action).run s₀ =
      (outcomeOfLease freeIdx res,
       { sAfterMk with files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files }) := by
  obtain ⟨hVal, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  have hScan := scanSlotsM_simFs_acquires sAfterMk cfg.poolDir hDirValid hFiles hSyms hHeld hDirsLen hPar
    action 0 cfg.totalSlots freeIdx (Nat.zero_le _) (by omega) hBusy hFree res hAct
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]
  rw [hVal]; dsimp only
  rw [stateM_bind_run, hMk]; dsimp only
  cases res with
  | ok v =>
    exact dispatch_first_scan_state simFs simTime cfg policy action sAfterMk (.ok (.leased freeIdx v))
      { sAfterMk with files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files }
      rfl (Or.inl ⟨freeIdx, v, hScan, rfl⟩)
  | error e =>
    exact dispatch_first_scan_state simFs simTime cfg policy action sAfterMk (.error e)
      { sAfterMk with files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files }
      rfl (Or.inr ⟨e, hScan, rfl⟩)

private theorem withSlot_simEx_firstScan_throws
    (cfg : PoolConfig) (policy : WaitPolicy) (s₀ sAfterMk : PoolSimState)
    (hValid : validPoolConfig cfg = true)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), sAfterMk))
    (hFiles : sAfterMk.files = []) (hSyms : sAfterMk.symlinks = [])
    (hDirsLen : ∀ d ∈ sAfterMk.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length)
    (hPar : normSimPath cfg.poolDir ∈ sAfterMk.dirs)
    (freeIdx : Nat) (hFreeLt : freeIdx < cfg.totalSlots)
    (hBusy : ∀ k, 0 ≤ k → k < freeIdx →
      hasSimLockConflict sAfterMk (slotLockPath simFs.join cfg.poolDir k) .exclusive = true)
    (hFree : hasSimLockConflict sAfterMk (slotLockPath simFs.join cfg.poolDir freeIdx) .exclusive = false)
    (action : Nat → ExceptT String (StateM PoolSimState) (Except SlotPoolError Unit))
    (hAct : (ExceptT.run (action freeIdx)).run { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks } =
      (.error "boom", { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks })) :
    (ExceptT.run ((mkApiM simFsEx simTimeEx).withSlot cfg policy action)).run s₀ =
      (.error "boom",
       { sAfterMk with files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files }) := by
  obtain ⟨hVal, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  have hScanEx := scanSlotsM_simFsEx_throws sAfterMk cfg.poolDir hDirValid hFiles hSyms hDirsLen hPar
    action 0 cfg.totalSlots freeIdx (Nat.zero_le _) (by omega) hBusy hFree hAct
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]
  rw [hVal]; dsimp only
  rw [exceptT_bind_run, simFsEx_mkdir_run, hMk]; dsimp only
  have hF : maxForeverPolls = (2 ^ 64 - 1) + 1 := by decide
  cases policy with
  | noWait =>
    dsimp only
    rw [exceptT_bind_run, hScanEx]
  | waitUpTo timeoutMs =>
    dsimp only
    rw [exceptT_bind_run]
    have hMonoEx : (ExceptT.run simTimeEx.monoNanosNow).run sAfterMk = (.ok sAfterMk.monoNanos, sAfterMk) := rfl
    rw [hMonoEx]; dsimp only
    rw [hF]; unfold pollWaitUpToM
    rw [exceptT_bind_run, hScanEx]
  | waitForever =>
    dsimp only
    rw [hF]; unfold pollForeverM
    rw [exceptT_bind_run, hScanEx]

/-- Specification 7 (`AllPass`): `withSlot` creates `cfg.poolDir`, scans ascending from slot `0`, acquires the lowest free slot `.exclusive` with `createIfMissing = true`, and releases it on `.ok` while keeping the lock file on disk. -/
theorem proof_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock :
    AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock mkApiM) := by
  intro cfg freeIdx val policy dirPreExists startMono ⟨hValid, hFreeLt⟩
  obtain ⟨_, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock, AllPass]
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  let s₀ : PoolSimState :=
    { dirs := if dirPreExists then [normSimPath cfg.poolDir] else []
      externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (startMono + 1000000000) freeIdx
      monoNanos := startMono }
  have hDirsLen0 : ∀ d ∈ s₀.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd
    cases dirPreExists
    · simp [s₀] at hd
    · simp only [s₀, ↓reduceIte, List.mem_singleton] at hd
      subst hd
      exact Nat.le_refl _
  obtain ⟨sAfterMk, hMkRun, hFilesMk, hSymsMk, hHeldMk, hExtMk, _, hMonoMk, hSleepMk, hParMk, hDirsLenMk⟩ :=
    simMkdir_clean s₀ cfg.poolDir rfl rfl rfl hDirValid hDirsLen0
  have hHeld0 : sAfterMk.heldLocks = [] := hHeldMk
  have hMonoEq : sAfterMk.monoNanos = startMono := hMonoMk
  have hSleepEq : sAfterMk.sleepLog = #[] := hSleepMk
  obtain ⟨hBusyBefore, hFreeAt⟩ := leasesBeforeSlot_conflict hDirValid hExtMk
  let expectedLockPath := slotLockPath simFs.join cfg.poolDir freeIdx
  let sEnd : PoolSimState := { sAfterMk with files := (expectedLockPath, "") :: sAfterMk.files }
  have hPostFree : hasSimLockConflict sEnd expectedLockPath .exclusive = false :=
    (leasesBeforeSlot_conflict (s := sEnd) hDirValid hExtMk).2 hHeld0
  have hPost := postProbe_on_endState sAfterMk cfg.poolDir hDirValid hSymsMk hDirsLenMk freeIdx hPostFree
  have hNextNo : hasSimFile sEnd (normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))) = false := by
    dsimp only [sEnd]
    rw [hasSimFile_cons_same_fields sAfterMk expectedLockPath _ hFilesMk]
    exact nextPath_not_in_single_file cfg.poolDir hDirValid freeIdx
  rw [withSlot_sim_firstScan_res cfg policy s₀ sAfterMk hValid hMkRun hFilesMk hSymsMk hHeld0 hDirsLenMk hParMk
    freeIdx hFreeLt (fun k _ hlt => hBusyBefore k hlt (by rw [hMonoEq]; omega)) (hFreeAt hHeld0) (.ok val)]
  · dsimp only [outcomeOfLease]
    rw [hPost]
    exact ⟨⟨rfl, hFreeLt⟩, ⟨hHeld0, rfl⟩, Or.inr hNextNo, ⟨hSleepEq, hMonoEq⟩, trivial⟩
  · rw [stateM_bind_run, simFs_sharedProbe_on_acquired sAfterMk cfg.poolDir hDirValid hSymsMk hDirsLenMk freeIdx]
    dsimp only
    simp [hFreeLt]
    rfl

private theorem pollForeverM_leasesBeforeSlotUntil_reaches {α : Type}
    (cfg : PoolConfig) (hValid : validPoolConfig cfg = true)
    (freeIdx targetRelNs lockedUntilNs : Nat)
    (hLtLocked : targetRelNs ≤ lockedUntilNs)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α)) :
    ∀ (k fuel : Nat) (s : PoolSimState),
      k < fuel →
      s.files = [] →
      s.symlinks = [] →
      s.heldLocks = [] →
      normSimPath cfg.poolDir ∈ s.dirs →
      (∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) →
      s.externalLeases = leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots →
      s.monoNanos + k * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs →
      ∃ remFuel, remFuel ≥ 1 ∧
        (pollForeverM simFs simTime cfg action fuel).run s =
          (pollForeverM simFs simTime cfg action remFuel).run
            { s with
              monoNanos := targetRelNs
              sleepLog := s.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } := by
  intro k
  induction k with
  | zero =>
    intro fuel s hLt _ _ _ _ _ _ hMono
    rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero] at hMono
    subst hMono
    refine ⟨fuel, hLt, ?_⟩
    simp [repeatSleepChunks]
  | succ k' ih =>
    intro fuel s hLt hFiles hSyms hHeld hPar hDirsLen hExt hMono
    obtain ⟨_, hDirValid, _, hPollPos⟩ := validatePoolConfig_of_true cfg hValid
    cases fuel with
    | zero => omega
    | succ f =>
      have hMonoLt : s.monoNanos < targetRelNs := by
        have hMulPos : 0 < (k' + 1) * cfg.pollIntervalMs * nanosecondsPerMs := by
          have : 1 ≤ nanosecondsPerMs := by decide
          exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos k') hPollPos) this
        omega
      obtain ⟨hBusyLt, hBusyGe, _⟩ := leasesBeforeSlotUntil_conflict hDirValid hExt
      have hAllBusy : ∀ j, 0 ≤ j → j < 0 + cfg.totalSlots →
          hasSimLockConflict s (slotLockPath simFs.join cfg.poolDir j) .exclusive = true := by
        intro j _ hj
        by_cases hjlt : j < freeIdx
        · exact hBusyLt j (by omega) hjlt (Nat.lt_of_lt_of_le hMonoLt hLtLocked)
        · exact hBusyGe j (by omega) (Nat.not_lt.mp hjlt) hMonoLt
      have hScan := scanSlotsM_simFs_allBusy s cfg.poolDir hDirValid hFiles hSyms hDirsLen hPar action 0 cfg.totalSlots hAllBusy
      let s1 : PoolSimState :=
        { s with
          monoNanos := s.monoNanos + cfg.pollIntervalMs * nanosecondsPerMs
          sleepLog := s.sleepLog ++ (sleepChunks cfg.pollIntervalMs).toArray }
      have hStep : (pollForeverM simFs simTime cfg action (f + 1)).run s =
          (pollForeverM simFs simTime cfg action f).run s1 := by
        conv => lhs; unfold pollForeverM
        rw [stateM_bind_run, hScan]
        dsimp only
        rw [stateM_bind_run, runSleepChunks_simTime_sleepChunks]
      have hMono1 : s1.monoNanos + k' * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs := by
        dsimp only [s1]
        have hDist : (k' + 1) * cfg.pollIntervalMs * nanosecondsPerMs =
            cfg.pollIntervalMs * nanosecondsPerMs + k' * cfg.pollIntervalMs * nanosecondsPerMs := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        omega
      obtain ⟨remFuel, hRemPos, hRec⟩ :=
        ih f s1 (Nat.lt_of_succ_lt_succ hLt) hFiles hSyms hHeld hPar hDirsLen hExt hMono1
      have hLogEq : s1.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k').toArray =
          s.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs (k' + 1)).toArray := by
        dsimp only [s1]
        have hRep : repeatSleepChunks cfg.pollIntervalMs (k' + 1) =
            sleepChunks cfg.pollIntervalMs ++ repeatSleepChunks cfg.pollIntervalMs k' := rfl
        rw [hRep]
        apply Array.ext'
        simp
      refine ⟨remFuel, hRemPos, ?_⟩
      rw [hStep, hRec, hLogEq]

private theorem pollWaitUpToM_leasesBeforeSlotUntil_rounds {α : Type}
    (cfg : PoolConfig) (hValid : validPoolConfig cfg = true)
    (freeIdx targetRelNs lockedUntilNs dl : Nat)
    (hLeDl : targetRelNs ≤ dl) (hLtLocked : targetRelNs ≤ lockedUntilNs)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α)) :
    ∀ (k fuel : Nat) (s : PoolSimState),
      k < fuel →
      s.files = [] →
      s.symlinks = [] →
      s.heldLocks = [] →
      normSimPath cfg.poolDir ∈ s.dirs →
      (∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) →
      s.externalLeases = leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots →
      s.monoNanos + k * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs →
      ∃ remFuel, remFuel ≥ 1 ∧
        (pollWaitUpToM simFs simTime cfg dl action fuel).run s =
          (pollWaitUpToM simFs simTime cfg dl action remFuel).run
            { s with
              monoNanos := targetRelNs
              sleepLog := s.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } := by
  intro k
  induction k with
  | zero =>
    intro fuel s hLt _ _ _ _ _ _ hMono
    rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero] at hMono
    subst hMono
    refine ⟨fuel, hLt, ?_⟩
    simp [repeatSleepChunks]
  | succ k' ih =>
    intro fuel s hLt hFiles hSyms hHeld hPar hDirsLen hExt hMono
    obtain ⟨_, hDirValid, _, hPollPos⟩ := validatePoolConfig_of_true cfg hValid
    cases fuel with
    | zero => omega
    | succ f =>
      have hMonoLtTarget : s.monoNanos < targetRelNs := by
        have hMulPos : 0 < (k' + 1) * cfg.pollIntervalMs * nanosecondsPerMs := by
          have : 1 ≤ nanosecondsPerMs := by decide
          exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos k') hPollPos) this
        omega
      have hMonoLtDl : s.monoNanos < dl := Nat.lt_of_lt_of_le hMonoLtTarget hLeDl
      obtain ⟨hBusyLt, hBusyGe, _⟩ := leasesBeforeSlotUntil_conflict hDirValid hExt
      have hAllBusy : ∀ j, 0 ≤ j → j < 0 + cfg.totalSlots →
          hasSimLockConflict s (slotLockPath simFs.join cfg.poolDir j) .exclusive = true := by
        intro j _ hj
        by_cases hjlt : j < freeIdx
        · exact hBusyLt j (by omega) hjlt (Nat.lt_of_lt_of_le hMonoLtTarget hLtLocked)
        · exact hBusyGe j (by omega) (Nat.not_lt.mp hjlt) hMonoLtTarget
      have hScan := scanSlotsM_simFs_allBusy s cfg.poolDir hDirValid hFiles hSyms hDirsLen hPar action 0 cfg.totalSlots hAllBusy
      let s1 : PoolSimState :=
        { s with
          monoNanos := s.monoNanos + cfg.pollIntervalMs * nanosecondsPerMs
          sleepLog := s.sleepLog ++ (sleepChunks cfg.pollIntervalMs).toArray }
      have hStep : (pollWaitUpToM simFs simTime cfg dl action (f + 1)).run s =
          (pollWaitUpToM simFs simTime cfg dl action f).run s1 := by
        conv => lhs; unfold pollWaitUpToM
        rw [stateM_bind_run, hScan]
        dsimp only
        rw [stateM_bind_run]
        have hMonoNow : simTime.monoNanosNow.run s = (s.monoNanos, s) := rfl
        rw [hMonoNow]
        dsimp only
        have hNotGe : ¬ (s.monoNanos ≥ dl) := Nat.not_le.mpr hMonoLtDl
        simp only [hNotGe, ↓reduceIte]
        have hNextEq : nextSleepMs cfg.pollIntervalMs s.monoNanos dl = cfg.pollIntervalMs := by
          dsimp [nextSleepMs, remainingWaitMs]
          simp only [hNotGe, ↓reduceIte]
          apply Nat.min_eq_left
          have hDist : (k' + 1) * cfg.pollIntervalMs * nanosecondsPerMs =
              cfg.pollIntervalMs * nanosecondsPerMs + k' * cfg.pollIntervalMs * nanosecondsPerMs := by
            rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.add_comm]
          dsimp [nanosecondsPerMs] at *
          omega
        rw [hNextEq, stateM_bind_run, runSleepChunks_simTime_sleepChunks]
      have hMono1 : s1.monoNanos + k' * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs := by
        dsimp only [s1]
        have hDist : (k' + 1) * cfg.pollIntervalMs * nanosecondsPerMs =
            cfg.pollIntervalMs * nanosecondsPerMs + k' * cfg.pollIntervalMs * nanosecondsPerMs := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        omega
      obtain ⟨remFuel, hRemPos, hRec⟩ :=
        ih f s1 (Nat.lt_of_succ_lt_succ hLt) hFiles hSyms hHeld hPar hDirsLen hExt hMono1
      have hLogEq : s1.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k').toArray =
          s.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs (k' + 1)).toArray := by
        dsimp only [s1]
        have hRep : repeatSleepChunks cfg.pollIntervalMs (k' + 1) =
            sleepChunks cfg.pollIntervalMs ++ repeatSleepChunks cfg.pollIntervalMs k' := rfl
        rw [hRep]
        apply Array.ext'
        simp
      refine ⟨remFuel, hRemPos, ?_⟩
      rw [hStep, hRec, hLogEq]

private theorem withSlot_sim_waitForever_rounds {α : Type}
    (cfg : PoolConfig) (freeIdx k : Nat) (s₀ sAfterMk : PoolSimState)
    (hValid : validPoolConfig cfg = true)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), sAfterMk))
    (hFiles : sAfterMk.files = []) (hSyms : sAfterMk.symlinks = [])
    (hHeld : sAfterMk.heldLocks = []) (hPar : normSimPath cfg.poolDir ∈ sAfterMk.dirs)
    (hDirsLen : ∀ d ∈ sAfterMk.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length)
    (targetRelNs lockedUntilNs : Nat)
    (hExt : sAfterMk.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots)
    (hLtLocked : targetRelNs ≤ lockedUntilNs) (hLockedStrict : targetRelNs < lockedUntilNs)
    (hRoundsMax : k < maxForeverPolls)
    (hMonoSum : sAfterMk.monoNanos + k * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs)
    (hFreeLt : freeIdx < cfg.totalSlots) (res : Except SlotPoolError α)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (hAct : (action freeIdx).run { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := targetRelNs
        sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } =
      (res, { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := targetRelNs
        sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray })) :
    ((mkApiM simFs simTime).withSlot cfg .waitForever action).run s₀ =
      (outcomeOfLease freeIdx res,
       { sAfterMk with
         files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
         monoNanos := targetRelNs
         sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray }) := by
  obtain ⟨hVal, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  let sTarget : PoolSimState :=
    { sAfterMk with
      monoNanos := targetRelNs
      sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray }
  have hExtTarget : sTarget.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots := hExt
  obtain ⟨hBusyLt, _, hFreeAt⟩ := leasesBeforeSlotUntil_conflict hDirValid hExtTarget
  have hScan := scanSlotsM_simFs_acquires sTarget cfg.poolDir hDirValid hFiles hSyms hHeld hDirsLen hPar
    action 0 cfg.totalSlots freeIdx (Nat.zero_le _) (by omega)
    (fun j _ hlt => hBusyLt j (by omega) hlt hLockedStrict)
    (hFreeAt hHeld hFreeLt (Nat.le_refl _)) res hAct
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]
  rw [hVal]; dsimp only
  rw [stateM_bind_run, hMk]; dsimp only
  obtain ⟨remFuel, hRemPos, hReach⟩ :=
    pollForeverM_leasesBeforeSlotUntil_reaches cfg hValid freeIdx targetRelNs lockedUntilNs
      hLtLocked action k maxForeverPolls sAfterMk hRoundsMax
      hFiles hSyms hHeld hPar hDirsLen hExt hMonoSum
  rw [hReach]
  obtain ⟨f', hf'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hRemPos)
  rw [hf']
  conv => lhs; unfold pollForeverM
  rw [stateM_bind_run, hScan]
  cases res <;> dsimp only [sTarget, outcomeOfExcept, outcomeOfLease] <;> rfl

private theorem withSlot_sim_waitUpTo_rounds {α : Type}
    (cfg : PoolConfig) (freeIdx k timeoutMs : Nat) (s₀ sAfterMk : PoolSimState)
    (hValid : validPoolConfig cfg = true)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), sAfterMk))
    (hFiles : sAfterMk.files = []) (hSyms : sAfterMk.symlinks = [])
    (hHeld : sAfterMk.heldLocks = []) (hPar : normSimPath cfg.poolDir ∈ sAfterMk.dirs)
    (hDirsLen : ∀ d ∈ sAfterMk.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length)
    (targetRelNs lockedUntilNs : Nat)
    (hExt : sAfterMk.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots)
    (hLeDl : targetRelNs ≤ deadlineNanos sAfterMk.monoNanos timeoutMs)
    (hLtLocked : targetRelNs ≤ lockedUntilNs) (hLockedStrict : targetRelNs < lockedUntilNs)
    (hRoundsLt : k < maxForeverPolls)
    (hMonoSum : sAfterMk.monoNanos + k * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs)
    (hFreeLt : freeIdx < cfg.totalSlots) (res : Except SlotPoolError α)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (hAct : (action freeIdx).run { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := targetRelNs
        sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } =
      (res, { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := targetRelNs
        sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray })) :
    ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run s₀ =
      (outcomeOfLease freeIdx res,
       { sAfterMk with
         files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
         monoNanos := targetRelNs
         sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray }) := by
  obtain ⟨hVal, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  let dl := deadlineNanos sAfterMk.monoNanos timeoutMs
  let sTarget : PoolSimState :=
    { sAfterMk with
      monoNanos := targetRelNs
      sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray }
  have hExtTarget : sTarget.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots := hExt
  obtain ⟨hBusyLt, _, hFreeAt⟩ := leasesBeforeSlotUntil_conflict hDirValid hExtTarget
  have hScan := scanSlotsM_simFs_acquires sTarget cfg.poolDir hDirValid hFiles hSyms hHeld hDirsLen hPar
    action 0 cfg.totalSlots freeIdx (Nat.zero_le _) (by omega)
    (fun j _ hlt => hBusyLt j (by omega) hlt hLockedStrict)
    (hFreeAt hHeld hFreeLt (Nat.le_refl _)) res hAct
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]
  rw [hVal]; dsimp only
  rw [stateM_bind_run, hMk]; dsimp only
  rw [stateM_bind_run]
  have hMonoNow : simTime.monoNanosNow.run sAfterMk = (sAfterMk.monoNanos, sAfterMk) := rfl
  rw [hMonoNow]; dsimp only
  obtain ⟨remFuel, hRemPos, hReach⟩ :=
    pollWaitUpToM_leasesBeforeSlotUntil_rounds cfg hValid freeIdx targetRelNs lockedUntilNs dl
      hLeDl hLtLocked action k maxForeverPolls sAfterMk hRoundsLt
      hFiles hSyms hHeld hPar hDirsLen hExt hMonoSum
  rw [hReach]
  obtain ⟨f', hf'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hRemPos)
  rw [hf']
  conv => lhs; unfold pollWaitUpToM
  rw [stateM_bind_run, hScan]
  cases res <;> dsimp only [sTarget, dl, outcomeOfExcept, outcomeOfLease] <;> rfl

private theorem withSlot_sim_retryPolicy_rounds {α : Type}
    (cfg : PoolConfig) (policy : WaitPolicy) (freeIdx k : Nat) (s₀ sAfterMk : PoolSimState)
    (hValid : validPoolConfig cfg = true)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), sAfterMk))
    (hFiles : sAfterMk.files = []) (hSyms : sAfterMk.symlinks = [])
    (hHeld : sAfterMk.heldLocks = []) (hMono0 : sAfterMk.monoNanos = 0)
    (hPar : normSimPath cfg.poolDir ∈ sAfterMk.dirs)
    (hDirsLen : ∀ d ∈ sAfterMk.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length)
    (targetRelNs lockedUntilNs : Nat)
    (hTarget : targetRelNs = k * cfg.pollIntervalMs * nanosecondsPerMs)
    (hExt : sAfterMk.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots)
    (hLtLocked : targetRelNs ≤ lockedUntilNs) (hLockedStrict : targetRelNs < lockedUntilNs)
    (hRoundsLt : k < maxForeverPolls)
    (hFreeLt : freeIdx < cfg.totalSlots) (res : Except SlotPoolError α)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (hAct : (action freeIdx).run { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := targetRelNs
        sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray } =
      (res, { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := targetRelNs
        sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray })) :
    ((mkApiM simFs simTime).withSlot cfg
      (if policy == .noWait then .waitForever else .waitUpTo (k * cfg.pollIntervalMs)) action).run s₀ =
      (outcomeOfLease freeIdx res,
       { sAfterMk with
         files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
         monoNanos := targetRelNs
         sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs k).toArray }) := by
  have hMonoSum : sAfterMk.monoNanos + k * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs := by
    rw [hMono0, Nat.zero_add, hTarget]
  cases hNoW : (policy == .noWait)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hLeDl : targetRelNs ≤ deadlineNanos sAfterMk.monoNanos (k * cfg.pollIntervalMs) := by
      dsimp [deadlineNanos]
      rw [hMono0, Nat.zero_add, hTarget]
      exact Nat.le_refl _
    exact withSlot_sim_waitUpTo_rounds cfg freeIdx k (k * cfg.pollIntervalMs) s₀ sAfterMk
      hValid hMk hFiles hSyms hHeld hPar hDirsLen targetRelNs lockedUntilNs hExt
      hLeDl hLtLocked hLockedStrict hRoundsLt hMonoSum hFreeLt res action hAct
  · simp only [↓reduceIte]
    exact withSlot_sim_waitForever_rounds cfg freeIdx k s₀ sAfterMk
      hValid hMk hFiles hSyms hHeld hPar hDirsLen targetRelNs lockedUntilNs hExt
      hLtLocked hLockedStrict hRoundsLt hMonoSum hFreeLt res action hAct

/-- Specification 8 (`AllPass`): callback `.error` on an acquired slot releases the lock, preserves the file on disk, stops scanning higher slots, and returns the error verbatim on both initial and retry scans. -/
theorem proof_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan :
    AllPass (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan mkApiM) := by
  intro cfg freeIdx retryRounds callbackErr policy ⟨hValid, hFreeLt, hRoundsPos, hRoundsMax⟩
  obtain ⟨_, hDirValid, _, hPollPos⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan, AllPass]
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  let freePath := slotLockPath simFs.join cfg.poolDir freeIdx
  let s₀ : PoolSimState :=
    { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx }
  have hDirsLen0 : ∀ d ∈ s₀.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd; cases hd
  obtain ⟨sAfterMk, hMkRun, hFilesMk, hSymsMk, hHeldMk, hExtMk, _, hMonoMk, hSleepMk, hParMk, hDirsLenMk⟩ :=
    simMkdir_clean s₀ cfg.poolDir rfl rfl rfl hDirValid hDirsLen0
  have hHeld0 : sAfterMk.heldLocks = [] := hHeldMk
  have hMono0 : sAfterMk.monoNanos = 0 := hMonoMk
  have hSleep0 : sAfterMk.sleepLog = #[] := hSleepMk
  obtain ⟨hBusyBefore, hFreeAt⟩ := leasesBeforeSlot_conflict hDirValid hExtMk
  let sEnd0 : PoolSimState := { sAfterMk with files := (freePath, "") :: sAfterMk.files }
  have hPostFree0 : hasSimLockConflict sEnd0 freePath .exclusive = false :=
    (leasesBeforeSlot_conflict (s := sEnd0) hDirValid hExtMk).2 hHeld0
  have hPost0 := postProbe_on_endState sAfterMk cfg.poolDir hDirValid hSymsMk hDirsLenMk freeIdx hPostFree0
  have hNoRan0 : hasSimFile sEnd0 "ran-other" = false := by
    dsimp only [sEnd0]
    rw [hasSimFile_cons_same_fields sAfterMk freePath _ hFilesMk]
    have hNe : freePath ≠ "ran-other" := (slotLockPath_props hDirValid freeIdx).2.2.2.2.1
    simp [hasSimFile, hNe]
  let targetRelNs := retryRounds * cfg.pollIntervalMs * nanosecondsPerMs
  let lockedUntilNs := targetRelNs + cfg.pollIntervalMs * nanosecondsPerMs
  let sRetry : PoolSimState :=
    { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots }
  have hDirsLenR : ∀ d ∈ sRetry.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd; cases hd
  obtain ⟨sAfterMkR, hMkRunR, hFilesMkR, hSymsMkR, hHeldMkR, hExtMkR, _, hMonoMkR, _, hParMkR, hDirsLenMkR⟩ :=
    simMkdir_clean sRetry cfg.poolDir rfl rfl rfl hDirValid hDirsLenR
  have hHeldR : sAfterMkR.heldLocks = [] := hHeldMkR
  have hMonoR0 : sAfterMkR.monoNanos = 0 := hMonoMkR
  have hLtLocked : targetRelNs ≤ lockedUntilNs := Nat.le_add_right _ _
  have hLockedStrict : targetRelNs < lockedUntilNs := by
    have hPos : 0 < cfg.pollIntervalMs * nanosecondsPerMs := Nat.mul_pos hPollPos (by decide)
    omega
  let sTarget : PoolSimState :=
    { sAfterMkR with
      monoNanos := targetRelNs
      sleepLog := sAfterMkR.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs retryRounds).toArray }
  let sEndR : PoolSimState := { sTarget with files := (freePath, "") :: sTarget.files }
  have hPostFreeR : hasSimLockConflict sEndR freePath .exclusive = false :=
    (leasesBeforeSlotUntil_conflict (s := sEndR) hDirValid hExtMkR).2.2 hHeldR hFreeLt (Nat.le_refl _)
  have hPostR := postProbe_on_endState sTarget cfg.poolDir hDirValid hSymsMkR hDirsLenMkR freeIdx hPostFreeR
  have hNoRanR : hasSimFile sEndR "ran-other" = false := by
    dsimp only [sEndR]
    rw [hasSimFile_cons_same_fields sTarget freePath _ hFilesMkR]
    have hNe : freePath ≠ "ran-other" := (slotLockPath_props hDirValid freeIdx).2.2.2.2.1
    simp [hasSimFile, hNe]
  rw [withSlot_sim_firstScan_res cfg policy s₀ sAfterMk hValid hMkRun hFilesMk hSymsMk hHeld0 hDirsLenMk hParMk
    freeIdx hFreeLt (fun k _ hlt => hBusyBefore k hlt (by rw [hMono0]; omega)) (hFreeAt hHeld0) (.error callbackErr)]
  · rw [withSlot_sim_retryPolicy_rounds cfg policy freeIdx retryRounds sRetry sAfterMkR hValid hMkRunR hFilesMkR hSymsMkR
      hHeldR hMonoR0 hParMkR hDirsLenMkR targetRelNs lockedUntilNs rfl hExtMkR hLtLocked hLockedStrict
      hRoundsMax hFreeLt (.error callbackErr)]
    · dsimp only [outcomeOfLease]
      rw [hPost0, hPostR]
      exact ⟨rfl, ⟨hHeld0, rfl⟩, ⟨hNoRan0, hSleep0⟩, ⟨rfl, hHeldR, rfl⟩, ⟨hNoRanR, rfl⟩, trivial⟩
    · simp only [beq_self_eq_true, ↓reduceIte]
      rw [stateM_bind_run, simFs_sharedProbe_on_acquired sTarget cfg.poolDir hDirValid hSymsMkR hDirsLenMkR freeIdx]
      rfl
  · simp only [beq_self_eq_true, ↓reduceIte]
    rw [stateM_bind_run, simFs_sharedProbe_on_acquired sAfterMk cfg.poolDir hDirValid hSymsMk hDirsLenMk freeIdx]
    rfl

/-- Specification 9 (`AllPass`): an uncaught monadic exception in `ExceptT String (StateM PoolSimState)` releases the held lock via `MonadFinally`, preserves the lock file on disk, and propagates the exception. -/
theorem proof_monadFinally_uncaughtException_releasesLockAndPropagates :
    AllPass (test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates mkApiM) := by
  intro cfg freeIdx policy ⟨hValid, hFreeLt⟩
  obtain ⟨_, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates, AllPass]
  rw [allPass_assert_end]
  let s₀ : PoolSimState :=
    { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx }
  let freePath := slotLockPath simFs.join cfg.poolDir freeIdx
  have hDirsLen0 : ∀ d ∈ s₀.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd; cases hd
  obtain ⟨sAfterMk, hMkRun, hFilesMk, hSymsMk, hHeldMk, hExtMk, _, hMonoMk, _, hParMk, hDirsLenMk⟩ :=
    simMkdir_clean s₀ cfg.poolDir rfl rfl rfl hDirValid hDirsLen0
  have hHeld0 : sAfterMk.heldLocks = [] := hHeldMk
  have hMono0 : sAfterMk.monoNanos = 0 := hMonoMk
  obtain ⟨hBusyBefore, hFreeAt⟩ := leasesBeforeSlot_conflict hDirValid hExtMk
  let sEnd : PoolSimState := { sAfterMk with files := (freePath, "") :: sAfterMk.files }
  have hPostFree : hasSimLockConflict sEnd freePath .exclusive = false :=
    (leasesBeforeSlot_conflict (s := sEnd) hDirValid hExtMk).2 hHeld0
  have hPost := postProbe_on_endState sAfterMk cfg.poolDir hDirValid hSymsMk hDirsLenMk freeIdx hPostFree
  rw [withSlot_simEx_firstScan_throws cfg policy s₀ sAfterMk hValid hMkRun hFilesMk hSymsMk hDirsLenMk hParMk
    freeIdx hFreeLt (fun k _ hlt => hBusyBefore k hlt (by rw [hMono0]; omega)) (hFreeAt hHeld0)]
  · rw [hPost]
    exact ⟨⟨rfl, hHeld0, rfl⟩, trivial⟩
  · rw [exceptT_bind_run]
    have hJoin : simFsEx.join = simFs.join := rfl
    rw [hJoin, simFsEx_sharedProbe_on_acquired sAfterMk cfg.poolDir hDirValid hSymsMk hDirsLenMk freeIdx]
    dsimp only
    simp only [beq_self_eq_true, ↓reduceIte]
    rfl

private theorem expectedWaitUpToChunks_succ (interval c m : Nat) :
    expectedWaitUpToChunks interval (c + 1) (m + 1) =
      sleepChunks (min interval (m + 1)) ++
        expectedWaitUpToChunks interval c ((m + 1) - min interval (m + 1)) := rfl

private theorem allPass_ite_assert (c : Prop) [Decidable c] (p : Prop) (rest : AllPassRun Unit) :
    ((if c then (NondetTest.assert p >>= fun _ => rest) else (NondetTest.assert True >>= fun _ => rest))
      (fun _ => True)) =
      ((c → p) ∧ (rest fun _ => True)) := by
  by_cases hc : c <;> simp [hc, allPass_assert]

private theorem pollWaitUpToM_expires_sim {α : Type}
    (cfg : PoolConfig) (hValid : validPoolConfig cfg = true) (dl : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α)) :
    ∀ (remMs fuel chunkFuel : Nat) (s : PoolSimState),
      remMs < fuel →
      remMs < chunkFuel →
      s.files = [] →
      s.symlinks = [] →
      s.heldLocks = [] →
      normSimPath cfg.poolDir ∈ s.dirs →
      (∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) →
      s.externalLeases = leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots →
      s.monoNanos + remMs * nanosecondsPerMs = dl →
      (pollWaitUpToM simFs simTime cfg dl action fuel).run s =
        (.ok .noSlot, { s with
          monoNanos := dl
          sleepLog := s.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs chunkFuel remMs).toArray }) := by
  intro remMs
  induction remMs using Nat.strongRecOn with
  | ind remMs ih =>
    intro fuel chunkFuel s hLtFuel hLtChunk hFiles hSyms hHeld hPar hDirsLen hExt hMono
    obtain ⟨_, hDirValid, _, hPollPos⟩ := validatePoolConfig_of_true cfg hValid
    cases fuel with
    | zero => omega
    | succ f =>
      cases chunkFuel with
      | zero => omega
      | succ cf =>
        have hBusyAll : ∀ j, 0 ≤ j → j < 0 + cfg.totalSlots →
            hasSimLockConflict s (slotLockPath simFs.join cfg.poolDir j) .exclusive = true := by
          intro j _ hj
          exact (leasesBeforeSlot_conflict hDirValid hExt).1 j (by omega) (by omega)
        have hScan := scanSlotsM_simFs_allBusy s cfg.poolDir hDirValid hFiles hSyms hDirsLen hPar action 0 cfg.totalSlots hBusyAll
        conv => lhs; unfold pollWaitUpToM
        rw [stateM_bind_run, hScan]
        dsimp only
        rw [stateM_bind_run]
        have hMonoNow : simTime.monoNanosNow.run s = (s.monoNanos, s) := rfl
        rw [hMonoNow]
        dsimp only
        cases remMs with
        | zero =>
          rw [Nat.zero_mul, Nat.add_zero] at hMono
          subst hMono
          simp only [Nat.le_refl, ↓reduceIte]
          unfold expectedWaitUpToChunks
          simp
          rfl
        | succ r =>
          have hNotGe : ¬ (s.monoNanos ≥ dl) := by
            have hPos : 0 < (r + 1) * nanosecondsPerMs := Nat.mul_pos (Nat.succ_pos r) (by decide)
            omega
          simp only [hNotGe, ↓reduceIte]
          have hRemEq : remainingWaitMs s.monoNanos dl = r + 1 := by
            dsimp [remainingWaitMs, nanosecondsPerMs] at hMono ⊢
            simp only [hNotGe, ↓reduceIte]
            omega
          let dur := Nat.min cfg.pollIntervalMs (r + 1)
          have hNextEq : nextSleepMs cfg.pollIntervalMs s.monoNanos dl = dur := by
            dsimp [nextSleepMs]
            rw [hRemEq]
          rw [hNextEq, stateM_bind_run, runSleepChunks_simTime_sleepChunks]
          dsimp only
          have hDurPos : 1 ≤ dur := Nat.le_min.mpr ⟨hPollPos, Nat.succ_pos r⟩
          have hDurLe : dur ≤ r + 1 := Nat.min_le_right _ _
          let rem' := (r + 1) - dur
          have hRemLt : rem' < r + 1 := by omega
          have hRemLtF : rem' < f := by omega
          have hRemLtCF : rem' < cf := by omega
          let s1 : PoolSimState :=
            { s with
              monoNanos := s.monoNanos + dur * nanosecondsPerMs
              sleepLog := s.sleepLog ++ (sleepChunks dur).toArray }
          have hMono1 : s1.monoNanos + rem' * nanosecondsPerMs = dl := by
            dsimp only [s1, rem']
            have : dur * nanosecondsPerMs + (r + 1 - dur) * nanosecondsPerMs = (r + 1) * nanosecondsPerMs := by
              rw [← Nat.add_mul, Nat.add_sub_cancel' hDurLe]
            omega
          rw [ih rem' hRemLt f cf s1 hRemLtF hRemLtCF hFiles hSyms hHeld hPar hDirsLen hExt hMono1]
          have hLogEq : s1.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs cf rem').toArray =
              s.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (cf + 1) (r + 1)).toArray := by
            dsimp only [s1]
            conv => rhs; rw [expectedWaitUpToChunks_succ]
            have hDurSym : min cfg.pollIntervalMs (r + 1) = dur := rfl
            rw [hDurSym]
            dsimp only [rem']
            apply Array.ext'
            simp
          rw [hLogEq]

private theorem expectedWaitUpToChunks_fuel_indep (pollIntervalMs : Nat) (hPollPos : 1 ≤ pollIntervalMs) :
    ∀ (m c1 c2 : Nat), m < c1 → m < c2 →
      expectedWaitUpToChunks pollIntervalMs c1 m = expectedWaitUpToChunks pollIntervalMs c2 m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro c1 c2 hc1 hc2
    cases c1 with
    | zero => omega
    | succ c1' =>
      cases c2 with
      | zero => omega
      | succ c2' =>
        cases m with
        | zero => rfl
        | succ m' =>
          rw [expectedWaitUpToChunks_succ, expectedWaitUpToChunks_succ]
          have hMinPos : 1 ≤ min pollIntervalMs (m' + 1) := Nat.le_min.mpr ⟨hPollPos, Nat.succ_pos m'⟩
          have hSubLt : m' + 1 - min pollIntervalMs (m' + 1) < m' + 1 := by omega
          rw [ih _ hSubLt c1' c2' (by omega) (by omega)]

private theorem pollWaitUpToM_reaches_dl {α : Type}
    (cfg : PoolConfig) (hValid : validPoolConfig cfg = true) (dl : Nat)
    (freeIdx lockedUntilNs : Nat) (hStrict : dl < lockedUntilNs)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α)) :
    ∀ (remMs fuel : Nat) (s : PoolSimState),
      remMs < fuel →
      s.files = [] →
      s.symlinks = [] →
      s.heldLocks = [] →
      normSimPath cfg.poolDir ∈ s.dirs →
      (∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) →
      s.externalLeases = leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx dl lockedUntilNs cfg.totalSlots →
      s.monoNanos + remMs * nanosecondsPerMs = dl →
      ∃ remFuel, remFuel ≥ 1 ∧
        (pollWaitUpToM simFs simTime cfg dl action fuel).run s =
          (pollWaitUpToM simFs simTime cfg dl action remFuel).run
            { s with
              monoNanos := dl
              sleepLog := s.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (remMs + 1) remMs).toArray } := by
  intro remMs
  induction remMs using Nat.strongRecOn with
  | ind remMs ih =>
    intro fuel s hLtFuel hFiles hSyms hHeld hPar hDirsLen hExt hMono
    obtain ⟨_, hDirValid, _, hPollPos⟩ := validatePoolConfig_of_true cfg hValid
    cases remMs with
    | zero =>
      rw [Nat.zero_mul, Nat.add_zero] at hMono
      subst hMono
      refine ⟨fuel, hLtFuel, ?_⟩
      simp [expectedWaitUpToChunks]
    | succ r =>
      cases fuel with
      | zero => omega
      | succ f =>
      have hMonoLt : s.monoNanos < dl := by
        have hPos : 0 < (r + 1) * nanosecondsPerMs := Nat.mul_pos (Nat.succ_pos r) (by decide)
        omega
      obtain ⟨hBusyLt, hBusyGe, _⟩ := leasesBeforeSlotUntil_conflict hDirValid hExt
      have hAllBusy : ∀ j, 0 ≤ j → j < 0 + cfg.totalSlots →
          hasSimLockConflict s (slotLockPath simFs.join cfg.poolDir j) .exclusive = true := by
        intro j _ hj
        by_cases hjlt : j < freeIdx
        · exact hBusyLt j (by omega) hjlt (Nat.lt_trans hMonoLt hStrict)
        · exact hBusyGe j (by omega) (Nat.not_lt.mp hjlt) hMonoLt
      have hScan := scanSlotsM_simFs_allBusy s cfg.poolDir hDirValid hFiles hSyms hDirsLen hPar action 0 cfg.totalSlots hAllBusy
      have hNotGe : ¬ (s.monoNanos ≥ dl) := Nat.not_le.mpr hMonoLt
      have hRemEq : remainingWaitMs s.monoNanos dl = r + 1 := by
        dsimp [remainingWaitMs, nanosecondsPerMs] at hMono ⊢
        simp only [hNotGe, ↓reduceIte]
        omega
      let dur := Nat.min cfg.pollIntervalMs (r + 1)
      have hNextEq : nextSleepMs cfg.pollIntervalMs s.monoNanos dl = dur := by
        dsimp [nextSleepMs]
        rw [hRemEq]
      let s1 : PoolSimState :=
        { s with
          monoNanos := s.monoNanos + dur * nanosecondsPerMs
          sleepLog := s.sleepLog ++ (sleepChunks dur).toArray }
      have hStep : (pollWaitUpToM simFs simTime cfg dl action (f + 1)).run s =
          (pollWaitUpToM simFs simTime cfg dl action f).run s1 := by
        conv => lhs; unfold pollWaitUpToM
        rw [stateM_bind_run, hScan]
        dsimp only
        rw [stateM_bind_run]
        have hMonoNow : simTime.monoNanosNow.run s = (s.monoNanos, s) := rfl
        rw [hMonoNow]
        dsimp only
        simp only [hNotGe, ↓reduceIte]
        rw [hNextEq, stateM_bind_run, runSleepChunks_simTime_sleepChunks]
      have hDurPos : 1 ≤ dur := Nat.le_min.mpr ⟨hPollPos, Nat.succ_pos r⟩
      have hDurLe : dur ≤ r + 1 := Nat.min_le_right _ _
      let rem' := (r + 1) - dur
      have hRemLt : rem' < r + 1 := by omega
      have hRemLtF : rem' < f := by omega
      have hMono1 : s1.monoNanos + rem' * nanosecondsPerMs = dl := by
        dsimp only [s1, rem']
        have : dur * nanosecondsPerMs + (r + 1 - dur) * nanosecondsPerMs = (r + 1) * nanosecondsPerMs := by
          rw [← Nat.add_mul, Nat.add_sub_cancel' hDurLe]
        omega
      obtain ⟨remFuel, hRemPos, hRec⟩ := ih rem' hRemLt f s1 hRemLtF hFiles hSyms hHeld hPar hDirsLen hExt hMono1
      have hChunkShift := expectedWaitUpToChunks_fuel_indep cfg.pollIntervalMs hPollPos
        rem' (rem' + 1) (r + 1) (Nat.lt_succ_self _) hRemLt
      have hLogEq : s1.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (rem' + 1) rem').toArray =
          s.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (r + 1 + 1) (r + 1)).toArray := by
        rw [hChunkShift]
        dsimp only [s1]
        conv => rhs; rw [expectedWaitUpToChunks_succ]
        have hDurSym : min cfg.pollIntervalMs (r + 1) = dur := rfl
        rw [hDurSym]
        dsimp only [rem']
        apply Array.ext'
        simp
      refine ⟨remFuel, hRemPos, ?_⟩
      rw [hStep, hRec, hLogEq]

private theorem withSlot_sim_waitUpTo_expires {α : Type}
    (cfg : PoolConfig) (timeoutMs : Nat) (s₀ sAfterMk : PoolSimState)
    (hValid : validPoolConfig cfg = true)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), sAfterMk))
    (hTimeoutMax : timeoutMs < maxForeverPolls)
    (hFiles : sAfterMk.files = []) (hSyms : sAfterMk.symlinks = [])
    (hHeld : sAfterMk.heldLocks = []) (hPar : normSimPath cfg.poolDir ∈ sAfterMk.dirs)
    (hDirsLen : ∀ d ∈ sAfterMk.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length)
    (hExt : sAfterMk.externalLeases =
      leasesBeforeSlot simFs.join cfg.poolDir (deadlineNanos sAfterMk.monoNanos timeoutMs + 1) cfg.totalSlots)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α)) :
    ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run s₀ =
      (.ok .noSlot,
       { sAfterMk with
         monoNanos := deadlineNanos sAfterMk.monoNanos timeoutMs
         sleepLog := sAfterMk.sleepLog ++ (expectedPollSleepLog cfg.pollIntervalMs timeoutMs).toArray }) := by
  obtain ⟨hVal, _, _, _⟩ := validatePoolConfig_of_true cfg hValid
  let dl := deadlineNanos sAfterMk.monoNanos timeoutMs
  have hMonoSum : sAfterMk.monoNanos + timeoutMs * nanosecondsPerMs = dl := rfl
  have hPoll := pollWaitUpToM_expires_sim cfg hValid dl action timeoutMs maxForeverPolls (timeoutMs + 1)
    sAfterMk hTimeoutMax (Nat.lt_succ_self _) hFiles hSyms hHeld hPar hDirsLen hExt hMonoSum
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]
  rw [hVal]; dsimp only
  rw [stateM_bind_run, hMk]; dsimp only
  rw [stateM_bind_run]
  have hMonoNow : simTime.monoNanosNow.run sAfterMk = (sAfterMk.monoNanos, sAfterMk) := rfl
  rw [hMonoNow]; dsimp only
  exact hPoll

private theorem withSlot_sim_waitUpTo_dl {α : Type}
    (cfg : PoolConfig) (freeIdx timeoutMs : Nat) (s₀ sAfterMk : PoolSimState)
    (hValid : validPoolConfig cfg = true)
    (hMk : (simFs.mkdir cfg.poolDir true true).run s₀ = (.ok (), sAfterMk))
    (hTimeoutMax : timeoutMs < maxForeverPolls)
    (hFiles : sAfterMk.files = []) (hSyms : sAfterMk.symlinks = [])
    (hHeld : sAfterMk.heldLocks = []) (hPar : normSimPath cfg.poolDir ∈ sAfterMk.dirs)
    (hDirsLen : ∀ d ∈ sAfterMk.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length)
    (hExt : sAfterMk.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx
        (deadlineNanos sAfterMk.monoNanos timeoutMs) (deadlineNanos sAfterMk.monoNanos timeoutMs + 1) cfg.totalSlots)
    (hFreeLt : freeIdx < cfg.totalSlots) (res : Except SlotPoolError α)
    (action : Nat → StateM PoolSimState (Except SlotPoolError α))
    (hAct : (action freeIdx).run { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := deadlineNanos sAfterMk.monoNanos timeoutMs
        sleepLog := sAfterMk.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (timeoutMs + 1) timeoutMs).toArray } =
      (res, { sAfterMk with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: sAfterMk.heldLocks
        monoNanos := deadlineNanos sAfterMk.monoNanos timeoutMs
        sleepLog := sAfterMk.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (timeoutMs + 1) timeoutMs).toArray })) :
    ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run s₀ =
      (outcomeOfLease freeIdx res,
       { sAfterMk with
         files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sAfterMk.files
         monoNanos := deadlineNanos sAfterMk.monoNanos timeoutMs
         sleepLog := sAfterMk.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (timeoutMs + 1) timeoutMs).toArray }) := by
  obtain ⟨hVal, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  let dl := deadlineNanos sAfterMk.monoNanos timeoutMs
  let sTarget : PoolSimState :=
    { sAfterMk with
      monoNanos := dl
      sleepLog := sAfterMk.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (timeoutMs + 1) timeoutMs).toArray }
  have hExtTarget : sTarget.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx
        (deadlineNanos sAfterMk.monoNanos timeoutMs) (deadlineNanos sAfterMk.monoNanos timeoutMs + 1) cfg.totalSlots := hExt
  obtain ⟨hBusyLt, _, hFreeAt⟩ := leasesBeforeSlotUntil_conflict hDirValid hExtTarget
  have hScan := scanSlotsM_simFs_acquires sTarget cfg.poolDir hDirValid hFiles hSyms hHeld hDirsLen hPar
    action 0 cfg.totalSlots freeIdx (Nat.zero_le _) (by omega)
    (fun k _ hlt => hBusyLt k (by omega) hlt (Nat.lt_succ_self dl))
    (hFreeAt hHeld hFreeLt (Nat.le_refl _)) res hAct
  dsimp only [mkApiM, Internal.mkApiM, withSlotM]
  rw [hVal]; dsimp only
  rw [stateM_bind_run, hMk]; dsimp only
  rw [stateM_bind_run]
  have hMonoNow : simTime.monoNanosNow.run sAfterMk = (sAfterMk.monoNanos, sAfterMk) := rfl
  rw [hMonoNow]; dsimp only
  have hMonoSum : sAfterMk.monoNanos + timeoutMs * nanosecondsPerMs = dl := rfl
  obtain ⟨remFuel, hRemPos, hReach⟩ :=
    pollWaitUpToM_reaches_dl cfg hValid dl freeIdx (dl + 1) (Nat.lt_succ_self dl)
      action timeoutMs maxForeverPolls sAfterMk hTimeoutMax
      hFiles hSyms hHeld hPar hDirsLen hExt hMonoSum
  rw [hReach]
  obtain ⟨f', hf'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hRemPos)
  rw [hf']
  conv => lhs; unfold pollWaitUpToM
  rw [stateM_bind_run, hScan]
  cases res <;> dsimp only [sTarget, dl, outcomeOfExcept, outcomeOfLease] <;> rfl

private theorem hasSimFile_with_expires (s : PoolSimState) (m : Nat) (l : Array UInt32) (p : String) :
    hasSimFile { s with monoNanos := m, sleepLog := l } p = hasSimFile s p := rfl

private theorem hasSimFile_of_files_nil {s : PoolSimState} (h : s.files = []) (p : String) :
    hasSimFile s p = false := by
  simp [hasSimFile, h]

private theorem poolSim_with_heldLocks (s : PoolSimState) (m : Nat) (l : Array UInt32) :
    ({ s with monoNanos := m, sleepLog := l } : PoolSimState).heldLocks = s.heldLocks := rfl

private theorem poolSim_with_monoNanos (s : PoolSimState) (m : Nat) (l : Array UInt32) :
    ({ s with monoNanos := m, sleepLog := l } : PoolSimState).monoNanos = m := rfl

private theorem poolSim_with_sleepLog (s : PoolSimState) (m : Nat) (l : Array UInt32) :
    ({ s with monoNanos := m, sleepLog := l } : PoolSimState).sleepLog = l := rfl

private theorem waitUpTo_expires_mk
    (cfg : PoolConfig) (timeoutMs startMono : Nat)
    (hValid : validPoolConfig cfg = true) :
    let dl := deadlineNanos startMono timeoutMs
    let sExpire : PoolSimState :=
      { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    ∃ sAfterMkE : PoolSimState,
      (simFs.mkdir cfg.poolDir true true).run sExpire = (.ok (), sAfterMkE) ∧
      sAfterMkE.files = [] ∧
      sAfterMkE.symlinks = [] ∧
      sAfterMkE.heldLocks = [] ∧
      normSimPath cfg.poolDir ∈ sAfterMkE.dirs ∧
      (∀ d ∈ sAfterMkE.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) ∧
      sAfterMkE.externalLeases =
        leasesBeforeSlot simFs.join cfg.poolDir (deadlineNanos sAfterMkE.monoNanos timeoutMs + 1) cfg.totalSlots ∧
      deadlineNanos sAfterMkE.monoNanos timeoutMs = dl ∧
      sAfterMkE.sleepLog = #[] := by
  obtain ⟨_, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  let dl := deadlineNanos startMono timeoutMs
  let sExpire : PoolSimState :=
    { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
      monoNanos := startMono }
  have hDirsLenE : ∀ d ∈ sExpire.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd; cases hd
  obtain ⟨sAfterMkE, hMkRunE, hFilesMkE, hSymsMkE, hHeldMkE, hExtMkE, _, hMonoMkE, hSleepMkE, hParMkE, hDirsLenMkE⟩ :=
    simMkdir_clean sExpire cfg.poolDir rfl rfl rfl hDirValid hDirsLenE
  have hHeldE : sAfterMkE.heldLocks = [] := hHeldMkE
  have hMonoE : sAfterMkE.monoNanos = startMono := hMonoMkE
  have hSleepE : sAfterMkE.sleepLog = #[] := hSleepMkE
  have hDlE : deadlineNanos sAfterMkE.monoNanos timeoutMs = dl := by
    dsimp [dl]; rw [hMonoE]
  have hExtE : sAfterMkE.externalLeases =
      leasesBeforeSlot simFs.join cfg.poolDir (deadlineNanos sAfterMkE.monoNanos timeoutMs + 1) cfg.totalSlots := by
    rw [hExtMkE, hDlE]
  exact ⟨sAfterMkE, hMkRunE, hFilesMkE, hSymsMkE, hHeldE, hParMkE, hDirsLenMkE, hExtE, hDlE, hSleepE⟩

private theorem waitUpTo_exp_1 (cfg : PoolConfig) (timeoutMs startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hTimeoutMax : timeoutMs < maxForeverPolls) :
    let dl := deadlineNanos startMono timeoutMs
    let sExpire : PoolSimState :=
      { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let expOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sExpire
    expOut.1 = .ok .noSlot := by
  dsimp only
  obtain ⟨sAfterMkE, hMk, hFiles, hSyms, hHeld, hPar, hDirsLen, hExt, _, _⟩ :=
    waitUpTo_expires_mk cfg timeoutMs startMono hValid
  rw [withSlot_sim_waitUpTo_expires cfg timeoutMs _ sAfterMkE hValid hMk hTimeoutMax
    hFiles hSyms hHeld hPar hDirsLen hExt]

private theorem waitUpTo_exp_2 (cfg : PoolConfig) (timeoutMs startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hTimeoutMax : timeoutMs < maxForeverPolls) :
    let dl := deadlineNanos startMono timeoutMs
    let sExpire : PoolSimState :=
      { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let expOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sExpire
    hasSimFile expOut.2 "ran-expired" = false := by
  dsimp only
  obtain ⟨sAfterMkE, hMk, hFiles, hSyms, hHeld, hPar, hDirsLen, hExt, _, _⟩ :=
    waitUpTo_expires_mk cfg timeoutMs startMono hValid
  rw [withSlot_sim_waitUpTo_expires cfg timeoutMs _ sAfterMkE hValid hMk hTimeoutMax
    hFiles hSyms hHeld hPar hDirsLen hExt, hasSimFile_with_expires]
  exact hasSimFile_of_files_nil hFiles "ran-expired"

private theorem waitUpTo_exp_3 (cfg : PoolConfig) (timeoutMs startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hTimeoutMax : timeoutMs < maxForeverPolls) :
    let dl := deadlineNanos startMono timeoutMs
    let sExpire : PoolSimState :=
      { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let expOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sExpire
    expOut.2.heldLocks = [] := by
  dsimp only
  obtain ⟨sAfterMkE, hMk, hFiles, hSyms, hHeld, hPar, hDirsLen, hExt, _, _⟩ :=
    waitUpTo_expires_mk cfg timeoutMs startMono hValid
  rw [withSlot_sim_waitUpTo_expires cfg timeoutMs _ sAfterMkE hValid hMk hTimeoutMax
    hFiles hSyms hHeld hPar hDirsLen hExt, poolSim_with_heldLocks]
  exact hHeld

private theorem waitUpTo_exp_4 (cfg : PoolConfig) (timeoutMs startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hTimeoutMax : timeoutMs < maxForeverPolls) :
    let dl := deadlineNanos startMono timeoutMs
    let sExpire : PoolSimState :=
      { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let expOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sExpire
    expOut.2.monoNanos = dl := by
  dsimp only
  obtain ⟨sAfterMkE, hMk, hFiles, hSyms, hHeld, hPar, hDirsLen, hExt, hDl, _⟩ :=
    waitUpTo_expires_mk cfg timeoutMs startMono hValid
  rw [withSlot_sim_waitUpTo_expires cfg timeoutMs _ sAfterMkE hValid hMk hTimeoutMax
    hFiles hSyms hHeld hPar hDirsLen hExt, poolSim_with_monoNanos]
  exact hDl

private theorem waitUpTo_exp_5 (cfg : PoolConfig) (timeoutMs startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hTimeoutMax : timeoutMs < maxForeverPolls) :
    let dl := deadlineNanos startMono timeoutMs
    let sExpire : PoolSimState :=
      { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let expOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sExpire
    expOut.2.sleepLog.toList = expectedPollSleepLog cfg.pollIntervalMs timeoutMs := by
  dsimp only
  obtain ⟨sAfterMkE, hMk, hFiles, hSyms, hHeld, hPar, hDirsLen, hExt, _, hSleep⟩ :=
    waitUpTo_expires_mk cfg timeoutMs startMono hValid
  rw [withSlot_sim_waitUpTo_expires cfg timeoutMs _ sAfterMkE hValid hMk hTimeoutMax
    hFiles hSyms hHeld hPar hDirsLen hExt, poolSim_with_sleepLog, Array.toList_append, hSleep]
  simp

private theorem waitUpTo_contendedPool_expires_ok
    (cfg : PoolConfig) (timeoutMs startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hTimeoutMax : timeoutMs < maxForeverPolls) :
    let dl := deadlineNanos startMono timeoutMs
    let sExpire : PoolSimState :=
      { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let expOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sExpire
    (expOut.1 = .ok .noSlot ∧ hasSimFile expOut.2 "ran-expired" = false ∧ expOut.2.heldLocks = []) ∧
      (expOut.2.monoNanos = dl ∧ expOut.2.sleepLog.toList = expectedPollSleepLog cfg.pollIntervalMs timeoutMs) :=
  ⟨⟨waitUpTo_exp_1 cfg timeoutMs startMono action hValid hTimeoutMax,
    waitUpTo_exp_2 cfg timeoutMs startMono action hValid hTimeoutMax,
    waitUpTo_exp_3 cfg timeoutMs startMono action hValid hTimeoutMax⟩,
   ⟨waitUpTo_exp_4 cfg timeoutMs startMono action hValid hTimeoutMax,
    waitUpTo_exp_5 cfg timeoutMs startMono action hValid hTimeoutMax⟩⟩

private theorem waitUpTo_contendedPool_rounds_ok
    (cfg : PoolConfig) (freeIdx rounds timeoutMs val startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hFreeLt : freeIdx < cfg.totalSlots)
    (hTimeoutMax : timeoutMs < maxForeverPolls)
    (hRBound : rounds * cfg.pollIntervalMs ≤ timeoutMs)
    (hAct : ∀ (s : PoolSimState), s.symlinks = [] →
      (∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) →
      (action freeIdx).run { s with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: s.heldLocks } =
      (.ok val, { s with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: s.heldLocks })) :
    let dl := deadlineNanos startMono timeoutMs
    let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
    let targetRelNs := startMono + rounds * cfg.pollIntervalMs * nanosecondsPerMs
    let sAcquire : PoolSimState :=
      { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let acqOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sAcquire
    acqOut.1 = .ok (.leased freeIdx val) ∧ acqOut.2.heldLocks = [] ∧
      acqOut.2.monoNanos = targetRelNs ∧ acqOut.2.monoNanos ≤ dl ∧
      (freeIdx + 1 ≥ cfg.totalSlots ∨ hasSimFile acqOut.2 nextPath = false) := by
  obtain ⟨_, hDirValid, _, hPollPos⟩ := validatePoolConfig_of_true cfg hValid
  let dl := deadlineNanos startMono timeoutMs
  let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
  let targetRelNs := startMono + rounds * cfg.pollIntervalMs * nanosecondsPerMs
  let sAcquire : PoolSimState :=
    { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs (dl + 1) cfg.totalSlots
      monoNanos := startMono }
  have hDirsLenA : ∀ d ∈ sAcquire.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd; cases hd
  obtain ⟨sAfterMkA, hMkRunA, hFilesMkA, hSymsMkA, hHeldMkA, hExtMkA, _, hMonoMkA, _, hParMkA, hDirsLenMkA⟩ :=
    simMkdir_clean sAcquire cfg.poolDir rfl rfl rfl hDirValid hDirsLenA
  have hHeldA : sAfterMkA.heldLocks = [] := hHeldMkA
  have hMonoA0 : sAfterMkA.monoNanos = startMono := hMonoMkA
  have hLeDl : targetRelNs ≤ dl := by
    dsimp only [targetRelNs, dl, deadlineNanos]
    have : rounds * cfg.pollIntervalMs * nanosecondsPerMs ≤ timeoutMs * nanosecondsPerMs :=
      Nat.mul_le_mul_right _ hRBound
    omega
  have hLeDlA : targetRelNs ≤ deadlineNanos sAfterMkA.monoNanos timeoutMs := by
    dsimp [dl] at hLeDl; rw [hMonoA0]; exact hLeDl
  have hLtLocked : targetRelNs ≤ dl + 1 := Nat.le_trans hLeDl (Nat.le_succ dl)
  have hLockedStrictA : targetRelNs < dl + 1 := Nat.lt_succ_of_le hLeDl
  have hRoundsLt : rounds < maxForeverPolls := by
    have h1 : rounds ≤ rounds * cfg.pollIntervalMs := Nat.le_mul_of_pos_right rounds hPollPos
    omega
  have hMonoSumA : sAfterMkA.monoNanos + rounds * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs := by
    rw [hMonoA0]
  let sTargetA : PoolSimState :=
    { sAfterMkA with
      monoNanos := targetRelNs
      sleepLog := sAfterMkA.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs rounds).toArray }
  let sEndA : PoolSimState := { sTargetA with files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sTargetA.files }
  have hNextNoA : hasSimFile sEndA nextPath = false := by
    dsimp only [sEndA, nextPath]
    rw [hasSimFile_cons_same_fields sTargetA _ _ hFilesMkA]
    exact nextPath_not_in_single_file cfg.poolDir hDirValid freeIdx
  dsimp only
  rw [withSlot_sim_waitUpTo_rounds cfg freeIdx rounds timeoutMs sAcquire sAfterMkA hValid hMkRunA
    hFilesMkA hSymsMkA hHeldA hParMkA hDirsLenMkA targetRelNs (dl + 1) hExtMkA
    hLeDlA hLtLocked hLockedStrictA hRoundsLt hMonoSumA hFreeLt (.ok val)
    action (hAct sTargetA hSymsMkA hDirsLenMkA)]
  dsimp only [outcomeOfLease]
  exact ⟨rfl, hHeldA, rfl, hLeDl, Or.inr hNextNoA⟩

private theorem waitUpTo_contendedPool_dl_ok
    (cfg : PoolConfig) (freeIdx timeoutMs val startMono : Nat)
    (action : Nat → StateM PoolSimState (Except SlotPoolError Nat))
    (hValid : validPoolConfig cfg = true) (hFreeLt : freeIdx < cfg.totalSlots)
    (hTimeoutMax : timeoutMs < maxForeverPolls)
    (hAct : ∀ (s : PoolSimState), s.symlinks = [] →
      (∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) →
      (action freeIdx).run { s with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: s.heldLocks } =
      (.ok val, { s with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: s.heldLocks })) :
    let dl := deadlineNanos startMono timeoutMs
    let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
    let sAcquireDl : PoolSimState :=
      { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx dl (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let acqDlOut := ((mkApiM simFs simTime).withSlot cfg (.waitUpTo timeoutMs) action).run sAcquireDl
    acqDlOut.1 = .ok (.leased freeIdx val) ∧ acqDlOut.2.heldLocks = [] ∧
      acqDlOut.2.monoNanos = dl ∧
      (freeIdx + 1 ≥ cfg.totalSlots ∨ hasSimFile acqDlOut.2 nextPath = false) := by
  obtain ⟨_, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  let dl := deadlineNanos startMono timeoutMs
  let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
  let sAcquireDl : PoolSimState :=
    { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx dl (dl + 1) cfg.totalSlots
      monoNanos := startMono }
  have hDirsLenD : ∀ d ∈ sAcquireDl.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd; cases hd
  obtain ⟨sAfterMkD, hMkRunD, hFilesMkD, hSymsMkD, hHeldMkD, hExtMkD, _, hMonoMkD, _, hParMkD, hDirsLenMkD⟩ :=
    simMkdir_clean sAcquireDl cfg.poolDir rfl rfl rfl hDirValid hDirsLenD
  have hHeldD : sAfterMkD.heldLocks = [] := hHeldMkD
  have hMonoD0 : sAfterMkD.monoNanos = startMono := hMonoMkD
  have hDlD : deadlineNanos sAfterMkD.monoNanos timeoutMs = dl := by
    dsimp [dl]; rw [hMonoD0]
  have hExtD : sAfterMkD.externalLeases =
      leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx
        (deadlineNanos sAfterMkD.monoNanos timeoutMs) (deadlineNanos sAfterMkD.monoNanos timeoutMs + 1)
        cfg.totalSlots := by
    rw [hExtMkD, hDlD]
  let sTargetD : PoolSimState :=
    { sAfterMkD with
      monoNanos := deadlineNanos sAfterMkD.monoNanos timeoutMs
      sleepLog := sAfterMkD.sleepLog ++ (expectedWaitUpToChunks cfg.pollIntervalMs (timeoutMs + 1) timeoutMs).toArray }
  let sEndD : PoolSimState := { sTargetD with files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sTargetD.files }
  have hNextNoD : hasSimFile sEndD nextPath = false := by
    dsimp only [sEndD, nextPath]
    rw [hasSimFile_cons_same_fields sTargetD _ _ hFilesMkD]
    exact nextPath_not_in_single_file cfg.poolDir hDirValid freeIdx
  dsimp only
  rw [withSlot_sim_waitUpTo_dl cfg freeIdx timeoutMs sAcquireDl sAfterMkD hValid hMkRunD hTimeoutMax
    hFilesMkD hSymsMkD hHeldD hParMkD hDirsLenMkD hExtD hFreeLt (.ok val)
    action (hAct sTargetD hSymsMkD hDirsLenMkD)]
  dsimp only [outcomeOfLease]
  exact ⟨rfl, hHeldD, hDlD, Or.inr hNextNoD⟩

/-- Specification 10 (`AllPass`): `WaitPolicy.waitUpTo` emits `expectedPollSleepLog`, expires cleanly at `deadlineNs`, and acquires the lowest freed slot on full-interval and clamped-remainder polls. -/
theorem proof_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline :
    AllPass (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline mkApiM) := by
  intro cfg freeIdx rounds timeoutMs val startMono ⟨hValid, hFreeLt, hTimeoutMax⟩
  obtain ⟨_, hDirValid, _, _⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline, AllPass]
  rw [allPass_assert, allPass_assert]
  have hExp := waitUpTo_contendedPool_expires_ok cfg timeoutMs startMono
    (fun _ => do
      let _ ← simFs.writeText "ran-expired" "bad"
      return (.ok val : Except SlotPoolError Nat))
    hValid hTimeoutMax
  refine ⟨hExp.1, hExp.2, ?_⟩
  let verifySlotAction : Nat → StateM PoolSimState (Except SlotPoolError Nat) := fun idx => do
    let p := slotLockPath simFs.join cfg.poolDir idx
    let sharedProbe ← simFs.tryWithFileLock p .shared false (pure (.ok ()))
    match sharedProbe with
    | .ok none =>
      if idx == freeIdx then
        return .ok val
      else
        return .error { kind := .ioError, message := "wrong slot after waitUpTo" }
    | _ =>
      return .error { kind := .ioError, message := "wrong lock mode after waitUpTo" }
  have hAct : ∀ (s : PoolSimState), s.symlinks = [] →
      (∀ d ∈ s.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length) →
      (verifySlotAction freeIdx).run
        { s with
          files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: s.files
          heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: s.heldLocks } =
      (.ok val, { s with
        files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: s.files
        heldLocks := (slotLockPath simFs.join cfg.poolDir freeIdx, .exclusive) :: s.heldLocks }) := by
    intro s hSyms hDirsLen
    dsimp only [verifySlotAction]
    rw [stateM_bind_run, simFs_sharedProbe_on_acquired s cfg.poolDir hDirValid hSyms hDirsLen freeIdx]
    dsimp only
    simp only [beq_self_eq_true, ↓reduceIte]
    rfl
  rw [allPass_ite_assert]
  refine ⟨?_, ?_⟩
  · intro ⟨_, hRBound⟩
    exact waitUpTo_contendedPool_rounds_ok cfg freeIdx rounds timeoutMs val startMono verifySlotAction hValid hFreeLt hTimeoutMax hRBound hAct
  · by_cases hT : 1 ≤ timeoutMs
    · simp only [hT, ↓reduceIte]
      rw [allPass_assert_end]
      exact ⟨waitUpTo_contendedPool_dl_ok cfg freeIdx timeoutMs val startMono verifySlotAction hValid hFreeLt hTimeoutMax hAct, trivial⟩
    · simp only [hT, ↓reduceIte]
      rw [allPass_assert_end]
      exact ⟨trivial, trivial⟩

/-- Specification 11 (`AllPass`): `WaitPolicy.waitForever` emits `repeatSleepChunks cfg.pollIntervalMs rounds`, acquires the lowest freed slot `.exclusive` without touching higher slots, and releases it on exit. -/
theorem proof_waitForever_contendedPool_pollsUntilSlotFree :
    AllPass (test_slotpool_waitForever_contendedPool_pollsUntilSlotFree mkApiM) := by
  intro cfg freeIdx rounds val startMono ⟨hValid, hFreeLt, _, hRoundsMax⟩
  obtain ⟨_, hDirValid, _, hPollPos⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_waitForever_contendedPool_pollsUntilSlotFree, AllPass]
  rw [allPass_assert, allPass_assert, allPass_assert_end]
  let targetRelNs := startMono + rounds * cfg.pollIntervalMs * nanosecondsPerMs
  let otherRelNs := targetRelNs + cfg.pollIntervalMs * nanosecondsPerMs
  let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
  let s₀ : PoolSimState :=
    { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs otherRelNs cfg.totalSlots
      monoNanos := startMono }
  have hDirsLen0 : ∀ d ∈ s₀.dirs, d.toList.length ≤ (normSimPath cfg.poolDir).toList.length := by
    intro d hd; cases hd
  obtain ⟨sAfterMk, hMkRun, hFilesMk, hSymsMk, hHeldMk, hExtMk, _, hMonoMk, hSleepMk, hParMk, hDirsLenMk⟩ :=
    simMkdir_clean s₀ cfg.poolDir rfl rfl rfl hDirValid hDirsLen0
  have hHeld0 : sAfterMk.heldLocks = [] := hHeldMk
  have hMono0 : sAfterMk.monoNanos = startMono := hMonoMk
  have hSleep0 : sAfterMk.sleepLog = #[] := hSleepMk
  have hLtLocked : targetRelNs ≤ otherRelNs := Nat.le_add_right _ _
  have hLockedStrict : targetRelNs < otherRelNs := by
    have hPos : 0 < cfg.pollIntervalMs * nanosecondsPerMs := Nat.mul_pos hPollPos (by decide)
    omega
  have hMonoSum : sAfterMk.monoNanos + rounds * cfg.pollIntervalMs * nanosecondsPerMs = targetRelNs := by
    rw [hMono0]
  let sTarget : PoolSimState :=
    { sAfterMk with
      monoNanos := targetRelNs
      sleepLog := sAfterMk.sleepLog ++ (repeatSleepChunks cfg.pollIntervalMs rounds).toArray }
  let sEnd : PoolSimState := { sTarget with files := (slotLockPath simFs.join cfg.poolDir freeIdx, "") :: sTarget.files }
  have hNextNo : hasSimFile sEnd nextPath = false := by
    dsimp only [sEnd, nextPath]
    rw [hasSimFile_cons_same_fields sTarget _ _ hFilesMk]
    exact nextPath_not_in_single_file cfg.poolDir hDirValid freeIdx
  have hSleepLog : sEnd.sleepLog.toList = repeatSleepChunks cfg.pollIntervalMs rounds := by
    dsimp only [sEnd, sTarget]
    rw [hSleep0]
    simp
  rw [withSlot_sim_waitForever_rounds cfg freeIdx rounds s₀ sAfterMk hValid hMkRun
    hFilesMk hSymsMk hHeld0 hParMk hDirsLenMk targetRelNs otherRelNs hExtMk
    hLtLocked hLockedStrict hRoundsMax hMonoSum hFreeLt (.ok val)]
  · dsimp only [outcomeOfLease]
    exact ⟨⟨rfl, hHeld0⟩, Or.inr hNextNo, ⟨rfl, hSleepLog⟩, trivial⟩
  · rw [stateM_bind_run, simFs_sharedProbe_on_acquired sTarget cfg.poolDir hDirValid hSymsMk hDirsLenMk freeIdx]
    dsimp only
    simp only [beq_self_eq_true, ↓reduceIte]
    rfl

/-- Witness 7 (`CanReach`): `test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock` is reachable for `mkApiM`. -/
theorem reach_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock :
    CanReach (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock mkApiM) := by
  refine ⟨{ poolDir := "pool/", totalSlots := 2, pollIntervalMs := 50 }, 1, 77, .waitUpTo 0, false, 123,
    by decide, ?_⟩
  dsimp only [test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock,
    CanReach, Bind.bind, NondetTest.assert]
  exact ⟨⟨rfl, by decide⟩, ⟨rfl, rfl⟩, Or.inl (by decide), ⟨rfl, rfl⟩, trivial⟩

/-- Witness 8 (`CanReach`): `test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan` is reachable for `mkApiM`. -/
theorem reach_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan :
    CanReach (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan mkApiM) := by
  refine ⟨{ poolDir := "pool", totalSlots := 2, pollIntervalMs := 2 }, 0, 1,
    { kind := .ioError, path := none, message := "" }, .noWait, by decide, ?_⟩
  dsimp only [test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan,
    CanReach, Bind.bind, NondetTest.assert]
  exact ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩

/-- Witness 9 (`CanReach`): `test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates` is reachable for `mkApiM`. -/
theorem reach_monadFinally_uncaughtException_releasesLockAndPropagates :
    CanReach (test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates mkApiM) := by
  refine ⟨{ poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 }, 0, .noWait, by decide, ?_⟩
  exact proof_monadFinally_uncaughtException_releasesLockAndPropagates
    { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 .noWait (by decide)

/-- Witness 10 (`CanReach`): `test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline` is reachable for `mkApiM`. -/
theorem reach_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline :
    CanReach (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline mkApiM) := by
  refine ⟨{ poolDir := "pool", totalSlots := 2, pollIntervalMs := 2 }, 0, 1, 3, 99, 0,
    by decide, ?_⟩
  dsimp only [test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline,
    CanReach, Bind.bind, NondetTest.assert]
  have hCond1 : 1 ≤ 1 ∧ 1 * 2 ≤ 3 := by decide
  have hCond2 : 1 ≤ 3 := by decide
  simp only [hCond1, hCond2, ↓reduceIte]
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨by decide, by decide⟩,
    ⟨rfl, rfl, rfl, by decide, Or.inr rfl⟩,
    ⟨rfl, rfl, rfl, Or.inr rfl⟩, trivial⟩

/-- Witness 11 (`CanReach`): `test_slotpool_waitForever_contendedPool_pollsUntilSlotFree` is reachable for `mkApiM`. -/
theorem reach_waitForever_contendedPool_pollsUntilSlotFree :
    CanReach (test_slotpool_waitForever_contendedPool_pollsUntilSlotFree mkApiM) := by
  refine ⟨{ poolDir := "pool", totalSlots := 3, pollIntervalMs := 50 }, 1, 3, 88, 500,
    by decide, ?_⟩
  dsimp [CanReach, Bind.bind, NondetTest.assert]
  exact ⟨⟨rfl, rfl⟩, Or.inr rfl, ⟨rfl, rfl⟩, trivial⟩

end LeanSwe.SlotPool.Proofs
