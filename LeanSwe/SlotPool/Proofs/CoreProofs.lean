import LeanSwe.SlotPool.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Impl
import LeanSwe.SlotPool.Interface
import LeanSwe.SlotPool.SpecTests
import LeanSwe.SlotPool.Proofs.SimLemmas

namespace LeanSwe.SlotPool.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Model
open LeanSwe.SlotPool.Internal (scanSlotsM pollWaitUpToM pollForeverM withSlotM)
open LeanSwe.SlotPool (mkApiM)

/-- Specification 1 (`AllPass`): `defaultTimingModelOps` satisfies exact deadline arithmetic, ceiling sub-ms rounding, clamping, and positive `UInt32` chunk sums. -/
theorem proof_model_timingAndSleepChunks :
    AllPass (test_slotpool_model_timingAndSleepChunks_exactAndChunked defaultTimingModelOps) := by
  intro startNs timeoutMs nowNs pollIntervalMs ms hPoll
  dsimp only [test_slotpool_model_timingAndSleepChunks_exactAndChunked, defaultTimingModelOps, AllPass]
  rw [allPass_assert]
  refine ⟨rfl, ?_⟩
  have hFuel : ms ≤ (ms / maxSleepChunkMs + 1) * maxSleepChunkMs := by
    dsimp [maxSleepChunkMs]
    omega
  obtain ⟨hAll, hSum⟩ := sleepChunksAux_spec (ms / maxSleepChunkMs + 1) ms hFuel
  by_cases hge : nowNs ≥ deadlineNanos startNs timeoutMs
  · simp only [hge, ↓reduceIte]
    rw [allPass_assert, allPass_assert, allPass_assert_end]
    dsimp only [remainingWaitMs, nextSleepMs]
    simp only [hge, ↓reduceIte]
    exact ⟨⟨trivial, Nat.min_zero _⟩, hAll, hSum, trivial⟩
  · simp only [hge, ↓reduceIte]
    rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
    dsimp only [remainingWaitMs, nextSleepMs, deadlineNanos, nanosecondsPerMs] at hge ⊢
    simp only [hge, ↓reduceIte]
    let deltaNs := startNs + timeoutMs * 1000000 - nowNs
    let rem := (deltaNs + 999999) / 1000000
    have h1 : 1 ≤ rem := by omega
    have h2 : (rem - 1) * 1000000 < deltaNs := by omega
    have h3 : deltaNs ≤ rem * 1000000 := by omega
    have hMinPos : 1 ≤ pollIntervalMs.min rem := Nat.le_min.mpr ⟨hPoll, h1⟩
    exact ⟨⟨h1, h2, h3⟩, ⟨hMinPos, Nat.min_le_left _ _, Nat.min_le_right _ _, trivial⟩, hAll, hSum, trivial⟩

/-- Witness 1 (`CanReach`): `test_slotpool_model_timingAndSleepChunks_exactAndChunked` is reachable for `defaultTimingModelOps`. -/
theorem reach_model_timingAndSleepChunks :
    CanReach (test_slotpool_model_timingAndSleepChunks_exactAndChunked defaultTimingModelOps) := by
  refine ⟨0, 20, 500000, 50, 4294967296, by decide, ?_⟩
  have hChunks := sleepChunksAux_spec (4294967296 / maxSleepChunkMs + 1) 4294967296 (by decide)
  dsimp [CanReach, Bind.bind, NondetTest.assert, defaultTimingModelOps, deadlineNanos,
    remainingWaitMs, nextSleepMs, nanosecondsPerMs, sleepChunks]
  exact ⟨rfl, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, rfl⟩,
    hChunks.1, hChunks.2, trivial⟩

/-- Specification 2 (`AllPass`): invalid `PoolConfig` values are rejected with `.invalidInput` before any filesystem, clock, or callback effect. -/
theorem proof_validation_invalidConfig_rejectedBeforeEffects
    {S : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) :
    AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects mkApiM fs time) := by
  intro s₀ cfg policy markerPath hInvalid
  obtain ⟨e, hVal, hKind, hPath, hMsg⟩ := validatePoolConfig_of_false cfg hInvalid
  dsimp only [test_slotpool_validation_invalidConfig_rejectedBeforeEffects, AllPass]
  rw [allPass_assert_end]
  have hRun : (((mkApiM fs time).withSlot cfg policy fun _ => do
      let _ ← fs.writeText markerPath "ran"
      return (.ok 1 : Except SlotPoolError Nat)).run s₀) = (.error e, s₀) := by
    dsimp only [mkApiM, Internal.mkApiM, withSlotM, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
    rw [hVal]
    rfl
  rw [hRun]
  exact ⟨⟨⟨e, rfl, hKind, hPath, hMsg⟩, rfl⟩, trivial⟩

/-- Witness 2 (`CanReach`): `test_slotpool_validation_invalidConfig_rejectedBeforeEffects` is reachable for `mkApiM`. -/
theorem reach_validation_invalidConfig_rejectedBeforeEffects :
    CanReach (test_slotpool_validation_invalidConfig_rejectedBeforeEffects mkApiM simFs simTime) :=
  ⟨{}, { poolDir := "", totalSlots := 0, pollIntervalMs := 50 }, .noWait, "marker.txt", by decide,
    proof_validation_invalidConfig_rejectedBeforeEffects simFs simTime
      {} { poolDir := "", totalSlots := 0, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)⟩

/-- Specification 3 (`AllPass`): `fs.mkdir` failures map to `SlotPoolError` with preserved `path` and non-empty message before polling or callbacks. -/
theorem proof_mkdir_fsError_propagatedBeforePolling
    {S : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) :
    AllPass (test_slotpool_mkdir_fsError_propagatedBeforePolling mkApiM fs time) := by
  intro s₀ cfg policy markerPath hValid
  obtain ⟨hVal, _, _, _⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_mkdir_fsError_propagatedBeforePolling, AllPass]
  cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with
  | mk mkRes sAfterMk =>
    dsimp only
    cases mkRes with
    | ok _ =>
      intro hFalse
      cases hFalse
    | error fe =>
      dsimp only
      rw [allPass_assert_end]
      have hRun : (((mkApiM fs time).withSlot cfg policy fun _ => do
          let _ ← fs.writeText markerPath "ran"
          return (.ok 1 : Except SlotPoolError Nat)).run s₀) = (.error (mapFsError fe), sAfterMk) := by
        dsimp only [mkApiM, Internal.mkApiM, withSlotM]
        rw [hVal]
        dsimp only
        rw [stateM_bind_run, hMk]
        rfl
      rw [hRun]
      exact ⟨⟨⟨mapFsError fe, rfl, rfl, rfl, mapFsError_nonEmpty fe⟩, rfl⟩, trivial⟩

/-- Witness 3 (`CanReach`): `test_slotpool_mkdir_fsError_propagatedBeforePolling` is reachable for `mkApiM`. -/
theorem reach_mkdir_fsError_propagatedBeforePolling :
    CanReach (test_slotpool_mkdir_fsError_propagatedBeforePolling mkApiM simFs simTime) := by
  refine ⟨{ files := [("pool", "blocking")] }, { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 },
    .noWait, "marker.txt", by decide, ?_⟩
  exact proof_mkdir_fsError_propagatedBeforePolling simFs simTime
    { files := [("pool", "blocking")] } { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 }
    .noWait "marker.txt" (by decide)

private theorem scanSlotsM_allNone {S α : Type} (fs : FsApiM (StateM S))
    (poolDir : String) (nextIdx rem : Nat) (action : Nat → StateM S (Except SlotPoolError α)) (s : S)
    (hNone : ∀ idx, (fs.tryWithFileLock (slotLockPath fs.join poolDir idx) .exclusive true
      (do return .ok (← action idx))).run s = (.ok none, s)) :
    (scanSlotsM fs poolDir nextIdx rem action).run s = (.allBusy, s) := by
  induction rem generalizing nextIdx with
  | zero => rfl
  | succ r ih =>
    unfold scanSlotsM
    rw [stateM_bind_run, hNone nextIdx]
    exact ih (nextIdx + 1)

private def mkFsAllBusyLog {S : Type} (fs : FsApiM (StateM S)) : FsApiM (StateM (S × List String)) :=
  { liftFsFirst (Aux := List String) fs with
    tryWithFileLock := fun p mode createIfMissing _ => do
      if mode == .exclusive && createIfMissing then
        modify fun (st, acc) => (st, acc ++ [p])
        return .ok none
      else
        return .error { kind := .invalidInput, path := some p, message := "unexpected lock mode or create flag" } }

private theorem scanSlotsM_logPaths {S α : Type} (fs : FsApiM (StateM S))
    (poolDir : String) (nextIdx rem : Nat)
    (action : Nat → StateM (S × List String) (Except SlotPoolError α))
    (st : S) (acc : List String) :
    (scanSlotsM (mkFsAllBusyLog fs) poolDir nextIdx rem action).run (st, acc) =
      (.allBusy, (st, acc ++ expectedSlotPaths fs.join poolDir nextIdx rem)) := by
  induction rem generalizing nextIdx acc with
  | zero =>
    simp [scanSlotsM, expectedSlotPaths]
    rfl
  | succ r ih =>
    unfold scanSlotsM expectedSlotPaths
    rw [stateM_bind_run]
    have hStep : ((mkFsAllBusyLog fs).tryWithFileLock
        (slotLockPath (mkFsAllBusyLog fs).join poolDir nextIdx) .exclusive true
        (do return .ok (← action nextIdx))).run (st, acc) =
        (.ok none, (st, acc ++ [slotLockPath fs.join poolDir nextIdx])) := rfl
    rw [hStep]
    dsimp only
    rw [ih (nextIdx + 1) (acc ++ [slotLockPath fs.join poolDir nextIdx])]
    simp [List.append_assoc]

/-- Specification 4 (`AllPass`): under `WaitPolicy.noWait`, a saturated pool probes every slot once in ascending order and returns `.ok .noSlot` without sleeping or running `action`. -/
theorem proof_noWait_allBusy_returnsNoSlotWithoutSleepOrAction
    {S : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) :
    AllPass (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction mkApiM fs time) := by
  intro s₀ cfg markerPath hValid hMkOk hMarker
  obtain ⟨hVal, _, _, _⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction, AllPass]
  rw [allPass_assert_end]
  let fsLift := liftFsFirst (Aux := List String) fs
  cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with
  | mk mkRes sAfterMk =>
    have hResOk : mkRes = .ok () := by rw [hMk] at hMkOk; exact hMkOk
    subst hResOk
    have hMarker' : ((fs.lstat markerPath).run sAfterMk).1.isOk = false := by
      rw [hMk] at hMarker; exact hMarker
    have hMkLift : ((mkFsAllBusyLog fs).mkdir cfg.poolDir true true).run (s₀, []) = (.ok (), (sAfterMk, [])) := by
      change (let (a, s') := (fs.mkdir cfg.poolDir true true).run s₀; (a, (s', []))) = _
      rw [hMk]
    have hRun : (((mkApiM (mkFsAllBusyLog fs) (liftTimeFirst time)).withSlot cfg .noWait fun _ => do
        let _ ← fsLift.writeText markerPath "ran"
        return (.ok 1 : Except SlotPoolError Nat)).run (s₀, [])) =
        (.ok .noSlot, (sAfterMk, expectedSlotPaths fs.join cfg.poolDir 0 cfg.totalSlots)) := by
      dsimp only [mkApiM, Internal.mkApiM, withSlotM]
      rw [hVal]; dsimp only
      rw [stateM_bind_run, hMkLift]; dsimp only
      rw [stateM_bind_run]
      have hScan := scanSlotsM_logPaths fs cfg.poolDir 0 cfg.totalSlots
        (fun _ => do let _ ← fsLift.writeText markerPath "ran"; return (.ok 1 : Except SlotPoolError Nat))
        sAfterMk []
      rw [List.nil_append] at hScan
      rw [hScan]; rfl
    show (let out := ((mkApiM (mkFsAllBusyLog fs) (liftTimeFirst time)).withSlot cfg .noWait fun _ => do
        let _ ← fsLift.writeText markerPath "ran"
        return (.ok 1 : Except SlotPoolError Nat)).run (s₀, [])
      (out.1 = .ok .noSlot ∧
        out.2 = ((Except.ok (), sAfterMk).2, expectedSlotPaths fs.join cfg.poolDir 0 cfg.totalSlots) ∧
        ((fs.lstat markerPath).run out.2.1).1.isOk = false) ∧ True)
    rw [hRun]
    exact ⟨⟨rfl, rfl, hMarker'⟩, trivial⟩

/-- Witness 4 (`CanReach`): `test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction` is reachable for `mkApiM`. -/
theorem reach_noWait_allBusy_returnsNoSlotWithoutSleepOrAction :
    CanReach (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction mkApiM simFs simTime) :=
  ⟨{}, { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 }, "marker.txt",
    by decide, rfl, rfl,
    proof_noWait_allBusy_returnsNoSlotWithoutSleepOrAction simFs simTime
      {} { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 } "marker.txt"
      (by decide) rfl rfl⟩

private def mkFsFailLock0 {S : Type} (fs : FsApiM (StateM S)) (cfg : PoolConfig)
    (errIdx : Nat) (lockFsErr : FsError) : FsApiM (StateM (S × Nat)) :=
  { liftFsFirst (Aux := Nat) fs with
    tryWithFileLock := fun p mode createIfMissing act => do
      let (st, callIdx) ← get
      let expectedPath := slotLockPath fs.join cfg.poolDir callIdx
      if p == expectedPath && mode == .exclusive && createIfMissing then
        set (st, callIdx + 1)
        if callIdx < errIdx then
          return .ok none
        else if callIdx == errIdx then
          return .error lockFsErr
        else
          let r ← act
          return r.map some
      else
        return .error { kind := .invalidInput, path := some p, message := "unexpected lock probe" } }

private theorem mkFsFailLock0_step {S β : Type} (fs : FsApiM (StateM S))
    (cfg : PoolConfig) (errIdx : Nat) (lockFsErr : FsError)
    (st : S) (callIdx : Nat) (act : StateM (S × Nat) (Except FsError β)) :
    ((mkFsFailLock0 fs cfg errIdx lockFsErr).tryWithFileLock
      (slotLockPath (mkFsFailLock0 fs cfg errIdx lockFsErr).join cfg.poolDir callIdx) .exclusive true act).run
      (st, callIdx) =
      if callIdx < errIdx then
        (.ok none, (st, callIdx + 1))
      else if callIdx == errIdx then
        (.error lockFsErr, (st, callIdx + 1))
      else
        ((do let r ← act; return r.map some : StateM (S × Nat) _).run (st, callIdx + 1)) := by
  dsimp only [mkFsFailLock0, liftFsFirst]
  show StateT.run
    (if (slotLockPath fs.join cfg.poolDir callIdx == slotLockPath fs.join cfg.poolDir callIdx &&
        (LockMode.exclusive == LockMode.exclusive) && true) = true then do
      set (st, callIdx + 1)
      if callIdx < errIdx then
        return .ok none
      else if callIdx == errIdx then
        return .error lockFsErr
      else
        let r ← act
        return r.map some
    else
      return .error { kind := .invalidInput, path := some (slotLockPath fs.join cfg.poolDir callIdx), message := "unexpected lock probe" })
    (st, callIdx) = _
  have hEx : (LockMode.exclusive == LockMode.exclusive) = true := rfl
  simp only [beq_self_eq_true, hEx, Bool.and_self, ↓reduceIte]
  by_cases h1 : callIdx < errIdx
  · simp [h1]; rfl
  · by_cases h2 : (callIdx == errIdx) = true
    · simp [h1, h2]; rfl
    · simp [h1, h2]

private theorem scanSlotsM_failLock0 {S α : Type} (fs : FsApiM (StateM S))
    (cfg : PoolConfig) (errIdx : Nat) (lockFsErr : FsError)
    (st : S) (nextIdx rem : Nat)
    (act : Nat → StateM (S × Nat) (Except SlotPoolError α))
    (hLe : nextIdx ≤ errIdx) (hLt : errIdx < nextIdx + rem) :
    (scanSlotsM (mkFsFailLock0 fs cfg errIdx lockFsErr) cfg.poolDir nextIdx rem act).run (st, nextIdx) =
      (.err (mapFsError lockFsErr), (st, errIdx + 1)) := by
  induction rem generalizing nextIdx with
  | zero => omega
  | succ r ih =>
    unfold scanSlotsM
    rw [stateM_bind_run, mkFsFailLock0_step]
    by_cases hlt : nextIdx < errIdx
    · simp only [hlt, ↓reduceIte]
      exact ih (nextIdx + 1) (by omega) (by omega)
    · have hEq : nextIdx = errIdx := by omega
      subst hEq
      simp only [Nat.lt_irrefl, ↓reduceIte, beq_self_eq_true]
      rfl

private def mkFsFailLock1 {S : Type} (fs : FsApiM (StateM S)) (cfg : PoolConfig)
    (errIdx : Nat) (lockFsErr : FsError) : FsApiM (StateM (S × Nat)) :=
  let targetCall := cfg.totalSlots + errIdx
  { liftFsFirst (Aux := Nat) fs with
    tryWithFileLock := fun p mode createIfMissing act => do
      let (st, callIdx) ← get
      let slotIdx := if callIdx < cfg.totalSlots then callIdx else callIdx - cfg.totalSlots
      let expectedPath := slotLockPath fs.join cfg.poolDir slotIdx
      if p == expectedPath && mode == .exclusive && createIfMissing then
        set (st, callIdx + 1)
        if callIdx < targetCall then
          return .ok none
        else if callIdx == targetCall then
          return .error lockFsErr
        else
          let r ← act
          return r.map some
      else
        return .error { kind := .invalidInput, path := some p, message := "unexpected retry lock probe" } }

private theorem mkFsFailLock1_step {S β : Type} (fs : FsApiM (StateM S))
    (cfg : PoolConfig) (errIdx : Nat) (lockFsErr : FsError)
    (st : S) (callIdx nextIdx : Nat) (act : StateM (S × Nat) (Except FsError β))
    (hSlot : (if callIdx < cfg.totalSlots then callIdx else callIdx - cfg.totalSlots) = nextIdx) :
    ((mkFsFailLock1 fs cfg errIdx lockFsErr).tryWithFileLock
      (slotLockPath (mkFsFailLock1 fs cfg errIdx lockFsErr).join cfg.poolDir nextIdx) .exclusive true act).run
      (st, callIdx) =
      if callIdx < cfg.totalSlots + errIdx then
        (.ok none, (st, callIdx + 1))
      else if callIdx == cfg.totalSlots + errIdx then
        (.error lockFsErr, (st, callIdx + 1))
      else
        ((do let r ← act; return r.map some : StateM (S × Nat) _).run (st, callIdx + 1)) := by
  dsimp only [mkFsFailLock1, liftFsFirst]
  show StateT.run
    (let slotIdx := if callIdx < cfg.totalSlots then callIdx else callIdx - cfg.totalSlots
     if (slotLockPath fs.join cfg.poolDir nextIdx == slotLockPath fs.join cfg.poolDir slotIdx &&
        (LockMode.exclusive == LockMode.exclusive) && true) = true then do
      set (st, callIdx + 1)
      if callIdx < cfg.totalSlots + errIdx then
        return .ok none
      else if callIdx == cfg.totalSlots + errIdx then
        return .error lockFsErr
      else
        let r ← act
        return r.map some
    else
      return .error { kind := .invalidInput, path := some (slotLockPath fs.join cfg.poolDir nextIdx), message := "unexpected retry lock probe" })
    (st, callIdx) = _
  have hEx : (LockMode.exclusive == LockMode.exclusive) = true := rfl
  simp only [hSlot, beq_self_eq_true, hEx, Bool.and_self, ↓reduceIte]
  by_cases h1 : callIdx < cfg.totalSlots + errIdx
  · simp [h1]; rfl
  · by_cases h2 : (callIdx == cfg.totalSlots + errIdx) = true
    · simp [h1, h2]; rfl
    · simp [h1, h2]

private theorem scanSlotsM_failLock1_poll0 {S α : Type} (fs : FsApiM (StateM S))
    (cfg : PoolConfig) (errIdx : Nat) (lockFsErr : FsError)
    (st : S) (nextIdx rem : Nat)
    (act : Nat → StateM (S × Nat) (Except SlotPoolError α))
    (hTotal : nextIdx + rem = cfg.totalSlots) :
    (scanSlotsM (mkFsFailLock1 fs cfg errIdx lockFsErr) cfg.poolDir nextIdx rem act).run (st, nextIdx) =
      (.allBusy, (st, cfg.totalSlots)) := by
  induction rem generalizing nextIdx with
  | zero =>
    have hEq : nextIdx = cfg.totalSlots := by omega
    subst hEq
    rfl
  | succ r ih =>
    unfold scanSlotsM
    rw [stateM_bind_run]
    have hLt : nextIdx < cfg.totalSlots := by omega
    have hSlot : (if nextIdx < cfg.totalSlots then nextIdx else nextIdx - cfg.totalSlots) = nextIdx := by
      simp [hLt]
    have hLtTgt : nextIdx < cfg.totalSlots + errIdx := by omega
    rw [mkFsFailLock1_step fs cfg errIdx lockFsErr st nextIdx nextIdx _ hSlot]
    simp only [hLtTgt, ↓reduceIte]
    exact ih (nextIdx + 1) (by omega)

private theorem scanSlotsM_failLock1_poll1 {S α : Type} (fs : FsApiM (StateM S))
    (cfg : PoolConfig) (errIdx : Nat) (lockFsErr : FsError)
    (st : S) (nextIdx rem : Nat)
    (act : Nat → StateM (S × Nat) (Except SlotPoolError α))
    (hLe : nextIdx ≤ errIdx) (hLt : errIdx < nextIdx + rem) :
    (scanSlotsM (mkFsFailLock1 fs cfg errIdx lockFsErr) cfg.poolDir nextIdx rem act).run
      (st, cfg.totalSlots + nextIdx) =
      (.err (mapFsError lockFsErr), (st, cfg.totalSlots + errIdx + 1)) := by
  induction rem generalizing nextIdx with
  | zero => omega
  | succ r ih =>
    unfold scanSlotsM
    rw [stateM_bind_run]
    have hNotLt : ¬ (cfg.totalSlots + nextIdx < cfg.totalSlots) := by omega
    have hSlot : (if cfg.totalSlots + nextIdx < cfg.totalSlots then cfg.totalSlots + nextIdx else cfg.totalSlots + nextIdx - cfg.totalSlots) = nextIdx := by
      simp [hNotLt]
    rw [mkFsFailLock1_step fs cfg errIdx lockFsErr st (cfg.totalSlots + nextIdx) nextIdx _ hSlot]
    by_cases hlt : nextIdx < errIdx
    · have hLtTgt : cfg.totalSlots + nextIdx < cfg.totalSlots + errIdx := by omega
      simp only [hLtTgt, ↓reduceIte, Nat.add_assoc]
      exact ih (nextIdx + 1) (by omega) (by omega)
    · have hEq : nextIdx = errIdx := by omega
      subst hEq
      simp only [Nat.lt_irrefl, ↓reduceIte, beq_self_eq_true]
      rfl

/-- Specification 5 (`AllPass`): `tryWithFileLock` errors fail fast without scanning higher slots or running `action` across initial and retry scans. -/
theorem proof_tryLock_fsError_propagatedWithoutRunningAction
    {S : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) :
    AllPass (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction mkApiM fs time) := by
  intro s₀ cfg errIdx retryPoll policy lockFsErr markerPath ⟨hValid, hErrLt⟩ hMkOk hMonoPure hMarker
  obtain ⟨hVal, _, _, hPoll⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_tryLock_fsError_propagatedWithoutRunningAction, AllPass]
  cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with
  | mk mkRes sAfterMk =>
    have hResOk : mkRes = .ok () := by rw [hMk] at hMkOk; exact hMkOk
    subst hResOk
    have hMono' : (time.monoNanosNow.run sAfterMk).2 = sAfterMk := by
      rw [hMk] at hMonoPure; exact hMonoPure
    have hMarker' : ((fs.lstat markerPath).run sAfterMk).1.isOk = false := by
      rw [hMk] at hMarker; exact hMarker
    let fsLift := liftFsFirst (Aux := Nat) fs
    let timeLift := liftTimeFirst (Aux := Nat) time
    cases retryPoll with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      rw [allPass_assert_end]
      have hMkLift : ((mkFsFailLock0 fs cfg errIdx lockFsErr).mkdir cfg.poolDir true true).run (s₀, 0) =
          (.ok (), (sAfterMk, 0)) := by
        change (let (a, s') := (fs.mkdir cfg.poolDir true true).run s₀; (a, (s', 0))) = _
        rw [hMk]
      have hScan := fun (act : Nat → StateM (S × Nat) (Except SlotPoolError Nat)) =>
        scanSlotsM_failLock0 fs cfg errIdx lockFsErr sAfterMk 0 cfg.totalSlots act (Nat.zero_le _) (by omega)
      have hRun : (((mkApiM (mkFsFailLock0 fs cfg errIdx lockFsErr) timeLift).withSlot cfg policy fun _ => do
          let _ ← fsLift.writeText markerPath "ran"
          return (.ok 1 : Except SlotPoolError Nat)).run (s₀, 0)) =
          (.error (mapFsError lockFsErr), (sAfterMk, errIdx + 1)) := by
        dsimp only [mkApiM, Internal.mkApiM, withSlotM]
        rw [hVal]; dsimp only
        rw [stateM_bind_run, hMkLift]; dsimp only
        cases policy with
        | noWait => rw [stateM_bind_run, hScan]; rfl
        | waitUpTo timeoutMs =>
          rw [stateM_bind_run]
          cases hMono : time.monoNanosNow.run sAfterMk with
          | mk startNs sMono =>
            have hsEq : sMono = sAfterMk := by rw [hMono] at hMono'; exact hMono'
            subst sMono
            have hML : timeLift.monoNanosNow.run (sAfterMk, 0) = (startNs, (sAfterMk, 0)) := by
              change (let (a, s') := time.monoNanosNow.run sAfterMk; (a, (s', 0))) = _; rw [hMono]
            rw [hML]; dsimp only
            have hF : maxForeverPolls = (2 ^ 64 - 1) + 1 := by decide
            rw [hF]; unfold pollWaitUpToM
            rw [stateM_bind_run, hScan]; rfl
        | waitForever =>
          have hF : maxForeverPolls = (2 ^ 64 - 1) + 1 := by decide
          rw [hF]; unfold pollForeverM
          rw [stateM_bind_run, hScan]; rfl
      show (let out := ((mkApiM (mkFsFailLock0 fs cfg errIdx lockFsErr) timeLift).withSlot cfg policy fun _ => do
          let _ ← fsLift.writeText markerPath "ran"
          return (.ok 1 : Except SlotPoolError Nat)).run (s₀, 0)
        ((∃ e, out.1 = .error e ∧ e.kind = mapFsErrorKind lockFsErr.kind ∧ e.path = lockFsErr.path ∧ e.message ≠ "") ∧
          out.2 = (sAfterMk, errIdx + 1) ∧
          ((fs.lstat markerPath).run out.2.1).1.isOk = false) ∧ True)
      rw [hRun]
      exact ⟨⟨⟨mapFsError lockFsErr, rfl, rfl, rfl, mapFsError_nonEmpty lockFsErr⟩, rfl, hMarker'⟩, trivial⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, NondetTest.assume]
      intro hMarkerAfter
      rw [allPass_assert_end]
      let targetCall := cfg.totalSlots + errIdx
      have hMkLift : ((mkFsFailLock1 fs cfg errIdx lockFsErr).mkdir cfg.poolDir true true).run (s₀, 0) =
          (.ok (), (sAfterMk, 0)) := by
        change (let (a, s') := (fs.mkdir cfg.poolDir true true).run s₀; (a, (s', 0))) = _
        rw [hMk]
      have hPoll0 := fun (act : Nat → StateM (S × Nat) (Except SlotPoolError Nat)) =>
        scanSlotsM_failLock1_poll0 fs cfg errIdx lockFsErr sAfterMk 0 cfg.totalSlots act (Nat.zero_add _)
      have hPoll1 : ∀ st (act : Nat → StateM (S × Nat) (Except SlotPoolError Nat)),
          (scanSlotsM (mkFsFailLock1 fs cfg errIdx lockFsErr) cfg.poolDir 0 cfg.totalSlots act).run
            (st, cfg.totalSlots) = (.err (mapFsError lockFsErr), (st, cfg.totalSlots + errIdx + 1)) := by
        intro st act
        have h := scanSlotsM_failLock1_poll1 fs cfg errIdx lockFsErr st 0 cfg.totalSlots act (Nat.zero_le _) (by omega)
        rw [Nat.add_zero] at h
        exact h
      cases hSleep : (runSleepChunks time (sleepChunks cfg.pollIntervalMs)).run sAfterMk with
      | mk _ sAfterSleep =>
        have hMarkerAfter' : ((fs.lstat markerPath).run sAfterSleep).1.isOk = false := by
          rw [hSleep] at hMarkerAfter; exact hMarkerAfter
        dsimp only
        have hSleepLift : (runSleepChunks timeLift (sleepChunks cfg.pollIntervalMs)).run (sAfterMk, cfg.totalSlots) =
            ((), (sAfterSleep, cfg.totalSlots)) := by
          rw [runSleepChunks_liftTimeFirst, hSleep]
        let retryPolicy := if policy == .noWait then WaitPolicy.waitForever else WaitPolicy.waitUpTo cfg.pollIntervalMs
        have hRun1 : (((mkApiM (mkFsFailLock1 fs cfg errIdx lockFsErr) timeLift).withSlot cfg retryPolicy fun _ => do
            let _ ← fsLift.writeText markerPath "ran"
            return (.ok 1 : Except SlotPoolError Nat)).run (s₀, 0)) =
            (.error (mapFsError lockFsErr), (sAfterSleep, targetCall + 1)) := by
          dsimp only [mkApiM, Internal.mkApiM, withSlotM]
          rw [hVal]; dsimp only
          rw [stateM_bind_run, hMkLift]; dsimp only
          cases hNoW : (policy == .noWait)
          · have hPol : retryPolicy = .waitUpTo cfg.pollIntervalMs := by simp [retryPolicy, hNoW]
            rw [hPol]; dsimp only
            rw [stateM_bind_run]
            cases hMono : time.monoNanosNow.run sAfterMk with
            | mk startNs sMono =>
              have hsEq : sMono = sAfterMk := by rw [hMono] at hMono'; exact hMono'
              subst sMono
              have hML0 : timeLift.monoNanosNow.run (sAfterMk, 0) = (startNs, (sAfterMk, 0)) := by
                change (let (a, s') := time.monoNanosNow.run sAfterMk; (a, (s', 0))) = _; rw [hMono]
              have hML1 : timeLift.monoNanosNow.run (sAfterMk, cfg.totalSlots) = (startNs, (sAfterMk, cfg.totalSlots)) := by
                change (let (a, s') := time.monoNanosNow.run sAfterMk; (a, (s', cfg.totalSlots))) = _; rw [hMono]
              rw [hML0]; dsimp only
              have hF2 : maxForeverPolls = ((2 ^ 64 - 2) + 1) + 1 := by decide
              rw [hF2]; unfold pollWaitUpToM
              rw [stateM_bind_run, hPoll0]; dsimp only
              rw [stateM_bind_run, hML1]; dsimp only
              have hNotGe : ¬ (startNs ≥ deadlineNanos startNs cfg.pollIntervalMs) := by
                dsimp [deadlineNanos, nanosecondsPerMs]; omega
              simp only [hNotGe, ↓reduceIte]
              have hNextEq : nextSleepMs cfg.pollIntervalMs startNs (deadlineNanos startNs cfg.pollIntervalMs) = cfg.pollIntervalMs := by
                dsimp [nextSleepMs, remainingWaitMs]
                simp only [hNotGe, ↓reduceIte]
                dsimp [deadlineNanos, nanosecondsPerMs] at *
                apply Nat.min_eq_left
                omega
              rw [hNextEq, stateM_bind_run, hSleepLift]; dsimp only
              unfold pollWaitUpToM
              rw [stateM_bind_run, hPoll1]; rfl
          · have hPol : retryPolicy = .waitForever := by simp [retryPolicy, hNoW]
            rw [hPol]; dsimp only
            have hF2 : maxForeverPolls = ((2 ^ 64 - 2) + 1) + 1 := by decide
            rw [hF2]; unfold pollForeverM
            rw [stateM_bind_run, hPoll0]; dsimp only
            rw [stateM_bind_run, hSleepLift]; dsimp only
            unfold pollForeverM
            rw [stateM_bind_run, hPoll1]; rfl
        show (let out1 := ((mkApiM (mkFsFailLock1 fs cfg errIdx lockFsErr) timeLift).withSlot cfg retryPolicy fun _ => do
            let _ ← fsLift.writeText markerPath "ran"
            return (.ok 1 : Except SlotPoolError Nat)).run (s₀, 0)
          ((∃ e, out1.1 = .error e ∧ e.kind = mapFsErrorKind lockFsErr.kind ∧ e.path = lockFsErr.path ∧ e.message ≠ "") ∧
            out1.2 = (sAfterSleep, targetCall + 1) ∧
            ((fs.lstat markerPath).run out1.2.1).1.isOk = false) ∧ True)
        rw [hRun1]
        exact ⟨⟨⟨mapFsError lockFsErr, rfl, rfl, rfl, mapFsError_nonEmpty lockFsErr⟩, rfl, hMarkerAfter'⟩, trivial⟩

/-- Witness 5 (`CanReach`): `test_slotpool_tryLock_fsError_propagatedWithoutRunningAction` is reachable for `mkApiM`. -/
theorem reach_tryLock_fsError_propagatedWithoutRunningAction :
    CanReach (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction mkApiM simFs simTime) :=
  ⟨{}, { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 }, 1, true, .waitForever,
    { kind := .permissionDenied, path := some "pool/slot-1.lock", message := "denied" }, "marker.txt",
    by decide, rfl, rfl, rfl,
    ⟨rfl, proof_tryLock_fsError_propagatedWithoutRunningAction simFs simTime
      {} { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 } 1 true .waitForever
      { kind := .permissionDenied, path := some "pool/slot-1.lock", message := "denied" }
      "marker.txt" (by decide) rfl rfl rfl rfl⟩⟩

/-- Specification 6 (`AllPass`): over arbitrary monotonic `TimeOpsM (StateM S)`, `WaitPolicy.waitUpTo` enforces immediate expiry, sub-ms ceiling rounding, budget clamping, and `UInt32` chunking. -/
theorem proof_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep
    {S : Type} (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) :
    AllPass (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep mkApiM fs time) := by
  intro s₀ cfg timeoutMs hValid _ hMkOk hMono1
  obtain ⟨hVal, _, _, hPoll⟩ := validatePoolConfig_of_true cfg hValid
  dsimp only [test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep, AllPass]
  let fsAllBusy : FsApiM (StateM S) :=
    { fs with
      tryWithFileLock := fun p mode createIfMissing _ =>
        if mode == .exclusive && createIfMissing then
          pure (.ok none)
        else
          pure (.error { kind := .invalidInput, path := some p, message := "unexpected lock mode or create flag" }) }
  have hScan : ∀ st (action : Nat → StateM S (Except SlotPoolError Nat)),
      (scanSlotsM fsAllBusy cfg.poolDir 0 cfg.totalSlots action).run st = (.allBusy, st) := by
    intro st act
    apply scanSlotsM_allNone
    intro _
    rfl
  cases hMk : (fs.mkdir cfg.poolDir true true).run s₀ with
  | mk mkRes s₁ =>
    have hResOk : mkRes = .ok () := by rw [hMk] at hMkOk; exact hMkOk
    subst hResOk
    rw [hMk] at hMono1
    dsimp only at hMono1 ⊢
    cases hStart : time.monoNanosNow.run s₁ with
    | mk startNs s₂ =>
      rw [hStart] at hMono1
      dsimp only at hMono1 ⊢
      cases hNow1 : time.monoNanosNow.run s₂ with
      | mk nowNs₁ s₃ =>
        rw [hNow1] at hMono1
        dsimp only at hMono1 ⊢
        let dl := deadlineNanos startNs timeoutMs
        by_cases hExp1 : nowNs₁ ≥ dl
        · simp only [dl, hExp1, ↓reduceIte]
          rw [allPass_assert_end]
          have hRun : (((mkApiM fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
              pure (.ok 1 : Except SlotPoolError Nat)).run s₀) = (.ok .noSlot, s₃) := by
            dsimp only [mkApiM, Internal.mkApiM, withSlotM]
            rw [hVal]
            dsimp only
            rw [stateM_bind_run]
            have hMk2 : (fsAllBusy.mkdir cfg.poolDir true true).run s₀ = (.ok (), s₁) := hMk
            rw [hMk2]
            dsimp only
            rw [stateM_bind_run, hStart]
            dsimp only
            have hF1 : maxForeverPolls = (2 ^ 64 - 1) + 1 := by decide
            rw [hF1]
            unfold pollWaitUpToM
            rw [stateM_bind_run, hScan]
            dsimp only
            rw [stateM_bind_run, hNow1]
            dsimp only
            split
            · rfl
            · contradiction
          show (let out := ((mkApiM fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
              pure (.ok 1 : Except SlotPoolError Nat)).run s₀
            (out.1 = .ok .noSlot ∧ out.2 = s₃) ∧ True)
          rw [hRun]
          exact ⟨⟨rfl, rfl⟩, trivial⟩
        · simp only [dl, hExp1, ↓reduceIte]
          let sleepDur₁ := nextSleepMs cfg.pollIntervalMs nowNs₁ dl
          have hDurBounds₁ : 1 ≤ sleepDur₁ ∧ sleepDur₁ ≤ cfg.pollIntervalMs := by
            dsimp [sleepDur₁, nextSleepMs, remainingWaitMs, nanosecondsPerMs]
            simp only [hExp1, ↓reduceIte]
            exact ⟨Nat.le_min.mpr ⟨hPoll, by omega⟩, Nat.min_le_left _ _⟩
          cases hSleep1 : (runSleepChunks time (sleepChunks sleepDur₁)).run s₃ with
          | mk _ s₄ =>
            have hSleep1' : (runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs nowNs₁ (deadlineNanos startNs timeoutMs)))).run s₃ = ((), s₄) := hSleep1
            dsimp only
            cases hNow2 : time.monoNanosNow.run s₄ with
            | mk nowNs₂ s₅ =>
              dsimp only
              by_cases hExp2 : nowNs₂ ≥ dl
              · simp only [dl, hExp2, ↓reduceIte]
                rw [allPass_assert_end]
                have hRun : (((mkApiM fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
                    pure (.ok 1 : Except SlotPoolError Nat)).run s₀) = (.ok .noSlot, s₅) := by
                  dsimp only [mkApiM, Internal.mkApiM, withSlotM]
                  rw [hVal]; dsimp only
                  rw [stateM_bind_run]
                  have hMk2 : (fsAllBusy.mkdir cfg.poolDir true true).run s₀ = (.ok (), s₁) := hMk
                  rw [hMk2]; dsimp only
                  rw [stateM_bind_run, hStart]; dsimp only
                  have hF2 : maxForeverPolls = ((2 ^ 64 - 2) + 1) + 1 := by decide
                  rw [hF2]; unfold pollWaitUpToM
                  rw [stateM_bind_run, hScan]; dsimp only
                  rw [stateM_bind_run, hNow1]; dsimp only
                  split
                  · contradiction
                  · rw [stateM_bind_run, hSleep1']; dsimp only
                    unfold pollWaitUpToM
                    rw [stateM_bind_run, hScan]; dsimp only
                    rw [stateM_bind_run, hNow2]; dsimp only
                    split
                    · rfl
                    · contradiction
                show (let out := ((mkApiM fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
                    pure (.ok 1 : Except SlotPoolError Nat)).run s₀
                  (1 ≤ sleepDur₁ ∧ sleepDur₁ ≤ cfg.pollIntervalMs ∧ out.1 = .ok .noSlot ∧ out.2 = s₅) ∧ True)
                rw [hRun]
                exact ⟨⟨hDurBounds₁.1, hDurBounds₁.2, rfl, rfl⟩, trivial⟩
              · simp only [dl, hExp2, ↓reduceIte]
                dsimp only [Bind.bind, NondetTest.assume]
                let sleepDur₂ := nextSleepMs cfg.pollIntervalMs nowNs₂ dl
                have hDurBounds₂ : 1 ≤ sleepDur₂ ∧ sleepDur₂ ≤ cfg.pollIntervalMs := by
                  dsimp [sleepDur₂, nextSleepMs, remainingWaitMs, nanosecondsPerMs]
                  simp only [hExp2, ↓reduceIte]
                  exact ⟨Nat.le_min.mpr ⟨hPoll, by omega⟩, Nat.min_le_left _ _⟩
                cases hSleep2 : (runSleepChunks time (sleepChunks sleepDur₂)).run s₅ with
                | mk _ s₆ =>
                  have hSleep2' : (runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs nowNs₂ (deadlineNanos startNs timeoutMs)))).run s₅ = ((), s₆) := hSleep2
                  dsimp only
                  cases hNow3 : time.monoNanosNow.run s₆ with
                  | mk nowNs₃ s₇ =>
                    dsimp only
                    intro _
                    rw [allPass_assert_end]
                    have hRun : (((mkApiM fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
                        pure (.ok 1 : Except SlotPoolError Nat)).run s₀) = (.ok .noSlot, s₇) := by
                      dsimp only [mkApiM, Internal.mkApiM, withSlotM]
                      rw [hVal]; dsimp only
                      rw [stateM_bind_run]
                      have hMk2 : (fsAllBusy.mkdir cfg.poolDir true true).run s₀ = (.ok (), s₁) := hMk
                      rw [hMk2]; dsimp only
                      rw [stateM_bind_run, hStart]; dsimp only
                      have hF3 : maxForeverPolls = (((2 ^ 64 - 3) + 1) + 1) + 1 := by decide
                      rw [hF3]; unfold pollWaitUpToM
                      rw [stateM_bind_run, hScan]; dsimp only
                      rw [stateM_bind_run, hNow1]; dsimp only
                      split
                      · contradiction
                      · rw [stateM_bind_run, hSleep1']; dsimp only
                        unfold pollWaitUpToM
                        rw [stateM_bind_run, hScan]; dsimp only
                        rw [stateM_bind_run, hNow2]; dsimp only
                        split
                        · contradiction
                        · rw [stateM_bind_run, hSleep2']; dsimp only
                          unfold pollWaitUpToM
                          rw [stateM_bind_run, hScan]; dsimp only
                          rw [stateM_bind_run, hNow3]; dsimp only
                          split
                          · rfl
                          · contradiction
                    show (let out := ((mkApiM fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
                        pure (.ok 1 : Except SlotPoolError Nat)).run s₀
                      (1 ≤ sleepDur₁ ∧ sleepDur₁ ≤ cfg.pollIntervalMs ∧
                        1 ≤ sleepDur₂ ∧ sleepDur₂ ≤ cfg.pollIntervalMs ∧ out.1 = .ok .noSlot ∧ out.2 = s₇) ∧ True)
                    rw [hRun]
                    exact ⟨⟨hDurBounds₁.1, hDurBounds₁.2, hDurBounds₂.1, hDurBounds₂.2, rfl, rfl⟩, trivial⟩

/-- Witness 6 (`CanReach`): `test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep` is reachable along the 2-sleep path for `mkApiM`. -/
theorem reach_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep :
    CanReach (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep mkApiM simFs simTime) := by
  refine ⟨{}, { poolDir := "pool", totalSlots := 1, pollIntervalMs := 10 }, 20,
    by decide, by decide, rfl, ?_, ?_⟩
  · have hMk0 : (simFs.mkdir "pool" true true).run {} = (.ok (), { dirs := ["pool"] }) := rfl
    rw [hMk0]; decide
  · have hMk0 : (simFs.mkdir "pool" true true).run {} = (.ok (), { dirs := ["pool"] }) := rfl
    have hp := proof_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep simFs simTime
      {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 10 } 20
      (by decide) (by decide) rfl (by rw [hMk0]; decide)
    dsimp only [CanReach, Bind.bind, NondetTest.assume, NondetTest.assert]
    dsimp only [test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep, AllPass,
      Bind.bind, NondetTest.assume, NondetTest.assert] at hp
    rw [hMk0] at hp ⊢
    dsimp only at hp ⊢
    have h1 : ¬ ((simTime.monoNanosNow.run (simTime.monoNanosNow.run { dirs := ["pool"] }).2).1 ≥
        deadlineNanos (simTime.monoNanosNow.run { dirs := ["pool"] }).1 20) := by decide
    have h2 : ¬ ((simTime.monoNanosNow.run ((runSleepChunks simTime (sleepChunks
        (nextSleepMs 10 (simTime.monoNanosNow.run (simTime.monoNanosNow.run { dirs := ["pool"] }).2).1
          (deadlineNanos (simTime.monoNanosNow.run { dirs := ["pool"] }).1 20)))).run
        (simTime.monoNanosNow.run (simTime.monoNanosNow.run { dirs := ["pool"] }).2).2).2).1 ≥
        deadlineNanos (simTime.monoNanosNow.run { dirs := ["pool"] }).1 20) := by decide
    simp only [h1, h2, ↓reduceIte] at hp ⊢
    exact ⟨by decide, hp (by decide)⟩

end LeanSwe.SlotPool.Proofs
