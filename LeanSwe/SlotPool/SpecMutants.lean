import Core.NondetTest
import LeanSwe.Fs.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Types
import LeanSwe.Time.Types
import LeanSwe.SlotPool.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.SlotPool`. -/

namespace LeanSwe.SlotPool

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Model

private def buggyTimingSubMsFloorOps : TimingModelOps :=
  { defaultTimingModelOps with
    remainingWaitMs := fun nowNs dl =>
      if nowNs ≥ dl then 0 else (dl - nowNs) / nanosecondsPerMs }

private def buggyTimingUnclampedNextOps : TimingModelOps :=
  { defaultTimingModelOps with
    nextSleepMs := fun pollMs _ _ => pollMs }

private def buggyTimingTruncatesUInt32Ops : TimingModelOps :=
  { defaultTimingModelOps with
    sleepChunks := fun ms => if ms == 0 then [] else [UInt32.ofNat ms] }

private def buggyAcceptsZeroSlots : SlotPoolBuilder (StateM PoolSimState) :=
  fun _ _ =>
    { withSlot := fun cfg _ _ =>
        if !validPoolDir cfg.poolDir || cfg.pollIntervalMs == 0 then
          pure (.error { kind := .invalidInput, message := "invalid" })
        else
          pure (.ok .noSlot) }

private def buggyAcceptsZeroPollInterval : SlotPoolBuilder (StateM PoolSimState) :=
  fun _ _ =>
    { withSlot := fun cfg _ _ =>
        if !validPoolDir cfg.poolDir || cfg.totalSlots == 0 then
          pure (.error { kind := .invalidInput, message := "invalid" })
        else
          pure (.ok .noSlot) }

private def buggyAcceptsEmptyPoolDir : SlotPoolBuilder (StateM PoolSimState) :=
  fun _ _ =>
    { withSlot := fun cfg _ _ =>
        if hasNulChar cfg.poolDir.toList || cfg.totalSlots == 0 || cfg.pollIntervalMs == 0 then
          pure (.error { kind := .invalidInput, message := "invalid" })
        else
          pure (.ok .noSlot) }

private def buggyAcceptsNulPoolDir : SlotPoolBuilder (StateM PoolSimState) :=
  fun _ _ =>
    { withSlot := fun cfg _ _ =>
        if cfg.poolDir.isEmpty || cfg.totalSlots == 0 || cfg.pollIntervalMs == 0 then
          pure (.error { kind := .invalidInput, message := "invalid" })
        else
          pure (.ok .noSlot) }

private def buggyMkdirBeforeValidation : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        let _ ← fs.mkdir "pool" true true
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        return .ok .noSlot }

private def buggySkipsMkdir : SlotPoolBuilder (StateM PoolSimState) :=
  fun _ _ =>
    { withSlot := fun cfg _ _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        return .ok .noSlot }

private def buggyContentionReturnsError {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () => return .error { kind := .ioError, message := "all slots busy" } }

private def buggyContentionRunsActionUnlocked {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          match ← action 0 with
          | .error e => return .error e
          | .ok v => return .ok (.leased 0 v) }

private def buggyNoWaitSleeps {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs time =>
    { withSlot := fun cfg _ _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          time.sleep 10
          return .ok .noSlot }

private def buggyTreatsLockErrorAsContention {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          let _ ← fs.tryWithFileLock (slotLockPath fs.join cfg.poolDir 0) .exclusive true (pure (.ok ()))
          return .ok .noSlot }

private def buggyWaitUpToSleepsWhenExpired : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg _ _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          let _ ← time.monoNanosNow
          let _ ← time.monoNanosNow
          time.sleep 1
          return .ok .noSlot }

private def buggyWaitUpToOversleepsBudget : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          match policy with
          | .waitUpTo timeoutMs =>
            let startNs ← time.monoNanosNow
            let dl := deadlineNanos startNs timeoutMs
            let nowNs ← time.monoNanosNow
            if nowNs ≥ dl then
              return .ok .noSlot
            else
              runSleepChunks time (sleepChunks cfg.pollIntervalMs)
              let _ ← time.monoNanosNow
              return .ok .noSlot
          | _ => return .ok .noSlot }

private def buggySubMsFloorSpinsZeroMs : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          match policy with
          | .waitUpTo timeoutMs =>
            let startNs ← time.monoNanosNow
            let dl := deadlineNanos startNs timeoutMs
            let nowNs ← time.monoNanosNow
            if nowNs ≥ dl then
              return .ok .noSlot
            else
              let floorRem := (dl - nowNs) / nanosecondsPerMs
              runSleepChunks time (sleepChunks (Nat.min cfg.pollIntervalMs floorRem))
              let _ ← time.monoNanosNow
              return .ok .noSlot
          | _ => return .ok .noSlot }

private def buggySleepTruncatesUInt32 : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          match policy with
          | .waitUpTo timeoutMs =>
            let startNs ← time.monoNanosNow
            let dl := deadlineNanos startNs timeoutMs
            let nowNs ← time.monoNanosNow
            if nowNs ≥ dl then
              return .ok .noSlot
            else
              let dur := nextSleepMs cfg.pollIntervalMs nowNs dl
              time.sleep (UInt32.ofNat dur)
              let _ ← time.monoNanosNow
              return .ok .noSlot
          | _ => return .ok .noSlot }

private def buggyIgnoresPoolDir : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir "/tmp/pool" true true
        let p := slotLockPath fs.join "/tmp/pool" 0
        match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.error e)) => return .error e
        | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyWrongSlotFileName : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let p := fs.join cfg.poolDir "slot-0"
        match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.error e)) => return .error e
        | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyOutOfRangeSlotIndex : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let badIdx := cfg.totalSlots
        let p := slotLockPath fs.join cfg.poolDir badIdx
        match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action badIdx)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.error e)) => return .error e
        | .ok (some (.ok v)) => return .ok (.leased badIdx v) }

private def buggySharedLockMode : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let p := slotLockPath fs.join cfg.poolDir 0
        match ← fs.tryWithFileLock p .shared true (do return .ok (← action 0)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.error e)) => return .error e
        | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyCreateIfMissingFalse : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let p := slotLockPath fs.join cfg.poolDir 0
        match ← fs.tryWithFileLock p .exclusive false (do return .ok (← action 0)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.error e)) => return .error e
        | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyDescendingScanOrder : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let hi := cfg.totalSlots - 1
        let p := slotLockPath fs.join cfg.poolDir hi
        match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action hi)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.error e)) => return .error e
        | .ok (some (.ok v)) => return .ok (.leased hi v) }

private def buggyMkdirNoParents : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir false true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          let p := slotLockPath fs.join cfg.poolDir 0
          match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
          | .error fe => return .error (mapFsError fe)
          | .ok none => return .ok .noSlot
          | .ok (some (.error e)) => return .error e
          | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyMkdirNoExistOk : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true false with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          let p := slotLockPath fs.join cfg.poolDir 0
          match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
          | .error fe => return .error (mapFsError fe)
          | .ok none => return .ok .noSlot
          | .ok (some (.error e)) => return .error e
          | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyWaitUpToZeroSkipsInitialScan : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg policy action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        match ← fs.mkdir cfg.poolDir true true with
        | .error fe => return .error (mapFsError fe)
        | .ok () =>
          match policy with
          | .waitUpTo 0 => return .ok .noSlot
          | _ =>
            let p := slotLockPath fs.join cfg.poolDir 0
            match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
            | .error fe => return .error (mapFsError fe)
            | .ok none => return .ok .noSlot
            | .ok (some (.error e)) => return .error e
            | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggySwallowsCallbackError : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let p := slotLockPath fs.join cfg.poolDir 0
        match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.error _)) => return .ok .noSlot
        | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyLeaksLockOnCallbackError : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let p := slotLockPath fs.join cfg.poolDir 0
        let np := normSimPath p
        modify fun s => { s with files := (np, "") :: s.files, heldLocks := (np, .exclusive) :: s.heldLocks }
        match ← action 0 with
        | .error e => return .error e
        | .ok v =>
          modify fun s => { s with heldLocks := removeFirstSimLock np .exclusive s.heldLocks }
          return .ok (.leased 0 v) }

private def buggyContinuesScanOnCallbackError : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        let p0 := slotLockPath fs.join cfg.poolDir 0
        match ← fs.tryWithFileLock p0 .exclusive true (do return .ok (← action 0)) with
        | .error fe => return .error (mapFsError fe)
        | .ok none => return .ok .noSlot
        | .ok (some (.ok v)) => return .ok (.leased 0 v)
        | .ok (some (.error e0)) =>
          if 1 < cfg.totalSlots then
            let p1 := slotLockPath fs.join cfg.poolDir 1
            match ← fs.tryWithFileLock p1 .exclusive true (do return .ok (← action 1)) with
            | .ok (some (.ok v1)) => return .ok (.leased 1 v1)
            | _ => return .error e0
          else
            return .error e0 }

private def buggyExLeaksLockOnThrow : SlotPoolBuilder (ExceptT String (StateM PoolSimState)) :=
  fun fs _ =>
    { withSlot := fun cfg _ action =>
        ExceptT.mk fun s₀ =>
          if !validPoolConfig cfg then
            (.ok (.error { kind := .invalidInput, message := "invalid" }), s₀)
          else
            let np := normSimPath (slotLockPath fs.join cfg.poolDir 0)
            let s₁ : PoolSimState :=
              { s₀ with
                dirs := normSimPath cfg.poolDir :: s₀.dirs
                files := (np, "") :: s₀.files
                heldLocks := (np, .exclusive) :: s₀.heldLocks }
            let (actRes, s₂) := (ExceptT.run (action 0)).run s₁
            match actRes with
            | .error ex => (.error ex, s₂)
            | .ok (.error e) =>
              (.ok (.error e), { s₂ with heldLocks := removeFirstSimLock np .exclusive s₂.heldLocks })
            | .ok (.ok v) =>
              (.ok (.ok (.leased 0 v)), { s₂ with heldLocks := removeFirstSimLock np .exclusive s₂.heldLocks }) }

private def buggyWaitUpToGivesUpImmediately : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        return .ok .noSlot }

private def buggyWaitUpToNeverRescansFreedSlot : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        match policy with
        | .waitUpTo timeoutMs =>
          runSleepChunks time (sleepChunks timeoutMs)
          return .ok .noSlot
        | _ => return .ok .noSlot }

private def buggyWaitForeverGivesUpOnFirstContention : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        if !validPoolConfig cfg then
          return .error { kind := .invalidInput, message := "invalid" }
        let _ ← fs.mkdir cfg.poolDir true true
        return .ok .noSlot }

example : ¬ Core.AllPass (test_slotpool_model_timingAndSleepChunks_exactAndChunked buggyTimingSubMsFloorOps) := by
  intro h
  have h0 := h 0 1 500000 50 10 (by decide)
  dsimp [test_slotpool_model_timingAndSleepChunks_exactAndChunked, buggyTimingSubMsFloorOps,
    defaultTimingModelOps, deadlineNanos, nanosecondsPerMs, Bind.bind, Core.NondetTest.assert] at h0
  exact absurd h0.2.1.1 (by decide)

example : ¬ Core.AllPass (test_slotpool_model_timingAndSleepChunks_exactAndChunked buggyTimingUnclampedNextOps) := by
  intro h
  have h0 := h 0 10 0 50 10 (by decide)
  dsimp [test_slotpool_model_timingAndSleepChunks_exactAndChunked, buggyTimingUnclampedNextOps,
    defaultTimingModelOps, deadlineNanos, remainingWaitMs, nanosecondsPerMs, Bind.bind, Core.NondetTest.assert] at h0
  exact absurd h0.2.2.1.2.2.1 (by decide)

example : ¬ Core.AllPass (test_slotpool_model_timingAndSleepChunks_exactAndChunked buggyTimingTruncatesUInt32Ops) := by
  intro h
  have h0 := h 0 10 0 50 4294967296 (by decide)
  dsimp [test_slotpool_model_timingAndSleepChunks_exactAndChunked, buggyTimingTruncatesUInt32Ops,
    defaultTimingModelOps, deadlineNanos, remainingWaitMs, nextSleepMs, nanosecondsPerMs, Bind.bind,
    Core.NondetTest.assert] at h0
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects
    buggyAcceptsZeroSlots simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 0, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects
    buggyAcceptsZeroPollInterval simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 2, pollIntervalMs := 0 } .noWait "marker.txt" (by decide)
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects
    buggyAcceptsEmptyPoolDir simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "", totalSlots := 2, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects
    buggyAcceptsNulPoolDir simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool\x00bad", totalSlots := 2, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects
    buggyMkdirBeforeValidation simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "", totalSlots := 1, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)
  exact absurd h0.1.2 (by decide)

example : ¬ Core.AllPass (test_slotpool_mkdir_fsError_propagatedBeforePolling
    buggySkipsMkdir simFs simTime) := by
  intro h
  let s₀ : PoolSimState := { files := [("pool", "blocking-file")] }
  have h0 := h s₀ { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction
    buggyContentionReturnsError simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } "marker.txt"
    (by decide) rfl rfl
  have hEq : (Except.error { kind := .ioError, message := "all slots busy" } : Except SlotPoolError (LeaseOutcome Nat)) =
      Except.ok .noSlot := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction
    buggyContentionRunsActionUnlocked simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } "marker.txt"
    (by decide) rfl rfl
  have hEq : (Except.ok (.leased 0 1) : Except SlotPoolError (LeaseOutcome Nat)) =
      Except.ok .noSlot := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction
    buggyNoWaitSleeps simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } "marker.txt"
    (by decide) rfl rfl
  exact absurd h0.1.2.1 (by decide)

example : ¬ Core.AllPass (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction
    buggyTreatsLockErrorAsContention simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 false .noWait
    { kind := .permissionDenied, path := some "pool/slot-0.lock", message := "denied" } "marker.txt"
    (by decide) rfl rfl rfl
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep
    buggyWaitUpToSleepsWhenExpired simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0
    (by decide) (by decide) rfl (by decide)
  exact absurd h0.1.2 (by decide)

example : ¬ Core.AllPass (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep
    buggyWaitUpToOversleepsBudget simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 20
    (by decide) (by decide) rfl (by decide)
  have h1 : ¬ ((simTime.monoNanosNow.run (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).1 ≥
      deadlineNanos (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 20) := by decide
  have h2 : (simTime.monoNanosNow.run ((runSleepChunks simTime (sleepChunks
      (nextSleepMs 50 (simTime.monoNanosNow.run (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).1
        (deadlineNanos (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 20)))).run
      (simTime.monoNanosNow.run (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).2).2).1 ≥
      deadlineNanos (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 20 := by decide
  dsimp only [test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep,
    Core.AllPass, Bind.bind, Core.NondetTest.assume, Core.NondetTest.assert] at h0
  simp only [h1, h2, ↓reduceIte] at h0
  have hMono := congrArg PoolSimState.monoNanos h0.1.2.2.2
  change 50000000 = 20000000 at hMono
  exact absurd hMono (by decide)

private def stepHalfMsClock : TimeOpsM (StateM PoolSimState) :=
  { simTime with
    monoNanosNow := do
      let s ← get
      let cur := s.monoNanos
      set { s with monoNanos := if cur == 0 then 500000 else cur }
      return cur }

example : ¬ Core.AllPass (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep
    buggySubMsFloorSpinsZeroMs simFs stepHalfMsClock) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 1
    (by decide) (by decide) rfl (by decide)
  have h1 : ¬ ((stepHalfMsClock.monoNanosNow.run (stepHalfMsClock.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).1 ≥
      deadlineNanos (stepHalfMsClock.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 1) := by decide
  have h2 : (stepHalfMsClock.monoNanosNow.run ((runSleepChunks stepHalfMsClock (sleepChunks
      (nextSleepMs 50 (stepHalfMsClock.monoNanosNow.run (stepHalfMsClock.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).1
        (deadlineNanos (stepHalfMsClock.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 1)))).run
      (stepHalfMsClock.monoNanosNow.run (stepHalfMsClock.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).2).2).1 ≥
      deadlineNanos (stepHalfMsClock.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 1 := by decide
  dsimp only [test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep,
    Core.AllPass, Bind.bind, Core.NondetTest.assume, Core.NondetTest.assert] at h0
  simp only [h1, h2, ↓reduceIte] at h0
  have hMono := congrArg PoolSimState.monoNanos h0.1.2.2.2
  change 500000 = 1500000 at hMono
  exact absurd hMono (by decide)

example : ¬ Core.AllPass (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep
    buggySleepTruncatesUInt32 simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 4294967296 } 4294967296
    (by decide) (by decide) rfl (by decide)
  have h1 : ¬ ((simTime.monoNanosNow.run (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).1 ≥
      deadlineNanos (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 4294967296) := by decide
  have h2 : (simTime.monoNanosNow.run ((runSleepChunks simTime (sleepChunks
      (nextSleepMs 4294967296 (simTime.monoNanosNow.run (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).1
        (deadlineNanos (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 4294967296)))).run
      (simTime.monoNanosNow.run (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).2).2).2).1 ≥
      deadlineNanos (simTime.monoNanosNow.run ((simFs.mkdir "pool" true true).run {}).2).1 4294967296 := by decide
  dsimp only [test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep,
    Core.AllPass, Bind.bind, Core.NondetTest.assume, Core.NondetTest.assert] at h0
  simp only [h1, h2, ↓reduceIte] at h0
  have hMono := congrArg PoolSimState.monoNanos h0.1.2.2.2
  change 0 = 4294967296000000 at hMono
  exact absurd hMono (by decide)

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyIgnoresPoolDir) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .ioError, path := some "pool/slot-0.lock", message := "exclusive lock invariant failed" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyWrongSlotFileName) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .ioError, path := some "pool/slot-0.lock", message := "exclusive lock invariant failed" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyOutOfRangeSlotIndex) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .ioError, path := some "pool/slot-1.lock", message := "slot index invariant failed" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggySharedLockMode) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .ioError, path := some "pool/slot-0.lock", message := "exclusive lock invariant failed" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyCreateIfMissingFalse) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .notFound, path := some "pool/slot-0.lock", message := "lock file does not exist" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyDescendingScanOrder) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .ioError, path := some "pool/slot-1.lock", message := "slot index invariant failed" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyMkdirNoParents) := by
  intro h
  have h0 := h { poolDir := "nested/pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .notFound, path := some "nested/pool", message := "parent directory does not exist" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyMkdirNoExistOk) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait true 0 (by decide)
  have hEq : (Except.error { kind := .alreadyExists, path := some "pool", message := "directory already exists" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyWaitUpToZeroSkipsInitialScan) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 (.waitUpTo 0) false 0 (by decide)
  have hEq : (Except.ok .noSlot : Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan
    buggySwallowsCallbackError) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1
    { kind := .ioError, message := "cb failed" } .noWait (by decide)
  have hEq : (Except.ok .noSlot : Except SlotPoolError (LeaseOutcome Nat)) =
      Except.error { kind := .ioError, message := "cb failed" } := h0.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan
    buggyLeaksLockOnCallbackError) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1
    { kind := .ioError, message := "cb failed" } .noWait (by decide)
  have hEq : [("pool/slot-0.lock", LockMode.exclusive)] = ([] : List (String × LockMode)) := h0.2.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan
    buggyContinuesScanOnCallbackError) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 } 0 1
    { kind := .ioError, message := "cb failed" } .noWait (by decide)
  have hEq : (Except.ok (.leased 1 99) : Except SlotPoolError (LeaseOutcome Nat)) =
      Except.error { kind := .ioError, message := "cb failed" } := h0.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates
    buggyExLeaksLockOnThrow) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 .noWait (by decide)
  have hEq : [("pool/slot-0.lock", .exclusive)] = ([] : List (String × LockMode)) := h0.1.2.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline
    buggyWaitUpToGivesUpImmediately) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1 50 7 0 (by decide)
  exact absurd h0.2.1.1 (by decide)

example : ¬ Core.AllPass (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline
    buggyWaitUpToNeverRescansFreedSlot) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1 50 7 0 (by decide)
  dsimp [test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline,
    buggyWaitUpToNeverRescansFreedSlot, Bind.bind, Core.NondetTest.assert] at h0
  have hEq : (Except.ok .noSlot : Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.2.2.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_waitForever_contendedPool_pollsUntilSlotFree
    buggyWaitForeverGivesUpOnFirstContention) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 2 9 0 (by decide)
  have hEq : (Except.ok .noSlot : Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 9) := h0.1.1
  cases hEq

private def buggyValidationDropsErrorPath : SlotPoolBuilder (StateM PoolSimState) :=
  fun _ _ =>
    { withSlot := fun cfg _ _ =>
        if !validPoolConfig cfg then
          pure (.error { kind := .invalidInput, path := none, message := "invalid" })
        else
          pure (.ok .noSlot) }

private def buggyMkdirDropsErrorPath : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          match ← fs.mkdir cfg.poolDir true true with
          | .error fe => return .error { mapFsError fe with path := none }
          | .ok () => return .ok .noSlot }

private def buggyNoWaitNeverScansSlots {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          match ← fs.mkdir cfg.poolDir true true with
          | .error fe => return .error (mapFsError fe)
          | .ok () => return .ok .noSlot }

private def buggyTreatsHigherSlotLockErrorAsContention {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          match ← fs.mkdir cfg.poolDir true true with
          | .error fe => return .error (mapFsError fe)
          | .ok () =>
            match ← fs.tryWithFileLock (slotLockPath fs.join cfg.poolDir 0) .exclusive true (pure (.ok ())) with
            | .error fe => return .error (mapFsError fe)
            | _ =>
              if 1 < cfg.totalSlots then
                let _ ← fs.tryWithFileLock (slotLockPath fs.join cfg.poolDir 1) .exclusive true (pure (.ok ()))
                return .ok .noSlot
              else
                return .ok .noSlot }

private def buggyRetrySwallowsLockFsError {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs time =>
    { withSlot := fun cfg policy _ => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          match ← fs.mkdir cfg.poolDir true true with
          | .error fe => return .error (mapFsError fe)
          | .ok () =>
            let p0 := slotLockPath fs.join cfg.poolDir 0
            match ← fs.tryWithFileLock p0 .exclusive true (pure (.ok ())) with
            | .error fe => return .error (mapFsError fe)
            | _ =>
              match policy with
              | .noWait => return .ok .noSlot
              | _ =>
                runSleepChunks time (sleepChunks cfg.pollIntervalMs)
                let _ ← fs.tryWithFileLock p0 .exclusive true (pure (.ok ()))
                return .ok .noSlot }

private def buggyTryLockDropsErrorPath {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs _ =>
    { withSlot := fun cfg _ _ => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          match ← fs.mkdir cfg.poolDir true true with
          | .error fe => return .error (mapFsError fe)
          | .ok () =>
            match ← fs.tryWithFileLock (slotLockPath fs.join cfg.poolDir 0) .exclusive true (pure (.ok ())) with
            | .error fe => return .error { mapFsError fe with path := none }
            | _ => return .ok .noSlot }

private def buggyPoll2SubMsFloor : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy _ => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          match ← fs.mkdir cfg.poolDir true true with
          | .error fe => return .error (mapFsError fe)
          | .ok () =>
            match policy with
            | .waitUpTo timeoutMs =>
              let startNs ← time.monoNanosNow
              let dl := deadlineNanos startNs timeoutMs
              let now₁ ← time.monoNanosNow
              if now₁ ≥ dl then
                return .ok .noSlot
              else
                runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs now₁ dl))
                let now₂ ← time.monoNanosNow
                if now₂ ≥ dl then
                  return .ok .noSlot
                else
                  let floorRem := (dl - now₂) / nanosecondsPerMs
                  runSleepChunks time (sleepChunks (Nat.min cfg.pollIntervalMs floorRem))
                  let _ ← time.monoNanosNow
                  return .ok .noSlot
            | _ => return .ok .noSlot }

private def buggyUnlinksLockFileOnRelease : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let p := slotLockPath fs.join cfg.poolDir 0
          let r ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0))
          let _ ← fs.unlink p true
          match r with
          | .error fe => return .error (mapFsError fe)
          | .ok none => return .ok .noSlot
          | .ok (some (.error ce)) => return .error ce
          | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyLeaksLockOnOk : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let np := normSimPath (slotLockPath fs.join cfg.poolDir 0)
          modify fun s => { s with files := (np, "") :: s.files, heldLocks := (np, .exclusive) :: s.heldLocks }
          match ← action 0 with
          | .error ce =>
            modify fun s => { s with heldLocks := removeFirstSimLock np .exclusive s.heldLocks }
            return .error ce
          | .ok v => return .ok (.leased 0 v) }

example : ¬ Core.AllPass (test_slotpool_validation_invalidConfig_rejectedBeforeEffects
    buggyValidationDropsErrorPath simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "", totalSlots := 1, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)
  rcases h0.1.1 with ⟨e, he, _, hPath, _⟩
  injection he with he'
  rw [← he'] at hPath
  cases hPath

example : ¬ Core.AllPass (test_slotpool_mkdir_fsError_propagatedBeforePolling
    buggyMkdirDropsErrorPath simFs simTime) := by
  intro h
  let s₀ : PoolSimState := { files := [("pool", "blocking-file")] }
  have h0 := h s₀ { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } .noWait "marker.txt" (by decide)
  rcases h0.1.1 with ⟨e, he, _, hPath, _⟩
  injection he with he'
  rw [← he'] at hPath
  cases hPath

example : ¬ Core.AllPass (test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction
    buggyNoWaitNeverScansSlots simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } "marker.txt"
    (by decide) rfl rfl
  exact absurd h0.1.2.1 (by decide)

example : ¬ Core.AllPass (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction
    buggyTreatsHigherSlotLockErrorAsContention simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 } 1 false .noWait
    { kind := .invalidInput, path := some "pool/slot-1.lock", message := "symlink" } "marker.txt"
    (by decide) rfl rfl rfl
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction
    buggyRetrySwallowsLockFsError simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 true .noWait
    { kind := .invalidInput, path := some "pool/slot-0.lock", message := "symlink" } "marker.txt"
    (by decide) rfl rfl rfl rfl
  rcases h0.1.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_slotpool_tryLock_fsError_propagatedWithoutRunningAction
    buggyTryLockDropsErrorPath simFs simTime) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 false .noWait
    { kind := .permissionDenied, path := some "pool/slot-0.lock", message := "denied" } "marker.txt"
    (by decide) rfl rfl rfl
  rcases h0.1.1 with ⟨e, he, _, hPath, _⟩
  injection he with he'
  rw [← he'] at hPath
  cases hPath

example : ¬ Core.AllPass (test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep
    buggyPoll2SubMsFloor simFs
    { simTime with
      sleep := fun ms =>
        modify fun s =>
          { s with
            monoNanos := s.monoNanos + (if s.monoNanos == 0 then 1500000 else ms.toNat * nanosecondsPerMs)
            sleepLog := s.sleepLog.push ms } }) := by
  intro h
  have h0 := h {} { poolDir := "pool", totalSlots := 1, pollIntervalMs := 1 } 2
    (by decide) (by decide) rfl (by decide) (by decide)
  exact absurd h0.1.2.2.2.2.2 (by decide)

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyUnlinksLockFileOnRelease) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : (Except.error { kind := .notFound, path := some "pool/slot-0.lock", message := "lock file does not exist" } :
      Except FsError (Option Unit)) = Except.ok (some ()) := h0.2.1.2
  cases hEq

example : ¬ Core.AllPass (test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    buggyLeaksLockOnOk) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 7 .noWait false 0 (by decide)
  have hEq : [("pool/slot-0.lock", LockMode.exclusive)] = ([] : List (String × LockMode)) := h0.2.1.1
  cases hEq

private def buggyReplacesCallbackError : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let p := slotLockPath fs.join cfg.poolDir 0
          match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
          | .error fe => return .error (mapFsError fe)
          | .ok none => return .ok .noSlot
          | .ok (some (.error _)) => return .error { kind := .ioError, message := "overwritten callback error" }
          | .ok (some (.ok v)) => return .ok (.leased 0 v) }

private def buggyRetrySwallowsCallbackError : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let p := slotLockPath fs.join cfg.poolDir 0
          match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
          | .error fe => return .error (mapFsError fe)
          | .ok (some (.error ce)) => return .error ce
          | .ok (some (.ok v)) => return .ok (.leased 0 v)
          | .ok none =>
            match policy with
            | .noWait => return .ok .noSlot
            | _ =>
              runSleepChunks time (sleepChunks cfg.pollIntervalMs)
              match ← fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)) with
              | .ok (some (.ok v)) => return .ok (.leased 0 v)
              | _ => return .ok .noSlot }

private def buggyExRunsUnlocked : SlotPoolBuilder (ExceptT String (StateM PoolSimState)) :=
  fun fs _ =>
    { withSlot := fun cfg _ action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let _ ← fs.touch (slotLockPath fs.join cfg.poolDir 0) true
          match ← action 0 with
          | .error ce => return .error ce
          | .ok v => return .ok (.leased 0 v) }

private def buggyExSwallowsException : SlotPoolBuilder (ExceptT String (StateM PoolSimState)) :=
  fun fs _ =>
    { withSlot := fun cfg _ action =>
        ExceptT.mk fun s₀ =>
          let (res, s₁) := (ExceptT.run (do
            let _ ← fs.mkdir cfg.poolDir true true
            let p := slotLockPath fs.join cfg.poolDir 0
            fs.tryWithFileLock p .exclusive true (do return .ok (← action 0)))).run s₀
          match res with
          | .error _ => (.ok (.ok .noSlot), s₁)
          | .ok (.error fe) => (.ok (.error (mapFsError fe)), s₁)
          | .ok (.ok none) => (.ok (.ok .noSlot), s₁)
          | .ok (.ok (some (.error ce))) => (.ok (.error ce), s₁)
          | .ok (.ok (some (.ok v))) => (.ok (.ok (.leased 0 v)), s₁) }

private def buggyWaitUpToSkipsScanAfterClampedSleep : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let p0 := slotLockPath fs.join cfg.poolDir 0
          match policy with
          | .waitUpTo timeoutMs =>
            let startNs ← time.monoNanosNow
            let dl := deadlineNanos startNs timeoutMs
            let fuel := timeoutMs / cfg.pollIntervalMs + 1
            let rec go : Nat → StateM PoolSimState (Except SlotPoolError (LeaseOutcome _))
              | 0 => return .ok .noSlot
              | f + 1 => do
                match ← fs.tryWithFileLock p0 .exclusive true (do return .ok (← action 0)) with
                | .error fe => return .error (mapFsError fe)
                | .ok (some (.error ce)) => return .error ce
                | .ok (some (.ok v)) => return .ok (.leased 0 v)
                | .ok none =>
                  let nowNs ← time.monoNanosNow
                  if nowNs ≥ dl then return .ok .noSlot
                  else
                    runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs nowNs dl))
                    go f
            go fuel
          | _ => return .ok .noSlot }

private def buggyWaitUpToSecondPollOneMs : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy _ => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          match policy with
          | .waitUpTo timeoutMs =>
            let startNs ← time.monoNanosNow
            let dl := deadlineNanos startNs timeoutMs
            let now₁ ← time.monoNanosNow
            if now₁ ≥ dl then
              return .ok .noSlot
            else
              runSleepChunks time (sleepChunks (nextSleepMs cfg.pollIntervalMs now₁ dl))
              let rec spin : Nat → StateM PoolSimState (Except SlotPoolError (LeaseOutcome _))
                | 0 => return .ok .noSlot
                | f + 1 => do
                  let nowNs ← time.monoNanosNow
                  if nowNs ≥ dl then return .ok .noSlot
                  else
                    time.sleep 1
                    spin f
              spin (timeoutMs + 1)
          | _ => return .ok .noSlot }

private def buggyRetryDescendingScanOrder : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg policy action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let p0 := slotLockPath fs.join cfg.poolDir 0
          match ← fs.tryWithFileLock p0 .exclusive true (do return .ok (← action 0)) with
          | .error fe => return .error (mapFsError fe)
          | .ok (some (.error ce)) => return .error ce
          | .ok (some (.ok v)) => return .ok (.leased 0 v)
          | .ok none =>
            match policy with
            | .noWait => return .ok .noSlot
            | _ =>
              runSleepChunks time (sleepChunks cfg.pollIntervalMs)
              let hi := cfg.totalSlots - 1
              let phi := slotLockPath fs.join cfg.poolDir hi
              match ← fs.tryWithFileLock phi .exclusive true (do return .ok (← action hi)) with
              | .error fe => return .error (mapFsError fe)
              | .ok (some (.error ce)) => return .error ce
              | .ok (some (.ok v)) => return .ok (.leased hi v)
              | .ok none => return .ok .noSlot }

private def buggyWaitForeverSleepsOneMs : SlotPoolBuilder (StateM PoolSimState) :=
  fun fs time =>
    { withSlot := fun cfg _ action => do
        match validatePoolConfig cfg with
        | .error e => return .error e
        | .ok _ =>
          let _ ← fs.mkdir cfg.poolDir true true
          let p0 := slotLockPath fs.join cfg.poolDir 0
          let rec loop : Nat → StateM PoolSimState (Except SlotPoolError (LeaseOutcome _))
            | 0 => return .ok .noSlot
            | f + 1 => do
              match ← fs.tryWithFileLock p0 .exclusive true (do return .ok (← action 0)) with
              | .error fe => return .error (mapFsError fe)
              | .ok (some (.error ce)) => return .error ce
              | .ok (some (.ok v)) => return .ok (.leased 0 v)
              | .ok none =>
                time.sleep 1
                loop f
          loop 200 }

example : ¬ Core.AllPass (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan
    buggyReplacesCallbackError) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1
    { kind := .permissionDenied, message := "my-cb-err" } .noWait (by decide)
  have hEq : (Except.error { kind := .ioError, message := "overwritten callback error" } :
      Except SlotPoolError (LeaseOutcome Nat)) =
      Except.error { kind := .permissionDenied, message := "my-cb-err" } := h0.1
  injection hEq with hErr
  have hK : SlotPoolErrorKind.ioError = SlotPoolErrorKind.permissionDenied := congrArg SlotPoolError.kind hErr
  cases hK

example : ¬ Core.AllPass (test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan
    buggyRetrySwallowsCallbackError) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1
    { kind := .ioError, message := "cb failed" } .noWait (by decide)
  have hEq : (Except.ok .noSlot : Except SlotPoolError (LeaseOutcome Nat)) =
      Except.error { kind := .ioError, message := "cb failed" } := h0.2.2.2.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates
    buggyExRunsUnlocked) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 .noWait (by decide)
  have hOut : ((ExceptT.run ((buggyExRunsUnlocked simFsEx simTimeEx).withSlot
      { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } .noWait fun idx => do
        let p := slotLockPath simFsEx.join "pool" idx
        let sharedProbe ← simFsEx.tryWithFileLock p .shared false (pure (.ok ()))
        match sharedProbe with
        | .ok none =>
          if idx == 0 then
            (throw "boom" : ExceptT String (StateM PoolSimState) (Except SlotPoolError Unit))
          else
            return .ok ()
        | _ =>
          return .ok ())).run {}).1 = .ok (.ok (.leased 0 ())) := rfl
  have hEq : (Except.ok (Except.ok (.leased 0 ())) :
      Except String (Except SlotPoolError (LeaseOutcome Unit))) = Except.error "boom" :=
    hOut.symm.trans h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates
    buggyExSwallowsException) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 .noWait (by decide)
  have hEq : (Except.ok (Except.ok .noSlot) :
      Except String (Except SlotPoolError (LeaseOutcome Unit))) = Except.error "boom" := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline
    buggyWaitUpToSkipsScanAfterClampedSleep) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1 20 7 0 (by decide)
  dsimp [test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline,
    Bind.bind, Core.NondetTest.assert] at h0
  have hEq : (Except.ok .noSlot : Except SlotPoolError (LeaseOutcome Nat)) =
      Except.ok (.leased 0 7) := h0.2.2.2.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline
    buggyWaitUpToSecondPollOneMs) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1 100 7 0 (by decide)
  exact absurd h0.2.1.2 (by decide)

example : ¬ Core.AllPass (test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline
    buggyRetryDescendingScanOrder) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 } 0 1 50 7 0 (by decide)
  dsimp [test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline,
    Bind.bind, Core.NondetTest.assert] at h0
  have hEq : (Except.error { kind := .ioError, message := "wrong slot after waitUpTo" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 7) := h0.2.2.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_waitForever_contendedPool_pollsUntilSlotFree
    buggyRetryDescendingScanOrder) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 2, pollIntervalMs := 50 } 0 1 9 0 (by decide)
  have hEq : (Except.error { kind := .ioError, message := "wrong slot after waitForever" } :
      Except SlotPoolError (LeaseOutcome Nat)) = Except.ok (.leased 0 9) := h0.1.1
  cases hEq

example : ¬ Core.AllPass (test_slotpool_waitForever_contendedPool_pollsUntilSlotFree
    buggyWaitForeverSleepsOneMs) := by
  intro h
  have h0 := h { poolDir := "pool", totalSlots := 1, pollIntervalMs := 50 } 0 1 9 0 (by decide)
  exact absurd h0.2.2.1.2 (by decide)

end LeanSwe.SlotPool
