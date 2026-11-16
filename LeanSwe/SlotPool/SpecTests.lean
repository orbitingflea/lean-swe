import Core.NondetTest
import LeanSwe.Fs.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Types
import LeanSwe.Time.Types

namespace LeanSwe.SlotPool

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Model

/-- `Model` timing and `UInt32` chunking helpers compute exact nanosecond deadlines, round positive sub-millisecond remainders up to at least `1 ms`, clamp sleeps to `pollIntervalMs`, and split arbitrary millisecond durations into positive `UInt32` chunks summing to `ms`. -/
def test_slotpool_model_timingAndSleepChunks_exactAndChunked
    {runner} [NondetTest runner]
    (ops : TimingModelOps := defaultTimingModelOps) : runner Unit := do
  let startNs ← nondet Nat
  let timeoutMs ← nondet Nat
  let nowNs ← nondet Nat
  let pollIntervalMs ← nondet Nat
  let ms ← nondet Nat
  assume (1 ≤ pollIntervalMs)
  let dl := ops.deadlineNanos startNs timeoutMs
  NondetTest.assert (dl = startNs + timeoutMs * nanosecondsPerMs)
  if nowNs ≥ dl then
    NondetTest.assert (ops.remainingWaitMs nowNs dl = 0 ∧ ops.nextSleepMs pollIntervalMs nowNs dl = 0)
  else
    let rem := ops.remainingWaitMs nowNs dl
    let nxt := ops.nextSleepMs pollIntervalMs nowNs dl
    NondetTest.assert (1 ≤ rem ∧ (rem - 1) * nanosecondsPerMs < dl - nowNs ∧ dl - nowNs ≤ rem * nanosecondsPerMs)
    NondetTest.assert (1 ≤ nxt ∧ nxt ≤ pollIntervalMs ∧ nxt ≤ rem ∧ nxt = Nat.min pollIntervalMs rem)
  let chunks := ops.sleepChunks ms
  NondetTest.assert (chunks.all (fun c => decide (0 < c.toNat)) = true)
  NondetTest.assert ((chunks.foldl (fun acc c => acc + c.toNat) 0) = ms)

/-- `withSlot` rejects every invalid `PoolConfig` (`poolDir` empty or containing NUL, `totalSlots = 0`, or `pollIntervalMs = 0`) with `.invalidInput`, `path = some cfg.poolDir`, and a non-empty message before performing any filesystem, clock, or callback effect. -/
def test_slotpool_validation_invalidConfig_rejectedBeforeEffects
    {S : Type} {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let cfg ← nondet PoolConfig
  let policy ← nondet WaitPolicy
  let markerPath ← nondet String
  assume (validPoolConfig cfg = false)
  let out := ((mkApi fs time).withSlot cfg policy fun _ => do
    let _ ← fs.writeText markerPath "ran"
    return (.ok 1 : Except SlotPoolError Nat)).run s₀
  NondetTest.assert ((∃ e, out.1 = .error e ∧ e.kind = .invalidInput ∧ e.path = some cfg.poolDir ∧ e.message ≠ "") ∧
    out.2 = s₀)

/-- When `fs.mkdir config.poolDir true true` fails, `withSlot` maps the `FsError` into a typed `SlotPoolError` with preserved `path` and non-empty message without touching the clock, locks, or callback. -/
def test_slotpool_mkdir_fsError_propagatedBeforePolling
    {S : Type} {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let cfg ← nondet PoolConfig
  let policy ← nondet WaitPolicy
  let markerPath ← nondet String
  assume (validPoolConfig cfg = true)
  let mkOut := (fs.mkdir cfg.poolDir true true).run s₀
  match mkOut.1 with
  | .ok () => assume False
  | .error fe =>
    let out := ((mkApi fs time).withSlot cfg policy fun _ => do
      let _ ← fs.writeText markerPath "ran"
      return (.ok 1 : Except SlotPoolError Nat)).run s₀
    NondetTest.assert ((∃ e, out.1 = .error e ∧ e.kind = mapFsErrorKind fe.kind ∧ e.path = fe.path ∧ e.message ≠ "") ∧
      out.2 = mkOut.2)

/-- On `WaitPolicy.noWait`, when all slots `0 .. totalSlots - 1` report contention (`.ok none`), `withSlot` probes every slot once in ascending order and returns `.ok .noSlot` without sleeping or invoking `action`. -/
def test_slotpool_noWait_allBusy_returnsNoSlotWithoutSleepOrAction
    {S : Type} {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM (S × List String)))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let cfg ← nondet PoolConfig
  let markerPath ← nondet String
  assume (validPoolConfig cfg = true)
  let mkOut := (fs.mkdir cfg.poolDir true true).run s₀
  assume (mkOut.1 = .ok ())
  assume (((fs.lstat markerPath).run mkOut.2).1.isOk = false)
  let fsLift := liftFsFirst (Aux := List String) fs
  let fsAllBusy : FsApiM (StateM (S × List String)) :=
    { fsLift with
      tryWithFileLock := fun p mode createIfMissing _ => do
        if mode == .exclusive && createIfMissing then
          modify fun (st, acc) => (st, acc ++ [p])
          return .ok none
        else
          return .error { kind := .invalidInput, path := some p, message := "unexpected lock mode or create flag" } }
  let out := ((mkApi fsAllBusy (liftTimeFirst time)).withSlot cfg .noWait fun _ => do
    let _ ← fsLift.writeText markerPath "ran"
    return (.ok 1 : Except SlotPoolError Nat)).run (s₀, [])
  NondetTest.assert (out.1 = .ok .noSlot ∧
    out.2 = (mkOut.2, expectedSlotPaths fs.join cfg.poolDir 0 cfg.totalSlots) ∧
    ((fs.lstat markerPath).run out.2.1).1.isOk = false)

/-- When `fs.tryWithFileLock` returns a filesystem `.error` on any slot `errIdx < totalSlots` (on either the initial scan or a contended retry poll), `withSlot` fails fast with the mapped `SlotPoolError` without probing higher slots or invoking `action`. -/
def test_slotpool_tryLock_fsError_propagatedWithoutRunningAction
    {S : Type} {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM (S × Nat)))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let cfg ← nondet PoolConfig
  let errIdx ← nondet Nat
  let retryPoll ← nondet Bool
  let policy ← nondet WaitPolicy
  let lockFsErr ← nondet FsError
  let markerPath ← nondet String
  assume (validPoolConfig cfg = true ∧ errIdx < cfg.totalSlots)
  let mkOut := (fs.mkdir cfg.poolDir true true).run s₀
  assume (mkOut.1 = .ok ())
  assume ((time.monoNanosNow.run mkOut.2).2 = mkOut.2)
  assume (((fs.lstat markerPath).run mkOut.2).1.isOk = false)
  let fsLift := liftFsFirst (Aux := Nat) fs
  let timeLift := liftTimeFirst (Aux := Nat) time
  if !retryPoll then
    let fsFailLock0 : FsApiM (StateM (S × Nat)) :=
      { fsLift with
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
    let out := ((mkApi fsFailLock0 timeLift).withSlot cfg policy fun _ => do
      let _ ← fsLift.writeText markerPath "ran"
      return (.ok 1 : Except SlotPoolError Nat)).run (s₀, 0)
    NondetTest.assert ((∃ e, out.1 = .error e ∧ e.kind = mapFsErrorKind lockFsErr.kind ∧ e.path = lockFsErr.path ∧ e.message ≠ "") ∧
      out.2 = (mkOut.2, errIdx + 1) ∧ ((fs.lstat markerPath).run out.2.1).1.isOk = false)
  else
    let afterSleepState := ((runSleepChunks time (sleepChunks cfg.pollIntervalMs)).run mkOut.2).2
    assume (((fs.lstat markerPath).run afterSleepState).1.isOk = false)
    let targetCall := cfg.totalSlots + errIdx
    let fsFailLock1 : FsApiM (StateM (S × Nat)) :=
      { fsLift with
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
    let retryPolicy := if policy == .noWait then .waitForever else .waitUpTo cfg.pollIntervalMs
    let out1 := ((mkApi fsFailLock1 timeLift).withSlot cfg retryPolicy fun _ => do
      let _ ← fsLift.writeText markerPath "ran"
      return (.ok 1 : Except SlotPoolError Nat)).run (s₀, 0)
    NondetTest.assert ((∃ e, out1.1 = .error e ∧ e.kind = mapFsErrorKind lockFsErr.kind ∧ e.path = lockFsErr.path ∧ e.message ≠ "") ∧
      out1.2 = (afterSleepState, targetCall + 1) ∧ ((fs.lstat markerPath).run out1.2.1).1.isOk = false)

/-- Over an arbitrary monotonic `TimeOpsM (StateM S)`, `WaitPolicy.waitUpTo` returns `.ok .noSlot` without sleeping when already expired (`nowNs >= deadlineNs`, including `waitUpTo 0`), and across one or multiple contended polls rounds positive sub-millisecond remainders up to `>= 1 ms`, clamps to `min pollIntervalMs remainingMs`, and chunks sleeps across `UInt32.max`. -/
def test_slotpool_waitUpTo_arbitraryClock_clampsRoundsUpAndChunksSleep
    {S : Type} {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM S))
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let cfg ← nondet PoolConfig
  let timeoutMs ← nondet Nat
  assume (validPoolConfig cfg = true)
  assume (timeoutMs < maxForeverPolls)
  let mkOut := (fs.mkdir cfg.poolDir true true).run s₀
  assume (mkOut.1 = .ok ())
  let fsAllBusy : FsApiM (StateM S) :=
    { fs with
      tryWithFileLock := fun p mode createIfMissing _ =>
        if mode == .exclusive && createIfMissing then
          pure (.ok none)
        else
          pure (.error { kind := .invalidInput, path := some p, message := "unexpected lock mode or create flag" }) }
  let startOut := time.monoNanosNow.run mkOut.2
  let dl := deadlineNanos startOut.1 timeoutMs
  let nowOut₁ := time.monoNanosNow.run startOut.2
  assume (startOut.1 ≤ nowOut₁.1)
  if nowOut₁.1 ≥ dl then
    let out := ((mkApi fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
      pure (.ok 1 : Except SlotPoolError Nat)).run s₀
    NondetTest.assert (out.1 = .ok .noSlot ∧ out.2 = nowOut₁.2)
  else
    let sleepDur₁ := nextSleepMs cfg.pollIntervalMs nowOut₁.1 dl
    let sleepOut₁ := (runSleepChunks time (sleepChunks sleepDur₁)).run nowOut₁.2
    let nowOut₂ := time.monoNanosNow.run sleepOut₁.2
    if nowOut₂.1 ≥ dl then
      let out := ((mkApi fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
        pure (.ok 1 : Except SlotPoolError Nat)).run s₀
      NondetTest.assert (1 ≤ sleepDur₁ ∧ sleepDur₁ ≤ cfg.pollIntervalMs ∧ out.1 = .ok .noSlot ∧ out.2 = nowOut₂.2)
    else
      let sleepDur₂ := nextSleepMs cfg.pollIntervalMs nowOut₂.1 dl
      let sleepOut₂ := (runSleepChunks time (sleepChunks sleepDur₂)).run nowOut₂.2
      let nowOut₃ := time.monoNanosNow.run sleepOut₂.2
      assume (nowOut₃.1 ≥ dl)
      let out := ((mkApi fsAllBusy time).withSlot cfg (.waitUpTo timeoutMs) fun _ =>
        pure (.ok 1 : Except SlotPoolError Nat)).run s₀
      NondetTest.assert (1 ≤ sleepDur₁ ∧ sleepDur₁ ≤ cfg.pollIntervalMs ∧
        1 ≤ sleepDur₂ ∧ sleepDur₂ ≤ cfg.pollIntervalMs ∧ out.1 = .ok .noSlot ∧ out.2 = nowOut₃.2)

/-- `withSlot` creates `cfg.poolDir` (`parents = true`, `existOk = true`), scans `slot-0.lock` .. `slot-<totalSlots - 1>.lock` in ascending order (including on `waitUpTo 0`), acquires the lowest free slot with `.exclusive` and `createIfMissing = true`, holds the `.exclusive` lock during `action`, and releases it on `.ok` while preserving the lock file on disk. -/
def test_slotpool_acquire_freeSlot_honorsPoolDirAscendingOrderAndExclusiveLock
    {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM PoolSimState)) : runner Unit := do
  let cfg ← nondet PoolConfig
  let freeIdx ← nondet Nat
  let val ← nondet Nat
  let policy ← nondet WaitPolicy
  let dirPreExists ← nondet Bool
  let startMono ← nondet Nat
  assume (validPoolConfig cfg = true ∧ freeIdx < cfg.totalSlots)
  let s₀ : PoolSimState :=
    { dirs := if dirPreExists then [normSimPath cfg.poolDir] else []
      externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (startMono + 1000000000) freeIdx
      monoNanos := startMono }
  let expectedLockPath := slotLockPath simFs.join cfg.poolDir freeIdx
  let out := ((mkApi simFs simTime).withSlot cfg policy fun idx => do
    let p := slotLockPath simFs.join cfg.poolDir idx
    let sharedProbe ← simFs.tryWithFileLock p .shared false (pure (.ok ()))
    match sharedProbe with
    | .ok none =>
      if idx == freeIdx && idx < cfg.totalSlots then
        return .ok val
      else
        return .error { kind := .ioError, path := some p, message := "slot index invariant failed" }
    | _ =>
      return .error { kind := .ioError, path := some p, message := "exclusive lock invariant failed" }).run s₀
  let postOut := (simFs.tryWithFileLock expectedLockPath .exclusive false (pure (.ok ()))).run out.2
  let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
  NondetTest.assert (out.1 = .ok (.leased freeIdx val) ∧ freeIdx < cfg.totalSlots)
  NondetTest.assert (out.2.heldLocks = [] ∧ postOut.1 = .ok (some ()))
  NondetTest.assert (freeIdx + 1 ≥ cfg.totalSlots ∨ hasSimFile out.2 nextPath = false)
  NondetTest.assert (out.2.sleepLog = #[] ∧ out.2.monoNanos = startMono)

/-- When `action` returns `.error callbackErr` on `freeIdx < totalSlots` (either immediately or after contended retry polls), `withSlot` releases the held `.exclusive` slot lock without unlinking the file, does not advance to higher free slots or keep polling, and returns `.error callbackErr` verbatim. -/
def test_slotpool_callbackError_acquiredSlot_preservesErrorReleasesLockAndStopsScan
    {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM PoolSimState)) : runner Unit := do
  let cfg ← nondet PoolConfig
  let freeIdx ← nondet Nat
  let retryRounds ← nondet Nat
  let callbackErr ← nondet SlotPoolError
  let policy ← nondet WaitPolicy
  assume (validPoolConfig cfg = true ∧ freeIdx < cfg.totalSlots ∧ 1 ≤ retryRounds ∧ retryRounds < maxForeverPolls)
  let freePath := slotLockPath simFs.join cfg.poolDir freeIdx
  let cbAction : Nat → StateM PoolSimState (Except SlotPoolError Nat) := fun idx => do
    if idx == freeIdx then
      let sharedProbe ← simFs.tryWithFileLock freePath .shared false (pure (.ok ()))
      match sharedProbe with
      | .ok none =>
        return (Except.error callbackErr : Except SlotPoolError Nat)
      | _ =>
        return .error { kind := .ioError, message := "target slot was not locked exclusive" }
    else
      let _ ← simFs.writeText "ran-other" "bad"
      return (.ok 99 : Except SlotPoolError Nat)
  let s₀ : PoolSimState :=
    { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx }
  let out := ((mkApi simFs simTime).withSlot cfg policy cbAction).run s₀
  let postOut := (simFs.tryWithFileLock freePath .exclusive false (pure (.ok ()))).run out.2
  NondetTest.assert (out.1 = .error callbackErr)
  NondetTest.assert (out.2.heldLocks = [] ∧ postOut.1 = .ok (some ()))
  NondetTest.assert (hasSimFile out.2 "ran-other" = false ∧ out.2.sleepLog = #[])
  let targetRelNs := retryRounds * cfg.pollIntervalMs * nanosecondsPerMs
  let lockedUntilNs := targetRelNs + cfg.pollIntervalMs * nanosecondsPerMs
  let sRetry : PoolSimState :=
    { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs lockedUntilNs cfg.totalSlots }
  let retryPolicy := if policy == .noWait then .waitForever else .waitUpTo (retryRounds * cfg.pollIntervalMs)
  let retryOut := ((mkApi simFs simTime).withSlot cfg retryPolicy cbAction).run sRetry
  let retryPostOut := (simFs.tryWithFileLock freePath .exclusive false (pure (.ok ()))).run retryOut.2
  NondetTest.assert (retryOut.1 = .error callbackErr ∧ retryOut.2.heldLocks = [] ∧ retryPostOut.1 = .ok (some ()))
  NondetTest.assert (hasSimFile retryOut.2 "ran-other" = false ∧ retryOut.2.monoNanos = targetRelNs)

/-- Over `ExceptT String (StateM PoolSimState)`, an uncaught monadic exception thrown while holding `freeIdx < totalSlots` `.exclusive` releases the slot lock via `MonadFinally`, preserves the lock file on disk, and propagates the exception. -/
def test_slotpool_monadFinally_uncaughtException_releasesLockAndPropagates
    {runner} [NondetTest runner]
    (mkExApi : SlotPoolBuilder (ExceptT String (StateM PoolSimState))) : runner Unit := do
  let cfg ← nondet PoolConfig
  let freeIdx ← nondet Nat
  let policy ← nondet WaitPolicy
  assume (validPoolConfig cfg = true ∧ freeIdx < cfg.totalSlots)
  let s₀ : PoolSimState :=
    { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir 1000000000 freeIdx }
  let freePath := slotLockPath simFs.join cfg.poolDir freeIdx
  let out := (ExceptT.run ((mkExApi simFsEx simTimeEx).withSlot cfg policy fun idx => do
    let p := slotLockPath simFsEx.join cfg.poolDir idx
    let sharedProbe ← simFsEx.tryWithFileLock p .shared false (pure (.ok ()))
    match sharedProbe with
    | .ok none =>
      if idx == freeIdx then
        (throw "boom" : ExceptT String (StateM PoolSimState) (Except SlotPoolError Unit))
      else
        return .ok ()
    | _ =>
      return .ok ())).run s₀
  let postOut := (simFs.tryWithFileLock freePath .exclusive false (pure (.ok ()))).run out.2
  NondetTest.assert (out.1 = .error "boom" ∧ out.2.heldLocks = [] ∧ postOut.1 = .ok (some ()))

/-- On a contended pool under `WaitPolicy.waitUpTo timeoutMs`, `withSlot` emits `expectedPollSleepLog`, acquires the lowest freed slot on both full-interval and clamped-remainder polls without touching higher slots, and expires at exact `deadlineNs` without running `action` when all slots stay busy. -/
def test_slotpool_waitUpTo_contendedPool_pollsAcquiresOrExpiresAtDeadline
    {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM PoolSimState)) : runner Unit := do
  let cfg ← nondet PoolConfig
  let freeIdx ← nondet Nat
  let rounds ← nondet Nat
  let timeoutMs ← nondet Nat
  let val ← nondet Nat
  let startMono ← nondet Nat
  assume (validPoolConfig cfg = true ∧ freeIdx < cfg.totalSlots ∧ timeoutMs < maxForeverPolls)
  let dl := deadlineNanos startMono timeoutMs
  let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
  let sExpire : PoolSimState :=
    { externalLeases := leasesBeforeSlot simFs.join cfg.poolDir (dl + 1) cfg.totalSlots
      monoNanos := startMono }
  let expOut := ((mkApi simFs simTime).withSlot cfg (.waitUpTo timeoutMs) fun _ => do
    let _ ← simFs.writeText "ran-expired" "bad"
    return (.ok val : Except SlotPoolError Nat)).run sExpire
  NondetTest.assert (expOut.1 = .ok .noSlot ∧ hasSimFile expOut.2 "ran-expired" = false ∧ expOut.2.heldLocks = [])
  NondetTest.assert (expOut.2.monoNanos = dl ∧
    expOut.2.sleepLog.toList = expectedPollSleepLog cfg.pollIntervalMs timeoutMs)
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
  if 1 ≤ rounds ∧ rounds * cfg.pollIntervalMs ≤ timeoutMs then
    let targetRelNs := startMono + rounds * cfg.pollIntervalMs * nanosecondsPerMs
    let sAcquire : PoolSimState :=
      { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let acqOut := ((mkApi simFs simTime).withSlot cfg (.waitUpTo timeoutMs) verifySlotAction).run sAcquire
    NondetTest.assert (acqOut.1 = .ok (.leased freeIdx val) ∧ acqOut.2.heldLocks = [] ∧
      acqOut.2.monoNanos = targetRelNs ∧ acqOut.2.monoNanos ≤ dl ∧
      (freeIdx + 1 ≥ cfg.totalSlots ∨ hasSimFile acqOut.2 nextPath = false))
  else
    NondetTest.assert True
  if 1 ≤ timeoutMs then
    let sAcquireDl : PoolSimState :=
      { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx dl (dl + 1) cfg.totalSlots
        monoNanos := startMono }
    let acqDlOut := ((mkApi simFs simTime).withSlot cfg (.waitUpTo timeoutMs) verifySlotAction).run sAcquireDl
    NondetTest.assert (acqDlOut.1 = .ok (.leased freeIdx val) ∧ acqDlOut.2.heldLocks = [] ∧
      acqDlOut.2.monoNanos = dl ∧
      (freeIdx + 1 ≥ cfg.totalSlots ∨ hasSimFile acqDlOut.2 nextPath = false))
  else
    NondetTest.assert True

/-- On a contended pool under `WaitPolicy.waitForever`, `withSlot` emits `repeatSleepChunks cfg.pollIntervalMs rounds`, acquires the lowest freed slot `freeIdx < totalSlots` `.exclusive` without touching higher slots, and releases it on exit. -/
def test_slotpool_waitForever_contendedPool_pollsUntilSlotFree
    {runner} [NondetTest runner]
    (mkApi : SlotPoolBuilder (StateM PoolSimState)) : runner Unit := do
  let cfg ← nondet PoolConfig
  let freeIdx ← nondet Nat
  let rounds ← nondet Nat
  let val ← nondet Nat
  let startMono ← nondet Nat
  assume (validPoolConfig cfg = true ∧ freeIdx < cfg.totalSlots ∧ 1 ≤ rounds ∧ rounds < maxForeverPolls)
  let targetRelNs := startMono + rounds * cfg.pollIntervalMs * nanosecondsPerMs
  let otherRelNs := targetRelNs + cfg.pollIntervalMs * nanosecondsPerMs
  let nextPath := normSimPath (slotLockPath simFs.join cfg.poolDir (freeIdx + 1))
  let s₀ : PoolSimState :=
    { externalLeases := leasesBeforeSlotUntil simFs.join cfg.poolDir freeIdx targetRelNs otherRelNs cfg.totalSlots
      monoNanos := startMono }
  let out := ((mkApi simFs simTime).withSlot cfg .waitForever fun idx => do
    let p := slotLockPath simFs.join cfg.poolDir idx
    let sharedProbe ← simFs.tryWithFileLock p .shared false (pure (.ok ()))
    match sharedProbe with
    | .ok none =>
      if idx == freeIdx then
        return .ok val
      else
        return .error { kind := .ioError, message := "wrong slot after waitForever" }
    | _ =>
      return .error { kind := .ioError, message := "wrong lock mode after waitForever" }).run s₀
  NondetTest.assert (out.1 = .ok (.leased freeIdx val) ∧ out.2.heldLocks = [])
  NondetTest.assert (freeIdx + 1 ≥ cfg.totalSlots ∨ hasSimFile out.2 nextPath = false)
  NondetTest.assert (out.2.monoNanos = targetRelNs ∧
    out.2.sleepLog.toList = repeatSleepChunks cfg.pollIntervalMs rounds)

/-- External OS kernel and multi-process advisory-locking assumptions grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- Multi-process POSIX `flock(2)` (`LOCK_EX | LOCK_NB` with `O_NOFOLLOW | O_CLOEXEC`) enforces mutual exclusion across child processes on `<poolDir>/slot-<i>.lock`, routing concurrent callers onto disjoint slots in `[0, totalSlots)`. -/
  multiProcessFlockMutualExclusion : Prop
  /-- Kernel open-file-description cleanup releases held `<poolDir>/slot-<i>.lock` advisory locks automatically when a callback throws `IO.Error` or a leaseholder subprocess is terminated via `SIGKILL`. -/
  kernelReleasesSlotLockOnExceptionAndSigkill : Prop
  /-- Real `IO.monoNanosNow` and `IO.sleep` satisfy `WaitPolicy.noWait`, `WaitPolicy.waitUpTo`, and `WaitPolicy.waitForever` wakeup and timeout contracts inside `LeanSwe.TempDir.withTempDir`. -/
  monotonicClockWaitPoliciesInTempDir : Prop

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
