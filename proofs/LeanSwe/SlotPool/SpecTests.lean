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

end LeanSwe.SlotPool
