import LeanSwe.Fs.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Types
import LeanSwe.Time.Types

namespace LeanSwe.SlotPool.Internal

open LeanSwe.Fs (FsApiM)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.SlotPool.Model

/-- Internal result of a single ascending scan across `0 .. totalSlots - 1`. -/
inductive ScanOutcome (α : Type) where
  /-- Acquired slot `slotIndex` and completed `action slotIndex` with `value`. -/
  | leased (slotIndex : Nat) (value : α)
  /-- Every scanned slot was busy under non-blocking lock acquisition. -/
  | allBusy
  /-- Aborted scan due to a filesystem error or callback error. -/
  | err (error : SlotPoolError)

/-- Scan `rem` slots starting at `nextIdx` in ascending order, taking the first free exclusive lock. -/
def scanSlotsM {m : Type → Type} {α : Type} [Monad m]
    (fs : FsApiM m) (poolDir : String) (nextIdx : Nat) :
    Nat → (Nat → m (Except SlotPoolError α)) → m (ScanOutcome α)
  | 0, _ => return .allBusy
  | rem + 1, action => do
    let lockPath := slotLockPath fs.join poolDir nextIdx
    match ← fs.tryWithFileLock lockPath .exclusive true (do return .ok (← action nextIdx)) with
    | .error fe => return .err (mapFsError fe)
    | .ok none => scanSlotsM fs poolDir (nextIdx + 1) rem action
    | .ok (some (.error cbErr)) => return .err cbErr
    | .ok (some (.ok val)) => return .leased nextIdx val

/-- Poll contended slots under `WaitPolicy.waitUpTo` using structural fuel `fuel` until acquisition or `deadlineNs`. -/
def pollWaitUpToM {m : Type → Type} {α : Type} [Monad m]
    (fs : FsApiM m) (time : TimeOpsM m) (cfg : PoolConfig) (deadlineNs : Nat)
    (action : Nat → m (Except SlotPoolError α)) :
    Nat → m (Except SlotPoolError (LeaseOutcome α))
  | 0 => return .ok .noSlot
  | fuel + 1 => do
    match ← scanSlotsM fs cfg.poolDir 0 cfg.totalSlots action with
    | .leased idx val => return .ok (.leased idx val)
    | .err e => return .error e
    | .allBusy =>
      let nowNs ← time.monoNanosNow
      if nowNs ≥ deadlineNs then
        return .ok .noSlot
      else
        let dur := nextSleepMs cfg.pollIntervalMs nowNs deadlineNs
        runSleepChunks time (sleepChunks dur)
        pollWaitUpToM fs time cfg deadlineNs action fuel

/-- Poll contended slots under `WaitPolicy.waitForever` using structural fuel `fuel` until acquisition. -/
def pollForeverM {m : Type → Type} {α : Type} [Monad m]
    (fs : FsApiM m) (time : TimeOpsM m) (cfg : PoolConfig)
    (action : Nat → m (Except SlotPoolError α)) :
    Nat → m (Except SlotPoolError (LeaseOutcome α))
  | 0 => return .ok .noSlot
  | fuel + 1 => do
    match ← scanSlotsM fs cfg.poolDir 0 cfg.totalSlots action with
    | .leased idx val => return .ok (.leased idx val)
    | .err e => return .error e
    | .allBusy =>
      runSleepChunks time (sleepChunks cfg.pollIntervalMs)
      pollForeverM fs time cfg action fuel

/-- Validate `cfg`, ensure `cfg.poolDir` exists, and acquire/release a single exclusive slot lease. -/
def withSlotM {m : Type → Type} {α : Type} [Monad m]
    (fs : FsApiM m) (time : TimeOpsM m) (cfg : PoolConfig) (policy : WaitPolicy)
    (action : Nat → m (Except SlotPoolError α)) : m (Except SlotPoolError (LeaseOutcome α)) := do
  match validatePoolConfig cfg with
  | .error e => return .error e
  | .ok _ =>
    match ← fs.mkdir cfg.poolDir true true with
    | .error fe => return .error (mapFsError fe)
    | .ok () =>
      match policy with
      | .noWait =>
        match ← scanSlotsM fs cfg.poolDir 0 cfg.totalSlots action with
        | .leased idx val => return .ok (.leased idx val)
        | .err e => return .error e
        | .allBusy => return .ok .noSlot
      | .waitUpTo timeoutMs =>
        let startNs ← time.monoNanosNow
        let dl := deadlineNanos startNs timeoutMs
        pollWaitUpToM fs time cfg dl action maxForeverPolls
      | .waitForever =>
        pollForeverM fs time cfg action maxForeverPolls

/-- Assemble a `SlotPoolApiM m` from injected `FsApiM m` and `TimeOpsM m` capabilities. -/
def mkApiM {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  fun fs time =>
    { withSlot := fun cfg policy action => withSlotM fs time cfg policy action }

end LeanSwe.SlotPool.Internal
