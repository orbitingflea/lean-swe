import LeanSwe.Fs.Types
import LeanSwe.SlotPool.Model
import LeanSwe.SlotPool.Types
import LeanSwe.Time.Types

/-!
Pure domain state-transition model and single-step refinement specification for
`LeanSwe.SlotPool` over `PoolSimState` (`FsApiM`, `TimeOpsM`, and `SlotPoolApiM`).
-/

namespace LeanSwe.SlotPool.Model

open LeanSwe.Fs (FsApiM FsError LockMode)
open LeanSwe.Time (TimeOpsM)

/-- Finite pure callback action supplied to `SlotPoolApiM.withSlot` during single-step refinement. -/
inductive StepAction where
  /-- Succeed on the acquired `slotIndex`, returning `slotIndex + tag`. -/
  | retSlot (tag : Nat)
  /-- Fail inside the lease callback with `err`. -/
  | retErr (err : SlotPoolError)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Evaluate a `StepAction` on acquired `slotIndex`. -/
def evalStepAction (slotIndex : Nat) : StepAction → Except SlotPoolError Nat
  | .retSlot tag => .ok (slotIndex + tag)
  | .retErr err => .error err

/-- Pure `mkdir` state transition on `PoolSimState`. -/
def specMkdir (s : PoolSimState) (path : String) (parents existOk : Bool) :
    Except FsError Unit × PoolSimState :=
  match simMkdirPure s path parents existOk with
  | .error fe => (.error fe, s)
  | .ok s' => (.ok (), s')

/-- Pure bracketed `tryWithFileLock` transition for a pure returning callback `res` on `PoolSimState`. -/
def specTryLockRet (s : PoolSimState) (lockPath : String) (mode : LockMode) (createIfMissing : Bool)
    (res : Except SlotPoolError Nat) :
    Except FsError (Option (Except SlotPoolError Nat)) × PoolSimState :=
  match simTryAcquirePure s lockPath mode createIfMissing with
  | .error fe => (.error fe, s)
  | .ok none => (.ok none, s)
  | .ok (some sLocked) =>
    (.ok (some res), { sLocked with heldLocks := removeFirstSimLock (normSimPath lockPath) mode sLocked.heldLocks })

/-- Pure single-chunk sleep transition advancing `monoNanos` and appending `ms` to `sleepLog`. -/
def specSleepStep (s : PoolSimState) (ms : UInt32) : PoolSimState :=
  { s with
    monoNanos := s.monoNanos + ms.toNat * nanosecondsPerMs
    sleepLog := s.sleepLog.push ms }

/-- Closed-form duration sleep transition advancing `monoNanos` by `durMs` milliseconds and logging `sleepChunks durMs`. -/
def specSleepDuration (s : PoolSimState) (durMs : Nat) : PoolSimState :=
  { s with
    monoNanos := s.monoNanos + durMs * nanosecondsPerMs
    sleepLog := s.sleepLog ++ (sleepChunks durMs).toArray }

/-- Pure ascending slot scan over `PoolSimState` from `nextIdx` across `rem` slots. -/
def specScanSlots (s : PoolSimState) (poolDir : String) (act : StepAction)
    (nextIdx : Nat) : Nat → Except SlotPoolError (LeaseOutcome Nat) × PoolSimState
  | 0 => (.ok .noSlot, s)
  | rem + 1 =>
    let lockPath := slotLockPath simJoin poolDir nextIdx
    match simTryAcquirePure s lockPath .exclusive true with
    | .error fe => (.error (mapFsError fe), s)
    | .ok none => specScanSlots s poolDir act (nextIdx + 1) rem
    | .ok (some sLocked) =>
      let s' := { sLocked with heldLocks := removeFirstSimLock (normSimPath lockPath) .exclusive sLocked.heldLocks }
      match evalStepAction nextIdx act with
      | .error cbErr => (.error cbErr, s')
      | .ok val => (.ok (.leased nextIdx val), s')

/-- Pure bounded-deadline polling transition over `PoolSimState` using structural `fuel`. -/
def specPollWaitUpTo (s : PoolSimState) (cfg : PoolConfig) (deadlineNs : Nat)
    (act : StepAction) : Nat → Except SlotPoolError (LeaseOutcome Nat) × PoolSimState
  | 0 => (.ok .noSlot, s)
  | fuel + 1 =>
    match specScanSlots s cfg.poolDir act 0 cfg.totalSlots with
    | (.ok (.leased idx val), s') => (.ok (.leased idx val), s')
    | (.error e, s') => (.error e, s')
    | (.ok .noSlot, s') =>
      if s'.monoNanos ≥ deadlineNs then
        (.ok .noSlot, s')
      else
        let dur := nextSleepMs cfg.pollIntervalMs s'.monoNanos deadlineNs
        specPollWaitUpTo (specSleepDuration s' dur) cfg deadlineNs act fuel

/-- Pure unbounded polling transition over `PoolSimState` using structural `fuel`. -/
def specPollForever (s : PoolSimState) (cfg : PoolConfig)
    (act : StepAction) : Nat → Except SlotPoolError (LeaseOutcome Nat) × PoolSimState
  | 0 => (.ok .noSlot, s)
  | fuel + 1 =>
    match specScanSlots s cfg.poolDir act 0 cfg.totalSlots with
    | (.ok (.leased idx val), s') => (.ok (.leased idx val), s')
    | (.error e, s') => (.error e, s')
    | (.ok .noSlot, s') =>
      specPollForever (specSleepDuration s' cfg.pollIntervalMs) cfg act fuel

/-- Pure domain transition for `SlotPoolApiM.withSlot` over `PoolSimState`. -/
def specWithSlot (s : PoolSimState) (cfg : PoolConfig) (policy : WaitPolicy) (act : StepAction) :
    Except SlotPoolError (LeaseOutcome Nat) × PoolSimState :=
  match validatePoolConfig cfg with
  | .error e => (.error e, s)
  | .ok _ =>
    match simMkdirPure s cfg.poolDir true true with
    | .error fe => (.error (mapFsError fe), s)
    | .ok s1 =>
      match policy with
      | .noWait => specScanSlots s1 cfg.poolDir act 0 cfg.totalSlots
      | .waitUpTo timeoutMs =>
        specPollWaitUpTo s1 cfg (deadlineNanos s1.monoNanos timeoutMs) act maxForeverPolls
      | .waitForever =>
        specPollForever s1 cfg act maxForeverPolls

/-- Total well-formedness guard on `PoolSimState` for `Core.RefinesStepFrom2`. -/
def slotPoolStepWf (_ : PoolSimState) : Bool := true

/-- Single-step filesystem capability request sum invoked by `LeanSwe.SlotPool`. -/
inductive FsStepReq where
  /-- Pure path join `fs.join base sub`. -/
  | join (base sub : String)
  /-- Directory creation `fs.mkdir path parents existOk`. -/
  | mkdir (path : String) (parents existOk : Bool)
  /-- Non-blocking advisory lock `fs.tryWithFileLock path mode createIfMissing (pure (.ok res))`. -/
  | tryLockRet (path : String) (mode : LockMode) (createIfMissing : Bool)
      (res : Except SlotPoolError Nat)
  deriving Repr, Inhabited

/-- Single-step output sum for `FsStepReq`. -/
inductive FsStepOut where
  /-- Joined path string from `FsStepReq.join`. -/
  | path (s : String)
  /-- Directory creation outcome from `FsStepReq.mkdir`. -/
  | mkdirRes (res : Except FsError Unit)
  /-- Non-blocking lock outcome from `FsStepReq.tryLockRet`. -/
  | tryLockRes (res : Except FsError (Option (Except SlotPoolError Nat)))
  deriving Repr, Inhabited

/-- Execute one `FsStepReq` against an arbitrary `FsApiM (StateM W)`. -/
def execFsStep {W : Type} (fs : FsApiM (StateM W)) : FsStepReq → StateM W FsStepOut
  | .join base sub => pure (.path (fs.join base sub))
  | .mkdir path parents existOk => .mkdirRes <$> fs.mkdir path parents existOk
  | .tryLockRet path mode createIfMissing res =>
    .tryLockRes <$> fs.tryWithFileLock path mode createIfMissing (pure (.ok res))

/-- Pure single-step evaluator for `FsStepReq` over `PoolSimState`. -/
def evalFsStep (s : PoolSimState) : FsStepReq → FsStepOut × PoolSimState
  | .join base sub => (.path (simJoin base sub), s)
  | .mkdir path parents existOk =>
    let (r, s') := specMkdir s path parents existOk
    (.mkdirRes r, s')
  | .tryLockRet path mode createIfMissing res =>
    let (r, s') := specTryLockRet s path mode createIfMissing res
    (.tryLockRes r, s')

/-- Allowed deterministic single-step relation for `FsApiM` over `PoolSimState`. -/
def allowedFsStep (s : PoolSimState) (req : FsStepReq) (out : FsStepOut) (s' : PoolSimState) : Prop :=
  let r := evalFsStep s req
  out = r.1 ∧ s' = r.2

/-- Single-step monotonic clock/sleep capability request sum invoked by `LeanSwe.SlotPool`. -/
inductive TimeStepReq where
  /-- Read monotonic clock in nanoseconds (`time.monoNanosNow`). -/
  | monoNanosNow
  /-- Sleep for `ms` milliseconds (`time.sleep ms`). -/
  | sleep (ms : UInt32)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single-step output sum for `TimeStepReq`. -/
inductive TimeStepOut where
  /-- Monotonic timestamp in nanoseconds from `TimeStepReq.monoNanosNow`. -/
  | nanos (ns : Nat)
  /-- Unit completion from `TimeStepReq.sleep`. -/
  | slept
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Execute one `TimeStepReq` against an arbitrary `TimeOpsM (StateM W)`. -/
def execTimeStep {W : Type} (time : TimeOpsM (StateM W)) : TimeStepReq → StateM W TimeStepOut
  | .monoNanosNow => .nanos <$> time.monoNanosNow
  | .sleep ms => do
    time.sleep ms
    return .slept

/-- Pure single-step evaluator for `TimeStepReq` over `PoolSimState`. -/
def evalTimeStep (s : PoolSimState) : TimeStepReq → TimeStepOut × PoolSimState
  | .monoNanosNow => (.nanos s.monoNanos, s)
  | .sleep ms => (.slept, specSleepStep s ms)

/-- Allowed deterministic single-step relation for `TimeOpsM` over `PoolSimState`. -/
def allowedTimeStep (s : PoolSimState) (req : TimeStepReq) (out : TimeStepOut) (s' : PoolSimState) : Prop :=
  let r := evalTimeStep s req
  out = r.1 ∧ s' = r.2

/-- Public request sum covering `SlotPoolApiM.withSlot` inside `Core.RefinesStepFrom2`. -/
inductive PkgStepReq where
  /-- Acquire one exclusive slot lease under `cfg` and `policy`, running `evalStepAction idx act`. -/
  | withSlot (cfg : PoolConfig) (policy : WaitPolicy) (act : StepAction)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Output wrapper for `PkgStepReq` transitions in `Core.RefinesStepFrom2`. -/
inductive PkgStepOut where
  /-- Lease outcome or `SlotPoolError` returned by `SlotPoolApiM.withSlot`. -/
  | leaseRes (res : Except SlotPoolError (LeaseOutcome Nat))
  deriving Repr, Inhabited

/-- Execute one `PkgStepReq` against an arbitrary `SlotPoolApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : SlotPoolApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .withSlot cfg policy act =>
    .leaseRes <$> api.withSlot cfg policy (fun idx => pure (evalStepAction idx act))

/-- Pure single-step evaluator for `PkgStepReq` over `PoolSimState`. -/
def evalPkgStep (s : PoolSimState) : PkgStepReq → PkgStepOut × PoolSimState
  | .withSlot cfg policy act =>
    let (r, s') := specWithSlot s cfg policy act
    (.leaseRes r, s')

/-- Allowed deterministic single-step relation for `SlotPoolApiM` over `PoolSimState`. -/
def allowedPkgStep (s : PoolSimState) (req : PkgStepReq) (out : PkgStepOut) (s' : PoolSimState) : Prop :=
  let r := evalPkgStep s req
  out = r.1 ∧ s' = r.2

end LeanSwe.SlotPool.Model
