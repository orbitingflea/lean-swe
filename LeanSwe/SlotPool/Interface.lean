import LeanSwe.Fs.Interface
import LeanSwe.SlotPool.Impl
import LeanSwe.SlotPool.Types
import LeanSwe.Time.Interface

namespace LeanSwe.SlotPool

/-- Construct a `SlotPoolApiM m` over custom `FsApiM m` and `TimeOpsM m` capability interfaces. -/
@[inline] def mkApiM {m : Type → Type} [Monad m] : SlotPoolBuilder m :=
  Internal.mkApiM

/-- Default concrete `IO` slot-pool API bundle backed by `LeanSwe.Fs.defaultApi` and `LeanSwe.Time.defaultOps`. -/
def defaultApi : SlotPoolApi :=
  mkApiM LeanSwe.Fs.defaultApi LeanSwe.Time.defaultOps

/-- Acquire one exclusive slot lease under `cfg` and `policy`, run `action slotIndex`, and release the lock on exit. -/
@[inline] def withSlot {α : Type} (cfg : PoolConfig) (policy : WaitPolicy)
    (action : Nat → IO (Except SlotPoolError α)) : IO (Except SlotPoolError (LeaseOutcome α)) :=
  defaultApi.withSlot cfg policy action

end LeanSwe.SlotPool
