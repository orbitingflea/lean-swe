import LeanSwe.Fs.Types
import LeanSwe.Time.Types

namespace LeanSwe.SlotPool

/-- Classification of failures in `LeanSwe.SlotPool`. -/
inductive SlotPoolErrorKind where
  /-- Invalid `PoolConfig` or invalid lock target entry (such as a symbolic link). -/
  | invalidInput
  /-- Target path or ancestor component does not exist. -/
  | notFound
  /-- A non-directory entry already exists at `poolDir`. -/
  | alreadyExists
  /-- Insufficient permissions to create `poolDir` or open/lock a slot file. -/
  | permissionDenied
  /-- Expected a regular lock file at `<poolDir>/slot-<i>.lock`, found a directory. -/
  | isADirectory
  /-- Expected a directory along `poolDir`, found a non-directory entry. -/
  | notADirectory
  /-- Advisory file locking or filesystem operation is unsupported on this filesystem. -/
  | unsupported
  /-- Underlying OS or filesystem I/O failure. -/
  | ioError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed error returned by `LeanSwe.SlotPool` operations. -/
structure SlotPoolError where
  /-- Machine-checkable error category. -/
  kind : SlotPoolErrorKind
  /-- Filesystem path associated with the failure, when applicable. -/
  path : Option String := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Configuration for a directory-backed cross-process slot pool. -/
structure PoolConfig where
  /-- Directory holding `slot-0.lock` through `slot-<totalSlots - 1>.lock`. -/
  poolDir : String
  /-- Number of concurrent slots in the pool (`>= 1`). -/
  totalSlots : Nat
  /-- Sleep interval in milliseconds between contended scans (`>= 1`, default `50`). -/
  pollIntervalMs : Nat := 50
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Contention waiting strategy when every slot in a pool is locked. -/
inductive WaitPolicy where
  /-- Scan all slots once in ascending index order and return `.noSlot` immediately without sleeping if all are busy. -/
  | noWait
  /-- Poll until a slot is acquired or `timeoutMs` monotonic milliseconds elapse (`0` still performs one initial scan). -/
  | waitUpTo (timeoutMs : Nat)
  /-- Poll every `pollIntervalMs` milliseconds until a slot becomes available. -/
  | waitForever
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Outcome of attempting to acquire a single exclusive slot lease. -/
inductive LeaseOutcome (α : Type) where
  /-- Acquired exclusive lock on `slotIndex` (`< totalSlots`) and completed `action slotIndex` with `value`. -/
  | leased (slotIndex : Nat) (value : α)
  /-- Every slot remained contended for the duration permitted by `WaitPolicy`. -/
  | noSlot
  deriving Repr, BEq, DecidableEq

instance {α : Type} : Inhabited (LeaseOutcome α) := ⟨.noSlot⟩

/-- Public cross-process slot-lease operations exported by `LeanSwe.SlotPool`, parameterized over `m`. -/
structure SlotPoolApiM (m : Type → Type) where
  /-- Acquire one exclusive slot lease under `PoolConfig` and `WaitPolicy`, run `action slotIndex`, and release the slot on exit. -/
  withSlot :
    {α : Type} → PoolConfig → WaitPolicy →
      (Nat → m (Except SlotPoolError α)) →
      m (Except SlotPoolError (LeaseOutcome α))

/-- Concrete `IO` slot-pool API bundle exported by `LeanSwe.SlotPool`. -/
abbrev SlotPoolApi := SlotPoolApiM IO

/-- Builder assembling a `SlotPoolApiM m` from injected `FsApiM m` and `TimeOpsM m` capabilities. -/
abbrev SlotPoolBuilder (m : Type → Type) :=
  LeanSwe.Fs.FsApiM m → LeanSwe.Time.TimeOpsM m → SlotPoolApiM m

end LeanSwe.SlotPool
