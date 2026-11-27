import LeanSwe.Fs.Types
import LeanSwe.SlotPool.Types
import LeanSwe.Time.Types

namespace LeanSwe.SlotPool.Internal

open LeanSwe.Fs (FsApiM FsError FsErrorKind)
open LeanSwe.Time (TimeOpsM)

/-- Nanoseconds in one millisecond (`1_000_000`). -/
def nanosecondsPerMs : Nat := 1000000

/-- Maximum milliseconds accepted by a single `UInt32` `TimeOpsM.sleep` call (`2 ^ 32 - 1`). -/
def maxSleepChunkMs : Nat := 4294967295

/-- Structural poll bound for `WaitPolicy.waitForever` (`2 ^ 64` polls). -/
def maxForeverPolls : Nat := 2 ^ 64

/-- Return `true` iff `cs` contains a NUL character (`'\x00'`). -/
def hasNulChar : List Char → Bool
  | [] => false
  | c :: cs => c == Char.ofNat 0 || hasNulChar cs

/-- Return `true` iff `poolDir` is non-empty and contains no NUL byte. -/
def validPoolDir (poolDir : String) : Bool :=
  !poolDir.isEmpty && !hasNulChar poolDir.toList

/-- Validate `cfg` at the API boundary, returning `.invalidInput` when `cfg` is malformed. -/
def validatePoolConfig (cfg : PoolConfig) : Except SlotPoolError PoolConfig :=
  if !validPoolDir cfg.poolDir then
    .error { kind := .invalidInput, path := some cfg.poolDir, message := "invalid pool directory path" }
  else if cfg.totalSlots == 0 then
    .error { kind := .invalidInput, path := some cfg.poolDir, message := "totalSlots must be at least 1" }
  else if cfg.pollIntervalMs == 0 then
    .error { kind := .invalidInput, path := some cfg.poolDir, message := "pollIntervalMs must be at least 1" }
  else
    .ok cfg

/-- Single ASCII decimal digit character `'0'` through `'9'` for `d < 10`. -/
def decDigitChar (d : Nat) : Char :=
  Char.ofNat (48 + d)

/-- Structurally recursive base-10 digit formatter prepending digits onto `acc`. -/
def natDecCharsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d := decDigitChar (n % 10)
    let q := n / 10
    if q == 0 then
      d :: acc
    else
      natDecCharsAux fuel q (d :: acc)

/-- Format `n` as a base-10 ASCII decimal string using structural recursion. -/
def natDecString (n : Nat) : String :=
  String.ofList (natDecCharsAux (n + 1) n [])

/-- Canonical lock filename `"slot-<slotIndex>.lock"` for `slotIndex`. -/
def slotFileName (slotIndex : Nat) : String :=
  "slot-" ++ natDecString slotIndex ++ ".lock"

/-- Full lock path `<poolDir>/slot-<slotIndex>.lock` constructed via `join`. -/
def slotLockPath (join : String → String → String) (poolDir : String) (slotIndex : Nat) : String :=
  join poolDir (slotFileName slotIndex)

/-- Compute monotonic deadline `startNs + timeoutMs * 1_000_000` in nanoseconds. -/
def deadlineNanos (startNs timeoutMs : Nat) : Nat :=
  startNs + timeoutMs * nanosecondsPerMs

/-- Compute remaining wait budget in milliseconds, rounding positive sub-millisecond remainders up to `1`. -/
def remainingWaitMs (nowNs deadlineNs : Nat) : Nat :=
  if nowNs ≥ deadlineNs then
    0
  else
    (deadlineNs - nowNs + 999999) / nanosecondsPerMs

/-- Compute the next bounded sleep duration `min pollIntervalMs (remainingWaitMs nowNs deadlineNs)`. -/
def nextSleepMs (pollIntervalMs nowNs deadlineNs : Nat) : Nat :=
  Nat.min pollIntervalMs (remainingWaitMs nowNs deadlineNs)

/-- Structurally recursive worker splitting `ms` into positive `UInt32` chunks bounded by `maxSleepChunkMs`. -/
def sleepChunksAux : Nat → Nat → List UInt32
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, ms =>
    let chunk := Nat.min ms maxSleepChunkMs
    UInt32.ofNat chunk :: sleepChunksAux fuel (ms - chunk)

/-- Split `ms` milliseconds into positive `UInt32` chunks summing to `ms`. -/
def sleepChunks (ms : Nat) : List UInt32 :=
  sleepChunksAux (ms / maxSleepChunkMs + 1) ms

/-- Execute a list of `UInt32` millisecond sleep chunks sequentially via `time.sleep`. -/
def runSleepChunks {m : Type → Type} [Monad m] (time : TimeOpsM m) : List UInt32 → m Unit
  | [] => pure ()
  | c :: cs => do
    time.sleep c
    runSleepChunks time cs

/-- Map an `FsErrorKind` into the corresponding `SlotPoolErrorKind`. -/
def mapFsErrorKind : FsErrorKind → SlotPoolErrorKind
  | .invalidInput => .invalidInput
  | .notFound => .notFound
  | .alreadyExists => .alreadyExists
  | .permissionDenied => .permissionDenied
  | .isADirectory => .isADirectory
  | .notADirectory => .notADirectory
  | .unsupported => .unsupported
  | .notEmpty | .wouldBlock | .ioError => .ioError

/-- Convert an `FsError` into a `SlotPoolError` with a guaranteed non-empty diagnostic message. -/
def mapFsError (err : FsError) : SlotPoolError :=
  { kind := mapFsErrorKind err.kind
    path := err.path
    message := if err.message.isEmpty then "filesystem error in slot pool" else err.message }

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
