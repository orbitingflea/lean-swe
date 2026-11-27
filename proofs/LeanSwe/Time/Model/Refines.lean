import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.Time.Types
import LeanSwe.Time.Model

/-!
# Raw Syscall Refinement Contract for `LeanSwe.Time`

Defines the external-boundary `TimeRandOpsM` single-step contract (`TimeRawState`,
`toModelState`, `rawWf`, `execRawStep`, `allowedRawStep`) expressing healthy
non-decreasing 64-bit `CLOCK_REALTIME` and `CLOCK_MONOTONIC` reads and
`CLOCK_MONOTONIC` `clock_nanosleep` advancement with bounded `Errno.EINTR`
retries (`≤ MAX_EINTR_RETRIES`) on `TIMER_ABSTIME` sleeps.
-/

namespace LeanSwe.Time.Model

open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand
  (TimeRandOpsM TimeRandReq TimeRandOutcome execTimeRandReq)

/-- Raw external-boundary clock state extending `TimeModelState` with a bounded
    `Errno.EINTR` interruption budget (`≤ MAX_EINTR_RETRIES`) for `TIMER_ABSTIME` sleeps. -/
structure TimeRawState where
  /-- Abstract UTC wall-clock reading in nanoseconds since the Unix epoch. -/
  wallNanos : Int := 0
  /-- Abstract monotonic clock reading in nanoseconds. -/
  monoNanos : Nat := 0
  /-- Remaining `Errno.EINTR` interruptions permitted before a `TIMER_ABSTIME` sleep completes. -/
  eintrBudget : Fin (MAX_EINTR_RETRIES + 1) := ⟨0, by decide⟩
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Project `TimeRawState` onto the caller-facing `TimeModelState`. -/
def toModelState (s : TimeRawState) : TimeModelState :=
  { wallNanos := s.wallNanos, monoNanos := s.monoNanos }

/-- Well-formedness guard on `TimeRawState` matching `pkgWf ∘ toModelState`. -/
def rawWf (s : TimeRawState) : Bool :=
  pkgWf (toModelState s)

/-- Execute one `TimeRandReq` against an arbitrary `TimeRandOpsM (StateM W)`. -/
def execRawStep {W : Type} (sys : TimeRandOpsM (StateM W))
    (req : TimeRandReq) : StateM W TimeRandOutcome :=
  execTimeRandReq sys req

/-- Allowed `TimeRandOpsM` single-step relation over `TimeRawState`.
    Healthy realtime and monotonic clock reads are non-decreasing within valid
    64-bit nanosecond bounds; valid `CLOCK_MONOTONIC` `TIMER_ABSTIME`
    `clock_nanosleep` calls may either return `.err Errno.EINTR` while strictly
    decrementing `eintrBudget` or succeed advancing `monoNanos` to at least the
    requested deadline; valid relative `CLOCK_MONOTONIC` sleeps succeed advancing
    `monoNanos` by at least `reqTs.toNanosNat` (clamped at `maxMonoNanos`). -/
def allowedRawStep (s : TimeRawState) (req : TimeRandReq)
    (out : TimeRandOutcome) (s' : TimeRawState) : Prop :=
  match req, out with
  | .clock_gettime .realtime, .timespec ts =>
    ts.hasValidNsec = true ∧
    s.wallNanos ≤ s'.wallNanos ∧
    isValidTimestampNanos s'.wallNanos = true ∧
    ts.toEpochNanos = s'.wallNanos ∧
    s.monoNanos ≤ s'.monoNanos ∧
    isValidMonoNanos s'.monoNanos = true
  | .clock_gettime .monotonic, .timespec ts =>
    ts.isValid = true ∧
    s.monoNanos ≤ s'.monoNanos ∧
    isValidMonoNanos s'.monoNanos = true ∧
    ts.toNanosNat = s'.monoNanos ∧
    s.wallNanos ≤ s'.wallNanos ∧
    isValidTimestampNanos s'.wallNanos = true
  | .clock_nanosleep .monotonic abstime reqTs, .unit =>
    reqTs.isValid = true ∧
    (if abstime then max s.monoNanos reqTs.toNanosNat
     else min maxMonoNanos (s.monoNanos + reqTs.toNanosNat)) ≤ s'.monoNanos ∧
    isValidMonoNanos s'.monoNanos = true ∧
    s.wallNanos ≤ s'.wallNanos ∧
    isValidTimestampNanos s'.wallNanos = true
  | .clock_nanosleep .realtime _ reqTs, .unit =>
    reqTs.isValid = true ∧ s' = s
  | .clock_nanosleep .monotonic true reqTs, .err e =>
    (reqTs.isValid = false ∧ e = Errno.EINVAL ∧ s' = s) ∨
    (reqTs.isValid = true ∧ e = Errno.EINTR ∧
      s'.eintrBudget.val < s.eintrBudget.val ∧
      s.monoNanos ≤ s'.monoNanos ∧
      isValidMonoNanos s'.monoNanos = true ∧
      s.wallNanos ≤ s'.wallNanos ∧
      isValidTimestampNanos s'.wallNanos = true)
  | .clock_nanosleep _ _ reqTs, .err e =>
    reqTs.isValid = false ∧ e = Errno.EINVAL ∧ s' = s
  | .getrandom _ _, .bytes _ => s' = s
  | _, _ => False

end LeanSwe.Time.Model
