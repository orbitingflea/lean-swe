import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.Uuid.Types
import LeanSwe.Uuid.Model

/-!
# Raw Syscall Refinement Contract for `LeanSwe.Uuid`

Defines the external-boundary `TimeRandOpsM` single-step contract (`UuidRawState`,
`toModelState`, `rawWf`, `execRawStep`, `allowedRawStep`) covering arbitrary
partial `getrandom(2)` chunks (`1..need` bytes), bounded `Errno.EINTR` retries
(`≤ 16`, matching `MAX_GETRANDOM_ATTEMPTS = 32`), and RFC 4122 v4 uniqueness.
-/

namespace LeanSwe.Uuid.Model

open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand
  (TimeRandOpsM TimeRandReq TimeRandOutcome execTimeRandReq)

/-- Maximum `Errno.EINTR` interruptions permitted per 16-byte UUIDv4 draw (`16`),
    leaving `16` attempts for up to 16 single-byte partial reads inside `MAX_GETRANDOM_ATTEMPTS` (`32`). -/
def MAX_GETRANDOM_EINTR : Nat := 16

/-- Raw external-boundary entropy state extending `UuidModelState` with in-flight
    partial-read bytes and a bounded `Errno.EINTR` retry budget. -/
structure UuidRawState where
  /-- UUIDs already issued in this execution; future completed draws never repeat any entry. -/
  seen : List Uuid := []
  /-- Partial entropy bytes accumulated so far for the active 16-byte draw. -/
  inFlight : ByteArray := ByteArray.empty
  /-- Remaining `Errno.EINTR` interruptions permitted during the active 16-byte draw. -/
  eintrBudget : Fin (MAX_GETRANDOM_EINTR + 1) := ⟨0, by decide⟩
  deriving BEq, DecidableEq, Inhabited

/-- Project `UuidRawState` onto the caller-facing `UuidModelState`. -/
def toModelState (s : UuidRawState) : UuidModelState :=
  { seen := s.seen }

/-- Well-formedness guard on `UuidRawState` matching `pkgWf ∘ toModelState`. -/
def rawWf (s : UuidRawState) : Bool :=
  pkgWf (toModelState s)

/-- Kernel-reducible `ByteArray` concatenation matching `Internal.appendBytes`. -/
def concatBytes (a b : ByteArray) : ByteArray :=
  if a.size == 0 then b
  else ByteArray.mk (a.data.toList ++ b.data.toList).toArray

/-- `prefixBytes` can be extended to 16 bytes stamping to an unseen RFC 4122 v4 UUID. -/
def hasFreshCompletion (seen : List Uuid) (prefixBytes : ByteArray) : Prop :=
  ∃ suf : ByteArray,
    prefixBytes.size + suf.size = 16 ∧
    match fromRandomBytes (concatBytes prefixBytes suf) with
    | .ok u => u ∉ seen
    | .error _ => False

/-- Execute one `TimeRandReq` against an arbitrary `TimeRandOpsM (StateM W)`. -/
def execRawStep {W : Type} (sys : TimeRandOpsM (StateM W))
    (req : TimeRandReq) : StateM W TimeRandOutcome :=
  execTimeRandReq sys req

/-- Allowed `TimeRandOpsM` single-step relation over `UuidRawState`.
    For `getrandom len {}` with `1 ≤ len.toNat` matching `16 - base.size`
    (where `base` resets to `ByteArray.empty` on a fresh 16-byte request and equals
    `s.inFlight` on continuation requests) whenever `hasFreshCompletion s.seen base`,
    healthy OS calls may either return `.err Errno.EINTR` while strictly decrementing
    `eintrBudget`, return a partial chunk (`1 ≤ got.size < len.toNat`) preserving
    `hasFreshCompletion`, or complete the 16-byte draw producing an unseen RFC 4122
    v4 UUID recorded onto `s'.seen`. -/
def allowedRawStep (s : UuidRawState) (req : TimeRandReq)
    (out : TimeRandOutcome) (s' : UuidRawState) : Prop :=
  match req, out with
  | .getrandom len flags, .err e =>
    let base := if len.toNat == 16 then ByteArray.empty else s.inFlight
    flags == {} ∧
    1 ≤ len.toNat ∧
    base.size + len.toNat = 16 ∧
    hasFreshCompletion s.seen base ∧
    e = Errno.EINTR ∧
    s'.eintrBudget.val < s.eintrBudget.val ∧
    s'.seen = s.seen ∧
    s'.inFlight = base
  | .getrandom len flags, .bytes got =>
    let base := if len.toNat == 16 then ByteArray.empty else s.inFlight
    if flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16) then
      (hasFreshCompletion s.seen base →
        1 ≤ got.size ∧
        got.size ≤ len.toNat ∧
        let next := concatBytes base got
        if next.size < 16 then
          s'.seen = s.seen ∧
          s'.inFlight = next ∧
          s'.eintrBudget.val ≤ s.eintrBudget.val ∧
          hasFreshCompletion s.seen next
        else
          s'.inFlight = ByteArray.empty ∧
          match fromRandomBytes next with
          | .ok u => u ∉ s.seen ∧ s'.seen = u :: s.seen
          | .error _ => False) ∧
      (¬ hasFreshCompletion s.seen base → s' = s)
    else
      s' = s
  | .clock_gettime _, .timespec _ => s' = s
  | .clock_nanosleep _ _ _, .unit => s' = s
  | _, _ => False

end LeanSwe.Uuid.Model
