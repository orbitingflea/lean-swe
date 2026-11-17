import Core.NondetTest
import LeanSwe.Process.Raw.Types

namespace LeanSwe.Process.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_processRaw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawProcessOps) : runner Unit := do
  let raw ← nondet ProcessRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- `ops.mapRawError` maps every `ProcessRawError` variant to its exact `ProcessErrorKind` and metadata. -/
def test_processRaw_mapRawError_preservesKindAndFields
    {runner} [NondetTest runner] (ops : RawProcessOps) : runner Unit := do
  let raw ← nondet ProcessRawError
  let err := ops.mapRawError raw
  match raw with
  | .executableNotFound prog errno _ =>
    NondetTest.assert (err.kind = .notFound ∧ err.program = some prog ∧ err.errnoCode = some errno)
  | .permissionDenied prog? errno _ =>
    NondetTest.assert (err.kind = .permissionDenied ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .invalidArgument prog? errno _ =>
    NondetTest.assert (err.kind = .invalidInput ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .timedOut prog _ _ =>
    NondetTest.assert (err.kind = .timedOut ∧ err.program = some prog)
  | .outputLimitExceeded prog _ _ =>
    NondetTest.assert (err.kind = .outputLimitExceeded ∧ err.program = some prog)
  | .signaled prog sig _ =>
    NondetTest.assert (err.kind = .terminatedBySignal ∧ err.program = some prog ∧ err.signal = some sig)
  | .otherError errno _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.errnoCode = some errno)
  | .userError _ =>
    NondetTest.assert (err.kind = .ioError)

/-- Spawning an empty program fails with `.invalidInput`, non-empty message, and no leaked handles. -/
def test_processRaw_spawn_emptyProgram_failsInvalidInput
    {S : Type} {runner} [NondetTest runner] (ops : RawProcessOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  assume (req.program = "")
  let n₀ := (ops.activeProcessCount.run s₀).1
  let (res, s₁) := (ops.spawn req).run s₀
  let n₁ := (ops.activeProcessCount.run s₁).1
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ n₁ = n₀)

/-- Spawning in a dedicated process group, killing the group, and reaping restores `activeProcessCount`. -/
def test_processRaw_killAndReap_restoresActiveCount
    {S : Type} {runner} [NondetTest runner] (ops : RawProcessOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let n₀ := (ops.activeProcessCount.run s₀).1
  let (spawnRes, s₁) := (ops.spawn req).run s₀
  match spawnRes with
  | .error _ => assume False
  | .ok h =>
    let n₁ := (ops.activeProcessCount.run s₁).1
    NondetTest.assert (h.pid > 0 ∧ h.pgid > 0 ∧ n₁ = n₀ + 1)
    let (killRes, s₂) := (ops.killProcessGroup h).run s₁
    let (reapRes, s₃) := (ops.reap h).run s₂
    let n₃ := (ops.activeProcessCount.run s₃).1
    NondetTest.assert (killRes = .ok () ∧ reapRes = .ok () ∧ n₃ = n₀)

end LeanSwe.Process.Raw
