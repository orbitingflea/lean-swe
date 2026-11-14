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
  assert (err.message ≠ "")

/-- `ops.mapRawError` maps every `ProcessRawError` variant to its exact `ProcessErrorKind` and metadata. -/
def test_processRaw_mapRawError_preservesKindAndFields
    {runner} [NondetTest runner] (ops : RawProcessOps) : runner Unit := do
  let raw ← nondet ProcessRawError
  let err := ops.mapRawError raw
  match raw with
  | .executableNotFound prog errno _ =>
    assert (err.kind = .notFound ∧ err.program = some prog ∧ err.errnoCode = some errno)
  | .permissionDenied prog? errno _ =>
    assert (err.kind = .permissionDenied ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .invalidArgument prog? errno _ =>
    assert (err.kind = .invalidInput ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .timedOut prog _ _ =>
    assert (err.kind = .timedOut ∧ err.program = some prog)
  | .outputLimitExceeded prog _ _ =>
    assert (err.kind = .outputLimitExceeded ∧ err.program = some prog)
  | .signaled prog sig _ =>
    assert (err.kind = .terminatedBySignal ∧ err.program = some prog ∧ err.signal = some sig)
  | .otherError errno _ =>
    assert (err.kind = .ioError ∧ err.errnoCode = some errno)
  | .userError _ =>
    assert (err.kind = .ioError)

/-- Spawning an empty program fails with `.invalidInput`, non-empty message, and no leaked handles. -/
def test_processRaw_spawn_emptyProgram_failsInvalidInput
    {S : Type} {runner} [NondetTest runner] (ops : RawProcessOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  assume (req.program = "")
  let n₀ := (ops.activeProcessCount.run s₀).1
  let (res, s₁) := (ops.spawn req).run s₀
  let n₁ := (ops.activeProcessCount.run s₁).1
  assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ n₁ = n₀)

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
    assert (h.pid > 0 ∧ h.pgid > 0 ∧ n₁ = n₀ + 1)
    let (killRes, s₂) := (ops.killProcessGroup h).run s₁
    let (reapRes, s₃) := (ops.reap h).run s₂
    let n₃ := (ops.activeProcessCount.run s₃).1
    assert (killRes = .ok () ∧ reapRes = .ok () ∧ n₃ = n₀)

private def stubRawOps : RawProcessOps :=
  { mapRawError := fun
      | .executableNotFound prog errno _ =>
        { kind := .notFound, program := some prog, errnoCode := some errno, message := "not found" }
      | .permissionDenied prog? errno _ =>
        { kind := .permissionDenied, program := prog?, errnoCode := some errno, message := "permission denied" }
      | .invalidArgument prog? errno _ =>
        { kind := .invalidInput, program := prog?, errnoCode := some errno, message := "invalid argument" }
      | .timedOut prog _ _ =>
        { kind := .timedOut, program := some prog, message := "timed out" }
      | .outputLimitExceeded prog _ _ =>
        { kind := .outputLimitExceeded, program := some prog, message := "output limit exceeded" }
      | .signaled prog sig _ =>
        { kind := .terminatedBySignal, program := some prog, signal := some sig, message := "signaled" }
      | .otherError errno _ =>
        { kind := .ioError, errnoCode := some errno, message := "os error" }
      | .userError _ =>
        { kind := .ioError, message := "process error" }
    spawn := fun _ => pure (.error { kind := .ioError, message := "stub" })
    awaitOutput := fun _ _ _ _ => pure (.error { kind := .ioError, message := "stub" })
    killProcessGroup := fun _ => pure (.ok ())
    reap := fun _ => pure (.ok ())
    activeProcessCount := pure 0 }

private def buggyEmptyErrRaw (base : RawProcessOps) : RawProcessOps :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyWrongKindRaw (base : RawProcessOps) : RawProcessOps :=
  { base with
    mapRawError := fun raw =>
      match raw with
      | .timedOut prog _ _ => { kind := .ioError, program := some prog, message := "timeout" }
      | other => base.mapRawError other }

private def stubStatefulRawOps : RawProcessOpsM (StateM Nat) :=
  { mapRawError := stubRawOps.mapRawError
    spawn := fun req => do
      if req.program == "" then
        return .error { kind := .invalidInput, program := some "", message := "empty program" }
      modify (· + 1)
      return .ok { handleId := 1, pid := 100, pgid := 100 }
    awaitOutput := fun _ _ _ _ =>
      pure (.ok (.exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }))
    killProcessGroup := fun _ => pure (.ok ())
    reap := fun _ => do
      modify (fun n => n - 1)
      return .ok ()
    activeProcessCount := fun s => (s, s) }

private def buggySpawnEmptyRaw (base : RawProcessOpsM (StateM Nat)) : RawProcessOpsM (StateM Nat) :=
  { base with
    spawn := fun _ => do
      modify (· + 1)
      return .ok { handleId := 1, pid := 100, pgid := 100 } }

private def buggyNoReapRaw (base : RawProcessOpsM (StateM Nat)) : RawProcessOpsM (StateM Nat) :=
  { base with reap := fun _ => pure (.ok ()) }

private def buggyNoTrackSpawnRaw (base : RawProcessOpsM (StateM Nat)) : RawProcessOpsM (StateM Nat) :=
  { base with
    spawn := fun _ => pure (.ok { handleId := 1, pid := 100, pgid := 100 })
    reap := fun _ => pure (.ok ()) }

example : ¬ Core.AllPass (test_processRaw_mapRawError_returnsNonEmptyMessage (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrRaw, assert] at h0

example : ¬ Core.AllPass (test_processRaw_mapRawError_preservesKindAndFields (buggyWrongKindRaw stubRawOps)) := by
  intro h
  have h0 := h (.timedOut "sleep" 10 "expired")
  simp [buggyWrongKindRaw, assert] at h0

example : ¬ Core.AllPass (test_processRaw_spawn_emptyProgram_failsInvalidInput (buggySpawnEmptyRaw stubStatefulRawOps)) := by
  intro h
  have h0 := h 0 { program := "" } rfl
  simp [buggySpawnEmptyRaw, stubStatefulRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, assert] at h0

example : ¬ Core.AllPass (test_processRaw_killAndReap_restoresActiveCount (buggyNoReapRaw stubStatefulRawOps)) := by
  intro h
  have h0 := h 0 { program := "echo" }
  simp [buggyNoReapRaw, stubStatefulRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, assert] at h0

example : ¬ Core.AllPass (test_processRaw_killAndReap_restoresActiveCount (buggyNoTrackSpawnRaw stubStatefulRawOps)) := by
  intro h
  have h0 := h 0 { program := "echo" }
  simp [buggyNoTrackSpawnRaw, stubStatefulRawOps, StateT.run, bind, pure, StateT.pure, assert] at h0

end LeanSwe.Process.Raw
