import Core.NondetTest
import LeanSwe.Process.Raw.Types
import LeanSwe.Process.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Process.Raw`. -/

namespace LeanSwe.Process.Raw

open Core (NondetTest)
open Core.NondetTest

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
