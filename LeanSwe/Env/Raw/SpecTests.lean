import Core.NondetTest
import LeanSwe.Env.Raw.Types

namespace LeanSwe.Env.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_envraw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawEnvOps) : runner Unit := do
  let raw ← nondet EnvRawError
  let err := ops.mapRawError raw
  assert (err.message ≠ "")

/-- `ops.mapRawError` maps each `EnvRawError` constructor to its expected `EnvErrorKind`, `key`, and `errnoCode`. -/
def test_envraw_mapRawError_preservesKindAndMetadata
    {runner} [NondetTest runner] (ops : RawEnvOps) : runner Unit := do
  let raw ← nondet EnvRawError
  let err := ops.mapRawError raw
  match raw with
  | .invalidEncoding key? _ =>
    assert (err.kind = .invalidEncoding ∧ err.key = key? ∧ err.errnoCode = none)
  | .invalidArgument key? code _ =>
    assert (err.kind = .invalidKey ∧ err.key = key? ∧ err.errnoCode = some code)
  | .otherError code _ =>
    assert (err.kind = .ioError ∧ err.key = none ∧ err.errnoCode = some code)
  | .userError _ =>
    assert (err.kind = .ioError ∧ err.key = none ∧ err.errnoCode = none)

private def stubRawOps : RawEnvOps :=
  { mapRawError := fun
      | .invalidEncoding key? _ =>
        { kind := .invalidEncoding, key := key?, errnoCode := none, message := "stub" }
      | .invalidArgument key? code _ =>
        { kind := .invalidKey, key := key?, errnoCode := some code, message := "stub" }
      | .otherError code _ =>
        { kind := .ioError, key := none, errnoCode := some code, message := "stub" }
      | .userError _ =>
        { kind := .ioError, key := none, errnoCode := none, message := "stub" }
    getEnv := fun _ => pure (.ok none)
    listEnv := pure (.ok #[]) }

private def buggyEmptyErrRaw (base : RawEnvOps) : RawEnvOps :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyWrongKindRaw (base : RawEnvOps) : RawEnvOps :=
  { base with
    mapRawError := fun
      | .invalidEncoding key? _ => { kind := .ioError, key := key?, message := "bad kind" }
      | other => base.mapRawError other }

example : ¬ Core.AllPass (test_envraw_mapRawError_returnsNonEmptyMessage (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrRaw, assert] at h0

example : ¬ Core.AllPass (test_envraw_mapRawError_preservesKindAndMetadata (buggyWrongKindRaw stubRawOps)) := by
  intro h
  have h0 := h (.invalidEncoding (some "PATH") "bad utf8")
  simp [buggyWrongKindRaw, assert] at h0

end LeanSwe.Env.Raw
