import Core.NondetTest
import LeanSwe.Uuid.Raw.Types

namespace LeanSwe.Uuid.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` has kind `.entropyFailed` and a non-empty diagnostic message, preserving `errno` on `.osError`. -/
def test_uuidraw_mapRawError_normalizesError
    {runner} [NondetTest runner] (ops : RawUuidOps) : runner Unit := do
  let raw ← nondet UuidRawError
  let err := ops.mapRawError raw
  assert (err.kind = .entropyFailed ∧ err.message ≠ "")
  match raw with
  | .osError code _ => assert (err.errnoCode = some code)
  | .shortRead _ _ => assert True
  | .userError _ => assert True

/-- Successful `ops.randomBytes16` calls return exactly 16 bytes, and failures carry a non-empty message. -/
def test_uuidraw_randomBytes16_returns16BytesOrError
    {S : Type} {runner} [NondetTest runner] (ops : RawUuidOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  match (ops.randomBytes16.run s₀).1 with
  | .ok bs => assert (bs.size = 16)
  | .error e => assert (e.message ≠ "")

private def stubRawOps : RawUuidOps :=
  { mapRawError := fun
      | .osError code _ => { kind := .entropyFailed, errnoCode := some code, message := "os error" }
      | .shortRead _ _ => { kind := .entropyFailed, message := "short read" }
      | .userError _ => { kind := .entropyFailed, message := "entropy failed" }
    randomBytes16 := pure (.ok (ByteArray.mk (Array.replicate 16 0))) }

private def buggyEmptyErrRaw (base : RawUuidOps) : RawUuidOps :=
  { base with mapRawError := fun _ => { kind := .entropyFailed, message := "" } }

private def buggyWrongKindRaw (base : RawUuidOps) : RawUuidOps :=
  { base with mapRawError := fun _ => { kind := .invalidFormat, message := "bad" } }

private def buggyMissingErrnoRaw (base : RawUuidOps) : RawUuidOps :=
  { base with mapRawError := fun _ => { kind := .entropyFailed, errnoCode := none, message := "bad" } }

private def buggyShortBytesRaw : RawUuidOpsM (StateM Unit) :=
  { mapRawError := stubRawOps.mapRawError
    randomBytes16 := pure (.ok (ByteArray.mk #[1, 2, 3])) }

private def buggyEmptyReadErrRaw : RawUuidOpsM (StateM Unit) :=
  { mapRawError := stubRawOps.mapRawError
    randomBytes16 := pure (.error { kind := .entropyFailed, message := "" }) }

example : ¬ Core.AllPass (test_uuidraw_mapRawError_normalizesError (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_uuidraw_mapRawError_normalizesError, buggyEmptyErrRaw,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuidraw_mapRawError_normalizesError (buggyWrongKindRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_uuidraw_mapRawError_normalizesError, buggyWrongKindRaw,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_uuidraw_mapRawError_normalizesError (buggyMissingErrnoRaw stubRawOps)) := by
  intro h
  have h0 := h (.osError 5 "EIO")
  dsimp [test_uuidraw_mapRawError_normalizesError, buggyMissingErrnoRaw,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.2 (by decide)

example : ¬ Core.AllPass (test_uuidraw_randomBytes16_returns16BytesOrError buggyShortBytesRaw) := by
  intro h
  have h0 := h ()
  simp [buggyShortBytesRaw, StateT.run, pure, StateT.pure, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_uuidraw_randomBytes16_returns16BytesOrError buggyEmptyReadErrRaw) := by
  intro h
  have h0 := h ()
  simp [buggyEmptyReadErrRaw, StateT.run, pure, StateT.pure, assert] at h0

end LeanSwe.Uuid.Raw
