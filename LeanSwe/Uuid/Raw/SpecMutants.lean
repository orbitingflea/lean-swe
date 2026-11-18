import Core.NondetTest
import LeanSwe.Uuid.Raw.Types
import LeanSwe.Uuid.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Uuid.Raw`. -/

namespace LeanSwe.Uuid.Raw

open Core (NondetTest)
open Core.NondetTest

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

private def buggyWrongReadErrKindRaw : RawUuidOpsM (StateM Unit) :=
  { mapRawError := stubRawOps.mapRawError
    randomBytes16 := pure (.error { kind := .invalidFormat, message := "wrong kind" }) }

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

example : ¬ Core.AllPass (test_uuidraw_randomBytes16_returns16BytesOrError buggyWrongReadErrKindRaw) := by
  intro h
  have h0 := h ()
  simp [buggyWrongReadErrKindRaw, StateT.run, pure, StateT.pure, assert] at h0

end LeanSwe.Uuid.Raw
