import Core.NondetTest
import Core.Assumptions
import LeanSwe.Json.Types
import LeanSweProofs.Json.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Json`. -/

namespace LeanSwe.Json

open Core (NondetTest AssumptionObligation ErrorObligation)
open Core.NondetTest

private def stubJsonApi : JsonApi :=
  { parse := fun _ => .error { kind := .parseError, message := "stub" }
    compress := fun _ => ""
    pretty := fun _ _ => ""
    decode := fun _ => .error { kind := .decodeError, message := "stub" }
    encode := fun _ => Lean.Json.null
    getObject := fun _ => .error { kind := .typeMismatch, message := "stub" }
    getArray := fun _ => .error { kind := .typeMismatch, message := "stub" }
    getField := fun _ _ => .error { kind := .typeMismatch, message := "stub" }
    getOptField := fun _ _ => .error { kind := .typeMismatch, message := "stub" }
    getPath := fun _ _ => .error { kind := .typeMismatch, message := "stub" } }

example : ¬ Core.AllPass (test_json_encodeDecode_primitivesRoundTrip stubJsonApi) := by
  intro h
  have h0 := h true 0 0 ""
  simp [stubJsonApi, bind, assert] at h0

example : ¬ Core.AllPass (test_json_encodeDecode_optionAndArrayRoundTrip stubJsonApi) := by
  intro h
  have h0 := h none #[]
  simp [stubJsonApi, bind, assert] at h0

private def buggyEmptyMsgDecodeApi : JsonApi :=
  { stubJsonApi with
    decode := fun _ => .error { kind := .decodeError, message := "" } }

example : ¬ Core.AllPass (test_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage buggyEmptyMsgDecodeApi) := by
  intro h
  have h0 := h Lean.Json.null
  simp [buggyEmptyMsgDecodeApi, assert] at h0

example : ¬ Core.AllPass (test_json_getObject_extractsObjAndRejectsNonObj stubJsonApi) := by
  intro h
  have h0 := h (Lean.Json.obj ∅)
  simp [stubJsonApi, assert] at h0

example : ¬ Core.AllPass (test_json_getArray_extractsArrAndRejectsNonArr stubJsonApi) := by
  intro h
  have h0 := h (Lean.Json.arr #[])
  simp [stubJsonApi, assert] at h0

example : ¬ Core.AllPass (test_json_getField_presentValid_returnsDecoded stubJsonApi) := by
  intro h
  have h0 := h "a" 1
  simp [stubJsonApi, assert] at h0

private def buggyGetFieldMissingAsTypeMismatchApi : JsonApi :=
  { stubJsonApi with
    getField := fun _ k => .error { kind := .typeMismatch, message := "bad", path := some k } }

example : ¬ Core.AllPass (test_json_getField_missingKey_returnsMissingFieldWithPath buggyGetFieldMissingAsTypeMismatchApi) := by
  intro h
  have h0 := h "a" "b" 1 (by decide)
  simp [buggyGetFieldMissingAsTypeMismatchApi, assert] at h0

private def buggyGetFieldEmptyPathApi : JsonApi :=
  { stubJsonApi with
    getField := fun _ _ => .error { kind := .decodeError, message := "bad", path := none } }

example : ¬ Core.AllPass (test_json_getField_wrongValueType_returnsDecodeErrorWithPath buggyGetFieldEmptyPathApi) := by
  intro h
  have h0 := h "a" "x"
  simp [buggyGetFieldEmptyPathApi, assert] at h0

private def buggyGetFieldNonObjAsMissingApi : JsonApi :=
  { stubJsonApi with
    getField := fun _ k => .error { kind := .missingField, message := "missing", path := some k } }

example : ¬ Core.AllPass (test_json_getField_nonObject_returnsTypeMismatch buggyGetFieldNonObjAsMissingApi) := by
  intro h
  have h0 := h Lean.Json.null "a" trivial
  simp [buggyGetFieldNonObjAsMissingApi, assert] at h0

example : ¬ Core.AllPass (test_json_getOptField_presentNullMissingAndBadType stubJsonApi) := by
  intro h
  have h0 := h "a" "b" 1 "bad" (by decide)
  simp [stubJsonApi, bind, assert] at h0

private def buggyGetOptFieldSwallowsNonObjApi : JsonApi :=
  { stubJsonApi with
    getOptField := fun {_} _ _ _ => .ok none }

example : ¬ Core.AllPass (test_json_getOptField_nonObject_returnsTypeMismatch buggyGetOptFieldSwallowsNonObjApi) := by
  intro h
  have h0 := h Lean.Json.null "a" trivial
  simp [buggyGetOptFieldSwallowsNonObjApi, assert] at h0

example : ¬ Core.AllPass (test_json_getPath_emptySingletonNestedAndErrors stubJsonApi) := by
  intro h
  have h0 := h (Lean.Json.obj ∅) "a" "b" "c" 1 (by decide)
  simp [stubJsonApi, bind, assert] at h0

private def buggyGetPathDropsPrefixOnDecodeErrorApi : JsonApi :=
  { stubJsonApi with
    getPath := fun {_} _ _ keys =>
      match keys.reverse with
      | last :: _ => .error { kind := .decodeError, message := "bad", path := some last }
      | [] => .error { kind := .decodeError, message := "bad", path := none } }

example : ¬ Core.AllPass (test_json_getPath_nestedDecodeAndIntermediateErrors buggyGetPathDropsPrefixOnDecodeErrorApi) := by
  intro h
  have h0 := h "a" "b" "bad"
  simp [buggyGetPathDropsPrefixOnDecodeErrorApi, bind, assert] at h0

private def buggyEmptyParseErrorApi : JsonApi :=
  { stubJsonApi with
    parse := fun _ => .error { kind := .parseError, message := "" } }

example : ¬ Core.AllPass (test_json_parse_onError_returnsParseErrorWithNonEmptyMessage buggyEmptyParseErrorApi) := by
  intro h
  have h0 := h "bad"
  simp [buggyEmptyParseErrorApi, assert] at h0

private def buggyParseWrongKindApi : JsonApi :=
  { stubJsonApi with
    parse := fun _ => .error { kind := .decodeError, message := "bad", path := none } }

example : ¬ Core.AllPass (test_json_parse_onError_returnsParseErrorWithNonEmptyMessage buggyParseWrongKindApi) := by
  intro h
  have h0 := h "bad"
  simp [buggyParseWrongKindApi, assert] at h0

private def buggyParseWithPathApi : JsonApi :=
  { stubJsonApi with
    parse := fun _ => .error { kind := .parseError, message := "bad", path := some "root" } }

example : ¬ Core.AllPass (test_json_parse_onError_returnsParseErrorWithNonEmptyMessage buggyParseWithPathApi) := by
  intro h
  have h0 := h "bad"
  simp [buggyParseWithPathApi, assert] at h0

end LeanSwe.Json
