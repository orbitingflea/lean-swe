import Core.NondetTest
import LeanSwe.Json.Types

namespace LeanSwe.Json

open Core (NondetTest)
open Core.NondetTest

/-- Encoding then decoding primitive types (`Bool`, `Nat`, `Int`, `String`) matches `Lean.toJson` and recovers the original values. -/
def test_json_encodeDecode_primitivesRoundTrip
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let b ← nondet Bool
  let n ← nondet Nat
  let i ← nondet Int
  let s ← nondet String
  NondetTest.assert (api.encode b = Lean.toJson b ∧ api.decode (api.encode b) = .ok b)
  NondetTest.assert (api.encode n = Lean.toJson n ∧ api.decode (api.encode n) = .ok n)
  NondetTest.assert (api.encode i = Lean.toJson i ∧ api.decode (api.encode i) = .ok i)
  NondetTest.assert (api.encode s = Lean.toJson s ∧ api.decode (api.encode s) = .ok s)

/-- Encoding then decoding `Option Nat` and `Array String` recovers the original values. -/
def test_json_encodeDecode_optionAndArrayRoundTrip
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let opt ← nondet (Option Nat)
  let xs ← nondet (Array String)
  NondetTest.assert (api.encode opt = Lean.toJson opt ∧ api.decode (api.encode opt) = .ok opt)
  NondetTest.assert (api.encode xs = Lean.toJson xs ∧ api.decode (api.encode xs) = .ok xs)

/-- Every `decode` failure returns `.decodeError` with a non-empty message and `path := none`. -/
def test_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  match api.decode (α := Nat) j with
  | .ok _ => assume False
  | .error e => NondetTest.assert (e.kind = .decodeError ∧ e.message ≠ "" ∧ e.path = none)

/-- `getObject` returns the underlying key-value map on `.obj` and `.typeMismatch` with non-empty message on non-objects. -/
def test_json_getObject_extractsObjAndRejectsNonObj
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  match j with
  | .obj kvs => NondetTest.assert (api.getObject j = .ok kvs)
  | _ =>
    match api.getObject j with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = .typeMismatch ∧ e.message ≠ "" ∧ e.path = none)

/-- `getArray` returns the underlying elements on `.arr` and `.typeMismatch` with non-empty message on non-arrays. -/
def test_json_getArray_extractsArrAndRejectsNonArr
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  match j with
  | .arr xs => NondetTest.assert (api.getArray j = .ok xs)
  | _ =>
    match api.getArray j with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = .typeMismatch ∧ e.message ≠ "" ∧ e.path = none)

/-- `getField` decodes a present typed object field cleanly. -/
def test_json_getField_presentValid_returnsDecoded
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let k ← nondet String
  let v ← nondet Nat
  let obj := Lean.Json.mkObj [(k, Lean.toJson v)]
  NondetTest.assert (api.getField (α := Nat) obj k = .ok v)

/-- `getField` on an absent object key returns `.missingField` with `path := some key` and a non-empty message. -/
def test_json_getField_missingKey_returnsMissingFieldWithPath
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let k1 ← nondet String
  let k2 ← nondet String
  let v ← nondet Nat
  assume (k1 ≠ k2)
  let obj := Lean.Json.mkObj [(k1, Lean.toJson v)]
  match api.getField (α := Nat) obj k2 with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .missingField ∧ e.path = some k2 ∧ e.message ≠ "")

/-- `getField` on a present field with incompatible JSON type returns `.decodeError` with `path := some key` and a non-empty message. -/
def test_json_getField_wrongValueType_returnsDecodeErrorWithPath
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let k ← nondet String
  let s ← nondet String
  let obj := Lean.Json.mkObj [(k, Lean.toJson s)]
  match api.getField (α := Nat) obj k with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .decodeError ∧ e.path = some k ∧ e.message ≠ "")

/-- `getField` on any non-object JSON value returns `.typeMismatch` with `path := none` and a non-empty message. -/
def test_json_getField_nonObject_returnsTypeMismatch
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  let k ← nondet String
  assume (match j with | .obj _ => False | _ => True)
  match api.getField (α := Nat) j k with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .typeMismatch ∧ e.path = none ∧ e.message ≠ "")

/-- `getOptField` returns `some v` for present valid values, `none` for `null` or absent keys, and `.decodeError` with `path` for wrong types. -/
def test_json_getOptField_presentNullMissingAndBadType
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let k1 ← nondet String
  let k2 ← nondet String
  let v ← nondet Nat
  let bad ← nondet String
  assume (k1 ≠ k2)
  NondetTest.assert (api.getOptField (α := Nat) (Lean.Json.mkObj [(k1, Lean.toJson v)]) k1 = .ok (some v))
  NondetTest.assert (api.getOptField (α := Nat) (Lean.Json.mkObj [(k1, Lean.Json.null)]) k1 = .ok none)
  NondetTest.assert (api.getOptField (α := Nat) (Lean.Json.mkObj [(k1, Lean.toJson v)]) k2 = .ok none)
  match api.getOptField (α := Nat) (Lean.Json.mkObj [(k1, Lean.toJson bad)]) k1 with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .decodeError ∧ e.path = some k1 ∧ e.message ≠ "")

/-- `getOptField` on any non-object JSON value returns `.typeMismatch` rather than silently returning `none`. -/
def test_json_getOptField_nonObject_returnsTypeMismatch
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  let k ← nondet String
  assume (match j with | .obj _ => False | _ => True)
  match api.getOptField (α := Nat) j k with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .typeMismatch ∧ e.path = none ∧ e.message ≠ "")

/-- `getPath` agrees with `decode` on `[]`, `getField` on `[k]`, decodes nested objects, and records dot-joined `path` on missing or non-object intermediates. -/
def test_json_getPath_emptySingletonNestedAndErrors
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  let k1 ← nondet String
  let k2 ← nondet String
  let k3 ← nondet String
  let v ← nondet Nat
  assume (k2 ≠ k3)
  NondetTest.assert (api.getPath (α := String) j [] = api.decode (α := String) j)
  NondetTest.assert (api.getPath (α := Nat) j [k1] = api.getField (α := Nat) j k1)
  let nested := Lean.Json.mkObj [(k1, Lean.Json.mkObj [(k2, Lean.toJson v)])]
  NondetTest.assert (api.getPath (α := Nat) nested [k1, k2] = .ok v)
  match api.getPath (α := Nat) nested [k1, k3] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .missingField ∧ e.path = some s!"{k1}.{k3}" ∧ e.message ≠ "")
  let flat := Lean.Json.mkObj [(k1, Lean.Json.null)]
  match api.getPath (α := Nat) flat [k1, k2] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .typeMismatch ∧ e.path = some k1 ∧ e.message ≠ "")

/-- `getPath` records the full dot-joined `path` on nested `.decodeError`, stops at missing intermediate keys, and rejects non-object roots. -/
def test_json_getPath_nestedDecodeAndIntermediateErrors
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let k1 ← nondet String
  let k2 ← nondet String
  let badStr ← nondet String
  let badNested := Lean.Json.mkObj [(k1, Lean.Json.mkObj [(k2, Lean.toJson badStr)])]
  match api.getPath (α := Nat) badNested [k1, k2] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .decodeError ∧ e.path = some s!"{k1}.{k2}" ∧ e.message ≠ "")
  match api.getPath (α := Nat) (Lean.Json.mkObj []) [k1, k2] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .missingField ∧ e.path = some k1 ∧ e.message ≠ "")
  match api.getPath (α := Nat) Lean.Json.null [k1, k2] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .typeMismatch ∧ e.path = none ∧ e.message ≠ "")

/-- Empirical contract (grounded in `RuntimeTests.lean`): `parse` failures always carry `.parseError`, a non-empty message, and `path := none`. -/
def empirical_json_parse_onError_returnsParseErrorWithNonEmptyMessage
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let raw ← nondet String
  match api.parse raw with
  | .ok _ => assume False
  | .error e => NondetTest.assert (e.kind = .parseError ∧ e.message ≠ "" ∧ e.path = none)

/-- Empirical contract (grounded in `RuntimeTests.lean`): `compress` emits non-empty single-line JSON (no `\n` or `\r`) that parses back to an equivalent JSON rendering. -/
def empirical_json_compress_noNewlineAndParseRoundTrip
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  let s := api.compress j
  NondetTest.assert (s ≠ "" ∧ !(s.contains '\n') ∧ !(s.contains '\r'))
  match api.parse s with
  | .error _ => NondetTest.assert False
  | .ok j' => NondetTest.assert (api.compress j' = s)

/-- Empirical contract (grounded in `RuntimeTests.lean`): `pretty` emits non-empty JSON that parses back to the same compressed representation. -/
def empirical_json_pretty_parseRoundTrip
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let j ← nondet Lean.Json
  let w ← nondet Nat
  assume (w > 0)
  let s := api.pretty j w
  NondetTest.assert (s ≠ "")
  match api.parse s with
  | .error _ => NondetTest.assert False
  | .ok j' => NondetTest.assert (api.compress j' = api.compress j)

/-- Empirical contract (grounded in `RuntimeTests.lean`): `encode` -> `compress` -> `parse` -> `decode` round-trips `Bool`, `Int`, `String`, and `Array String`. -/
def empirical_json_encodeCompressParseDecode_roundTrip
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let b ← nondet Bool
  let i ← nondet Int
  let s ← nondet String
  let xs ← nondet (Array String)
  match api.parse (api.compress (api.encode b)) with
  | .error _ => NondetTest.assert False
  | .ok jb => NondetTest.assert (api.decode jb = .ok b)
  match api.parse (api.compress (api.encode i)) with
  | .error _ => NondetTest.assert False
  | .ok ji => NondetTest.assert (api.decode ji = .ok i)
  match api.parse (api.compress (api.encode s)) with
  | .error _ => NondetTest.assert False
  | .ok js => NondetTest.assert (api.decode js = .ok s)
  match api.parse (api.compress (api.encode xs)) with
  | .error _ => NondetTest.assert False
  | .ok jxs => NondetTest.assert (api.decode jxs = .ok xs)

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

example : ¬ Core.AllPass (empirical_json_parse_onError_returnsParseErrorWithNonEmptyMessage buggyEmptyParseErrorApi) := by
  intro h
  have h0 := h "bad"
  simp [buggyEmptyParseErrorApi, assert] at h0

example : ¬ Core.AllPass (empirical_json_compress_noNewlineAndParseRoundTrip stubJsonApi) := by
  intro h
  have h0 := h Lean.Json.null
  simp [stubJsonApi, bind, assert] at h0

example : ¬ Core.AllPass (empirical_json_pretty_parseRoundTrip stubJsonApi) := by
  intro h
  have h0 := h Lean.Json.null 80 (by decide)
  simp [stubJsonApi, bind, assert] at h0

example : ¬ Core.AllPass (empirical_json_encodeCompressParseDecode_roundTrip stubJsonApi) := by
  intro h
  have h0 := h true 1 "s" #[]
  simp [stubJsonApi, bind, assert] at h0

/-- Throwaway added promise verifying Bool round-trip. -/
def test_json_throwawayAdd
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let b ← nondet Bool
  NondetTest.assert (api.encode b = Lean.toJson b ∧ api.decode (api.encode b) = .ok b)

end LeanSwe.Json
