import Core.NondetTest
import Core.Assumptions
import LeanSwe.Json.Types

namespace LeanSwe.Json

open Core (NondetTest AssumptionObligation ErrorObligation)
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

/-- Every `parse` failure returns `.parseError` with a non-empty message and `path := none`. -/
def test_json_parse_onError_returnsParseErrorWithNonEmptyMessage
    {runner} [NondetTest runner] (api : JsonApi) : runner Unit := do
  let raw ← nondet String
  match api.parse raw with
  | .ok _ => NondetTest.assert True
  | .error e => NondetTest.assert (e.kind = .parseError ∧ e.message ≠ "" ∧ e.path = none)

/-- Trusted `Lean.Data.Json.{Parser,Printer}` (`Lean.Json.parse`, `Lean.Json.compress`, `Lean.Json.pretty`) boundary obligations verified at runtime with nonce logging.
    Object round-trip probes (`assume_json_compress_noNewlineAndParseRoundTrip` and `assume_json_pretty_parseRoundTrip`) apply to `Lean.Json` values whose object maps satisfy `Std.TreeMap.Raw.WF` (unique sorted keys, as produced by `Lean.Json.mkObj`, `Lean.toJson`, and `Lean.Json.parse`). -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.Json.assume_json_compress_noNewlineAndParseRoundTrip"
      subject := "LeanSwe.Json.compress"
      formalPred? := none }
  , { name := "LeanSwe.Json.assume_json_pretty_parseRoundTrip"
      subject := "LeanSwe.Json.pretty"
      formalPred? := none }
  , { name := "LeanSwe.Json.assume_json_encodeCompressParseDecode_roundTrip"
      subject := "LeanSwe.Json.parse"
      formalPred? := none } ]

/-- Declared error-coverage matrix for `LeanSwe.Json` fallible requests (`JsonErrorKind`). -/
def errorCoverage : List (ErrorObligation JsonErrorKind) :=
  [ { request := "LeanSwe.Json.parse"
      errorKind := .parseError
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_parse_parseError" .real }
  , { request := "LeanSwe.Json.parse"
      errorKind := .missingField
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_parse_never_missingField" }
  , { request := "LeanSwe.Json.parse"
      errorKind := .typeMismatch
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_parse_never_typeMismatch" }
  , { request := "LeanSwe.Json.parse"
      errorKind := .decodeError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_parse_never_decodeError" }
  , { request := "LeanSwe.Json.decode"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_decode_never_parseError" }
  , { request := "LeanSwe.Json.decode"
      errorKind := .missingField
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_decode_never_missingField" }
  , { request := "LeanSwe.Json.decode"
      errorKind := .typeMismatch
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_decode_never_typeMismatch" }
  , { request := "LeanSwe.Json.decode"
      errorKind := .decodeError
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_decode_decodeError" .real }
  , { request := "LeanSwe.Json.getObject"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getObject_never_parseError" }
  , { request := "LeanSwe.Json.getObject"
      errorKind := .missingField
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getObject_never_missingField" }
  , { request := "LeanSwe.Json.getObject"
      errorKind := .typeMismatch
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getObject_typeMismatch" .real }
  , { request := "LeanSwe.Json.getObject"
      errorKind := .decodeError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getObject_never_decodeError" }
  , { request := "LeanSwe.Json.getArray"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getArray_never_parseError" }
  , { request := "LeanSwe.Json.getArray"
      errorKind := .missingField
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getArray_never_missingField" }
  , { request := "LeanSwe.Json.getArray"
      errorKind := .typeMismatch
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getArray_typeMismatch" .real }
  , { request := "LeanSwe.Json.getArray"
      errorKind := .decodeError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getArray_never_decodeError" }
  , { request := "LeanSwe.Json.getField"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getField_never_parseError" }
  , { request := "LeanSwe.Json.getField"
      errorKind := .missingField
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getField_missingField" .real }
  , { request := "LeanSwe.Json.getField"
      errorKind := .typeMismatch
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getField_typeMismatch" .real }
  , { request := "LeanSwe.Json.getField"
      errorKind := .decodeError
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getField_decodeError" .real }
  , { request := "LeanSwe.Json.getOptField"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getOptField_never_parseError" }
  , { request := "LeanSwe.Json.getOptField"
      errorKind := .missingField
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getOptField_never_missingField" }
  , { request := "LeanSwe.Json.getOptField"
      errorKind := .typeMismatch
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getOptField_typeMismatch" .real }
  , { request := "LeanSwe.Json.getOptField"
      errorKind := .decodeError
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getOptField_decodeError" .real }
  , { request := "LeanSwe.Json.getPath"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Json.Proofs.json_getPath_never_parseError" }
  , { request := "LeanSwe.Json.getPath"
      errorKind := .missingField
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getPath_missingField" .real }
  , { request := "LeanSwe.Json.getPath"
      errorKind := .typeMismatch
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getPath_typeMismatch" .real }
  , { request := "LeanSwe.Json.getPath"
      errorKind := .decodeError
      justification := .tested "LeanSwe.Json.RuntimeTests.err_json_getPath_decodeError" .real } ]

end LeanSwe.Json
