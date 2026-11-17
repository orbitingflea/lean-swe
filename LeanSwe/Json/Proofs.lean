import LeanSwe.Json.Interface
import LeanSwe.Json.SpecTests
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF

namespace LeanSwe.Json.Proofs

open Core
open Core.NondetTest

private theorem ensureNonEmpty_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.ensureNonEmpty fallback msg ≠ "" := by
  unfold Internal.ensureNonEmpty
  by_cases h : msg == ""
  · simp [h, hf]
  · simp only [h]
    intro heq
    subst heq
    exact h (by decide)

private theorem toJson_nat (n : Nat) : Lean.toJson n = Lean.Json.num n := rfl
private theorem toJson_str (s : String) : Lean.toJson s = Lean.Json.str s := rfl

private theorem fromJson_bool_toJson (b : Bool) : Lean.fromJson? (Lean.toJson b) = .ok b := by
  cases b <;> rfl

private theorem fromJson_nat_toJson (n : Nat) : Lean.fromJson? (Lean.toJson n) = .ok n := rfl

private theorem fromJson_int_toJson (i : Int) : Lean.fromJson? (Lean.toJson i) = .ok i := rfl

private theorem fromJson_str_toJson (s : String) : Lean.fromJson? (Lean.toJson s) = .ok s := rfl

private theorem fromJson_option_nat_toJson (opt : Option Nat) :
    Lean.fromJson? (Lean.toJson opt) = .ok opt := by
  cases opt <;> rfl

private theorem fromJson_array_str_toJson (xs : Array String) :
    Lean.fromJson? (Lean.toJson xs) = .ok xs := by
  change Lean.Array.fromJson? (Lean.Json.arr (xs.map Lean.toJson)) = .ok xs
  simp only [Lean.Array.fromJson?]
  rw [Array.mapM_map]
  have hfn : (Lean.fromJson? (α := String) ∘ Lean.toJson) = fun x => pure x := by
    funext x
    exact fromJson_str_toJson x
  rw [hfn, Array.mapM_pure]
  simp [pure, Except.pure]

private theorem missingField_msg_ne_empty (k : String) :
    s!"missing field: {k}" ≠ "" := by
  intro heq
  have hlen := congrArg String.length heq
  simp [toString] at hlen

private theorem treeMap_empty_getElem? (k : String) :
    (∅ : Std.TreeMap.Raw String Lean.Json compare)[k]? = none :=
  Std.TreeMap.Raw.getElem?_emptyc

private theorem treeMap_singleton_getElem?_self (k : String) (v : Lean.Json) :
    ((∅ : Std.TreeMap.Raw String Lean.Json compare).insert k v)[k]? = some v :=
  Std.TreeMap.Raw.getElem?_insert_self Std.TreeMap.Raw.WF.emptyc

private theorem treeMap_singleton_getElem?_ne (k1 k2 : String) (v : Lean.Json) (hne : k1 ≠ k2) :
    ((∅ : Std.TreeMap.Raw String Lean.Json compare).insert k1 v)[k2]? = none := by
  rw [Std.TreeMap.Raw.getElem?_insert Std.TreeMap.Raw.WF.emptyc]
  have hcmp : compare k1 k2 ≠ .eq := by
    intro h
    exact hne ((Std.LawfulEqCmp.compare_eq_iff_eq).mp h)
  simp [hcmp, Std.TreeMap.Raw.getElem?_emptyc]

private theorem mkObj_empty_eq :
    Lean.Json.mkObj [] = Lean.Json.obj (∅ : Std.TreeMap.Raw String Lean.Json compare) := rfl

private theorem mkObj_singleton_eq (k : String) (v : Lean.Json) :
    Lean.Json.mkObj [(k, v)] =
      Lean.Json.obj ((∅ : Std.TreeMap.Raw String Lean.Json compare).insert k v) := rfl

/-- Proof of `test_json_encodeDecode_primitivesRoundTrip` for `defaultApi`. -/
theorem proof_json_encodeDecode_primitivesRoundTrip :
    AllPass (test_json_encodeDecode_primitivesRoundTrip defaultApi) := by
  intro b _ n i s
  dsimp [defaultApi, Internal.defaultApi, Internal.encode, Internal.decode, Bind.bind,
    Core.NondetTest.assert]
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩
  · rw [fromJson_bool_toJson]
  · rw [fromJson_nat_toJson]
  · rw [fromJson_int_toJson]
  · rw [fromJson_str_toJson]

/-- Non-vacuity `CanReach` witness for `test_json_encodeDecode_primitivesRoundTrip`. -/
theorem reach_json_encodeDecode_primitivesRoundTrip :
    CanReach (test_json_encodeDecode_primitivesRoundTrip defaultApi) :=
  ⟨true, rfl, 0, 0, "", proof_json_encodeDecode_primitivesRoundTrip true rfl 0 0 ""⟩

/-- Proof of `test_json_encodeDecode_optionAndArrayRoundTrip` for `defaultApi`. -/
theorem proof_json_encodeDecode_optionAndArrayRoundTrip :
    AllPass (test_json_encodeDecode_optionAndArrayRoundTrip defaultApi) := by
  intro opt xs
  dsimp [defaultApi, Internal.defaultApi, Internal.encode, Internal.decode, Bind.bind,
    Core.NondetTest.assert]
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩
  · rw [fromJson_option_nat_toJson]
  · rw [fromJson_array_str_toJson]

/-- Non-vacuity `CanReach` witness for `test_json_encodeDecode_optionAndArrayRoundTrip`. -/
theorem reach_json_encodeDecode_optionAndArrayRoundTrip :
    CanReach (test_json_encodeDecode_optionAndArrayRoundTrip defaultApi) :=
  ⟨none, #[], proof_json_encodeDecode_optionAndArrayRoundTrip none #[]⟩

/-- Proof of `test_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage` for `defaultApi`. -/
theorem proof_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage :
    AllPass (test_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage defaultApi) := by
  intro j
  dsimp [defaultApi, Internal.defaultApi, Internal.decode]
  cases Lean.fromJson? (α := Nat) j with
  | ok _ => simp [Core.NondetTest.assume]
  | error msg =>
    dsimp [Core.NondetTest.assert]
    exact ⟨⟨rfl, ensureNonEmpty_ne_empty "JSON decode error" msg (by decide), rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage`. -/
theorem reach_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage :
    CanReach (test_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage defaultApi) :=
  ⟨Lean.Json.null, by
    dsimp [test_json_decode_onError_returnsDecodeErrorWithNonEmptyMessage, defaultApi,
      Internal.defaultApi, Internal.decode]
    have hnull : Lean.fromJson? (α := Nat) Lean.Json.null = .error "Natural number expected" := rfl
    rw [hnull]
    simp [Internal.ensureNonEmpty, assert]⟩

/-- Proof of `test_json_getObject_extractsObjAndRejectsNonObj` for `defaultApi`. -/
theorem proof_json_getObject_extractsObjAndRejectsNonObj :
    AllPass (test_json_getObject_extractsObjAndRejectsNonObj defaultApi) := by
  intro j
  cases j <;>
    simp [defaultApi, Internal.defaultApi, Internal.getObject, assert]

/-- Non-vacuity `CanReach` witness for `test_json_getObject_extractsObjAndRejectsNonObj`. -/
theorem reach_json_getObject_extractsObjAndRejectsNonObj :
    CanReach (test_json_getObject_extractsObjAndRejectsNonObj defaultApi) :=
  ⟨Lean.Json.obj ∅, proof_json_getObject_extractsObjAndRejectsNonObj (Lean.Json.obj ∅)⟩

/-- Proof of `test_json_getArray_extractsArrAndRejectsNonArr` for `defaultApi`. -/
theorem proof_json_getArray_extractsArrAndRejectsNonArr :
    AllPass (test_json_getArray_extractsArrAndRejectsNonArr defaultApi) := by
  intro j
  cases j <;>
    simp [defaultApi, Internal.defaultApi, Internal.getArray, assert]

/-- Non-vacuity `CanReach` witness for `test_json_getArray_extractsArrAndRejectsNonArr`. -/
theorem reach_json_getArray_extractsArrAndRejectsNonArr :
    CanReach (test_json_getArray_extractsArrAndRejectsNonArr defaultApi) :=
  ⟨Lean.Json.arr #[], proof_json_getArray_extractsArrAndRejectsNonArr (Lean.Json.arr #[])⟩

/-- Proof of `test_json_getField_presentValid_returnsDecoded` for `defaultApi`. -/
theorem proof_json_getField_presentValid_returnsDecoded :
    AllPass (test_json_getField_presentValid_returnsDecoded defaultApi) := by
  intro k v
  dsimp [defaultApi, Internal.defaultApi, Internal.getField, Core.NondetTest.assert]
  rw [mkObj_singleton_eq]
  dsimp only
  rw [treeMap_singleton_getElem?_self]
  dsimp [Internal.decode]
  rw [fromJson_nat_toJson]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_json_getField_presentValid_returnsDecoded`. -/
theorem reach_json_getField_presentValid_returnsDecoded :
    CanReach (test_json_getField_presentValid_returnsDecoded defaultApi) :=
  ⟨"a", 1, proof_json_getField_presentValid_returnsDecoded "a" 1⟩

/-- Proof of `test_json_getField_missingKey_returnsMissingFieldWithPath` for `defaultApi`. -/
theorem proof_json_getField_missingKey_returnsMissingFieldWithPath :
    AllPass (test_json_getField_missingKey_returnsMissingFieldWithPath defaultApi) := by
  intro k1 k2 v hne
  dsimp [defaultApi, Internal.defaultApi, Internal.getField, Core.NondetTest.assert]
  rw [mkObj_singleton_eq]
  dsimp only
  rw [treeMap_singleton_getElem?_ne k1 k2 (Lean.toJson v) hne]
  exact ⟨⟨rfl, rfl, missingField_msg_ne_empty k2⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_json_getField_missingKey_returnsMissingFieldWithPath`. -/
theorem reach_json_getField_missingKey_returnsMissingFieldWithPath :
    CanReach (test_json_getField_missingKey_returnsMissingFieldWithPath defaultApi) :=
  ⟨"a", "b", 1, by decide,
    proof_json_getField_missingKey_returnsMissingFieldWithPath "a" "b" 1 (by decide)⟩

/-- Proof of `test_json_getField_wrongValueType_returnsDecodeErrorWithPath` for `defaultApi`. -/
theorem proof_json_getField_wrongValueType_returnsDecodeErrorWithPath :
    AllPass (test_json_getField_wrongValueType_returnsDecodeErrorWithPath defaultApi) := by
  intro k s
  dsimp [defaultApi, Internal.defaultApi, Internal.getField, Core.NondetTest.assert]
  rw [mkObj_singleton_eq]
  dsimp only
  rw [treeMap_singleton_getElem?_self, toJson_str]
  have hget : Lean.fromJson? (α := Nat) (Lean.Json.str s) = .error "Natural number expected" := rfl
  dsimp [Internal.decode]
  rw [hget]
  simp [Internal.ensureNonEmpty]

/-- Non-vacuity `CanReach` witness for `test_json_getField_wrongValueType_returnsDecodeErrorWithPath`. -/
theorem reach_json_getField_wrongValueType_returnsDecodeErrorWithPath :
    CanReach (test_json_getField_wrongValueType_returnsDecodeErrorWithPath defaultApi) :=
  ⟨"a", "bad", proof_json_getField_wrongValueType_returnsDecodeErrorWithPath "a" "bad"⟩

/-- Proof of `test_json_getField_nonObject_returnsTypeMismatch` for `defaultApi`. -/
theorem proof_json_getField_nonObject_returnsTypeMismatch :
    AllPass (test_json_getField_nonObject_returnsTypeMismatch defaultApi) := by
  intro j k hnot
  cases j with
  | obj _ => exact False.elim hnot
  | null => simp [defaultApi, Internal.defaultApi, Internal.getField, assert]
  | bool _ => simp [defaultApi, Internal.defaultApi, Internal.getField, assert]
  | num _ => simp [defaultApi, Internal.defaultApi, Internal.getField, assert]
  | str _ => simp [defaultApi, Internal.defaultApi, Internal.getField, assert]
  | arr _ => simp [defaultApi, Internal.defaultApi, Internal.getField, assert]

/-- Non-vacuity `CanReach` witness for `test_json_getField_nonObject_returnsTypeMismatch`. -/
theorem reach_json_getField_nonObject_returnsTypeMismatch :
    CanReach (test_json_getField_nonObject_returnsTypeMismatch defaultApi) :=
  ⟨Lean.Json.null, "a", trivial,
    proof_json_getField_nonObject_returnsTypeMismatch Lean.Json.null "a" trivial⟩

/-- Proof of `test_json_getOptField_presentNullMissingAndBadType` for `defaultApi`. -/
theorem proof_json_getOptField_presentNullMissingAndBadType :
    AllPass (test_json_getOptField_presentNullMissingAndBadType defaultApi) := by
  intro k1 k2 v bad hne
  dsimp [defaultApi, Internal.defaultApi, Internal.getOptField, Bind.bind, Core.NondetTest.assert]
  simp only [mkObj_singleton_eq, toJson_nat, toJson_str]
  rw [treeMap_singleton_getElem?_self, treeMap_singleton_getElem?_self,
    treeMap_singleton_getElem?_ne k1 k2 (Lean.Json.num (Lean.JsonNumber.fromNat v)) hne,
    treeMap_singleton_getElem?_self]
  have hok : Lean.fromJson? (α := Nat) (Lean.Json.num v) = .ok v := rfl
  have hbad : Lean.fromJson? (α := Nat) (Lean.Json.str bad) = .error "Natural number expected" := rfl
  dsimp [Internal.decode]
  rw [hok, hbad]
  simp [Internal.ensureNonEmpty]

/-- Non-vacuity `CanReach` witness for `test_json_getOptField_presentNullMissingAndBadType`. -/
theorem reach_json_getOptField_presentNullMissingAndBadType :
    CanReach (test_json_getOptField_presentNullMissingAndBadType defaultApi) :=
  ⟨"a", "b", 1, "bad", by decide,
    proof_json_getOptField_presentNullMissingAndBadType "a" "b" 1 "bad" (by decide)⟩

/-- Proof of `test_json_getOptField_nonObject_returnsTypeMismatch` for `defaultApi`. -/
theorem proof_json_getOptField_nonObject_returnsTypeMismatch :
    AllPass (test_json_getOptField_nonObject_returnsTypeMismatch defaultApi) := by
  intro j k hnot
  cases j with
  | obj _ => exact False.elim hnot
  | null => simp [defaultApi, Internal.defaultApi, Internal.getOptField, assert]
  | bool _ => simp [defaultApi, Internal.defaultApi, Internal.getOptField, assert]
  | num _ => simp [defaultApi, Internal.defaultApi, Internal.getOptField, assert]
  | str _ => simp [defaultApi, Internal.defaultApi, Internal.getOptField, assert]
  | arr _ => simp [defaultApi, Internal.defaultApi, Internal.getOptField, assert]

/-- Non-vacuity `CanReach` witness for `test_json_getOptField_nonObject_returnsTypeMismatch`. -/
theorem reach_json_getOptField_nonObject_returnsTypeMismatch :
    CanReach (test_json_getOptField_nonObject_returnsTypeMismatch defaultApi) :=
  ⟨Lean.Json.null, "a", trivial,
    proof_json_getOptField_nonObject_returnsTypeMismatch Lean.Json.null "a" trivial⟩

private theorem getPath_singleton_eq_getField {α : Type} [Lean.FromJson α]
    (j : Lean.Json) (k : String) :
    Internal.getPath (α := α) j [k] = Internal.getField (α := α) j k := by
  cases j with
  | obj kvs =>
    simp only [Internal.getPath, Internal.getPathAux, Internal.joinPath, Internal.getField]
    cases kvs.get? k with
    | none => rfl
    | some v =>
      simp only []
      cases Internal.decode (α := α) v <;> rfl
  | null => rfl
  | bool _ => rfl
  | num _ => rfl
  | str _ => rfl
  | arr _ => rfl

/-- Proof of `test_json_getPath_emptySingletonNestedAndErrors` for `defaultApi`. -/
theorem proof_json_getPath_emptySingletonNestedAndErrors :
    AllPass (test_json_getPath_emptySingletonNestedAndErrors defaultApi) := by
  intro j k1 k2 k3 v hne
  dsimp [defaultApi, Internal.defaultApi, Bind.bind, Core.NondetTest.assert]
  have hempty : Internal.getPath (α := String) j [] = Internal.decode (α := String) j := by
    simp only [Internal.getPath, Internal.getPathAux, List.isEmpty]
    cases Internal.decode (α := String) j <;> rfl
  have hsingle : Internal.getPath (α := Nat) j [k1] = Internal.getField (α := Nat) j k1 :=
    getPath_singleton_eq_getField j k1
  have hnested : Internal.getPath (α := Nat)
      (Lean.Json.mkObj [(k1, Lean.Json.mkObj [(k2, Lean.toJson v)])]) [k1, k2] = .ok v := by
    simp only [Internal.getPath, Internal.getPathAux, mkObj_singleton_eq, Std.TreeMap.Raw.get?_eq_getElem?,
      treeMap_singleton_getElem?_self, Internal.decode, fromJson_nat_toJson]
  have hmiss : Internal.getPath (α := Nat)
      (Lean.Json.mkObj [(k1, Lean.Json.mkObj [(k2, Lean.toJson v)])]) [k1, k3] =
      .error { kind := .missingField, message := s!"missing field: {k3}", path := some s!"{k1}.{k3}" } := by
    simp only [Internal.getPath, Internal.getPathAux, mkObj_singleton_eq, Std.TreeMap.Raw.get?_eq_getElem?,
      treeMap_singleton_getElem?_self, treeMap_singleton_getElem?_ne k2 k3 (Lean.toJson v) hne,
      Internal.joinPath, Internal.joinSegments, List.isEmpty, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, Bool.false_eq_true, ↓reduceIte, toString]
  have hflat : Internal.getPath (α := Nat)
      (Lean.Json.mkObj [(k1, Lean.Json.null)]) [k1, k2] =
      .error { kind := .typeMismatch, message := "expected JSON object", path := some k1 } := by
    simp only [Internal.getPath, Internal.getPathAux, mkObj_singleton_eq, Std.TreeMap.Raw.get?_eq_getElem?,
      treeMap_singleton_getElem?_self, Internal.joinPath, Internal.joinSegments, List.isEmpty,
      List.reverse_cons, List.reverse_nil, List.nil_append, Bool.false_eq_true, ↓reduceIte]
  rw [hempty, hsingle, hnested, hmiss, hflat]
  exact ⟨rfl, rfl, rfl, ⟨rfl, rfl, missingField_msg_ne_empty k3⟩, ⟨rfl, rfl, by simp⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_json_getPath_emptySingletonNestedAndErrors`. -/
theorem reach_json_getPath_emptySingletonNestedAndErrors :
    CanReach (test_json_getPath_emptySingletonNestedAndErrors defaultApi) :=
  ⟨Lean.Json.null, "a", "b", "c", 1, by decide,
    proof_json_getPath_emptySingletonNestedAndErrors Lean.Json.null "a" "b" "c" 1 (by decide)⟩

/-- Proof of `test_json_getPath_nestedDecodeAndIntermediateErrors` for `defaultApi`. -/
theorem proof_json_getPath_nestedDecodeAndIntermediateErrors :
    AllPass (test_json_getPath_nestedDecodeAndIntermediateErrors defaultApi) := by
  intro k1 k2 badStr
  dsimp [defaultApi, Internal.defaultApi, Internal.getPath, Internal.getPathAux, Bind.bind,
    Core.NondetTest.assert]
  rw [mkObj_singleton_eq, mkObj_singleton_eq, mkObj_empty_eq]
  dsimp only
  rw [treeMap_singleton_getElem?_self]
  dsimp only
  rw [treeMap_singleton_getElem?_self, treeMap_empty_getElem?, toJson_str]
  have hbad : Lean.fromJson? (α := Nat) (Lean.Json.str badStr) = .error "Natural number expected" := rfl
  dsimp [Internal.decode]
  rw [hbad]
  dsimp [Internal.ensureNonEmpty, Internal.joinPath, Internal.joinSegments]
  refine ⟨⟨rfl, ?_, by decide⟩, ⟨rfl, rfl, missingField_msg_ne_empty k1⟩, ⟨rfl, rfl, by decide⟩, trivial⟩
  simp [Internal.joinSegments, toString]

/-- Non-vacuity `CanReach` witness for `test_json_getPath_nestedDecodeAndIntermediateErrors`. -/
theorem reach_json_getPath_nestedDecodeAndIntermediateErrors :
    CanReach (test_json_getPath_nestedDecodeAndIntermediateErrors defaultApi) :=
  ⟨"a", "b", "bad",
    proof_json_getPath_nestedDecodeAndIntermediateErrors "a" "b" "bad"⟩

end LeanSwe.Json.Proofs
