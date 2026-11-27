import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import Core.Obeys
import LeanSwe.Json.Interface
import LeanSweProofs.Json.Model

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- `ensureNonEmpty fallback msg` is always non-empty (`!isEmpty = true`) when `fallback ≠ ""`. -/
theorem ensureNonEmpty_not_isEmpty (fallback msg : String) (hf : fallback ≠ "") :
    !(ensureNonEmpty fallback msg).isEmpty = true := by
  have hne : ensureNonEmpty fallback msg ≠ "" := by
    unfold ensureNonEmpty
    by_cases h : msg == ""
    · simp [h, hf]
    · simp only [h]; intro heq; subst heq; exact h rfl
  cases he : (ensureNonEmpty fallback msg).isEmpty
  · rfl
  · exact absurd (String.isEmpty_iff.mp he) hne

/-- `s!"missing field: {k}"` is never empty (`!isEmpty = true`). -/
theorem missingField_not_isEmpty (k : String) :
    !(s!"missing field: {k}").isEmpty = true := by
  cases he : (s!"missing field: {k}").isEmpty
  · rfl
  · exfalso
    have hlen := congrArg String.length (String.isEmpty_iff.mp he)
    simp [toString] at hlen

/-- `"expected JSON object"` is non-empty (`!isEmpty = true`). -/
private theorem expectedObj_not_isEmpty : !("expected JSON object").isEmpty = true := by decide

/-- `joinSegmentsAux acc rest` equals `acc ++ "." ++ String.intercalate "." rest` on non-empty `rest`. -/
theorem joinSegmentsAux_eq (acc : String) :
    ∀ (rest : List String),
      joinSegmentsAux acc rest =
        match rest with
        | [] => acc
        | _ => acc ++ "." ++ String.intercalate "." rest
  | [] => rfl
  | [b] => by simp [joinSegmentsAux, String.intercalate_singleton]
  | b :: c :: tl => by
    rw [joinSegmentsAux, joinSegmentsAux_eq (acc ++ "." ++ b) (c :: tl),
      String.intercalate_cons_cons]
    simp [String.append_assoc]

/-- `joinSegments xs` equals `String.intercalate "." xs` for all `xs`. -/
theorem joinSegments_eq_intercalate :
    ∀ (xs : List String), joinSegments xs = String.intercalate "." xs
  | [] => by simp [joinSegments]
  | [k] => by simp [joinSegments, joinSegmentsAux, String.intercalate_singleton]
  | k :: b :: tl => by
    simp only [joinSegments, joinSegmentsAux_eq k (b :: tl)]
    rw [String.intercalate_cons_cons]

/-- `Internal.joinPath` equals `Model.modelJoinPath` on every reversed path prefix. -/
theorem joinPath_eq_modelJoinPath (revPrefix : List String) :
    joinPath revPrefix = modelJoinPath revPrefix := by
  unfold joinPath modelJoinPath
  split <;> simp [joinSegments_eq_intercalate]

/-- `LeanSwe.Json.decode` obeys `Model.allowedDecode`. -/
theorem allowedDecode_holds {α : Type} [Lean.FromJson α] :
    Core.ObeysPure (LeanSwe.Json.decode (α := α)) (Model.allowedDecode (α := α)) := by
  intro j
  simp only [LeanSwe.Json.decode, Internal.decode, Model.allowedDecode]
  cases Lean.fromJson? (α := α) j with
  | ok a => rfl
  | error msg => exact ⟨rfl, rfl, ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩

/-- `LeanSwe.Json.getObject` obeys `Model.allowedGetObject`. -/
theorem allowedGetObject_holds :
    Core.ObeysPure LeanSwe.Json.getObject Model.allowedGetObject := by
  intro j
  cases j <;> simp [LeanSwe.Json.getObject, Internal.getObject, Model.allowedGetObject] <;> decide

/-- `LeanSwe.Json.getArray` obeys `Model.allowedGetArray`. -/
theorem allowedGetArray_holds :
    Core.ObeysPure LeanSwe.Json.getArray Model.allowedGetArray := by
  intro j
  cases j <;> simp [LeanSwe.Json.getArray, Internal.getArray, Model.allowedGetArray] <;> decide

/-- `LeanSwe.Json.getField` obeys `Model.allowedGetField`. -/
theorem allowedGetField_holds {α : Type} [Lean.FromJson α] :
    Core.ObeysPure2 (LeanSwe.Json.getField (α := α)) (Model.allowedGetField (α := α)) := by
  intro j key
  cases j with
  | obj kvs =>
    simp only [LeanSwe.Json.getField, Internal.getField, Model.allowedGetField]
    cases kvs.get? key with
    | none => exact ⟨rfl, rfl, missingField_not_isEmpty key⟩
    | some v =>
      simp only [Internal.decode]
      cases hf : Lean.fromJson? (α := α) v with
      | ok a => simp [hf]
      | error msg =>
        refine ⟨by simp [hf, Except.isOk, Except.toBool], rfl, rfl,
          ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
  | null | bool _ | num _ | str _ | arr _ =>
    simp [LeanSwe.Json.getField, Internal.getField, Model.allowedGetField]

/-- `LeanSwe.Json.getOptField` obeys `Model.allowedGetOptField`. -/
theorem allowedGetOptField_holds {α : Type} [Lean.FromJson α] :
    Core.ObeysPure2 (LeanSwe.Json.getOptField (α := α)) (Model.allowedGetOptField (α := α)) := by
  intro j key
  cases j with
  | obj kvs =>
    simp only [LeanSwe.Json.getOptField, Internal.getOptField, Model.allowedGetOptField]
    cases hget : kvs.get? key with
    | none => trivial
    | some v =>
      cases v with
      | null => trivial
      | bool b =>
        simp only [Internal.decode]
        cases hf : Lean.fromJson? (α := α) (.bool b) with
        | ok a => exact ⟨by simp, hf⟩
        | error msg =>
          exact ⟨by simp, by simp [hf, Except.isOk, Except.toBool], rfl, rfl,
            ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
      | num n =>
        simp only [Internal.decode]
        cases hf : Lean.fromJson? (α := α) (.num n) with
        | ok a => exact ⟨by simp, hf⟩
        | error msg =>
          exact ⟨by simp, by simp [hf, Except.isOk, Except.toBool], rfl, rfl,
            ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
      | str s =>
        simp only [Internal.decode]
        cases hf : Lean.fromJson? (α := α) (.str s) with
        | ok a => exact ⟨by simp, hf⟩
        | error msg =>
          exact ⟨by simp, by simp [hf, Except.isOk, Except.toBool], rfl, rfl,
            ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
      | arr xs =>
        simp only [Internal.decode]
        cases hf : Lean.fromJson? (α := α) (.arr xs) with
        | ok a => exact ⟨by simp, hf⟩
        | error msg =>
          exact ⟨by simp, by simp [hf, Except.isOk, Except.toBool], rfl, rfl,
            ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
      | obj sub =>
        simp only [Internal.decode]
        cases hf : Lean.fromJson? (α := α) (.obj sub) with
        | ok a => exact ⟨by simp, hf⟩
        | error msg =>
          exact ⟨by simp, by simp [hf, Except.isOk, Except.toBool], rfl, rfl,
            ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
  | null | bool _ | num _ | str _ | arr _ =>
    simp [LeanSwe.Json.getOptField, Internal.getOptField, Model.allowedGetOptField]

/-- `Internal.getPathAux` satisfies `Model.allowedGetPathAux` for any `revPrefix`. -/
theorem allowedGetPathAux_holds {α : Type} [Lean.FromJson α] :
    ∀ (keys : List String) (revPrefix : List String) (j : Lean.Json),
      Model.allowedGetPathAux revPrefix j keys (Internal.getPathAux (α := α) revPrefix j keys)
  | [], revPrefix, j => by
    simp only [Internal.getPathAux, Model.allowedGetPathAux, Internal.decode]
    cases hf : Lean.fromJson? (α := α) j with
    | ok a => rfl
    | error msg =>
      by_cases hemp : revPrefix.isEmpty = true
      · simp only [hemp, ↓reduceIte]
        exact ⟨trivial, by simp [Model.modelJoinPath, hemp],
          ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
        exact ⟨trivial, joinPath_eq_modelJoinPath revPrefix,
          ensureNonEmpty_not_isEmpty "JSON decode error" msg (by decide)⟩
  | key :: rest, revPrefix, j => by
    cases j with
    | obj kvs =>
      simp only [Internal.getPathAux, Model.allowedGetPathAux]
      cases kvs.get? key with
      | some v => exact allowedGetPathAux_holds rest (key :: revPrefix) v
      | none =>
        exact ⟨_, rfl, rfl, joinPath_eq_modelJoinPath (key :: revPrefix), missingField_not_isEmpty key⟩
    | null | bool _ | num _ | str _ | arr _ =>
      simp only [Internal.getPathAux, Model.allowedGetPathAux]
      exact ⟨_, rfl, rfl, joinPath_eq_modelJoinPath revPrefix, expectedObj_not_isEmpty⟩

/-- `LeanSwe.Json.getPath` obeys `Model.allowedGetPath`. -/
theorem allowedGetPath_holds {α : Type} [Lean.FromJson α] :
    Core.ObeysPure2 (LeanSwe.Json.getPath (α := α)) (Model.allowedGetPath (α := α)) :=
  fun j keys => allowedGetPathAux_holds keys [] j

end LeanSwe.Json.Proofs
