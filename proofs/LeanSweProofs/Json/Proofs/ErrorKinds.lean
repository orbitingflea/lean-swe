import LeanSwe.Json.Interface

namespace LeanSwe.Json.Proofs

/-- Any error returned by `LeanSwe.Json.parse` has kind `.parseError`. -/
theorem parse_error_kind_eq (raw : String) {e : JsonError}
    (h : LeanSwe.Json.parse raw = .error e) : e.kind = .parseError := by
  dsimp [LeanSwe.Json.parse, Internal.parse] at h
  cases hparse : Internal.parsePure raw with
  | ok _ => simp [hparse] at h
  | error msg => simp [hparse] at h; cases h; rfl

/-- Any error returned by `Internal.decode` has kind `.decodeError`. -/
private theorem internal_decode_error_kind_eq {α : Type} [Lean.FromJson α] (j : Lean.Json) {e : JsonError}
    (h : Internal.decode (α := α) j = .error e) : e.kind = .decodeError := by
  dsimp [Internal.decode] at h
  cases hdec : Lean.fromJson? (α := α) j with
  | ok _ => simp [hdec] at h
  | error msg => simp [hdec] at h; cases h; rfl

/-- Any error returned by `LeanSwe.Json.decode` has kind `.decodeError`. -/
theorem decode_error_kind_eq {α : Type} [Lean.FromJson α] (j : Lean.Json) {e : JsonError}
    (h : LeanSwe.Json.decode (α := α) j = .error e) : e.kind = .decodeError :=
  internal_decode_error_kind_eq j h

/-- Any error returned by `LeanSwe.Json.getObject` has kind `.typeMismatch`. -/
theorem getObject_error_kind_eq (j : Lean.Json) {e : JsonError}
    (h : LeanSwe.Json.getObject j = .error e) : e.kind = .typeMismatch := by
  cases j <;> simp [LeanSwe.Json.getObject, Internal.getObject] at h <;> cases h <;> rfl

/-- Any error returned by `LeanSwe.Json.getArray` has kind `.typeMismatch`. -/
theorem getArray_error_kind_eq (j : Lean.Json) {e : JsonError}
    (h : LeanSwe.Json.getArray j = .error e) : e.kind = .typeMismatch := by
  cases j <;> simp [LeanSwe.Json.getArray, Internal.getArray] at h <;> cases h <;> rfl

/-- Any error returned by `LeanSwe.Json.getField` never has kind `.parseError`. -/
theorem getField_error_kind_ne_parseError {α : Type} [Lean.FromJson α]
    (j : Lean.Json) (key : String) {e : JsonError}
    (h : LeanSwe.Json.getField (α := α) j key = .error e) : e.kind ≠ .parseError := by
  cases j with
  | obj kvs =>
    simp only [LeanSwe.Json.getField, Internal.getField] at h
    cases hget : kvs.get? key with
    | none =>
      simp only [hget, Except.error.injEq] at h
      subst h; dsimp only; decide
    | some v =>
      simp only [hget] at h
      cases hd : Internal.decode (α := α) v with
      | ok _ => simp [hd] at h
      | error e' =>
        simp only [hd, Except.error.injEq] at h
        subst h
        have hk := internal_decode_error_kind_eq v hd
        dsimp only; rw [hk]; decide
  | null | bool _ | num _ | str _ | arr _ =>
    simp only [LeanSwe.Json.getField, Internal.getField, Except.error.injEq] at h
    subst h; dsimp only; decide

/-- Any error returned by `LeanSwe.Json.getOptField` has kind `.typeMismatch` or `.decodeError`. -/
theorem getOptField_error_kind {α : Type} [Lean.FromJson α]
    (j : Lean.Json) (key : String) {e : JsonError}
    (h : LeanSwe.Json.getOptField (α := α) j key = .error e) :
    e.kind = .typeMismatch ∨ e.kind = .decodeError := by
  cases j with
  | obj kvs =>
    simp only [LeanSwe.Json.getOptField, Internal.getOptField] at h
    cases hget : kvs.get? key with
    | none => simp [hget] at h
    | some v =>
      simp only [hget] at h
      cases v with
      | null => simp at h
      | bool b =>
        dsimp only at h
        cases hd : Internal.decode (α := α) (.bool b) with
        | ok _ => simp [hd] at h
        | error e' => simp only [hd, Except.error.injEq] at h; subst h; dsimp only; exact Or.inr (internal_decode_error_kind_eq _ hd)
      | num n =>
        dsimp only at h
        cases hd : Internal.decode (α := α) (.num n) with
        | ok _ => simp [hd] at h
        | error e' => simp only [hd, Except.error.injEq] at h; subst h; dsimp only; exact Or.inr (internal_decode_error_kind_eq _ hd)
      | str s =>
        dsimp only at h
        cases hd : Internal.decode (α := α) (.str s) with
        | ok _ => simp [hd] at h
        | error e' => simp only [hd, Except.error.injEq] at h; subst h; dsimp only; exact Or.inr (internal_decode_error_kind_eq _ hd)
      | arr xs =>
        dsimp only at h
        cases hd : Internal.decode (α := α) (.arr xs) with
        | ok _ => simp [hd] at h
        | error e' => simp only [hd, Except.error.injEq] at h; subst h; dsimp only; exact Or.inr (internal_decode_error_kind_eq _ hd)
      | obj sub =>
        dsimp only at h
        cases hd : Internal.decode (α := α) (.obj sub) with
        | ok _ => simp [hd] at h
        | error e' => simp only [hd, Except.error.injEq] at h; subst h; dsimp only; exact Or.inr (internal_decode_error_kind_eq _ hd)
  | null | bool _ | num _ | str _ | arr _ =>
    simp only [LeanSwe.Json.getOptField, Internal.getOptField, Except.error.injEq] at h
    subst h; exact Or.inl rfl

/-- Any error returned by `Internal.getPathAux` never has kind `.parseError`. -/
theorem getPathAux_error_kind_ne_parseError {α : Type} [Lean.FromJson α]
    (keys : List String) (revPrefix : List String) (j : Lean.Json) {e : JsonError}
    (h : Internal.getPathAux (α := α) revPrefix j keys = .error e) : e.kind ≠ .parseError := by
  induction keys generalizing revPrefix j with
  | nil =>
    simp only [Internal.getPathAux] at h
    cases hd : Internal.decode (α := α) j with
    | ok _ => simp [hd] at h
    | error e' =>
      have hk := internal_decode_error_kind_eq j hd
      by_cases hemp : revPrefix.isEmpty = true <;>
        simp only [hd, hemp, Bool.false_eq_true, ↓reduceIte, Except.error.injEq] at h <;>
        subst h <;> simp [hk]
  | cons key rest ih =>
    cases j with
    | obj kvs =>
      simp only [Internal.getPathAux] at h
      cases hget : kvs.get? key with
      | some v => simp only [hget] at h; exact ih (key :: revPrefix) v h
      | none => simp only [hget, Except.error.injEq] at h; subst h; intro hc; cases hc
    | null | bool _ | num _ | str _ | arr _ =>
      simp only [Internal.getPathAux, Except.error.injEq] at h
      subst h; intro hc; cases hc

end LeanSwe.Json.Proofs
