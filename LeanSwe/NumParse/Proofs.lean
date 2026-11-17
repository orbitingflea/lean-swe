import LeanSwe.NumParse.Proofs.IntProofs
import LeanSwe.NumParse.Proofs.FloatExpProofs
import LeanSwe.NumParse.Proofs.FloatParseProofs
import LeanSwe.NumParse.Proofs.SpecContractProofs
import LeanSwe.NumParse.Proofs.FloatRenderProofs
import LeanSwe.NumParse.Proofs.FloatFormatProofs

namespace LeanSwe.NumParse.Proofs

open Core
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem consumeIntDigits_ne_overflow (b : NumBase) (acc : Nat) (cs : List Char) :
    consumeIntDigits b acc cs ≠ .error .overflow := by
  fun_induction consumeIntDigits b acc cs with
  | case1 => simp
  | case2 _ _ _ _ _ ih1 => exact ih1
  | case3 => simp
  | case4 => simp
  | case5 _ _ _ _ _ _ _ ih1 => exact ih1
  | case6 => simp

private theorem parseDecAfterSign_ne_overflow (neg : Bool) (cs : List Char) :
    parseDecAfterSign neg cs ≠ .error .overflow := by
  unfold parseDecAfterSign
  split
  · simp
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · split
          · split <;> simp
          · simp
        · simp
  · split
    · cases hci : consumeIntDigits .dec _ _ with
      | ok _ => simp
      | error k =>
        intro hk
        cases hk
        exact consumeIntDigits_ne_overflow .dec _ _ hci
    · simp

private theorem parseIntModelChars_ne_overflow (cs : List Char) :
    parseIntModelChars cs ≠ .error .overflow := by
  unfold parseIntModelChars
  split
  · simp
  · split <;> first | (simp; done) | exact parseDecAfterSign_ne_overflow _ _
  · split <;> first | (simp; done) | exact parseDecAfterSign_ne_overflow _ _
  · exact parseDecAfterSign_ne_overflow _ _
  · exact parseDecAfterSign_ne_overflow _ _
  · split
    · split
      · simp
      · simp
      · split
        · cases hci : consumeIntDigits _ _ _ with
          | ok _ => simp
          | error k =>
            intro hk
            cases hk
            exact consumeIntDigits_ne_overflow _ _ _ hci
        · simp
    · exact parseDecAfterSign_ne_overflow _ _
  · exact parseDecAfterSign_ne_overflow _ _

/-- `LeanSwe.NumParse.parseInt` never fails with `.overflow`. -/
theorem numparse_parseInt_never_overflow (s : String) :
    NeverErrorKindPure NumParseError.kind .overflow (LeanSwe.NumParse.parseInt s) := by
  cases h : LeanSwe.NumParse.parseInt s with
  | ok _ => trivial
  | error e =>
    change Internal.parseInt s = .error e at h
    have hmap := (parseInt_spec s).1
    rw [h] at hmap
    dsimp [Except.mapError, parseIntModel] at hmap
    intro hk
    rw [hk] at hmap
    exact parseIntModelChars_ne_overflow s.toList hmap.symm

private theorem consumeDecFloatDigits_err_ok (acc count : Nat) (cs : List Char)
    {k : NumParseErrorKind} (hk : consumeDecFloatDigits acc count cs = .error k) :
    k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  fun_induction consumeDecFloatDigits acc count cs with
  | case1 => cases hk
  | case2 _ _ _ _ _ ih1 => exact ih1 hk
  | case3 => cases hk; exact ⟨by decide, by decide⟩
  | case4 => cases hk; exact ⟨by decide, by decide⟩
  | case5 _ _ _ _ _ _ _ ih1 => exact ih1 hk
  | case6 => cases hk

private theorem parseFloatIntPart_err_ok (cs : List Char) {k : NumParseErrorKind}
    (hk : parseFloatIntPart cs = .error k) :
    k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  unfold parseFloatIntPart at hk
  split at hk
  · cases hk; exact ⟨by decide, by decide⟩
  · cases hk; exact ⟨by decide, by decide⟩
  · split at hk
    · split at hk
      · cases hk; exact ⟨by decide, by decide⟩
      · split at hk
        · split at hk
          · split at hk <;> cases hk <;> exact ⟨by decide, by decide⟩
          · cases hk; exact ⟨by decide, by decide⟩
        · cases hk
    · cases hk
  · split at hk
    · cases hcd : consumeDecFloatDigits _ 1 _ with
      | ok _ => rw [hcd] at hk; cases hk
      | error k0 => rw [hcd] at hk; cases hk; exact consumeDecFloatDigits_err_ok _ _ _ hcd
    · cases hk; exact ⟨by decide, by decide⟩

private theorem parseFloatExpPart_err_ok (cs : List Char) {k : NumParseErrorKind}
    (hk : parseFloatExpPart cs = .error k) :
    k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  unfold parseFloatExpPart at hk
  dsimp only at hk
  split at hk
  · cases hk; exact ⟨by decide, by decide⟩
  · cases hk; exact ⟨by decide, by decide⟩
  · split at hk
    · cases hcd : consumeDecFloatDigits _ 1 _ with
      | ok _ => rw [hcd] at hk; cases hk
      | error k0 => rw [hcd] at hk; cases hk; exact consumeDecFloatDigits_err_ok _ _ _ hcd
    · cases hk; exact ⟨by decide, by decide⟩

private theorem parseFloatModelChars_err_ok (cs : List Char) {k : NumParseErrorKind}
    (hk : parseFloatModelChars cs = .error k) :
    k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  unfold parseFloatModelChars at hk
  rcases cs with _ | ⟨c0, cs0⟩
  · cases hk; exact ⟨by decide, by decide⟩
  · dsimp only at hk
    split at hk
    · split at hk
      · cases hk
      · cases hk; exact ⟨by decide, by decide⟩
    · split at hk
      · cases hk
      · cases hk; exact ⟨by decide, by decide⟩
    · cases hp : parseFloatIntPart _ with
      | error k0 =>
        rw [hp] at hk
        cases hk
        exact parseFloatIntPart_err_ok _ hp
      | ok res =>
        rw [hp] at hk
        dsimp only at hk
        split at hk
        · split at hk
          · cases hk; exact ⟨by decide, by decide⟩
          · split at hk
            · cases hd : consumeDecFloatDigits _ _ _ with
              | error k1 =>
                rw [hd] at hk
                cases hk
                exact consumeDecFloatDigits_err_ok _ _ _ hd
              | ok res1 =>
                rw [hd] at hk
                dsimp only at hk
                split at hk
                · cases he : parseFloatExpPart _ with
                  | error k2 => rw [he] at hk; cases hk; exact parseFloatExpPart_err_ok _ he
                  | ok res2 =>
                    rw [he] at hk; dsimp only at hk
                    split at hk <;> cases hk
                    exact ⟨by decide, by decide⟩
                · cases he : parseFloatExpPart _ with
                  | error k2 => rw [he] at hk; cases hk; exact parseFloatExpPart_err_ok _ he
                  | ok res2 =>
                    rw [he] at hk; dsimp only at hk
                    split at hk <;> cases hk
                    exact ⟨by decide, by decide⟩
                · cases hk
                · cases hk; exact ⟨by decide, by decide⟩
            · cases hk; exact ⟨by decide, by decide⟩
          · cases hk; exact ⟨by decide, by decide⟩
        · cases he : parseFloatExpPart _ with
          | error k2 => rw [he] at hk; cases hk; exact parseFloatExpPart_err_ok _ he
          | ok res2 =>
            rw [he] at hk; dsimp only at hk
            split at hk <;> cases hk
            exact ⟨by decide, by decide⟩
        · cases he : parseFloatExpPart _ with
          | error k2 => rw [he] at hk; cases hk; exact parseFloatExpPart_err_ok _ he
          | ok res2 =>
            rw [he] at hk; dsimp only at hk
            split at hk <;> cases hk
            exact ⟨by decide, by decide⟩
        · cases hk; exact ⟨by decide, by decide⟩

private theorem parseFloat_err_ok (s : String) {e : NumParseError}
    (h : LeanSwe.NumParse.parseFloat s = .error e) :
    e.kind ≠ .invalidSignForBase ∧ e.kind ≠ .overflow := by
  change Internal.parseFloat s = .error e at h
  have hmap := (parseFloat_spec s).1
  rw [h] at hmap
  dsimp [Except.mapError, parseFloatModel] at hmap
  exact parseFloatModelChars_err_ok s.toList hmap.symm

/-- `LeanSwe.NumParse.parseFloat` never fails with `.invalidSignForBase`. -/
theorem numparse_parseFloat_never_invalidSignForBase (s : String) :
    NeverErrorKindPure NumParseError.kind .invalidSignForBase (LeanSwe.NumParse.parseFloat s) := by
  cases h : LeanSwe.NumParse.parseFloat s with
  | ok _ => trivial
  | error e => exact (parseFloat_err_ok s h).1

/-- `LeanSwe.NumParse.parseFloat` never fails with `.overflow`. -/
theorem numparse_parseFloat_never_overflow (s : String) :
    NeverErrorKindPure NumParseError.kind .overflow (LeanSwe.NumParse.parseFloat s) := by
  cases h : LeanSwe.NumParse.parseFloat s with
  | ok _ => trivial
  | error e => exact (parseFloat_err_ok s h).2

end LeanSwe.NumParse.Proofs
