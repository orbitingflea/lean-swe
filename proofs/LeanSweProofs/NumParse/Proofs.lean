import Core.Assumptions
import Core.Obeys
import LeanSweProofs.NumParse.Model.Obeys
import LeanSweProofs.NumParse.Proofs.IntProofs
import LeanSweProofs.NumParse.Proofs.FloatExpProofs
import LeanSweProofs.NumParse.Proofs.FloatParseProofs
import LeanSweProofs.NumParse.Proofs.SpecContractProofs
import LeanSweProofs.NumParse.Proofs.FloatRenderProofs
import LeanSweProofs.NumParse.Proofs.FloatFormatProofs

namespace LeanSwe.NumParse.Proofs

open Core
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem consumeIntDigits_ne_overflow (b : NumBase) (acc : Nat) (cs : List Char) :
    consumeIntDigits b acc cs ≠ .error .overflow := by
  fun_induction consumeIntDigits b acc cs <;> simp_all

private theorem parseDecAfterSign_ne_overflow (neg : Bool) (cs : List Char) :
    parseDecAfterSign neg cs ≠ .error .overflow := by
  unfold parseDecAfterSign
  repeat' (first | (simp; done) | (intro hk; cases hk; exact consumeIntDigits_ne_overflow .dec _ _ ‹_›) | split)

private theorem parseIntModelChars_ne_overflow (cs : List Char) :
    parseIntModelChars cs ≠ .error .overflow := by
  unfold parseIntModelChars
  repeat' (first | (simp; done) | exact parseDecAfterSign_ne_overflow _ _ | (intro hk; cases hk; exact consumeIntDigits_ne_overflow _ _ _ ‹_›) | split)

/-- `LeanSwe.NumParse.parseInt` never fails with `.overflow`. -/
theorem numparse_parseInt_never_overflow (s : String) :
    NeverErrorKindPure NumParseError.kind .overflow (LeanSwe.NumParse.parseInt s) := by
  cases h : LeanSwe.NumParse.parseInt s with
  | ok _ => trivial
  | error e =>
    change Internal.parseInt s = .error e at h; have hm := (parseInt_spec s).1; rw [h] at hm
    dsimp [Except.mapError, parseIntModel] at hm; intro hk; rw [hk] at hm; exact parseIntModelChars_ne_overflow s.toList hm.symm

private theorem consumeDecFloatDigits_err_ok (acc count : Nat) (cs : List Char)
    {k : NumParseErrorKind} (hk : consumeDecFloatDigits acc count cs = .error k) :
    k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  fun_induction consumeDecFloatDigits acc count cs with
  | case1 | case6 => cases hk
  | case2 _ _ _ _ _ ih | case5 _ _ _ _ _ _ _ ih => exact ih hk
  | case3 | case4 => cases hk; decide

private theorem parseFloatIntPart_err_ok (cs : List Char) {k : NumParseErrorKind}
    (hk : parseFloatIntPart cs = .error k) : k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  unfold parseFloatIntPart at hk
  repeat' (first | (cases hk; exact ⟨by decide, by decide⟩; done) | (cases hk; exact consumeDecFloatDigits_err_ok _ _ _ ‹_›; done) | (cases hk; done) | split at hk)

private theorem parseFloatExpPart_err_ok (cs : List Char) {k : NumParseErrorKind}
    (hk : parseFloatExpPart cs = .error k) : k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  unfold parseFloatExpPart at hk; dsimp only at hk
  repeat' (first | (cases hk; exact ⟨by decide, by decide⟩; done) | (cases hk; exact consumeDecFloatDigits_err_ok _ _ _ ‹_›; done) | (cases hk; done) | split at hk)

private theorem parseFloatModelChars_err_ok (cs : List Char) {k : NumParseErrorKind}
    (hk : parseFloatModelChars cs = .error k) : k ≠ .invalidSignForBase ∧ k ≠ .overflow := by
  unfold parseFloatModelChars at hk; dsimp only at hk
  repeat' (first | (cases hk; exact ⟨by decide, by decide⟩; done) | (cases hk; exact parseFloatIntPart_err_ok _ ‹_›; done) | (cases hk; exact consumeDecFloatDigits_err_ok _ _ _ ‹_›; done) | (cases hk; exact parseFloatExpPart_err_ok _ ‹_›; done) | (cases hk; done) | split at hk)

private theorem parseFloat_err_ok (s : String) {e : NumParseError}
    (h : LeanSwe.NumParse.parseFloat s = .error e) :
    e.kind ≠ .invalidSignForBase ∧ e.kind ≠ .overflow := by
  change Internal.parseFloat s = .error e at h
  have hm := (parseFloat_spec s).1; rw [h] at hm
  exact parseFloatModelChars_err_ok s.toList hm.symm

/-- `LeanSwe.NumParse.parseFloat` never fails with `.invalidSignForBase`. -/
theorem numparse_parseFloat_never_invalidSignForBase (s : String) :
    NeverErrorKindPure NumParseError.kind .invalidSignForBase (LeanSwe.NumParse.parseFloat s) := by
  cases h : LeanSwe.NumParse.parseFloat s with | ok _ => trivial | error e => exact (parseFloat_err_ok s h).1

/-- `LeanSwe.NumParse.parseFloat` never fails with `.overflow`. -/
theorem numparse_parseFloat_never_overflow (s : String) :
    NeverErrorKindPure NumParseError.kind .overflow (LeanSwe.NumParse.parseFloat s) := by
  cases h : LeanSwe.NumParse.parseFloat s with | ok _ => trivial | error e => exact (parseFloat_err_ok s h).2

/-- Full public `Interface` obedience of `LeanSwe.NumParse` against `LeanSwe.NumParse.Model`. -/
theorem obeys_model :
    Core.ObeysPure LeanSwe.NumParse.parseInt Model.allowedParseInt ∧
    Core.ObeysPure LeanSwe.NumParse.parseInt64 Model.allowedParseInt64 ∧
    Core.ObeysPure LeanSwe.NumParse.formatInt Model.allowedFormatInt ∧
    Core.ObeysPure LeanSwe.NumParse.parseFloat Model.allowedParseFloat ∧
    Core.ObeysPure LeanSwe.NumParse.formatFloat Model.allowedFormatFloat :=
  ⟨parseInt_spec,
   parseInt64_spec,
   allowedFormatInt_formatInt,
   parseFloat_spec,
   fun x => (proof_numparse_formatFloat_specAndRoundTrip x).1⟩

end LeanSwe.NumParse.Proofs
