import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.Interface
import LeanSwe.Toml.SpecTests
import LeanSwe.Toml.Proofs.Parametric
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs

namespace LeanSwe.Toml.Proofs

open Core
open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

private theorem natToDecCharsPos_digits (n : Nat) (acc : List Char)
    (hacc : acc.all (fun c => isAsciiDigit c || c == '-') = true) :
    (LeanSwe.NumParse.Internal.natToDecCharsPos n acc).all
      (fun c => isAsciiDigit c || c == '-') = true := by
  match n with
  | 0 =>
    unfold LeanSwe.NumParse.Internal.natToDecCharsPos
    exact hacc
  | m + 1 =>
    unfold LeanSwe.NumParse.Internal.natToDecCharsPos
    apply natToDecCharsPos_digits ((m + 1) / 10) _
    simp only [List.all_cons, hacc, Bool.and_true, Bool.or_eq_true]
    left
    have hlt : (m + 1) % 10 < 10 := Nat.mod_lt _ (by decide)
    match hrm : (m + 1) % 10 with
    | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
    | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
    | _ + 10 => omega
termination_by n

private theorem defaultNumApi_formatIntChars (n : Int) :
    (LeanSwe.NumParse.defaultApi.formatInt n).toList.all
      (fun c => isAsciiDigit c || c == '-') = true := by
  change (String.ofList (LeanSwe.NumParse.Internal.formatIntChars n)).toList.all
      (fun c => isAsciiDigit c || c == '-') = true
  rw [String.toList_ofList]
  cases n with
  | ofNat k =>
    cases k with
    | zero => decide
    | succ m =>
      unfold LeanSwe.NumParse.Internal.formatIntChars
      exact natToDecCharsPos_digits (m + 1) [] rfl
  | negSucc k =>
    unfold LeanSwe.NumParse.Internal.formatIntChars
    simp only [List.all_cons, (by decide : (isAsciiDigit '-' || '-' == '-') = true), Bool.true_and]
    exact natToDecCharsPos_digits (k + 1) [] rfl

/-- Concrete `ValidNumApi` witness for `LeanSwe.NumParse.defaultApi`. -/
theorem validNumApi_defaultApi : ValidNumApi LeanSwe.NumParse.defaultApi :=
  { onError := LeanSwe.NumParse.Proofs.proof_numparse_onError_returnsNonEmptyMessage
  , parseInt64 := LeanSwe.NumParse.Proofs.proof_numparse_parseInt64_matchesModel
  , parseFloat := LeanSwe.NumParse.Proofs.proof_numparse_parseFloat_matchesModel
  , formatInt := LeanSwe.NumParse.Proofs.proof_numparse_formatInt_roundTrip
  , formatFloat := LeanSwe.NumParse.Proofs.proof_numparse_formatFloat_specAndRoundTrip
  , formatIntChars := defaultNumApi_formatIntChars
  }

private theorem defaultApi_eq :
    LeanSwe.Toml.defaultApi = Impl.makeTomlApi LeanSwe.NumParse.defaultApi := rfl

section
attribute [local irreducible] Core.AllPass Core.CanReach

/-- Concrete `AllPass` proof of `test_toml_onError_returnsNonEmptyMessage` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_onError_returnsNonEmptyMessage :
    Core.AllPass (test_toml_onError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_onError LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_onError_returnsNonEmptyMessage`. -/
theorem reach_toml_onError_returnsNonEmptyMessage :
    Core.CanReach (test_toml_onError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_onError LeanSwe.NumParse.defaultApi

/-- Concrete `AllPass` proof of `test_toml_accessorError_returnsNonEmptyMessage` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_accessorError_returnsNonEmptyMessage :
    Core.AllPass (test_toml_accessorError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_accessorError LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_accessorError_returnsNonEmptyMessage`. -/
theorem reach_toml_accessorError_returnsNonEmptyMessage :
    Core.CanReach (test_toml_accessorError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_accessorError LeanSwe.NumParse.defaultApi

/-- Concrete `AllPass` proof of `test_toml_parse_returnsWellFormedTable` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_parse_returnsWellFormedTable :
    Core.AllPass (test_toml_parse_returnsWellFormedTable LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_parse_returnsWellFormedTable LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_parse_returnsWellFormedTable`. -/
theorem reach_toml_parse_returnsWellFormedTable :
    Core.CanReach (test_toml_parse_returnsWellFormedTable LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_parse_returnsWellFormedTable LeanSwe.NumParse.defaultApi

/-- Concrete `AllPass` proof of `test_toml_render_parse_roundTrip` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_render_parse_roundTrip :
    Core.AllPass (test_toml_render_parse_roundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_render_parse_roundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_render_parse_roundTrip`. -/
theorem reach_toml_render_parse_roundTrip :
    Core.CanReach (test_toml_render_parse_roundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_render_parse_roundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_format_validAndRoundTrip` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_format_validAndRoundTrip :
    Core.AllPass (test_toml_format_validAndRoundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_format_validAndRoundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_format_validAndRoundTrip`. -/
theorem reach_toml_format_validAndRoundTrip :
    Core.CanReach (test_toml_format_validAndRoundTrip LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_format_validAndRoundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_keysAndProvenance_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_keysAndProvenance_conformsToSpec :
    Core.AllPass (test_toml_keysAndProvenance_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_keysAndProvenance LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_keysAndProvenance_conformsToSpec`. -/
theorem reach_toml_keysAndProvenance_conformsToSpec :
    Core.CanReach (test_toml_keysAndProvenance_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_keysAndProvenance LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_inlineTablesAndAot_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_inlineTablesAndAot_conformsToSpec :
    Core.AllPass (test_toml_inlineTablesAndAot_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_inlineTablesAndAot LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_inlineTablesAndAot_conformsToSpec`. -/
theorem reach_toml_inlineTablesAndAot_conformsToSpec :
    Core.CanReach (test_toml_inlineTablesAndAot_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_inlineTablesAndAot LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_stringsAndControls_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_stringsAndControls_conformsToSpec :
    Core.AllPass (test_toml_stringsAndControls_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_stringsAndControls LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_stringsAndControls_conformsToSpec`. -/
theorem reach_toml_stringsAndControls_conformsToSpec :
    Core.CanReach (test_toml_stringsAndControls_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_stringsAndControls LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_numbersAndDatetimes_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_numbersAndDatetimes_conformsToSpec :
    Core.AllPass (test_toml_numbersAndDatetimes_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_numbersAndDatetimes LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `CanReach` witness for `test_toml_numbersAndDatetimes_conformsToSpec`. -/
theorem reach_toml_numbersAndDatetimes_conformsToSpec :
    Core.CanReach (test_toml_numbersAndDatetimes_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_numbersAndDatetimes LeanSwe.NumParse.defaultApi validNumApi_defaultApi

/-- Concrete `AllPass` proof of `test_toml_codecsAndAccessors_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_codecsAndAccessors_conformsToSpec :
    Core.AllPass (test_toml_codecsAndAccessors_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact allPass_codecsAndAccessors LeanSwe.NumParse.defaultApi

/-- Concrete `CanReach` witness for `test_toml_codecsAndAccessors_conformsToSpec`. -/
theorem reach_toml_codecsAndAccessors_conformsToSpec :
    Core.CanReach (test_toml_codecsAndAccessors_conformsToSpec LeanSwe.Toml.defaultApi) := by
  rw [defaultApi_eq]
  exact canReach_codecsAndAccessors LeanSwe.NumParse.defaultApi

end

end LeanSwe.Toml.Proofs
