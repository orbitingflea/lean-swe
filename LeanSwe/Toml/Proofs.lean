import Core.NondetTest
import Core.Refines
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.Interface
import LeanSwe.Toml.SpecTests
import LeanSwe.Toml.Proofs.Core
import LeanSwe.Toml.Proofs.ModelCheck
import LeanSwe.Toml.Proofs.FormatBridge
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Interface
import LeanSwe.NumParse.SpecTests
import LeanSwe.NumParse.Proofs

/-!
# Verified TOML 1.0 Implementation Entry Point

Exports the top-level specification proofs (`proof_toml_*`, `reach_toml_*`),
`validNumApi_defaultApi`, and error-kind non-occurrence theorems (`toml_*_never_*`).
-/

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
  | 0 => unfold LeanSwe.NumParse.Internal.natToDecCharsPos; exact hacc
  | m + 1 =>
    unfold LeanSwe.NumParse.Internal.natToDecCharsPos
    apply natToDecCharsPos_digits ((m + 1) / 10) _
    simp only [List.all_cons, hacc, Bool.and_true, Bool.or_eq_true]; left
    have hlt : (m + 1) % 10 < 10 := Nat.mod_lt _ (by decide)
    match hrm : (m + 1) % 10 with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
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
    | succ m => unfold LeanSwe.NumParse.Internal.formatIntChars; exact natToDecCharsPos_digits (m + 1) [] rfl
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

section
attribute [local irreducible] Core.AllPass Core.CanReach

/-- Concrete `AllPass` proof of `test_toml_onError_returnsNonEmptyMessage` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_onError_returnsNonEmptyMessage : Core.AllPass (test_toml_onError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := allPass_onError LeanSwe.NumParse.defaultApi
/-- Concrete `CanReach` witness for `test_toml_onError_returnsNonEmptyMessage`. -/
theorem reach_toml_onError_returnsNonEmptyMessage : Core.CanReach (test_toml_onError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := canReach_onError LeanSwe.NumParse.defaultApi
/-- Concrete `AllPass` proof of `test_toml_accessorError_returnsNonEmptyMessage` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_accessorError_returnsNonEmptyMessage : Core.AllPass (test_toml_accessorError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := allPass_accessorError LeanSwe.NumParse.defaultApi
/-- Concrete `CanReach` witness for `test_toml_accessorError_returnsNonEmptyMessage`. -/
theorem reach_toml_accessorError_returnsNonEmptyMessage : Core.CanReach (test_toml_accessorError_returnsNonEmptyMessage LeanSwe.Toml.defaultApi) := canReach_accessorError LeanSwe.NumParse.defaultApi
/-- Concrete `AllPass` proof of `test_toml_parse_returnsWellFormedTable` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_parse_returnsWellFormedTable : Core.AllPass (test_toml_parse_returnsWellFormedTable LeanSwe.Toml.defaultApi) := allPass_parse_returnsWellFormedTable LeanSwe.NumParse.defaultApi
/-- Concrete `CanReach` witness for `test_toml_parse_returnsWellFormedTable`. -/
theorem reach_toml_parse_returnsWellFormedTable : Core.CanReach (test_toml_parse_returnsWellFormedTable LeanSwe.Toml.defaultApi) := canReach_parse_returnsWellFormedTable LeanSwe.NumParse.defaultApi
/-- Concrete `AllPass` proof of `test_toml_render_parse_roundTrip` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_render_parse_roundTrip : Core.AllPass (test_toml_render_parse_roundTrip LeanSwe.Toml.defaultApi) := allPass_render_parse_roundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `CanReach` witness for `test_toml_render_parse_roundTrip`. -/
theorem reach_toml_render_parse_roundTrip : Core.CanReach (test_toml_render_parse_roundTrip LeanSwe.Toml.defaultApi) := canReach_render_parse_roundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `AllPass` proof of `test_toml_format_validAndRoundTrip` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_format_validAndRoundTrip : Core.AllPass (test_toml_format_validAndRoundTrip LeanSwe.Toml.defaultApi) := allPass_format_validAndRoundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `CanReach` witness for `test_toml_format_validAndRoundTrip`. -/
theorem reach_toml_format_validAndRoundTrip : Core.CanReach (test_toml_format_validAndRoundTrip LeanSwe.Toml.defaultApi) := canReach_format_validAndRoundTrip LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `AllPass` proof of `test_toml_keysAndProvenance_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_keysAndProvenance_conformsToSpec : Core.AllPass (test_toml_keysAndProvenance_conformsToSpec LeanSwe.Toml.defaultApi) := allPass_keysAndProvenance LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `CanReach` witness for `test_toml_keysAndProvenance_conformsToSpec`. -/
theorem reach_toml_keysAndProvenance_conformsToSpec : Core.CanReach (test_toml_keysAndProvenance_conformsToSpec LeanSwe.Toml.defaultApi) := canReach_keysAndProvenance LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `AllPass` proof of `test_toml_inlineTablesAndAot_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_inlineTablesAndAot_conformsToSpec : Core.AllPass (test_toml_inlineTablesAndAot_conformsToSpec LeanSwe.Toml.defaultApi) := allPass_inlineTablesAndAot LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `CanReach` witness for `test_toml_inlineTablesAndAot_conformsToSpec`. -/
theorem reach_toml_inlineTablesAndAot_conformsToSpec : Core.CanReach (test_toml_inlineTablesAndAot_conformsToSpec LeanSwe.Toml.defaultApi) := canReach_inlineTablesAndAot LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `AllPass` proof of `test_toml_stringsAndControls_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_stringsAndControls_conformsToSpec : Core.AllPass (test_toml_stringsAndControls_conformsToSpec LeanSwe.Toml.defaultApi) := allPass_stringsAndControls LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `CanReach` witness for `test_toml_stringsAndControls_conformsToSpec`. -/
theorem reach_toml_stringsAndControls_conformsToSpec : Core.CanReach (test_toml_stringsAndControls_conformsToSpec LeanSwe.Toml.defaultApi) := canReach_stringsAndControls LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `AllPass` proof of `test_toml_numbersAndDatetimes_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_numbersAndDatetimes_conformsToSpec : Core.AllPass (test_toml_numbersAndDatetimes_conformsToSpec LeanSwe.Toml.defaultApi) := allPass_numbersAndDatetimes LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `CanReach` witness for `test_toml_numbersAndDatetimes_conformsToSpec`. -/
theorem reach_toml_numbersAndDatetimes_conformsToSpec : Core.CanReach (test_toml_numbersAndDatetimes_conformsToSpec LeanSwe.Toml.defaultApi) := canReach_numbersAndDatetimes LeanSwe.NumParse.defaultApi validNumApi_defaultApi
/-- Concrete `AllPass` proof of `test_toml_codecsAndAccessors_conformsToSpec` for `LeanSwe.Toml.defaultApi`. -/
theorem proof_toml_codecsAndAccessors_conformsToSpec : Core.AllPass (test_toml_codecsAndAccessors_conformsToSpec LeanSwe.Toml.defaultApi) := allPass_codecsAndAccessors LeanSwe.NumParse.defaultApi
/-- Concrete `CanReach` witness for `test_toml_codecsAndAccessors_conformsToSpec`. -/
theorem reach_toml_codecsAndAccessors_conformsToSpec : Core.CanReach (test_toml_codecsAndAccessors_conformsToSpec LeanSwe.Toml.defaultApi) := canReach_codecsAndAccessors LeanSwe.NumParse.defaultApi

end

private theorem parse_never_of (k : TomlErrorKind)
    (hk : k = .missingField ∨ k = .typeMismatch ∨ k = .decodeError) (raw : String) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.parse raw) := by
  show Core.NeverErrorKindPure TomlError.kind k (parseWithNum LeanSwe.NumParse.defaultApi raw)
  unfold Core.NeverErrorKindPure parseWithNum
  cases hp : parseCharsWithNum (toCharNumApi LeanSwe.NumParse.defaultApi) raw.toList with
  | ok _ => trivial
  | error e =>
    have ⟨_, h1, h2, h3⟩ := parseCharsWithNum_err_ok _ _ hp
    rcases hk with rfl | rfl | rfl <;> assumption

/-- `Toml.parse` never returns `.missingField`. -/
theorem toml_parse_never_missingField (raw : String) : Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.parse raw) := parse_never_of .missingField (Or.inl rfl) raw
/-- `Toml.parse` never returns `.typeMismatch`. -/
theorem toml_parse_never_typeMismatch (raw : String) : Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.parse raw) := parse_never_of .typeMismatch (Or.inr (Or.inl rfl)) raw
/-- `Toml.parse` never returns `.decodeError`. -/
theorem toml_parse_never_decodeError (raw : String) : Core.NeverErrorKindPure TomlError.kind .decodeError (LeanSwe.Toml.parse raw) := parse_never_of .decodeError (Or.inr (Or.inr rfl)) raw

private theorem decode_never_of (k : TomlErrorKind) (hk : k ≠ .decodeError)
    (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.decode (α := α) v) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.decode tomlDecode
  cases (FromToml.fromToml v : Except TomlError α) with | ok _ => trivial | error _ => exact hk.symm

/-- `Toml.decode` never returns `.parseError`. -/
theorem toml_decode_never_parseError (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.decode (α := α) v) := decode_never_of .parseError (by decide) α v
/-- `Toml.decode` never returns `.duplicateKey`. -/
theorem toml_decode_never_duplicateKey (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.decode (α := α) v) := decode_never_of .duplicateKey (by decide) α v
/-- `Toml.decode` never returns `.redefinedTable`. -/
theorem toml_decode_never_redefinedTable (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.decode (α := α) v) := decode_never_of .redefinedTable (by decide) α v
/-- `Toml.decode` never returns `.immutableInlineTable`. -/
theorem toml_decode_never_immutableInlineTable (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.decode (α := α) v) := decode_never_of .immutableInlineTable (by decide) α v
/-- `Toml.decode` never returns `.invalidUtf8OrControl`. -/
theorem toml_decode_never_invalidUtf8OrControl (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.decode (α := α) v) := decode_never_of .invalidUtf8OrControl (by decide) α v
/-- `Toml.decode` never returns `.numericOverflow`. -/
theorem toml_decode_never_numericOverflow (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.decode (α := α) v) := decode_never_of .numericOverflow (by decide) α v
/-- `Toml.decode` never returns `.missingField`. -/
theorem toml_decode_never_missingField (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.decode (α := α) v) := decode_never_of .missingField (by decide) α v
/-- `Toml.decode` never returns `.typeMismatch`. -/
theorem toml_decode_never_typeMismatch (α : Type) [FromToml α] (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.decode (α := α) v) := decode_never_of .typeMismatch (by decide) α v

private theorem getTable_never_of (k : TomlErrorKind) (hk : k ≠ .typeMismatch) (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getTable v) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getTable tomlGetTable
  cases v <;> first | trivial | exact hk.symm

/-- `Toml.getTable` never returns `.parseError`. -/
theorem toml_getTable_never_parseError (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getTable v) := getTable_never_of .parseError (by decide) v
/-- `Toml.getTable` never returns `.duplicateKey`. -/
theorem toml_getTable_never_duplicateKey (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getTable v) := getTable_never_of .duplicateKey (by decide) v
/-- `Toml.getTable` never returns `.redefinedTable`. -/
theorem toml_getTable_never_redefinedTable (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getTable v) := getTable_never_of .redefinedTable (by decide) v
/-- `Toml.getTable` never returns `.immutableInlineTable`. -/
theorem toml_getTable_never_immutableInlineTable (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getTable v) := getTable_never_of .immutableInlineTable (by decide) v
/-- `Toml.getTable` never returns `.invalidUtf8OrControl`. -/
theorem toml_getTable_never_invalidUtf8OrControl (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getTable v) := getTable_never_of .invalidUtf8OrControl (by decide) v
/-- `Toml.getTable` never returns `.numericOverflow`. -/
theorem toml_getTable_never_numericOverflow (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getTable v) := getTable_never_of .numericOverflow (by decide) v
/-- `Toml.getTable` never returns `.missingField`. -/
theorem toml_getTable_never_missingField (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.getTable v) := getTable_never_of .missingField (by decide) v
/-- `Toml.getTable` never returns `.decodeError`. -/
theorem toml_getTable_never_decodeError (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .decodeError (LeanSwe.Toml.getTable v) := getTable_never_of .decodeError (by decide) v

private theorem getArray_never_of (k : TomlErrorKind) (hk : k ≠ .typeMismatch) (v : TomlValue) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getArray v) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getArray tomlGetArray
  cases v <;> first | trivial | exact hk.symm

/-- `Toml.getArray` never returns `.parseError`. -/
theorem toml_getArray_never_parseError (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getArray v) := getArray_never_of .parseError (by decide) v
/-- `Toml.getArray` never returns `.duplicateKey`. -/
theorem toml_getArray_never_duplicateKey (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getArray v) := getArray_never_of .duplicateKey (by decide) v
/-- `Toml.getArray` never returns `.redefinedTable`. -/
theorem toml_getArray_never_redefinedTable (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getArray v) := getArray_never_of .redefinedTable (by decide) v
/-- `Toml.getArray` never returns `.immutableInlineTable`. -/
theorem toml_getArray_never_immutableInlineTable (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getArray v) := getArray_never_of .immutableInlineTable (by decide) v
/-- `Toml.getArray` never returns `.invalidUtf8OrControl`. -/
theorem toml_getArray_never_invalidUtf8OrControl (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getArray v) := getArray_never_of .invalidUtf8OrControl (by decide) v
/-- `Toml.getArray` never returns `.numericOverflow`. -/
theorem toml_getArray_never_numericOverflow (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getArray v) := getArray_never_of .numericOverflow (by decide) v
/-- `Toml.getArray` never returns `.missingField`. -/
theorem toml_getArray_never_missingField (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.getArray v) := getArray_never_of .missingField (by decide) v
/-- `Toml.getArray` never returns `.decodeError`. -/
theorem toml_getArray_never_decodeError (v : TomlValue) : Core.NeverErrorKindPure TomlError.kind .decodeError (LeanSwe.Toml.getArray v) := getArray_never_of .decodeError (by decide) v

private theorem getField_never_of (k : TomlErrorKind) (hk1 : k ≠ .missingField) (hk2 : k ≠ .decodeError)
    (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getField (α := α) t key) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getField tomlGetField
  cases lookupKey key t with
  | none => exact hk1.symm
  | some v => dsimp only; cases (FromToml.fromToml v : Except TomlError α) <;> first | trivial | exact hk2.symm

/-- `Toml.getField` never returns `.parseError`. -/
theorem toml_getField_never_parseError (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getField (α := α) t key) := getField_never_of .parseError (by decide) (by decide) α t key
/-- `Toml.getField` never returns `.duplicateKey`. -/
theorem toml_getField_never_duplicateKey (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getField (α := α) t key) := getField_never_of .duplicateKey (by decide) (by decide) α t key
/-- `Toml.getField` never returns `.redefinedTable`. -/
theorem toml_getField_never_redefinedTable (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getField (α := α) t key) := getField_never_of .redefinedTable (by decide) (by decide) α t key
/-- `Toml.getField` never returns `.immutableInlineTable`. -/
theorem toml_getField_never_immutableInlineTable (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getField (α := α) t key) := getField_never_of .immutableInlineTable (by decide) (by decide) α t key
/-- `Toml.getField` never returns `.invalidUtf8OrControl`. -/
theorem toml_getField_never_invalidUtf8OrControl (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getField (α := α) t key) := getField_never_of .invalidUtf8OrControl (by decide) (by decide) α t key
/-- `Toml.getField` never returns `.numericOverflow`. -/
theorem toml_getField_never_numericOverflow (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getField (α := α) t key) := getField_never_of .numericOverflow (by decide) (by decide) α t key
/-- `Toml.getField` never returns `.typeMismatch`. -/
theorem toml_getField_never_typeMismatch (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.getField (α := α) t key) := getField_never_of .typeMismatch (by decide) (by decide) α t key

private theorem getOptField_never_of (k : TomlErrorKind) (hk : k ≠ .decodeError)
    (α : Type) [FromToml α] (t : TomlTable) (key : String) :
    Core.NeverErrorKindPure TomlError.kind k (LeanSwe.Toml.getOptField (α := α) t key) := by
  unfold Core.NeverErrorKindPure LeanSwe.Toml.getOptField tomlGetOptField
  cases lookupKey key t with
  | none => trivial
  | some v => dsimp only; cases (FromToml.fromToml v : Except TomlError α) <;> first | trivial | exact hk.symm

/-- `Toml.getOptField` never returns `.parseError`. -/
theorem toml_getOptField_never_parseError (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .parseError (by decide) α t key
/-- `Toml.getOptField` never returns `.duplicateKey`. -/
theorem toml_getOptField_never_duplicateKey (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .duplicateKey (by decide) α t key
/-- `Toml.getOptField` never returns `.redefinedTable`. -/
theorem toml_getOptField_never_redefinedTable (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .redefinedTable (by decide) α t key
/-- `Toml.getOptField` never returns `.immutableInlineTable`. -/
theorem toml_getOptField_never_immutableInlineTable (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .immutableInlineTable (by decide) α t key
/-- `Toml.getOptField` never returns `.invalidUtf8OrControl`. -/
theorem toml_getOptField_never_invalidUtf8OrControl (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .invalidUtf8OrControl (by decide) α t key
/-- `Toml.getOptField` never returns `.numericOverflow`. -/
theorem toml_getOptField_never_numericOverflow (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .numericOverflow (by decide) α t key
/-- `Toml.getOptField` never returns `.missingField`. -/
theorem toml_getOptField_never_missingField (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .missingField (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .missingField (by decide) α t key
/-- `Toml.getOptField` never returns `.typeMismatch`. -/
theorem toml_getOptField_never_typeMismatch (α : Type) [FromToml α] (t : TomlTable) (key : String) : Core.NeverErrorKindPure TomlError.kind .typeMismatch (LeanSwe.Toml.getOptField (α := α) t key) := getOptField_never_of .typeMismatch (by decide) α t key

private theorem getPathAux_never_of (k : TomlErrorKind)
    (hk1 : k ≠ .missingField) (hk2 : k ≠ .typeMismatch) (hk3 : k ≠ .decodeError)
    (α : Type) [FromToml α] (revPrefix : List String) (t : TomlTable) (keys : List String) :
    Core.NeverErrorKindPure TomlError.kind k (tomlGetPathAux (α := α) revPrefix t keys) := by
  induction keys generalizing revPrefix t with
  | nil =>
    unfold Core.NeverErrorKindPure tomlGetPathAux
    cases (FromToml.fromToml (.table t) : Except TomlError α) <;> first | trivial | exact hk3.symm
  | cons hd tl ih =>
    cases tl with
    | nil =>
      unfold Core.NeverErrorKindPure tomlGetPathAux
      cases lookupKey hd t with
      | none => exact hk1.symm
      | some v => dsimp only; cases (FromToml.fromToml v : Except TomlError α) <;> first | trivial | exact hk3.symm
    | cons _ _ =>
      unfold Core.NeverErrorKindPure tomlGetPathAux
      cases lookupKey hd t with
      | none => exact hk1.symm
      | some v =>
        dsimp only
        cases v with
        | table sub => exact ih (hd :: revPrefix) sub
        | _ => exact hk2.symm

/-- `Toml.getPath` never returns `.parseError`. -/
theorem toml_getPath_never_parseError (α : Type) [FromToml α] (t : TomlTable) (keys : List String) : Core.NeverErrorKindPure TomlError.kind .parseError (LeanSwe.Toml.getPath (α := α) t keys) := getPathAux_never_of .parseError (by decide) (by decide) (by decide) α [] t keys
/-- `Toml.getPath` never returns `.duplicateKey`. -/
theorem toml_getPath_never_duplicateKey (α : Type) [FromToml α] (t : TomlTable) (keys : List String) : Core.NeverErrorKindPure TomlError.kind .duplicateKey (LeanSwe.Toml.getPath (α := α) t keys) := getPathAux_never_of .duplicateKey (by decide) (by decide) (by decide) α [] t keys
/-- `Toml.getPath` never returns `.redefinedTable`. -/
theorem toml_getPath_never_redefinedTable (α : Type) [FromToml α] (t : TomlTable) (keys : List String) : Core.NeverErrorKindPure TomlError.kind .redefinedTable (LeanSwe.Toml.getPath (α := α) t keys) := getPathAux_never_of .redefinedTable (by decide) (by decide) (by decide) α [] t keys
/-- `Toml.getPath` never returns `.immutableInlineTable`. -/
theorem toml_getPath_never_immutableInlineTable (α : Type) [FromToml α] (t : TomlTable) (keys : List String) : Core.NeverErrorKindPure TomlError.kind .immutableInlineTable (LeanSwe.Toml.getPath (α := α) t keys) := getPathAux_never_of .immutableInlineTable (by decide) (by decide) (by decide) α [] t keys
/-- `Toml.getPath` never returns `.invalidUtf8OrControl`. -/
theorem toml_getPath_never_invalidUtf8OrControl (α : Type) [FromToml α] (t : TomlTable) (keys : List String) : Core.NeverErrorKindPure TomlError.kind .invalidUtf8OrControl (LeanSwe.Toml.getPath (α := α) t keys) := getPathAux_never_of .invalidUtf8OrControl (by decide) (by decide) (by decide) α [] t keys
/-- `Toml.getPath` never returns `.numericOverflow`. -/
theorem toml_getPath_never_numericOverflow (α : Type) [FromToml α] (t : TomlTable) (keys : List String) : Core.NeverErrorKindPure TomlError.kind .numericOverflow (LeanSwe.Toml.getPath (α := α) t keys) := getPathAux_never_of .numericOverflow (by decide) (by decide) (by decide) α [] t keys

private theorem allowedParse_holds (raw : String) :
    Model.allowedParse raw (LeanSwe.Toml.parse raw) := by
  have hwf := proof_toml_parse_returnsWellFormedTable raw
  have herr := proof_toml_onError_returnsNonEmptyMessage raw
  dsimp only [Core.AllPass, Core.AllPassRun, test_toml_parse_returnsWellFormedTable,
    test_toml_onError_returnsNonEmptyMessage, LeanSwe.Toml.defaultApi, makeTomlApi,
    Core.NondetTest.nondet, Core.NondetTest.assert, bind, pure] at hwf herr
  change Model.allowedParse raw (parseWithNum LeanSwe.NumParse.defaultApi raw)
  cases hp : parseWithNum LeanSwe.NumParse.defaultApi raw with
  | ok parsed =>
    rw [hp] at hwf
    refine ⟨hwf.1, fun doc tape hr => ?_⟩
    have hrt := proof_toml_render_parse_roundTrip (doc, tape)
    dsimp only [Core.AllPass, Core.AllPassRun, test_toml_render_parse_roundTrip,
      LeanSwe.Toml.defaultApi, makeTomlApi, Core.NondetTest.nondet, Core.NondetTest.assume,
      Core.NondetTest.assert, bind, pure] at hrt
    rw [hr] at hrt
    dsimp only at hrt
    rw [hp] at hrt
    exact hrt.1
  | error e =>
    rw [hp] at herr
    refine ⟨herr.1, fun doc tape hr => ?_⟩
    have hrt := proof_toml_render_parse_roundTrip (doc, tape)
    dsimp only [Core.AllPass, Core.AllPassRun, test_toml_render_parse_roundTrip,
      LeanSwe.Toml.defaultApi, makeTomlApi, Core.NondetTest.nondet, Core.NondetTest.assume,
      Core.NondetTest.assert, bind, pure] at hrt
    rw [hr] at hrt
    dsimp only at hrt
    rw [hp] at hrt
    exact hrt.1

private theorem nonEmptyMsg_ne_empty (msg : String) : nonEmptyMsg msg ≠ "" := by
  unfold nonEmptyMsg
  by_cases h : msg.isEmpty = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    intro he
    subst he
    exact h rfl

private theorem nonEmptyMsg_not_isEmpty (msg : String) : !(nonEmptyMsg msg).isEmpty = true := by
  simp [nonEmptyMsg_ne_empty]

private theorem allowedGetTable_holds (v : TomlValue) :
    Model.allowedGetTable v (LeanSwe.Toml.getTable v) := by
  cases v <;> simp [Model.allowedGetTable, LeanSwe.Toml.getTable, tomlGetTable, mkErr, nonEmptyMsg_ne_empty]

private theorem allowedGetArray_holds (v : TomlValue) :
    Model.allowedGetArray v (LeanSwe.Toml.getArray v) := by
  cases v <;> simp [Model.allowedGetArray, LeanSwe.Toml.getArray, tomlGetArray, mkErr, nonEmptyMsg_ne_empty]

private theorem allowedDecode_holds {α : Type} [FromToml α] (v : TomlValue) :
    Model.allowedDecode v (LeanSwe.Toml.decode (α := α) v) := by
  unfold Model.allowedDecode LeanSwe.Toml.decode tomlDecode
  cases FromToml.fromToml (α := α) v <;> simp [nonEmptyMsg_ne_empty]

private theorem allowedGetField_holds {α : Type} [FromToml α] (t : TomlTable) (key : String) :
    Model.allowedGetField t key (LeanSwe.Toml.getField (α := α) t key) := by
  unfold Model.allowedGetField LeanSwe.Toml.getField tomlGetField
  cases lookupKey key t with
  | none => simp [mkErr, nonEmptyMsg_ne_empty]
  | some v =>
    cases hf : FromToml.fromToml (α := α) v
    · simp [hf, Except.isOk, Except.toBool, nonEmptyMsg_ne_empty]
    · simp [hf]

private theorem allowedGetOptField_holds {α : Type} [FromToml α] (t : TomlTable) (key : String) :
    Model.allowedGetOptField t key (LeanSwe.Toml.getOptField (α := α) t key) := by
  unfold Model.allowedGetOptField LeanSwe.Toml.getOptField tomlGetOptField
  cases lookupKey key t with
  | none => trivial
  | some v =>
    cases hf : FromToml.fromToml (α := α) v
    · simp [hf, Except.isOk, Except.toBool, nonEmptyMsg_ne_empty]
    · simp [hf]

private theorem allowedGetPathAux_holds {α : Type} [FromToml α]
    (revPrefix : List String) (t : TomlTable) (keys : List String) :
    Model.allowedGetPathAux revPrefix t keys (tomlGetPathAux (α := α) revPrefix t keys) := by
  induction keys generalizing revPrefix t with
  | nil =>
    unfold Model.allowedGetPathAux tomlGetPathAux
    cases FromToml.fromToml (α := α) (.table t)
    · simp [nonEmptyMsg_ne_empty]
    · simp
  | cons k rest ih =>
    cases rest with
    | nil =>
      unfold Model.allowedGetPathAux tomlGetPathAux joinPath
      cases lookupKey k t with
      | none => simp [mkErr, nonEmptyMsg_ne_empty]
      | some v =>
        cases hf : FromToml.fromToml (α := α) v
        · simp [hf, Except.isOk, Except.toBool, nonEmptyMsg_ne_empty]
        · simp [hf]
    | cons k' tl =>
      unfold Model.allowedGetPathAux tomlGetPathAux joinPath
      cases lookupKey k t with
      | none => exact ⟨_, rfl, rfl, rfl, nonEmptyMsg_not_isEmpty _⟩
      | some v =>
        cases v with
        | table sub => exact ih (k :: revPrefix) sub
        | _ => exact ⟨_, rfl, rfl, rfl, nonEmptyMsg_not_isEmpty _⟩

/-- Full public `Interface` refinement of `LeanSwe.Toml` against `LeanSwe.Toml.Model`. -/
theorem refines_model :
    Core.RefinesPure LeanSwe.Toml.parse Model.allowedParse ∧
    Core.RefinesPure LeanSwe.Toml.format Model.allowedFormat ∧
    Core.RefinesPure LeanSwe.Toml.getTable Model.allowedGetTable ∧
    Core.RefinesPure LeanSwe.Toml.getArray Model.allowedGetArray ∧
    (∀ {α : Type} [FromToml α], Core.RefinesPure (@LeanSwe.Toml.decode α _) (@Model.allowedDecode α _)) ∧
    (∀ {α : Type} [ToToml α], Core.RefinesPureEq (@LeanSwe.Toml.encode α _) (@Model.encodeModel α _)) ∧
    (∀ {α : Type} [FromToml α], Core.RefinesPure2 (@LeanSwe.Toml.getField α _) (@Model.allowedGetField α _)) ∧
    (∀ {α : Type} [FromToml α], Core.RefinesPure2 (@LeanSwe.Toml.getOptField α _) (@Model.allowedGetOptField α _)) ∧
    (∀ {α : Type} [FromToml α], Core.RefinesPure2 (@LeanSwe.Toml.getPath α _) (@Model.allowedGetPath α _)) :=
  ⟨allowedParse_holds,
   formatWithNum_allowedFormat LeanSwe.NumParse.defaultApi validNumApi_defaultApi,
   allowedGetTable_holds,
   allowedGetArray_holds,
   fun v => allowedDecode_holds v,
   fun _ => rfl,
   fun t key => allowedGetField_holds t key,
   fun t key => allowedGetOptField_holds t key,
   fun t keys => allowedGetPathAux_holds [] t keys⟩

end LeanSwe.Toml.Proofs
