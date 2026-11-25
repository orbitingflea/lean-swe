import Core.NondetTest
import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model
import LeanSwe.Toml.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Toml`. -/

namespace LeanSwe.Toml

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.NumParse.Model

private def stubTomlApi : TomlApi :=
  { parse := fun _ => .error { kind := .parseError, message := "" }
  , format := fun _ => ""
  , decode := fun _ => .error { kind := .decodeError, message := "" }
  , encode := ToToml.toToml
  , getTable := fun _ => .error { kind := .typeMismatch, message := "" }
  , getArray := fun _ => .error { kind := .typeMismatch, message := "" }
  , getField := fun _ _ => .error { kind := .missingField, message := "" }
  , getOptField := fun _ _ => .ok none
  , getPath := fun _ _ => .error { kind := .missingField, message := "" }
  }

example : ¬ Core.AllPass (test_toml_onError_returnsNonEmptyMessage stubTomlApi) := by
  intro h
  have h0 := h ""
  simp [stubTomlApi, assert] at h0

example : ¬ Core.AllPass (test_toml_accessorError_returnsNonEmptyMessage stubTomlApi) := by
  intro h
  have h0 := h (.int 0) #[] "" []
  simp [stubTomlApi, bind, pure, assert] at h0

private def illFormedParseApi : TomlApi :=
  { stubTomlApi with
    parse := fun _ => .ok #[("dup", .int 1), ("dup", .int 2)] }

example : ¬ Core.AllPass (test_toml_parse_returnsWellFormedTable illFormedParseApi) := by
  intro h
  have h0 := h ""
  simp [illFormedParseApi, Model.WellFormedTable, Model.wellFormedTableBool,
    Model.noDupKeysBool, Model.hasKeyList, assert] at h0

private def buggyWrongAstParseApi : TomlApi :=
  { stubTomlApi with
    parse := fun _ => .ok #[("wrong", .int 1)] }

example : ¬ Core.AllPass (test_toml_render_parse_roundTrip buggyWrongAstParseApi) := by
  intro h
  have h0 := h (#[], {})
  have hr : Model.render #[] {} = some "" := by
    simp [Model.render, Model.renderLF, Model.wellFormedTableBool,
      Model.wellFormedValueBool.wellFormedTableListBool, Model.noDupKeysBool,
      Model.isEofTrivia, Model.checkEofTriviaAux, Model.renderStmts,
      Model.skelMatchesEntries, Model.skelMatchesEntriesAll, Model.expandNewlines]
  simp [buggyWrongAstParseApi, hr, Model.TomlTableEquiv, Model.TomlTableEquivList,
    Model.lookupKeyList, assert] at h0

example : ¬ Core.AllPass (test_toml_format_validAndRoundTrip buggyWrongAstParseApi) := by
  intro h
  have h0 := h #[]
  have hwf : Model.WellFormedTable #[] := rfl
  have h1 := h0 hwf
  simp [buggyWrongAstParseApi, Model.TomlTableEquiv, Model.TomlTableEquivList,
    Model.lookupKeyList, assert] at h1

example : ¬ Core.AllPass (test_toml_keysAndProvenance_conformsToSpec stubTomlApi) := by
  intro h
  simp [Core.AllPass, test_toml_keysAndProvenance_conformsToSpec, keyProvenanceOkCases,
    checkParseEquiv, stubTomlApi, bind, pure, assert] at h

example : ¬ Core.AllPass (test_toml_inlineTablesAndAot_conformsToSpec stubTomlApi) := by
  intro h
  simp [Core.AllPass, test_toml_inlineTablesAndAot_conformsToSpec, inlineAotOkCases,
    checkParseEquiv, stubTomlApi, bind, pure, assert] at h

example : ¬ Core.AllPass (test_toml_stringsAndControls_conformsToSpec stubTomlApi) := by
  intro h
  simp [Core.AllPass, test_toml_stringsAndControls_conformsToSpec, stringOkCases,
    checkParseEquiv, stubTomlApi, bind, pure, assert] at h

example : ¬ Core.AllPass (test_toml_numbersAndDatetimes_conformsToSpec stubTomlApi) := by
  intro h
  simp [Core.AllPass, test_toml_numbersAndDatetimes_conformsToSpec, numberDatetimeOkCases,
    checkParseEquiv, stubTomlApi, bind, pure, assert] at h

example : ¬ Core.AllPass (test_toml_codecsAndAccessors_conformsToSpec stubTomlApi) := by
  intro h
  have h0 := h "" 0 0.0 false
    { dateTime := Std.Time.PlainDateTime.mk (specDate 2024 1 1) (specTime 0 0 0), offset := specOffset 0 }
    (Std.Time.PlainDateTime.mk (specDate 2024 1 1) (specTime 0 0 0))
    (specDate 2024 1 1) (specTime 0 0 0) #[] #[]
  simp [stubTomlApi, bind, assert] at h0

end LeanSwe.Toml
