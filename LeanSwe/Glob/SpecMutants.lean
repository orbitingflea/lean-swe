import Core.NondetTest
import Core.Assumptions
import LeanSwe.Glob.Types
import LeanSwe.Glob.Model
import LeanSwe.Glob.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Glob`. -/

namespace LeanSwe.Glob

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.Glob.Model

private def stubGlobApi : GlobApi :=
  { validate := fun _ => .ok ()
    isMatch := fun _ _ => .ok false
    filter := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    escape := id }

private def alwaysTrueApi : GlobApi :=
  { validate := fun _ => .ok ()
    isMatch := fun _ _ => .ok true
    filter := fun _ xs => .ok xs
    countMatches := fun _ xs => .ok xs.size
    escape := id }

example : ¬ Core.AllPass (test_glob_validate_matchesModel alwaysTrueApi) := by
  intro h
  have h0 := h "[a"
  have hm : validateModel "[a" = .error .unclosedClass := rfl
  simp only [alwaysTrueApi, hm, assert] at h0
  exact h0.1

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel alwaysTrueApi) := by
  intro h
  have h0 := h "*" "a/b"
  have hm : isMatchModel "*" "a/b" = .ok false := rfl
  simp only [alwaysTrueApi, hm, assert] at h0
  cases h0.1

example : ¬ Core.AllPass (test_glob_filter_matchesModel alwaysTrueApi) := by
  intro h
  have h0 := h "*" #["a", "a/b"]
  have hm : filterModel "*" #["a", "a/b"] = .ok #["a"] := rfl
  simp only [alwaysTrueApi, hm, assert] at h0
  have hsz := congrArg Array.size h0.1
  simp at hsz

example : ¬ Core.AllPass (test_glob_countMatches_matchesModel alwaysTrueApi) := by
  intro h
  have h0 := h "*" #["a", "a/b"]
  have hm : countMatchesModel "*" #["a", "a/b"] = .ok 1 := rfl
  simp only [alwaysTrueApi, hm, assert] at h0
  exact (by decide : (#["a", "a/b"] : Array String).size ≠ 1) h0.1

example : ¬ Core.AllPass (test_glob_escape_matchesModel alwaysTrueApi) := by
  intro h
  have h0 := h "a*"
  have hm : escapeModel "a*" = "a\\*" := rfl
  simp only [alwaysTrueApi, id, hm, assert] at h0
  exact (by decide : "a*" ≠ "a\\*") h0.1

private def buggyCountApi : GlobApi :=
  { stubGlobApi with countMatches := fun _ _ => .ok 99 }

example : ¬ Core.AllPass (test_glob_countMatches_eq_filterSize buggyCountApi) := by
  intro h
  have h0 := h "*" #[]
  simp [buggyCountApi, stubGlobApi, assert] at h0

example : ¬ Core.AllPass (test_glob_globStar_matchesAll stubGlobApi) := by
  intro h
  have h0 := h "a/b"
  simp [stubGlobApi, assert] at h0

example : ¬ Core.AllPass (test_glob_escape_matchesSelf stubGlobApi) := by
  intro h
  have h0 := h "a"
  simp [stubGlobApi, assert] at h0

private def buggySilentValidateApi : GlobApi :=
  { validate := fun _ => .error { kind := .unclosedClass, message := "err" }
    isMatch := fun _ _ => .ok true
    filter := fun _ xs => .ok xs
    countMatches := fun _ xs => .ok xs.size
    escape := id }

example : ¬ Core.AllPass (test_glob_isMatch_iff_validateOk buggySilentValidateApi) := by
  intro h
  have h0 := h "[" "a"
  simp [buggySilentValidateApi, assert] at h0

private def buggyAlwaysErrorApi : GlobApi :=
  { validate := fun _ => .error { kind := .unclosedClass, message := "err" }
    isMatch := fun _ _ => .error { kind := .unclosedClass, message := "err" }
    filter := fun _ _ => .error { kind := .unclosedClass, message := "err" }
    countMatches := fun _ _ => .error { kind := .unclosedClass, message := "err" }
    escape := escapeModel }

example : ¬ Core.AllPass (test_glob_validate_matchesModel buggyAlwaysErrorApi) := by
  intro h
  have h0 := h "*"
  have hm : validateModel "*" = .ok () := rfl
  simp only [buggyAlwaysErrorApi, hm, assert] at h0
  exact h0.1

private def buggyWrongErrorKindApi : GlobApi :=
  { stubGlobApi with
    validate := fun _ => .error { kind := .unclosedClass, message := "err" } }

example : ¬ Core.AllPass (test_glob_validate_matchesModel buggyWrongErrorKindApi) := by
  intro h
  have h0 := h "[z-a]"
  have hm : validateModel "[z-a]" = .error .invalidRange := rfl
  simp only [buggyWrongErrorKindApi, hm, assert] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_glob_validate_matchesModel buggyWrongErrorKindApi) := by
  intro h
  have h0 := h "[]"
  have hm : validateModel "[]" = .error .emptyClass := rfl
  simp only [buggyWrongErrorKindApi, hm, assert] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_glob_validate_matchesModel buggyWrongErrorKindApi) := by
  intro h
  have h0 := h "a\\"
  have hm : validateModel "a\\" = .error .trailingEscape := rfl
  simp only [buggyWrongErrorKindApi, hm, assert] at h0
  cases h0.1.1

private def buggyStarCrossesSlashApi : GlobApi :=
  { stubGlobApi with isMatch := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel buggyStarCrossesSlashApi) := by
  intro h
  have h0 := h "*" "a/b"
  have hm : isMatchModel "*" "a/b" = .ok false := rfl
  simp only [buggyStarCrossesSlashApi, hm, assert] at h0
  cases h0.1

private def buggyQuestionCrossesSlashApi : GlobApi :=
  { stubGlobApi with isMatch := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel buggyQuestionCrossesSlashApi) := by
  intro h
  have h0 := h "?" "/"
  have hm : isMatchModel "?" "/" = .ok false := rfl
  simp only [buggyQuestionCrossesSlashApi, hm, assert] at h0
  cases h0.1

private def buggyGlobStarRequiresSegmentApi : GlobApi :=
  { stubGlobApi with isMatch := fun _ _ => .ok false }

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel buggyGlobStarRequiresSegmentApi) := by
  intro h
  have h0 := h "**/b" "b"
  have hm : isMatchModel "**/b" "b" = .ok true := rfl
  simp only [buggyGlobStarRequiresSegmentApi, hm, assert] at h0
  exact Bool.false_ne_true h0.1

private def buggyGlobStarNoRecursionApi : GlobApi :=
  { stubGlobApi with isMatch := fun _ _ => .ok false }

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel buggyGlobStarNoRecursionApi) := by
  intro h
  have h0 := h "**/b" "x/y/b"
  have hm : isMatchModel "**/b" "x/y/b" = .ok true := rfl
  simp only [buggyGlobStarNoRecursionApi, hm, assert] at h0
  exact Bool.false_ne_true h0.1

private def buggyCharClassRangeApi : GlobApi :=
  { stubGlobApi with isMatch := fun _ _ => .ok false }

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel buggyCharClassRangeApi) := by
  intro h
  have h0 := h "[a-c]" "b"
  have hm : isMatchModel "[a-c]" "b" = .ok true := rfl
  simp only [buggyCharClassRangeApi, hm, assert] at h0
  exact Bool.false_ne_true h0.1

private def buggyNegatedClassApi : GlobApi :=
  { stubGlobApi with isMatch := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel buggyNegatedClassApi) := by
  intro h
  have h0 := h "[!a]" "a"
  have hm : isMatchModel "[!a]" "a" = .ok false := rfl
  simp only [buggyNegatedClassApi, hm, assert] at h0
  cases h0.1

private def buggyEscapeWildcardApi : GlobApi :=
  { stubGlobApi with isMatch := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_glob_isMatch_matchesModel buggyEscapeWildcardApi) := by
  intro h
  have h0 := h "\\*" "x"
  have hm : isMatchModel "\\*" "x" = .ok false := rfl
  simp only [buggyEscapeWildcardApi, hm, assert] at h0
  cases h0.1

private def buggyEscapeSlashApi : GlobApi :=
  { stubGlobApi with escape := fun _ => "a\\/b" }

example : ¬ Core.AllPass (test_glob_escape_matchesModel buggyEscapeSlashApi) := by
  intro h
  have h0 := h "a/b"
  have hm : escapeModel "a/b" = "a/b" := rfl
  simp only [buggyEscapeSlashApi, hm, assert] at h0
  exact (by decide : "a\\/b" ≠ "a/b") h0.1

private def buggyFilterOrderApi : GlobApi :=
  { stubGlobApi with filter := fun _ _ => .ok #["b", "a"] }

example : ¬ Core.AllPass (test_glob_filter_matchesModel buggyFilterOrderApi) := by
  intro h
  have h0 := h "*" #["a", "b"]
  have hm : filterModel "*" #["a", "b"] = .ok #["a", "b"] := rfl
  simp only [buggyFilterOrderApi, hm, assert] at h0
  exact (by decide : (#["b", "a"] : Array String) ≠ #["a", "b"]) h0.1

end LeanSwe.Glob
