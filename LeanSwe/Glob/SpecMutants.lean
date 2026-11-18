import Core.NondetTest
import Core.Assumptions
import LeanSwe.Glob.Types
import LeanSwe.Glob.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Glob`. -/

namespace LeanSwe.Glob

open Core (NondetTest ErrorObligation)
open Core.NondetTest

private def buggyCountApi : GlobApi :=
  { validate := fun _ => .ok ()
    isMatch := fun _ _ => .ok false
    filter := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 99
    escape := id }

example : ¬ Core.AllPass (test_glob_countMatches_eq_filterSize buggyCountApi) := by
  intro h
  have h0 := h "*.lean" #[]
  simp [buggyCountApi, assert] at h0

private def buggyNeverMatchApi : GlobApi :=
  { validate := fun _ => .ok ()
    isMatch := fun _ _ => .ok false
    filter := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    escape := id }

example : ¬ Core.AllPass (test_glob_globStar_matchesAll buggyNeverMatchApi) := by
  intro h
  have h0 := h "src/Main.lean"
  simp [buggyNeverMatchApi, assert] at h0

example : ¬ Core.AllPass (test_glob_escape_matchesSelf buggyNeverMatchApi) := by
  intro h
  have h0 := h "a.lean"
  simp [buggyNeverMatchApi, assert] at h0

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

end LeanSwe.Glob
