import Core.NondetTest
import Core.Assumptions
import LeanSwe.RegExp.Types
import LeanSwe.RegExp.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.RegExp`. -/

namespace LeanSwe.RegExp

open Core (NondetTest ErrorObligation)
open Core.NondetTest

private def buggyCountApi : RegexApi :=
  { testPattern := fun _ _ => .ok false
    findFirst := fun _ _ => .ok none
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 99
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

example : ¬ Core.AllPass (test_regex_countMatches_eq_findAllSize buggyCountApi) := by
  intro h
  have h0 := h "a" "a"
  simp [buggyCountApi, assert] at h0

example : ¬ Core.AllPass (test_regex_replaceAll_emptyOnEmpty_eqReplacement buggyCountApi) := by
  intro h
  have h0 := h "x"
  simp [buggyCountApi, assert] at h0

private def buggyNeverMatchApi : RegexApi :=
  { testPattern := fun _ _ => .ok false
    findFirst := fun _ _ => .ok none
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

example : ¬ Core.AllPass (test_regex_emptyPattern_matchesAnyHaystack buggyNeverMatchApi) := by
  intro h
  have h0 := h "abc"
  simp [buggyNeverMatchApi, assert] at h0

private def buggyTestApi : RegexApi :=
  { testPattern := fun _ _ => .ok true
    findFirst := fun _ _ => .ok none
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

example : ¬ Core.AllPass (test_regex_testPattern_iff_findFirstSome buggyTestApi) := by
  intro h
  have h0 := h "a" "a"
  simp [buggyTestApi, assert] at h0

end LeanSwe.RegExp
