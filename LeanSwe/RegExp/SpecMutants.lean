import Core.NondetTest
import Core.Assumptions
import LeanSwe.RegExp.Types
import LeanSwe.RegExp.Model
import LeanSwe.RegExp.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.RegExp`. -/

namespace LeanSwe.RegExp

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.RegExp.Model

private def stubRegexApi : RegexApi :=
  { testPattern := fun _ _ => .ok false
    findFirst := fun _ _ => .ok none
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

private def alwaysTrueApi : RegexApi :=
  { testPattern := fun _ _ => .ok true
    findFirst := fun _ _ => .ok (some { matched := "", startByte := 0, stopByte := 0 })
    findAll := fun _ _ => .ok #[]
    countMatches := fun _ _ => .ok 0
    replaceAll := fun _ h _ => .ok h
    splitBy := fun _ h => .ok #[h] }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel alwaysTrueApi) := by
  intro h
  have h0 := h "a" "b"
  have hm : testPatternModel "a" "b" = .ok false := rfl
  simp only [alwaysTrueApi, hm, assert] at h0
  cases h0.1

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel alwaysTrueApi) := by
  intro h
  have h0 := h "[" "a"
  have hm : testPatternModel "[" "a" = .error .unexpectedEof := rfl
  simp only [alwaysTrueApi, hm, assert] at h0
  exact h0.1

private def buggyCountApi : RegexApi :=
  { stubRegexApi with countMatches := fun _ _ => .ok 99 }

example : ¬ Core.AllPass (test_regex_countMatches_eq_findAllSize buggyCountApi) := by
  intro h
  have h0 := h "a" "a"
  simp [buggyCountApi, stubRegexApi, assert] at h0

example : ¬ Core.AllPass (test_regex_replaceAll_emptyOnEmpty_eqReplacement buggyCountApi) := by
  intro h
  have h0 := h "x"
  simp [buggyCountApi, stubRegexApi, assert] at h0

example : ¬ Core.AllPass (test_regex_emptyPattern_matchesAnyHaystack stubRegexApi) := by
  intro h
  have h0 := h "a"
  simp [stubRegexApi, assert] at h0

private def buggyTestApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_iff_findFirstSome buggyTestApi) := by
  intro h
  have h0 := h "a" "a"
  simp [buggyTestApi, stubRegexApi, assert] at h0

private def buggyStarRequiresOneApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok false }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyStarRequiresOneApi) := by
  intro h
  have h0 := h "a*" ""
  have hm : testPatternModel "a*" "" = .ok true := rfl
  simp only [buggyStarRequiresOneApi, hm, assert] at h0
  exact Bool.false_ne_true h0.1

private def buggyPlusAcceptsZeroApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyPlusAcceptsZeroApi) := by
  intro h
  have h0 := h "a+" ""
  have hm : testPatternModel "a+" "" = .ok false := rfl
  simp only [buggyPlusAcceptsZeroApi, hm, assert] at h0
  cases h0.1

private def buggyQuestionMatchesTwoApi : RegexApi :=
  { stubRegexApi with
    findFirst := fun _ _ => .ok (some { matched := "aa", startByte := 0, stopByte := 2 }) }

example : ¬ Core.AllPass (test_regex_findFirst_matchesModel buggyQuestionMatchesTwoApi) := by
  intro h
  have h0 := h "a?" "aa"
  have hm : findFirstModel "a?" "aa" = .ok (some { matched := "a", startByte := 0, stopByte := 1 }) := rfl
  simp only [buggyQuestionMatchesTwoApi, hm, assert] at h0
  have hstop := congrArg (Option.map MatchSpan.stopByte) h0.1
  cases hstop

private def buggyLazyIsGreedyApi : RegexApi :=
  { stubRegexApi with
    findFirst := fun _ _ => .ok (some { matched := "aa", startByte := 0, stopByte := 2 }) }

example : ¬ Core.AllPass (test_regex_findFirst_matchesModel buggyLazyIsGreedyApi) := by
  intro h
  have h0 := h "a+?" "aa"
  have hm : findFirstModel "a+?" "aa" = .ok (some { matched := "a", startByte := 0, stopByte := 1 }) := rfl
  simp only [buggyLazyIsGreedyApi, hm, assert] at h0
  have hstop := congrArg (Option.map MatchSpan.stopByte) h0.1
  cases hstop

private def buggyAltDropsSecondApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok false }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyAltDropsSecondApi) := by
  intro h
  have h0 := h "a|b" "b"
  have hm : testPatternModel "a|b" "b" = .ok true := rfl
  simp only [buggyAltDropsSecondApi, hm, assert] at h0
  exact Bool.false_ne_true h0.1

private def buggyAltLongestApi : RegexApi :=
  { stubRegexApi with
    findFirst := fun _ _ => .ok (some { matched := "ab", startByte := 0, stopByte := 2 }) }

example : ¬ Core.AllPass (test_regex_findFirst_matchesModel buggyAltLongestApi) := by
  intro h
  have h0 := h "a|ab" "ab"
  have hm : findFirstModel "a|ab" "ab" = .ok (some { matched := "a", startByte := 0, stopByte := 1 }) := rfl
  simp only [buggyAltLongestApi, hm, assert] at h0
  have hstop := congrArg (Option.map MatchSpan.stopByte) h0.1
  cases hstop

private def buggyGroupScopeApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok false }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyGroupScopeApi) := by
  intro h
  have h0 := h "(?:a)" "a"
  have hm : testPatternModel "(?:a)" "a" = .ok true := rfl
  simp only [buggyGroupScopeApi, hm, assert] at h0
  exact Bool.false_ne_true h0.1

private def buggyCharClassRangeApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok false }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyCharClassRangeApi) := by
  intro h
  have h0 := h "[a-c]" "b"
  have hm : testPatternModel "[a-c]" "b" = .ok true := rfl
  simp only [buggyCharClassRangeApi, hm, assert] at h0
  exact Bool.false_ne_true h0.1

private def buggyCharClassNegationApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyCharClassNegationApi) := by
  intro h
  have h0 := h "[^0]" "0"
  have hm : testPatternModel "[^0]" "0" = .ok false := rfl
  simp only [buggyCharClassNegationApi, hm, assert] at h0
  cases h0.1

private def buggyAnchorStartApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyAnchorStartApi) := by
  intro h
  have h0 := h "^a" "ba"
  have hm : testPatternModel "^a" "ba" = .ok false := rfl
  simp only [buggyAnchorStartApi, hm, assert] at h0
  cases h0.1

private def buggyAnchorEndApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyAnchorEndApi) := by
  intro h
  have h0 := h "a$" "ab"
  have hm : testPatternModel "a$" "ab" = .ok false := rfl
  simp only [buggyAnchorEndApi, hm, assert] at h0
  cases h0.1

private def buggyWordBoundaryApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyWordBoundaryApi) := by
  intro h
  have h0 := h "\\ba" "ba"
  have hm : testPatternModel "\\ba" "ba" = .ok false := rfl
  simp only [buggyWordBoundaryApi, hm, assert] at h0
  cases h0.1

private def buggyEscapeDotApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyEscapeDotApi) := by
  intro h
  have h0 := h "\\." "x"
  have hm : testPatternModel "\\." "x" = .ok false := rfl
  simp only [buggyEscapeDotApi, hm, assert] at h0
  cases h0.1

private def buggyBraceQuantApi : RegexApi :=
  { stubRegexApi with testPattern := fun _ _ => .ok true }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyBraceQuantApi) := by
  intro h
  have h0 := h "a{2}" "a"
  have hm : testPatternModel "a{2}" "a" = .ok false := rfl
  simp only [buggyBraceQuantApi, hm, assert] at h0
  cases h0.1

private def buggyUtf8OffsetApi : RegexApi :=
  { stubRegexApi with
    findFirst := fun _ _ => .ok (some { matched := "b", startByte := 1, stopByte := 2 }) }

example : ¬ Core.AllPass (test_regex_findFirst_matchesModel buggyUtf8OffsetApi) := by
  intro h
  have h0 := h "b" "αb"
  have hm : findFirstModel "b" "αb" = .ok (some { matched := "b", startByte := 2, stopByte := 3 }) := rfl
  simp only [buggyUtf8OffsetApi, hm, assert] at h0
  cases h0.1

private def buggyReplaceFirstOnlyApi : RegexApi :=
  { stubRegexApi with replaceAll := fun _ _ _ => .ok "xa" }

example : ¬ Core.AllPass (test_regex_replaceAll_matchesModel buggyReplaceFirstOnlyApi) := by
  intro h
  have h0 := h "a" "aa" "x"
  have hm : replaceAllModel "a" "aa" "x" = .ok "xx" := rfl
  simp only [buggyReplaceFirstOnlyApi, hm, assert] at h0
  exact (by decide : "xa" ≠ "xx") h0.1

private def buggySplitDropsEmptyApi : RegexApi :=
  { stubRegexApi with splitBy := fun _ _ => .ok #["", ""] }

example : ¬ Core.AllPass (test_regex_splitBy_matchesModel buggySplitDropsEmptyApi) := by
  intro h
  have h0 := h "," ",,"
  have hm : splitByModel "," ",," = .ok #["", "", ""] := rfl
  simp only [buggySplitDropsEmptyApi, hm, assert] at h0
  exact (by decide : (#["", ""] : Array String) ≠ #["", "", ""]) h0.1

private def buggyFindAllDropsSecondApi : RegexApi :=
  { stubRegexApi with
    findAll := fun _ _ => .ok #[{ matched := "a", startByte := 0, stopByte := 1 }] }

example : ¬ Core.AllPass (test_regex_findAll_matchesModel buggyFindAllDropsSecondApi) := by
  intro h
  have h0 := h "a" "aa"
  have hm : findAllModel "a" "aa" =
      .ok #[{ matched := "a", startByte := 0, stopByte := 1 },
            { matched := "a", startByte := 1, stopByte := 2 }] := rfl
  simp only [buggyFindAllDropsSecondApi, hm, assert] at h0
  have hsz := congrArg Array.size h0.1
  simp at hsz

private def buggyCountMatchesModelApi : RegexApi :=
  { stubRegexApi with countMatches := fun _ _ => .ok 1 }

example : ¬ Core.AllPass (test_regex_countMatches_matchesModel buggyCountMatchesModelApi) := by
  intro h
  have h0 := h "a" "aa"
  have hm : countMatchesModel "a" "aa" = .ok 2 := rfl
  simp only [buggyCountMatchesModelApi, hm, assert] at h0
  exact (by decide : (1 : Nat) ≠ 2) h0.1

private def buggyWrongErrorKindApi : RegexApi :=
  { stubRegexApi with
    testPattern := fun _ _ => .error { kind := .invalidSyntax, message := "err" } }

example : ¬ Core.AllPass (test_regex_testPattern_matchesModel buggyWrongErrorKindApi) := by
  intro h
  have h0 := h "[a" "a"
  have hm : testPatternModel "[a" "a" = .error .unexpectedEof := rfl
  simp only [buggyWrongErrorKindApi, hm, assert] at h0
  cases h0.1.1

end LeanSwe.RegExp
