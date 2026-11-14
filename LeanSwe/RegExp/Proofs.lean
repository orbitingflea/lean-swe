import LeanSwe.RegExp.Interface
import LeanSwe.RegExp.SpecTests

namespace LeanSwe.RegExp.Proofs

open Core
open Core.NondetTest

private theorem ensureNonEmptyMsg_ne_empty (fallback : String) (hf : fallback ≠ "") (e : RegexError) :
    (Internal.ensureNonEmptyMsg fallback e).message ≠ "" := by
  unfold Internal.ensureNonEmptyMsg
  by_cases h : e.message.isEmpty = true
  · simp [h, hf]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    intro heq
    rw [heq] at h
    exact h rfl

private theorem parseRegex_error_ne_empty (pat : String) (e : RegexError)
    (h : Internal.parseRegex pat = .error e) : e.message ≠ "" := by
  unfold Internal.parseRegex at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · cases h
      exact ensureNonEmptyMsg_ne_empty "invalid regular expression" (by decide) _
    · split at h
      · contradiction
      · cases h; decide
      · cases h; decide

private theorem findFirstSpanFrom_accept (hay : String) :
    Internal.findFirstSpanFrom #[Internal.NfaState.accept] 0 hay hay.startPos none =
      some ⟨hay.startPos, hay.startPos, Internal.pos_le_refl hay.startPos⟩ := by
  have hExp :
      Internal.expandThreads #[Internal.NfaState.accept] hay hay.startPos none
          (if h : hay.startPos ≠ hay.endPos then some (hay.startPos.get h) else none)
          #[] 0 (Array.replicate 1 false) #[] none =
        (Array.replicate 1 false, #[], none, false) := by
    unfold Internal.expandThreads
    simp
  unfold Internal.findFirstSpanFrom Internal.runVmLoop
  dsimp only
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
  rw [hExp]
  dsimp only
  rw [show Array.replicate 1 false = #[false] from rfl]
  simp only [Internal.addThread, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.zero_lt_one, ↓reduceDIte]
  simp only [show (#[false] : Array Bool)[0] = false from rfl, Bool.false_eq_true, ↓reduceIte]
  simp only [Array.getElem?_eq_getElem (by decide : 0 < #[Internal.NfaState.accept].size)]
  split <;> rfl

private theorem findFirstSpan_empty (hay : String) :
    Internal.findFirstSpan "" hay =
      .ok (some ⟨hay.startPos, hay.startPos, Internal.pos_le_refl hay.startPos⟩) := by
  have hParse : Internal.parseRegex "" = .ok .empty := by
    simp [Internal.parseRegex]
  have hComp : Internal.compileRegex .empty = (0, #[Internal.NfaState.accept]) := by
    simp [Internal.compileRegex, Internal.compileAst, Internal.emitState]
  simp [Internal.findFirstSpan, hParse, hComp, findFirstSpanFrom_accept hay]

private theorem findAllSpansLoop_empty_empty :
    Internal.findAllSpansLoop #[Internal.NfaState.accept] 0 "" "".startPos none #[] =
      #[⟨"".startPos, "".startPos, Internal.pos_le_refl "".startPos⟩] := by
  unfold Internal.findAllSpansLoop
  rw [findFirstSpanFrom_accept ""]
  dsimp only
  have hEq : "".startPos = "".endPos := by decide
  simp [hEq]

private theorem findAllSpans_empty_empty :
    Internal.findAllSpans "" "" =
      .ok #[⟨"".startPos, "".startPos, Internal.pos_le_refl "".startPos⟩] := by
  have hParse : Internal.parseRegex "" = .ok .empty := by
    simp [Internal.parseRegex]
  have hComp : Internal.compileRegex .empty = (0, #[Internal.NfaState.accept]) := by
    simp [Internal.compileRegex, Internal.compileAst, Internal.emitState]
  simp [Internal.findAllSpans, hParse, hComp, findAllSpansLoop_empty_empty]

/-- Proof of `test_regex_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_regex_onError_returnsNonEmptyMessage :
    AllPass (test_regex_onError_returnsNonEmptyMessage defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.testPattern, Internal.testPattern, Internal.findFirstSpan]
  cases hp : Internal.parseRegex pat with
  | ok ast =>
    simp [Except.map, assume]
  | error e =>
    simp only [Except.map, assert]
    exact ⟨parseRegex_error_ne_empty pat e hp, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_onError_returnsNonEmptyMessage`. -/
theorem reach_regex_onError_returnsNonEmptyMessage :
    CanReach (test_regex_onError_returnsNonEmptyMessage defaultApi) := by
  refine ⟨"[", "hello", ?_⟩
  simp +decide [defaultApi, RegExp.testPattern, Internal.testPattern, Internal.findFirstSpan,
    Internal.parseRegex, Internal.parseAlternation, Internal.parseAltLoop, Internal.parseSeqLoop,
    Internal.parseAtom, Internal.parseCharClass, Internal.parseCharClassBody,
    Internal.ParseState.peek?, Internal.ParseState.advance, Internal.errEof,
    Internal.ensureNonEmptyMsg, Except.map, assert]

/-- Proof of `test_regex_testPattern_iff_findFirstSome` for `defaultApi`. -/
theorem proof_regex_testPattern_iff_findFirstSome :
    AllPass (test_regex_testPattern_iff_findFirstSome defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.testPattern, RegExp.findFirst, Internal.testPattern,
    Internal.findFirst]
  cases Internal.findFirstSpan pat hay with
  | error e => simp [Except.map, assume]
  | ok sp? =>
    cases sp? with
    | none => simp [Except.map, assert]
    | some sp => simp [Except.map, assert]

/-- Non-vacuity `CanReach` witness for `test_regex_testPattern_iff_findFirstSome`. -/
theorem reach_regex_testPattern_iff_findFirstSome :
    CanReach (test_regex_testPattern_iff_findFirstSome defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h := proof_regex_testPattern_iff_findFirstSome "" ""
  simp only [defaultApi] at h ⊢
  exact h

/-- Proof of `test_regex_countMatches_eq_findAllSize` for `defaultApi`. -/
theorem proof_regex_countMatches_eq_findAllSize :
    AllPass (test_regex_countMatches_eq_findAllSize defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.countMatches, RegExp.findAll, Internal.countMatches]
  cases Internal.findAll pat hay with
  | error e => simp [Except.map, assume]
  | ok xs => simp [Except.map, assert]

/-- Non-vacuity `CanReach` witness for `test_regex_countMatches_eq_findAllSize`. -/
theorem reach_regex_countMatches_eq_findAllSize :
    CanReach (test_regex_countMatches_eq_findAllSize defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h := proof_regex_countMatches_eq_findAllSize "" ""
  simp only [defaultApi] at h ⊢
  exact h

/-- Proof of `test_regex_findAll_spansValid` for `defaultApi`. -/
theorem proof_regex_findAll_spansValid :
    AllPass (test_regex_findAll_spansValid defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.findAll, Internal.findAll]
  cases Internal.findAllSpans pat hay with
  | error e => simp [Except.map, assume]
  | ok spans =>
    simp only [Except.map, assume, assert]
    intro i hi
    have hi' : i < spans.size := by simpa using hi
    simp only [hi, getElem!_pos, Array.getElem_map, Internal.posSpanToMatchSpan]
    exact ⟨⟨String.Pos.le_iff.mp spans[i].hle, spans[i].stopPos.isValid.le_utf8ByteSize⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_findAll_spansValid`. -/
theorem reach_regex_findAll_spansValid :
    CanReach (test_regex_findAll_spansValid defaultApi) := by
  refine ⟨"", "", 0, ?_, ?_⟩
  · simp only [Internal.compileAst, List.size_toArray, List.length_nil,
      show (#[] : Array Internal.NfaState).push Internal.NfaState.accept = #[Internal.NfaState.accept] from rfl]
    rw [findAllSpansLoop_empty_empty]
    simp
  · simp only [Internal.compileAst, List.size_toArray, List.length_nil,
      show (#[] : Array Internal.NfaState).push Internal.NfaState.accept = #[Internal.NfaState.accept] from rfl]
    rw [findAllSpansLoop_empty_empty]
    simp +decide [Internal.posSpanToMatchSpan, assert]

/-- Proof of `test_regex_splitBy_nonEmpty` for `defaultApi`. -/
theorem proof_regex_splitBy_nonEmpty :
    AllPass (test_regex_splitBy_nonEmpty defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.splitBy, Internal.splitBy]
  cases Internal.findAllSpans pat hay with
  | error e => simp [Except.map, assume]
  | ok spans =>
    simp only [Except.map, Internal.splitFromSpans, Array.size_push, assert]
    exact ⟨Nat.succ_pos _, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_splitBy_nonEmpty`. -/
theorem reach_regex_splitBy_nonEmpty :
    CanReach (test_regex_splitBy_nonEmpty defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h := proof_regex_splitBy_nonEmpty "" ""
  simp only [defaultApi] at h ⊢
  exact h

/-- Proof of `test_regex_emptyPattern_matchesAnyHaystack` for `defaultApi`. -/
theorem proof_regex_emptyPattern_matchesAnyHaystack :
    AllPass (test_regex_emptyPattern_matchesAnyHaystack defaultApi) := by
  intro hay
  simp [defaultApi, RegExp.testPattern, Internal.testPattern, findFirstSpan_empty hay,
    Except.map, assert]

/-- Non-vacuity `CanReach` witness for `test_regex_emptyPattern_matchesAnyHaystack`. -/
theorem reach_regex_emptyPattern_matchesAnyHaystack :
    CanReach (test_regex_emptyPattern_matchesAnyHaystack defaultApi) := by
  refine ⟨"abc", ?_⟩
  have h := proof_regex_emptyPattern_matchesAnyHaystack "abc"
  simp only [defaultApi] at h ⊢
  exact h

/-- Proof of `test_regex_replaceAll_emptyOnEmpty_eqReplacement` for `defaultApi`. -/
theorem proof_regex_replaceAll_emptyOnEmpty_eqReplacement :
    AllPass (test_regex_replaceAll_emptyOnEmpty_eqReplacement defaultApi) := by
  intro rep
  simp [defaultApi, RegExp.replaceAll, Internal.replaceAll, findAllSpans_empty_empty,
    Internal.replaceFromSpans, Except.map, assert]
  have hExt1 : String.extract "".startPos "".startPos = "" := by decide
  have hExt2 : String.extract "".startPos "".endPos = "" := by decide
  simp [hExt1, hExt2]

/-- Non-vacuity `CanReach` witness for `test_regex_replaceAll_emptyOnEmpty_eqReplacement`. -/
theorem reach_regex_replaceAll_emptyOnEmpty_eqReplacement :
    CanReach (test_regex_replaceAll_emptyOnEmpty_eqReplacement defaultApi) := by
  refine ⟨"X", ?_⟩
  have h := proof_regex_replaceAll_emptyOnEmpty_eqReplacement "X"
  simp only [defaultApi] at h ⊢
  exact h

end LeanSwe.RegExp.Proofs
