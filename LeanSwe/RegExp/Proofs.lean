import Core.Obeys
import LeanSwe.RegExp.Interface
import LeanSwe.RegExp.Model
import LeanSwe.RegExp.SpecTests
import LeanSwe.RegExp.Proofs.ParserClass
import LeanSwe.RegExp.Proofs.ParserMain
import LeanSwe.RegExp.Proofs.EvalCombinators
import LeanSwe.RegExp.Proofs.EvalMatch

namespace LeanSwe.RegExp.Proofs

open Core
open Core.NondetTest

private theorem testPattern_matchesModel_props (pat hay : String) :
    match testPattern pat hay, Model.testPatternModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [testPattern, Internal.testPattern, Model.testPatternModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      have hf := (findFirstIdx_eq hay.toList.toArray ast 0).1
      rw [List.size_toArray] at hf
      simp [hf]

private theorem findFirst_matchesModel_props (pat hay : String) :
    match findFirst pat hay, Model.findFirstModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [findFirst, Internal.findFirst, Model.findFirstModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hf := findFirstIdx_eq chars ast 0
      have hf1 : Internal.findFirstIdx (Internal.evalTable chars ast) chars.size 0 =
          Model.findFirstIdx (toModel ast) hay.toList 0 := hf.1
      cases hres : Model.findFirstIdx (toModel ast) hay.toList 0 with
      | none =>
        have hres' : Internal.findFirstIdx (Internal.evalTable hay.toList.toArray ast)
            hay.toList.toArray.size 0 = none :=
          hf1.trans hres
        rw [hres']
        rfl
      | some v =>
        obtain ⟨i, j⟩ := v
        have hres' : Internal.findFirstIdx (Internal.evalTable chars ast) chars.size 0 = some (i, j) :=
          hf1.trans hres
        have hbd := hf.2 i j hres'
        have hres'' : Internal.findFirstIdx (Internal.evalTable hay.toList.toArray ast)
            hay.toList.toArray.size 0 = some (i, j) := hres'
        rw [hres'', Option.map_some]
        exact congrArg some (mkMatchSpanFast_eq chars hbd.2.1 hbd.2.2)

private theorem findAll_matchesModel_props (pat hay : String) :
    match findAll pat hay, Model.findAllModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [findAll, Internal.findAll, Model.findAllModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hfa := findAllIdx_eq chars ast
      have hfa' : Internal.findAllIdx chars ast = Model.findAllIdx (toModel ast) hay.toList := hfa.1
      simp only [chars, hfa']
      congr 1
      apply List.map_congr_left
      intro sp hsp
      have hbd := hfa.2 sp (by rw [hfa']; exact hsp)
      exact mkMatchSpanFast_eq chars hbd.1 hbd.2

private theorem countMatches_matchesModel_props (pat hay : String) :
    match countMatches pat hay, Model.countMatchesModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [countMatches, Internal.countMatches, Model.countMatchesModel, Except.map]
  have hfa := findAll_matchesModel_props pat hay
  simp only [findAll] at hfa
  cases h1 : Internal.findAll pat hay <;> cases h2 : Model.findAllModel pat hay <;> rw [h1, h2] at hfa
  · exact hfa
  · exact False.elim hfa
  · exact False.elim hfa
  · simp [hfa]

private theorem replaceAll_matchesModel_props (pat hay rep : String) :
    match replaceAll pat hay rep, Model.replaceAllModel pat hay rep with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [replaceAll, Internal.replaceAll, Model.replaceAllModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hfa := (findAllIdx_eq chars ast).1
      have hrep := replaceSpansFast_eq chars rep 0 (Internal.findAllIdx chars ast)
      simpa [chars, hfa] using hrep

private theorem splitBy_matchesModel_props (pat hay : String) :
    match splitBy pat hay, Model.splitByModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [splitBy, Internal.splitBy, Model.splitByModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hfa := (findAllIdx_eq chars ast).1
      have hsp := splitSpansFast_eq chars 0 (Internal.findAllIdx chars ast)
      simpa [chars, hfa] using hsp

private theorem utf8ByteSize_ofList (l : List Char) :
    (String.ofList l).utf8ByteSize = (l.map Char.utf8Size).sum := by
  induction l with
  | nil => simp
  | cons c cs ih => simp [String.ofList_cons, Char.utf8Size, ih]

private theorem utf8ByteOffset_mono_le (cs : List Char) {i j : Nat} (hij : i ≤ j) :
    Model.utf8ByteOffset cs i ≤ Model.utf8ByteOffset cs j ∧
      Model.utf8ByteOffset cs j ≤ (String.ofList cs).utf8ByteSize := by
  rw [utf8ByteSize_ofList]
  have h1 : Model.utf8ByteOffset cs i ≤ Model.utf8ByteOffset cs j := by
    simp only [Model.utf8ByteOffset]
    have hj' : cs.take j = cs.take (i + (j - i)) := by rw [Nat.add_sub_of_le hij]
    have htake : cs.take j = cs.take i ++ (cs.drop i).take (j - i) := by
      rw [hj', List.take_add]
    rw [htake, List.map_append, List.sum_append]
    exact Nat.le_add_right _ _
  have h2 : Model.utf8ByteOffset cs j ≤ (cs.map Char.utf8Size).sum := by
    simp only [Model.utf8ByteOffset]
    have hsplit : cs = cs.take j ++ cs.drop j := (List.take_append_drop j cs).symm
    have hsum : (cs.map Char.utf8Size).sum =
        ((cs.take j).map Char.utf8Size).sum + ((cs.drop j).map Char.utf8Size).sum := by
      calc (cs.map Char.utf8Size).sum
          = ((cs.take j ++ cs.drop j).map Char.utf8Size).sum := by rw [← hsplit]
        _ = ((cs.take j).map Char.utf8Size).sum + ((cs.drop j).map Char.utf8Size).sum := by
          rw [List.map_append, List.sum_append]
    rw [hsum]
    exact Nat.le_add_right _ _
  exact ⟨h1, h2⟩

/-- Proof of `test_regex_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_regex_onError_returnsNonEmptyMessage :
    AllPass (test_regex_onError_returnsNonEmptyMessage defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := testPattern_matchesModel_props pat hay
  cases h1 : testPattern pat hay with
  | error e =>
    cases h2 : Model.testPatternModel pat hay with
    | error k =>
      rw [h1, h2] at hm
      simp [assert, hm.2]
    | ok =>
      rw [h1, h2] at hm
      exact False.elim hm
  | ok b =>
    simp [assume]

private theorem empty_toList_eq : "".toList = [] := by decide

private theorem parseRegex_empty_eq : Internal.parseRegex "" = .ok .empty := by
  simp [Internal.parseRegex, Array.isEmpty]

private theorem testPattern_empty_eq (hay : String) (h : hay.toList = []) :
    testPattern "" hay = .ok true := by
  simp [testPattern, Internal.testPattern, parseRegex_empty_eq, Except.map,
    Internal.findFirstIdx, Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab, h]

/-- Non-vacuity `CanReach` witness for `test_regex_onError_returnsNonEmptyMessage`. -/
theorem reach_regex_onError_returnsNonEmptyMessage :
    CanReach (test_regex_onError_returnsNonEmptyMessage defaultApi) := by
  refine ⟨"[", "hello", ?_⟩
  have hl : "[".toList = ['['] := by decide
  simp [defaultApi, testPattern, Internal.testPattern, Internal.parseRegex, hl, Array.isEmpty,
    Internal.parseAlt, Internal.parseSeq, Internal.parseAtom, Internal.parseCharClass,
    Internal.parseClassBody, Internal.isLeadingQuantifier, Internal.mkError,
    bind, Except.bind, Except.map, assert]

/-- Proof of `test_regex_testPattern_iff_findFirstSome` for `defaultApi`. -/
theorem proof_regex_testPattern_iff_findFirstSome :
    AllPass (test_regex_testPattern_iff_findFirstSome defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have htp := testPattern_matchesModel_props pat hay
  have hff := findFirst_matchesModel_props pat hay
  cases h1 : testPattern pat hay with
  | error => simp [assume]
  | ok b =>
    rw [h1] at htp
    cases h2 : Model.testPatternModel pat hay with
    | error => rw [h2] at htp; exact False.elim htp
    | ok bm =>
      rw [h2] at htp
      subst htp
      cases hp : Model.parseRegex pat with
      | error => simp [Model.testPatternModel, hp, Except.map] at h2
      | ok r =>
        simp only [Model.testPatternModel, hp, Except.map, Except.ok.injEq] at h2
        have hffm : Model.findFirstModel pat hay =
            .ok ((Model.findFirstIdx r hay.toList 0).map fun (i, j) =>
              Model.mkMatchSpan hay.toList i j) := by
          simp [Model.findFirstModel, hp, Except.map]
        rw [hffm] at hff
        cases h3 : findFirst pat hay with
        | error => rw [h3] at hff; exact False.elim hff
        | ok sp? =>
          rw [h3] at hff
          simp only at hff
          subst hff
          simp [assert, ← h2]

/-- Non-vacuity `CanReach` witness for `test_regex_testPattern_iff_findFirstSome`. -/
theorem reach_regex_testPattern_iff_findFirstSome :
    CanReach (test_regex_testPattern_iff_findFirstSome defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h1 := testPattern_empty_eq "" empty_toList_eq
  have h2 : findFirst "" "" = .ok (some { matched := "", startByte := 0, stopByte := 0 }) := by
    simp [findFirst, Internal.findFirst, parseRegex_empty_eq, Except.map,
      Internal.findFirstIdx, Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.mkMatchSpanFast, Internal.buildByteOffsets, Internal.buildByteOffsets.loop]
  simp [defaultApi, h1, h2, assert]

/-- Proof of `test_regex_countMatches_eq_findAllSize` for `defaultApi`. -/
theorem proof_regex_countMatches_eq_findAllSize :
    AllPass (test_regex_countMatches_eq_findAllSize defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.countMatches, RegExp.findAll, Internal.countMatches]
  cases Internal.findAll pat hay <;> simp [Except.map, assume, assert]

/-- Non-vacuity `CanReach` witness for `test_regex_countMatches_eq_findAllSize`. -/
theorem reach_regex_countMatches_eq_findAllSize :
    CanReach (test_regex_countMatches_eq_findAllSize defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h2i : Internal.findAll "" "" = .ok #[{ matched := "", startByte := 0, stopByte := 0 }] := by
    simp [Internal.findAll, parseRegex_empty_eq, Except.map,
      Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.mkMatchSpanFast, Internal.buildByteOffsets, Internal.buildByteOffsets.loop]
  have h2 : findAll "" "" = .ok #[{ matched := "", startByte := 0, stopByte := 0 }] := h2i
  have h1 : countMatches "" "" = .ok 1 := by
    simp [countMatches, Internal.countMatches, h2i, Except.map]
  simp [defaultApi, h1, h2, assert]

/-- Proof of `test_regex_findAll_spansValid` for `defaultApi`. -/
theorem proof_regex_findAll_spansValid :
    AllPass (test_regex_findAll_spansValid defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.findAll, Internal.findAll]
  cases hp : Internal.parseRegex pat with
  | error e => simp [Except.map, assume]
  | ok ast =>
    simp only [Except.map, assume, assert]
    intro i hi
    let chars := hay.toList.toArray
    have hfa := findAllIdx_eq chars ast
    let idxList := Internal.findAllIdx chars ast
    have hi' : i < idxList.length := by simpa [idxList] using hi
    have hmem : idxList[i] ∈ idxList := List.getElem_mem hi'
    have hbd := hfa.2 idxList[i] hmem
    have hb := buildByteOffsets_spec chars
    have hmono := utf8ByteOffset_mono_le hay.toList hbd.1
    rw [String.ofList_toList] at hmono
    have hsp_eq :
        ((idxList.map fun (a, b) =>
            Internal.mkMatchSpanFast chars (Internal.buildByteOffsets chars) a b).toArray)[i]! =
          Internal.mkMatchSpanFast chars (Internal.buildByteOffsets chars) idxList[i].1 idxList[i].2 := by
      simp [hi']
    rw [hsp_eq]
    unfold Internal.mkMatchSpanFast
    rw [hb.2 idxList[i].1 (Nat.le_trans hbd.1 hbd.2), hb.2 idxList[i].2 hbd.2]
    exact ⟨⟨by simpa [chars] using hmono.1, by simpa [chars] using hmono.2⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_findAll_spansValid`. -/
theorem reach_regex_findAll_spansValid :
    CanReach (test_regex_findAll_spansValid defaultApi) := by
  have hidx : Internal.findAllIdx #[] Internal.RegexAst.empty = [(0, 0)] := by
    simp [Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab]
  refine ⟨"", "", 0, ?_, ?_⟩
  · simp [hidx]
  · simp [hidx, Internal.mkMatchSpanFast, Internal.buildByteOffsets,
      Internal.buildByteOffsets.loop, assert]

/-- Proof of `test_regex_splitBy_nonEmpty` for `defaultApi`. -/
theorem proof_regex_splitBy_nonEmpty :
    AllPass (test_regex_splitBy_nonEmpty defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.splitBy, Internal.splitBy]
  cases hp : Internal.parseRegex pat with
  | error e => simp [Except.map, assume]
  | ok ast =>
    simp only [Except.map, assert]
    refine ⟨?_, trivial⟩
    cases Internal.findAllIdx hay.toList.toArray ast <;> simp [Internal.splitSpansFast]

/-- Non-vacuity `CanReach` witness for `test_regex_splitBy_nonEmpty`. -/
theorem reach_regex_splitBy_nonEmpty :
    CanReach (test_regex_splitBy_nonEmpty defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h1 : splitBy "" "" = .ok #["", ""] := by
    simp [splitBy, Internal.splitBy, parseRegex_empty_eq, Except.map,
      Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.splitSpansFast]
  simp [defaultApi, h1, assert]

/-- Proof of `test_regex_emptyPattern_matchesAnyHaystack` for `defaultApi`. -/
theorem proof_regex_emptyPattern_matchesAnyHaystack :
    AllPass (test_regex_emptyPattern_matchesAnyHaystack defaultApi) := by
  intro hay
  simp only [defaultApi, RegExp.testPattern, Internal.testPattern, parseRegex_empty_eq]
  simp only [Except.map, assert]
  let chars := hay.toList.toArray
  have ht := (evalTable_matches chars .empty).2 0 (Nat.zero_le _)
  unfold Internal.findFirstIdx
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  cases hsz : chars.size with
  | zero =>
    simp only [Internal.findFirstIdxAux]
    rw [ht.1]
    simp [Model.evalAt, toModel]
  | succ m =>
    simp only [Internal.findFirstIdxAux]
    rw [ht.1]
    simp [Model.evalAt, toModel]

/-- Non-vacuity `CanReach` witness for `test_regex_emptyPattern_matchesAnyHaystack`. -/
theorem reach_regex_emptyPattern_matchesAnyHaystack :
    CanReach (test_regex_emptyPattern_matchesAnyHaystack defaultApi) := by
  refine ⟨"abc", ?_⟩
  have habc : "abc".toList = ['a', 'b', 'c'] := by decide
  have h1 : testPattern "" "abc" = .ok true := by
    simp [testPattern, Internal.testPattern, parseRegex_empty_eq, Except.map,
      Internal.findFirstIdx, Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab, habc]
  simp [defaultApi, h1, assert]

/-- Proof of `test_regex_replaceAll_emptyOnEmpty_eqReplacement` for `defaultApi`. -/
theorem proof_regex_replaceAll_emptyOnEmpty_eqReplacement :
    AllPass (test_regex_replaceAll_emptyOnEmpty_eqReplacement defaultApi) := by
  intro rep
  have hr := replaceAll_matchesModel_props "" "" rep
  have hm : Model.replaceAllModel "" "" rep = .ok rep := by
    simp [Model.replaceAllModel, Model.parseRegex, Model.parseRegexChars,
      Except.map, Model.findAllIdx, Model.findAllIdxAux, Model.findFirstIdx,
      Model.findFirstIdxAux, Model.evalAt, Model.replaceSpans]
  rw [hm] at hr
  cases ha : replaceAll "" "" rep with
  | error => rw [ha] at hr; exact False.elim hr
  | ok out =>
    rw [ha] at hr
    simpa [defaultApi, ha, assert] using hr

/-- Non-vacuity `CanReach` witness for `test_regex_replaceAll_emptyOnEmpty_eqReplacement`. -/
theorem reach_regex_replaceAll_emptyOnEmpty_eqReplacement :
    CanReach (test_regex_replaceAll_emptyOnEmpty_eqReplacement defaultApi) := by
  refine ⟨"X", ?_⟩
  have h1 : replaceAll "" "" "X" = .ok "X" := by
    simp [replaceAll, Internal.replaceAll, parseRegex_empty_eq, Except.map,
      Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.replaceSpansFast]
  simp [defaultApi, h1, assert]

/-- Proof of `test_regex_testPattern_matchesModel` for `defaultApi`. -/
theorem proof_regex_testPattern_matchesModel :
    AllPass (test_regex_testPattern_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := testPattern_matchesModel_props pat hay
  cases h1 : testPattern pat hay <;> cases h2 : Model.testPatternModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_findFirst_matchesModel` for `defaultApi`. -/
theorem proof_regex_findFirst_matchesModel :
    AllPass (test_regex_findFirst_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := findFirst_matchesModel_props pat hay
  cases h1 : findFirst pat hay <;> cases h2 : Model.findFirstModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_findAll_matchesModel` for `defaultApi`. -/
theorem proof_regex_findAll_matchesModel :
    AllPass (test_regex_findAll_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := findAll_matchesModel_props pat hay
  cases h1 : findAll pat hay <;> cases h2 : Model.findAllModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_countMatches_matchesModel` for `defaultApi`. -/
theorem proof_regex_countMatches_matchesModel :
    AllPass (test_regex_countMatches_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := countMatches_matchesModel_props pat hay
  cases h1 : countMatches pat hay <;> cases h2 : Model.countMatchesModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_replaceAll_matchesModel` for `defaultApi`. -/
theorem proof_regex_replaceAll_matchesModel :
    AllPass (test_regex_replaceAll_matchesModel defaultApi) := by
  intro pat hay rep
  simp only [defaultApi]
  have hm := replaceAll_matchesModel_props pat hay rep
  cases h1 : replaceAll pat hay rep <;> cases h2 : Model.replaceAllModel pat hay rep <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_splitBy_matchesModel` for `defaultApi`. -/
theorem proof_regex_splitBy_matchesModel :
    AllPass (test_regex_splitBy_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := splitBy_matchesModel_props pat hay
  cases h1 : splitBy pat hay <;> cases h2 : Model.splitByModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]


/-- Full public `Interface` obedience of `LeanSwe.RegExp` against `LeanSwe.RegExp.Model`. -/
theorem obeys_model :
    Core.ObeysPure2 LeanSwe.RegExp.testPattern Model.allowedTestPattern ∧
    Core.ObeysPure2 LeanSwe.RegExp.findFirst Model.allowedFindFirst ∧
    Core.ObeysPure2 LeanSwe.RegExp.findAll Model.allowedFindAll ∧
    Core.ObeysPure2 LeanSwe.RegExp.countMatches Model.allowedCountMatches ∧
    Core.ObeysPure3 LeanSwe.RegExp.replaceAll Model.allowedReplaceAll ∧
    Core.ObeysPure2 LeanSwe.RegExp.splitBy Model.allowedSplitBy :=
  ⟨testPattern_matchesModel_props,
   findFirst_matchesModel_props,
   findAll_matchesModel_props,
   countMatches_matchesModel_props,
   replaceAll_matchesModel_props,
   splitBy_matchesModel_props⟩

end LeanSwe.RegExp.Proofs
