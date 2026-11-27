import Core.Obeys
import LeanSwe.RegExp.Interface
import LeanSwe.RegExp.Model
import LeanSwe.RegExp.Proofs.ParserClass
import LeanSwe.RegExp.Proofs.ParserMain
import LeanSwe.RegExp.Proofs.EvalCombinators
import LeanSwe.RegExp.Proofs.EvalMatch

namespace LeanSwe.RegExp.Proofs

open Core

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
