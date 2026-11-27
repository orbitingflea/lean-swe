import LeanSwe.NumParse.Interface
import LeanSweProofs.NumParse.Model
import LeanSweProofs.NumParse.SpecTests
import LeanSweProofs.NumParse.Proofs.IntProofs
import LeanSweProofs.NumParse.Proofs.FloatParseProofs

namespace LeanSwe.NumParse.Proofs

open Core
open Core.NondetTest
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Proof of `test_numparse_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_numparse_onError_returnsNonEmptyMessage :
    AllPass (test_numparse_onError_returnsNonEmptyMessage defaultApi) := by
  intro s
  dsimp [test_numparse_onError_returnsNonEmptyMessage, defaultApi, Internal.defaultApi, Bind.bind, Core.NondetTest.assert]
  cases h1 : Internal.parseInt s <;> cases h2 : Internal.parseInt64 s <;>
    cases h3 : Internal.parseFloat s <;> dsimp only <;> refine ⟨?_, ?_, ?_, trivial⟩ <;>
    first | trivial | exact (parseInt_spec s).2 _ h1 | exact (parseInt64_spec s).2 _ h2 | exact (parseFloat_spec s).2 _ h3

/-- Non-vacuity `CanReach` witness for `test_numparse_onError_returnsNonEmptyMessage`. -/
theorem reach_numparse_onError_returnsNonEmptyMessage :
    CanReach (test_numparse_onError_returnsNonEmptyMessage defaultApi) := ⟨"", proof_numparse_onError_returnsNonEmptyMessage ""⟩

/-- Proof of `test_numparse_parseInt_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt_matchesModel :
    AllPass (test_numparse_parseInt_matchesModel defaultApi) := by
  intro s; have hs := parseInt_spec s
  dsimp [test_numparse_parseInt_matchesModel, defaultApi, Internal.defaultApi, Core.NondetTest.assert]
  cases h : Internal.parseInt s with
  | error e => rw [show parseIntModel s = .error e.kind by rw [← hs.1, h]; rfl]; exact ⟨⟨rfl, hs.2 e h⟩, trivial⟩
  | ok v => rw [show parseIntModel s = .ok v by rw [← hs.1, h]; rfl]; exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt_matchesModel`. -/
theorem reach_numparse_parseInt_matchesModel :
    CanReach (test_numparse_parseInt_matchesModel defaultApi) := ⟨"0", proof_numparse_parseInt_matchesModel "0"⟩

/-- Proof of `test_numparse_parseInt64_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseInt64_matchesModel :
    AllPass (test_numparse_parseInt64_matchesModel defaultApi) := by
  intro s; have hs := parseInt64_spec s
  dsimp [test_numparse_parseInt64_matchesModel, defaultApi, Internal.defaultApi, Core.NondetTest.assert]
  cases h : Internal.parseInt64 s with
  | error e => rw [show parseInt64Model s = .error e.kind by rw [← hs.1, h]; rfl]; exact ⟨⟨rfl, hs.2 e h⟩, trivial⟩
  | ok v => rw [show parseInt64Model s = .ok v by rw [← hs.1, h]; rfl]; exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_parseInt64_matchesModel`. -/
theorem reach_numparse_parseInt64_matchesModel :
    CanReach (test_numparse_parseInt64_matchesModel defaultApi) := ⟨"0", proof_numparse_parseInt64_matchesModel "0"⟩

/-- Proof of `test_numparse_formatInt_roundTrip` for `defaultApi`. -/
theorem proof_numparse_formatInt_roundTrip :
    AllPass (test_numparse_formatInt_roundTrip defaultApi) := by
  intro n; rcases parseIntModel_formatInt n with ⟨hnoU, hmodel⟩
  have hpi_ok := impl_eq_ok_of_mapError (parseInt_spec (Internal.formatInt n)).1 hmodel
  have h64 := parseInt64_spec (Internal.formatInt n)
  dsimp [test_numparse_formatInt_roundTrip, defaultApi, Internal.defaultApi, Bind.bind, Core.NondetTest.assert]
  refine ⟨hnoU, hmodel, hpi_ok, ?_⟩
  by_cases hr : inInt64Range n = true
  · simp only [hr, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .ok (Int64.ofInt n) := by rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr]
    exact ⟨impl_eq_ok_of_mapError h64.1 hm64, trivial⟩
  · have hr' : inInt64Range n = false := Bool.eq_false_iff.mpr hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    have hm64 : parseInt64Model (Internal.formatInt n) = .error .overflow := by rw [parseInt64Model_eq_parseIntModel, hmodel]; simp [hr']
    rcases impl_eq_error_of_mapError h64.1 hm64 with ⟨e, he, hk⟩; rw [he]; exact ⟨⟨hk, h64.2 e he⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_formatInt_roundTrip`. -/
theorem reach_numparse_formatInt_roundTrip :
    CanReach (test_numparse_formatInt_roundTrip defaultApi) := ⟨0, proof_numparse_formatInt_roundTrip 0⟩

/-- Proof of `test_numparse_parseFloat_matchesModel` for `defaultApi`. -/
theorem proof_numparse_parseFloat_matchesModel :
    AllPass (test_numparse_parseFloat_matchesModel defaultApi) := by
  intro s; have hs := parseFloat_spec s
  dsimp [test_numparse_parseFloat_matchesModel, defaultApi, Internal.defaultApi, Core.NondetTest.assert]
  cases h : Internal.parseFloat s with
  | error e => rw [show parseFloatModel s = .error e.kind by rw [← hs.1, h]; rfl]; exact ⟨⟨rfl, hs.2 e h⟩, trivial⟩
  | ok v => rw [show parseFloatModel s = .ok v by rw [← hs.1, h]; rfl]; exact ⟨floatBitMatch_refl v, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_parseFloat_matchesModel`. -/
theorem reach_numparse_parseFloat_matchesModel :
    CanReach (test_numparse_parseFloat_matchesModel defaultApi) := ⟨"0.0", proof_numparse_parseFloat_matchesModel "0.0"⟩

private theorem evalSci_eq (neg : Bool) (m : Nat) (e : Int) :
    Internal.evalScientificFloat neg m e = evalFloat neg m e := by
  have h := Except.ok.inj ((parseFloatExpTail_spec "" neg m e ['0']).1)
  change Internal.evalScientificFloat neg m (0 + e) = evalFloat neg m (0 + e) at h
  rwa [Int.zero_add] at h

private theorem list_forM_allPass_bind {α : Type} (xs : List α) (f : α → AllPassRun Unit)
    (k : Unit → AllPassRun Unit) (post : Unit → Prop)
    (hxs : ∀ x ∈ xs, ∀ q : Unit → Prop, q () → f x q) (hk : k () post) :
    (xs.forM f >>= k) post := by
  induction xs with
  | nil => exact hk
  | cons x xs ih => exact hxs x (by simp) _ (ih (fun y hy => hxs y (by simp [hy])))

private theorem list_forM_allPass {α : Type} (xs : List α) (f : α → AllPassRun Unit)
    (post : Unit → Prop) (hxs : ∀ x ∈ xs, ∀ q : Unit → Prop, q () → f x q) (hp : post ()) :
    xs.forM f post := by
  induction xs with
  | nil => exact hp
  | cons x xs ih => exact hxs x (by simp) _ (ih (fun y hy => hxs y (by simp [hy])))

/-- Proof of `test_numparse_int_concreteBoundaries` for `defaultApi`. -/
theorem proof_numparse_int_concreteBoundaries :
    AllPass (test_numparse_int_concreteBoundaries defaultApi) := by
  unfold AllPass test_numparse_int_concreteBoundaries
  apply list_forM_allPass_bind
  · rintro ⟨s, exp⟩ hp q hq; dsimp only at hp ⊢
    have hm : parseIntModel s = .ok exp := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [show defaultApi.parseInt s = .ok exp from impl_eq_ok_of_mapError (parseInt_spec s).1 hm]; exact ⟨rfl, hq⟩
  · apply list_forM_allPass_bind
    · rintro ⟨s, exp⟩ hp q hq; dsimp only at hp ⊢
      have hm : parseIntModel s = .error exp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      rcases impl_eq_error_of_mapError (parseInt_spec s).1 hm with ⟨e, he, hk⟩
      rw [show defaultApi.parseInt s = .error e from he]; exact ⟨⟨hk, (parseInt_spec s).2 e he⟩, hq⟩
    · apply list_forM_allPass_bind
      · rintro ⟨s, exp⟩ hp q hq; dsimp only at hp ⊢
        have hm : parseInt64Model s = .ok exp := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        rw [show defaultApi.parseInt64 s = .ok exp from impl_eq_ok_of_mapError (parseInt64_spec s).1 hm]; exact ⟨rfl, hq⟩
      · apply list_forM_allPass_bind
        · rintro ⟨s, exp⟩ hp q hq; dsimp only at hp ⊢
          have hm : parseInt64Model s = .error exp := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
            rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
          rcases impl_eq_error_of_mapError (parseInt64_spec s).1 hm with ⟨e, he, hk⟩
          rw [show defaultApi.parseInt64 s = .error e from he]; exact ⟨⟨hk, (parseInt64_spec s).2 e he⟩, hq⟩
        · apply list_forM_allPass _ _ _ _ True.intro; intro n _ q hq
          exact ⟨⟨(parseIntModel_formatInt n).2, impl_eq_ok_of_mapError (parseInt_spec _).1 (parseIntModel_formatInt n).2⟩, hq⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_int_concreteBoundaries`. -/
theorem reach_numparse_int_concreteBoundaries : CanReach (test_numparse_int_concreteBoundaries defaultApi) :=
  proof_numparse_int_concreteBoundaries

private theorem float_ok_case {s : String} {expected : Float}
    (h : ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch expected y) {q : Unit → Prop} (hq : q ()) :
    (match defaultApi.parseFloat s with
      | .ok actual => NondetTest.assert (FloatBitMatch expected actual)
      | .error _ => NondetTest.assert False : AllPassRun Unit) q := by
  rcases h with ⟨y, hmy, hbit⟩
  rw [show defaultApi.parseFloat s = .ok y from impl_eq_ok_of_mapError (parseFloat_spec s).1 hmy]; exact ⟨hbit, hq⟩

private theorem exists_parseFloatModel_of_eq {s : String} {neg : Bool} {m : Nat} {e : Int}
    (h : parseFloatModel s = .ok (evalFloat neg m e)) :
    ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch (evalFloat neg m e) y :=
  ⟨evalFloat neg m e, h, floatBitMatch_refl _⟩

/-- Proof of `test_numparse_float_concreteSpecialsAndEdges` for `defaultApi`. -/
theorem proof_numparse_float_concreteSpecialsAndEdges :
    AllPass (test_numparse_float_concreteSpecialsAndEdges defaultApi) := by
  have hBig : ∀ {s : String} {neg : Bool} {m : Nat} {e : Int} {v : Float},
      evalFloat neg m e = v → parseFloatModel s = .ok (evalFloat neg m e) → ∃ y, parseFloatModel s = .ok y ∧ FloatBitMatch v y :=
    fun hv hp => ⟨_, hp.trans (congrArg Except.ok hv), floatBitMatch_refl _⟩
  unfold AllPass test_numparse_float_concreteSpecialsAndEdges
  apply list_forM_allPass_bind
  · intro p hp q hq; apply float_ok_case _ hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, floatBitMatch_refl _⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact exists_parseFloatModel_of_eq rfl
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact ⟨_, rfl, by unfold FloatBitMatch; decide⟩
    · exact hBig (evalSci_eq false 1 400).symm rfl
    · exact hBig (evalSci_eq true 1 400).symm rfl
    · exact hBig (evalSci_eq false 1 (-400)).symm rfl
    · exact hBig (evalSci_eq true 1 (-400)).symm rfl
    · exact hBig (evalSci_eq false 1 1000000000).symm rfl
    · exact hBig (evalSci_eq true 1 1000000000).symm rfl
    · exact hBig (evalSci_eq false 1 (-1000000000)).symm rfl
    · exact hBig (evalSci_eq true 1 (-1000000000)).symm rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
    · exact exists_parseFloatModel_of_eq rfl
  · apply list_forM_allPass_bind
    · rintro ⟨s, exp⟩ hp q hq; dsimp only at hp ⊢
      have hm : parseFloatModel s = .error exp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      rcases impl_eq_error_of_mapError (parseFloat_spec s).1 hm with ⟨e, he, hk⟩
      rw [show defaultApi.parseFloat s = .error e from he]; exact ⟨⟨hk, (parseFloat_spec s).2 e he⟩, hq⟩
    · have hp : defaultApi.parseFloat "0.0" = .ok (evalFloat false 0 (-1)) := impl_eq_ok_of_mapError (parseFloat_spec "0.0").1 rfl
      have hn : defaultApi.parseFloat "-0.0" = .ok (evalFloat true 0 (-1)) := impl_eq_ok_of_mapError (parseFloat_spec "-0.0").1 rfl
      rw [hp, hn]; exact ⟨by decide, by decide, by decide, by unfold FloatEquiv; decide, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_numparse_float_concreteSpecialsAndEdges`. -/
theorem reach_numparse_float_concreteSpecialsAndEdges : CanReach (test_numparse_float_concreteSpecialsAndEdges defaultApi) :=
  proof_numparse_float_concreteSpecialsAndEdges

end LeanSwe.NumParse.Proofs
