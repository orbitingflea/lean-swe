import Lean.Data.Json.Basic
import LeanSwe.Json.Interface
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ModelDecode
import LeanSwe.Json.Proofs.TreeMapWf
import LeanSwe.Json.Proofs.ParseCompleteHelpers
import LeanSwe.Json.Proofs.FormatScalar
import LeanSwe.Json.Proofs.FormatNumber
import LeanSwe.Json.Proofs.FormatTreeDoc
import LeanSwe.Json.Proofs.FormatCompress

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Single-line flattened string of a `JsonDoc` (`line` emits `" "`). -/
def flatDoc : JsonDoc → String
  | .text s => s
  | .line => " "
  | .nest _ d => flatDoc d
  | .group d => flatDoc d
  | .append d1 d2 => flatDoc d1 ++ flatDoc d2

/-- Flattened string of a worklist of `DocItem`s. -/
def itemsFlatStr : List DocItem → String
  | [] => ""
  | it :: rest => flatDoc it.doc ++ itemsFlatStr rest

/-- Every call to `formatDocLoop` appends a suffix onto `acc`. -/
theorem formatDocLoop_append_acc :
    ∀ (w : Nat) (items : List DocItem) (width col : Nat) (acc : String),
      docItemsWeight items ≤ w →
      ∃ suf : String, formatDocLoop width col acc items = acc ++ suf := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro items width col acc hw
    cases items with
    | nil => unfold formatDocLoop; exact ⟨"", (String.append_empty).symm⟩
    | cons it rest =>
      rcases it with ⟨fl, ind, d⟩
      cases d with
      | text s =>
        unfold formatDocLoop
        obtain ⟨suf, hsuf⟩ := ih (docItemsWeight rest) (by simp [docItemsWeight, docWeight] at hw ⊢; omega)
          rest width (col + s.length) (acc ++ s) (Nat.le_refl _)
        exact ⟨s ++ suf, by rw [hsuf, String.append_assoc]⟩
      | line =>
        unfold formatDocLoop
        by_cases hfl : fl = true
        · simp only [hfl, ↓reduceIte]
          obtain ⟨suf, hsuf⟩ := ih (docItemsWeight rest) (by simp [docItemsWeight, docWeight] at hw ⊢; omega)
            rest width (col + 1) (acc ++ " ") (Nat.le_refl _)
          exact ⟨" " ++ suf, by rw [hsuf, String.append_assoc]⟩
        · simp only [hfl, Bool.false_eq_true, ↓reduceIte]
          let nl := String.ofList ('\n' :: List.replicate ind ' ')
          obtain ⟨suf, hsuf⟩ := ih (docItemsWeight rest) (by simp [docItemsWeight, docWeight] at hw ⊢; omega)
            rest width ind (acc ++ nl) (Nat.le_refl _)
          exact ⟨nl ++ suf, by rw [hsuf, String.append_assoc]⟩
      | nest n sub =>
        unfold formatDocLoop
        exact ih (docItemsWeight (⟨fl, ind + n, sub⟩ :: rest))
          (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ width col acc (Nat.le_refl _)
      | append d1 d2 =>
        unfold formatDocLoop
        exact ih (docItemsWeight (⟨fl, ind, d1⟩ :: ⟨fl, ind, d2⟩ :: rest))
          (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ width col acc (Nat.le_refl _)
      | group sub =>
        unfold formatDocLoop; dsimp only
        exact ih (docItemsWeight (⟨_, ind, sub⟩ :: rest))
          (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ width col acc (Nat.le_refl _)

/-- When all items have `flatten = true`, `formatDocLoop` appends `itemsFlatStr items` onto `acc`. -/
theorem formatDocLoop_all_flat :
    ∀ (w : Nat) (items : List DocItem) (width col : Nat) (acc : String),
      docItemsWeight items ≤ w →
      items.all (·.flatten) = true →
      formatDocLoop width col acc items = acc ++ itemsFlatStr items := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro items width col acc hw hall
    cases items with
    | nil => simp [formatDocLoop, itemsFlatStr]
    | cons it rest =>
      rcases it with ⟨fl, ind, d⟩
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rcases hall with ⟨rfl, hallRest⟩
      cases d with
      | text s =>
        unfold formatDocLoop itemsFlatStr flatDoc
        rw [ih (docItemsWeight rest) (by simp [docItemsWeight, docWeight] at hw ⊢; omega)
          rest width _ _ (Nat.le_refl _) hallRest, String.append_assoc]
      | line =>
        unfold formatDocLoop itemsFlatStr flatDoc; simp only [↓reduceIte]
        rw [ih (docItemsWeight rest) (by simp [docItemsWeight, docWeight] at hw ⊢; omega)
          rest width _ _ (Nat.le_refl _) hallRest, String.append_assoc]
      | nest n sub =>
        unfold formatDocLoop itemsFlatStr flatDoc
        exact ih (docItemsWeight (⟨true, ind + n, sub⟩ :: rest))
          (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ width col acc (Nat.le_refl _)
          (by simp [hallRest])
      | append d1 d2 =>
        unfold formatDocLoop itemsFlatStr flatDoc
        rw [ih (docItemsWeight (⟨true, ind, d1⟩ :: ⟨true, ind, d2⟩ :: rest))
          (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ width col acc (Nat.le_refl _)
          (by simp [hallRest])]
        simp [itemsFlatStr, String.append_assoc]
      | group sub =>
        unfold formatDocLoop itemsFlatStr flatDoc; simp only [Bool.true_or]
        exact ih (docItemsWeight (⟨true, ind, sub⟩ :: rest))
          (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ width col acc (Nat.le_refl _)
          (by simp [hallRest])

/-- When all items have `flatten = true`, `docFits rem items` equals `decide ((itemsFlatStr items).length ≤ rem)`. -/
theorem docFits_all_flat :
    ∀ (w : Nat) (items : List DocItem) (rem : Int),
      docItemsWeight items ≤ w →
      items.all (·.flatten) = true →
      docFits rem items = decide (((itemsFlatStr items).length : Int) ≤ rem) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro items rem hw hall
    cases items with
    | nil => simp [docFits, itemsFlatStr]
    | cons it rest =>
      rcases it with ⟨fl, ind, d⟩
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rcases hall with ⟨rfl, hallRest⟩
      cases d with
      | text s =>
        unfold docFits itemsFlatStr flatDoc
        by_cases hneg : rem < 0
        · simp only [hneg, ↓reduceIte, String.length_append]
          symm; apply decide_eq_false; omega
        · simp only [hneg, ↓reduceIte, String.length_append]
          rw [ih (docItemsWeight rest) (by simp [docItemsWeight, docWeight] at hw ⊢; omega)
            rest _ (Nat.le_refl _) hallRest]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      | line =>
        unfold docFits itemsFlatStr flatDoc; simp only [↓reduceIte]
        by_cases hneg : rem < 0
        · simp only [hneg, ↓reduceIte, String.length_append]
          symm; apply decide_eq_false; omega
        · simp only [hneg, ↓reduceIte, String.length_append]
          have hspLen : " ".length = 1 := rfl
          rw [hspLen, ih (docItemsWeight rest) (by simp [docItemsWeight, docWeight] at hw ⊢; omega)
            rest _ (Nat.le_refl _) hallRest]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      | nest n sub =>
        unfold docFits itemsFlatStr flatDoc
        by_cases hneg : rem < 0
        · simp only [hneg, ↓reduceIte]; symm; apply decide_eq_false; omega
        · simp only [hneg, ↓reduceIte]
          simpa [itemsFlatStr] using ih (docItemsWeight (⟨true, ind + n, sub⟩ :: rest))
            (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ rem (Nat.le_refl _) (by simp [hallRest])
      | append d1 d2 =>
        unfold docFits itemsFlatStr flatDoc
        by_cases hneg : rem < 0
        · simp only [hneg, ↓reduceIte]; symm; apply decide_eq_false; omega
        · simp only [hneg, ↓reduceIte]
          have hsub := ih (docItemsWeight (⟨true, ind, d1⟩ :: ⟨true, ind, d2⟩ :: rest))
            (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ rem (Nat.le_refl _) (by simp [hallRest])
          simpa [itemsFlatStr, String.append_assoc] using hsub
      | group sub =>
        unfold docFits itemsFlatStr flatDoc
        by_cases hneg : rem < 0
        · simp only [hneg, ↓reduceIte]; symm; apply decide_eq_false; omega
        · simp only [hneg, ↓reduceIte]
          simpa [itemsFlatStr] using ih (docItemsWeight (⟨true, ind, sub⟩ :: rest))
            (by simp [docItemsWeight, docWeight] at hw ⊢; omega) _ rem (Nat.le_refl _) (by simp [hallRest])

/-- `flatDoc (joinCommaLineFwd d0 dtl)` equals `String.intercalate ", "` of `flatDoc`. -/
theorem flatDoc_joinCommaLineFwd (d0 : JsonDoc) (dtl : List JsonDoc) :
    flatDoc (joinCommaLineFwd d0 dtl) = String.intercalate ", " ((d0 :: dtl).map flatDoc) := by
  induction dtl generalizing d0 with
  | nil => simp [joinCommaLineFwd, String.intercalate_singleton]
  | cons d1 rest ih =>
    simp only [joinCommaLineFwd, flatDoc, ih d1]
    have hc : "," ++ (" " ++ String.intercalate ", " ((d1 :: rest).map flatDoc)) =
        ", " ++ String.intercalate ", " ((d1 :: rest).map flatDoc) := by
      rw [← String.append_assoc]; rfl
    rw [hc]
    simp only [List.map_cons, String.intercalate_cons_cons, ← String.append_assoc]

private theorem flatPrettyTree_eq_entries :
    ∀ (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)),
      flatPrettyTree t = (treeEntries t).map (fun (ek, ev) => canonicalStringLit ek ++ ": " ++ flatPretty ev)
  | .leaf => by simp [flatPrettyTree, treeEntries]
  | .inner _ k v l r => by
    rw [flatPrettyTree, treeEntries]
    simp [flatPrettyTree_eq_entries l, flatPrettyTree_eq_entries r]

/-- `flatDoc (treeDoc j)` equals `Model.flatPretty j` for every `j : Lean.Json`. -/
theorem flatDoc_treeDoc_eq_flatPretty :
    ∀ (n : Nat) (j : Lean.Json), jsonRank j ≤ n → flatDoc (treeDoc j) = flatPretty j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j hj
    cases j with
    | null => unfold treeDoc flatDoc flatPretty; rfl
    | bool b => cases b <;> (unfold treeDoc flatDoc flatPretty; rfl)
    | num x => unfold treeDoc flatDoc flatPretty; exact jsonNumberToString_eq_canonical x
    | str s => unfold treeDoc flatDoc flatPretty; exact renderString_eq_canonicalStringLit s
    | arr elems =>
      cases hlist : elems.toList with
      | nil =>
        rw [treeDoc_arr_nil hlist]
        unfold flatPretty
        simp [hlist, flatDoc]
      | cons x0 xtl =>
        rw [treeDoc_arr_cons hlist]
        unfold flatPretty
        simp only [hlist, docBracket, flatDoc, flatDoc_joinCommaLineFwd]
        have hRankSub : ∀ x ∈ x0 :: xtl, jsonRank x < n := by
          intro x hx
          have hlt := jsonRank_lt_jsonListRank hx
          simp only [jsonRank, hlist] at hj; omega
        have hMap : ∀ xs : List Lean.Json, (∀ x ∈ xs, jsonRank x < n) →
            (treeDocList xs).map flatDoc = flatPrettyList xs := by
          intro xs hR; induction xs with
          | nil => rw [treeDocList, flatPrettyList]; rfl
          | cons u utl ihu =>
            rw [treeDocList, flatPrettyList]
            simp [ih (jsonRank u) (hR u List.mem_cons_self) u (Nat.le_refl _),
              ihu (fun y hy => hR y (List.mem_cons_of_mem _ hy))]
        have hm := hMap xtl (fun y hy => hRankSub y (List.mem_cons_of_mem _ hy))
        have hx0 := ih (jsonRank x0) (hRankSub x0 List.mem_cons_self) x0 (Nat.le_refl _)
        rw [flatPrettyList]
        simp [hx0, hm, String.append_assoc]
    | obj kvs =>
      cases hEnt : objEntries kvs with
      | nil =>
        rw [treeDoc_obj_nil hEnt]
        unfold flatPretty
        simp [hEnt, flatDoc]
      | cons e0 etl =>
        rw [treeDoc_obj_cons hEnt]
        unfold flatPretty
        have hTreeEq : flatPrettyTree kvs.inner.inner =
            (e0 :: etl).map (fun (ek, ev) => canonicalStringLit ek ++ ": " ++ flatPretty ev) := by
          rw [flatPrettyTree_eq_entries, ← objEntries, hEnt]
        simp only [hEnt, hTreeEq, docBracket, flatDoc, flatDoc_joinCommaLineFwd]
        have hRankSub : ∀ p ∈ e0 :: etl, jsonRank p.2 < n := by
          intro ⟨ek, ev⟩ hp
          have hlt := jsonRank_lt_jsonAssocRank hp
          have htr : jsonAssocRank (e0 :: etl) = jsonTreeRank kvs.inner.inner := by
            rw [← hEnt]; exact jsonAssocRank_treeEntries kvs.inner.inner
          simp only [jsonRank] at hj; dsimp only at *; omega
        have hKvFlat : ∀ p ∈ e0 :: etl, flatDoc (kvDoc p) = canonicalStringLit p.1 ++ ": " ++ flatPretty p.2 := by
          intro ⟨ek, ev⟩ hp
          simp only [kvDoc, flatDoc, renderString_eq_canonicalStringLit,
            ih (jsonRank ev) (hRankSub (ek, ev) hp) ev (Nat.le_refl _)]
          simp [String.append_assoc]; rfl
        have hMapKv : ∀ sub : List (String × Lean.Json), (∀ p ∈ sub, p ∈ e0 :: etl) →
            (sub.map kvDoc).map flatDoc = sub.map (fun (ek, ev) => canonicalStringLit ek ++ ": " ++ flatPretty ev) := by
          intro sub hSub; induction sub with
          | nil => rfl
          | cons a atl iha =>
            simp [hKvFlat a (hSub a List.mem_cons_self), iha (fun p hp => hSub p (List.mem_cons_of_mem _ hp))]
        have hm := hMapKv (e0 :: etl) (fun _ h => h)
        simp only [List.map_cons] at hm ⊢
        rw [hm]
        simp [String.append_assoc]

/-- Evaluating a single `.text s` item from `""` returns `s`. -/
theorem formatDocLoop_singleton_text (w : Nat) (s : String) :
    formatDocLoop w 0 "" [⟨false, 0, .text s⟩] = s := by
  unfold formatDocLoop
  unfold formatDocLoop
  exact String.empty_append

/-- Non-empty and `startsWith "{"` properties of `pretty j lineWidth` for all `j` and `lineWidth`. -/
theorem pretty_nonEmpty_and_startsWith (j : Lean.Json) (lineWidth : Nat) :
    let out := LeanSwe.Json.pretty j lineWidth
    !out.isEmpty = true ∧ out.startsWith "{" = (match j with | .obj _ => true | _ => false) := by
  have hCons : ∀ {s : String} {c : Char} {tl : List Char}, s.toList = c :: tl →
      !s.isEmpty = true ∧ s.startsWith "{" = (c == '{') :=
    fun h => ⟨not_isEmpty_iff.mpr (by rw [h]; simp), startsWith_openBrace_of_toList_cons h⟩
  have hBracket : ∀ (openCh : Char) (body : JsonDoc) (closeDel : String),
      ∃ suf : String,
        formatDocLoop lineWidth 0 "" [⟨false, 0, docBracket (String.ofList [openCh]) body closeDel⟩] =
          String.ofList (openCh :: suf.toList) := by
    intro openCh body closeDel
    dsimp only [docBracket]
    unfold formatDocLoop; dsimp only
    unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop
    obtain ⟨suf, hsuf⟩ := formatDocLoop_append_acc _ _ lineWidth _ ("" ++ String.ofList [openCh]) (Nat.le_refl _)
    refine ⟨suf, ?_⟩
    rw [hsuf]
    calc "" ++ String.ofList [openCh] ++ suf
        = String.ofList [openCh] ++ String.ofList suf.toList := by simp [String.ofList_toList]
      _ = String.ofList (openCh :: suf.toList) := by rw [← String.ofList_append, List.singleton_append]
  simp only [LeanSwe.Json.pretty, Internal.pretty, renderFormat_eq_treeDoc]
  cases j with
  | null =>
    unfold treeDoc; rw [formatDocLoop_singleton_text]
    exact hCons (c := 'n') (tl := ['u', 'l', 'l']) rfl
  | bool b =>
    cases b <;> (unfold treeDoc; rw [formatDocLoop_singleton_text])
    · exact hCons (c := 'f') (tl := ['a', 'l', 's', 'e']) rfl
    · exact hCons (c := 't') (tl := ['r', 'u', 'e']) rfl
  | num n =>
    unfold treeDoc; rw [formatDocLoop_singleton_text]
    obtain ⟨h1, _, _, h4, _⟩ := jsonNumberToString_spec n
    exact ⟨h1, h4⟩
  | str s =>
    unfold treeDoc; rw [formatDocLoop_singleton_text]
    obtain ⟨h1, _, _, h4, _⟩ := renderString_spec s
    exact ⟨h1, h4⟩
  | arr elems =>
    cases hlist : elems.toList with
    | nil =>
      rw [treeDoc_arr_nil hlist, formatDocLoop_singleton_text]
      exact hCons (c := '[') (tl := [']']) rfl
    | cons x0 xtl =>
      rw [treeDoc_arr_cons hlist]
      obtain ⟨suf, hsuf⟩ := hBracket '[' (joinCommaLineFwd (treeDoc x0) (treeDocList xtl)) "]"
      dsimp only; rw [hsuf]
      exact hCons String.toList_ofList
  | obj kvs =>
    cases hEnt : objEntries kvs with
    | nil =>
      rw [treeDoc_obj_nil hEnt, formatDocLoop_singleton_text]
      exact hCons (c := '{') (tl := ['}']) rfl
    | cons e0 etl =>
      rw [treeDoc_obj_cons hEnt]
      obtain ⟨suf, hsuf⟩ := hBracket '{' (joinCommaLineFwd (kvDoc e0) (etl.map kvDoc)) "}"
      dsimp only; rw [hsuf]
      exact hCons String.toList_ofList

/-- Flattening guarantee: whenever `(flatPretty j).length ≤ lineWidth`, `pretty j lineWidth = flatPretty j`. -/
theorem pretty_eq_flatPretty_of_le (j : Lean.Json) (lineWidth : Nat)
    (hle : (flatPretty j).length ≤ lineWidth) :
    LeanSwe.Json.pretty j lineWidth = flatPretty j := by
  have hFlatEq := flatDoc_treeDoc_eq_flatPretty (jsonRank j) j (Nat.le_refl _)
  rw [← hFlatEq] at hle ⊢
  simp only [LeanSwe.Json.pretty, Internal.pretty, renderFormat_eq_treeDoc]
  have hGroup : ∀ inner : JsonDoc, (flatDoc (.group inner)).length ≤ lineWidth →
      formatDocLoop lineWidth 0 "" [⟨false, 0, .group inner⟩] = flatDoc (.group inner) := by
    intro inner hlen
    unfold formatDocLoop; dsimp only
    have hFits := docFits_all_flat (docItemsWeight [⟨true, 0, inner⟩]) [⟨true, 0, inner⟩]
      ((lineWidth : Int) - 0) (Nat.le_refl _) rfl
    simp only [itemsFlatStr, String.append_empty, Int.sub_zero] at hFits
    have hFitTrue : docFits ((lineWidth : Int) - (0 : Nat)) [⟨true, 0, inner⟩] = true := by
      have hz : ((0 : Nat) : Int) = 0 := rfl
      rw [hz, Int.sub_zero, hFits, decide_eq_true_iff]
      exact Int.ofNat_le.mpr hlen
    rw [hFitTrue, Bool.false_or, formatDocLoop_all_flat _ [⟨true, 0, inner⟩] lineWidth 0 "" (Nat.le_refl _) rfl]
    simp [itemsFlatStr, flatDoc]
  cases j with
  | null => unfold treeDoc flatDoc; exact formatDocLoop_singleton_text lineWidth "null"
  | bool b => cases b <;> (unfold treeDoc flatDoc; exact formatDocLoop_singleton_text lineWidth _)
  | num n => unfold treeDoc flatDoc; exact formatDocLoop_singleton_text lineWidth _
  | str s => unfold treeDoc flatDoc; exact formatDocLoop_singleton_text lineWidth _
  | arr elems =>
    cases hlist : elems.toList with
    | nil =>
      rw [treeDoc_arr_nil hlist]; unfold flatDoc
      exact formatDocLoop_singleton_text lineWidth "[]"
    | cons x0 xtl =>
      rw [treeDoc_arr_cons hlist] at hle ⊢
      exact hGroup _ hle
  | obj kvs =>
    cases hEnt : objEntries kvs with
    | nil =>
      rw [treeDoc_obj_nil hEnt]; unfold flatDoc
      exact formatDocLoop_singleton_text lineWidth "{}"
    | cons e0 etl =>
      rw [treeDoc_obj_cons hEnt] at hle ⊢
      exact hGroup _ hle

end LeanSwe.Json.Proofs
