import Lean.Data.Json.Basic
import Core.Obeys
import LeanSwe.Json.Interface
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.ModelDecode
import LeanSweProofs.Json.Proofs.TreeMapWf
import LeanSweProofs.Json.Proofs.ParseCompleteHelpers
import LeanSweProofs.Json.Proofs.FormatScalar
import LeanSweProofs.Json.Proofs.FormatNumber
import LeanSweProofs.Json.Proofs.FormatTreeDoc

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Pure compact evaluation of a single `JsonDoc` node (`line` emits `""`). -/
def compactOne : JsonDoc → String
  | .text s => s
  | .line => ""
  | .nest _ d => compactOne d
  | .group d => compactOne d
  | .append d1 d2 => compactOne d1 ++ compactOne d2

/-- `compactDocLoop` steps across one head `JsonDoc` by appending `compactOne d`. -/
theorem compactDocLoop_cons (d : JsonDoc) :
    ∀ (rest : List JsonDoc) (acc : String),
      compactDocLoop acc (d :: rest) = compactDocLoop (acc ++ compactOne d) rest := by
  induction d with
  | text s => intros; simp [compactDocLoop, compactOne]
  | line => intros; simp [compactDocLoop, compactOne]
  | nest n d ih => intros; simp [compactDocLoop, compactOne, ih]
  | group d ih => intros; simp [compactDocLoop, compactOne, ih]
  | append d1 d2 ih1 ih2 => intros; simp [compactDocLoop, compactOne, ih1, ih2, String.append_assoc]

/-- `LeanSwe.Json.compress j` equals `compactOne (treeDoc j)`. -/
theorem compress_eq_compactOne (j : Lean.Json) :
    LeanSwe.Json.compress j = compactOne (treeDoc j) := by
  simp [LeanSwe.Json.compress, Internal.compress, renderFormat_eq_treeDoc,
    compactDocLoop_cons, compactDocLoop]

/-- Forward comma-line joiner equivalent to `joinCommaLineRev`. -/
def joinCommaLineFwd : JsonDoc → List JsonDoc → JsonDoc
  | d0, [] => d0
  | d0, d1 :: dtl => .append d0 (.append (.text ",") (.append .line (joinCommaLineFwd d1 dtl)))
termination_by structural _ ds => ds

/-- Snoc-pair merging identity for `joinCommaLineFwd`. -/
theorem joinCommaLineFwd_snoc_pair (ds : List JsonDoc) (a b : JsonDoc) :
    (match ds ++ [a, b] with | [] => JsonDoc.text "" | h :: t => joinCommaLineFwd h t) =
      (match ds ++ [JsonDoc.append a (.append (.text ",") (.append .line b))] with
       | [] => JsonDoc.text "" | h :: t => joinCommaLineFwd h t) := by
  induction ds with
  | nil => rfl
  | cons d tl ih =>
    cases tl with
    | nil => rfl
    | cons d2 tl2 => simp only [List.cons_append, joinCommaLineFwd]; congr 3

/-- `joinCommaLineRev acc revDocs` equals `joinCommaLineFwd` over `revDocs.reverse ++ [acc]`. -/
theorem joinCommaLineRev_eq_fwd (acc : JsonDoc) (revDocs : List JsonDoc) :
    joinCommaLineRev acc revDocs =
      match revDocs.reverse ++ [acc] with
      | [] => acc
      | h :: t => joinCommaLineFwd h t := by
  induction revDocs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [joinCommaLineRev, ih, List.reverse_cons, List.append_assoc, List.singleton_append]
    have h := joinCommaLineFwd_snoc_pair xs.reverse x acc
    cases h1 : xs.reverse ++ [x, acc] with
    | nil => exfalso; have := congrArg List.length h1; simp at this
    | cons u utl =>
      cases h2 : xs.reverse ++ [JsonDoc.append x (.append (.text ",") (.append .line acc))] with
      | nil => exfalso; have := congrArg List.length h2; simp at this
      | cons v vtl =>
        rw [h1, h2] at h; exact h.symm

/-- Formatted `JsonDoc` for a single `(key, value)` object entry. -/
def kvDoc (p : String × Lean.Json) : JsonDoc :=
  JsonDoc.group (.append (.text (renderString p.1 ++ ":")) (.append .line (treeDoc p.2)))

/-- Map relation between `treeEntriesDoc t` and `treeEntries t`. -/
theorem treeEntriesDoc_eq_map (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    treeEntriesDoc t = (treeEntries t).map kvDoc := by
  induction t with
  | leaf => simp [treeEntriesDoc, treeEntries]
  | inner _ k v l r ihl ihr => rw [treeEntriesDoc, treeEntries]; simp [ihl, ihr, kvDoc]

/-- Unfolding equation for `treeDoc` on an empty array. -/
theorem treeDoc_arr_nil {elems : Array Lean.Json} (h : elems.toList = []) :
    treeDoc (.arr elems) = .text "[]" := by
  rcases elems with ⟨l⟩; dsimp at h; subst h; unfold treeDoc; rfl

/-- Unfolding equation for `treeDoc` on a non-empty array. -/
theorem treeDoc_arr_cons {elems : Array Lean.Json} {x0 : Lean.Json} {xtl : List Lean.Json}
    (h : elems.toList = x0 :: xtl) :
    treeDoc (.arr elems) = docBracket "[" (joinCommaLineFwd (treeDoc x0) (treeDocList xtl)) "]" := by
  rcases elems with ⟨l⟩
  dsimp at h; subst h
  conv => lhs; unfold treeDoc
  dsimp only
  cases hrev : (x0 :: xtl).reverse with
  | nil => exfalso; have := congrArg List.length hrev; simp at this
  | cons last restRev =>
    dsimp only
    rw [joinCommaLineRev_eq_fwd]
    have hEq2 := congrArg List.reverse hrev
    rw [List.reverse_reverse, List.reverse_cons] at hEq2
    have hLast : treeDocList [last] = [treeDoc last] := by rw [treeDocList, treeDocList]
    have hCons : treeDocList (x0 :: xtl) = treeDoc x0 :: treeDocList xtl := by rw [treeDocList]
    have hCancel : (treeDocList restRev).reverse ++ [treeDoc last] = treeDoc x0 :: treeDocList xtl := by
      rw [← treeDocList_reverse, ← hLast, ← treeDocList_append, hEq2.symm, hCons]
    rw [hCancel]

/-- Unfolding equation for `treeDoc` on an empty object (`objEntries kvs = []`). -/
theorem treeDoc_obj_nil {kvs : Std.TreeMap.Raw String Lean.Json compare} (h : objEntries kvs = []) :
    treeDoc (.obj kvs) = .text "{}" := by
  rcases kvs with ⟨⟨t⟩⟩
  cases t with
  | leaf => unfold treeDoc; rfl
  | inner sz k v l r => simp [objEntries, treeEntries] at h

/-- Unfolding equation for `treeDoc` on a non-empty object (`objEntries kvs = e0 :: etl`). -/
theorem treeDoc_obj_cons {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {e0 : String × Lean.Json} {etl : List (String × Lean.Json)}
    (h : objEntries kvs = e0 :: etl) :
    treeDoc (.obj kvs) = docBracket "{" (joinCommaLineFwd (kvDoc e0) (etl.map kvDoc)) "}" := by
  rcases kvs with ⟨⟨t⟩⟩
  cases t with
  | leaf => simp [objEntries, treeEntries] at h
  | inner sz k v l r =>
    dsimp [objEntries] at h
    conv => lhs; unfold treeDoc
    dsimp only
    rw [treeEntriesDoc_eq_map, h]
    cases hrev : ((e0 :: etl).map kvDoc).reverse with
    | nil => exfalso; have := congrArg List.length hrev; simp at this
    | cons last restRev =>
      dsimp only
      rw [joinCommaLineRev_eq_fwd]
      have hCancel : restRev.reverse ++ [last] = kvDoc e0 :: etl.map kvDoc := by
        have hEq2 := congrArg List.reverse hrev
        simpa [List.reverse_cons] using hEq2.symm
      rw [hCancel]

/-- Strict rank bound `jsonRank ev < jsonAssocRank es` for any `(ek, ev) ∈ es`. -/
theorem jsonRank_lt_jsonAssocRank {ek : String} {ev : Lean.Json} :
    ∀ {es : List (String × Lean.Json)}, (ek, ev) ∈ es → jsonRank ev < jsonAssocRank es
  | [], hp => by cases hp
  | (ak, av) :: atl, hp => by
    simp only [List.mem_cons, jsonAssocRank] at hp ⊢
    rcases hp with hEq | hm
    · injection hEq with _ hv; subst hv; omega
    · have := jsonRank_lt_jsonAssocRank hm; omega

/-- Strict rank bound `jsonRank x < jsonListRank xs` for any `x ∈ xs`. -/
theorem jsonRank_lt_jsonListRank {x : Lean.Json} :
    ∀ {xs : List Lean.Json}, x ∈ xs → jsonRank x < jsonListRank xs
  | [], hx => by cases hx
  | a :: atl, hx => by
    simp only [List.mem_cons, jsonListRank] at hx ⊢
    rcases hx with rfl | hm
    · omega
    · have := jsonRank_lt_jsonListRank hm; omega

/-- `compactOne (joinCommaLineFwd d0 dtl)` equals `String.intercalate ","` of `compactOne`. -/
theorem compactOne_joinCommaLineFwd (d0 : JsonDoc) (dtl : List JsonDoc) :
    compactOne (joinCommaLineFwd d0 dtl) = String.intercalate "," ((d0 :: dtl).map compactOne) := by
  induction dtl generalizing d0 with
  | nil => simp [joinCommaLineFwd, String.intercalate_singleton]
  | cons d1 rest ih =>
    simp only [joinCommaLineFwd, compactOne, String.empty_append, ih d1, List.map_cons]
    rw [String.intercalate_cons_cons, String.append_assoc]

/-- Single-line character check (`c ≠ '\n' ∧ c ≠ '\r'`) preserved across `String.intercalate ","`. -/
theorem noCrLf_intercalate_comma :
    ∀ (ps : List String),
      (∀ p ∈ ps, !p.contains '\n' = true ∧ !p.contains '\r' = true) →
      !(String.intercalate "," ps).contains '\n' = true ∧
        !(String.intercalate "," ps).contains '\r' = true
  | [], _ => ⟨not_contains_char_iff.mpr (by decide), not_contains_char_iff.mpr (by decide)⟩
  | [p], h => by rw [String.intercalate_singleton]; exact h p List.mem_cons_self
  | p1 :: p2 :: rest, h => by
    obtain ⟨ih1, ih2⟩ := noCrLf_intercalate_comma (p2 :: rest) (fun p hp => h p (List.mem_cons_of_mem _ hp))
    obtain ⟨hp1n, hp1r⟩ := h p1 List.mem_cons_self
    rw [String.intercalate_cons_cons]
    rw [not_contains_char_iff] at hp1n hp1r ih1 ih2
    have hComma : ",".toList = [','] := rfl
    refine ⟨?_, ?_⟩
    · rw [not_contains_char_iff, String.toList_append, String.toList_append, hComma]
      intro hm
      rcases List.mem_append.mp hm with hm1 | hm2
      · rcases List.mem_append.mp hm1 with h1 | h2
        · exact hp1n h1
        · simp only [List.mem_singleton] at h2; cases h2
      · exact ih1 hm2
    · rw [not_contains_char_iff, String.toList_append, String.toList_append, hComma]
      intro hm
      rcases List.mem_append.mp hm with hm1 | hm2
      · rcases List.mem_append.mp hm1 with h1 | h2
        · exact hp1r h1
        · simp only [List.mem_singleton] at h2; cases h2
      · exact ih2 hm2

/-- Joint induction proving all `Model.allowedCompress` obligations on `compactOne (treeDoc j)`. -/
theorem compactOne_treeDoc_spec :
    ∀ (n : Nat) (j : Lean.Json), jsonRank j ≤ n →
      let out := compactOne (treeDoc j)
      !out.isEmpty = true ∧ !out.contains '\n' = true ∧ !out.contains '\r' = true ∧
        out.startsWith "{" = (match j with | .obj _ => true | _ => false) ∧
        (wellFormedJsonBool j = true →
          ∃ tape : RenderTape, isCompactTape tape = true ∧ renderVal j tape = some out) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j hj
    cases j with
    | null =>
      unfold treeDoc compactOne
      exact ⟨not_isEmpty_iff.mpr (by decide), not_contains_char_iff.mpr (by decide),
        not_contains_char_iff.mpr (by decide), startsWith_openBrace_of_toList_cons (c := 'n') (tl := ['u', 'l', 'l']) rfl,
        fun _ => ⟨.null "" "", by simp [isCompactTape], by simp [renderVal, isJsonWs]⟩⟩
    | bool b =>
      cases b <;> unfold treeDoc compactOne
      · exact ⟨not_isEmpty_iff.mpr (by decide), not_contains_char_iff.mpr (by decide),
          not_contains_char_iff.mpr (by decide), startsWith_openBrace_of_toList_cons (c := 'f') (tl := ['a', 'l', 's', 'e']) rfl,
          fun _ => ⟨.bool "" "", by simp [isCompactTape], by simp [renderVal, isJsonWs]⟩⟩
      · exact ⟨not_isEmpty_iff.mpr (by decide), not_contains_char_iff.mpr (by decide),
          not_contains_char_iff.mpr (by decide), startsWith_openBrace_of_toList_cons (c := 't') (tl := ['r', 'u', 'e']) rfl,
          fun _ => ⟨.bool "" "", by simp [isCompactTape], by simp [renderVal, isJsonWs]⟩⟩
    | num x =>
      unfold treeDoc compactOne
      obtain ⟨h1, h2, h3, h4, nt, hRen⟩ := jsonNumberToString_spec x
      exact ⟨h1, h2, h3, h4, fun _ => ⟨.num "" nt "", by simp [isCompactTape], by simp [renderVal, isJsonWs, hRen]⟩⟩
    | str s =>
      unfold treeDoc compactOne
      obtain ⟨h1, h2, h3, h4, styles, hRen⟩ := renderString_spec s
      exact ⟨h1, h2, h3, h4, fun _ => ⟨.str "" styles "", by simp [isCompactTape], by simp [renderVal, isJsonWs, hRen]⟩⟩
    | arr elems =>
      cases hlist : elems.toList with
      | nil =>
        rw [treeDoc_arr_nil hlist]
        dsimp only [compactOne]
        have hemp : elems.isEmpty = true := Array.isEmpty_iff.mpr (Array.ext' hlist)
        exact ⟨not_isEmpty_iff.mpr (by decide), not_contains_char_iff.mpr (by decide),
          not_contains_char_iff.mpr (by decide), startsWith_openBrace_of_toList_cons (c := '[') (tl := [']']) rfl,
          fun _ => ⟨.emptyArr "" "" "", by simp [isCompactTape], by simp [renderVal, hemp, isJsonWs]⟩⟩
      | cons x0 xtl =>
        have hMap : ∀ xs : List Lean.Json, (treeDocList xs).map compactOne = xs.map (fun x => compactOne (treeDoc x)) := by
          intro xs; induction xs with
          | nil => simp [treeDocList]
          | cons u utl ihu => rw [treeDocList]; simp [ihu]
        have htd : compactOne (treeDoc (.arr elems)) =
            "[" ++ String.intercalate "," ((x0 :: xtl).map (fun x => compactOne (treeDoc x))) ++ "]" := by
          rw [treeDoc_arr_cons hlist]
          simp [docBracket, compactOne, compactOne_joinCommaLineFwd, hMap, String.append_assoc]
        rw [htd]
        let mid := String.intercalate "," ((x0 :: xtl).map (fun x => compactOne (treeDoc x)))
        let out := "[" ++ mid ++ "]"
        have houtL : out.toList = '[' :: (mid.toList ++ [']']) := by simp [out, String.toList_append]
        have hRankSub : ∀ x ∈ x0 :: xtl, jsonRank x < n := by
          intro x hx
          have hlt := jsonRank_lt_jsonListRank hx
          simp only [jsonRank, hlist] at hj; omega
        have hNoCrLfMid : !mid.contains '\n' = true ∧ !mid.contains '\r' = true := by
          apply noCrLf_intercalate_comma
          intro p hp; rcases List.mem_map.mp hp with ⟨x, hxIn, rfl⟩
          have hSpec := ih (jsonRank x) (hRankSub x hxIn) x (Nat.le_refl _)
          exact ⟨hSpec.2.1, hSpec.2.2.1⟩
        refine ⟨not_isEmpty_iff.mpr (by rw [houtL]; simp),
          not_contains_of_toList_wrap houtL (by decide) (by decide) (not_contains_char_iff.mp hNoCrLfMid.1),
          not_contains_of_toList_wrap houtL (by decide) (by decide) (not_contains_char_iff.mp hNoCrLfMid.2),
          startsWith_openBrace_of_toList_cons houtL, ?_⟩
        · intro hWfArr
          simp only [wellFormedJsonBool, hlist] at hWfArr
          have hBuild : ∀ xs : List Lean.Json,
              (∀ x ∈ xs, jsonRank x < n) → wellFormedJsonListBool xs = true →
              ∃ ts : List RenderTape, isCompactListTape ts = true ∧
                renderArrElems xs ts = some (xs.map (fun x => compactOne (treeDoc x))) := by
            intro xs hR hW
            induction xs with
            | nil => exact ⟨[], by simp [isCompactListTape], by simp [renderArrElems]⟩
            | cons u utl ihu =>
              simp only [wellFormedJsonListBool, Bool.and_eq_true] at hW
              obtain ⟨tu, hCompU, hRenU⟩ := (ih (jsonRank u) (hR u List.mem_cons_self) u (Nat.le_refl _)).2.2.2.2 hW.1
              obtain ⟨tutl, hCompTl, hRenTl⟩ := ihu (fun y hy => hR y (List.mem_cons_of_mem _ hy)) hW.2
              exact ⟨tu :: tutl, by simp [isCompactListTape, hCompU, hCompTl],
                by simp [renderArrElems, hRenU, hRenTl, bind, Option.bind]⟩
          obtain ⟨ts, hCompTs, hRenTs⟩ := hBuild (x0 :: xtl) hRankSub hWfArr
          have hNotEmp : (!elems.isEmpty) = true := by
            cases he : elems.isEmpty
            · rfl
            · exfalso; have := Array.isEmpty_iff.mp he; subst this; simp at hlist
          exact ⟨.arr "" ts "", by simp [isCompactTape, hCompTs],
            by simp [renderVal, hNotEmp, isJsonWs, hlist, hRenTs, bind, Option.bind]⟩
    | obj kvs =>
      cases hEnt : objEntries kvs with
      | nil =>
        rw [treeDoc_obj_nil hEnt]
        dsimp only [compactOne]
        have hemp : (objEntries kvs).isEmpty = true := by simp [hEnt]
        exact ⟨not_isEmpty_iff.mpr (by decide), not_contains_char_iff.mpr (by decide),
          not_contains_char_iff.mpr (by decide), startsWith_openBrace_of_toList_cons (c := '{') (tl := ['}']) rfl,
          fun _ => ⟨.emptyObj "" "" "", by simp [isCompactTape], by simp [renderVal, hemp, isJsonWs]⟩⟩
      | cons e0 etl =>
        let entries := e0 :: etl
        have hentriesNe : objEntries kvs ≠ [] := by rw [hEnt]; simp
        have hKvComp : ∀ p : String × Lean.Json, compactOne (kvDoc p) = renderString p.1 "" ++ ":" ++ compactOne (treeDoc p.2) := by
          intro ⟨ek, ev⟩; simp [kvDoc, compactOne, String.append_assoc]
        have hMapKv : ∀ es : List (String × Lean.Json),
            (es.map kvDoc).map compactOne = es.map (fun (ek, ev) => renderString ek "" ++ ":" ++ compactOne (treeDoc ev)) := by
          intro es; induction es with
          | nil => rfl
          | cons a atl iha => simp [hKvComp, iha]
        have htd : compactOne (treeDoc (.obj kvs)) =
            "{" ++ String.intercalate "," (entries.map fun (ek, ev) =>
              renderString ek "" ++ ":" ++ compactOne (treeDoc ev)) ++ "}" := by
          rw [treeDoc_obj_cons hEnt]
          dsimp only [docBracket, compactOne]
          rw [compactOne_joinCommaLineFwd, List.map_cons, hKvComp, hMapKv]
          simp [entries, String.append_assoc]
        rw [htd]
        let mid := String.intercalate "," (entries.map fun (ek, ev) =>
          renderString ek "" ++ ":" ++ compactOne (treeDoc ev))
        let out := "{" ++ mid ++ "}"
        have houtL : out.toList = '{' :: (mid.toList ++ ['}']) := by simp [out, String.toList_append]
        have hRankSub : ∀ p ∈ entries, jsonRank p.2 < n := by
          intro ⟨ek, ev⟩ hp
          have hlt := jsonRank_lt_jsonAssocRank hp
          have htr : jsonAssocRank entries = jsonTreeRank kvs.inner.inner := by
            dsimp only [entries]; rw [← hEnt]; exact jsonAssocRank_treeEntries kvs.inner.inner
          simp only [jsonRank] at hj; dsimp only at *; omega
        have hNoCrLfMid : !mid.contains '\n' = true ∧ !mid.contains '\r' = true := by
          apply noCrLf_intercalate_comma
          intro s hs; rcases List.mem_map.mp hs with ⟨⟨ek, ev⟩, hpIn, rfl⟩
          obtain ⟨_, hkN, hkR, _, _⟩ := renderString_spec ek
          have hvSpec := ih (jsonRank ev) (hRankSub (ek, ev) hpIn) ev (Nat.le_refl _)
          have hvN := hvSpec.2.1
          have hvR := hvSpec.2.2.1
          rw [not_contains_char_iff] at hkN hkR hvN hvR
          have hCol : ":".toList = [':'] := rfl
          refine ⟨?_, ?_⟩
          · rw [not_contains_char_iff, String.toList_append, String.toList_append, hCol]
            intro hm
            rcases List.mem_append.mp hm with hm1 | hm2
            · rcases List.mem_append.mp hm1 with h1 | h2
              · exact hkN h1
              · simp only [List.mem_singleton] at h2; cases h2
            · exact hvN hm2
          · rw [not_contains_char_iff, String.toList_append, String.toList_append, hCol]
            intro hm
            rcases List.mem_append.mp hm with hm1 | hm2
            · rcases List.mem_append.mp hm1 with h1 | h2
              · exact hkR h1
              · simp only [List.mem_singleton] at h2; cases h2
            · exact hvR hm2
        refine ⟨not_isEmpty_iff.mpr (by rw [houtL]; simp),
          not_contains_of_toList_wrap houtL (by decide) (by decide) (not_contains_char_iff.mp hNoCrLfMid.1),
          not_contains_of_toList_wrap houtL (by decide) (by decide) (not_contains_char_iff.mp hNoCrLfMid.2),
          startsWith_openBrace_of_toList_cons houtL, ?_⟩
        · intro hWfObj
          simp only [wellFormedJsonBool, Bool.and_eq_true] at hWfObj
          rcases hWfObj with ⟨hSorted, hWfTree⟩
          have hNoDup : noDupKeysBool entries = true := by
            dsimp only [entries]; rw [← hEnt]; exact noDupKeysBool_of_isStrictlySortedKeys hSorted
          have hWfVals : ∀ p ∈ entries, wellFormedJsonBool p.2 = true := by
            dsimp only [entries]; rw [← hEnt]; exact (wellFormedJsonTreeBool_iff_entries kvs.inner.inner).mp hWfTree
          have hBuildObj : ∀ sub : List (String × Lean.Json),
              (∀ p ∈ sub, p ∈ entries) →
              ∃ plan : List (ObjKeyTape × RenderTape),
                plan.map (fun q => q.1.key) = sub.map Prod.fst ∧
                isCompactObjTape plan = true ∧
                renderObjEntries entries plan =
                  some (sub.map fun (ek, ev) => renderString ek "" ++ ":" ++ compactOne (treeDoc ev)) := by
            intro sub hSub
            induction sub with
            | nil => exact ⟨[], rfl, by simp [isCompactObjTape], by simp [renderObjEntries]⟩
            | cons hd tl iht =>
              rcases hd with ⟨ek, ev⟩
              have hpIn := hSub (ek, ev) List.mem_cons_self
              obtain ⟨_, _, _, _, stylesK, hRenK⟩ := renderString_spec ek
              obtain ⟨vt, hCompV, hRenV⟩ :=
                (ih (jsonRank ev) (hRankSub (ek, ev) hpIn) ev (Nat.le_refl _)).2.2.2.2 (hWfVals (ek, ev) hpIn)
              obtain ⟨planTl, hKeysTl, hCompTl, hRenTl⟩ := iht (fun p hp => hSub p (List.mem_cons_of_mem _ hp))
              have hlu : lookupKeyList ek entries = some ev :=
                (lookupKeyList_eq_some_iff_mem hNoDup ek ev).mpr hpIn
              refine ⟨(⟨"", ek, stylesK, ""⟩, vt) :: planTl, by simp [hKeysTl],
                by simp [isCompactObjTape, hCompV, hCompTl], ?_⟩
              simp [renderObjEntries, isJsonWs, hlu, hRenK, hRenV, hRenTl, bind, Option.bind, String.append_assoc]
          obtain ⟨plan, hPlanKeys, hCompPlan, hRenPlan⟩ := hBuildObj entries (fun _ h => h)
          have hPerm : isObjPlanPerm entries plan = true := by
            have hndK := nodup_of_noDupKeysBool hNoDup
            have hndPlanB : noDupStringsBool (plan.map fun q => q.1.key) = true := by
              rw [hPlanKeys]; exact noDupStringsBool_of_nodup hndK
            have hLenEq : plan.length = entries.length := by
              have := congrArg List.length hPlanKeys; simpa using this
            simp only [isObjPlanPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
            refine ⟨⟨⟨hNoDup, hndPlanB⟩, hLenEq⟩, fun p hp => ?_⟩
            rw [hasKeyList_iff_mem, ← hPlanKeys]
            exact List.mem_map_of_mem hp
          exact ⟨.obj "" plan "", by simp [isCompactTape, hCompPlan],
            by simp [renderVal, hEnt, entries, isJsonWs, hPerm, hRenPlan, bind, Option.bind]⟩

/-- `LeanSwe.Json.compress` obeys `Model.allowedCompress` on all `Lean.Json` values. -/
theorem allowedCompress_holds : Core.ObeysPure LeanSwe.Json.compress Model.allowedCompress := by
  intro j
  rw [compress_eq_compactOne]
  obtain ⟨h1, h2, h3, h4, h5⟩ := compactOne_treeDoc_spec (jsonRank j) j (Nat.le_refl _)
  simp only [Model.allowedCompress]
  refine ⟨h1, h2, h3, ?_⟩
  by_cases hwf : wellFormedJsonBool j = true
  · simp only [hwf, ↓reduceIte]
    obtain ⟨tape, hComp, hRen⟩ := h5 hwf
    exact ⟨tape, hComp, by simp [render, hwf, hRen]⟩
  · simp only [hwf, Bool.false_eq_true, ↓reduceIte, h4]; rfl

end LeanSwe.Json.Proofs
