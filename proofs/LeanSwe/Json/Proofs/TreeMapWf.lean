import Lean.Data.Json.Basic
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import LeanSwe.Json.Model

namespace LeanSwe.Json.Proofs

open LeanSwe.Json.Model

/-- `Std.DTreeMap.Internal.Impl.foldrM` in `Id` consing `(k, v)` prepends `treeEntries t` onto `acc`. -/
private theorem impl_foldrM_cons_eq_treeEntries :
    ∀ (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) (acc : List (String × Lean.Json)),
      Id.run (t.foldrM (m := Id) (fun k v l => pure ((k, v) :: l)) acc) = treeEntries t ++ acc
  | .leaf, acc => rfl
  | .inner _ k v l r, acc => by
    simp only [treeEntries, List.append_assoc, List.cons_append]
    change Id.run (l.foldrM (m := Id) (fun k v l => pure ((k, v) :: l))
      ((k, v) :: Id.run (r.foldrM (m := Id) (fun k v l => pure ((k, v) :: l)) acc))) =
      treeEntries l ++ (k, v) :: (treeEntries r ++ acc)
    rw [impl_foldrM_cons_eq_treeEntries r acc, impl_foldrM_cons_eq_treeEntries l]

/-- `Std.DTreeMap.Internal.Impl.foldr` consing `(k, v)` prepends `treeEntries t` onto `acc`. -/
theorem impl_foldr_cons_eq_treeEntries
    (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) (acc : List (String × Lean.Json)) :
    t.foldr (fun k v l => (k, v) :: l) acc = treeEntries t ++ acc :=
  impl_foldrM_cons_eq_treeEntries t acc

/-- `kvs.toList` equals `objEntries kvs` for every raw JSON object map. -/
theorem toList_eq_objEntries (kvs : Std.TreeMap.Raw String Lean.Json compare) :
    kvs.toList = objEntries kvs := by
  change kvs.inner.inner.foldr (fun k v l => (k, v) :: l) [] = treeEntries kvs.inner.inner
  rw [impl_foldr_cons_eq_treeEntries, List.append_nil]

/-- Equivalence between `isStrictlySortedKeys` and `List.Pairwise (compare ·.1 ·.1 = .lt)`. -/
theorem isStrictlySortedKeys_iff_pairwise (l : List (String × Lean.Json)) :
    isStrictlySortedKeys l = true ↔ l.Pairwise (fun a b => compare a.1 b.1 = .lt) := by
  induction l with
  | nil => simp [isStrictlySortedKeys]
  | cons a tl ih =>
    cases tl with
    | nil => simp [isStrictlySortedKeys]
    | cons b rest =>
      simp only [isStrictlySortedKeys, Bool.and_eq_true, beq_iff_eq, ih, List.pairwise_cons]
      constructor
      · rintro ⟨hab, hbRest⟩
        refine ⟨fun x hx => ?_, hbRest⟩
        rcases List.mem_cons.mp hx with rfl | hxRest
        · exact hab
        · exact Std.TransCmp.lt_trans hab (hbRest.1 x hxRest)
      · rintro ⟨haAll, hbRest⟩
        exact ⟨haAll b List.mem_cons_self, hbRest⟩

/-- Any strictly key-sorted association list is duplicate-free (`noDupKeysBool l = true`). -/
theorem noDupKeysBool_of_isStrictlySortedKeys {l : List (String × Lean.Json)}
    (h : isStrictlySortedKeys l = true) : noDupKeysBool l = true := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    have hpw := (isStrictlySortedKeys_iff_pairwise (a :: tl)).mp h
    obtain ⟨haAll, htlPw⟩ := List.pairwise_cons.mp hpw
    simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ih ((isStrictlySortedKeys_iff_pairwise tl).mpr htlPw)⟩
    apply Bool.eq_false_iff.mpr
    intro hhas
    have hmem : a.1 ∈ tl.map Prod.fst := by
      clear h ih hpw haAll htlPw
      induction tl with
      | nil => cases hhas
      | cons hd rest ihr =>
        simp only [hasKeyList, Bool.or_eq_true, beq_iff_eq, List.map_cons, List.mem_cons] at hhas ⊢
        rcases hhas with heq | hr
        · exact Or.inl heq
        · exact Or.inr (ihr hr)
    rcases List.mem_map.mp hmem with ⟨p, hpIn, hpEq⟩
    have hlt := haAll p hpIn
    rw [hpEq] at hlt
    rw [Std.ReflCmp.compare_self (cmp := compare)] at hlt
    cases hlt

/-- On a duplicate-free association list, `lookupKeyList k l = some v` holds iff `(k, v) ∈ l`. -/
theorem lookupKeyList_eq_some_iff_mem {l : List (String × Lean.Json)}
    (hnd : noDupKeysBool l = true) (k : String) (v : Lean.Json) :
    lookupKeyList k l = some v ↔ (k, v) ∈ l := by
  induction l with
  | nil => simp [lookupKeyList]
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    simp only [lookupKeyList, List.mem_cons]
    by_cases hk : k == k'
    · have hkEq : k = k' := beq_iff_eq.mp hk
      subst hkEq
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
      constructor
      · rintro rfl; exact Or.inl rfl
      · rintro (rfl | hmem)
        · rfl
        · exfalso
          have hhas : hasKeyList k tl = true := by
            clear hnd ih
            induction tl with
            | nil => cases hmem
            | cons x xtl ihx =>
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hm
              · simp [hasKeyList]
              · simp [hasKeyList, ihx hm]
          rw [hhas] at hnd; cases hnd.1
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, ih hnd.2]
      have hne : k ≠ k' := fun heq => hk (beq_iff_eq.mpr heq)
      constructor
      · exact Or.inr
      · rintro (⟨rfl, _⟩ | hm)
        · exact absurd rfl hne
        · exact hm

/-- Every `Std.TreeMap.Raw.WF` JSON object map has strictly sorted keys in `objEntries kvs`. -/
theorem wf_isStrictlySortedKeys {kvs : Std.TreeMap.Raw String Lean.Json compare}
    (hwf : kvs.WF) : isStrictlySortedKeys (objEntries kvs) = true := by
  rw [isStrictlySortedKeys_iff_pairwise, ← toList_eq_objEntries]
  exact Std.TreeMap.Raw.ordered_keys_toList hwf

/-- On any `Std.TreeMap.Raw.WF` JSON object map, `lookupKeyList k (objEntries kvs)` equals `kvs.get? k`. -/
theorem wf_lookupKeyList_eq_get? {kvs : Std.TreeMap.Raw String Lean.Json compare}
    (hwf : kvs.WF) (k : String) :
    lookupKeyList k (objEntries kvs) = kvs.get? k := by
  have hnd := noDupKeysBool_of_isStrictlySortedKeys (wf_isStrictlySortedKeys hwf)
  rw [Std.TreeMap.Raw.get?_eq_getElem?]
  cases hget : kvs[k]? with
  | none =>
    cases hlu : lookupKeyList k (objEntries kvs) with
    | none => rfl
    | some v =>
      have hmem := (lookupKeyList_eq_some_iff_mem hnd k v).mp hlu
      rw [← toList_eq_objEntries, Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some hwf, hget] at hmem
      cases hmem
  | some v =>
    apply (lookupKeyList_eq_some_iff_mem hnd k v).mpr
    rw [← toList_eq_objEntries, Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some hwf]
    exact hget

/-- `wellFormedJsonTreeBool t = true` iff every value in `treeEntries t` satisfies `wellFormedJsonBool`. -/
theorem wellFormedJsonTreeBool_iff_entries (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    wellFormedJsonTreeBool t = true ↔ ∀ p ∈ treeEntries t, wellFormedJsonBool p.2 = true := by
  induction t with
  | leaf => simp [wellFormedJsonTreeBool, treeEntries]
  | inner _ k v l r ihl ihr =>
    simp only [wellFormedJsonTreeBool, treeEntries, Bool.and_eq_true, ihl, ihr, List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨⟨hl, hv⟩, hr⟩ p (hpL | rfl | hpR)
      · exact hl p hpL
      · exact hv
      · exact hr p hpR
    · intro hall
      exact ⟨⟨fun p hp => hall p (Or.inl hp), hall (k, v) (Or.inr (Or.inl rfl))⟩,
        fun p hp => hall p (Or.inr (Or.inr hp))⟩

/-- `wellFormedJsonListBool xs = true` iff every element of `xs` satisfies `wellFormedJsonBool`. -/
theorem wellFormedJsonListBool_iff_forall (xs : List Lean.Json) :
    wellFormedJsonListBool xs = true ↔ ∀ x ∈ xs, wellFormedJsonBool x = true := by
  induction xs with
  | nil => simp [wellFormedJsonListBool]
  | cons x tl ih =>
    simp only [wellFormedJsonListBool, Bool.and_eq_true, ih, List.mem_cons]
    exact ⟨fun ⟨hx, htl⟩ y hy => hy.elim (· ▸ hx) (htl y),
      fun h => ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩⟩

/-- Inserting a `WellFormedJson` value into a `WF` map of `WellFormedJson` values yields a `WF`, `WellFormedJson` object. -/
theorem wf_insert_wellFormed {kvs : Std.TreeMap.Raw String Lean.Json compare}
    (hwf : kvs.WF) (hvals : ∀ p ∈ objEntries kvs, wellFormedJsonBool p.2 = true)
    (k : String) {v : Lean.Json} (hv : wellFormedJsonBool v = true) :
    (kvs.insert k v).WF ∧
      wellFormedJsonBool (.obj (kvs.insert k v)) = true ∧
      ∀ p ∈ objEntries (kvs.insert k v), wellFormedJsonBool p.2 = true := by
  have hwf' : (kvs.insert k v).WF := Std.TreeMap.Raw.WF.insert hwf
  have hvals' : ∀ p ∈ objEntries (kvs.insert k v), wellFormedJsonBool p.2 = true := by
    intro ⟨pk, pv⟩ hp
    rw [← toList_eq_objEntries, Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some hwf',
      Std.TreeMap.Raw.getElem?_insert hwf] at hp
    by_cases hcmp : compare k pk = .eq
    · simp [hcmp] at hp
      subst hp; exact hv
    · simp [hcmp] at hp
      have hmemOld : (pk, pv) ∈ objEntries kvs := by
        rw [← toList_eq_objEntries, Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some hwf]
        exact hp
      exact hvals (pk, pv) hmemOld
  refine ⟨hwf', ?_, hvals'⟩
  simp only [wellFormedJsonBool, Bool.and_eq_true]
  exact ⟨wf_isStrictlySortedKeys hwf', (wellFormedJsonTreeBool_iff_entries _).mpr hvals'⟩

end LeanSwe.Json.Proofs
