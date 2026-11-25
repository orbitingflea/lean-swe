import Lean.Data.Json.Basic
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import LeanSwe.Json.Interface
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex
import LeanSwe.Json.Proofs.ModelDecode
import LeanSwe.Json.Proofs.TreeMapWf

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- `isJsonWs` is closed under string concatenation. -/
theorem isJsonWs_append {a b : String} (ha : isJsonWs a = true) (hb : isJsonWs b = true) :
    isJsonWs (a ++ b) = true := by
  simp only [isJsonWs, String.toList_append, List.all_append, Bool.and_eq_true]
  exact ⟨ha, hb⟩

/-- Prepend leading JSON whitespace `w` onto the outer `wsBefore` slot of a `RenderTape`. -/
def prependWsBefore (w : String) : RenderTape → RenderTape
  | .null wb wa => .null (w ++ wb) wa
  | .bool wb wa => .bool (w ++ wb) wa
  | .num wb nt wa => .num (w ++ wb) nt wa
  | .str wb st wa => .str (w ++ wb) st wa
  | .emptyArr wb wi wa => .emptyArr (w ++ wb) wi wa
  | .arr wb ts wa => .arr (w ++ wb) ts wa
  | .emptyObj wb wi wa => .emptyObj (w ++ wb) wi wa
  | .obj wb es wa => .obj (w ++ wb) es wa

/-- Append trailing JSON whitespace `w` onto the outer `wsAfter` slot of a `RenderTape`. -/
def appendWsAfter (t : RenderTape) (w : String) : RenderTape :=
  match t with
  | .null wb wa => .null wb (wa ++ w)
  | .bool wb wa => .bool wb (wa ++ w)
  | .num wb nt wa => .num wb nt (wa ++ w)
  | .str wb st wa => .str wb st (wa ++ w)
  | .emptyArr wb wi wa => .emptyArr wb wi (wa ++ w)
  | .arr wb ts wa => .arr wb ts (wa ++ w)
  | .emptyObj wb wi wa => .emptyObj wb wi (wa ++ w)
  | .obj wb es wa => .obj wb es (wa ++ w)

/-- `prependWsBefore` preserves `withinResourceLimitsBool`. -/
theorem withinLimits_prependWsBefore (w : String) (t : RenderTape) :
    withinResourceLimitsBool (prependWsBefore w t) = withinResourceLimitsBool t := by
  cases t <;> simp [withinResourceLimitsBool, prependWsBefore]

/-- `appendWsAfter` preserves `withinResourceLimitsBool`. -/
theorem withinLimits_appendWsAfter (t : RenderTape) (w : String) :
    withinResourceLimitsBool (appendWsAfter t w) = withinResourceLimitsBool t := by
  cases t <;> simp [withinResourceLimitsBool, appendWsAfter]

/-- `prependWsBefore w t` prepends `w` onto the rendered string of `t`. -/
theorem renderVal_prependWsBefore {j : Lean.Json} {t : RenderTape} {s w : String}
    (hr : renderVal j t = some s) (hw : isJsonWs w = true) :
    renderVal j (prependWsBefore w t) = some (w ++ s) := by
  cases t <;> cases j <;> simp only [renderVal, prependWsBefore, bind, Option.bind, Option.map] at hr ⊢ <;> try cases hr
  · split at hr <;> try simp at hr
    rcases hr with rfl; rename_i hc; simp only [Bool.and_eq_true] at hc
    simp [isJsonWs_append hw hc.1, hc.2, String.append_assoc]
  · split at hr <;> try simp at hr
    rcases hr with rfl; rename_i hc; simp only [Bool.and_eq_true] at hc
    simp [isJsonWs_append hw hc.1, hc.2, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb nt wa n hc; simp only [Bool.and_eq_true] at hc
    cases hn : renderNum n nt <;> rw [hn] at hr <;> simp at hr; subst hr
    simp [isJsonWs_append hw hc.1, hc.2, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb st wa strVal hc; simp only [Bool.and_eq_true] at hc
    cases hs : renderStringLiteral strVal st <;> rw [hs] at hr <;> simp at hr; subst hr
    simp [isJsonWs_append hw hc.1, hc.2, String.append_assoc]
  · split at hr <;> try simp at hr
    subst hr; rename_i hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3, h4⟩
    simp [h1, isJsonWs_append hw h2, h3, h4, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb ts wa elems hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3⟩
    cases hp : renderArrElems elems.toList ts <;> rw [hp] at hr <;> simp at hr; subst hr
    simp [h1, isJsonWs_append hw h2, h3, String.append_assoc]
  · split at hr <;> try simp at hr
    subst hr; rename_i hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3, h4⟩
    simp [h1, isJsonWs_append hw h2, h3, h4, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb es wa kvs hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3, h4⟩
    cases hp : renderObjEntries (objEntries kvs) es <;> rw [hp] at hr <;> simp at hr; subst hr
    simp [h1, isJsonWs_append hw h2, h3, h4, String.append_assoc]

/-- `appendWsAfter t w` appends `w` onto the rendered string of `t`. -/
theorem renderVal_appendWsAfter {j : Lean.Json} {t : RenderTape} {s w : String}
    (hr : renderVal j t = some s) (hw : isJsonWs w = true) :
    renderVal j (appendWsAfter t w) = some (s ++ w) := by
  cases t <;> cases j <;> simp only [renderVal, appendWsAfter, bind, Option.bind, Option.map] at hr ⊢ <;> try cases hr
  · split at hr <;> try simp at hr
    subst hr; rename_i hc; simp only [Bool.and_eq_true] at hc
    simp [hc.1, isJsonWs_append hc.2 hw, String.append_assoc]
  · split at hr <;> try simp at hr
    subst hr; rename_i hc; simp only [Bool.and_eq_true] at hc
    simp [hc.1, isJsonWs_append hc.2 hw, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb nt wa n hc; simp only [Bool.and_eq_true] at hc
    cases hn : renderNum n nt <;> rw [hn] at hr <;> simp at hr; subst hr
    simp [hc.1, isJsonWs_append hc.2 hw, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb st wa strVal hc; simp only [Bool.and_eq_true] at hc
    cases hs : renderStringLiteral strVal st <;> rw [hs] at hr <;> simp at hr; subst hr
    simp [hc.1, isJsonWs_append hc.2 hw, String.append_assoc]
  · split at hr <;> try simp at hr
    subst hr; rename_i hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3, h4⟩
    simp [h1, h2, h3, isJsonWs_append h4 hw, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb ts wa elems hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3⟩
    cases hp : renderArrElems elems.toList ts <;> rw [hp] at hr <;> simp at hr; subst hr
    simp [h1, h2, isJsonWs_append h3 hw, String.append_assoc]
  · split at hr <;> try simp at hr
    subst hr; rename_i hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3, h4⟩
    simp [h1, h2, h3, isJsonWs_append h4 hw, String.append_assoc]
  · split at hr <;> try simp at hr
    rename_i wb es wa kvs hc; simp only [Bool.and_eq_true, and_assoc] at hc
    rcases hc with ⟨h1, h2, h3, h4⟩
    cases hp : renderObjEntries (objEntries kvs) es <;> rw [hp] at hr <;> simp at hr; subst hr
    simp [h1, h2, isJsonWs_append h3 hw, h4, String.append_assoc]

/-- `String.intercalate ","` snoc identity for non-empty string lists. -/
theorem intercalate_comma_snoc {parts : List String} (hne : parts ≠ []) (last : String) :
    String.intercalate "," (parts ++ [last]) = String.intercalate "," parts ++ "," ++ last := by
  induction parts with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    cases tl with
    | nil =>
      change String.intercalate "," [a, last] = String.intercalate "," [a] ++ "," ++ last
      rw [String.intercalate_cons_cons, String.intercalate_singleton, String.intercalate_singleton, String.append_assoc]
    | cons b rest =>
      change String.intercalate "," (a :: b :: (rest ++ [last])) = _
      rw [String.intercalate_cons_cons, String.intercalate_cons_cons,
        show b :: (rest ++ [last]) = (b :: rest) ++ [last] from rfl, ih (by simp)]
      simp only [String.append_assoc]

/-- Snoc step for `renderArrElems`. -/
theorem renderArrElems_snoc {xs : List Lean.Json} {ts : List RenderTape} {parts : List String}
    {x : Lean.Json} {t : RenderTape} {s : String}
    (hp : renderArrElems xs ts = some parts) (hx : renderVal x t = some s) :
    renderArrElems (xs ++ [x]) (ts ++ [t]) = some (parts ++ [s]) ∧ parts ++ [s] ≠ [] := by
  refine ⟨?_, by simp⟩
  induction xs generalizing ts parts with
  | nil =>
    cases ts <;> simp [renderArrElems] at hp
    subst hp; simp [renderArrElems, hx, bind, Option.bind]
  | cons a atl ih =>
    cases ts with
    | nil => simp [renderArrElems] at hp
    | cons ta ttl =>
      simp only [renderArrElems, bind, Option.bind] at hp
      cases ha : renderVal a ta <;> rw [ha] at hp <;> simp at hp
      cases htl : renderArrElems atl ttl <;> rw [htl] at hp <;> simp at hp
      subst hp
      simp [renderArrElems, ha, ih htl, bind, Option.bind]

/-- Snoc step for `withinResourceLimitsListBool`. -/
theorem withinLimitsList_snoc {ts : List RenderTape} {t : RenderTape}
    (hts : withinResourceLimitsListBool ts = true) (ht : withinResourceLimitsBool t = true) :
    withinResourceLimitsListBool (ts ++ [t]) = true := by
  induction ts with
  | nil => simp [withinResourceLimitsListBool, ht]
  | cons a tl ih =>
    simp only [withinResourceLimitsListBool, List.cons_append, Bool.and_eq_true] at hts ⊢
    exact ⟨hts.1, ih hts.2⟩

/-- Snoc step for `withinResourceLimitsObjBool`. -/
theorem withinLimitsObj_snoc {es : List (ObjKeyTape × RenderTape)} (kt : ObjKeyTape) {vt : RenderTape}
    (hes : withinResourceLimitsObjBool es = true) (hvt : withinResourceLimitsBool vt = true) :
    withinResourceLimitsObjBool (es ++ [(kt, vt)]) = true := by
  induction es with
  | nil => simp [withinResourceLimitsObjBool, hvt]
  | cons a tl ih =>
    rcases a with ⟨ka, va⟩
    simp only [List.cons_append, withinResourceLimitsObjBool, Bool.and_eq_true] at hes ⊢
    exact ⟨hes.1, ih hes.2⟩

/-- Inserting a fresh key preserves `renderObjEntries` on prior entries and appends the new entry. -/
theorem renderObjEntries_snoc_insert {kvs : Std.TreeMap.Raw String Lean.Json compare}
    (hwf : kvs.WF) {prior : List (ObjKeyTape × RenderTape)} {priorParts : List String}
    (hPrior : renderObjEntries (objEntries kvs) prior = some priorParts)
    {curKt : ObjKeyTape}
    (hFresh : ∀ p ∈ prior, p.1.key ≠ curKt.key)
    {curRk : String} {val : Lean.Json} {vt : RenderTape} {rv : String}
    (hwsK : isJsonWs curKt.wsBeforeKey = true) (hwsC : isJsonWs curKt.wsBeforeColon = true)
    (hrk : renderStringLiteral curKt.key curKt.keyChars = some curRk)
    (hrv : renderVal val vt = some rv) :
    renderObjEntries (objEntries (kvs.insert curKt.key val)) (prior ++ [(curKt, vt)]) =
      some (priorParts ++ [curKt.wsBeforeKey ++ curRk ++ curKt.wsBeforeColon ++ ":" ++ rv]) := by
  have hwf' : (kvs.insert curKt.key val).WF := Std.TreeMap.Raw.WF.insert hwf
  induction prior generalizing priorParts with
  | nil =>
    simp only [renderObjEntries, Option.some.injEq] at hPrior; subst hPrior
    simp only [List.nil_append, renderObjEntries, hwsK, hwsC, Bool.not_true, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte, wf_lookupKeyList_eq_get? hwf',
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_insert_self hwf,
      hrk, hrv, bind, Option.bind]
  | cons hd tl ih =>
    rcases hd with ⟨kt0, vt0⟩
    simp only [renderObjEntries, bind, Option.bind] at hPrior
    by_cases hws0 : (!isJsonWs kt0.wsBeforeKey || !isJsonWs kt0.wsBeforeColon) = true
    · simp [hws0] at hPrior
    · simp only [hws0, Bool.false_eq_true, ↓reduceIte] at hPrior
      cases hlu0 : lookupKeyList kt0.key (objEntries kvs) with
      | none => rw [hlu0] at hPrior; cases hPrior
      | some v0 =>
        rw [hlu0] at hPrior; dsimp only at hPrior
        cases hrk0 : renderStringLiteral kt0.key kt0.keyChars with
        | none => rw [hrk0] at hPrior; cases hPrior
        | some rk0 =>
          cases hrv0 : renderVal v0 vt0 with
          | none => rw [hrk0, hrv0] at hPrior; cases hPrior
          | some rv0 =>
            cases htl : renderObjEntries (objEntries kvs) tl with
            | none => rw [hrk0, hrv0, htl] at hPrior; cases hPrior
            | some ptl =>
              rw [hrk0, hrv0, htl] at hPrior; injection hPrior with hPrior; subst hPrior
              have hne0 : curKt.key ≠ kt0.key := Ne.symm (hFresh (kt0, vt0) List.mem_cons_self)
              have hcmpNe : ¬(compare curKt.key kt0.key = .eq) := by
                rw [Std.LawfulEqCmp.compare_eq_iff_eq]; exact hne0
              have hlu0' : lookupKeyList kt0.key (objEntries (kvs.insert curKt.key val)) = lookupKeyList kt0.key (objEntries kvs) := by
                rw [wf_lookupKeyList_eq_get? hwf', wf_lookupKeyList_eq_get? hwf,
                  Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.get?_eq_getElem?,
                  Std.TreeMap.Raw.getElem?_insert hwf]
                simp [hcmpNe]
              simp only [List.cons_append, renderObjEntries, hws0, Bool.false_eq_true, ↓reduceIte,
                hlu0', hlu0, hrk0, hrv0, ih htl (fun p hp => hFresh p (List.mem_cons_of_mem _ hp)),
                bind, Option.bind]

/-- Two duplicate-free lists of strings with identical membership have equal length. -/
theorem length_eq_of_nodup_mem_iff {xs ys : List String}
    (hndX : xs.Nodup) (hndY : ys.Nodup) (hmem : ∀ q : String, q ∈ xs ↔ q ∈ ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ytl => exfalso; exact List.not_mem_nil ((hmem y).mpr List.mem_cons_self)
  | cons x xtl ih =>
    obtain ⟨hxNot, hndXtl⟩ := List.nodup_cons.mp hndX
    have hxInY : x ∈ ys := (hmem x).mp List.mem_cons_self
    have hMemErase : ∀ q : String, q ∈ xtl ↔ q ∈ ys.erase x := by
      intro q
      by_cases hqx : q = x
      · subst hqx; exact ⟨fun h => absurd h hxNot, fun h => absurd h (hndY.not_mem_erase)⟩
      · rw [List.mem_erase_of_ne hqx, ← hmem q]
        exact ⟨List.mem_cons_of_mem x, fun h => (List.mem_cons.mp h).resolve_left hqx⟩
    have hlenTl := ih hndXtl (hndY.erase x) hMemErase
    have hposY : 1 ≤ ys.length := List.length_pos_of_mem hxInY
    rw [List.length_erase_of_mem hxInY] at hlenTl
    simp; omega

/-- `Nodup` implies `noDupStringsBool = true`. -/
theorem noDupStringsBool_of_nodup {ks : List String} (h : ks.Nodup) :
    noDupStringsBool ks = true := by
  induction ks with
  | nil => rfl
  | cons k tl ih =>
    obtain ⟨hk, htl⟩ := List.nodup_cons.mp h
    simp only [noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    exact ⟨hk, ih htl⟩

/-- Establish `isObjPlanPerm (objEntries kvs) plan = true` from `kvs.WF`, `Nodup`, and membership equivalence. -/
theorem isObjPlanPerm_of_wf_mem {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {plan : List (ObjKeyTape × RenderTape)}
    (hwf : kvs.WF)
    (hndPlan : (plan.map (fun p => p.1.key)).Nodup)
    (hMem : ∀ q : String, kvs.contains q = true ↔ q ∈ plan.map (fun p => p.1.key)) :
    isObjPlanPerm (objEntries kvs) plan = true := by
  have hndEntriesBool := noDupKeysBool_of_isStrictlySortedKeys (wf_isStrictlySortedKeys hwf)
  have hndEntries := nodup_of_noDupKeysBool hndEntriesBool
  have hMemEntries : ∀ q : String, q ∈ plan.map (fun p => p.1.key) ↔ q ∈ (objEntries kvs).map Prod.fst := by
    intro q
    rw [← hMem q, ← hasKeyList_iff_mem]
    rw [← lookupKeyList_isSome_iff_hasKeyList, wf_lookupKeyList_eq_get? hwf,
      Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.isSome_getElem?_eq_contains hwf]
  have hlen : plan.length = (objEntries kvs).length := by
    have := length_eq_of_nodup_mem_iff hndPlan hndEntries hMemEntries
    simpa using this
  simp only [isObjPlanPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨hndEntriesBool, noDupStringsBool_of_nodup hndPlan⟩, hlen⟩, ?_⟩
  intro p hp
  rw [hasKeyList_iff_mem]
  exact (hMemEntries p.1.key).mp (List.mem_map_of_mem hp)

/-- Well-formedness and prefix-rendering witness for a single open `ParseFrame`. -/
def ValidFrame : ParseFrame → String → Prop
  | .arr elems, framePref =>
    if elems.isEmpty then
      ∃ wb wsFirst, isJsonWs wb = true ∧ isJsonWs wsFirst = true ∧
        framePref = wb ++ "[" ++ wsFirst
    else
      ∃ wb ts parts, isJsonWs wb = true ∧
        wellFormedJsonListBool elems.toList = true ∧
        withinResourceLimitsListBool ts = true ∧
        renderArrElems elems.toList ts = some parts ∧
        parts ≠ [] ∧
        framePref = wb ++ "[" ++ String.intercalate "," parts ++ ","
  | .obj kvs key, framePref =>
    ∃ (wb : String) (prior : List (ObjKeyTape × RenderTape)) (priorParts : List String)
      (curKt : ObjKeyTape) (curRk : String),
      kvs.WF ∧
      (∀ p ∈ objEntries kvs, wellFormedJsonBool p.2 = true) ∧
      kvs.contains key = false ∧
      isJsonWs wb = true ∧
      curKt.key = key ∧
      isJsonWs curKt.wsBeforeKey = true ∧
      isJsonWs curKt.wsBeforeColon = true ∧
      renderStringLiteral key curKt.keyChars = some curRk ∧
      (prior.map (fun p => p.1.key)).Nodup ∧
      (∀ q : String, kvs.contains q = true ↔ q ∈ prior.map (fun p => p.1.key)) ∧
      withinResourceLimitsObjBool prior = true ∧
      renderObjEntries (objEntries kvs) prior = some priorParts ∧
      framePref = wb ++ "{" ++
        (match priorParts with | [] => "" | _ => String.intercalate "," priorParts ++ ",") ++
        curKt.wsBeforeKey ++ curRk ++ curKt.wsBeforeColon ++ ":"

/-- Well-formedness and total consumed prefix witness for a stack of open `ParseFrame`s. -/
inductive ValidStack : List ParseFrame → String → Prop where
  /-- Empty frame stack has consumed `""`. -/
  | nil : ValidStack [] ""
  /-- Top frame `f` has consumed `framePref` after outer frames `fs` consumed `outerPref`. -/
  | cons {f : ParseFrame} {fs : List ParseFrame} {outerPref framePref : String} :
      ValidStack fs outerPref → ValidFrame f framePref →
      ValidStack (f :: fs) (outerPref ++ framePref)

/-- Extending a valid array `ParseFrame` with a parsed element `val` and rendered `valStr'`. -/
theorem validFrame_arr_step {elems : Array Lean.Json} {framePref : String}
    {val : Lean.Json} {valTape' : RenderTape} {valStr' : String}
    (hTop : ValidFrame (.arr elems) framePref)
    (hWfVal : wellFormedJsonBool val = true)
    (hLimVal' : withinResourceLimitsBool valTape' = true)
    (hRenVal' : renderVal val valTape' = some valStr') :
    ∃ (wb : String) (ts' : List RenderTape) (parts' : List String),
      isJsonWs wb = true ∧
      !(elems.push val).isEmpty = true ∧
      wellFormedJsonListBool (elems.push val).toList = true ∧
      withinResourceLimitsListBool ts' = true ∧
      renderArrElems (elems.push val).toList ts' = some parts' ∧
      parts' ≠ [] ∧
      framePref ++ valStr' = wb ++ "[" ++ String.intercalate "," parts' := by
  have hPushNotEmp : !(elems.push val).isEmpty = true := by
    cases h : (elems.push val).isEmpty with
    | false => rfl
    | true => exfalso; have := congrArg Array.size (Array.isEmpty_iff.mp h); simp at this
  simp only [ValidFrame] at hTop
  by_cases hEmp : elems.isEmpty = true
  · rw [ite_eq_left hEmp] at hTop
    rcases hTop with ⟨wb, wsFirst, hwb, hwsF, hfpEq⟩
    have hnil : elems.toList = [] := Array.isEmpty_iff.mp hEmp ▸ rfl
    have hRen0 := renderVal_prependWsBefore hRenVal' hwsF
    have hLim0 : withinResourceLimitsBool (prependWsBefore wsFirst valTape') = true := by
      rw [withinLimits_prependWsBefore]; exact hLimVal'
    refine ⟨wb, [prependWsBefore wsFirst valTape'], [wsFirst ++ valStr'], hwb,
      hPushNotEmp,
      by simp [Array.toList_push, hnil, wellFormedJsonListBool, hWfVal],
      by simp [withinResourceLimitsListBool, hLim0],
      by simp [Array.toList_push, hnil, renderArrElems, hRen0, bind, Option.bind],
      by simp, ?_⟩
    rw [String.intercalate_singleton, hfpEq]; simp [String.append_assoc]
  · rw [ite_eq_right hEmp] at hTop
    rcases hTop with ⟨wb, ts, parts, hwb, hWfElems, hLimTs, hRenTs, hPartsNe, hfpEq⟩
    obtain ⟨hRenSnoc, hSnocNe⟩ := renderArrElems_snoc hRenTs hRenVal'
    refine ⟨wb, ts ++ [valTape'], parts ++ [valStr'], hwb,
      hPushNotEmp,
      by
        rw [Array.toList_push, wellFormedJsonListBool_iff_forall]
        rw [wellFormedJsonListBool_iff_forall] at hWfElems
        intro y hy; rcases List.mem_append.mp hy with h1 | h2
        · exact hWfElems y h1
        · simp at h2; subst h2; exact hWfVal,
      withinLimitsList_snoc hLimTs hLimVal',
      by rwa [Array.toList_push],
      hSnocNe, ?_⟩
    rw [intercalate_comma_snoc hPartsNe, hfpEq]; simp [String.append_assoc]

/-- Every error returned by `LeanSwe.Json.parse` has kind `.parseError` and non-empty message. -/
theorem parse_error_kind_and_nonempty {raw : String} {e : JsonError}
    (hp : LeanSwe.Json.parse raw = .error e) :
    e.kind = .parseError ∧ !e.message.isEmpty = true := by
  simp only [LeanSwe.Json.parse, Internal.parse] at hp
  cases hPure : Internal.parsePure raw with
  | ok _ => simp [hPure] at hp
  | error msg =>
    simp only [hPure, Except.error.injEq] at hp
    subst hp
    refine ⟨rfl, ?_⟩
    have hne : Internal.ensureNonEmpty "JSON parse error" msg ≠ "" := by
      unfold Internal.ensureNonEmpty
      by_cases hm : msg == ""
      · simp [hm]
      · simp only [hm]; intro heq; subst heq; exact hm rfl
    cases hEmpty : (Internal.ensureNonEmpty "JSON parse error" msg).isEmpty
    · rfl
    · exact absurd (String.isEmpty_iff.mp hEmpty) hne

end LeanSwe.Json.Proofs
