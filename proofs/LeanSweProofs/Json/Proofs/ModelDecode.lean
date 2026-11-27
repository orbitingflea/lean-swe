import Lean.Data.Json.Basic
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.ScalarLex

namespace LeanSwe.Json.Proofs

open LeanSwe.Json.Model

/-- Canonical tree AST decoded from pure RFC 8259 character syntax for `render_injective`. -/
inductive ModelVal where
  /-- JSON `null` literal. -/
  | null
  /-- JSON `true` or `false` literal. -/
  | bool (b : Bool)
  /-- JSON numeric value parsed via `evalNumTape`. -/
  | num (n : Lean.JsonNumber)
  /-- JSON string value. -/
  | str (s : String)
  /-- JSON array of `ModelVal` elements. -/
  | arr (elems : List ModelVal)
  /-- JSON object association list of `(key, value)` pairs. -/
  | obj (entries : List (String × ModelVal))

/-- Look up the first occurrence of `k` in a `ModelVal` object association list. -/
def lookupModelKey (k : String) : List (String × ModelVal) → Option ModelVal
  | [] => none
  | (k', v) :: rest => if k == k' then some v else lookupModelKey k rest

/-- Any value found via `lookupModelKey` has strictly smaller `sizeOf` than the association list. -/
theorem lookupModelKey_sizeOf {k : String} {ms : List (String × ModelVal)} {mv : ModelVal}
    (h : lookupModelKey k ms = some mv) : sizeOf mv < sizeOf ms := by
  induction ms with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [lookupModelKey] at h
    split at h
    · cases h; simp +arith
    · exact Nat.lt_trans (ih h) (by simp +arith)

mutual
  /-- Semantic agreement between a `Lean.Json` document and a decoded `ModelVal`. -/
  def JsonMatchesModel : Lean.Json → ModelVal → Prop
    | .null, .null => True
    | .bool b1, .bool b2 => b1 = b2
    | .num n1, .num n2 => numEquiv n1 n2
    | .str s1, .str s2 => s1 = s2
    | .arr xs, .arr ms => ListMatchesModel xs.toList ms
    | .obj kvs, .obj ms => ObjMatchesModel (objEntries kvs) ms
    | _, _ => False
  termination_by _ m => sizeOf m * 2 + 1
  decreasing_by all_goals simp +arith

  /-- Element-wise semantic agreement between `List Lean.Json` and `List ModelVal`. -/
  def ListMatchesModel : List Lean.Json → List ModelVal → Prop
    | [], [] => True
    | x :: xs, m :: ms => JsonMatchesModel x m ∧ ListMatchesModel xs ms
    | _, _ => False
  termination_by _ ms => sizeOf ms * 2 + 2
  decreasing_by all_goals simp +arith

  /-- Lookup-extensional semantic agreement between object association lists. -/
  def ObjMatchesModel (es : List (String × Lean.Json)) (ms : List (String × ModelVal)) : Prop :=
    (∀ k : String, lookupKeyList k es = none ↔ lookupModelKey k ms = none) ∧
    (∀ (k : String) (v : Lean.Json) (mv : ModelVal),
      lookupKeyList k es = some v → (hm : lookupModelKey k ms = some mv) → JsonMatchesModel v mv)
  termination_by sizeOf ms * 2 + 2
  decreasing_by
    have := lookupModelKey_sizeOf hm
    omega
end

/-- Two `Lean.Json` documents matching the same `ModelVal` are `JsonEquiv`. -/
theorem jsonEquiv_of_matches_same :
    ∀ (n : Nat) (m : ModelVal) (a b : Lean.Json),
      sizeOf m ≤ n → JsonMatchesModel a m → JsonMatchesModel b m → JsonEquiv a b := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m a b hm ha hb
    cases m with
    | null => cases a <;> cases b <;> simp [JsonMatchesModel, JsonEquiv] at ha hb ⊢
    | bool bv =>
      cases a <;> cases b <;> simp [JsonMatchesModel, JsonEquiv] at ha hb ⊢
      exact ha.trans hb.symm
    | num nv =>
      cases a <;> cases b <;> simp [JsonMatchesModel, JsonEquiv] at ha hb ⊢
      exact numEquiv_trans ha (numEquiv_symm hb)
    | str sv =>
      cases a <;> cases b <;> simp [JsonMatchesModel, JsonEquiv] at ha hb ⊢
      exact ha.trans hb.symm
    | arr ms =>
      cases a <;> cases b <;> simp [JsonMatchesModel, JsonEquiv] at ha hb ⊢
      rename_i xs ys
      have hlist : ∀ (l : List ModelVal) (as bs : List Lean.Json),
          sizeOf l < sizeOf (ModelVal.arr ms) →
          ListMatchesModel as l → ListMatchesModel bs l → JsonListEquiv as bs := by
        intro l as bs hl has hbs
        induction l generalizing as bs with
        | nil => cases as <;> cases bs <;> simp [ListMatchesModel, JsonListEquiv] at has hbs ⊢
        | cons mv mrest ihl =>
          cases as with
          | nil => simp [ListMatchesModel] at has
          | cons xa xas =>
            cases bs with
            | nil => simp [ListMatchesModel] at hbs
            | cons xb xbs =>
              simp only [ListMatchesModel, JsonListEquiv] at has hbs ⊢
              have hmv : sizeOf mv < sizeOf (mv :: mrest) := by simp +arith
              have hmrest : sizeOf mrest < sizeOf (mv :: mrest) := by simp +arith
              exact ⟨ih (sizeOf mv) (by omega) mv xa xb (Nat.le_refl _) has.1 hbs.1,
                ihl xas xbs (by omega) has.2 hbs.2⟩
      exact hlist ms xs.toList ys.toList (by simp +arith) ha hb
    | obj ms =>
      cases a <;> cases b <;> simp [JsonMatchesModel, JsonEquiv] at ha hb ⊢
      rename_i kvs1 kvs2
      simp only [ObjMatchesModel] at ha hb
      simp only [JsonObjEquivList]
      refine ⟨fun k hk1 => (hb.1 k).mpr ((ha.1 k).mp hk1), fun k v1 hk1 => ?_⟩
      cases hmk : lookupModelKey k ms with
      | none =>
        have h1n := (ha.1 k).mpr hmk
        rw [hk1] at h1n; cases h1n
      | some mv =>
        cases hk2 : lookupKeyList k (objEntries kvs2) with
        | none =>
          have hmn := (hb.1 k).mp hk2
          rw [hmk] at hmn; cases hmn
        | some v2 =>
          have hmv : sizeOf mv < sizeOf ms := lookupModelKey_sizeOf hmk
          have hms : sizeOf ms < sizeOf (ModelVal.obj ms) := by simp +arith
          exact ⟨v2, rfl, ih (sizeOf mv) (by omega) mv v1 v2 (Nat.le_refl _)
            (ha.2 k v1 mv hk1 hmk) (hb.2 k v2 mv hk2 hmk)⟩

mutual
  /-- Fuel-bounded pure character-level RFC 8259 value decoder (free of resource caps). -/
  def decodeModelVal (fuel : Nat) (cs : List Char) : Option (ModelVal × List Char) :=
    match fuel with
    | 0 => none
    | f + 1 =>
      match dropJsonWs cs with
      | 'n' :: 'u' :: 'l' :: 'l' :: r => some (.null, dropJsonWs r)
      | 't' :: 'r' :: 'u' :: 'e' :: r => some (.bool true, dropJsonWs r)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => some (.bool false, dropJsonWs r)
      | '"' :: r => (lexStringBody r).map fun p => (.str (String.ofList p.1), dropJsonWs p.2)
      | '[' :: r =>
        match dropJsonWs r with
        | ']' :: r2 => some (.arr [], dropJsonWs r2)
        | _ => do
          let (elems, rAfter) ← decodeModelArr f r
          some (.arr elems, dropJsonWs rAfter)
      | '{' :: r =>
        match dropJsonWs r with
        | '}' :: r2 => some (.obj [], dropJsonWs r2)
        | _ => do
          let (entries, rAfter) ← decodeModelObj f r
          some (.obj entries, dropJsonWs rAfter)
      | r@('-' :: _) => (lexNumberChars r).map fun p => (.num (evalNumTape p.1), dropJsonWs p.2)
      | r@(c :: _) =>
        if isAsciiDigit c then (lexNumberChars r).map fun p => (.num (evalNumTape p.1), dropJsonWs p.2)
        else none
      | [] => none
  termination_by fuel * 3

  /-- Fuel-bounded pure character-level RFC 8259 non-empty array decoder. -/
  def decodeModelArr (fuel : Nat) (cs : List Char) : Option (List ModelVal × List Char) :=
    match fuel with
    | 0 => none
    | f + 1 => do
      let (v, r) ← decodeModelVal f cs
      match r with
      | ']' :: rNext => some ([v], rNext)
      | ',' :: rNext => do
        let (vs, rEnd) ← decodeModelArr f rNext
        some (v :: vs, rEnd)
      | _ => none
  termination_by fuel * 3 + 1

  /-- Fuel-bounded pure character-level RFC 8259 non-empty object decoder. -/
  def decodeModelObj (fuel : Nat) (cs : List Char) :
      Option (List (String × ModelVal) × List Char) :=
    match fuel with
    | 0 => none
    | f + 1 => do
      let (k, r1) ← lexStringLit (dropJsonWs cs)
      match dropJsonWs r1 with
      | ':' :: r2 => do
        let (v, r3) ← decodeModelVal f r2
        match r3 with
        | '}' :: rNext => some ([(k, v)], rNext)
        | ',' :: rNext => do
          let (rest, rEnd) ← decodeModelObj f rNext
          some ((k, v) :: rest, rEnd)
        | _ => none
      | _ => none
  termination_by fuel * 3 + 2
end

/-- Every rendered JSON value starts (after leading whitespace) with a non-delimiter token character. -/
theorem first_nonWs_renderVal :
    ∀ {j : Lean.Json} {tape : RenderTape} {seg : String} (after : List Char),
      renderVal j tape = some seg →
      ∃ c tl, dropJsonWs (seg.toList ++ after) = c :: tl ∧ c ≠ ']' ∧ c ≠ '}' := by
  intro j tape seg after h
  cases tape with
  | null wb wa =>
    cases j <;> simp [renderVal] at h
    rcases h with ⟨⟨hwb, _⟩, rfl⟩
    simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
    exact ⟨'n', _, rfl, by decide, by decide⟩
  | bool wb wa =>
    cases j <;> simp [renderVal] at h
    rename_i b
    rcases h with ⟨⟨hwb, _⟩, rfl⟩
    cases b <;> simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
    · exact ⟨'f', _, rfl, by decide, by decide⟩
    · exact ⟨'t', _, rfl, by decide, by decide⟩
  | num wb nt wa =>
    cases j <;> simp [renderVal, renderNum] at h
    rcases h with ⟨⟨hwb, _⟩, ⟨_, _⟩, rfl⟩
    simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
    unfold renderNumTape
    simp only [String.toList_append, List.append_assoc]
    cases nt.minus with
    | true => exact ⟨'-', _, rfl, by decide, by decide⟩
    | false =>
      obtain ⟨hwNe, hwAll, _⟩ := repr_nat_props nt.whole
      cases hw : nt.whole.repr.toList with
      | nil => exact absurd hw hwNe
      | cons d dtl =>
        rw [hw] at hwAll
        simp only [List.all_cons, Bool.and_eq_true] at hwAll
        have hnotWs : isJsonWsChar d = false := by
          cases hws : isJsonWsChar d
          · rfl
          · simp only [isJsonWsChar, Bool.or_eq_true, beq_iff_eq] at hws
            rcases hws with ((rfl | rfl) | rfl) | rfl <;> simp [isAsciiDigit] at hwAll
        have hne1 : d ≠ ']' := by rintro rfl; simp [isAsciiDigit] at hwAll
        have hne2 : d ≠ '}' := by rintro rfl; simp [isAsciiDigit] at hwAll
        simp only [Bool.false_eq_true, ↓reduceIte, String.toList_empty, List.nil_append, List.cons_append, dropJsonWs, hnotWs]
        exact ⟨d, _, rfl, hne1, hne2⟩
  | str wb st wa =>
    cases j <;> simp [renderVal] at h
    rename_i s
    rcases h with ⟨⟨hwb, _⟩, lit, hlit, rfl⟩
    simp only [renderStringLiteral, bind, Option.bind] at hlit
    cases hb : renderStringChars s.toList st with
    | none => rw [hb] at hlit; cases hlit
    | some body =>
      rw [hb] at hlit
      injection hlit with hlit
      subst hlit
      simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
      exact ⟨'"', _, rfl, by decide, by decide⟩
  | emptyArr wb wi wa =>
    cases j <;> simp [renderVal] at h
    simp only [and_assoc] at h
    rcases h with ⟨_, hwb, _, _, rfl⟩
    simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
    exact ⟨'[', _, rfl, by decide, by decide⟩
  | arr wb ts wa =>
    cases j <;> simp [renderVal, bind, Option.bind] at h
    rename_i elems
    simp only [and_assoc] at h
    rcases h with ⟨_, hwb, _, hseg⟩
    cases hp : renderArrElems elems.toList ts with
    | none => rw [hp] at hseg; cases hseg
    | some parts =>
      rw [hp] at hseg; injection hseg with hseg; subst hseg
      simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
      exact ⟨'[', _, rfl, by decide, by decide⟩
  | emptyObj wb wi wa =>
    cases j <;> simp [renderVal] at h
    simp only [and_assoc] at h
    rcases h with ⟨_, hwb, _, _, rfl⟩
    simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
    exact ⟨'{', _, rfl, by decide, by decide⟩
  | obj wb es wa =>
    cases j <;> simp [renderVal, bind, Option.bind] at h
    rename_i kvPairs
    simp only [and_assoc] at h
    rcases h with ⟨_, hwb, _, _, hseg⟩
    cases hp : renderObjEntries (objEntries kvPairs) es with
    | none => rw [hp] at hseg; cases hseg
    | some parts =>
      rw [hp] at hseg; injection hseg with hseg; subst hseg
      simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
      exact ⟨'{', _, rfl, by decide, by decide⟩

/-- `hasKeyList k entries = true` iff `k` appears in `entries.map Prod.fst`. -/
theorem hasKeyList_iff_mem (k : String) (entries : List (String × Lean.Json)) :
    hasKeyList k entries = true ↔ k ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [hasKeyList]
  | cons hd tl ih =>
    rcases hd with ⟨k', _⟩
    simp only [hasKeyList, Bool.or_eq_true, beq_iff_eq, List.map_cons, List.mem_cons, ih]

/-- `(lookupKeyList k entries).isSome` equals `hasKeyList k entries`. -/
theorem lookupKeyList_isSome_iff_hasKeyList (k : String) (entries : List (String × Lean.Json)) :
    (lookupKeyList k entries).isSome = hasKeyList k entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    simp only [lookupKeyList, hasKeyList]
    by_cases hk : (k == k') = true
    · simp [hk]
    · simp [hk, ih]

/-- `noDupStringsBool ks = true` implies `ks.Nodup`. -/
theorem nodup_of_noDupStringsBool {ks : List String} (h : noDupStringsBool ks = true) :
    ks.Nodup := by
  induction ks with
  | nil => exact List.nodup_nil
  | cons k tl ih =>
    simp only [noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, ih h.2⟩

/-- `noDupKeysBool entries = true` implies `(entries.map Prod.fst).Nodup`. -/
theorem nodup_of_noDupKeysBool {entries : List (String × Lean.Json)}
    (h : noDupKeysBool entries = true) : (entries.map Prod.fst).Nodup := by
  induction entries with
  | nil => exact List.nodup_nil
  | cons hd tl ih =>
    rcases hd with ⟨k, _⟩
    simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hmem
    rw [(hasKeyList_iff_mem k tl).mpr hmem] at h
    cases h.1

/-- Two duplicate-free lists of equal length where `xs ⊆ ys` have identical membership. -/
theorem mem_keys_subset_eq {xs ys : List String}
    (hndX : xs.Nodup) (hndY : ys.Nodup) (hlen : xs.length = ys.length)
    (hsub : ∀ k ∈ xs, k ∈ ys) (q : String) : q ∈ xs ↔ q ∈ ys := by
  constructor
  · exact fun h => hsub q h
  · intro hqy
    induction xs generalizing ys with
    | nil => cases ys <;> simp at hlen hqy
    | cons x xtl ih =>
      obtain ⟨hxNotX, hndXtl⟩ := List.nodup_cons.mp hndX
      by_cases hqx : q = x
      · exact hqx ▸ List.mem_cons_self
      · have hxInY : x ∈ ys := hsub x List.mem_cons_self
        have hEraseSub : ∀ k ∈ xtl, k ∈ ys.erase x := by
          intro k hk
          have hne : k ≠ x := fun heq => hxNotX (heq ▸ hk)
          exact (List.mem_erase_of_ne hne).mpr (hsub k (List.mem_cons_of_mem x hk))
        have hEraseLen : xtl.length = (ys.erase x).length := by
          rw [List.length_erase_of_mem hxInY]
          simp at hlen; omega
        have hqInErase : q ∈ ys.erase x := (List.mem_erase_of_ne hqx).mpr hqy
        exact List.mem_cons_of_mem x (ih hndXtl (hndY.erase x) hEraseLen hEraseSub hqInErase)

/-- Character-list unfolding step for `String.intercalate ","` on a 2+-element list. -/
theorem intercalate_comma_cons_cons (a b : String) (rest : List String) :
    (String.intercalate "," (a :: b :: rest)).toList =
      a.toList ++ ',' :: (String.intercalate "," (b :: rest)).toList := by
  have hComma : ",".toList = [','] := rfl
  simp [String.intercalate_cons_cons, String.toList_append, hComma]

end LeanSwe.Json.Proofs
