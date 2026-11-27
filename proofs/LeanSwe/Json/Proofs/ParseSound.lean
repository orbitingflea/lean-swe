import Lean.Data.Json.Basic
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import LeanSwe.Json.Interface
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex
import LeanSwe.Json.Proofs.ModelDecode
import LeanSwe.Json.Proofs.Utf8Ws
import LeanSwe.Json.Proofs.TreeMapWf
import LeanSwe.Json.Proofs.ParseSoundLeaves

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- `JsonListEquiv` distributes over list concatenation. -/
theorem jsonListEquiv_append {a1 b1 a2 b2 : List Lean.Json}
    (h1 : JsonListEquiv a1 b1) (h2 : JsonListEquiv a2 b2) :
    JsonListEquiv (a1 ++ a2) (b1 ++ b2) := by
  induction a1 generalizing b1 with
  | nil => cases b1 <;> simp [JsonListEquiv] at h1 ⊢; exact h2
  | cons x xr ih =>
    cases b1 with
    | nil => simp [JsonListEquiv] at h1
    | cons y yr =>
      simp only [List.cons_append, JsonListEquiv] at h1 ⊢
      exact ⟨h1.1, ih h1.2⟩

/-- `JsonListEquiv` is reflexive on every list of `Lean.Json` values. -/
theorem jsonListEquiv_refl : ∀ (xs : List Lean.Json), JsonListEquiv xs xs
  | [] => by simp [JsonListEquiv]
  | x :: xr => by simp only [JsonListEquiv]; exact ⟨jsonEquiv_refl x, jsonListEquiv_refl xr⟩

private theorem renderArrElems_cons_eq_some {x0 : Lean.Json} {xrest : List Lean.Json}
    {t0 : RenderTape} {trest : List RenderTape} {parts : List String}
    (hp : renderArrElems (x0 :: xrest) (t0 :: trest) = some parts) :
    ∃ seg0 ptl,
      renderVal x0 t0 = some seg0 ∧
      renderArrElems xrest trest = some ptl ∧
      parts = seg0 :: ptl := by
  rw [renderArrElems] at hp; simp only [bind, Option.bind] at hp
  cases hr0 : renderVal x0 t0 with
  | none => rw [hr0] at hp; cases hp
  | some seg0 =>
    rw [hr0] at hp; dsimp only at hp
    cases hrtl : renderArrElems xrest trest with
    | none => rw [hrtl] at hp; cases hp
    | some ptl =>
      rw [hrtl] at hp; injection hp with hp
      exact ⟨seg0, ptl, rfl, rfl, hp.symm⟩

private theorem renderObjEntries_cons_eq_some {entries : List (String × Lean.Json)}
    {kt : ObjKeyTape} {vt : RenderTape} {erest : List (ObjKeyTape × RenderTape)} {parts : List String}
    (hp : renderObjEntries entries ((kt, vt) :: erest) = some parts) :
    ∃ v rk rv ptl,
      isJsonWs kt.wsBeforeKey = true ∧ isJsonWs kt.wsBeforeColon = true ∧
      lookupKeyList kt.key entries = some v ∧
      renderStringLiteral kt.key kt.keyChars = some rk ∧
      renderVal v vt = some rv ∧
      renderObjEntries entries erest = some ptl ∧
      parts = (kt.wsBeforeKey ++ rk ++ kt.wsBeforeColon ++ ":" ++ rv) :: ptl := by
  rw [renderObjEntries] at hp; simp only [bind, Option.bind] at hp
  by_cases hws : (!isJsonWs kt.wsBeforeKey || !isJsonWs kt.wsBeforeColon) = true
  · simp [hws] at hp
  · simp only [hws, Bool.false_eq_true, ↓reduceIte] at hp
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hws
    cases hlu : lookupKeyList kt.key entries with
    | none => rw [hlu] at hp; cases hp
    | some v =>
      rw [hlu] at hp; dsimp only at hp
      cases hrk : renderStringLiteral kt.key kt.keyChars with
      | none => rw [hrk] at hp; cases hp
      | some rk =>
        rw [hrk] at hp; dsimp only at hp
        cases hrv : renderVal v vt with
        | none => rw [hrv] at hp; cases hp
        | some rv =>
          rw [hrv] at hp; dsimp only at hp
          cases hrtl : renderObjEntries entries erest with
          | none => rw [hrtl] at hp; cases hp
          | some ptl =>
            rw [hrtl] at hp; injection hp with hp
            exact ⟨v, rk, rv, ptl, hws.1, hws.2, rfl, rfl, hrv, rfl, hp.symm⟩

private def objTailChars (ptl : List String) (closeTail : List Char) : List Char :=
  match ptl with
  | [] => '}' :: closeTail
  | s1 :: srest => ',' :: ((String.intercalate "," (s1 :: srest)).toList ++ ('}' :: closeTail))

private theorem objMemberIntercalate_toList (kt : ObjKeyTape) (rk rv : String)
    (ptl : List String) (closeTail : List Char) :
    (String.intercalate "," ((kt.wsBeforeKey ++ rk ++ kt.wsBeforeColon ++ ":" ++ rv) :: ptl)).toList ++
      ('}' :: closeTail) =
      kt.wsBeforeKey.toList ++
        (rk.toList ++ (kt.wsBeforeColon.toList ++ (':' :: (rv.toList ++ objTailChars ptl closeTail)))) := by
  have hCol : ":".toList = [':'] := rfl
  cases ptl with
  | nil =>
    rw [String.intercalate_singleton]
    simp [objTailChars, String.toList_append, hCol, List.append_assoc]
  | cons s1 srest =>
    rw [intercalate_comma_cons_cons]
    simp [objTailChars, String.toList_append, hCol, List.append_assoc]

mutual
  /-- Continuation-passing soundness of `parseWantValue` on any resource-bounded `RenderTape`. -/
  theorem parseWantValue_renderVal :
      ∀ (tape : RenderTape) (j : Lean.Json) {seg : String} (after : List Char)
        {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size) (frames : List ParseFrame),
        withinResourceLimitsBool tape = true →
        renderVal j tape = some seg →
        isDelimOrEof after = true →
        ByteSliceAt bytes pos (seg.toList ++ after) →
        ∃ (outVal : Lean.Json) (afterPos : Nat) (hAfterPos : afterPos ≤ bytes.size),
          parseWantValue bytes pos hPos frames = parseAfterValue bytes afterPos hAfterPos frames outVal ∧
          JsonEquiv j outVal ∧
          wellFormedJsonBool outVal = true ∧
          ByteSliceAt bytes afterPos after
    | .null _ _, _, _, after, _, _, hPos, frames, _, hr, hafter, hSlice =>
      parseWantValue_null after hPos frames hr hafter hSlice
    | .bool _ _, _, _, after, _, _, hPos, frames, _, hr, hafter, hSlice =>
      parseWantValue_bool after hPos frames hr hafter hSlice
    | .num _ _ _, _, _, after, _, _, hPos, frames, hLim, hr, hafter, hSlice =>
      parseWantValue_num after hPos frames (by simpa [withinResourceLimitsBool] using hLim) hr hafter hSlice
    | .str _ _ _, _, _, after, _, _, hPos, frames, _, hr, hafter, hSlice =>
      parseWantValue_str after hPos frames hr hafter hSlice
    | .emptyArr _ _ _, _, _, after, _, _, hPos, frames, _, hr, hafter, hSlice =>
      parseWantValue_emptyArr after hPos frames hr hafter hSlice
    | .emptyObj _ _ _, _, _, after, _, _, hPos, frames, _, hr, hafter, hSlice =>
      parseWantValue_emptyObj after hPos frames hr hafter hSlice
    | .arr wb ts wa, j, _, after, bytes, pos, hPos, frames, hLim, hr, hafter, hSlice => by
      cases j <;> simp [renderVal, bind, Option.bind] at hr
      rename_i elems
      simp only [and_assoc] at hr
      rcases hr with ⟨hne, hwb, hwa, hparts⟩
      simp only [withinResourceLimitsBool] at hLim
      cases hp : renderArrElems elems.toList ts with
      | none => simp [hp] at hparts
      | some parts =>
        simp only [hp, Option.some.injEq] at hparts; subst hparts
        cases hlist : elems.toList with
        | nil => exact absurd (Array.ext' hlist) hne
        | cons x0 xrest =>
          rw [hlist] at hp
          cases ts with
          | nil => simp [renderArrElems] at hp
          | cons t0 trest =>
            obtain ⟨seg0, ptl, hr0, _, rfl⟩ := renderArrElems_cons_eq_some hp
            let innerCs := (String.intercalate "," (seg0 :: ptl)).toList ++ (']' :: (wa.toList ++ after))
            have hFirst : ∃ c tl, dropJsonWs innerCs = c :: tl ∧ c ≠ ']' := by
              cases ptl with
              | nil =>
                dsimp [innerCs]; rw [String.intercalate_singleton]
                obtain ⟨c, tl, hd, hc1, _⟩ := first_nonWs_renderVal (']' :: (wa.toList ++ after)) hr0
                exact ⟨c, tl, hd, hc1⟩
              | cons s1 srest =>
                dsimp [innerCs]; rw [intercalate_comma_cons_cons, List.append_assoc]
                obtain ⟨c, tl, hd, hc1, _⟩ := first_nonWs_renderVal
                  (',' :: ((String.intercalate "," (s1 :: srest)).toList ++ (']' :: (wa.toList ++ after)))) hr0
                exact ⟨c, tl, hd, hc1⟩
            obtain ⟨cFirst, tlFirst, hDropFirst, hcNeClose⟩ := hFirst
            simp only [String.toList_append, List.append_assoc] at hSlice
            change ByteSliceAt bytes pos (wb.toList ++ ('[' :: innerCs)) at hSlice
            obtain ⟨hltP, hsP⟩ := skipWsSub_to_nonWs hPos hwb rfl _ hSlice
            rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
            rw [hSub] at hltP hsP; dsimp only at hltP hsP
            obtain ⟨_, hgP, hsInner⟩ := byteSliceAt_ascii_cons hsP (by decide)
            have hSpInner := skipWsSub_spec innerCs hltP hsInner
            rcases hSpEq : splitJsonWs innerCs with ⟨wsIn, restIn⟩
            rcases hSub1 : skipWsSub bytes (p + 1) hltP with ⟨p1, hp1Ge, hp1Le⟩
            rw [hSpEq, hSub1] at hSpInner; dsimp only at hSpInner
            rcases hSpInner with ⟨hp1Eq, _, hrestDrop, hsP1⟩
            rw [hDropFirst] at hrestDrop; subst hrestDrop
            have hltP1 := byteSliceAt_cons_lt_size hsP1
            have hbNot5d : (bytes[p1]'hltP1 == 0x5d) = false := by
              by_cases ha : cFirst.toNat < 0x80
              · obtain ⟨_, hg1, _⟩ := byteSliceAt_ascii_cons hsP1 ha
                rw [hg1]; apply Bool.eq_false_iff.mpr
                rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, UInt32.toNat_toUInt8,
                  Nat.mod_eq_of_lt (by change cFirst.toNat < 256; omega)]
                intro h; exact hcNeClose (Char.ext (UInt32.toNat_inj.mp h))
              · have h128 := byteSliceAt_nonAscii_ge_128 hsP1 (by omega) hltP1
                rw [UInt8.le_iff_toNat_le] at h128
                apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj]
                change (bytes[p1]'hltP1).toNat ≠ 93; change 128 ≤ (bytes[p1]'hltP1).toNat at h128; omega
            have hWantEq : parseWantValue bytes (p + 1) hltP (.arr #[] :: frames) =
                parseWantValue bytes p1 hp1Le (.arr #[] :: frames) := by
              have hnwFirst : isJsonWsChar cFirst = false := by
                have hspP := splitJsonWs_props innerCs; rw [hSpEq] at hspP; exact hspP.2.2.2
              have hspSelf := splitJsonWs_ws_append (ws := []) (rest := cFirst :: tlFirst) rfl hnwFirst
              rw [List.nil_append] at hspSelf
              have hSpecSelf := skipWsSub_spec (cFirst :: tlFirst) hp1Le hsP1
              rw [hspSelf] at hSpecSelf; dsimp only [List.length_nil] at hSpecSelf
              rcases hSpecSelf with ⟨hpSelf, _, _, _⟩
              rw [Nat.add_zero] at hpSelf
              unfold parseWantValue
              rcases hS_a : skipWsSub bytes (p + 1) hltP with ⟨pa, _, _⟩
              rcases hS_b : skipWsSub bytes p1 hp1Le with ⟨pb, _, _⟩
              have hpa : pa = p1 := by
                have h1 := skipWsSub_spec innerCs hltP hsInner
                rw [hSpEq, hS_a] at h1; exact h1.1.trans hp1Eq.symm
              rw [hS_b] at hpSelf; dsimp only at hpSelf; subst hpa; subst hpSelf; rfl
            obtain ⟨outArr, closePos, hClosePos, hArrEq, hListEqv, hWfArr, hsAfterClose⟩ :=
              parseArr_renderArrElems (t0 :: trest) (x0 :: xrest) #[] (wa.toList ++ after)
                hltP frames (by simp) (by simp [wellFormedJsonListBool]) hLim hp hsInner
            obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
              parseAfterValue_ws_prefix hClosePos hwa hafter frames (.arr outArr) hsAfterClose
            refine ⟨.arr outArr, afterPos, hAfterPos, ?_, by simpa [JsonEquiv, hlist] using hListEqv, hWfArr, hAfterSlice⟩
            conv => lhs; unfold parseWantValue
            rw [hSub]; dsimp only
            have hbOpen : ('[').val.toUInt8 = 0x5b := rfl
            simp only [hltP, ↓reduceDIte, hgP, hbOpen, beq_self_eq_true, ↓reduceIte]
            rw [hSub1]; dsimp only
            simp only [hltP1, ↓reduceDIte, hbNot5d, Bool.false_eq_true, ↓reduceIte]
            rw [← hWantEq, hArrEq, hAfterEq]
    | .obj wb es wa, j, _, after, bytes, pos, hPos, frames, hLim, hr, hafter, hSlice => by
      cases j <;> simp [renderVal, bind, Option.bind] at hr
      rename_i kvs
      simp only [and_assoc] at hr
      rcases hr with ⟨hne, hwb, hwa, hperm, hparts⟩
      simp only [withinResourceLimitsBool] at hLim
      cases hp : renderObjEntries (objEntries kvs) es with
      | none => simp [hp] at hparts
      | some parts =>
        simp only [hp, Option.some.injEq] at hparts; subst hparts
        cases es with
        | nil =>
          simp only [isObjPlanPerm, Bool.and_eq_true, beq_iff_eq, List.length_nil] at hperm
          have h0 : objEntries kvs = [] := List.length_eq_zero_iff.mp hperm.1.2.symm
          exact absurd h0 hne
        | cons e0 erest =>
          rcases he0 : e0 with ⟨kt0, vt0⟩
          rw [he0] at hp hperm hLim
          obtain ⟨v0, rk0, rv0, ptl, hwsK0_1, hwsK0_2, hlu0, hrk0, hrv0, hrtl, rfl⟩ :=
            renderObjEntries_cons_eq_some hp
          simp only [String.toList_append, List.append_assoc,
            show "{".toList = ['{'] from rfl, show "}".toList = ['}'] from rfl,
            List.cons_append, List.nil_append] at hSlice
          rw [objMemberIntercalate_toList kt0 rk0 rv0 ptl (wa.toList ++ after)] at hSlice
          obtain ⟨valPos0, hValPos0, hOpenStep, hsVal0⟩ :=
            parseWantValue_obj_open hPos frames hwb kt0 (rv0.toList ++ objTailChars ptl (wa.toList ++ after))
              hwsK0_1 hwsK0_2 hrk0 hSlice
          simp only [isObjPlanPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hperm
          rcases hperm with ⟨⟨⟨hndE, hndP⟩, hlenEq⟩, hallIn⟩
          have hNodupPlan := nodup_of_noDupStringsBool hndP
          rw [withinResourceLimitsObjBool, Bool.and_eq_true] at hLim
          obtain ⟨outKvs, closePos, hClosePos, hObjEq, hWfOut, hWfJsonOut, hsAfterClose, hLookupOut⟩ :=
            parseObj_renderObjEntries erest (objEntries kvs) ∅ kt0 vt0 v0 rv0 ptl
              (wa.toList ++ after) hValPos0 frames Std.TreeMap.Raw.WF.emptyc (fun _ h => nomatch h)
              (fun _ _ => Std.TreeMap.Raw.contains_emptyc) hNodupPlan hLim.1 hLim.2 hlu0 hrv0 hrtl hsVal0
          obtain ⟨afterPos, hAfterPos, hAfterEq, hAfterSlice⟩ :=
            parseAfterValue_ws_prefix hClosePos hwa hafter frames (.obj outKvs) hsAfterClose
          have hMemPlan : ∀ q : String, q ∈ ((kt0, vt0) :: erest).map (fun p => p.1.key) ↔
              q ∈ (objEntries kvs).map Prod.fst :=
            mem_keys_subset_eq hNodupPlan (nodup_of_noDupKeysBool hndE) (by simpa using hlenEq)
              (fun k hk => by
                rcases List.mem_map.mp hk with ⟨p, hpIn, rfl⟩
                exact (hasKeyList_iff_mem p.1.key (objEntries kvs)).mp (hallIn p hpIn))
          have hObjEquiv : JsonObjEquivList (objEntries kvs) (objEntries outKvs) := by
            simp only [JsonObjEquivList]
            refine ⟨fun q hqNone => ?_, fun q v1 hqSome => ?_⟩
            · rw [wf_lookupKeyList_eq_get? hWfOut]
              have hqNotInE : q ∉ (objEntries kvs).map Prod.fst := by
                intro hm
                have hhs := (hasKeyList_iff_mem q (objEntries kvs)).mpr hm
                rw [← lookupKeyList_isSome_iff_hasKeyList, hqNone] at hhs; cases hhs
              have hqNotPlan : q ∉ ((kt0, vt0) :: erest).map (fun p => p.1.key) :=
                fun hm => hqNotInE ((hMemPlan q).mp hm)
              have hSpec := hLookupOut q
              rw [ite_eq_right hqNotPlan] at hSpec
              rw [hSpec, Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_emptyc]
            · rw [wf_lookupKeyList_eq_get? hWfOut]
              have hqInE : q ∈ (objEntries kvs).map Prod.fst := by
                apply (hasKeyList_iff_mem q (objEntries kvs)).mp
                rw [← lookupKeyList_isSome_iff_hasKeyList, hqSome]; rfl
              have hqInPlan : q ∈ ((kt0, vt0) :: erest).map (fun p => p.1.key) := (hMemPlan q).mpr hqInE
              have hSpec := hLookupOut q
              rw [ite_eq_left hqInPlan] at hSpec
              obtain ⟨vOrig, vOut, hOrig, hOutGet, hEqv⟩ := hSpec
              rw [hqSome] at hOrig; injection hOrig with hvEq; subst hvEq
              exact ⟨vOut, hOutGet, hEqv⟩
          refine ⟨.obj outKvs, afterPos, hAfterPos, ?_, by simpa [JsonEquiv] using hObjEquiv, hWfJsonOut, hAfterSlice⟩
          rw [hOpenStep, hObjEq, hAfterEq]
  termination_by tape => sizeOf tape * 2 + 1
  decreasing_by all_goals (subst_vars; simp +arith)

  /-- Continuation soundness across non-empty array element lists. -/
  theorem parseArr_renderArrElems :
      ∀ (ts : List RenderTape) (xs : List Lean.Json) (acc : Array Lean.Json)
        {parts : List String} (afterClose : List Char) {bytes : ByteArray} {pos : Nat}
        (hPos : pos ≤ bytes.size) (frames : List ParseFrame),
        ts ≠ [] →
        wellFormedJsonListBool acc.toList = true →
        withinResourceLimitsListBool ts = true →
        renderArrElems xs ts = some parts →
        ByteSliceAt bytes pos ((String.intercalate "," parts).toList ++ (']' :: afterClose)) →
        ∃ (outArr : Array Lean.Json) (closePos : Nat) (hClosePos : closePos ≤ bytes.size),
          parseWantValue bytes pos hPos (.arr acc :: frames) =
            parseAfterValue bytes closePos hClosePos frames (.arr outArr) ∧
          JsonListEquiv (acc.toList ++ xs) outArr.toList ∧
          wellFormedJsonBool (.arr outArr) = true ∧
          ByteSliceAt bytes closePos afterClose
    | [], _, _, _, _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
    | [t], [x], acc, _, afterClose, bytes, pos, hPos, frames, _, hWfAcc, hLim, hp, hSlice => by
      simp only [renderArrElems, bind, Option.bind] at hp
      simp only [withinResourceLimitsListBool, Bool.and_true] at hLim
      cases hr : renderVal x t with
      | none => rw [hr] at hp; cases hp
      | some seg =>
        rw [hr] at hp; injection hp with hp; subst hp
        rw [String.intercalate_singleton] at hSlice
        obtain ⟨outX, p1, hp1, hWant1, hEqvX, hWfX, hs1⟩ :=
          parseWantValue_renderVal t x (']' :: afterClose) hPos (.arr acc :: frames) hLim hr rfl hSlice
        obtain ⟨hLt1, hCloseStep, hsAfter⟩ := parseAfterValue_arr_close hp1 acc frames outX afterClose hs1
        have hWfOut : wellFormedJsonBool (.arr (acc.push outX)) = true := by
          simp only [wellFormedJsonBool, Array.toList_push]
          rw [wellFormedJsonListBool_iff_forall] at hWfAcc ⊢
          intro y hy
          rcases List.mem_append.mp hy with hyAcc | hyOut
          · exact hWfAcc y hyAcc
          · simp only [List.mem_singleton] at hyOut; subst hyOut; exact hWfX
        refine ⟨acc.push outX, p1 + 1, hLt1, ?_, ?_, hWfOut, hsAfter⟩
        · rw [hWant1, hCloseStep]
        · rw [Array.toList_push]
          exact jsonListEquiv_append (jsonListEquiv_refl acc.toList) (by simp [JsonListEquiv, hEqvX])
    | t :: t2 :: ts, x :: x2 :: xs, acc, _, afterClose, bytes, pos, hPos, frames, _, hWfAcc, hLim, hp, hSlice => by
      rw [withinResourceLimitsListBool, Bool.and_eq_true] at hLim
      obtain ⟨seg, ptl, hr, hrtl, rfl⟩ := renderArrElems_cons_eq_some hp
      cases ptl with
      | nil =>
        rw [renderArrElems] at hrtl; simp only [bind, Option.bind] at hrtl
        cases hr2 : renderVal x2 t2 <;> rw [hr2] at hrtl <;> try simp at hrtl
        cases hrtl2 : renderArrElems xs ts <;> rw [hrtl2] at hrtl <;> simp at hrtl
      | cons s2 srest =>
        rw [intercalate_comma_cons_cons, List.append_assoc] at hSlice
        let rem := (String.intercalate "," (s2 :: srest)).toList ++ (']' :: afterClose)
        obtain ⟨outX, p1, hp1, hWant1, hEqvX, hWfX, hs1⟩ :=
          parseWantValue_renderVal t x (',' :: rem) hPos (.arr acc :: frames) hLim.1 hr rfl hSlice
        obtain ⟨hLt1, hCommaStep, hsRem⟩ := parseAfterValue_arr_comma hp1 acc frames outX rem hs1
        have hWfPush : wellFormedJsonListBool (acc.push outX).toList = true := by
          rw [Array.toList_push, wellFormedJsonListBool_iff_forall]
          rw [wellFormedJsonListBool_iff_forall] at hWfAcc
          intro y hy
          rcases List.mem_append.mp hy with hyAcc | hyOut
          · exact hWfAcc y hyAcc
          · simp only [List.mem_singleton] at hyOut; subst hyOut; exact hWfX
        obtain ⟨outArr, closePos, hClosePos, hRestEq, hListEqv, hWfArr, hsAfter⟩ :=
          parseArr_renderArrElems (t2 :: ts) (x2 :: xs) (acc.push outX) afterClose
            hLt1 frames (by simp) hWfPush hLim.2 hrtl hsRem
        refine ⟨outArr, closePos, hClosePos, ?_, ?_, hWfArr, hsAfter⟩
        · rw [hWant1, hCommaStep]; exact hRestEq
        · rw [Array.toList_push, List.append_assoc, List.singleton_append] at hListEqv
          have hSelf : JsonListEquiv (acc.toList ++ x :: x2 :: xs) (acc.toList ++ outX :: x2 :: xs) :=
            jsonListEquiv_append (jsonListEquiv_refl acc.toList)
              (by rw [JsonListEquiv]; exact ⟨hEqvX, jsonListEquiv_refl (x2 :: xs)⟩)
          have hTrans : ∀ (l1 l2 l3 : List Lean.Json), JsonListEquiv l1 l2 → JsonListEquiv l2 l3 → JsonListEquiv l1 l3 := by
            intro l1 l2 l3 h12 h23
            have hArr : JsonEquiv (.arr l1.toArray) (.arr l3.toArray) :=
              jsonEquiv_trans (b := .arr l2.toArray) (by simpa [JsonEquiv] using h12) (by simpa [JsonEquiv] using h23)
            simpa [JsonEquiv] using hArr
          exact hTrans _ _ _ hSelf hListEqv
    | [_], [], _, _, _, _, _, _, _, _, _, _, hp, _ => by simp [renderArrElems] at hp
    | [t], x :: _ :: _, _, _, _, _, _, _, _, _, _, _, hp, _ => by
      rw [renderArrElems] at hp; simp only [bind, Option.bind] at hp
      cases hr : renderVal x t <;> rw [hr] at hp <;> simp [renderArrElems] at hp
    | _ :: _ :: _, [], _, _, _, _, _, _, _, _, _, _, hp, _ => by simp [renderArrElems] at hp
    | t :: _ :: _, [x], _, _, _, _, _, _, _, _, _, _, hp, _ => by
      rw [renderArrElems] at hp; simp only [bind, Option.bind] at hp
      cases hr : renderVal x t <;> rw [hr] at hp <;> simp [renderArrElems] at hp
  termination_by ts => sizeOf ts * 2 + 2
  decreasing_by all_goals (subst_vars; simp +arith)

  /-- Continuation soundness across remaining object member tapes. -/
  theorem parseObj_renderObjEntries :
      ∀ (erest : List (ObjKeyTape × RenderTape)) (entries : List (String × Lean.Json))
        (accKvs : Std.TreeMap.Raw String Lean.Json compare)
        (kt : ObjKeyTape) (vt : RenderTape) (v : Lean.Json) (rv : String) (ptl : List String)
        (afterClose : List Char) {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size)
        (frames : List ParseFrame),
        accKvs.WF →
        (∀ p ∈ objEntries accKvs, wellFormedJsonBool p.2 = true) →
        (∀ p ∈ (kt, vt) :: erest, accKvs.contains p.1.key = false) →
        (((kt, vt) :: erest).map (fun p => p.1.key)).Nodup →
        withinResourceLimitsBool vt = true →
        withinResourceLimitsObjBool erest = true →
        lookupKeyList kt.key entries = some v →
        renderVal v vt = some rv →
        renderObjEntries entries erest = some ptl →
        ByteSliceAt bytes pos (rv.toList ++ objTailChars ptl afterClose) →
        ∃ (outKvs : Std.TreeMap.Raw String Lean.Json compare) (closePos : Nat) (hClosePos : closePos ≤ bytes.size),
          parseWantValue bytes pos hPos (.obj accKvs kt.key :: frames) =
            parseAfterValue bytes closePos hClosePos frames (.obj outKvs) ∧
          outKvs.WF ∧
          wellFormedJsonBool (.obj outKvs) = true ∧
          ByteSliceAt bytes closePos afterClose ∧
          (∀ q : String,
            if q ∈ ((kt, vt) :: erest).map (fun p => p.1.key) then
              ∃ vOrig vOut, lookupKeyList q entries = some vOrig ∧ outKvs.get? q = some vOut ∧ JsonEquiv vOrig vOut
            else
              outKvs.get? q = accKvs.get? q)
    | [], entries, accKvs, kt, vt, v, rv, ptl, afterClose, bytes, pos, hPos, frames,
      hwfAcc, hvalsAcc, _, _, hLimV, _, hlu, hrv, hrtl, hSlice => by
      simp only [renderObjEntries, Option.some.injEq] at hrtl; subst hrtl
      dsimp only [objTailChars] at hSlice
      obtain ⟨outV, p1, hp1, hWant1, hEqvV, hWfV, hs1⟩ :=
        parseWantValue_renderVal vt v ('}' :: afterClose) hPos (.obj accKvs kt.key :: frames) hLimV hrv rfl hSlice
      obtain ⟨hLt1, hCloseStep, hsAfter⟩ := parseAfterValue_obj_close hp1 accKvs kt.key frames outV afterClose hs1
      obtain ⟨hwfOut, hWfObjOut, _⟩ := wf_insert_wellFormed hwfAcc hvalsAcc kt.key hWfV
      refine ⟨accKvs.insert kt.key outV, p1 + 1, hLt1, ?_, hwfOut, hWfObjOut, hsAfter, ?_⟩
      · rw [hWant1, hCloseStep]
      · intro q
        simp only [List.map_cons, List.map_nil, List.mem_singleton]
        by_cases hq : q = kt.key
        · subst hq
          simp only [↓reduceIte, Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_insert_self hwfAcc]
          exact ⟨v, outV, hlu, rfl, hEqvV⟩
        · simp only [hq, ↓reduceIte, Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_insert hwfAcc]
          have hcmp : ¬(compare kt.key q = .eq) := by
            rw [Std.LawfulEqCmp.compare_eq_iff_eq]; exact Ne.symm hq
          simp [hcmp]
    | (kt1, vt1) :: etl, entries, accKvs, kt, vt, v, rv, ptl, afterClose, bytes, pos, hPos, frames,
      hwfAcc, hvalsAcc, hDisj, hNodup, hLimV, hLimRest, hlu, hrv, hrtl, hSlice => by
      obtain ⟨v1, rk1, rv1, ptl2, hwsK1_1, hwsK1_2, hlu1, hrk1, hrv1, hrtl2, rfl⟩ :=
        renderObjEntries_cons_eq_some hrtl
      dsimp only [objTailChars] at hSlice
      let remAfterComma := (String.intercalate ","
        ((kt1.wsBeforeKey ++ rk1 ++ kt1.wsBeforeColon ++ ":" ++ rv1) :: ptl2)).toList ++ ('}' :: afterClose)
      obtain ⟨outV, p1, hp1, hWant1, hEqvV, hWfV, hs1⟩ :=
        parseWantValue_renderVal vt v (',' :: remAfterComma) hPos (.obj accKvs kt.key :: frames) hLimV hrv rfl hSlice
      obtain ⟨hwfMid, _, hvalsMid⟩ := wf_insert_wellFormed hwfAcc hvalsAcc kt.key hWfV
      obtain ⟨hktNotInTail, hNodupTail⟩ := List.nodup_cons.mp hNodup
      have hDisjMid : ∀ p ∈ (kt1, vt1) :: etl, (accKvs.insert kt.key outV).contains p.1.key = false := by
        intro p hpIn
        rw [Std.TreeMap.Raw.contains_insert hwfAcc]
        have hne : kt.key ≠ p.1.key := by
          intro heq
          have hm : p.1.key ∈ ((kt1, vt1) :: etl).map (fun q => q.1.key) := List.mem_map_of_mem hpIn
          rw [← heq] at hm
          exact hktNotInTail hm
        have hcmp : (compare kt.key p.1.key == .eq) = false := by
          apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, Std.LawfulEqCmp.compare_eq_iff_eq]; exact hne
        simp [hcmp, hDisj p (List.mem_cons_of_mem _ hpIn)]
      have hRemSplit : (',' :: remAfterComma) =
          ',' :: (kt1.wsBeforeKey.toList ++ (rk1.toList ++ (kt1.wsBeforeColon.toList ++
            (':' :: (rv1.toList ++ objTailChars ptl2 afterClose))))) := by
        dsimp only [remAfterComma]
        rw [objMemberIntercalate_toList kt1 rk1 rv1 ptl2 afterClose]
      rw [hRemSplit] at hs1
      obtain ⟨valPos1, hValPos1, hCommaStep, hsVal1⟩ :=
        parseAfterValue_obj_comma hp1 accKvs kt.key frames outV kt1 (rv1.toList ++ objTailChars ptl2 afterClose)
          hwsK1_1 hwsK1_2 hrk1 (hDisjMid (kt1, vt1) List.mem_cons_self) hs1
      rw [withinResourceLimitsObjBool, Bool.and_eq_true] at hLimRest
      obtain ⟨outKvs, closePos, hClosePos, hRestEq, hwfOut, hWfObjOut, hsAfter, hLookupRest⟩ :=
        parseObj_renderObjEntries etl entries (accKvs.insert kt.key outV) kt1 vt1 v1 rv1 ptl2
          afterClose hValPos1 frames hwfMid hvalsMid hDisjMid hNodupTail hLimRest.1 hLimRest.2 hlu1 hrv1 hrtl2 hsVal1
      refine ⟨outKvs, closePos, hClosePos, ?_, hwfOut, hWfObjOut, hsAfter, ?_⟩
      · rw [hWant1, hCommaStep, hRestEq]
      · intro q
        have hSpec := hLookupRest q
        by_cases hqTail : q ∈ ((kt1, vt1) :: etl).map (fun p => p.1.key)
        · rw [ite_eq_left hqTail] at hSpec
          have hqAll : q ∈ ((kt, vt) :: (kt1, vt1) :: etl).map (fun p => p.1.key) := List.mem_cons_of_mem _ hqTail
          rw [ite_eq_left hqAll]; exact hSpec
        · rw [ite_eq_right hqTail] at hSpec
          by_cases hqHead : q = kt.key
          · subst hqHead
            have hqAll : kt.key ∈ ((kt, vt) :: (kt1, vt1) :: etl).map (fun p => p.1.key) := List.mem_cons_self
            rw [ite_eq_left hqAll, hSpec, Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.getElem?_insert_self hwfAcc]
            exact ⟨v, outV, hlu, rfl, hEqvV⟩
          · have hqNotAll : q ∉ ((kt, vt) :: (kt1, vt1) :: etl).map (fun p => p.1.key) := by
              intro hm; rcases List.mem_cons.mp hm with h1 | h2; exact hqHead h1; exact hqTail h2
            rw [ite_eq_right hqNotAll, hSpec, Std.TreeMap.Raw.get?_eq_getElem?, Std.TreeMap.Raw.get?_eq_getElem?,
              Std.TreeMap.Raw.getElem?_insert hwfAcc]
            have hcmp : ¬(compare kt.key q = .eq) := by
              rw [Std.LawfulEqCmp.compare_eq_iff_eq]; exact Ne.symm hqHead
            simp [hcmp]
  termination_by erest _ _ _ vt => (sizeOf vt + sizeOf erest) * 2 + 2
  decreasing_by all_goals (subst_vars; simp +arith)
end

/-- Round-trip soundness of `Model.render` into `LeanSwe.Json.parse` under `withinResourceLimits`. -/
theorem render_parse_roundTrip {doc : Lean.Json} {tape : RenderTape} {raw : String}
    (hLim : withinResourceLimits tape) (hRender : render doc tape = some raw) :
    ∃ out : Lean.Json,
      LeanSwe.Json.parse raw = .ok out ∧ WellFormedJson out ∧ JsonEquiv doc out := by
  simp only [render] at hRender
  cases hwfDoc : wellFormedJsonBool doc <;> rw [hwfDoc] at hRender <;> simp at hRender
  have hSlice0 : ByteSliceAt raw.toUTF8 0 (raw.toList ++ []) := by
    simpa using byteSliceAt_toUTF8_zero raw
  obtain ⟨out, afterPos, hAfterPos, hWant, hEqv, hWfOut, hsEnd⟩ :=
    parseWantValue_renderVal tape doc [] (Nat.zero_le _) [] hLim hRender rfl hSlice0
  have hEof := parseAfterValue_nil_eof hAfterPos out hsEnd
  refine ⟨out, ?_, hWfOut, hEqv⟩
  simp only [LeanSwe.Json.parse, Internal.parse, Internal.parsePure]
  rw [hWant, hEof]

end LeanSwe.Json.Proofs
