import Lean.Data.Json.Basic
import Core.Obeys
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.ScalarLex
import LeanSweProofs.Json.Proofs.ModelDecode

namespace LeanSwe.Json.Proofs

open LeanSwe.Json.Model

private theorem isAsciiDigit_cases {d : Char} (h : isAsciiDigit d = true) :
    d = '0' ∨ d = '1' ∨ d = '2' ∨ d = '3' ∨ d = '4' ∨
    d = '5' ∨ d = '6' ∨ d = '7' ∨ d = '8' ∨ d = '9' := by
  simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h
  change 48 ≤ d.toNat ∧ d.toNat ≤ 57 at h
  match hn : d.toNat - 48 with
  | 0 => exact Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 48; omega)))
  | 1 => exact Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 49; omega))))
  | 2 => exact Or.inr (Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 50; omega)))))
  | 3 => exact Or.inr (Or.inr (Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 51; omega))))))
  | 4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 52; omega)))))))
  | 5 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 53; omega))))))))
  | 6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 54; omega)))))))))
  | 7 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 55; omega))))))))))
  | 8 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 56; omega)))))))))))
  | 9 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Char.ext (UInt32.toNat_inj.mp (by change d.toNat = 57; omega)))))))))))
  | _ + 10 => omega

mutual
  private theorem decodeModelVal_renderVal :
      ∀ (tape : RenderTape) (j : Lean.Json) {seg : String} (after : List Char) (fuel : Nat),
        renderVal j tape = some seg →
        isDelimOrEof after = true →
        (seg.toList ++ after).length * 2 < fuel →
        ∃ mv, decodeModelVal fuel (seg.toList ++ after) = some (mv, after) ∧ JsonMatchesModel j mv
    | .null wb wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal] at hr
        rcases hr with ⟨⟨hwb, hwa⟩, rfl⟩
        refine ⟨.null, ?_, by simp [JsonMatchesModel]⟩
        unfold decodeModelVal
        simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
        change some (ModelVal.null, dropJsonWs (wa.toList ++ after)) = some (ModelVal.null, after)
        rw [dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
    | .bool wb wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal] at hr
        rename_i b
        rcases hr with ⟨⟨hwb, hwa⟩, rfl⟩
        refine ⟨.bool b, ?_, by simp [JsonMatchesModel]⟩
        unfold decodeModelVal
        cases b <;>
          simp only [↓reduceIte, Bool.false_eq_true, String.toList_append, List.append_assoc,
            dropJsonWs_ws_append hwb]
        · change some (ModelVal.bool false, dropJsonWs (wa.toList ++ after)) = some (ModelVal.bool false, after)
          rw [dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
        · change some (ModelVal.bool true, dropJsonWs (wa.toList ++ after)) = some (ModelVal.bool true, after)
          rw [dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
    | .num wb nt wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal, renderNum] at hr
        rename_i n
        rcases hr with ⟨⟨hwb, hwa⟩, ⟨hvnt, heqv⟩, rfl⟩
        have hStopWa : isNumStop (wa.toList ++ after) = true := by
          cases hwaList : wa.toList with
          | nil =>
            simp only [List.nil_append]
            cases after with
            | nil => rfl
            | cons c _ =>
              simp only [isDelimOrEof, Bool.or_eq_true, beq_iff_eq] at hafter
              rcases hafter with (rfl | rfl) | rfl <;> rfl
          | cons c cs =>
            have hcWs : isJsonWsChar c = true := by
              have hwAll : wa.toList.all isJsonWsChar = true := hwa
              rw [hwaList, List.all_cons, Bool.and_eq_true] at hwAll; exact hwAll.1
            simp only [List.cons_append, isJsonWsChar, Bool.or_eq_true, beq_iff_eq] at hcWs ⊢
            rcases hcWs with ((rfl | rfl) | rfl) | rfl <;> rfl
        obtain ⟨hlex, _⟩ := lexNumberChars_renderNumTape hvnt hStopWa
        refine ⟨.num (evalNumTape nt), ?_, by simp [JsonMatchesModel, (numEquivBool_iff n (evalNumTape nt)).mp heqv]⟩
        unfold decodeModelVal
        simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
        cases hminus : nt.minus with
        | true =>
          have htot : ∃ ntl, (renderNumTape nt).toList ++ (wa.toList ++ after) = '-' :: ntl :=
            ⟨_, by unfold renderNumTape; dsimp only; simp only [hminus, ↓reduceIte,
              show "-".toList = ['-'] from rfl, String.toList_append, List.cons_append,
              List.nil_append, List.append_assoc]; rfl⟩
          obtain ⟨ntl, htotEq⟩ := htot
          rw [htotEq]
          dsimp only [dropJsonWs, isJsonWsChar]
          change (lexNumberChars ('-' :: ntl)).map (fun p => (ModelVal.num (evalNumTape p.1), dropJsonWs p.2)) = _
          rw [← htotEq, hlex]
          simp [Option.map, dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
        | false =>
          obtain ⟨hwNe, hwAll, _⟩ := repr_nat_props nt.whole
          cases hw : nt.whole.repr.toList with
          | nil => exact absurd hw hwNe
          | cons d dtl =>
            rw [hw, List.all_cons, Bool.and_eq_true] at hwAll
            have hdDig : isAsciiDigit d = true := hwAll.1
            have htot : ∃ ntl, (renderNumTape nt).toList ++ (wa.toList ++ after) = d :: ntl :=
              ⟨_, by unfold renderNumTape; dsimp only; simp only [hminus, Bool.false_eq_true,
                ↓reduceIte, String.empty_append, String.toList_append, List.append_assoc,
                List.cons_append, hw]; rfl⟩
            obtain ⟨ntl, htotEq⟩ := htot
            rw [htotEq]
            rcases isAsciiDigit_cases hdDig with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              (change (lexNumberChars (_ :: ntl)).map (fun p => (ModelVal.num (evalNumTape p.1), dropJsonWs p.2)) = _;
               rw [← htotEq, hlex]; simp [Option.map, dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter])
    | .str wb st wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal] at hr
        rename_i s
        rcases hr with ⟨⟨hwb, hwa⟩, lit, hlit, rfl⟩
        simp only [renderStringLiteral, bind, Option.bind] at hlit
        cases hb : renderStringChars s.toList st <;> rw [hb] at hlit <;> simp at hlit
        subst hlit
        refine ⟨.str s, ?_, by simp [JsonMatchesModel]⟩
        unfold decodeModelVal
        simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
        change (lexStringBody ((String.ofList _).toList ++ ('"' :: (wa.toList ++ after)))).map
          (fun p => (ModelVal.str (String.ofList p.1), dropJsonWs p.2)) = some (ModelVal.str s, after)
        rw [String.toList_ofList, lexStringBody_renderStringChars s.toList st hb (wa.toList ++ after)]
        simp [Option.map, String.ofList_toList, dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
    | .emptyArr wb wi wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal] at hr
        simp only [and_assoc] at hr
        rcases hr with ⟨hempty, hwb, hwi, hwa, rfl⟩
        subst hempty
        refine ⟨.arr [], ?_, by simp [JsonMatchesModel, ListMatchesModel]⟩
        unfold decodeModelVal
        simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
        change (match dropJsonWs (wi.toList ++ (']' :: (wa.toList ++ after))) with
          | ']' :: r2 => some (ModelVal.arr [], dropJsonWs r2)
          | _ => _) = some (ModelVal.arr [], after)
        rw [dropJsonWs_ws_append hwi]
        change some (ModelVal.arr [], dropJsonWs (wa.toList ++ after)) = some (ModelVal.arr [], after)
        rw [dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
    | .arr wb ts wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal, bind, Option.bind] at hr
        rename_i elems
        simp only [and_assoc] at hr
        rcases hr with ⟨hne, hwb, hwa, hparts⟩
        cases hp : renderArrElems elems.toList ts with
        | none => rw [hp] at hparts; cases hparts
        | some parts =>
          rw [hp] at hparts; injection hparts with hparts; subst hparts
          cases hlist : elems.toList with
          | nil => exact absurd (Array.ext' hlist) hne
          | cons x0 xrest =>
            rw [hlist] at hp
            cases ts with
            | nil => simp [renderArrElems] at hp
            | cons t0 trest =>
              have hp0 := hp
              simp only [renderArrElems, bind, Option.bind] at hp0
              cases hr0 : renderVal x0 t0 with
              | none => rw [hr0] at hp0; cases hp0
              | some seg0 =>
                cases hrtl : renderArrElems xrest trest with
                | none => rw [hr0, hrtl] at hp0; cases hp0
                | some ptl =>
                  rw [hr0, hrtl] at hp0; injection hp0 with hp0; subst hp0
                  have hFirst : ∃ c tl, dropJsonWs ((String.intercalate "," (seg0 :: ptl)).toList ++
                      (']' :: (wa.toList ++ after))) = c :: tl ∧ c ≠ ']' := by
                    cases ptl with
                    | nil =>
                      rw [String.intercalate_singleton]
                      obtain ⟨c, tl, hd, hc1, _⟩ := first_nonWs_renderVal (']' :: (wa.toList ++ after)) hr0
                      exact ⟨c, tl, hd, hc1⟩
                    | cons s1 srest =>
                      rw [intercalate_comma_cons_cons, List.append_assoc]
                      obtain ⟨c, tl, hd, hc1, _⟩ := first_nonWs_renderVal
                        (',' :: ((String.intercalate "," (s1 :: srest)).toList ++ (']' :: (wa.toList ++ after)))) hr0
                      exact ⟨c, tl, hd, hc1⟩
                  have hLenSub : ((String.intercalate "," (seg0 :: ptl)).toList ++ (']' :: (wa.toList ++ after))).length * 2 + 1 < f := by
                    simp only [String.toList_append, List.length_append, List.length_cons] at hfuel ⊢
                    have : "[".toList.length = 1 := rfl
                    have : "]".toList.length = 1 := rfl
                    omega
                  obtain ⟨mvs, hdecArr, hmatchArr⟩ :=
                    decodeModelArr_renderArrElems (t0 :: trest) (x0 :: xrest) (wa.toList ++ after) f (by simp) hp hLenSub
                  refine ⟨.arr mvs, ?_, by simpa [JsonMatchesModel, hlist] using hmatchArr⟩
                  unfold decodeModelVal
                  simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
                  obtain ⟨c, tl, hd, hcNe⟩ := hFirst
                  change (match dropJsonWs ((String.intercalate "," (seg0 :: ptl)).toList ++ (']' :: (wa.toList ++ after))) with
                    | ']' :: r2 => some (ModelVal.arr [], dropJsonWs r2)
                    | _ => do
                      let (elems, rAfter) ← decodeModelArr f ((String.intercalate "," (seg0 :: ptl)).toList ++ (']' :: (wa.toList ++ after)))
                      some (ModelVal.arr elems, dropJsonWs rAfter)) = some (ModelVal.arr mvs, after)
                  rw [hd]
                  split
                  · rename_i heq; injection heq with h1 _; exact absurd h1 hcNe
                  · simp only [hdecArr, bind, Option.bind, dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
    | .emptyObj wb wi wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal] at hr
        rename_i kvs
        simp only [and_assoc] at hr
        rcases hr with ⟨hnil, hwb, hwi, hwa, rfl⟩
        refine ⟨.obj [], ?_, ?_⟩
        · unfold decodeModelVal
          simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
          change (match dropJsonWs (wi.toList ++ ('}' :: (wa.toList ++ after))) with
            | '}' :: r2 => some (ModelVal.obj [], dropJsonWs r2)
            | _ => _) = some (ModelVal.obj [], after)
          rw [dropJsonWs_ws_append hwi]
          change some (ModelVal.obj [], dropJsonWs (wa.toList ++ after)) = some (ModelVal.obj [], after)
          rw [dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]
        · simp [JsonMatchesModel, ObjMatchesModel, hnil, lookupKeyList, lookupModelKey]
    | .obj wb es wa, j, _, after, fuel, hr, hafter, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        cases j <;> simp [renderVal, bind, Option.bind] at hr
        rename_i kvs
        simp only [and_assoc] at hr
        rcases hr with ⟨hne, hwb, hwa, hperm, hparts⟩
        cases hp : renderObjEntries (objEntries kvs) es with
        | none => rw [hp] at hparts; cases hparts
        | some parts =>
          rw [hp] at hparts; injection hparts with hparts; subst hparts
          cases es with
          | nil =>
            simp only [isObjPlanPerm, Bool.and_eq_true, beq_iff_eq, List.length_nil] at hperm
            have h0 : objEntries kvs = [] := List.length_eq_zero_iff.mp hperm.1.2.symm
            exact absurd h0 hne
          | cons e0 erest =>
            rcases he0 : e0 with ⟨kt0, vt0⟩
            rw [he0] at hp hperm
            have hp0 := hp
            simp only [renderObjEntries, bind, Option.bind] at hp0
            by_cases hwsK : (!isJsonWs kt0.wsBeforeKey || !isJsonWs kt0.wsBeforeColon) = true
            · simp [hwsK] at hp0
            · simp only [hwsK, Bool.false_eq_true, ↓reduceIte] at hp0
              simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hwsK
              cases hlu0 : lookupKeyList kt0.key (objEntries kvs) with
              | none => rw [hlu0] at hp0; cases hp0
              | some v0 =>
                rw [hlu0] at hp0; dsimp only at hp0
                cases hrk0 : renderStringLiteral kt0.key kt0.keyChars with
                | none => rw [hrk0] at hp0; cases hp0
                | some rk0 =>
                  cases hrv0 : renderVal v0 vt0 with
                  | none => rw [hrk0, hrv0] at hp0; cases hp0
                  | some rv0 =>
                    cases hrtl : renderObjEntries (objEntries kvs) erest with
                    | none => rw [hrk0, hrv0, hrtl] at hp0; cases hp0
                    | some ptl =>
                      rw [hrk0, hrv0, hrtl] at hp0; injection hp0 with hp0; subst hp0
                      have hQuote0 : ∃ body0, rk0.toList = '"' :: body0 := by
                        simp only [renderStringLiteral, bind, Option.bind] at hrk0
                        cases hb : renderStringChars kt0.key.toList kt0.keyChars <;> rw [hb] at hrk0 <;> simp at hrk0
                        subst hrk0; exact ⟨_, by simp [String.toList_append, String.toList_ofList, show "\"".toList = ['"'] from rfl]; rfl⟩
                      obtain ⟨body0, hbody0⟩ := hQuote0
                      have hFirst : ∃ tl, dropJsonWs ((String.intercalate ","
                          ((kt0.wsBeforeKey ++ rk0 ++ kt0.wsBeforeColon ++ ":" ++ rv0) :: ptl)).toList ++
                          ('}' :: (wa.toList ++ after))) = '"' :: tl := by
                        cases ptl with
                        | nil =>
                          rw [String.intercalate_singleton]
                          simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwsK.1, hbody0, List.cons_append]
                          exact ⟨_, rfl⟩
                        | cons s1 srest =>
                          rw [intercalate_comma_cons_cons, List.append_assoc]
                          simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwsK.1, hbody0, List.cons_append]
                          exact ⟨_, rfl⟩
                      have hLenSub : ((String.intercalate ","
                          ((kt0.wsBeforeKey ++ rk0 ++ kt0.wsBeforeColon ++ ":" ++ rv0) :: ptl)).toList ++
                          ('}' :: (wa.toList ++ after))).length * 2 + 1 < f := by
                        simp only [String.toList_append, List.length_append, List.length_cons] at hfuel ⊢
                        have : "{".toList.length = 1 := rfl
                        have : "}".toList.length = 1 := rfl
                        omega
                      obtain ⟨ms, hdecObj, hKeysEq, hLookupMatch⟩ :=
                        decodeModelObj_renderObjEntries ((kt0, vt0) :: erest) (objEntries kvs) (wa.toList ++ after) f (by simp) hp hLenSub
                      simp only [isObjPlanPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hperm
                      rcases hperm with ⟨⟨⟨hndE, hndP⟩, hlenEq⟩, hallIn⟩
                      have hMemIff : ∀ q : String, q ∈ ms.map Prod.fst ↔ q ∈ (objEntries kvs).map Prod.fst := by
                        intro q
                        rw [hKeysEq]
                        exact mem_keys_subset_eq (nodup_of_noDupStringsBool hndP) (nodup_of_noDupKeysBool hndE)
                          (by simp only [List.length_map]; exact hlenEq)
                          (fun k hk => by
                            rcases List.mem_map.mp hk with ⟨p, hpIn, rfl⟩
                            exact (hasKeyList_iff_mem p.1.key (objEntries kvs)).mp (hallIn p hpIn)) q
                      have hNodupMs : (ms.map Prod.fst).Nodup := hKeysEq ▸ nodup_of_noDupStringsBool hndP
                      have hObjMatch : ObjMatchesModel (objEntries kvs) ms := by
                        simp only [ObjMatchesModel]
                        refine ⟨fun k => ?_, fun k v mv hkE hkM => ?_⟩
                        · have h1 : lookupKeyList k (objEntries kvs) = none ↔ k ∉ (objEntries kvs).map Prod.fst := by
                            cases hlu : lookupKeyList k (objEntries kvs) with
                            | none =>
                              have hF : hasKeyList k (objEntries kvs) = false := by
                                rw [← lookupKeyList_isSome_iff_hasKeyList, hlu]; rfl
                              exact ⟨fun _ hm => (by rw [(hasKeyList_iff_mem k _).mpr hm] at hF; cases hF), fun _ => rfl⟩
                            | some v =>
                              have hT : hasKeyList k (objEntries kvs) = true := by
                                rw [← lookupKeyList_isSome_iff_hasKeyList, hlu]; rfl
                              exact ⟨fun h => (by cases h), fun hnot => absurd ((hasKeyList_iff_mem k _).mp hT) hnot⟩
                          have h2 : lookupModelKey k ms = none ↔ k ∉ ms.map Prod.fst := by
                            clear hdecObj hKeysEq hLookupMatch hMemIff hNodupMs
                            induction ms with
                            | nil => simp [lookupModelKey]
                            | cons hd tl ih =>
                              rcases hd with ⟨k', _⟩
                              simp only [lookupModelKey, List.map_cons, List.mem_cons]
                              by_cases hk : k = k'
                              · subst hk; simp
                              · have hbeq : (k == k') = false := beq_false_of_ne hk
                                simp only [hbeq, Bool.false_eq_true, ↓reduceIte, not_or]
                                exact ⟨fun h => ⟨hk, ih.mp h⟩, fun h => ih.mpr h.2⟩
                          rw [h1, h2, hMemIff]
                        · exact hLookupMatch hNodupMs k v mv hkE hkM
                      refine ⟨.obj ms, ?_, by simpa [JsonMatchesModel] using hObjMatch⟩
                      unfold decodeModelVal
                      simp only [String.toList_append, List.append_assoc, dropJsonWs_ws_append hwb]
                      obtain ⟨tl, hd⟩ := hFirst
                      let innerCs := (String.intercalate ","
                        ((kt0.wsBeforeKey ++ rk0 ++ kt0.wsBeforeColon ++ ":" ++ rv0) :: ptl)).toList ++
                        ('}' :: (wa.toList ++ after))
                      change (match dropJsonWs innerCs with
                        | '}' :: r2 => some (ModelVal.obj [], dropJsonWs r2)
                        | _ => do
                          let (entries, rAfter) ← decodeModelObj f innerCs
                          some (ModelVal.obj entries, dropJsonWs rAfter)) = some (ModelVal.obj ms, after)
                      dsimp only [innerCs]; rw [hd]
                      simp only [hdecObj, bind, Option.bind, dropJsonWs_ws_append hwa, dropJsonWs_of_delimOrEof hafter]; rfl
  termination_by tape => sizeOf tape * 2 + 1
  decreasing_by all_goals (subst_vars; simp +arith)

  private theorem decodeModelArr_renderArrElems :
      ∀ (ts : List RenderTape) (xs : List Lean.Json) {parts : List String} (afterClose : List Char) (fuel : Nat),
        ts ≠ [] →
        renderArrElems xs ts = some parts →
        ((String.intercalate "," parts).toList ++ (']' :: afterClose)).length * 2 + 1 < fuel →
        ∃ mvs, decodeModelArr fuel ((String.intercalate "," parts).toList ++ (']' :: afterClose)) =
            some (mvs, afterClose) ∧
          ListMatchesModel xs mvs
    | [], _, _, _, _, hne, _, _ => absurd rfl hne
    | [t], [x], _, afterClose, fuel, _, hp, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        simp only [renderArrElems, bind, Option.bind] at hp
        cases hr : renderVal x t with
        | none => rw [hr] at hp; cases hp
        | some seg =>
          rw [hr] at hp
          have hpEq : [seg] = _ := Option.some.inj (by simpa [renderArrElems] using hp)
          subst hpEq
          rw [String.intercalate_singleton] at hfuel ⊢
          obtain ⟨mv, hdec, hm⟩ := decodeModelVal_renderVal t x (']' :: afterClose) f hr rfl (by omega)
          exact ⟨[mv], by rw [decodeModelArr]; simp [hdec, bind, Option.bind], by simp [ListMatchesModel, hm]⟩
    | t :: t2 :: ts, x :: x2 :: xs, _, afterClose, fuel, _, hp, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        rw [renderArrElems] at hp; simp only [bind, Option.bind] at hp
        cases hr : renderVal x t with
        | none => rw [hr] at hp; cases hp
        | some seg =>
          cases hrtl : renderArrElems (x2 :: xs) (t2 :: ts) with
          | none => rw [hr, hrtl] at hp; cases hp
          | some ptl =>
            rw [hr, hrtl] at hp; injection hp with hp; subst hp
            cases ptl with
            | nil =>
              rw [renderArrElems] at hrtl; simp only [bind, Option.bind] at hrtl
              cases hr2 : renderVal x2 t2 <;> rw [hr2] at hrtl <;> try simp at hrtl
              cases hrtl2 : renderArrElems xs ts <;> rw [hrtl2] at hrtl <;> simp at hrtl
            | cons s2 srest =>
              rw [intercalate_comma_cons_cons, List.append_assoc, List.cons_append] at hfuel ⊢
              let rem := (String.intercalate "," (s2 :: srest)).toList ++ (']' :: afterClose)
              have hlen1 : (seg.toList ++ (',' :: rem)).length * 2 < f := by
                dsimp only [rem]; simp only [List.length_append, List.length_cons] at hfuel ⊢; omega
              have hlen2 : rem.length * 2 + 1 < f := by
                dsimp only [rem]; simp only [List.length_append, List.length_cons] at hfuel ⊢; omega
              obtain ⟨mv, hdec1, hm1⟩ := decodeModelVal_renderVal t x (',' :: rem) f hr rfl hlen1
              obtain ⟨mvs, hdec2, hm2⟩ := decodeModelArr_renderArrElems (t2 :: ts) (x2 :: xs) afterClose f (by simp) hrtl hlen2
              refine ⟨mv :: mvs, ?_, by simp [ListMatchesModel, hm1, hm2]⟩
              dsimp only [rem] at hdec1
              rw [decodeModelArr]
              simp only [hdec1, hdec2, bind, Option.bind]
    | [_], [], _, _, _, _, hp, _ => by simp [renderArrElems] at hp
    | [t], x1 :: _ :: _, _, _, _, _, hp, _ => by
      simp only [renderArrElems, bind, Option.bind] at hp; cases hr : renderVal x1 t <;> rw [hr] at hp <;> simp at hp
    | _ :: _ :: _, [], _, _, _, _, hp, _ => by simp [renderArrElems] at hp
    | t1 :: _ :: _, [x1], _, _, _, _, hp, _ => by
      simp only [renderArrElems, bind, Option.bind] at hp; cases hr : renderVal x1 t1 <;> rw [hr] at hp <;> simp at hp
  termination_by ts => sizeOf ts * 2 + 2
  decreasing_by all_goals (subst_vars; simp +arith)

  private theorem decodeModelObj_renderObjEntries :
      ∀ (es : List (ObjKeyTape × RenderTape)) (entries : List (String × Lean.Json))
        {parts : List String} (afterClose : List Char) (fuel : Nat),
        es ≠ [] → renderObjEntries entries es = some parts →
        ((String.intercalate "," parts).toList ++ ('}' :: afterClose)).length * 2 + 1 < fuel →
        ∃ ms, decodeModelObj fuel ((String.intercalate "," parts).toList ++ ('}' :: afterClose)) = some (ms, afterClose) ∧
          ms.map Prod.fst = es.map (fun p => p.1.key) ∧
          ((ms.map Prod.fst).Nodup → ∀ (k : String) (v : Lean.Json) (mv : ModelVal),
            lookupKeyList k entries = some v → lookupModelKey k ms = some mv → JsonMatchesModel v mv)
    | [], _, _, _, _, hne, _, _ => absurd rfl hne
    | [(kt, vt)], entries, _, afterClose, fuel, _, hp, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
        simp only [renderObjEntries, bind, Option.bind] at hp
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
              cases hrv : renderVal v vt with
              | none => rw [hrk, hrv] at hp; cases hp
              | some rv =>
                rw [hrk, hrv] at hp
                have hpEq : [kt.wsBeforeKey ++ rk ++ kt.wsBeforeColon ++ ":" ++ rv] = _ :=
                  Option.some.inj (by simpa [renderObjEntries] using hp)
                subst hpEq
                have hdRk : ∀ tail, dropJsonWs (rk.toList ++ tail) = rk.toList ++ tail := by
                  intro tail; simp only [renderStringLiteral, bind, Option.bind] at hrk
                  cases hb : renderStringChars kt.key.toList kt.keyChars <;> rw [hb] at hrk <;> simp at hrk
                  subst hrk; simp only [String.toList_append, String.toList_ofList, show "\"".toList = ['"'] from rfl, List.cons_append]
                  rfl
                have hdCol : ∀ tail, dropJsonWs (':' :: tail) = ':' :: tail := fun _ => rfl
                rw [String.intercalate_singleton] at hfuel ⊢
                simp only [String.toList_append, List.append_assoc] at hfuel ⊢
                obtain ⟨hlexK, _⟩ := lexStringLit_renderStringLiteral hrk
                  (kt.wsBeforeColon.toList ++ (':' :: (rv.toList ++ ('}' :: afterClose))))
                have hlenVal : (rv.toList ++ ('}' :: afterClose)).length * 2 < f := by
                  simp only [List.length_append, List.length_cons] at hfuel ⊢
                  have : ":".toList.length = 1 := rfl; omega
                obtain ⟨mv, hdecV, hmV⟩ := decodeModelVal_renderVal vt v ('}' :: afterClose) f hrv rfl hlenVal
                refine ⟨[(kt.key, mv)], ?_, rfl, ?_⟩
                · rw [decodeModelObj]
                  simp only [dropJsonWs_ws_append hws.1, hdRk, show ":".toList = [':'] from rfl,
                    List.cons_append, List.nil_append, hlexK, bind, Option.bind,
                    dropJsonWs_ws_append hws.2, hdCol, hdecV]
                · intro _ k v' mv' hkE hkM; simp only [lookupModelKey] at hkM
                  by_cases hk : k == kt.key
                  · simp only [hk, ↓reduceIte, Option.some.injEq] at hkM; subst hkM
                    rw [beq_iff_eq.mp hk, hlu] at hkE; cases hkE; exact hmV
                  · simp [hk] at hkM
    | (kt, vt) :: e2 :: es, entries, _, afterClose, fuel, _, hp, hfuel => by
      cases fuel with
      | zero => omega
      | succ f =>
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
              cases hrv : renderVal v vt with
              | none => rw [hrk, hrv] at hp; cases hp
              | some rv =>
                cases hrtl : renderObjEntries entries (e2 :: es) with
                | none => rw [hrk, hrv, hrtl] at hp; cases hp
                | some ptl =>
                  rw [hrk, hrv, hrtl] at hp; injection hp with hp; subst hp
                  cases ptl with
                  | nil =>
                    rcases e2 with ⟨kt2, vt2⟩
                    rw [renderObjEntries] at hrtl; simp only [bind, Option.bind] at hrtl
                    split at hrtl <;> try simp at hrtl
                    cases hlu2 : lookupKeyList kt2.key entries <;> rw [hlu2] at hrtl <;> try simp at hrtl
                    rename_i v2
                    cases hrk2 : renderStringLiteral kt2.key kt2.keyChars <;> rw [hrk2] at hrtl <;> try simp at hrtl
                    cases hrv2 : renderVal v2 vt2 <;> rw [hrv2] at hrtl <;> try simp at hrtl
                    cases hrtl2 : renderObjEntries entries es <;> rw [hrtl2] at hrtl <;> simp at hrtl
                  | cons s2 srest =>
                    have hdRk : ∀ tail, dropJsonWs (rk.toList ++ tail) = rk.toList ++ tail := by
                      intro tail; simp only [renderStringLiteral, bind, Option.bind] at hrk
                      cases hb : renderStringChars kt.key.toList kt.keyChars <;> rw [hb] at hrk <;> simp at hrk
                      subst hrk; simp only [String.toList_append, String.toList_ofList, show "\"".toList = ['"'] from rfl, List.cons_append]
                      rfl
                    have hdCol : ∀ tail, dropJsonWs (':' :: tail) = ':' :: tail := fun _ => rfl
                    rw [intercalate_comma_cons_cons, List.append_assoc, List.cons_append] at hfuel ⊢
                    let rem := (String.intercalate "," (s2 :: srest)).toList ++ ('}' :: afterClose)
                    simp only [String.toList_append, List.append_assoc] at hfuel ⊢
                    obtain ⟨hlexK, _⟩ := lexStringLit_renderStringLiteral hrk
                      (kt.wsBeforeColon.toList ++ (':' :: (rv.toList ++ (',' :: rem))))
                    have hlenVal : (rv.toList ++ (',' :: rem)).length * 2 < f := by
                      dsimp only [rem]; simp only [List.length_append, List.length_cons] at hfuel ⊢
                      have : ":".toList.length = 1 := rfl; omega
                    have hlenRem : rem.length * 2 + 1 < f := by
                      dsimp only [rem]; simp only [List.length_append, List.length_cons] at hfuel ⊢
                      have : ":".toList.length = 1 := rfl; omega
                    obtain ⟨mv, hdecV, hmV⟩ := decodeModelVal_renderVal vt v (',' :: rem) f hrv rfl hlenVal
                    obtain ⟨ms, hdecRest, hKeysRest, hMatchRest⟩ :=
                      decodeModelObj_renderObjEntries (e2 :: es) entries afterClose f (by simp) hrtl hlenRem
                    refine ⟨(kt.key, mv) :: ms, ?_, by simp [hKeysRest], ?_⟩
                    · dsimp only [rem] at hlexK hdecV
                      rw [decodeModelObj]
                      simp only [dropJsonWs_ws_append hws.1, hdRk, show ":".toList = [':'] from rfl,
                        List.cons_append, List.nil_append, hlexK, bind, Option.bind,
                        dropJsonWs_ws_append hws.2, hdCol, hdecV, hdecRest]
                    · intro hnd k v' mv' hkE hkM; obtain ⟨_, hndTail⟩ := List.nodup_cons.mp hnd
                      simp only [lookupModelKey] at hkM
                      by_cases hk : k == kt.key
                      · simp only [hk, ↓reduceIte, Option.some.injEq] at hkM; subst hkM
                        rw [beq_iff_eq.mp hk, hlu] at hkE; cases hkE; exact hmV
                      · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hkM
                        exact hMatchRest hndTail k v' mv' hkE hkM
  termination_by es => sizeOf es * 2 + 2
  decreasing_by all_goals (subst_vars; simp +arith)
end

/-- Standalone injectivity of `Model.render` up to `JsonEquiv` over pure RFC 8259 syntax. -/
theorem render_injective : Core.RenderInjectiveModulo render JsonEquiv := by
  intro a b t₁ t₂ s ha hb
  simp only [render] at ha hb
  cases hwfa : wellFormedJsonBool a <;> rw [hwfa] at ha <;> simp at ha
  cases hwfb : wellFormedJsonBool b <;> rw [hwfb] at hb <;> simp at hb
  let fuel := (s.toList ++ []).length * 2 + 1
  obtain ⟨m1, hd1, hm1⟩ := decodeModelVal_renderVal t₁ a [] fuel ha rfl (by omega)
  obtain ⟨m2, hd2, hm2⟩ := decodeModelVal_renderVal t₂ b [] fuel hb rfl (by omega)
  simp only [List.append_nil] at hd1 hd2
  rw [hd1] at hd2
  have hmEq : m1 = m2 := congrArg Prod.fst (Option.some.inj hd2)
  subst hmEq
  exact jsonEquiv_of_matches_same (sizeOf m1) m1 a b (Nat.le_refl _) hm1 hm2

end LeanSwe.Json.Proofs
