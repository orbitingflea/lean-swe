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
import LeanSweProofs.Json.Proofs.FormatCompress
import LeanSweProofs.Json.Proofs.FormatPrettyFlat

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Every `.line` break string emitted by `formatDocLoop` satisfies `isJsonWs`. -/
theorem isJsonWs_line_emit (fl : Bool) (ind : Nat) :
    isJsonWs (if fl then " " else String.ofList ('\n' :: List.replicate ind ' ')) = true := by
  cases fl with
  | true => simp only [↓reduceIte]; rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, isJsonWs, String.toList_ofList,
      List.all_cons, (by decide : isJsonWsChar '\n' = true), Bool.true_and]
    rw [List.all_eq_true]; intro c hc; rw [List.eq_of_mem_replicate hc]; decide

/-- Continuation soundness of `formatDocLoop` on `treeDoc j`, producing a valid `RenderTape`. -/
theorem formatDocLoop_treeDoc_renderVal :
    ∀ (n : Nat) (j : Lean.Json), jsonRank j ≤ n → wellFormedJsonBool j = true →
      ∀ (width col ind : Nat) (fl : Bool) (acc : String) (rest : List DocItem),
        ∃ (seg : String) (col' : Nat) (tape : RenderTape),
          formatDocLoop width col acc (⟨fl, ind, treeDoc j⟩ :: rest) =
            formatDocLoop width col' (acc ++ seg) rest ∧
          renderVal j tape = some seg := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j hj hWf width col ind fl acc rest
    cases j with
    | null =>
      exact ⟨"null", col + 4, .null "" "",
        by unfold treeDoc; (conv => lhs; unfold formatDocLoop); rfl,
        by simp [renderVal, isJsonWs]⟩
    | bool b =>
      cases b
      · exact ⟨"false", col + 5, .bool "" "",
          by unfold treeDoc; (conv => lhs; unfold formatDocLoop); rfl,
          by simp [renderVal, isJsonWs]⟩
      · exact ⟨"true", col + 4, .bool "" "",
          by unfold treeDoc; (conv => lhs; unfold formatDocLoop); rfl,
          by simp [renderVal, isJsonWs]⟩
    | num x =>
      obtain ⟨_, _, _, _, nt, hRen⟩ := jsonNumberToString_spec x
      exact ⟨jsonNumberToString x, col + (jsonNumberToString x).length, .num "" nt "",
        by unfold treeDoc; (conv => lhs; unfold formatDocLoop),
        by simp [renderVal, isJsonWs, hRen]⟩
    | str s =>
      obtain ⟨_, _, _, _, styles, hRen⟩ := renderString_spec s
      exact ⟨renderString s "", col + (renderString s "").length, .str "" styles "",
        by unfold treeDoc; (conv => lhs; unfold formatDocLoop),
        by simp [renderVal, isJsonWs, hRen]⟩
    | arr elems =>
      cases hlist : elems.toList with
      | nil =>
        have hemp : elems.isEmpty = true := Array.isEmpty_iff.mpr (Array.ext' hlist)
        exact ⟨"[]", col + 2, .emptyArr "" "" "",
          by rw [treeDoc_arr_nil hlist]; (conv => lhs; unfold formatDocLoop); rfl,
          by simp [renderVal, hemp, isJsonWs]⟩
      | cons x0 xtl =>
        have hRankSub : ∀ x ∈ x0 :: xtl, jsonRank x < n := by
          intro x hx
          have hlt := jsonRank_lt_jsonListRank hx
          simp only [jsonRank, hlist] at hj; omega
        simp only [wellFormedJsonBool, hlist] at hWf
        have hArrChain : ∀ (u : Lean.Json) (utl : List Lean.Json) (c0 indA : Nat) (flA : Bool)
            (accA : String) (wsPre : String) (tailItems : List DocItem),
            (∀ y ∈ u :: utl, jsonRank y < n) →
            wellFormedJsonListBool (u :: utl) = true →
            isJsonWs wsPre = true →
            ∃ (parts : List String) (cEnd : Nat) (ts : List RenderTape),
              formatDocLoop width c0 (accA ++ wsPre)
                (⟨flA, indA, joinCommaLineFwd (treeDoc u) (treeDocList utl)⟩ :: tailItems) =
                formatDocLoop width cEnd (accA ++ String.intercalate "," parts) tailItems ∧
              renderArrElems (u :: utl) ts = some parts := by
          intro u utl
          induction utl generalizing u with
          | nil =>
            intro c0 indA flA accA wsPre tailItems hR hWL hWsPre
            simp only [wellFormedJsonListBool, Bool.and_true] at hWL
            obtain ⟨segU, c1, tU, hLoopU, hRenU⟩ :=
              ih (jsonRank u) (hR u List.mem_cons_self) u (Nat.le_refl _) hWL width c0 indA flA (accA ++ wsPre) tailItems
            refine ⟨[wsPre ++ segU], c1, [prependWsBefore wsPre tU], ?_, ?_⟩
            · rw [treeDocList, joinCommaLineFwd, String.intercalate_singleton, hLoopU, String.append_assoc]
            · simp [renderArrElems, renderVal_prependWsBefore hRenU hWsPre, bind, Option.bind]
          | cons u1 urest ihu =>
            intro c0 indA flA accA wsPre tailItems hR hWL hWsPre
            rw [wellFormedJsonListBool, Bool.and_eq_true] at hWL
            have htdCons : treeDocList (u1 :: urest) = treeDoc u1 :: treeDocList urest := by rw [treeDocList]
            obtain ⟨segU, c1, tU, hLoopU, hRenU⟩ :=
              ih (jsonRank u) (hR u List.mem_cons_self) u (Nat.le_refl _) hWL.1 width c0 indA flA (accA ++ wsPre)
                (⟨flA, indA, .append (.text ",") (.append .line (joinCommaLineFwd (treeDoc u1) (treeDocList urest)))⟩ :: tailItems)
            let wsNext := if flA then " " else String.ofList ('\n' :: List.replicate indA ' ')
            let c2 := if flA then (c1 + 1) + 1 else indA
            have hMidStep : formatDocLoop width c1 ((accA ++ wsPre) ++ segU)
                (⟨flA, indA, .append (.text ",") (.append .line (joinCommaLineFwd (treeDoc u1) (treeDocList urest)))⟩ :: tailItems) =
                formatDocLoop width c2 (((accA ++ (wsPre ++ segU) ++ ",") ++ wsNext))
                  (⟨flA, indA, joinCommaLineFwd (treeDoc u1) (treeDocList urest)⟩ :: tailItems) := by
              conv => lhs; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop
              cases flA <;> simp [wsNext, c2, show ",".length = 1 from rfl, String.append_assoc]
            obtain ⟨partsTl, cEnd, tsTl, hLoopTl, hRenTl⟩ :=
              ihu u1 c2 indA flA (accA ++ (wsPre ++ segU) ++ ",") wsNext tailItems
                (fun y hy => hR y (List.mem_cons_of_mem _ hy)) hWL.2 (isJsonWs_line_emit flA indA)
            cases partsTl with
            | nil =>
              cases tsTl with
              | nil => simp [renderArrElems] at hRenTl
              | cons t1 ttl =>
                rw [renderArrElems] at hRenTl; simp only [bind, Option.bind] at hRenTl
                cases hr1 : renderVal u1 t1 <;> rw [hr1] at hRenTl <;> try simp at hRenTl
                cases hrtl : renderArrElems urest ttl <;> rw [hrtl] at hRenTl <;> simp at hRenTl
            | cons p1 ptl =>
              refine ⟨(wsPre ++ segU) :: p1 :: ptl, cEnd, prependWsBefore wsPre tU :: tsTl, ?_, ?_⟩
              · rw [htdCons, joinCommaLineFwd]
                conv => lhs; unfold formatDocLoop
                rw [hLoopU, hMidStep, hLoopTl, String.intercalate_cons_cons]
                simp [String.append_assoc]
              · simp [renderArrElems, renderVal_prependWsBefore hRenU hWsPre, hRenTl, bind, Option.bind]
        rw [treeDoc_arr_cons hlist]; dsimp only [docBracket]
        let fit := fl || docFits ((width : Int) - (col : Int))
          (⟨true, ind, .nest 1 (.append (.text "[") (.append (joinCommaLineFwd (treeDoc x0) (treeDocList xtl)) (.text "]")))⟩ :: rest)
        obtain ⟨parts, cEnd, ts, hChainEq, hRenTs⟩ :=
          hArrChain x0 xtl (col + 1) (ind + 1) fit (acc ++ "[") "" (⟨fit, ind + 1, .text "]"⟩ :: rest)
            hRankSub hWf rfl
        have hNotEmp : (!elems.isEmpty) = true := by
          cases he : elems.isEmpty
          · rfl
          · exfalso; have := Array.isEmpty_iff.mp he; subst this; simp at hlist
        refine ⟨"[" ++ String.intercalate "," parts ++ "]", cEnd + 1, .arr "" ts "", ?_, ?_⟩
        · conv => lhs; unfold formatDocLoop; dsimp only; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop
          have hOpen : (acc ++ "[") ++ "" = acc ++ "[" := String.append_empty
          rw [← hOpen]
          change formatDocLoop width (col + "[".length) ((acc ++ "[") ++ "")
            (⟨fit, ind + 1, joinCommaLineFwd (treeDoc x0) (treeDocList xtl)⟩ :: ⟨fit, ind + 1, .text "]"⟩ :: rest) = _
          have hl1 : "[".length = 1 := rfl
          have hl2 : "]".length = 1 := rfl
          rw [hl1, hChainEq]
          conv => lhs; unfold formatDocLoop
          simp [hl2, String.append_assoc]
        · simp [renderVal, hNotEmp, isJsonWs, hlist, hRenTs, bind, Option.bind]
    | obj kvs =>
      cases hEntL : objEntries kvs with
      | nil =>
        have hemp : (objEntries kvs).isEmpty = true := by simp [hEntL]
        exact ⟨"{}", col + 2, .emptyObj "" "" "",
          by rw [treeDoc_obj_nil hEntL]; (conv => lhs; unfold formatDocLoop); rfl,
          by simp [renderVal, hemp, isJsonWs]⟩
      | cons e0 etl =>
        let entries := e0 :: etl
        simp only [wellFormedJsonBool, Bool.and_eq_true] at hWf
        rcases hWf with ⟨hSorted, hWfTree⟩
        have hNoDup : noDupKeysBool entries = true := by
          dsimp only [entries]; rw [← hEntL]; exact noDupKeysBool_of_isStrictlySortedKeys hSorted
        have hWfVals : ∀ p ∈ entries, wellFormedJsonBool p.2 = true := by
          dsimp only [entries]; rw [← hEntL]; exact (wellFormedJsonTreeBool_iff_entries kvs.inner.inner).mp hWfTree
        have hRankSub : ∀ p ∈ entries, jsonRank p.2 < n := by
          intro ⟨ek, ev⟩ hp
          have hlt := jsonRank_lt_jsonAssocRank hp
          have htr : jsonAssocRank entries = jsonTreeRank kvs.inner.inner := by
            dsimp only [entries]; rw [← hEntL]; exact jsonAssocRank_treeEntries kvs.inner.inner
          simp only [jsonRank] at hj; dsimp only at *; omega
        have hKvSingle : ∀ (ek : String) (ev : Lean.Json) (c0 indO : Nat) (flO : Bool)
            (accO wsK : String) (tailItems : List DocItem),
            (ek, ev) ∈ entries → isJsonWs wsK = true →
            ∃ (part : String) (c1 : Nat) (kt : ObjKeyTape) (vt : RenderTape),
              kt.key = ek ∧
              formatDocLoop width c0 (accO ++ wsK) (⟨flO, indO, kvDoc (ek, ev)⟩ :: tailItems) =
                formatDocLoop width c1 (accO ++ part) tailItems ∧
              renderObjEntries entries [(kt, vt)] = some [part] := by
          intro ek ev c0 indO flO accO wsK tailItems hpIn hWsK
          obtain ⟨_, _, _, _, stylesK, hRenK⟩ := renderString_spec ek
          let kvInner := JsonDoc.append (.text (renderString ek ++ ":")) (.append .line (treeDoc ev))
          let fitKv := flO || docFits ((width : Int) - (c0 : Int)) (⟨true, indO, kvInner⟩ :: tailItems)
          let wsV := if fitKv then " " else String.ofList ('\n' :: List.replicate indO ' ')
          let cAfterWs := if fitKv then (c0 + (renderString ek "" ++ ":").length) + 1 else indO
          obtain ⟨rv, c1, vt0, hLoopV, hRenV⟩ :=
            ih (jsonRank ev) (hRankSub (ek, ev) hpIn) ev (Nat.le_refl _) (hWfVals (ek, ev) hpIn)
              width cAfterWs indO fitKv (((accO ++ wsK) ++ (renderString ek "" ++ ":")) ++ wsV) tailItems
          have hlu : lookupKeyList ek entries = some ev :=
            (lookupKeyList_eq_some_iff_mem hNoDup ek ev).mpr hpIn
          let kt : ObjKeyTape := ⟨wsK, ek, stylesK, ""⟩
          let vt := prependWsBefore wsV vt0
          let part := wsK ++ renderString ek "" ++ "" ++ ":" ++ (wsV ++ rv)
          refine ⟨part, c1, kt, vt, rfl, ?_, ?_⟩
          · dsimp only [kvDoc]
            conv => lhs; unfold formatDocLoop; dsimp only; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop
            have hStepWs : formatDocLoop width (c0 + (renderString ek "" ++ ":").length)
                ((accO ++ wsK) ++ (renderString ek "" ++ ":"))
                (⟨fitKv, indO, .line⟩ :: ⟨fitKv, indO, treeDoc ev⟩ :: tailItems) =
                formatDocLoop width cAfterWs (((accO ++ wsK) ++ (renderString ek "" ++ ":")) ++ wsV)
                  (⟨fitKv, indO, treeDoc ev⟩ :: tailItems) := by
              dsimp only [wsV, cAfterWs]
              conv => lhs; unfold formatDocLoop
              cases fitKv <;> rfl
            change formatDocLoop width (c0 + (renderString ek "" ++ ":").length)
                ((accO ++ wsK) ++ (renderString ek "" ++ ":"))
                (⟨fitKv, indO, .line⟩ :: ⟨fitKv, indO, treeDoc ev⟩ :: tailItems) = _
            rw [hStepWs, hLoopV]
            simp [part, String.append_assoc]
          · have hWsV : isJsonWs wsV = true := isJsonWs_line_emit fitKv indO
            have hWsEmp : isJsonWs "" = true := rfl
            simp [renderObjEntries, kt, vt, part, hWsK, hWsEmp, hlu, hRenK,
              renderVal_prependWsBefore hRenV hWsV, bind, Option.bind]
        have hObjChain : ∀ (a0 : String × Lean.Json) (atl : List (String × Lean.Json))
            (c0 indO : Nat) (flO : Bool) (accO wsK : String) (tailItems : List DocItem),
            (∀ p ∈ a0 :: atl, p ∈ entries) → isJsonWs wsK = true →
            ∃ (parts : List String) (cEnd : Nat) (plan : List (ObjKeyTape × RenderTape)),
              plan.map (fun q => q.1.key) = (a0 :: atl).map Prod.fst ∧
              formatDocLoop width c0 (accO ++ wsK)
                (⟨flO, indO, joinCommaLineFwd (kvDoc a0) (atl.map kvDoc)⟩ :: tailItems) =
                formatDocLoop width cEnd (accO ++ String.intercalate "," parts) tailItems ∧
              renderObjEntries entries plan = some parts := by
          intro a0 atl
          induction atl generalizing a0 with
          | nil =>
            intro c0 indO flO accO wsK tailItems hSub hWsK
            obtain ⟨part, c1, kt, vt, hkEq, hLoop, hRen1⟩ :=
              hKvSingle a0.1 a0.2 c0 indO flO accO wsK tailItems (hSub a0 List.mem_cons_self) hWsK
            refine ⟨[part], c1, [(kt, vt)], by simp [hkEq], ?_, hRen1⟩
            simpa [joinCommaLineFwd, String.intercalate_singleton] using hLoop
          | cons e1 erest ihe =>
            intro c0 indO flO accO wsK tailItems hSub hWsK
            simp only [List.map_cons, joinCommaLineFwd]
            obtain ⟨part0, c1, kt0, vt0, hkEq0, hLoop0, hRen0⟩ :=
              hKvSingle a0.1 a0.2 c0 indO flO accO wsK
                (⟨flO, indO, .append (.text ",") (.append .line (joinCommaLineFwd (kvDoc e1) (erest.map kvDoc)))⟩ :: tailItems)
                (hSub a0 List.mem_cons_self) hWsK
            let wsNext := if flO then " " else String.ofList ('\n' :: List.replicate indO ' ')
            let c2 := if flO then (c1 + 1) + 1 else indO
            have hMidStep : formatDocLoop width c1 (accO ++ part0)
                (⟨flO, indO, .append (.text ",") (.append .line (joinCommaLineFwd (kvDoc e1) (erest.map kvDoc)))⟩ :: tailItems) =
                formatDocLoop width c2 ((accO ++ part0 ++ ",") ++ wsNext)
                  (⟨flO, indO, joinCommaLineFwd (kvDoc e1) (erest.map kvDoc)⟩ :: tailItems) := by
              conv => lhs; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop
              cases flO <;> simp [wsNext, c2, show ",".length = 1 from rfl, String.append_assoc]
            obtain ⟨partsTl, cEnd, planTl, hKeysTl, hLoopTl, hRenTl⟩ :=
              ihe e1 c2 indO flO (accO ++ part0 ++ ",") wsNext tailItems
                (fun p hp => hSub p (List.mem_cons_of_mem _ hp)) (isJsonWs_line_emit flO indO)
            cases partsTl with
            | nil =>
              cases planTl with
              | nil => simp at hKeysTl
              | cons q qtl =>
                rcases q with ⟨kt2, vt2⟩
                rw [renderObjEntries] at hRenTl; simp only [bind, Option.bind] at hRenTl
                split at hRenTl <;> try simp at hRenTl
                cases hlu2 : lookupKeyList kt2.key entries <;> rw [hlu2] at hRenTl <;> try simp at hRenTl
                rename_i v2
                cases hrk2 : renderStringLiteral kt2.key kt2.keyChars <;> rw [hrk2] at hRenTl <;> try simp at hRenTl
                cases hrv2 : renderVal v2 vt2 <;> rw [hrv2] at hRenTl <;> try simp at hRenTl
                cases hrtl2 : renderObjEntries entries qtl <;> rw [hrtl2] at hRenTl <;> simp at hRenTl
            | cons p1 ptl =>
              have hRenCons : renderObjEntries entries ((kt0, vt0) :: planTl) = some (part0 :: p1 :: ptl) := by
                simp only [renderObjEntries, bind, Option.bind] at hRen0 ⊢
                by_cases hws0 : (!isJsonWs kt0.wsBeforeKey || !isJsonWs kt0.wsBeforeColon) = true
                · simp [hws0] at hRen0
                · simp only [hws0, Bool.false_eq_true, ↓reduceIte] at hRen0 ⊢
                  cases hlu0 : lookupKeyList kt0.key entries with
                  | none => rw [hlu0] at hRen0; cases hRen0
                  | some v0 =>
                    rw [hlu0] at hRen0; dsimp only at hRen0 ⊢
                    cases hrk0 : renderStringLiteral kt0.key kt0.keyChars with
                    | none => rw [hrk0] at hRen0; cases hRen0
                    | some rk0 =>
                      rw [hrk0] at hRen0; dsimp only at hRen0 ⊢
                      cases hrv0 : renderVal v0 vt0 with
                      | none => rw [hrv0] at hRen0; cases hRen0
                      | some rv0 =>
                        rw [hrv0] at hRen0; dsimp only at hRen0 ⊢
                        injection hRen0 with hListEq
                        injection hListEq with hEq0
                        simp [hEq0, hRenTl]
              refine ⟨part0 :: p1 :: ptl, cEnd, (kt0, vt0) :: planTl, by simp [hkEq0, hKeysTl], ?_, hRenCons⟩
              conv => lhs; unfold formatDocLoop
              rw [hLoop0, hMidStep, hLoopTl, String.intercalate_cons_cons]
              simp [String.append_assoc]
        rw [treeDoc_obj_cons hEntL]; dsimp only [docBracket]
        let fit := fl || docFits ((width : Int) - (col : Int))
          (⟨true, ind, .nest 1 (.append (.text "{") (.append (joinCommaLineFwd (kvDoc e0) (etl.map kvDoc)) (.text "}")))⟩ :: rest)
        obtain ⟨parts, cEnd, plan, hPlanKeys, hChainEq, hRenPlan⟩ :=
          hObjChain e0 etl (col + 1) (ind + 1) fit (acc ++ "{") "" (⟨fit, ind + 1, .text "}"⟩ :: rest)
            (fun _ hp => hp) rfl
        have hPerm : isObjPlanPerm entries plan = true := by
          have hndK := nodup_of_noDupKeysBool hNoDup
          have hndPlanB : noDupStringsBool (plan.map fun q => q.1.key) = true := by
            rw [hPlanKeys]; exact noDupStringsBool_of_nodup hndK
          have hLenEq : plan.length = entries.length := by
            have := congrArg List.length hPlanKeys; simpa [entries] using this
          simp only [isObjPlanPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
          refine ⟨⟨⟨hNoDup, hndPlanB⟩, hLenEq⟩, fun p hp => ?_⟩
          rw [hasKeyList_iff_mem, ← hPlanKeys]
          exact List.mem_map_of_mem hp
        refine ⟨"{" ++ String.intercalate "," parts ++ "}", cEnd + 1, .obj "" plan "", ?_, ?_⟩
        · conv => lhs; unfold formatDocLoop; dsimp only; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop; unfold formatDocLoop
          have hOpen : (acc ++ "{") ++ "" = acc ++ "{" := String.append_empty
          rw [← hOpen]
          change formatDocLoop width (col + "{".length) ((acc ++ "{") ++ "")
            (⟨fit, ind + 1, joinCommaLineFwd (kvDoc e0) (etl.map kvDoc)⟩ :: ⟨fit, ind + 1, .text "}"⟩ :: rest) = _
          have hl1 : "{".length = 1 := rfl
          have hl2 : "}".length = 1 := rfl
          rw [hl1, hChainEq]
          conv => lhs; unfold formatDocLoop
          simp [hl2, String.append_assoc]
        · simp [renderVal, hEntL, entries, isJsonWs, hPerm, hRenPlan, bind, Option.bind]

/-- `LeanSwe.Json.pretty` obeys `Model.allowedPretty` across all `Lean.Json` values and `lineWidth`s. -/
theorem allowedPretty_holds : Core.ObeysPure2 (@LeanSwe.Json.pretty) Model.allowedPretty := by
  intro j lineWidth
  obtain ⟨hNe, hStarts⟩ := pretty_nonEmpty_and_startsWith j lineWidth
  simp only [Model.allowedPretty]
  refine ⟨hNe, pretty_eq_flatPretty_of_le j lineWidth, ?_⟩
  by_cases hwf : wellFormedJsonBool j = true
  · simp only [hwf, ↓reduceIte]
    obtain ⟨seg, col', tape, hLoop, hRen⟩ :=
      formatDocLoop_treeDoc_renderVal (jsonRank j) j (Nat.le_refl _) hwf lineWidth 0 0 false "" []
    have hOutEq : LeanSwe.Json.pretty j lineWidth = seg := by
      simp only [LeanSwe.Json.pretty, Internal.pretty, renderFormat_eq_treeDoc, hLoop]
      simp [formatDocLoop]
    exact ⟨tape, by rw [hOutEq]; simp [render, hwf, hRen]⟩
  · simp only [hwf, Bool.false_eq_true, ↓reduceIte, hStarts]; rfl

end LeanSwe.Json.Proofs
