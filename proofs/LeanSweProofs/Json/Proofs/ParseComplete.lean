import Lean.Data.Json.Basic
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import Core.Obeys
import LeanSwe.Json.Interface
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.ScalarLex
import LeanSweProofs.Json.Proofs.ModelDecode
import LeanSweProofs.Json.Proofs.Injective
import LeanSweProofs.Json.Proofs.Utf8Ws
import LeanSweProofs.Json.Proofs.StringComplete
import LeanSweProofs.Json.Proofs.NumberComplete
import LeanSweProofs.Json.Proofs.TreeMapWf
import LeanSweProofs.Json.Proofs.ParseSound
import LeanSweProofs.Json.Proofs.ParseCompleteHelpers

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Strong induction proving simultaneous completeness of `parseWantValue` and `parseAfterValue`. -/
theorem parse_mutual_complete :
    ∀ (fuel : Nat),
      (∀ {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size) {frames : List ParseFrame}
         {cs : List Char} {stackPref : String} {out : Lean.Json},
        (bytes.size - pos) * 2 + 1 ≤ fuel →
        ByteSliceAt bytes pos cs →
        ValidStack frames stackPref →
        parseWantValue bytes pos hPos frames = .ok out →
        wellFormedJsonBool out = true ∧
          ∃ tape : RenderTape, withinResourceLimitsBool tape = true ∧
            renderVal out tape = some (stackPref ++ String.ofList cs)) ∧
      (∀ {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size) {frames : List ParseFrame}
         {val : Lean.Json} {valTape : RenderTape} {valStr : String}
         {cs : List Char} {stackPref : String} {out : Lean.Json},
        (bytes.size - pos) * 2 ≤ fuel →
        ByteSliceAt bytes pos cs →
        ValidStack frames stackPref →
        wellFormedJsonBool val = true →
        withinResourceLimitsBool valTape = true →
        renderVal val valTape = some valStr →
        parseAfterValue bytes pos hPos frames val = .ok out →
        wellFormedJsonBool out = true ∧
          ∃ tape : RenderTape, withinResourceLimitsBool tape = true ∧
            renderVal out tape = some (stackPref ++ valStr ++ String.ofList cs)) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    refine ⟨?_, ?_⟩
    · intro bytes pos hPos frames cs stackPref out hFuel hSlice hStack hWant
      unfold parseWantValue at hWant
      have hSp := skipWsSub_spec cs hPos hSlice
      have hSpProps := splitJsonWs_props cs
      rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
      rcases hSplit : splitJsonWs cs with ⟨ws0, csP⟩
      rw [hSub] at hWant; rw [hSub, hSplit] at hSp
      rw [hSplit] at hSpProps
      rcases hSp with ⟨hpEq, hws0, _, hsP⟩
      rcases hSpProps with ⟨hcsEq0, _, _, _⟩
      dsimp only at hpEq hsP hWant
      split at hWant <;> try cases hWant
      rename_i hLt
      let wb := String.ofList ws0
      have hwb : isJsonWs wb = true := hws0
      let b := bytes[p]'hLt
      by_cases hb5b : b == 0x5b
      · simp only [show bytes[p] == 0x5b from hb5b, ↓reduceIte] at hWant
        have hbEq : bytes[p]'hLt = 0x5b := beq_iff_eq.mp hb5b
        obtain ⟨openCh, csAfterOpen, rfl, hopenNat, _, hsAfterOpen⟩ :=
          byteSliceAt_head_lt_128 hsP hLt (by rw [hbEq]; decide)
        have hopenEq : openCh = '[' := by
          apply Char.ext; apply UInt32.toNat_inj.mp; change openCh.toNat = ('[').toNat; rw [hopenNat, hbEq]; rfl
        subst hopenEq
        have hSp1 := skipWsSub_spec csAfterOpen hLt hsAfterOpen
        have hSpProps1 := splitJsonWs_props csAfterOpen
        rcases hSub1 : skipWsSub bytes (p + 1) hLt with ⟨p1, hp1Ge, hp1Le⟩
        rcases hSplit1 : splitJsonWs csAfterOpen with ⟨ws1, csP1⟩
        rw [hSub1] at hWant; rw [hSub1, hSplit1] at hSp1; rw [hSplit1] at hSpProps1
        rcases hSp1 with ⟨_, hws1, _, hsP1⟩
        dsimp only at hsP1 hSpProps1 hWant
        split at hWant <;> try cases hWant
        rename_i hClose
        by_cases hb5d : bytes[p1]'hClose == 0x5d
        · simp only [hb5d, ↓reduceIte] at hWant
          have hbEq1 := beq_iff_eq.mp hb5d
          obtain ⟨closeCh, csAfterClose, rfl, hcloseNat, _, hsAfterClose⟩ :=
            byteSliceAt_head_lt_128 hsP1 hClose (by rw [hbEq1]; decide)
          have hcloseEq : closeCh = ']' := by
            apply Char.ext; apply UInt32.toNat_inj.mp; change closeCh.toNat = (']').toNat; rw [hcloseNat, hbEq1]; rfl
          subst hcloseEq
          let wi := String.ofList ws1
          have hRenEmpty : renderVal (.arr #[]) (.emptyArr wb wi "") = some (wb ++ "[" ++ wi ++ "]") := by
            unfold renderVal; simp [hwb, show isJsonWs wi = true from hws1]; rfl
          have hDec : (bytes.size - (p1 + 1)) * 2 < fuel := by omega
          obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
            (ih ((bytes.size - (p1 + 1)) * 2) hDec).2 hClose (Nat.le_refl _) hsAfterClose hStack
              (by simp [wellFormedJsonBool, wellFormedJsonListBool]) (by simp [withinResourceLimitsBool]) hRenEmpty hWant
          refine ⟨hWfOut, tape, hLimOut, ?_⟩
          have hStrEq : stackPref ++ (wb ++ "[" ++ wi ++ "]") ++ String.ofList csAfterClose =
              stackPref ++ String.ofList cs := by
            simp [wb, wi, hcsEq0, hSpProps1.1, String.ofList_append, String.append_assoc]
          rwa [← hStrEq]
        · simp only [hb5d, Bool.false_eq_true, ↓reduceIte] at hWant
          let wsFirst := String.ofList ws1
          have hFrame : ValidFrame (.arr #[]) (wb ++ "[" ++ wsFirst) :=
            ⟨wb, wsFirst, hwb, hws1, rfl⟩
          have hDec : (bytes.size - p1) * 2 + 1 < fuel := by omega
          obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
            (ih ((bytes.size - p1) * 2 + 1) hDec).1 hp1Le (Nat.le_refl _) hsP1 (.cons hStack hFrame) hWant
          refine ⟨hWfOut, tape, hLimOut, ?_⟩
          have hStrEq : (stackPref ++ (wb ++ "[" ++ wsFirst)) ++ String.ofList csP1 =
              stackPref ++ String.ofList cs := by
            simp [wb, wsFirst, hcsEq0, hSpProps1.1, String.ofList_append, String.append_assoc]
          rwa [← hStrEq]
      · simp only [show (bytes[p] == 0x5b) = false from Bool.eq_false_iff.mpr hb5b, Bool.false_eq_true, ↓reduceIte] at hWant
        by_cases hb7b : b == 0x7b
        · simp only [show bytes[p] == 0x7b from hb7b, ↓reduceIte] at hWant
          have hbEq : bytes[p]'hLt = 0x7b := beq_iff_eq.mp hb7b
          obtain ⟨openCh, csAfterOpen, rfl, hopenNat, _, hsAfterOpen⟩ :=
            byteSliceAt_head_lt_128 hsP hLt (by rw [hbEq]; decide)
          have hopenEq : openCh = '{' := by
            apply Char.ext; apply UInt32.toNat_inj.mp; change openCh.toNat = ('{').toNat; rw [hopenNat, hbEq]; rfl
          subst hopenEq
          have hSp1 := skipWsSub_spec csAfterOpen hLt hsAfterOpen
          have hSpProps1 := splitJsonWs_props csAfterOpen
          rcases hSub1 : skipWsSub bytes (p + 1) hLt with ⟨p1, hp1Ge, hp1Le⟩
          rcases hSplit1 : splitJsonWs csAfterOpen with ⟨ws1, csP1⟩
          rw [hSub1] at hWant; rw [hSub1, hSplit1] at hSp1; rw [hSplit1] at hSpProps1
          rcases hSp1 with ⟨_, hws1, _, hsP1⟩
          dsimp only at hsP1 hSpProps1 hWant
          split at hWant <;> try cases hWant
          rename_i hClose
          by_cases hb7d : bytes[p1]'hClose == 0x7d
          · simp only [hb7d, ↓reduceIte] at hWant
            have hbEq1 := beq_iff_eq.mp hb7d
            obtain ⟨closeCh, csAfterClose, rfl, hcloseNat, _, hsAfterClose⟩ :=
              byteSliceAt_head_lt_128 hsP1 hClose (by rw [hbEq1]; decide)
            have hcloseEq : closeCh = '}' := by
              apply Char.ext; apply UInt32.toNat_inj.mp; change closeCh.toNat = ('}').toNat; rw [hcloseNat, hbEq1]; rfl
            subst hcloseEq
            let wi := String.ofList ws1
            have hRenEmpty : renderVal (.obj ∅) (.emptyObj wb wi "") = some (wb ++ "{" ++ wi ++ "}") := by
              have hEmp : (objEntries (∅ : Std.TreeMap.Raw String Lean.Json compare)).isEmpty = true := rfl
              unfold renderVal; simp [hEmp, hwb, show isJsonWs wi = true from hws1]; rfl
            have hDec : (bytes.size - (p1 + 1)) * 2 < fuel := by omega
            have hWfEmpObj : wellFormedJsonBool (.obj ∅) = true := by
              have hL : (∅ : Std.TreeMap.Raw String Lean.Json compare).inner.inner = .leaf := rfl
              simp [wellFormedJsonBool, hL, wellFormedJsonTreeBool, objEntries, treeEntries, isStrictlySortedKeys]
            obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
              (ih ((bytes.size - (p1 + 1)) * 2) hDec).2 hClose (Nat.le_refl _) hsAfterClose hStack hWfEmpObj (by simp [withinResourceLimitsBool]) hRenEmpty hWant
            refine ⟨hWfOut, tape, hLimOut, ?_⟩
            have hStrEq : stackPref ++ (wb ++ "{" ++ wi ++ "}") ++ String.ofList csAfterClose =
                stackPref ++ String.ofList cs := by
              simp [wb, wi, hcsEq0, hSpProps1.1, String.ofList_append, String.append_assoc]
            rwa [← hStrEq]
          · simp only [hb7d, Bool.false_eq_true, ↓reduceIte] at hWant
            match hKeyP : parseStringAt bytes p1 with
            | .error _ => simp [hKeyP] at hWant
            | .ok ⟨k, ⟨p2, hp2a, hp2b⟩⟩ =>
            rw [hKeyP] at hWant; obtain ⟨kStyles, rk0, csP2, hcsP1Eq, hrk0, hsP2⟩ := parseStringAt_complete hsP1 hKeyP
            dsimp only at hsP2 hWant
            have hSp3 := skipWsSub_spec csP2 hp2b hsP2
            have hSpProps3 := splitJsonWs_props csP2
            rcases hSub3 : skipWsSub bytes p2 hp2b with ⟨p3, hp3Ge, hp3Le⟩
            rcases hSplit3 : splitJsonWs csP2 with ⟨wsCol, csP3⟩
            rw [hSub3] at hWant; rw [hSub3, hSplit3] at hSp3; rw [hSplit3] at hSpProps3
            rcases hSp3 with ⟨_, hwsCol, _, hsP3⟩
            dsimp only at hsP3 hSpProps3 hWant
            split at hWant <;> try cases hWant
            rename_i hCol
            by_cases hbCol : bytes[p3]'hCol == 0x3a
            · simp only [hbCol, ↓reduceIte] at hWant
              have hbEqCol := beq_iff_eq.mp hbCol
              obtain ⟨colCh, csVal0, rfl, hcolNat, _, hsVal0⟩ :=
                byteSliceAt_head_lt_128 hsP3 hCol (by rw [hbEqCol]; decide)
              have hcolEq : colCh = ':' := by
                apply Char.ext; apply UInt32.toNat_inj.mp; change colCh.toNat = (':').toNat; rw [hcolNat, hbEqCol]; rfl
              subst hcolEq
              let curKt : ObjKeyTape := ⟨String.ofList ws1, k, kStyles, String.ofList wsCol⟩
              let framePref := wb ++ "{" ++ "" ++ curKt.wsBeforeKey ++ rk0 ++ curKt.wsBeforeColon ++ ":"
              have hEmpEntries : objEntries (∅ : Std.TreeMap.Raw String Lean.Json compare) = [] := rfl
              have hFrame : ValidFrame (.obj ∅ k) framePref :=
                ⟨wb, [], [], curKt, rk0, Std.TreeMap.Raw.WF.emptyc,
                  by simp [hEmpEntries], Std.TreeMap.Raw.contains_emptyc,
                  hwb, rfl, hws1, hwsCol, hrk0, List.nodup_nil,
                  fun q => by simp [Std.TreeMap.Raw.contains_emptyc],
                  by simp [withinResourceLimitsObjBool], by simp [renderObjEntries], rfl⟩
              have hDec : (bytes.size - (p3 + 1)) * 2 + 1 < fuel := by omega
              obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
                (ih ((bytes.size - (p3 + 1)) * 2 + 1) hDec).1 hCol (Nat.le_refl _) hsVal0 (.cons hStack hFrame) hWant
              refine ⟨hWfOut, tape, hLimOut, ?_⟩
              have hStrEq : (stackPref ++ framePref) ++ String.ofList csVal0 = stackPref ++ String.ofList cs := by
                simp [framePref, curKt, wb, hcsEq0, hSpProps1.1, hcsP1Eq, hSpProps3.1,
                  String.ofList_append, String.ofList_toList, String.append_assoc]
              rwa [← hStrEq]
            · simp [hbCol] at hWant
        · simp only [show (bytes[p] == 0x7b) = false from Bool.eq_false_iff.mpr hb7b, Bool.false_eq_true, ↓reduceIte] at hWant
          by_cases hb22 : b == 0x22
          · simp only [show bytes[p] == 0x22 from hb22, ↓reduceIte] at hWant
            match hStrP : parseStringAt bytes p with
            | .error _ => simp [hStrP] at hWant
            | .ok ⟨s, ⟨p1, hp1a, hp1b⟩⟩ =>
            rw [hStrP] at hWant; obtain ⟨styles, lit, csAfter, hcsPEq, hlit, hsAfter⟩ := parseStringAt_complete hsP hStrP
            dsimp only at hsAfter hWant
            have hRen : renderVal (.str s) (.str wb styles "") = some (wb ++ lit) := by
              unfold renderVal; simp [hwb, hlit]; rfl
            have hDec : (bytes.size - p1) * 2 < fuel := by omega
            obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
              (ih ((bytes.size - p1) * 2) hDec).2 hp1b (Nat.le_refl _) hsAfter hStack
                (by simp [wellFormedJsonBool]) (by simp [withinResourceLimitsBool]) hRen hWant
            refine ⟨hWfOut, tape, hLimOut, ?_⟩
            have hStrEq : stackPref ++ (wb ++ lit) ++ String.ofList csAfter = stackPref ++ String.ofList cs := by
              simp [wb, hcsEq0, hcsPEq, String.ofList_append, String.ofList_toList, String.append_assoc]
            rwa [← hStrEq]
          · simp only [show (bytes[p] == 0x22) = false from Bool.eq_false_iff.mpr hb22, Bool.false_eq_true, ↓reduceIte] at hWant
            by_cases hb74 : b == 0x74
            · simp only [show bytes[p] == 0x74 from hb74, ↓reduceIte] at hWant
              by_cases hkw : matchesKeyword bytes p kwTrue = true
              · simp only [hkw, ↓reduceIte] at hWant
                split at hWant <;> try cases hWant
                rename_i hEnd
                obtain ⟨csAfter, hcsPEq, hsAfter⟩ :=
                  (matchesKeyword_ascii_spec ['t', 'r', 'u', 'e'] (by decide) hsP).mp hkw
                have hRen : renderVal (.bool true) (.bool wb "") = some (wb ++ "true") := by
                  unfold renderVal; simp [hwb]; rfl
                have hDec : (bytes.size - (p + 4)) * 2 < fuel := by omega
                obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
                  (ih ((bytes.size - (p + 4)) * 2) hDec).2 hEnd (Nat.le_refl _) hsAfter hStack
                    (by simp [wellFormedJsonBool]) (by simp [withinResourceLimitsBool]) hRen hWant
                refine ⟨hWfOut, tape, hLimOut, ?_⟩
                have h1 : String.ofList csP = "true" ++ String.ofList csAfter := by
                  rw [hcsPEq, String.ofList_append]
                have hStrEq : stackPref ++ (wb ++ "true") ++ String.ofList csAfter = stackPref ++ String.ofList cs := by
                  simp [wb, hcsEq0, String.ofList_append, h1, String.append_assoc]
                rwa [← hStrEq]
              · simp [hkw] at hWant
            · simp only [show (bytes[p] == 0x74) = false from Bool.eq_false_iff.mpr hb74, Bool.false_eq_true, ↓reduceIte] at hWant
              by_cases hb66 : b == 0x66
              · simp only [show bytes[p] == 0x66 from hb66, ↓reduceIte] at hWant
                by_cases hkw : matchesKeyword bytes p kwFalse = true
                · simp only [hkw, ↓reduceIte] at hWant
                  split at hWant <;> try cases hWant
                  rename_i hEnd
                  obtain ⟨csAfter, hcsPEq, hsAfter⟩ :=
                    (matchesKeyword_ascii_spec ['f', 'a', 'l', 's', 'e'] (by decide) hsP).mp hkw
                  have hRen : renderVal (.bool false) (.bool wb "") = some (wb ++ "false") := by
                    unfold renderVal; simp [hwb]; rfl
                  have hDec : (bytes.size - (p + 5)) * 2 < fuel := by omega
                  obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
                    (ih ((bytes.size - (p + 5)) * 2) hDec).2 hEnd (Nat.le_refl _) hsAfter hStack
                      (by simp [wellFormedJsonBool]) (by simp [withinResourceLimitsBool]) hRen hWant
                  refine ⟨hWfOut, tape, hLimOut, ?_⟩
                  have h1 : String.ofList csP = "false" ++ String.ofList csAfter := by
                    rw [hcsPEq, String.ofList_append]
                  have hStrEq : stackPref ++ (wb ++ "false") ++ String.ofList csAfter = stackPref ++ String.ofList cs := by
                    simp [wb, hcsEq0, String.ofList_append, h1, String.append_assoc]
                  rwa [← hStrEq]
                · simp [hkw] at hWant
              · simp only [show (bytes[p] == 0x66) = false from Bool.eq_false_iff.mpr hb66, Bool.false_eq_true, ↓reduceIte] at hWant
                by_cases hb6e : b == 0x6e
                · simp only [show bytes[p] == 0x6e from hb6e, ↓reduceIte] at hWant
                  by_cases hkw : matchesKeyword bytes p kwNull = true
                  · simp only [hkw, ↓reduceIte] at hWant
                    split at hWant <;> try cases hWant
                    rename_i hEnd
                    obtain ⟨csAfter, hcsPEq, hsAfter⟩ :=
                      (matchesKeyword_ascii_spec ['n', 'u', 'l', 'l'] (by decide) hsP).mp hkw
                    have hRen : renderVal .null (.null wb "") = some (wb ++ "null") := by
                      unfold renderVal; simp [hwb]; rfl
                    have hDec : (bytes.size - (p + 4)) * 2 < fuel := by omega
                    obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
                      (ih ((bytes.size - (p + 4)) * 2) hDec).2 hEnd (Nat.le_refl _) hsAfter hStack
                        (by simp [wellFormedJsonBool]) (by simp [withinResourceLimitsBool]) hRen hWant
                    refine ⟨hWfOut, tape, hLimOut, ?_⟩
                    have h1 : String.ofList csP = "null" ++ String.ofList csAfter := by
                      rw [hcsPEq, String.ofList_append]
                    have hStrEq : stackPref ++ (wb ++ "null") ++ String.ofList csAfter = stackPref ++ String.ofList cs := by
                      simp [wb, hcsEq0, String.ofList_append, h1, String.append_assoc]
                    rwa [← hStrEq]
                  · simp [hkw] at hWant
                · simp only [show (bytes[p] == 0x6e) = false from Bool.eq_false_iff.mpr hb6e, Bool.false_eq_true, ↓reduceIte] at hWant
                  by_cases hbNum : (bytes[p]'hLt == 0x2d || (0x30 ≤ bytes[p]'hLt && bytes[p]'hLt ≤ 0x39)) = true
                  · simp only [hbNum, ↓reduceIte] at hWant
                    match hNumP : parseNumberAt bytes p with
                    | .error _ => simp [hNumP] at hWant
                    | .ok ⟨n, ⟨p1, hp1a, hp1b⟩⟩ =>
                    rw [hNumP] at hWant; dsimp only at hWant
                    obtain ⟨nt, csAfter, hvnt, hlimNt, hevalNt, hcsPEq, hsAfter⟩ := parseNumberAt_complete hsP hNumP
                    dsimp only at hsAfter
                    have hRen : renderVal (.num n) (.num wb nt "") = some (wb ++ renderNumTape nt) := by
                      have heqvB : numEquivBool n (evalNumTape nt) = true := by
                        rw [numEquivBool_iff, hevalNt]; exact numEquiv_refl n
                      unfold renderVal renderNum; simp [hwb, hvnt, heqvB]; rfl
                    have hDec : (bytes.size - p1) * 2 < fuel := by omega
                    obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
                      (ih ((bytes.size - p1) * 2) hDec).2 hp1b (Nat.le_refl _) hsAfter hStack (by simp [wellFormedJsonBool]) (by simp [withinResourceLimitsBool, hlimNt]) hRen hWant
                    refine ⟨hWfOut, tape, hLimOut, ?_⟩
                    have hStrEq : stackPref ++ (wb ++ renderNumTape nt) ++ String.ofList csAfter = stackPref ++ String.ofList cs := by
                      simp [wb, hcsEq0, hcsPEq, String.ofList_append, String.ofList_toList, String.append_assoc]
                    rwa [← hStrEq]
                  · simp [hbNum] at hWant
    · intro bytes pos hPos frames val valTape valStr cs stackPref out hFuel hSlice hStack hWfVal hLimVal hRenVal hAfter
      unfold parseAfterValue at hAfter
      have hSp := skipWsSub_spec cs hPos hSlice
      have hSpProps := splitJsonWs_props cs
      rcases hSub : skipWsSub bytes pos hPos with ⟨p, hpGe, hpLe⟩
      rcases hSplit : splitJsonWs cs with ⟨wsA, csP⟩
      rw [hSub] at hAfter; rw [hSub, hSplit] at hSp; rw [hSplit] at hSpProps
      rcases hSp with ⟨_, hwsA, _, hsP⟩
      dsimp only at hsP hSpProps hAfter
      let wa := String.ofList wsA
      let valTape' := appendWsAfter valTape wa
      let valStr' := valStr ++ wa
      have hLimVal' : withinResourceLimitsBool valTape' = true := by
        rw [withinLimits_appendWsAfter]; exact hLimVal
      have hRenVal' : renderVal val valTape' = some valStr' :=
        renderVal_appendWsAfter hRenVal hwsA
      cases hStack with
      | nil =>
        by_cases hEof : p == bytes.size
        · simp only [hEof, ↓reduceIte, Except.ok.injEq] at hAfter
          subst hAfter
          have hEmptyCsP : csP = [] := by
            have hs := byteSliceAt_size hsP
            have hpSz := beq_iff_eq.mp hEof
            have h0 : csP.utf8Encode.size = 0 := by omega
            exact List.utf8Encode_eq_empty.mp (ByteArray.size_eq_zero_iff.mp h0)
          refine ⟨hWfVal, valTape', hLimVal', ?_⟩
          have hStrEq : "" ++ valStr ++ String.ofList cs = valStr' := by
            simp [valStr', wa, hSpProps.1, hEmptyCsP]
          rwa [hStrEq]
        · simp [hEof] at hAfter
      | @cons topFrame restFrames outerPref framePref hOuter hTop =>
        cases topFrame with
        | arr elems =>
          dsimp only at hAfter
          split at hAfter <;> try cases hAfter
          rename_i hLt
          obtain ⟨wb, ts', parts', hwb, hNotEmp', hWfList', hLimTs', hRenTs', hPartsNe', hPrefJoin⟩ :=
            validFrame_arr_step hTop hWfVal hLimVal' hRenVal'
          by_cases hb5d : bytes[p]'hLt == 0x5d
          · simp only [hb5d, ↓reduceIte] at hAfter
            have hbEq := beq_iff_eq.mp hb5d
            obtain ⟨closeCh, csAfterClose, rfl, hcloseNat, _, hsAfterClose⟩ :=
              byteSliceAt_head_lt_128 hsP hLt (by rw [hbEq]; decide)
            have hcloseEq : closeCh = ']' := by
              apply Char.ext; apply UInt32.toNat_inj.mp; change closeCh.toNat = (']').toNat; rw [hcloseNat, hbEq]; rfl
            subst hcloseEq
            let arrTape : RenderTape := .arr wb ts' ""
            let arrStr := wb ++ "[" ++ String.intercalate "," parts' ++ "]"
            have hRenArr : renderVal (.arr (elems.push val)) arrTape = some arrStr := by
              dsimp only [arrTape]; unfold renderVal
              have hNotEmpB : (elems.push val).isEmpty = false := by
                cases h : (elems.push val).isEmpty with
                | false => rfl
                | true => rw [h] at hNotEmp'; cases hNotEmp'
              have hc : (!(elems.push val).isEmpty && isJsonWs wb && isJsonWs "") = true := by
                rw [hNotEmpB, hwb]; rfl
              rw [ite_eq_left hc, hRenTs']
              dsimp only [bind, Option.bind, arrStr]; rw [String.append_empty]
            have hDec : (bytes.size - (p + 1)) * 2 < fuel := by omega
            obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
              (ih ((bytes.size - (p + 1)) * 2) hDec).2 hLt (Nat.le_refl _) hsAfterClose hOuter
                (by rw [wellFormedJsonBool]; exact hWfList')
                (by dsimp only [arrTape]; rw [withinResourceLimitsBool]; exact hLimTs') hRenArr hAfter
            refine ⟨hWfOut, tape, hLimOut, ?_⟩
            have hStrEq : outerPref ++ arrStr ++ String.ofList csAfterClose =
                (outerPref ++ framePref) ++ valStr ++ String.ofList cs := by
              have hCsEq : String.ofList cs = String.ofList wsA ++ ("]" ++ String.ofList csAfterClose) := by
                rw [hSpProps.1, String.ofList_append, show (']' :: csAfterClose) = [']'] ++ csAfterClose from rfl,
                  String.ofList_append]
              dsimp only [arrStr]; dsimp only [valStr', wa] at hPrefJoin
              rw [← hPrefJoin, hCsEq]; simp only [String.append_assoc]
            rwa [← hStrEq]
          · simp only [hb5d, Bool.false_eq_true, ↓reduceIte] at hAfter
            by_cases hb2c : bytes[p]'hLt == 0x2c
            · simp only [hb2c, ↓reduceIte] at hAfter
              have hbEq := beq_iff_eq.mp hb2c
              obtain ⟨commaCh, csAfterComma, rfl, hcommaNat, _, hsAfterComma⟩ :=
                byteSliceAt_head_lt_128 hsP hLt (by rw [hbEq]; decide)
              have hcommaEq : commaCh = ',' := by
                apply Char.ext; apply UInt32.toNat_inj.mp; change commaCh.toNat = (',').toNat; rw [hcommaNat, hbEq]; rfl
              subst hcommaEq
              let nextFramePref := wb ++ "[" ++ String.intercalate "," parts' ++ ","
              have hNextFrame : ValidFrame (.arr (elems.push val)) nextFramePref := by
                simp only [ValidFrame]
                have hEmpF : ¬((elems.push val).isEmpty = true) := by
                  intro h; rw [h] at hNotEmp'; cases hNotEmp'
                rw [ite_eq_right hEmpF]
                exact ⟨wb, ts', parts', hwb, hWfList', hLimTs', hRenTs', hPartsNe', rfl⟩
              have hDec : (bytes.size - (p + 1)) * 2 + 1 < fuel := by omega
              obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
                (ih ((bytes.size - (p + 1)) * 2 + 1) hDec).1 hLt (Nat.le_refl _) hsAfterComma (.cons hOuter hNextFrame) hAfter
              refine ⟨hWfOut, tape, hLimOut, ?_⟩
              have hStrEq : (outerPref ++ nextFramePref) ++ String.ofList csAfterComma =
                  (outerPref ++ framePref) ++ valStr ++ String.ofList cs := by
                have hCsEq : String.ofList cs = String.ofList wsA ++ ("," ++ String.ofList csAfterComma) := by
                  rw [hSpProps.1, String.ofList_append, show (',' :: csAfterComma) = [','] ++ csAfterComma from rfl,
                    String.ofList_append]
                dsimp only [nextFramePref]; dsimp only [valStr', wa] at hPrefJoin
                rw [← hPrefJoin, hCsEq]; simp only [String.append_assoc]
              rwa [← hStrEq]
            · simp [hb2c] at hAfter
        | obj kvs key =>
          dsimp only at hAfter
          let kvs' := kvs.insert key val
          split at hAfter <;> try cases hAfter
          rename_i hLt
          rcases hTop with ⟨wb, prior, priorParts, curKt, curRk, hwfKvs, hvalsKvs, hNotMemKey,
            hwb, hcurKeyEq, hwsCurK, hwsCurC, hcurRk, hndPrior, hMemPrior, hLimPrior, hRenPrior, hfpEq⟩
          subst hcurKeyEq
          obtain ⟨hwfKvs', hWfObj', hvalsKvs'⟩ := wf_insert_wellFormed hwfKvs hvalsKvs curKt.key hWfVal
          have hKeyNotInPrior : curKt.key ∉ prior.map (fun p => p.1.key) := by
            rw [← hMemPrior curKt.key, hNotMemKey]; simp
          have hFreshPrior : ∀ p ∈ prior, p.1.key ≠ curKt.key :=
            fun p hp heq => hKeyNotInPrior (heq ▸ List.mem_map_of_mem hp)
          let curPart := curKt.wsBeforeKey ++ curRk ++ curKt.wsBeforeColon ++ ":" ++ valStr'
          let allPrior := prior ++ [(curKt, valTape')]
          let allParts := priorParts ++ [curPart]
          have hRenAll := renderObjEntries_snoc_insert hwfKvs hRenPrior hFreshPrior hwsCurK hwsCurC hcurRk hRenVal'
          have hLimAll := withinLimitsObj_snoc curKt hLimPrior hLimVal'
          have hndAll : (allPrior.map (fun p => p.1.key)).Nodup := by
            rw [List.map_append, List.nodup_append]
            exact ⟨hndPrior, by simp [List.Nodup], fun x hx y hy heq => by
              simp at hy; subst hy heq; exact hKeyNotInPrior hx⟩
          have hMemAll : ∀ q : String, kvs'.contains q = true ↔ q ∈ allPrior.map (fun p => p.1.key) := by
            intro q
            rw [Std.TreeMap.Raw.contains_insert hwfKvs, Bool.or_eq_true, beq_iff_eq,
              Std.LawfulEqCmp.compare_eq_iff_eq, hMemPrior q, List.map_append, List.mem_append,
              List.map_singleton, List.mem_singleton]
            exact ⟨fun h => h.elim (fun h1 => Or.inr h1.symm) Or.inl,
              fun h => h.elim Or.inr (fun h1 => Or.inl h1.symm)⟩
          have hPrefObjJoin : framePref ++ valStr' = wb ++ "{" ++ String.intercalate "," allParts := by
            cases hpp : priorParts with
            | nil =>
              simp only [allParts, hpp, List.nil_append, String.intercalate_singleton]
              rw [hfpEq, hpp]; simp [curPart, String.append_assoc]
            | cons p0 ptl =>
              have hnePP : p0 :: ptl ≠ [] := by simp
              dsimp only [allParts]
              rw [hpp, intercalate_comma_snoc hnePP, hfpEq, hpp]
              simp [curPart, String.append_assoc]
          by_cases hb7d : bytes[p]'hLt == 0x7d
          · simp only [hb7d, ↓reduceIte] at hAfter
            have hbEq := beq_iff_eq.mp hb7d
            obtain ⟨closeCh, csAfterClose, rfl, hcloseNat, _, hsAfterClose⟩ :=
              byteSliceAt_head_lt_128 hsP hLt (by rw [hbEq]; decide)
            have hcloseEq : closeCh = '}' := by
              apply Char.ext; apply UInt32.toNat_inj.mp; change closeCh.toNat = ('}').toNat; rw [hcloseNat, hbEq]; rfl
            subst hcloseEq
            have hPerm := isObjPlanPerm_of_wf_mem hwfKvs' hndAll hMemAll
            have hNotEmpEntries : (objEntries kvs').isEmpty = false := by
              have hIn : curKt.key ∈ (objEntries kvs').map Prod.fst := by
                rw [← hasKeyList_iff_mem, ← lookupKeyList_isSome_iff_hasKeyList,
                  wf_lookupKeyList_eq_get? hwfKvs', Std.TreeMap.Raw.get?_eq_getElem?,
                  Std.TreeMap.Raw.getElem?_insert_self hwfKvs]
                rfl
              cases he : objEntries kvs' with
              | nil => rw [he] at hIn; cases hIn
              | cons _ _ => rfl
            let objTape : RenderTape := .obj wb allPrior ""
            let objStr := wb ++ "{" ++ String.intercalate "," allParts ++ "}"
            have hRenObj : renderVal (.obj kvs') objTape = some objStr := by
              dsimp only [objTape]; unfold renderVal; dsimp only
              have hc : (!(objEntries kvs').isEmpty && isJsonWs wb && isJsonWs "" &&
                  isObjPlanPerm (objEntries kvs') allPrior) = true := by
                rw [hNotEmpEntries, hwb, show isJsonWs "" = true from rfl]
                dsimp only [kvs', Bool.not_false, Bool.and_true, Bool.true_and]; exact hPerm
              rw [ite_eq_left hc]
              dsimp only [kvs', allPrior, allParts, curPart] at hRenAll ⊢
              rw [hRenAll]; dsimp only [bind, Option.bind, objStr, allParts, curPart]; rw [String.append_empty]
            have hDec : (bytes.size - (p + 1)) * 2 < fuel := by omega
            obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
              (ih ((bytes.size - (p + 1)) * 2) hDec).2 hLt (Nat.le_refl _) hsAfterClose hOuter hWfObj'
                (by dsimp only [objTape, allPrior]; rw [withinResourceLimitsBool]; exact hLimAll) hRenObj hAfter
            refine ⟨hWfOut, tape, hLimOut, ?_⟩
            have hStrEq : outerPref ++ objStr ++ String.ofList csAfterClose =
                (outerPref ++ framePref) ++ valStr ++ String.ofList cs := by
              have hCsEq : String.ofList cs = String.ofList wsA ++ ("}" ++ String.ofList csAfterClose) := by
                rw [hSpProps.1, String.ofList_append, show ('}' :: csAfterClose) = ['}'] ++ csAfterClose from rfl,
                  String.ofList_append]
              dsimp only [objStr]; dsimp only [valStr', wa] at hPrefObjJoin
              rw [← hPrefObjJoin, hCsEq]; simp only [String.append_assoc]
            rwa [← hStrEq]
          · simp only [hb7d, Bool.false_eq_true, ↓reduceIte] at hAfter
            by_cases hb2c : bytes[p]'hLt == 0x2c
            · simp only [hb2c, ↓reduceIte] at hAfter
              have hbEq := beq_iff_eq.mp hb2c
              obtain ⟨commaCh, csAfterComma, rfl, hcommaNat, _, hsAfterComma⟩ :=
                byteSliceAt_head_lt_128 hsP hLt (by rw [hbEq]; decide)
              have hcommaEq : commaCh = ',' := by
                apply Char.ext; apply UInt32.toNat_inj.mp; change commaCh.toNat = (',').toNat; rw [hcommaNat, hbEq]; rfl
              subst hcommaEq
              have hSp1 := skipWsSub_spec csAfterComma hLt hsAfterComma
              have hSpProps1 := splitJsonWs_props csAfterComma
              rcases hSub1 : skipWsSub bytes (p + 1) hLt with ⟨p1, hp1Ge, hp1Le⟩
              rcases hSplit1 : splitJsonWs csAfterComma with ⟨wsNextK, csP1⟩
              rw [hSub1] at hAfter; rw [hSub1, hSplit1] at hSp1; rw [hSplit1] at hSpProps1
              rcases hSp1 with ⟨_, hwsNextK, _, hsP1⟩
              dsimp only at hsP1 hSpProps1 hAfter
              match hKeyP : parseStringAt bytes p1 with
              | .error _ => simp [hKeyP] at hAfter
              | .ok ⟨nextKey, ⟨p2, hp2a, hp2b⟩⟩ =>
              rw [hKeyP] at hAfter; obtain ⟨nextStyles, nextRk, csP2, hcsP1Eq, hNextRk, hsP2⟩ := parseStringAt_complete hsP1 hKeyP
              dsimp only at hsP2 hAfter
              by_cases hDup : (kvs.insert curKt.key val).contains nextKey = true
              · rw [ite_eq_left hDup] at hAfter; cases hAfter
              · rw [ite_eq_right hDup] at hAfter
                have hDupF : kvs'.contains nextKey = false := Bool.eq_false_iff.mpr hDup
                have hSp3 := skipWsSub_spec csP2 hp2b hsP2
                have hSpProps3 := splitJsonWs_props csP2
                rcases hSub3 : skipWsSub bytes p2 hp2b with ⟨p3, hp3Ge, hp3Le⟩
                rcases hSplit3 : splitJsonWs csP2 with ⟨wsNextC, csP3⟩
                rw [hSub3] at hAfter; rw [hSub3, hSplit3] at hSp3; rw [hSplit3] at hSpProps3
                rcases hSp3 with ⟨_, hwsNextC, _, hsP3⟩
                dsimp only at hsP3 hSpProps3 hAfter
                split at hAfter <;> try cases hAfter
                rename_i hCol
                by_cases hbCol : bytes[p3]'hCol == 0x3a
                · simp only [hbCol, ↓reduceIte] at hAfter
                  have hbEqCol := beq_iff_eq.mp hbCol
                  obtain ⟨colCh, csValNext, rfl, hcolNat, _, hsValNext⟩ :=
                    byteSliceAt_head_lt_128 hsP3 hCol (by rw [hbEqCol]; decide)
                  have hcolEq : colCh = ':' := by
                    apply Char.ext; apply UInt32.toNat_inj.mp; change colCh.toNat = (':').toNat; rw [hcolNat, hbEqCol]; rfl
                  subst hcolEq
                  let nextKt : ObjKeyTape := ⟨String.ofList wsNextK, nextKey, nextStyles, String.ofList wsNextC⟩
                  let nextFramePref := wb ++ "{" ++
                    (String.intercalate "," allParts ++ ",") ++
                    nextKt.wsBeforeKey ++ nextRk ++ nextKt.wsBeforeColon ++ ":"
                  have hNextFrame : ValidFrame (.obj kvs' nextKey) nextFramePref :=
                    ⟨wb, allPrior, allParts, nextKt, nextRk, hwfKvs', hvalsKvs', hDupF,
                      hwb, rfl, hwsNextK, hwsNextC, hNextRk, hndAll, hMemAll, hLimAll, hRenAll,
                      by cases priorParts <;> rfl⟩
                  have hDec : (bytes.size - (p3 + 1)) * 2 + 1 < fuel := by omega
                  obtain ⟨hWfOut, tape, hLimOut, hRenOut⟩ :=
                    (ih ((bytes.size - (p3 + 1)) * 2 + 1) hDec).1 hCol (Nat.le_refl _) hsValNext (.cons hOuter hNextFrame) hAfter
                  refine ⟨hWfOut, tape, hLimOut, ?_⟩
                  have hStrEq : (outerPref ++ nextFramePref) ++ String.ofList csValNext =
                      (outerPref ++ framePref) ++ valStr ++ String.ofList cs := by
                    have hCsEq : String.ofList cs =
                        String.ofList wsA ++ ("," ++ (String.ofList wsNextK ++
                          (nextRk ++ (String.ofList wsNextC ++ (":" ++ String.ofList csValNext))))) := by
                      have hConsComma : (',' :: csAfterComma) = [','] ++ csAfterComma := rfl
                      have hConsCol : (':' :: csValNext) = [':'] ++ csValNext := rfl
                      rw [hSpProps.1, String.ofList_append, hConsComma, String.ofList_append,
                        hSpProps1.1, String.ofList_append, hcsP1Eq, String.ofList_append, String.ofList_toList,
                        hSpProps3.1, String.ofList_append, hConsCol, String.ofList_append]
                    dsimp only [nextFramePref, nextKt]; dsimp only [valStr', wa] at hPrefObjJoin
                    have hJoinComma : wb ++ "{" ++ (String.intercalate "," allParts ++ ",") =
                        (framePref ++ (valStr ++ String.ofList wsA)) ++ "," := by
                      rw [← String.append_assoc, ← hPrefObjJoin]
                    rw [hJoinComma, hCsEq]; simp only [String.append_assoc]
                  rwa [← hStrEq]
                · simp [hbCol] at hAfter
            · simp [hb2c] at hAfter

/-- Completeness of `LeanSwe.Json.parse`: every `.ok out` is `WellFormedJson` and witnessed by a resource-bounded `RenderTape`. -/
theorem parse_ok_complete {raw : String} {out : Lean.Json}
    (h : LeanSwe.Json.parse raw = .ok out) :
    WellFormedJson out ∧ ∃ tape : RenderTape, withinResourceLimits tape ∧ render out tape = some raw := by
  simp only [LeanSwe.Json.parse, Internal.parse] at h
  cases hPure : Internal.parsePure raw with
  | error _ => simp [hPure] at h
  | ok parsed =>
    simp only [hPure, Except.ok.injEq] at h; subst h
    obtain ⟨hWf, tape, hLim, hRen⟩ :=
      (parse_mutual_complete (raw.toUTF8.size * 2 + 1)).1 (Nat.zero_le _)
        (Nat.le_refl _) (byteSliceAt_toUTF8_zero raw) .nil hPure
    simp only [String.empty_append, String.ofList_toList] at hRen
    exact ⟨hWf, tape, hLim, by simp [render, hWf, hRen]⟩

/-- `LeanSwe.Json.parse` obeys `Core.ObeysInverseRenderWithin` over pure RFC 8259 `Model.render` and `Model.withinResourceLimits`. -/
theorem parse_obeys_inverse_render :
    Core.ObeysInverseRenderWithin LeanSwe.Json.parse Model.render
      Model.withinResourceLimits Model.WellFormedJson Model.JsonEquiv JsonError.message :=
  Core.ObeysInverseRenderWithin.of_injective render_injective
    (fun _ _ hp => let ⟨hwf, t, _, hr⟩ := parse_ok_complete hp; ⟨hwf, t, hr⟩)
    (fun _ _ hp => ⟨(parse_error_kind_and_nonempty hp).2,
      fun _ _ hRen hLim => by
        obtain ⟨_, hOk, _, _⟩ := render_parse_roundTrip hLim hRen; rw [hp] at hOk; cases hOk⟩)

end LeanSwe.Json.Proofs
