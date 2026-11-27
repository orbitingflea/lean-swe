import Lean.Data.Json.Basic
import LeanSwe.Json.Impl
import LeanSweProofs.Json.Model
import LeanSweProofs.Json.Proofs.ScalarLex
import LeanSweProofs.Json.Proofs.Utf8Ws
import LeanSweProofs.Json.Proofs.DigitsScan
import LeanSweProofs.Json.Proofs.NumberParse

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

private theorem parseNumberWhole_complete {bytes : ByteArray} {pos p0 : Nat}
    {hp0Ge : pos ≤ p0} {h1 : p0 < bytes.size} {cs0 : List Char}
    {whole : Nat} {p1Sub : { p : Nat // pos < p ∧ p ≤ bytes.size }}
    (hsP0 : ByteSliceAt bytes p0 cs0)
    (hW : parseNumberWhole bytes pos p0 hp0Ge h1 = .ok (whole, p1Sub)) :
    ∃ cs1, cs0 = whole.repr.toList ++ cs1 ∧ ByteSliceAt bytes p1Sub.1 cs1 := by
  unfold parseNumberWhole at hW
  dsimp only at hW
  let b0 := bytes[p0]'h1
  by_cases hb30 : b0 == 0x30
  · simp only [show bytes[p0] == 0x30 from hb30, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hW
    rcases hW with ⟨rfl, rfl⟩
    have hbEq : bytes[p0]'h1 = 0x30 := beq_iff_eq.mp hb30
    obtain ⟨c0, tl0, rfl, hc0, _, hs1⟩ := byteSliceAt_head_lt_128 hsP0 h1 (by rw [hbEq]; decide)
    have hc0Eq : c0 = '0' := by apply Char.ext; apply UInt32.toNat_inj.mp; change c0.toNat = ('0').toNat; rw [hc0, hbEq]; rfl
    subst hc0Eq
    exact ⟨tl0, rfl, hs1⟩
  · simp only [show (bytes[p0] == 0x30) = false from Bool.eq_false_iff.mpr hb30, Bool.false_eq_true, ↓reduceIte] at hW
    by_cases hb19 : (0x31 ≤ b0 && b0 ≤ 0x39) = true
    · simp only [show (0x31 ≤ bytes[p0] && bytes[p0] ≤ 0x39) = true from hb19, ↓reduceIte] at hW
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hb19
      dsimp only [b0] at hb19
      change 49 ≤ (bytes[p0]'h1).toNat ∧ (bytes[p0]'h1).toNat ≤ 57 at hb19
      obtain ⟨c0, tl0, rfl, hc0, _, hs1⟩ := byteSliceAt_head_lt_128 hsP0 h1
        (by rw [UInt8.lt_iff_toNat_lt]; change (bytes[p0]'h1).toNat < 128; omega)
      have hScan := scanDigits_intTail_spec h1 (by omega) ((bytes[p0]'h1).toNat - 0x30) (by omega) hs1
      have hspP := spanDigits_props hs1
      rcases hsp : spanDigits tl0 with ⟨ds, cs1⟩
      rw [hsp] at hScan hspP
      rcases hRes : scanDigits bytes (p0 + 1) h1 (b0.toNat - 0x30) 1 bytes.size false 0 with ⟨w, cnt, pSub⟩
      rw [hRes] at hScan hW
      dsimp only at hScan hspP
      simp only [Except.ok.injEq, Prod.mk.injEq] at hW
      rcases hW with ⟨rfl, rfl⟩
      rcases hScan with ⟨hwEq, _, _, hsP1⟩
      have hc019 : '1' ≤ c0 ∧ c0 ≤ '9' := by
        simp only [Char.le_def, UInt32.le_iff_toNat_le]; change 0x31 ≤ c0.toNat ∧ c0.toNat ≤ 0x39; omega
      have hwRepr : w.repr.toList = c0 :: ds := by
        have hwLoop : w = parseDecDigitsLoop 0 (c0 :: ds) := by
          simp only [parseDecDigitsLoop_cons, Nat.zero_mul, Nat.zero_add, hc0]; exact hwEq
        rw [hwLoop]; exact repr_of_nonZeroHeadDigits hc019 hspP.2.1
      exact ⟨cs1, by rw [hwRepr, List.cons_append, hspP.1], hsP1⟩
    · simp [show (0x31 ≤ bytes[p0] && bytes[p0] ≤ 0x39) = false from Bool.eq_false_iff.mpr hb19] at hW

private theorem parseNumberFrac_complete {bytes : ByteArray} {pos : Nat} {sign : Int} {whole : Nat}
    {p1Sub : { p : Nat // pos < p ∧ p ≤ bytes.size }} {cs1 : List Char}
    {baseNum : Lean.JsonNumber} {p2Sub : { p : Nat // pos < p ∧ p ≤ bytes.size }}
    (hsP1 : ByteSliceAt bytes p1Sub.1 cs1)
    (hF : parseNumberFrac bytes pos sign whole p1Sub = .ok (baseNum, p2Sub)) :
    ∃ (frac? : Option String) (cs2 : List Char),
      (match frac? with | none => true | some f => isNonEmptyDigits f) = true ∧
      (match frac? with | none => 0 | some f => f.toList.length) ≤ maxFracDigits ∧
      baseNum = (match frac? with
        | none => Lean.JsonNumber.fromInt (sign * whole)
        | some f => Lean.JsonNumber.mk (sign * (whole * (10 ^ f.toList.length) + parseDecDigits f)) f.toList.length) ∧
      cs1 = (match frac? with | none => "" | some f => "." ++ f).toList ++ cs2 ∧
      ByteSliceAt bytes p2Sub.1 cs2 := by
  unfold parseNumberFrac at hF
  dsimp only at hF
  by_cases hDot : p1Sub.1 < bytes.size
  · simp only [hDot, ↓reduceDIte] at hF
    by_cases hbDot : (bytes[p1Sub.1]'hDot == 0x2e) = true
    · simp only [hbDot, ↓reduceIte] at hF
      have hbEq := beq_iff_eq.mp hbDot
      obtain ⟨dotC, afterDot, rfl, hdotNat, _, hsAfterDot⟩ := byteSliceAt_head_lt_128 hsP1 hDot (by rw [hbEq]; decide)
      have hdotEq : dotC = '.' := by apply Char.ext; apply UInt32.toNat_inj.mp; change dotC.toNat = ('.').toNat; rw [hdotNat, hbEq]; rfl
      subst hdotEq
      have hScan := scanDigits_frac_spec hDot hsAfterDot
      have hspP := spanDigits_props hsAfterDot
      rcases hsp : spanDigits afterDot with ⟨fDs, cs2⟩
      rw [hsp] at hScan hspP
      rcases hRes : scanDigits bytes (p1Sub.1 + 1) hDot 0 0 100_000 false 0 with ⟨frac, d, pSub⟩
      rw [hRes] at hScan hF
      dsimp only at hScan hspP hF
      by_cases hle : fDs.length ≤ 100_000
      · rw [ite_eq_left hle] at hScan
        rcases hScan with ⟨hfracEq, hdEq, _, hsP2⟩
        by_cases hd0 : d == 0
        · simp [hd0] at hF
        · have hNotGt : ¬(d > 100_000) := by omega
          simp only [hd0, Bool.false_eq_true, hNotGt, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hF
          rcases hF with ⟨rfl, rfl⟩
          have hfNe : fDs.isEmpty = false := by
            cases fDs with | nil => simp at hdEq; simp [hdEq] at hd0 | cons _ _ => rfl
          refine ⟨some (String.ofList fDs), cs2, ?_, ?_, ?_, ?_, hsP2⟩
          · simp [isNonEmptyDigits, String.toList_ofList, hfNe, hspP.2.1]
          · simp [String.toList_ofList, maxFracDigits, hle]
          · simp [String.toList_ofList, parseDecDigits, hdEq, hfracEq]
          · simp [String.toList_append, String.toList_ofList, hspP.1]
      · rw [ite_eq_right hle] at hScan
        simp [hScan] at hF
    · simp only [hbDot, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hF
      rcases hF with ⟨rfl, rfl⟩
      exact ⟨none, cs1, rfl, Nat.zero_le _, rfl, rfl, hsP1⟩
  · simp only [hDot, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at hF
    rcases hF with ⟨rfl, rfl⟩
    exact ⟨none, cs1, rfl, Nat.zero_le _, rfl, rfl, hsP1⟩

/-- Completeness of `parseNumberAt` on `ByteSliceAt`, producing a valid, resource-bounded `NumTape`. -/
theorem parseNumberAt_complete {bytes : ByteArray} {pos : Nat} {cs : List Char}
    {n : Lean.JsonNumber} {pOut : { p : Nat // pos < p ∧ p ≤ bytes.size }}
    (hSlice : ByteSliceAt bytes pos cs) (hParse : parseNumberAt bytes pos = .ok (n, pOut)) :
    ∃ (nt : NumTape) (after : List Char),
      validNumTape nt = true ∧
      numTapeWithinLimits nt = true ∧
      evalNumTape nt = n ∧
      cs = (renderNumTape nt).toList ++ after ∧
      ByteSliceAt bytes pOut.1 after := by
  unfold parseNumberAt at hParse
  split at hParse <;> try cases hParse
  rename_i hlt0
  let neg := bytes[pos]'hlt0 == 0x2d
  let p0 := if neg then pos + 1 else pos
  let sign : Int := if neg then -1 else 1
  have hSignSplit : ∃ csAfterSign,
      cs = (if neg then ['-'] else []) ++ csAfterSign ∧
      ByteSliceAt bytes p0 csAfterSign := by
    by_cases hneg : neg = true
    · have hbEq : bytes[pos]'hlt0 = 0x2d := beq_iff_eq.mp hneg
      obtain ⟨c0, tl0, rfl, hc0, _, hs1⟩ := byteSliceAt_head_lt_128 hSlice hlt0 (by rw [hbEq]; decide)
      have hc0Eq : c0 = '-' := by apply Char.ext; apply UInt32.toNat_inj.mp; change c0.toNat = ('-').toNat; rw [hc0, hbEq]; rfl
      subst hc0Eq
      exact ⟨tl0, by simp [hneg], by simpa [p0, hneg] using hs1⟩
    · simp only [Bool.not_eq_true] at hneg
      exact ⟨cs, by simp [hneg], by simpa [p0, hneg] using hSlice⟩
  obtain ⟨cs0, hcsEq0, hsP0⟩ := hSignSplit
  have hltP0 : p0 < bytes.size := by
    apply Decidable.byContradiction
    intro hn
    dsimp only [p0, neg] at hn
    simp only [hn, ↓reduceDIte] at hParse
    cases hParse
  have hp0Ge : pos ≤ p0 := by dsimp [p0]; split <;> omega
  have hIf1 : (if h1 : p0 < bytes.size then
      match parseNumberWhole bytes pos p0 hp0Ge h1 with
      | Except.error e => Except.error e
      | Except.ok (whole, p1Sub) =>
        match parseNumberFrac bytes pos sign whole p1Sub with
        | Except.error e => Except.error e
        | Except.ok (baseNum, p2Sub) => parseNumberExp bytes pos baseNum p2Sub
    else Except.error "unexpected end of input in number") = Except.ok (n, pOut) := hParse
  clear hParse
  simp only [hltP0, ↓reduceDIte] at hIf1
  have hParse := hIf1; clear hIf1
  obtain ⟨res1, hWholeOk⟩ : ∃ res1, parseNumberWhole bytes pos p0 hp0Ge hltP0 = .ok res1 := by
    cases h : parseNumberWhole bytes pos p0 hp0Ge hltP0 with
    | error _ => rw [h] at hParse; cases hParse
    | ok r => exact ⟨r, rfl⟩
  rw [hWholeOk] at hParse; dsimp only at hParse
  rcases res1 with ⟨whole, p1Sub⟩
  obtain ⟨cs1, hcs0Eq, hsP1⟩ := parseNumberWhole_complete hsP0 hWholeOk
  obtain ⟨res2, hFracOk⟩ : ∃ res2, parseNumberFrac bytes pos sign whole p1Sub = .ok res2 := by
    cases h : parseNumberFrac bytes pos sign whole p1Sub with
    | error _ => rw [h] at hParse; cases hParse
    | ok r => exact ⟨r, rfl⟩
  rw [hFracOk] at hParse; dsimp only at hParse
  rcases res2 with ⟨baseNum, p2Sub⟩
  obtain ⟨frac?, cs2, hFracVal, hFracLim, hBaseEq, hcs1Eq, hsP2⟩ := parseNumberFrac_complete hsP1 hFracOk
  unfold parseNumberExp at hParse
  dsimp only at hParse
  let p2 := p2Sub.1
  by_cases hExpLt : p2 < bytes.size
  · simp only [show p2Sub.1 < bytes.size from hExpLt, ↓reduceDIte] at hParse
    by_cases hbE : (bytes[p2]'hExpLt == 0x65 || bytes[p2]'hExpLt == 0x45) = true
    · simp only [show (bytes[p2Sub.1] == 0x65 || bytes[p2Sub.1] == 0x45) = true from hbE, ↓reduceIte] at hParse
      have hbELt : bytes[p2]'hExpLt < 0x80 := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hbE
        rcases hbE with hb1 | hb2
        · rw [hb1]; decide
        · rw [hb2]; decide
      obtain ⟨eCh, cs3, rfl, heNat, _, hsP3⟩ := byteSliceAt_head_lt_128 hsP2 hExpLt hbELt
      let upperE := bytes[p2]'hExpLt == 0x45
      have heChEq : eCh = (if upperE then 'E' else 'e') := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hbE
        rcases hbE with hb1 | hb2
        · have hu : upperE = false := by dsimp [upperE]; rw [hb1]; rfl
          rw [hu]; apply Char.ext; apply UInt32.toNat_inj.mp; change eCh.toNat = ('e').toNat; rw [heNat, hb1]; rfl
        · have hu : upperE = true := by dsimp [upperE]; rw [hb2]; rfl
          rw [hu]; apply Char.ext; apply UInt32.toNat_inj.mp; change eCh.toNat = ('E').toNat; rw [heNat, hb2]; rfl
      let p3 := p2 + 1
      have hSignESplit : ∃ (sgn : ExpSign) (p4Sub : { p : Nat // p3 ≤ p ∧ p ≤ bytes.size }) (cs4 : List Char),
          (if hSign : p3 < bytes.size then
             if bytes[p3]'hSign == 0x2d then (true, (⟨p3 + 1, by omega, hSign⟩ : { p : Nat // p3 ≤ p ∧ p ≤ bytes.size }))
             else if bytes[p3]'hSign == 0x2b then (false, ⟨p3 + 1, by omega, hSign⟩)
             else (false, ⟨p3, Nat.le_refl _, Nat.le_of_lt hSign⟩)
           else (false, ⟨p3, Nat.le_refl _, hExpLt⟩)) = (sgn == .minus, p4Sub) ∧
          cs3 = (renderExpSign sgn).toList ++ cs4 ∧
          ByteSliceAt bytes p4Sub.1 cs4 := by
        by_cases hSign : p3 < bytes.size
        · by_cases hm : (bytes[p3]'hSign == 0x2d) = true
          · have hbEq := beq_iff_eq.mp hm
            obtain ⟨sCh, cs4, rfl, hsNat, _, hsP4⟩ := byteSliceAt_head_lt_128 hsP3 hSign (by rw [hbEq]; decide)
            have hsEq : sCh = '-' := by apply Char.ext; apply UInt32.toNat_inj.mp; change sCh.toNat = ('-').toNat; rw [hsNat, hbEq]; rfl
            subst hsEq
            exact ⟨.minus, ⟨p3 + 1, by omega, hSign⟩, cs4,
              by simp [hSign, hm, (by decide : (ExpSign.minus == .minus) = true)], rfl, hsP4⟩
          · by_cases hp : (bytes[p3]'hSign == 0x2b) = true
            · have hbEq := beq_iff_eq.mp hp
              obtain ⟨sCh, cs4, rfl, hsNat, _, hsP4⟩ := byteSliceAt_head_lt_128 hsP3 hSign (by rw [hbEq]; decide)
              have hsEq : sCh = '+' := by apply Char.ext; apply UInt32.toNat_inj.mp; change sCh.toNat = ('+').toNat; rw [hsNat, hbEq]; rfl
              subst hsEq
              exact ⟨.plus, ⟨p3 + 1, by omega, hSign⟩, cs4,
                by simp [hSign, hm, hp, (by decide : (ExpSign.plus == .minus) = false)], rfl, hsP4⟩
            · exact ⟨.none, ⟨p3, Nat.le_refl _, Nat.le_of_lt hSign⟩, cs3,
                by simp [hSign, hm, hp, (by decide : (ExpSign.none == .minus) = false)], rfl, hsP3⟩
        · exact ⟨.none, ⟨p3, Nat.le_refl _, hExpLt⟩, cs3,
            by simp [hSign, (by decide : (ExpSign.none == .minus) = false)], rfl, hsP3⟩
      obtain ⟨sgn, p4Sub, cs4, hSignEOk, hcs3Eq, hsP4⟩ := hSignESplit
      dsimp only [p2, p3] at hSignEOk
      rw [hSignEOk] at hParse
      dsimp only at hParse
      have hScanE := scanDigits_exp_spec p4Sub.2.2 hsP4
      have hspP := spanDigits_props hsP4
      rcases hsp : spanDigits cs4 with ⟨eDs, after⟩
      rw [hsp] at hScanE hspP
      rcases hResE : scanDigits bytes p4Sub.1 p4Sub.2.2 0 0 bytes.size true 100_000 with ⟨expVal, expDigits, pSub⟩
      rw [hResE] at hScanE hParse
      dsimp only at hScanE hspP hParse
      by_cases hValLe : parseDecDigitsLoop 0 eDs ≤ 100_000
      · rw [ite_eq_left hValLe] at hScanE
        rcases hScanE with ⟨hexpValEq, hexpDigsEq, _, hsAfter⟩
        by_cases hd0 : expDigits == 0
        · simp [hd0] at hParse
        · have hNotGt : ¬(expVal > 100_000) := by omega
          simp only [hd0, Bool.false_eq_true, hNotGt, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hParse
          rcases hParse with ⟨rfl, rfl⟩
          have heNe : eDs.isEmpty = false := by
            cases eDs with | nil => simp at hexpDigsEq; simp [hexpDigsEq] at hd0 | cons _ _ => rfl
          dsimp only [sign] at hBaseEq
          refine ⟨⟨neg, whole, frac?, some ⟨upperE, sgn, String.ofList eDs⟩⟩, after, ?_, ?_, ?_, ?_, hsAfter⟩
          · unfold validNumTape; rw [Bool.and_eq_true]
            exact ⟨hFracVal, by simp [isNonEmptyDigits, String.toList_ofList, heNe, hspP.2.1]⟩
          · unfold numTapeWithinLimits; rw [Bool.and_eq_true]
            exact ⟨decide_eq_true hFracLim, by simp [maxAbsExponent, parseDecDigits, String.toList_ofList, hValLe]⟩
          · rw [hBaseEq]
            unfold evalNumTape; dsimp only [parseDecDigits]
            rw [String.toList_ofList, ← hexpValEq]
            cases sgn <;> rfl
          · unfold renderNumTape; dsimp only
            rw [hcsEq0, hcs0Eq, hcs1Eq, heChEq, hcs3Eq, hspP.1]
            by_cases hn : neg = true <;> by_cases hu : upperE = true <;>
              (simp [hn, hu, String.toList_append, String.toList_ofList, List.append_assoc,
                show "-".toList = ['-'] from rfl, show "E".toList = ['E'] from rfl,
                show "e".toList = ['e'] from rfl]; rfl)
      · rw [ite_eq_right hValLe] at hScanE
        obtain ⟨hGt, hCnt⟩ := hScanE
        have hd0 : (expDigits == 0) = false := by
          apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq]; omega
        simp [hd0, show expVal > 100_000 by omega] at hParse
    · simp only [show (bytes[p2Sub.1] == 0x65 || bytes[p2Sub.1] == 0x45) = false from Bool.eq_false_iff.mpr hbE,
        Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hParse
      rcases hParse with ⟨rfl, rfl⟩
      dsimp only [sign] at hBaseEq
      refine ⟨⟨neg, whole, frac?, none⟩, cs2, ?_, ?_, ?_, ?_, hsP2⟩
      · unfold validNumTape; simp; exact hFracVal
      · unfold numTapeWithinLimits; rw [Bool.and_eq_true]
        exact ⟨decide_eq_true hFracLim, by simp [maxAbsExponent]⟩
      · rw [hBaseEq]; rfl
      · unfold renderNumTape; dsimp only
        rw [hcsEq0, hcs0Eq, hcs1Eq]
        by_cases hn : neg = true <;>
          (simp [hn, String.toList_append, List.append_assoc, show "-".toList = ['-'] from rfl]; rfl)
  · simp only [show ¬(p2Sub.1 < bytes.size) from hExpLt, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at hParse
    rcases hParse with ⟨rfl, rfl⟩
    dsimp only [sign] at hBaseEq
    refine ⟨⟨neg, whole, frac?, none⟩, cs2, ?_, ?_, ?_, ?_, hsP2⟩
    · unfold validNumTape; simp; exact hFracVal
    · unfold numTapeWithinLimits; rw [Bool.and_eq_true]
      exact ⟨decide_eq_true hFracLim, by simp [maxAbsExponent]⟩
    · rw [hBaseEq]; rfl
    · unfold renderNumTape; dsimp only
      rw [hcsEq0, hcs0Eq, hcs1Eq]
      by_cases hn : neg = true <;>
        (simp [hn, String.toList_append, List.append_assoc, show "-".toList = ['-'] from rfl]; rfl)

end LeanSwe.Json.Proofs
