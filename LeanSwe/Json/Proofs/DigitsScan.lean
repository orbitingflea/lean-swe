import Lean.Data.Json.Basic
import LeanSwe.Json.Impl
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex
import LeanSwe.Json.Proofs.Utf8Ws

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- `parseDecDigitsLoop` is monotone (`acc ≤ parseDecDigitsLoop acc ds`). -/
theorem parseDecDigitsLoop_ge (acc : Nat) (ds : List Char) :
    acc ≤ parseDecDigitsLoop acc ds := by
  induction ds generalizing acc with
  | nil => exact Nat.le_refl _
  | cons d tl ih =>
    simp only [parseDecDigitsLoop_cons]
    exact Nat.le_trans (by omega) (ih _)

private theorem toDigitsCore_step10 (f n : Nat) (suf : List Char) :
    Nat.toDigitsCore 10 (f + 1) n suf =
      if n / 10 = 0 then Nat.digitChar (n % 10) :: suf
      else Nat.toDigitsCore 10 f (n / 10) (Nat.digitChar (n % 10) :: suf) := rfl

private theorem toDigitsCore_fuel_irrel (f1 f2 n : Nat) (suf : List Char)
    (h1 : n < f1) (h2 : n < f2) :
    Nat.toDigitsCore 10 f1 n suf = Nat.toDigitsCore 10 f2 n suf := by
  induction f1 generalizing f2 n suf with
  | zero => omega
  | succ f1' ih =>
    cases f2 with
    | zero => omega
    | succ f2' =>
      rw [toDigitsCore_step10, toDigitsCore_step10]
      generalize Nat.digitChar (n % 10) = dc
      by_cases hq : n / 10 = 0
      · rw [ite_eq_left hq, ite_eq_left hq]
      · rw [ite_eq_right hq, ite_eq_right hq]
        exact ih f2' (n / 10) (dc :: suf) (by omega) (by omega)

private theorem toDigitsCore_suf (f n : Nat) (suf : List Char) (h : n < f) :
    Nat.toDigitsCore 10 f n suf = Nat.toDigitsCore 10 f n [] ++ suf := by
  induction f generalizing n suf with
  | zero => omega
  | succ f' ih =>
    rw [toDigitsCore_step10, toDigitsCore_step10]
    generalize Nat.digitChar (n % 10) = dc
    by_cases hq : n / 10 = 0
    · rw [ite_eq_left hq, ite_eq_left hq]; rfl
    · rw [ite_eq_right hq, ite_eq_right hq,
        ih (n / 10) (dc :: suf) (by omega), ih (n / 10) [dc] (by omega), List.append_assoc]
      rfl

/-- Fuel-irrelevance and suffix-append rule for `Nat.toDigitsCore 10`. -/
theorem toDigitsCore_append_suf (f1 f2 n : Nat) (suf : List Char)
    (h1 : n < f1) (h2 : n < f2) :
    Nat.toDigitsCore 10 f1 n suf = Nat.toDigitsCore 10 f2 n [] ++ suf := by
  rw [toDigitsCore_fuel_irrel f1 f2 n suf h1 h2, toDigitsCore_suf f2 n suf h2]

/-- Positive accumulator property for `(parseDecDigitsLoop acc ds).repr`. -/
theorem repr_parseDecDigitsLoop_pos {acc : Nat} (hpos : 1 ≤ acc) :
    ∀ {ds : List Char}, ds.all isAsciiDigit = true →
      (parseDecDigitsLoop acc ds).repr.toList = acc.repr.toList ++ ds
  | [], _ => by simp
  | d :: tl, hds => by
    simp only [List.all_cons, Bool.and_eq_true] at hds
    rcases hds with ⟨hd, htl⟩
    have hdBounds : 0x30 ≤ d.toNat ∧ d.toNat ≤ 0x39 := by
      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hd
      exact hd
    let v := d.toNat - 0x30
    have hvLt : v < 10 := by omega
    have hdChar : Nat.digitChar v = d := by
      apply Char.ext; apply UInt32.toNat_inj.mp
      change (Nat.digitChar v).toNat = d.toNat
      have ⟨_, h2⟩ := digitChar_lt10_props hvLt
      have h1 := (digitChar_lt10_props hvLt).1
      simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h1
      change 0x30 ≤ (Nat.digitChar v).toNat ∧ (Nat.digitChar v).toNat ≤ 0x39 at h1
      omega
    let acc' := acc * 10 + v
    have hacc'Pos : 1 ≤ acc' := by omega
    have hstepRepr : acc'.repr.toList = acc.repr.toList ++ [d] := by
      have hr1 : acc'.repr.toList = Nat.toDigits 10 acc' := String.toList_ofList
      have hr2 : acc.repr.toList = Nat.toDigits 10 acc := String.toList_ofList
      rw [hr1, hr2]
      unfold Nat.toDigits
      rw [toDigitsCore_step10]
      have hqNe : acc' / 10 ≠ 0 := by omega
      have hqEq : acc' / 10 = acc := by omega
      have hmEq : acc' % 10 = v := by omega
      rw [ite_eq_right hqNe, hqEq, hmEq, hdChar]
      exact toDigitsCore_append_suf acc' (acc + 1) acc [d] (by omega) (by omega)
    simp only [parseDecDigitsLoop_cons]
    rw [repr_parseDecDigitsLoop_pos hacc'Pos htl, hstepRepr, List.append_assoc, List.singleton_append]

/-- Canonical decimal round-trip for a non-zero leading digit `'1'..'9'` followed by ASCII digits. -/
theorem repr_of_nonZeroHeadDigits {c : Char} {ds : List Char}
    (hc : '1' ≤ c ∧ c ≤ '9') (hds : ds.all isAsciiDigit = true) :
    (parseDecDigitsLoop 0 (c :: ds)).repr.toList = c :: ds := by
  have hcBounds : 0x31 ≤ c.toNat ∧ c.toNat ≤ 0x39 := by
    rcases hc with ⟨h1, h2⟩
    rw [Char.le_def, UInt32.le_iff_toNat_le] at h1 h2
    exact ⟨h1, h2⟩
  let d0 := c.toNat - 0x30
  have hd0Bounds : 1 ≤ d0 ∧ d0 ≤ 9 := by omega
  have hd0Repr : d0.repr.toList = [c] := by
    have hr : d0.repr.toList = Nat.toDigits 10 d0 := String.toList_ofList
    rw [hr]; unfold Nat.toDigits
    rw [toDigitsCore_step10]
    have hq0 : d0 / 10 = 0 := by omega
    have hm0 : d0 % 10 = d0 := by omega
    rw [ite_eq_left hq0, hm0]
    congr 1
    have ⟨h1, h2⟩ := digitChar_lt10_props (show d0 < 10 by omega)
    simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h1
    change 0x30 ≤ (Nat.digitChar d0).toNat ∧ (Nat.digitChar d0).toNat ≤ 0x39 at h1
    apply Char.ext; apply UInt32.toNat_inj.mp
    change (Nat.digitChar d0).toNat = c.toNat
    omega
  simp only [parseDecDigitsLoop_cons, Nat.zero_mul, Nat.zero_add]
  rw [repr_parseDecDigitsLoop_pos hd0Bounds.1 hds, hd0Repr, List.singleton_append]

/-- Equivalence between byte-level `0x30 ≤ b && b ≤ 0x39` and `isAsciiDigit` on ASCII `< 0x80`. -/
theorem isDigitByte_ascii_eq {c : Char} (hascii : c.toNat < 0x80) :
    (0x30 ≤ c.val.toUInt8 && c.val.toUInt8 ≤ 0x39) = isAsciiDigit c := by
  unfold isAsciiDigit
  have htoNat : c.val.toUInt8.toNat = c.toNat := by
    rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, htoNat,
    Char.le_def, UInt32.le_iff_toNat_le]
  rfl

/-- Pure accumulator step of `scanDigitsLoop`. -/
def digitChunkStep (bigAcc chunkAcc chunkLen d : Nat) : Nat × Nat × Nat :=
  if chunkLen == 18 then (bigAcc * decChunkBase + chunkAcc, d, 1)
  else (bigAcc, chunkAcc * 10 + d, chunkLen + 1)

/-- One-step chunk-value identity for `scanDigitsLoop`. -/
theorem chunkStep_val_eq (bigAcc chunkAcc chunkLen d : Nat) (hLen : chunkLen ≤ 18)
    (hd : d < 10) (hchunk : chunkAcc < 10 ^ chunkLen) :
    let step := digitChunkStep bigAcc chunkAcc chunkLen d
    step.1 * (10 ^ step.2.2) + step.2.1 = (bigAcc * (10 ^ chunkLen) + chunkAcc) * 10 + d ∧
      1 ≤ step.2.2 ∧ step.2.2 ≤ 18 ∧ step.2.1 < 10 ^ step.2.2 := by
  dsimp only [digitChunkStep]
  cases h18 : chunkLen == 18 with
  | true =>
    have hEq18 : chunkLen = 18 := beq_iff_eq.mp h18
    simp only [↓reduceIte, hEq18]
    exact ⟨rfl, by decide, by decide, hd⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hNe18 : chunkLen ≠ 18 := fun h => by rw [beq_iff_eq.mpr h] at h18; cases h18
    have hpow : 10 ^ (chunkLen + 1) = (10 ^ chunkLen) * 10 := Nat.pow_succ 10 chunkLen
    refine ⟨?_, by omega, by omega, ?_⟩
    · rw [hpow, Nat.add_mul, Nat.mul_assoc]; omega
    · rw [hpow]; omega

/-- Simplification of `overVal` in `scanDigitsLoop` to `hasValCap && decide (val' > limitVal)`. -/
theorem overVal_eq (hasValCap : Bool) (bigAcc' chunkAcc' chunkLen' limitVal : Nat)
    (hl1 : 1 ≤ chunkLen') :
    (if hasValCap then
      bigAcc' > limitVal ||
        (bigAcc' > 0 && bigAcc' * (10 ^ chunkLen') + chunkAcc' > limitVal) ||
        (bigAcc' == 0 && chunkAcc' > limitVal)
     else false) = (hasValCap && decide (bigAcc' * (10 ^ chunkLen') + chunkAcc' > limitVal)) := by
  cases hasValCap with
  | false => rfl
  | true =>
    simp only [↓reduceIte, Bool.true_and]
    by_cases hb0 : bigAcc' = 0
    · subst hb0; simp
    · have hpowPos : 1 ≤ 10 ^ chunkLen' := by
        have : 10 ^ 1 ≤ 10 ^ chunkLen' := Nat.pow_le_pow_right (by decide) hl1
        omega
      have hleVal : bigAcc' ≤ bigAcc' * (10 ^ chunkLen') + chunkAcc' := by
        have := Nat.mul_le_mul_left bigAcc' hpowPos
        omega
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      omega

/-- Exact specification of `scanDigitsLoop` when `hasValCap = false`. -/
theorem scanDigitsLoop_noValCap_spec :
    ∀ (cs : List Char) {bytes : ByteArray} {pos : Nat}
      (bigAcc chunkAcc chunkLen count limitCount limitVal : Nat),
      ByteSliceAt bytes pos cs →
      chunkLen ≤ 18 →
      chunkAcc < 10 ^ chunkLen →
      let (ds, rest) := spanDigits cs
      let res := scanDigitsLoop bytes pos bigAcc chunkAcc chunkLen count limitCount false limitVal
      if count + ds.length ≤ limitCount then
        res = (parseDecDigitsLoop (bigAcc * (10 ^ chunkLen) + chunkAcc) ds,
               count + ds.length, pos + ds.length) ∧
          ByteSliceAt bytes (pos + ds.length) rest
      else
        count ≤ limitCount → res.2.1 = limitCount + 1
  | [], bytes, pos, bigAcc, chunkAcc, chunkLen, count, limitCount, limitVal, hSlice, _, _ => by
    have heq := byteSliceAt_nil_eq_size hSlice
    have hnot : ¬(pos < bytes.size) := by omega
    simp only [spanDigits, List.length_nil, Nat.add_zero]
    unfold scanDigitsLoop
    simp only [hnot, ↓reduceDIte]
    split
    · exact ⟨rfl, hSlice⟩
    · intro hle; omega
  | c :: tl, bytes, pos, bigAcc, chunkAcc, chunkLen, count, limitCount, limitVal, hSlice, hLen, hChunk => by
    have hlt := byteSliceAt_cons_lt_size hSlice
    by_cases hdig : isAsciiDigit c = true
    · have hascii : c.toNat < 0x80 := by
        simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hdig
        change 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 at hdig; omega
      obtain ⟨_, hget, hsNext⟩ := byteSliceAt_ascii_cons hSlice hascii
      have hbDig : (0x30 ≤ bytes[pos]'hlt && bytes[pos]'hlt ≤ 0x39) = true := by
        rw [hget, isDigitByte_ascii_eq hascii, hdig]
      have hdNat : (bytes[pos]'hlt).toNat - 0x30 = c.toNat - 0x30 := by
        rw [hget, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by change c.toNat < 256; omega)]; rfl
      have hdLt10 : c.toNat - 0x30 < 10 := by
        simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hdig
        change 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 at hdig; omega
      rcases hsp : spanDigits tl with ⟨dsTl, restTl⟩
      simp only [spanDigits, hdig, ↓reduceIte, hsp, List.length_cons]
      by_cases hOverCnt : count + 1 > limitCount
      · have hNotFit : ¬(count + (dsTl.length + 1) ≤ limitCount) := by omega
        simp only [hNotFit, ↓reduceIte]
        intro hCntLe
        unfold scanDigitsLoop
        simp only [hlt, ↓reduceDIte, hbDig, hOverCnt, ↓reduceIte]
        omega
      · obtain ⟨hValEq, hl1, hl18, hcLt⟩ := chunkStep_val_eq bigAcc chunkAcc chunkLen (c.toNat - 0x30) hLen hdLt10 hChunk
        let stepTup := digitChunkStep bigAcc chunkAcc chunkLen (c.toNat - 0x30)
        have ih := scanDigitsLoop_noValCap_spec tl stepTup.1 stepTup.2.1 stepTup.2.2
          (count + 1) limitCount limitVal hsNext hl18 hcLt
        rw [hsp] at ih
        dsimp only at ih
        unfold scanDigitsLoop
        simp only [hlt, ↓reduceDIte, hbDig, hOverCnt, ↓reduceIte, hdNat]
        change (if count + (dsTl.length + 1) ≤ limitCount then
            scanDigitsLoop bytes (pos + 1) stepTup.1 stepTup.2.1 stepTup.2.2 (count + 1) limitCount false limitVal = _ ∧ _
          else _)
        by_cases hFit : count + (dsTl.length + 1) ≤ limitCount
        · have hFit' : (count + 1) + dsTl.length ≤ limitCount := by omega
          rw [ite_eq_left hFit'] at ih
          simp only [hFit, ↓reduceIte]
          refine ⟨?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using ih.2⟩
          rw [ih.1]
          have hStepVal : stepTup.1 * (10 ^ stepTup.2.2) + stepTup.2.1 =
              (bigAcc * (10 ^ chunkLen) + chunkAcc) * 10 + (c.toNat - 0x30) := hValEq
          rw [hStepVal]
          simp [Nat.add_assoc, Nat.add_comm 1]
        · have hFit' : ¬((count + 1) + dsTl.length ≤ limitCount) := by omega
          rw [ite_eq_right hFit'] at ih
          simp only [hFit, ↓reduceIte]
          intro _; exact ih (by omega)
    · simp only [Bool.not_eq_true] at hdig
      have hbNotDig : (0x30 ≤ bytes[pos]'hlt && bytes[pos]'hlt ≤ 0x39) = false := by
        by_cases hascii : c.toNat < 0x80
        · obtain ⟨_, hget, _⟩ := byteSliceAt_ascii_cons hSlice hascii
          rw [hget, isDigitByte_ascii_eq hascii, hdig]
        · have hge128 := byteSliceAt_nonAscii_ge_128 hSlice (by omega) hlt
          have hgeNat : 128 ≤ (bytes[pos]'hlt).toNat := UInt8.le_iff_toNat_le.mp hge128
          rw [Bool.and_eq_false_iff]; right
          rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le]
          have h57 : (0x39 : UInt8).toNat = 57 := rfl
          omega
      simp only [spanDigits, hdig, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.add_zero]
      unfold scanDigitsLoop
      simp only [hlt, ↓reduceDIte, hbNotDig, Bool.false_eq_true, ↓reduceIte]
      split
      · exact ⟨rfl, hSlice⟩
      · intro hle; omega

/-- Exact specification of `scanDigitsLoop` when `hasValCap = true` and `count + ds.length ≤ limitCount`. -/
theorem scanDigitsLoop_valCap_spec :
    ∀ (cs : List Char) {bytes : ByteArray} {pos : Nat}
      (bigAcc chunkAcc chunkLen count limitCount limitVal : Nat),
      ByteSliceAt bytes pos cs →
      chunkLen ≤ 18 →
      chunkAcc < 10 ^ chunkLen →
      count + (spanDigits cs).1.length ≤ limitCount →
      if parseDecDigitsLoop (bigAcc * (10 ^ chunkLen) + chunkAcc) (spanDigits cs).1 ≤ limitVal then
        scanDigitsLoop bytes pos bigAcc chunkAcc chunkLen count limitCount true limitVal =
          (parseDecDigitsLoop (bigAcc * (10 ^ chunkLen) + chunkAcc) (spanDigits cs).1,
           count + (spanDigits cs).1.length, pos + (spanDigits cs).1.length) ∧
          ByteSliceAt bytes (pos + (spanDigits cs).1.length) (spanDigits cs).2
      else
        bigAcc * (10 ^ chunkLen) + chunkAcc ≤ limitVal →
          limitVal < (scanDigitsLoop bytes pos bigAcc chunkAcc chunkLen count limitCount true limitVal).1 ∧
          count + 1 ≤ (scanDigitsLoop bytes pos bigAcc chunkAcc chunkLen count limitCount true limitVal).2.1
  | [], bytes, pos, bigAcc, chunkAcc, chunkLen, count, limitCount, limitVal, hSlice, _, _, _ => by
    have heq := byteSliceAt_nil_eq_size hSlice
    have hnot : ¬(pos < bytes.size) := by omega
    simp only [spanDigits, List.length_nil, Nat.add_zero, parseDecDigitsLoop_nil]
    unfold scanDigitsLoop
    simp only [hnot, ↓reduceDIte]
    split
    · exact ⟨trivial, hSlice⟩
    · intro hle; omega
  | c :: tl, bytes, pos, bigAcc, chunkAcc, chunkLen, count, limitCount, limitVal, hSlice, hLen, hChunk, hCntBnd => by
    have hlt := byteSliceAt_cons_lt_size hSlice
    by_cases hdig : isAsciiDigit c = true
    · have hascii : c.toNat < 0x80 := by
        simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hdig
        change 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 at hdig; omega
      obtain ⟨_, hget, hsNext⟩ := byteSliceAt_ascii_cons hSlice hascii
      have hbDig : (0x30 ≤ bytes[pos]'hlt && bytes[pos]'hlt ≤ 0x39) = true := by
        rw [hget, isDigitByte_ascii_eq hascii, hdig]
      have hdNat : (bytes[pos]'hlt).toNat - 0x30 = c.toNat - 0x30 := by
        rw [hget, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by change c.toNat < 256; omega)]; rfl
      have hdLt10 : c.toNat - 0x30 < 10 := by
        simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at hdig
        change 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 at hdig; omega
      rcases hsp : spanDigits tl with ⟨dsTl, restTl⟩
      simp only [spanDigits, hdig, ↓reduceIte, hsp, List.length_cons, parseDecDigitsLoop_cons] at hCntBnd ⊢
      have hNotOverCnt : ¬(count + 1 > limitCount) := by omega
      obtain ⟨hValEq, hl1, hl18, hcLt⟩ := chunkStep_val_eq bigAcc chunkAcc chunkLen (c.toNat - 0x30) hLen hdLt10 hChunk
      let stepTup := digitChunkStep bigAcc chunkAcc chunkLen (c.toNat - 0x30)
      let val1 := stepTup.1 * (10 ^ stepTup.2.2) + stepTup.2.1
      have hStepVal : val1 = (bigAcc * (10 ^ chunkLen) + chunkAcc) * 10 + (c.toNat - 0x30) := hValEq
      have hOverEq : (decide (stepTup.1 > limitVal) ||
          (decide (stepTup.1 > 0) && decide (val1 > limitVal)) ||
          (stepTup.1 == 0 && decide (stepTup.2.1 > limitVal))) = decide (val1 > limitVal) := by
        have h0 := overVal_eq true stepTup.1 stepTup.2.1 stepTup.2.2 limitVal hl1
        simpa [val1] using h0
      unfold scanDigitsLoop
      simp only [hlt, ↓reduceDIte, hbDig, hNotOverCnt, ↓reduceIte, hdNat]
      change (if parseDecDigitsLoop ((bigAcc * (10 ^ chunkLen) + chunkAcc) * 10 + (c.toNat - 0x30)) dsTl ≤ limitVal then
          (if (decide (stepTup.1 > limitVal) ||
               (decide (stepTup.1 > 0) && decide (val1 > limitVal)) ||
               (stepTup.1 == 0 && decide (stepTup.2.1 > limitVal))) = true
           then (val1, count + 1, pos + 1)
           else scanDigitsLoop bytes (pos + 1) stepTup.1 stepTup.2.1 stepTup.2.2 (count + 1) limitCount true limitVal) =
            (parseDecDigitsLoop ((bigAcc * (10 ^ chunkLen) + chunkAcc) * 10 + (c.toNat - 0x30)) dsTl,
             count + (dsTl.length + 1), pos + (dsTl.length + 1)) ∧
            ByteSliceAt bytes (pos + (dsTl.length + 1)) restTl
        else
          bigAcc * (10 ^ chunkLen) + chunkAcc ≤ limitVal →
            limitVal < (if (decide (stepTup.1 > limitVal) ||
                 (decide (stepTup.1 > 0) && decide (val1 > limitVal)) ||
                 (stepTup.1 == 0 && decide (stepTup.2.1 > limitVal))) = true
              then (val1, count + 1, pos + 1)
              else scanDigitsLoop bytes (pos + 1) stepTup.1 stepTup.2.1 stepTup.2.2 (count + 1) limitCount true limitVal).1 ∧
            count + 1 ≤ (if (decide (stepTup.1 > limitVal) ||
                 (decide (stepTup.1 > 0) && decide (val1 > limitVal)) ||
                 (stepTup.1 == 0 && decide (stepTup.2.1 > limitVal))) = true
              then (val1, count + 1, pos + 1)
              else scanDigitsLoop bytes (pos + 1) stepTup.1 stepTup.2.1 stepTup.2.2 (count + 1) limitCount true limitVal).2.1)
      simp only [hOverEq, ← hStepVal]
      have hMono : val1 ≤ parseDecDigitsLoop val1 dsTl := parseDecDigitsLoop_ge val1 dsTl
      by_cases hOver1 : val1 > limitVal
      · have hNotFullLe : ¬(parseDecDigitsLoop val1 dsTl ≤ limitVal) := by omega
        rw [decide_eq_true hOver1, ite_eq_right hNotFullLe]
        simp only [↓reduceIte]
        intro _; exact ⟨hOver1, Nat.le_refl _⟩
      · rw [decide_eq_false hOver1]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have ih := scanDigitsLoop_valCap_spec tl stepTup.1 stepTup.2.1 stepTup.2.2
          (count + 1) limitCount limitVal hsNext hl18 hcLt (by rw [hsp]; dsimp only; omega)
        rw [hsp] at ih
        dsimp only at ih
        by_cases hFullLe : parseDecDigitsLoop val1 dsTl ≤ limitVal
        · rw [ite_eq_left hFullLe] at ih ⊢
          have hcEq : count + 1 + dsTl.length = count + (dsTl.length + 1) := by omega
          have hpEq : pos + 1 + dsTl.length = pos + (dsTl.length + 1) := by omega
          exact ⟨by rw [ih.1, hcEq, hpEq], by rw [← hpEq]; exact ih.2⟩
        · rw [ite_eq_right hFullLe] at ih ⊢
          intro _
          obtain ⟨hGt, hCnt⟩ := ih (by omega)
          exact ⟨hGt, by omega⟩
    · simp only [Bool.not_eq_true] at hdig
      have hbNotDig : (0x30 ≤ bytes[pos]'hlt && bytes[pos]'hlt ≤ 0x39) = false := by
        by_cases hascii : c.toNat < 0x80
        · obtain ⟨_, hget, _⟩ := byteSliceAt_ascii_cons hSlice hascii
          rw [hget, isDigitByte_ascii_eq hascii, hdig]
        · have hge128 := byteSliceAt_nonAscii_ge_128 hSlice (by omega) hlt
          have hgeNat : 128 ≤ (bytes[pos]'hlt).toNat := UInt8.le_iff_toNat_le.mp hge128
          rw [Bool.and_eq_false_iff]; right
          rw [decide_eq_false_iff_not, UInt8.le_iff_toNat_le]
          have h57 : (0x39 : UInt8).toNat = 57 := rfl
          omega
      simp only [spanDigits, hdig, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.add_zero, parseDecDigitsLoop_nil]
      unfold scanDigitsLoop
      simp only [hlt, ↓reduceDIte, hbNotDig, Bool.false_eq_true, ↓reduceIte]
      split
      · exact ⟨trivial, hSlice⟩
      · intro hle; omega

end LeanSwe.Json.Proofs
