import LeanSwe.Base64.Interface
import LeanSwe.Base64.Model
import LeanSwe.Base64.Proofs.CodecEquiv

namespace LeanSwe.Base64.Proofs

open LeanSwe.Base64
open LeanSwe.Base64.Model

/-- Decompose `encodeBytesList` into unpadded alphabet characters plus `'='` padding. -/
theorem encodeBytesList_split (a : Alphabet) (pad : Bool) (bs : List UInt8) :
    encodeBytesList a pad bs =
      encodeBytesList a false bs ++
        List.replicate (expectedPaddingCount { alphabet := a, pad := pad } bs.length) '=' := by
  match bs with
  | [] => simp [encodeBytesList, expectedPaddingCount]
  | [b0] => cases pad <;> simp [encodeBytesList, expectedPaddingCount]
  | [b0, b1] => cases pad <;> simp [encodeBytesList, expectedPaddingCount]
  | b0 :: b1 :: b2 :: rest =>
    have ih := encodeBytesList_split a pad rest
    have hlen : (b0 :: b1 :: b2 :: rest).length % 3 = rest.length % 3 := by
      simp [List.length_cons]
      omega
    simp only [encodeBytesList, expectedPaddingCount, hlen] at ih ⊢
    rw [ih]
    rfl

private theorem unpadded_len_add3 (n : Nat) :
    ((n + 3) * 4 + 2) / 3 = (n * 4 + 2) / 3 + 4 := by
  omega

/-- Length, alphabet membership, and `decodeDataChars` round-trip for unpadded encodings. -/
theorem encodeBytesList_unpadded_props (a : Alphabet) (bs : List UInt8) :
    (encodeBytesList a false bs).length = expectedEncodedLength { alphabet := a, pad := false } bs.length ∧
    (encodeBytesList a false bs).all (isAlphabetChar a) = true ∧
    (∀ strict offset, decodeDataChars a strict offset (encodeBytesList a false bs) = .ok bs) ∧
    (bs.length % 3 = 0 → (encodeBytesList a false bs).length % 4 = 0) := by
  match bs with
  | [] =>
    simp [encodeBytesList, expectedEncodedLength, decodeDataChars]
  | [b0] =>
    refine ⟨by simp [encodeBytesList, expectedEncodedLength], ?_, ?_, by simp⟩
    · simp [encodeBytesList, isAlphabetChar_encodeSextet a (u8_hi6_lt64 b0),
        isAlphabetChar_encodeSextet a (u8_lo2_shift4_lt64 b0)]
    · intro strict offset
      simp only [encodeBytesList, decodeDataChars, decodeChar?_encodeSextet a (u8_hi6_lt64 b0),
        decodeChar?_encodeSextet a (u8_lo2_shift4_lt64 b0), u8_lo2_shift4_canon b0,
        ne_eq, not_true_eq_false, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        u8_recombine_1byte b0, UInt8.ofNat_toNat]
  | [b0, b1] =>
    have hp := pack4_4_props ⟨b0.toNat &&& 0x03, u8_lo2_lt4 b0⟩ ⟨b1.toNat >>> 4, u8_hi4_lt16 b1⟩
    refine ⟨by simp [encodeBytesList, expectedEncodedLength], ?_, ?_, by simp⟩
    · simp [encodeBytesList, isAlphabetChar_encodeSextet a (u8_hi6_lt64 b0),
        isAlphabetChar_encodeSextet a hp.1,
        isAlphabetChar_encodeSextet a (u8_lo4_shift2_lt64 b1)]
    · intro strict offset
      simp only [encodeBytesList, decodeDataChars, decodeChar?_encodeSextet a (u8_hi6_lt64 b0),
        decodeChar?_encodeSextet a hp.1,
        decodeChar?_encodeSextet a (u8_lo4_shift2_lt64 b1), u8_lo4_shift2_canon b1,
        ne_eq, not_true_eq_false, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        u8_recombine_hi2_lo4 b0 b1, u8_recombine_4_4_final b0 b1, UInt8.ofNat_toNat]
  | b0 :: b1 :: b2 :: rest =>
    have ih := encodeBytesList_unpadded_props a rest
    have hp1 := pack4_4_props ⟨b0.toNat &&& 0x03, u8_lo2_lt4 b0⟩ ⟨b1.toNat >>> 4, u8_hi4_lt16 b1⟩
    have hp2 := pack4_2_props ⟨b1.toNat &&& 0x0F, u8_lo4_lt16 b1⟩ ⟨b2.toNat >>> 6, u8_hi2_lt4 b2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have ih1 := ih.1
      have hlen : (b0 :: b1 :: b2 :: rest).length = rest.length + 3 := rfl
      simp only [encodeBytesList, List.length_cons, expectedEncodedLength, hlen, Bool.false_eq_true, ↓reduceIte] at ih1 ⊢
      rw [unpadded_len_add3, ← ih1]
    · simp [encodeBytesList, isAlphabetChar_encodeSextet a (u8_hi6_lt64 b0),
        isAlphabetChar_encodeSextet a hp1.1, isAlphabetChar_encodeSextet a hp2.1,
        isAlphabetChar_encodeSextet a (u8_lo6_lt64 b2), ih.2.1]
    · intro strict offset
      simp only [encodeBytesList, decodeDataChars, decodeChar?_encodeSextet a (u8_hi6_lt64 b0),
        decodeChar?_encodeSextet a hp1.1, decodeChar?_encodeSextet a hp2.1,
        decodeChar?_encodeSextet a (u8_lo6_lt64 b2), ih.2.2.1 strict (offset + 4),
        u8_recombine_hi2_lo4 b0 b1, u8_recombine_4_4 b0 b1 b2, u8_recombine_2_6 b1 b2,
        UInt8.ofNat_toNat]
    · intro h
      have hlen : (b0 :: b1 :: b2 :: rest).length = rest.length + 3 := rfl
      have hmod : rest.length % 3 = 0 := by rw [hlen] at h; omega
      have hrm := ih.2.2.2 hmod
      simp only [encodeBytesList, List.length_cons]
      omega

private theorem scanInvalidChar_all_ok (a : Alphabet) (idx : Nat) (cs : List Char)
    (h : cs.all (fun c => isAlphabetChar a c || c == '=') = true) :
    scanInvalidChar a idx cs = none := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    unfold scanInvalidChar
    simp only [h.1, ↓reduceIte]
    exact ih (idx + 1) h.2

private theorem findFirstEq_of_all_alphabet_and_eqs (a : Alphabet) (idx : Nat)
    (data eqs : List Char)
    (hdata : data.all (isAlphabetChar a) = true)
    (heqs : eqs.all (· == '=') = true) :
    findFirstEq idx (data ++ eqs) =
      if eqs.isEmpty then none else some (idx + data.length) := by
  induction data generalizing idx with
  | nil =>
    cases eqs with
    | nil => rfl
    | cons c cs =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at heqs
      simp [findFirstEq, heqs.1]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hdata
    have hne : c ≠ '=' := by
      intro hc
      subst hc
      rw [isAlphabetChar_eq_false] at hdata
      cases hdata.1
    simp only [List.cons_append, findFirstEq, beq_iff_eq, hne, ↓reduceIte]
    rw [ih (idx + 1) hdata.2]
    cases eqs with
    | nil => rfl
    | cons _ _ => simp; omega

/-- Model-level round-trip `decodeModelChars decOpts (encodeBytesList ...) = .ok bs`. -/
theorem decodeModelChars_encodeBytesList
    (encOpts : EncodeOptions) (decOpts : DecodeOptions) (bs : List UInt8)
    (halph : decOpts.alphabet = encOpts.alphabet)
    (hpad1 : encOpts.pad = false ∨ decOpts.padding ≠ .forbidden ∨ bs.length % 3 = 0)
    (hpad2 : encOpts.pad = true ∨ decOpts.padding ≠ .required ∨ bs.length % 3 = 0) :
    decodeModelChars decOpts (encodeBytesList encOpts.alphabet encOpts.pad bs) = .ok bs := by
  rw [encodeBytesList_split encOpts.alphabet encOpts.pad bs]
  have hprops := encodeBytesList_unpadded_props encOpts.alphabet bs
  have hdataAlph : (encodeBytesList encOpts.alphabet false bs).all (isAlphabetChar decOpts.alphabet) = true := by
    rw [halph]; exact hprops.2.1
  have heqsAll : (List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=').all (· == '=') = true := by
    simp
  have hscan : scanInvalidChar decOpts.alphabet 0
      (encodeBytesList encOpts.alphabet false bs ++
        List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=') = none := by
    apply scanInvalidChar_all_ok
    rw [List.all_append]
    simp only [Bool.and_eq_true]
    constructor
    · exact List.all_eq_true.mpr fun c hc => by simp [List.all_eq_true.mp hdataAlph c hc]
    · exact List.all_eq_true.mpr fun c hc => by simp [List.all_eq_true.mp heqsAll c hc]
  have hfirst := findFirstEq_of_all_alphabet_and_eqs decOpts.alphabet 0
    (encodeBytesList encOpts.alphabet false bs)
    (List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=')
    hdataAlph heqsAll
  have hlenData : (encodeBytesList encOpts.alphabet false bs).length =
      expectedEncodedLength { alphabet := encOpts.alphabet, pad := false } bs.length := hprops.1
  have hlenMod : ((encodeBytesList encOpts.alphabet false bs).length +
      expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) % 4 =
      if encOpts.pad then 0 else (bs.length * 4 + 2) / 3 % 4 := by
    cases hpad : encOpts.pad
    · simp [expectedPaddingCount, hlenData, expectedEncodedLength, hpad]
    · simp only [expectedPaddingCount, hlenData, expectedEncodedLength, hpad, Bool.false_eq_true, ↓reduceIte]
      have hmod3 : bs.length % 3 = 0 ∨ bs.length % 3 = 1 ∨ bs.length % 3 = 2 := by omega
      rcases hmod3 with h0 | h1 | h2
      · have hk : bs.length = 3 * (bs.length / 3) := by omega
        have ha : (3 * (bs.length / 3) * 4 + 2) / 3 = 4 * (bs.length / 3) := by omega
        rw [hk, ha]; omega
      · have hk : bs.length = 3 * (bs.length / 3) + 1 := by omega
        have ha : ((3 * (bs.length / 3) + 1) * 4 + 2) / 3 = 4 * (bs.length / 3) + 2 := by omega
        rw [hk, ha]; omega
      · have hk : bs.length = 3 * (bs.length / 3) + 2 := by omega
        have ha : ((3 * (bs.length / 3) + 2) * 4 + 2) / 3 = 4 * (bs.length / 3) + 3 := by omega
        rw [hk, ha]; omega
  unfold decodeModelChars
  rw [hscan, hfirst]
  by_cases hEmpty : (List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=').isEmpty
  · have hEq0 : expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length = 0 := by
      have : (List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=').length = 0 :=
        List.isEmpty_iff_length_eq_zero.mp hEmpty
      simpa [List.length_replicate] using this
    have hEqsNil : List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=' = [] :=
      List.isEmpty_iff.mp hEmpty
    simp only [hEqsNil, List.isEmpty_nil, ↓reduceIte, List.append_nil]
    have hModNe1 : (encodeBytesList encOpts.alphabet false bs).length % 4 ≠ 1 := by
      rw [hlenData, expectedEncodedLength]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hmod3 : bs.length % 3 = 0 ∨ bs.length % 3 = 1 ∨ bs.length % 3 = 2 := by omega
      rcases hmod3 with h0 | h1 | h2
      · have hk : bs.length = 3 * (bs.length / 3) := by omega
        have ha : (3 * (bs.length / 3) * 4 + 2) / 3 = 4 * (bs.length / 3) := by omega
        rw [hk, ha]; omega
      · have hk : bs.length = 3 * (bs.length / 3) + 1 := by omega
        have ha : ((3 * (bs.length / 3) + 1) * 4 + 2) / 3 = 4 * (bs.length / 3) + 2 := by omega
        rw [hk, ha]; omega
      · have hk : bs.length = 3 * (bs.length / 3) + 2 := by omega
        have ha : ((3 * (bs.length / 3) + 2) * 4 + 2) / 3 = 4 * (bs.length / 3) + 3 := by omega
        rw [hk, ha]; omega
    have hModBeq : ((encodeBytesList encOpts.alphabet false bs).length % 4 == 1) = false := by
      simp [hModNe1]
    have hReqOk : ¬(decOpts.padding = .required ∧ (encodeBytesList encOpts.alphabet false bs).length % 4 ≠ 0) := by
      rintro ⟨hreq, hne⟩
      rcases hpad2 with hpadT | hneReq | hmod0
      · have h0 : bs.length % 3 = 0 := by
          unfold expectedPaddingCount at hEq0
          rw [hpadT] at hEq0
          simp only [↓reduceIte] at hEq0
          omega
        exact hne (hprops.2.2.2 h0)
      · exact hneReq hreq
      · exact hne (hprops.2.2.2 hmod0)
    simp only [hModBeq, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact False.elim (hReqOk h)
    · rw [halph]
      exact hprops.2.2.1 decOpts.strictCanonicalBits 0
  · have hEqPos : 0 < expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length := by
      cases hc : List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=' with
      | nil => simp [hc] at hEmpty
      | cons _ _ =>
        have hlen := congrArg List.length hc
        simp only [List.length_replicate, List.length_cons] at hlen
        omega
    have hPadTrue : encOpts.pad = true := by
      cases hp : encOpts.pad
      · simp [expectedPaddingCount, hp] at hEqPos
      · rfl
    have hBsModNe0 : bs.length % 3 ≠ 0 := by
      intro h0
      simp [expectedPaddingCount, hPadTrue, h0] at hEqPos
    have hNotForb : decOpts.padding ≠ .forbidden := by
      rcases hpad1 with hF | hNF | h0
      · rw [hPadTrue] at hF; cases hF
      · exact hNF
      · exact False.elim (hBsModNe0 h0)
    have hDropAll : ((encodeBytesList encOpts.alphabet false bs ++
        List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=').drop
        (encodeBytesList encOpts.alphabet false bs).length).all (· == '=') = true := by
      rw [List.drop_left]
      exact heqsAll
    have hTotMod4 : (encodeBytesList encOpts.alphabet false bs ++
        List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=').length % 4 = 0 := by
      simp only [List.length_append, List.length_replicate]
      simpa [hPadTrue] using hlenMod
    have hEqLe2 : (encodeBytesList encOpts.alphabet false bs ++
        List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=').length -
        (encodeBytesList encOpts.alphabet false bs).length ≤ 2 := by
      simp only [List.length_append, List.length_replicate, Nat.add_sub_cancel_left]
      simp only [expectedPaddingCount, hPadTrue, ↓reduceIte]
      omega
    have hTake : (encodeBytesList encOpts.alphabet false bs ++
        List.replicate (expectedPaddingCount { alphabet := encOpts.alphabet, pad := encOpts.pad } bs.length) '=').take
        (encodeBytesList encOpts.alphabet false bs).length =
        encodeBytesList encOpts.alphabet false bs := List.take_left
    simp only [hEmpty, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, hNotForb, hDropAll, Bool.not_true,
      hTotMod4, ne_eq, not_true_eq_false, gt_iff_lt, Nat.not_lt.mpr hEqLe2, hTake]
    rw [halph]
    exact hprops.2.2.1 decOpts.strictCanonicalBits 0

private theorem sextet_canonical_1 (s0 s1 : Nat) (hs0 : s0 < 64) (hs1 : s1 < 64)
    (hcanon : (s1 &&& 0x0F) = 0) :
    let b0 := UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))
    b0.toNat >>> 2 = s0 ∧ ((b0.toNat &&& 0x03) <<< 4) = s1 := by
  have h1m : s1 % 16 = 0 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod s1 4]
    exact hcanon
  have hs1div : s1 >>> 4 < 4 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hpack : (s0 <<< 2) ||| (s1 >>> 4) = s0 * 4 + s1 / 16 := by
    rw [shiftLeft_or_eq_add _ _ 2 hs1div, Nat.shiftRight_eq_div_pow]
  have hlt : (s0 <<< 2) ||| (s1 >>> 4) < 2 ^ 8 := by
    rw [hpack]
    omega
  dsimp only
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt, hpack,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod _ 2]
  omega

private theorem sextet_canonical_2 (s0 s1 s2 : Nat) (hs0 : s0 < 64) (hs1 : s1 < 64) (hs2 : s2 < 64)
    (hcanon : (s2 &&& 0x03) = 0) :
    let b0 := UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))
    let b1 := UInt8.ofNat (((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2))
    b0.toNat >>> 2 = s0 ∧
    (((b0.toNat &&& 0x03) <<< 4) ||| (b1.toNat >>> 4)) = s1 ∧
    ((b1.toNat &&& 0x0F) <<< 2) = s2 := by
  have h2m : s2 % 4 = 0 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod s2 2]
    exact hcanon
  have hs1hi : s1 >>> 4 < 4 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hs2hi : s2 >>> 2 < 16 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hp0 : (s0 <<< 2) ||| (s1 >>> 4) = s0 * 4 + s1 / 16 := by
    rw [shiftLeft_or_eq_add _ _ 2 hs1hi, Nat.shiftRight_eq_div_pow]
  have hp1 : ((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2) = (s1 % 16) * 16 + s2 / 4 := by
    rw [shiftLeft_or_eq_add _ _ 4 hs2hi, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 4]
  have hlt0 : (s0 <<< 2) ||| (s1 >>> 4) < 2 ^ 8 := by rw [hp0]; omega
  have hlt1 : ((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2) < 2 ^ 8 := by rw [hp1]; omega
  dsimp only
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt0, Nat.mod_eq_of_lt hlt1, hp0, hp1]
  have hb0div : (s0 * 4 + s1 / 16) >>> 2 = s0 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hb0mod : (s0 * 4 + s1 / 16) &&& 0x03 = s1 / 16 := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; omega
  have hb1div : ((s1 % 16) * 16 + s2 / 4) >>> 4 = s1 % 16 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hb1mod : ((s1 % 16) * 16 + s2 / 4) &&& 0x0F = s2 / 4 := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; omega
  refine ⟨hb0div, ?_, ?_⟩
  · rw [hb0mod, hb1div, shiftLeft_or_eq_add _ _ 4 (by omega)]
    omega
  · rw [hb1mod, Nat.shiftLeft_eq]
    omega

private theorem sextet_canonical_3 (s0 s1 s2 s3 : Nat)
    (hs0 : s0 < 64) (hs1 : s1 < 64) (hs2 : s2 < 64) (hs3 : s3 < 64) :
    let b0 := UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))
    let b1 := UInt8.ofNat (((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2))
    let b2 := UInt8.ofNat (((s2 &&& 0x03) <<< 6) ||| s3)
    b0.toNat >>> 2 = s0 ∧
    (((b0.toNat &&& 0x03) <<< 4) ||| (b1.toNat >>> 4)) = s1 ∧
    (((b1.toNat &&& 0x0F) <<< 2) ||| (b2.toNat >>> 6)) = s2 ∧
    (b2.toNat &&& 0x3F) = s3 := by
  have hs1hi : s1 >>> 4 < 4 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hs2hi : s2 >>> 2 < 16 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hp0 : (s0 <<< 2) ||| (s1 >>> 4) = s0 * 4 + s1 / 16 := by
    rw [shiftLeft_or_eq_add _ _ 2 hs1hi, Nat.shiftRight_eq_div_pow]
  have hp1 : ((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2) = (s1 % 16) * 16 + s2 / 4 := by
    rw [shiftLeft_or_eq_add _ _ 4 hs2hi, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 4]
  have hp2 : ((s2 &&& 0x03) <<< 6) ||| s3 = (s2 % 4) * 64 + s3 := by
    rw [shiftLeft_or_eq_add _ _ 6 hs3, Nat.and_two_pow_sub_one_eq_mod _ 2]
  have hlt0 : (s0 <<< 2) ||| (s1 >>> 4) < 2 ^ 8 := by rw [hp0]; omega
  have hlt1 : ((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2) < 2 ^ 8 := by rw [hp1]; omega
  have hlt2 : ((s2 &&& 0x03) <<< 6) ||| s3 < 2 ^ 8 := by rw [hp2]; omega
  dsimp only
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt hlt0, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2,
    hp0, hp1, hp2]
  have hb0div : (s0 * 4 + s1 / 16) >>> 2 = s0 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hb0mod : (s0 * 4 + s1 / 16) &&& 0x03 = s1 / 16 := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 2]; omega
  have hb1div : ((s1 % 16) * 16 + s2 / 4) >>> 4 = s1 % 16 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hb1mod : ((s1 % 16) * 16 + s2 / 4) &&& 0x0F = s2 / 4 := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; omega
  have hb2div : ((s2 % 4) * 64 + s3) >>> 6 = s2 % 4 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hb2mod : ((s2 % 4) * 64 + s3) &&& 0x3F = s3 := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 6]; omega
  refine ⟨hb0div, ?_, ?_, hb2mod⟩
  · rw [hb0mod, hb1div, shiftLeft_or_eq_add _ _ 4 (by omega)]; omega
  · rw [hb1mod, hb2div, shiftLeft_or_eq_add _ _ 2 (by omega)]; omega

/-- Under `strict = true`, accepted `decodeDataChars` input equals `encodeBytesList a false bs`. -/
theorem decodeDataChars_strict_eq_encode (a : Alphabet) (offset : Nat)
    (cs : List Char) (bs : List UInt8)
    (h : decodeDataChars a true offset cs = .ok bs) :
    cs = encodeBytesList a false bs := by
  match cs with
  | [] =>
    cases h; rfl
  | [_] =>
    cases h
  | [c0, c1] =>
    unfold decodeDataChars at h
    cases h0 : decodeChar? a c0 with
    | none => simp [h0] at h
    | some s0 =>
      cases h1 : decodeChar? a c1 with
      | none => simp [h0, h1] at h
      | some s1 =>
        by_cases hcan : (s1 &&& 0x0F) = 0
        · simp only [h0, h1, hcan, Bool.true_and, ne_eq, not_true_eq_false,
            decide_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
          subst h
          obtain ⟨hs0lt, hc0⟩ := decodeChar?_lt_64_and_encode a c0 s0 h0
          obtain ⟨hs1lt, hc1⟩ := decodeChar?_lt_64_and_encode a c1 s1 h1
          have hsext := sextet_canonical_1 s0 s1 hs0lt hs1lt hcan
          simp only [encodeBytesList, hsext.1, hsext.2, hc0, hc1]; rfl
        · simp [h0, h1, hcan] at h
  | [c0, c1, c2] =>
    unfold decodeDataChars at h
    cases h0 : decodeChar? a c0 with
    | none => simp [h0] at h
    | some s0 =>
      cases h1 : decodeChar? a c1 with
      | none => simp [h0, h1] at h
      | some s1 =>
        cases h2 : decodeChar? a c2 with
        | none => simp [h0, h1, h2] at h
        | some s2 =>
          by_cases hcan : (s2 &&& 0x03) = 0
          · simp only [h0, h1, h2, hcan, Bool.true_and, ne_eq, not_true_eq_false,
              decide_false, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
            subst h
            obtain ⟨hs0lt, hc0⟩ := decodeChar?_lt_64_and_encode a c0 s0 h0
            obtain ⟨hs1lt, hc1⟩ := decodeChar?_lt_64_and_encode a c1 s1 h1
            obtain ⟨hs2lt, hc2⟩ := decodeChar?_lt_64_and_encode a c2 s2 h2
            have hsext := sextet_canonical_2 s0 s1 s2 hs0lt hs1lt hs2lt hcan
            simp only [encodeBytesList, hsext.1, hsext.2.1, hsext.2.2, hc0, hc1, hc2]; rfl
          · simp [h0, h1, h2, hcan] at h
  | c0 :: c1 :: c2 :: c3 :: rest =>
    unfold decodeDataChars at h
    cases h0 : decodeChar? a c0 with
    | none => simp [h0] at h
    | some s0 =>
      cases h1 : decodeChar? a c1 with
      | none => simp [h0, h1] at h
      | some s1 =>
        cases h2 : decodeChar? a c2 with
        | none => simp [h0, h1, h2] at h
        | some s2 =>
          cases h3 : decodeChar? a c3 with
          | none => simp [h0, h1, h2, h3] at h
          | some s3 =>
            cases hrec : decodeDataChars a true (offset + 4) rest with
            | error err => simp [h0, h1, h2, h3, hrec] at h
            | ok bs' =>
              simp only [h0, h1, h2, h3, hrec, Except.ok.injEq] at h
              subst h
              obtain ⟨hs0lt, hc0⟩ := decodeChar?_lt_64_and_encode a c0 s0 h0
              obtain ⟨hs1lt, hc1⟩ := decodeChar?_lt_64_and_encode a c1 s1 h1
              obtain ⟨hs2lt, hc2⟩ := decodeChar?_lt_64_and_encode a c2 s2 h2
              obtain ⟨hs3lt, hc3⟩ := decodeChar?_lt_64_and_encode a c3 s3 h3
              have hsext := sextet_canonical_3 s0 s1 s2 s3 hs0lt hs1lt hs2lt hs3lt
              have hrest := decodeDataChars_strict_eq_encode a (offset + 4) rest bs' hrec
              simp only [encodeBytesList, hsext.1, hsext.2.1, hsext.2.2.1, hsext.2.2.2,
                hc0, hc1, hc2, hc3, hrest]

/-- A list whose elements are all `'='` equals `List.replicate cs.length '='`. -/
theorem list_all_eq_replicate {cs : List Char} (h : cs.all (· == '=') = true) :
    cs = List.replicate cs.length '=' := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
    exact ⟨h.1, ih h.2⟩

/-- `findFirstEq idx xs = some q` implies `q < idx + xs.length`. -/
theorem findFirstEq_lt_length (idx : Nat) (xs : List Char) (q : Nat)
    (h : findFirstEq idx xs = some q) : q < idx + xs.length := by
  induction xs generalizing idx with
  | nil => cases h
  | cons x xs ih =>
    unfold findFirstEq at h
    split at h
    · cases h; simp
    · have := ih (idx + 1) h; simp; omega

/-- Modulo-4 residue of unpadded Base64 length `(n * 4 + 2) / 3` from `n % 3`. -/
theorem unpadded_len_mod4 (n : Nat) :
    let len := (n * 4 + 2) / 3
    (n % 3 = 0 → len % 4 = 0) ∧
    (n % 3 = 1 → len % 4 = 2) ∧
    (n % 3 = 2 → len % 4 = 3) := by
  let k := n / 3
  have hk : n = 3 * k + n % 3 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hn : n = 3 * k := by omega
    have hmul : (3 * k * 4 + 2) / 3 = 4 * k := by omega
    rw [hn, hmul]
    omega
  · intro h1
    have hn : n = 3 * k + 1 := by omega
    have hmul : ((3 * k + 1) * 4 + 2) / 3 = 4 * k + 2 := by omega
    rw [hn, hmul]
    omega
  · intro h2
    have hn : n = 3 * k + 2 := by omega
    have hmul : ((3 * k + 2) * 4 + 2) / 3 = 4 * k + 3 := by omega
    rw [hn, hmul]
    omega

end LeanSwe.Base64.Proofs
