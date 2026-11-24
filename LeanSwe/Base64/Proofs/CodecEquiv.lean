import LeanSwe.Base64.Interface
import LeanSwe.Base64.Model

namespace LeanSwe.Base64.Proofs

open LeanSwe.Base64
open LeanSwe.Base64.Model

private theorem errorKindLabel_ne_empty (k : Base64ErrorKind) :
    Internal.errorKindLabel k ≠ "" := by
  cases k <;> decide

/-- `Internal.makeError` always constructs a non-empty diagnostic message. -/
theorem makeError_msg_ne_empty (k : Base64ErrorKind) (offset : Nat) (detail : String) :
    (Internal.makeError k offset detail).message ≠ "" := by
  unfold Internal.makeError
  intro heq
  have hlen := congrArg String.length heq
  simp only [String.length_append] at hlen
  have h1 : (" at offset " : String).length = 11 := rfl
  have h2 : (": " : String).length = 2 := rfl
  have h3 : ("" : String).length = 0 := rfl
  omega

private theorem scanInvalidChar_eq (a : Alphabet) (idx : Nat) (cs : List Char) :
    Internal.scanInvalidChar a idx cs = Model.scanInvalidChar a idx cs := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c cs ih =>
    unfold Internal.scanInvalidChar Model.scanInvalidChar
    change (if Model.isAlphabetChar a c || c == '=' then Internal.scanInvalidChar a (idx + 1) cs else some idx) =
      (if Model.isAlphabetChar a c || c == '=' then Model.scanInvalidChar a (idx + 1) cs else some idx)
    split
    · exact ih (idx + 1)
    · rfl

private theorem findFirstEq_eq (idx : Nat) (cs : List Char) :
    Internal.findFirstEq idx cs = Model.findFirstEq idx cs := by
  induction cs generalizing idx with
  | nil => rfl
  | cons c cs ih =>
    unfold Internal.findFirstEq Model.findFirstEq
    split
    · rfl
    · exact ih (idx + 1)

private theorem decodeChar?_eq (a : Alphabet) (c : Char) :
    Internal.decodeChar? a c = Model.decodeChar? a c := rfl

private theorem encodeSextet_eq (a : Alphabet) (s : Nat) :
    Internal.encodeSextet a s = Model.encodeSextet a s := rfl

private theorem decodeDataChars_spec (a : Alphabet) (strict : Bool) (offset : Nat) (cs : List Char) :
    (Internal.decodeDataChars a strict offset cs).mapError (fun e => (e.kind, e.offset)) =
        Model.decodeDataChars a strict offset cs ∧
      ∀ e, Internal.decodeDataChars a strict offset cs = .error e → e.message ≠ "" := by
  match cs with
  | [] =>
    exact ⟨rfl, fun _ h => by cases h⟩
  | [_] =>
    exact ⟨rfl, fun _ h => by cases h; exact makeError_msg_ne_empty _ _ _⟩
  | [c0, c1] =>
    unfold Internal.decodeDataChars Model.decodeDataChars
    simp only [decodeChar?_eq]
    cases h0 : Model.decodeChar? a c0 with
    | none =>
      exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
    | some s0 =>
      cases h1 : Model.decodeChar? a c1 with
      | none =>
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      | some s1 =>
        by_cases hst : (strict && decide ((s1 &&& 0x0F) ≠ 0)) = true
        · simp only [hst, ↓reduceIte, Except.mapError]
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        · simp only [hst, Bool.false_eq_true, ↓reduceIte, Except.mapError]
          exact ⟨trivial, fun _ he => by cases he⟩
  | [c0, c1, c2] =>
    unfold Internal.decodeDataChars Model.decodeDataChars
    simp only [decodeChar?_eq]
    cases h0 : Model.decodeChar? a c0 with
    | none =>
      exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
    | some s0 =>
      cases h1 : Model.decodeChar? a c1 with
      | none =>
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      | some s1 =>
        cases h2 : Model.decodeChar? a c2 with
        | none =>
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        | some s2 =>
          by_cases hst : (strict && decide ((s2 &&& 0x03) ≠ 0)) = true
          · simp only [hst, ↓reduceIte, Except.mapError]
            exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
          · simp only [hst, Bool.false_eq_true, ↓reduceIte, Except.mapError]
            exact ⟨trivial, fun _ he => by cases he⟩
  | c0 :: c1 :: c2 :: c3 :: rest =>
    have ih := decodeDataChars_spec a strict (offset + 4) rest
    unfold Internal.decodeDataChars Model.decodeDataChars
    simp only [decodeChar?_eq]
    cases h0 : Model.decodeChar? a c0 with
    | none =>
      exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
    | some s0 =>
      cases h1 : Model.decodeChar? a c1 with
      | none =>
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      | some s1 =>
        cases h2 : Model.decodeChar? a c2 with
        | none =>
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        | some s2 =>
          cases h3 : Model.decodeChar? a c3 with
          | none =>
            exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
          | some s3 =>
            cases hrec : Internal.decodeDataChars a strict (offset + 4) rest with
            | ok bs =>
              have hm : Model.decodeDataChars a strict (offset + 4) rest = .ok bs := by
                rw [← ih.1, hrec]; rfl
              simp only [hm, Except.mapError]
              exact ⟨trivial, fun _ he => by cases he⟩
            | error err =>
              have hm : Model.decodeDataChars a strict (offset + 4) rest = .error (err.kind, err.offset) := by
                rw [← ih.1, hrec]; rfl
              simp only [hm, Except.mapError]
              exact ⟨trivial, fun e he => by cases he; exact ih.2 err hrec⟩

private theorem decodeChars_spec (opts : DecodeOptions) (chars : List Char) :
    (Internal.decodeChars opts chars).mapError (fun e => (e.kind, e.offset)) =
        Model.decodeModelChars opts chars ∧
      ∀ e, Internal.decodeChars opts chars = .error e → e.message ≠ "" := by
  unfold Internal.decodeChars Model.decodeModelChars
  rw [scanInvalidChar_eq, findFirstEq_eq]
  cases hscan : Model.scanInvalidChar opts.alphabet 0 chars with
  | some idx =>
    exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
  | none =>
    cases heq : Model.findFirstEq 0 chars with
    | some p =>
      by_cases hforb : opts.padding = .forbidden
      · simp only [hforb, ↓reduceIte, Except.mapError]
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      · cases hall : (chars.drop p).all (· == '=')
        · simp only [hforb, ↓reduceIte, hall, Bool.not_false, Except.mapError]
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        · simp only [hforb, ↓reduceIte, hall, Bool.not_true, Bool.false_eq_true]
          split
          · exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
          · split
            · exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
            · exact decodeDataChars_spec opts.alphabet opts.strictCanonicalBits 0 (chars.take p)
    | none =>
      by_cases hmod1 : (chars.length % 4 == 1) = true
      · simp only [hmod1, ↓reduceIte, Except.mapError]
        exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
      · by_cases hreq : (opts.padding = .required && decide (chars.length % 4 ≠ 0)) = true
        · simp only [hmod1, Bool.false_eq_true, ↓reduceIte, hreq, Except.mapError]
          exact ⟨rfl, fun _ he => by cases he; exact makeError_msg_ne_empty _ _ _⟩
        · have hds := decodeDataChars_spec opts.alphabet opts.strictCanonicalBits 0 chars
          simp only [hmod1, Bool.false_eq_true, ↓reduceIte, hreq]
          exact hds

/-- `decodeWith` matches `Model.decodeModel` on `.ok` and `(kind, offset)` with non-empty errors. -/
theorem decodeWith_matchesModel_aux (opts : DecodeOptions) (s : String) :
    (decodeWith opts s).mapError (fun e => (e.kind, e.offset)) = decodeModel opts s ∧
      ∀ e, decodeWith opts s = .error e → e.message ≠ "" := by
  have h := decodeChars_spec opts s.toList
  change ((Internal.decodeChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray)).mapError
      (fun e => (e.kind, e.offset)) =
      (Model.decodeModelChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray) ∧
    ∀ e, (Internal.decodeChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray) = .error e →
      e.message ≠ ""
  cases hres : Internal.decodeChars opts s.toList with
  | ok bs =>
    have hm : Model.decodeModelChars opts s.toList = .ok bs := by
      rw [← h.1, hres]; rfl
    simp [Except.map, Except.mapError, hm]
  | error err =>
    have hm : Model.decodeModelChars opts s.toList = .error (err.kind, err.offset) := by
      rw [← h.1, hres]; rfl
    refine ⟨?_, fun e he => ?_⟩
    · simp [Except.map, Except.mapError, hm]
    · simp [Except.map] at he; subst he; exact h.2 err hres

/-- `Internal.encodeBytesList` equals `Model.encodeBytesList`. -/
theorem encodeBytesList_eq (a : Alphabet) (pad : Bool) (bs : List UInt8) :
    Internal.encodeBytesList a pad bs = Model.encodeBytesList a pad bs := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: rest =>
    unfold Internal.encodeBytesList Model.encodeBytesList
    simp only [encodeSextet_eq, encodeBytesList_eq]

/-- `encodeWith` equals `Model.encodeModel`. -/
theorem encodeWith_eq_encodeModel (opts : EncodeOptions) (bs : ByteArray) :
    encodeWith opts bs = encodeModel opts bs := by
  change String.ofList (Internal.encodeBytesList opts.alphabet opts.pad bs.data.toList) =
    String.ofList (Model.encodeBytesList opts.alphabet opts.pad bs.data.toList)
  rw [encodeBytesList_eq]

private theorem decodeChar?_encodeSextet_fin (a : Alphabet) (s : Fin 64) :
    decodeChar? a (encodeSextet a s.val) = some s.val := by
  revert s
  cases a <;> decide

/-- `decodeChar?` inverts `encodeSextet` on every 6-bit value `s < 64`. -/
theorem decodeChar?_encodeSextet (a : Alphabet) {s : Nat} (hs : s < 64) :
    decodeChar? a (encodeSextet a s) = some s :=
  decodeChar?_encodeSextet_fin a ⟨s, hs⟩

/-- Every encoded sextet `s < 64` belongs to `Alphabet`. -/
theorem isAlphabetChar_encodeSextet (a : Alphabet) {s : Nat} (hs : s < 64) :
    isAlphabetChar a (encodeSextet a s) = true := by
  unfold isAlphabetChar
  rw [decodeChar?_encodeSextet a hs]
  rfl

/-- Padding `'='` is never an alphabet data character. -/
theorem isAlphabetChar_eq_false (a : Alphabet) :
    isAlphabetChar a '=' = false := by
  cases a <;> decide

/-- Any `decodeChar?` hit produces `s < 64` that re-encodes to `c`. -/
theorem decodeChar?_lt_64_and_encode (a : Alphabet) (c : Char) (s : Nat)
    (h : decodeChar? a c = some s) : s < 64 ∧ encodeSextet a s = c := by
  unfold decodeChar? at h
  split at h
  · rename_i hAZ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAZ
    cases h
    have h1 : 'A'.toNat = 65 := rfl
    have h2 : 'Z'.toNat = 90 := rfl
    have h3 : 'A'.toNat ≤ c.toNat := Char.le_def.mp hAZ.1
    have h4 : c.toNat ≤ 'Z'.toNat := Char.le_def.mp hAZ.2
    have hlt : c.toNat - 'A'.toNat < 26 := by omega
    refine ⟨by omega, ?_⟩
    unfold encodeSextet
    simp only [hlt, ↓reduceIte]
    have hsum : 'A'.toNat + (c.toNat - 'A'.toNat) = c.toNat := by omega
    rw [hsum, Char.ofNat_toNat]
  · split at h
    · rename_i _ haz
      simp only [Bool.and_eq_true, decide_eq_true_eq] at haz
      cases h
      have h1 : 'a'.toNat = 97 := rfl
      have h2 : 'z'.toNat = 122 := rfl
      have h3 : 'a'.toNat ≤ c.toNat := Char.le_def.mp haz.1
      have h4 : c.toNat ≤ 'z'.toNat := Char.le_def.mp haz.2
      have hlt : c.toNat - 'a'.toNat + 26 < 52 := by omega
      refine ⟨by omega, ?_⟩
      unfold encodeSextet
      have hnot1 : ¬(c.toNat - 'a'.toNat + 26 < 26) := by omega
      simp only [hnot1, ↓reduceIte, hlt]
      have hsum : 'a'.toNat + (c.toNat - 'a'.toNat + 26 - 26) = c.toNat := by omega
      rw [hsum, Char.ofNat_toNat]
    · split at h
      · rename_i _ _ h09
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h09
        cases h
        have h1 : '0'.toNat = 48 := rfl
        have h2 : '9'.toNat = 57 := rfl
        have h3 : '0'.toNat ≤ c.toNat := Char.le_def.mp h09.1
        have h4 : c.toNat ≤ '9'.toNat := Char.le_def.mp h09.2
        have hlt : c.toNat - '0'.toNat + 52 < 62 := by omega
        refine ⟨by omega, ?_⟩
        unfold encodeSextet
        have hnot1 : ¬(c.toNat - '0'.toNat + 52 < 26) := by omega
        have hnot2 : ¬(c.toNat - '0'.toNat + 52 < 52) := by omega
        simp only [hnot1, hnot2, ↓reduceIte, hlt]
        have hsum : '0'.toNat + (c.toNat - '0'.toNat + 52 - 52) = c.toNat := by omega
        rw [hsum, Char.ofNat_toNat]
      · cases a with
        | standard =>
          simp only at h
          split at h
          · rename_i hc; cases h; simp at hc; subst hc; exact ⟨by omega, rfl⟩
          · split at h
            · rename_i hc; cases h; simp at hc; subst hc; exact ⟨by omega, rfl⟩
            · cases h
        | urlSafe =>
          simp only at h
          split at h
          · rename_i hc; cases h; simp at hc; subst hc; exact ⟨by omega, rfl⟩
          · split at h
            · rename_i hc; cases h; simp at hc; subst hc; exact ⟨by omega, rfl⟩
            · cases h

/-- Bitwise `(a <<< k) ||| b` equals `a * 2 ^ k + b` when `b < 2 ^ k`. -/
theorem shiftLeft_or_eq_add (a b k : Nat) (hb : b < 2 ^ k) :
    (a <<< k) ||| b = a * 2 ^ k + b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.mul_comm a (2 ^ k), Nat.testBit_two_pow_mul_add a hb j]
  by_cases hj : j < k
  · have hge : ¬(j ≥ k) := by omega
    simp [hj, hge]
  · have hge : j ≥ k := by omega
    have hfalse : b.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hge))
    simp [hj, hge, hfalse]

/-- Top 6 bits of a `UInt8` lie below `64`. -/
theorem u8_hi6_lt64 (x : UInt8) : x.toNat >>> 2 < 64 := by
  have hx := UInt8.toNat_lt x
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- Low 2 bits of a `UInt8` lie below `4`. -/
theorem u8_lo2_lt4 (x : UInt8) : (x.toNat &&& 0x03) < 4 := by
  have hmod : x.toNat &&& 0x03 = x.toNat % 2 ^ 2 := Nat.and_two_pow_sub_one_eq_mod x.toNat 2
  rw [hmod]
  omega

/-- Top 4 bits of a `UInt8` lie below `16`. -/
theorem u8_hi4_lt16 (x : UInt8) : (x.toNat >>> 4) < 16 := by
  have hx := UInt8.toNat_lt x
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- Low 4 bits of a `UInt8` lie below `16`. -/
theorem u8_lo4_lt16 (x : UInt8) : (x.toNat &&& 0x0F) < 16 := by
  have hmod : x.toNat &&& 0x0F = x.toNat % 2 ^ 4 := Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  rw [hmod]
  omega

/-- Top 2 bits of a `UInt8` lie below `4`. -/
theorem u8_hi2_lt4 (x : UInt8) : (x.toNat >>> 6) < 4 := by
  have hx := UInt8.toNat_lt x
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- Low 6 bits of a `UInt8` lie below `64`. -/
theorem u8_lo6_lt64 (x : UInt8) : (x.toNat &&& 0x3F) < 64 := by
  have hmod : x.toNat &&& 0x3F = x.toNat % 2 ^ 6 := Nat.and_two_pow_sub_one_eq_mod x.toNat 6
  rw [hmod]
  omega

/-- Shifted low 2 bits of a `UInt8` lie below `64`. -/
theorem u8_lo2_shift4_lt64 (x : UInt8) : ((x.toNat &&& 0x03) <<< 4) < 64 := by
  have h1 := u8_lo2_lt4 x
  rw [Nat.shiftLeft_eq]
  omega

/-- Shifted low 2 bits of a `UInt8` have zero low 4 pad bits. -/
theorem u8_lo2_shift4_canon (x : UInt8) : (((x.toNat &&& 0x03) <<< 4) &&& 0x0F) = 0 := by
  rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod _ 4]
  omega

/-- Shifted low 4 bits of a `UInt8` lie below `64`. -/
theorem u8_lo4_shift2_lt64 (x : UInt8) : ((x.toNat &&& 0x0F) <<< 2) < 64 := by
  have h1 := u8_lo4_lt16 x
  rw [Nat.shiftLeft_eq]
  omega

/-- Shifted low 4 bits of a `UInt8` have zero low 2 pad bits. -/
theorem u8_lo4_shift2_canon (x : UInt8) : (((x.toNat &&& 0x0F) <<< 2) &&& 0x03) = 0 := by
  rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod _ 2]
  omega

/-- Single-byte Base64 sextet split recombines to `x.toNat`. -/
theorem u8_recombine_1byte (x : UInt8) :
    (((x.toNat >>> 2) <<< 2) ||| (((x.toNat &&& 0x03) <<< 4) >>> 4)) = x.toNat := by
  have hlo : (((x.toNat &&& 0x03) <<< 4) >>> 4) = x.toNat % 4 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod _ 2]
    omega
  rw [hlo, shiftLeft_or_eq_add _ _ 2 (by omega), Nat.shiftRight_eq_div_pow]
  omega

/-- Packing 2-bit and 4-bit fields into a 6-bit sextet preserves bounds and projections. -/
theorem pack4_4_props (a : Fin 4) (b : Fin 16) :
    ((a.val <<< 4) ||| b.val) < 64 ∧
    (((a.val <<< 4) ||| b.val) >>> 4) = a.val ∧
    (((a.val <<< 4) ||| b.val) &&& 0x0F) = b.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hadd : (a.val <<< 4) ||| b.val = a.val * 2 ^ 4 + b.val :=
    shiftLeft_or_eq_add a.val b.val 4 (by omega)
  rw [hadd, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 4]
  omega

/-- Packing 4-bit and 2-bit fields into a 6-bit sextet preserves bounds and projections. -/
theorem pack4_2_props (a : Fin 16) (b : Fin 4) :
    ((a.val <<< 2) ||| b.val) < 64 ∧
    (((a.val <<< 2) ||| b.val) >>> 2) = a.val ∧
    (((a.val <<< 2) ||| b.val) &&& 0x03) = b.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hadd : (a.val <<< 2) ||| b.val = a.val * 2 ^ 2 + b.val :=
    shiftLeft_or_eq_add a.val b.val 2 (by omega)
  rw [hadd, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 2]
  omega

/-- First byte reconstruction from sextets 0 and 1. -/
theorem u8_recombine_hi2_lo4 (x y : UInt8) :
    ((((x.toNat >>> 2) <<< 2) ||| ((((x.toNat &&& 0x03) <<< 4) ||| (y.toNat >>> 4)) >>> 4)) = x.toNat) := by
  have hp := pack4_4_props ⟨x.toNat &&& 0x03, u8_lo2_lt4 x⟩ ⟨y.toNat >>> 4, u8_hi4_lt16 y⟩
  rw [hp.2.1]
  have hlo := u8_lo2_lt4 x
  rw [shiftLeft_or_eq_add _ _ 2 hlo, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 2]
  omega

/-- Second byte reconstruction in a full 3-byte quantum. -/
theorem u8_recombine_4_4 (x y z : UInt8) :
    ((((((x.toNat &&& 0x03) <<< 4) ||| (y.toNat >>> 4)) &&& 0x0F) <<< 4) |||
      ((((y.toNat &&& 0x0F) <<< 2) ||| (z.toNat >>> 6)) >>> 2)) = y.toNat := by
  have hp1 := pack4_4_props ⟨x.toNat &&& 0x03, u8_lo2_lt4 x⟩ ⟨y.toNat >>> 4, u8_hi4_lt16 y⟩
  have hp2 := pack4_2_props ⟨y.toNat &&& 0x0F, u8_lo4_lt16 y⟩ ⟨z.toNat >>> 6, u8_hi2_lt4 z⟩
  rw [hp1.2.2, hp2.2.1]
  dsimp only
  have hlo := u8_lo4_lt16 y
  rw [shiftLeft_or_eq_add _ _ 4 hlo, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 4]
  omega

/-- Second byte reconstruction in a final 2-byte quantum. -/
theorem u8_recombine_4_4_final (x y : UInt8) :
    ((((((x.toNat &&& 0x03) <<< 4) ||| (y.toNat >>> 4)) &&& 0x0F) <<< 4) |||
      (((y.toNat &&& 0x0F) <<< 2) >>> 2)) = y.toNat := by
  have hp1 := pack4_4_props ⟨x.toNat &&& 0x03, u8_lo2_lt4 x⟩ ⟨y.toNat >>> 4, u8_hi4_lt16 y⟩
  have hp2 := pack4_2_props ⟨y.toNat &&& 0x0F, u8_lo4_lt16 y⟩ ⟨0, by decide⟩
  simp only [Nat.or_zero] at hp2
  rw [hp1.2.2, hp2.2.1]
  dsimp only
  have hlo := u8_lo4_lt16 y
  rw [shiftLeft_or_eq_add _ _ 4 hlo, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 4]
  omega

/-- Third byte reconstruction in a full 3-byte quantum. -/
theorem u8_recombine_2_6 (y z : UInt8) :
    ((((((y.toNat &&& 0x0F) <<< 2) ||| (z.toNat >>> 6)) &&& 0x03) <<< 6) |||
      (z.toNat &&& 0x3F)) = z.toNat := by
  have hp := pack4_2_props ⟨y.toNat &&& 0x0F, u8_lo4_lt16 y⟩ ⟨z.toNat >>> 6, u8_hi2_lt4 z⟩
  rw [hp.2.2]
  dsimp only
  have hlo := u8_lo6_lt64 z
  rw [shiftLeft_or_eq_add _ _ 6 hlo, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 6]
  omega

end LeanSwe.Base64.Proofs
