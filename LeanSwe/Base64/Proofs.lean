import LeanSwe.Base64.Interface
import LeanSwe.Base64.Model
import LeanSwe.Base64.SpecTests

namespace LeanSwe.Base64.Proofs

open Core
open Core.NondetTest
open LeanSwe.Base64
open LeanSwe.Base64.Model

private theorem errorKindLabel_ne_empty (k : Base64ErrorKind) :
    Internal.errorKindLabel k ≠ "" := by
  cases k <;> decide

private theorem makeError_msg_ne_empty (k : Base64ErrorKind) (offset : Nat) (detail : String) :
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

private theorem decodeWith_matchesModel_aux (opts : DecodeOptions) (s : String) :
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

private theorem encodeBytesList_eq (a : Alphabet) (pad : Bool) (bs : List UInt8) :
    Internal.encodeBytesList a pad bs = Model.encodeBytesList a pad bs := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: rest =>
    unfold Internal.encodeBytesList Model.encodeBytesList
    simp only [encodeSextet_eq, encodeBytesList_eq]

private theorem encodeWith_eq_encodeModel (opts : EncodeOptions) (bs : ByteArray) :
    encodeWith opts bs = encodeModel opts bs := by
  change String.ofList (Internal.encodeBytesList opts.alphabet opts.pad bs.data.toList) =
    String.ofList (Model.encodeBytesList opts.alphabet opts.pad bs.data.toList)
  rw [encodeBytesList_eq]

private theorem decodeChar?_encodeSextet_fin (a : Alphabet) (s : Fin 64) :
    decodeChar? a (encodeSextet a s.val) = some s.val := by
  revert s
  cases a <;> decide

private theorem decodeChar?_encodeSextet (a : Alphabet) {s : Nat} (hs : s < 64) :
    decodeChar? a (encodeSextet a s) = some s :=
  decodeChar?_encodeSextet_fin a ⟨s, hs⟩

private theorem isAlphabetChar_encodeSextet (a : Alphabet) {s : Nat} (hs : s < 64) :
    isAlphabetChar a (encodeSextet a s) = true := by
  unfold isAlphabetChar
  rw [decodeChar?_encodeSextet a hs]
  rfl

private theorem isAlphabetChar_eq_false (a : Alphabet) :
    isAlphabetChar a '=' = false := by
  cases a <;> decide

private theorem decodeChar?_lt_64_and_encode (a : Alphabet) (c : Char) (s : Nat)
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

private theorem shiftLeft_or_eq_add (a b k : Nat) (hb : b < 2 ^ k) :
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

private theorem u8_hi6_lt64 (x : UInt8) : x.toNat >>> 2 < 64 := by
  have hx := UInt8.toNat_lt x
  rw [Nat.shiftRight_eq_div_pow]
  omega

private theorem u8_lo2_lt4 (x : UInt8) : (x.toNat &&& 0x03) < 4 := by
  have hmod : x.toNat &&& 0x03 = x.toNat % 2 ^ 2 := Nat.and_two_pow_sub_one_eq_mod x.toNat 2
  rw [hmod]
  omega

private theorem u8_hi4_lt16 (x : UInt8) : (x.toNat >>> 4) < 16 := by
  have hx := UInt8.toNat_lt x
  rw [Nat.shiftRight_eq_div_pow]
  omega

private theorem u8_lo4_lt16 (x : UInt8) : (x.toNat &&& 0x0F) < 16 := by
  have hmod : x.toNat &&& 0x0F = x.toNat % 2 ^ 4 := Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  rw [hmod]
  omega

private theorem u8_hi2_lt4 (x : UInt8) : (x.toNat >>> 6) < 4 := by
  have hx := UInt8.toNat_lt x
  rw [Nat.shiftRight_eq_div_pow]
  omega

private theorem u8_lo6_lt64 (x : UInt8) : (x.toNat &&& 0x3F) < 64 := by
  have hmod : x.toNat &&& 0x3F = x.toNat % 2 ^ 6 := Nat.and_two_pow_sub_one_eq_mod x.toNat 6
  rw [hmod]
  omega

private theorem u8_lo2_shift4_lt64 (x : UInt8) : ((x.toNat &&& 0x03) <<< 4) < 64 := by
  have h1 := u8_lo2_lt4 x
  rw [Nat.shiftLeft_eq]
  omega

private theorem u8_lo2_shift4_canon (x : UInt8) : (((x.toNat &&& 0x03) <<< 4) &&& 0x0F) = 0 := by
  rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod _ 4]
  omega

private theorem u8_lo4_shift2_lt64 (x : UInt8) : ((x.toNat &&& 0x0F) <<< 2) < 64 := by
  have h1 := u8_lo4_lt16 x
  rw [Nat.shiftLeft_eq]
  omega

private theorem u8_lo4_shift2_canon (x : UInt8) : (((x.toNat &&& 0x0F) <<< 2) &&& 0x03) = 0 := by
  rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod _ 2]
  omega

private theorem u8_recombine_1byte (x : UInt8) :
    (((x.toNat >>> 2) <<< 2) ||| (((x.toNat &&& 0x03) <<< 4) >>> 4)) = x.toNat := by
  have hlo : (((x.toNat &&& 0x03) <<< 4) >>> 4) = x.toNat % 4 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod _ 2]
    omega
  rw [hlo, shiftLeft_or_eq_add _ _ 2 (by omega), Nat.shiftRight_eq_div_pow]
  omega

private theorem pack4_4_props (a : Fin 4) (b : Fin 16) :
    ((a.val <<< 4) ||| b.val) < 64 ∧
    (((a.val <<< 4) ||| b.val) >>> 4) = a.val ∧
    (((a.val <<< 4) ||| b.val) &&& 0x0F) = b.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hadd : (a.val <<< 4) ||| b.val = a.val * 2 ^ 4 + b.val :=
    shiftLeft_or_eq_add a.val b.val 4 (by omega)
  rw [hadd, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 4]
  omega

private theorem pack4_2_props (a : Fin 16) (b : Fin 4) :
    ((a.val <<< 2) ||| b.val) < 64 ∧
    (((a.val <<< 2) ||| b.val) >>> 2) = a.val ∧
    (((a.val <<< 2) ||| b.val) &&& 0x03) = b.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hadd : (a.val <<< 2) ||| b.val = a.val * 2 ^ 2 + b.val :=
    shiftLeft_or_eq_add a.val b.val 2 (by omega)
  rw [hadd, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 2]
  omega

private theorem u8_recombine_hi2_lo4 (x y : UInt8) :
    ((((x.toNat >>> 2) <<< 2) ||| ((((x.toNat &&& 0x03) <<< 4) ||| (y.toNat >>> 4)) >>> 4)) = x.toNat) := by
  have hp := pack4_4_props ⟨x.toNat &&& 0x03, u8_lo2_lt4 x⟩ ⟨y.toNat >>> 4, u8_hi4_lt16 y⟩
  rw [hp.2.1]
  have hlo := u8_lo2_lt4 x
  rw [shiftLeft_or_eq_add _ _ 2 hlo, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 2]
  omega

private theorem u8_recombine_4_4 (x y z : UInt8) :
    ((((((x.toNat &&& 0x03) <<< 4) ||| (y.toNat >>> 4)) &&& 0x0F) <<< 4) |||
      ((((y.toNat &&& 0x0F) <<< 2) ||| (z.toNat >>> 6)) >>> 2)) = y.toNat := by
  have hp1 := pack4_4_props ⟨x.toNat &&& 0x03, u8_lo2_lt4 x⟩ ⟨y.toNat >>> 4, u8_hi4_lt16 y⟩
  have hp2 := pack4_2_props ⟨y.toNat &&& 0x0F, u8_lo4_lt16 y⟩ ⟨z.toNat >>> 6, u8_hi2_lt4 z⟩
  rw [hp1.2.2, hp2.2.1]
  dsimp only
  have hlo := u8_lo4_lt16 y
  rw [shiftLeft_or_eq_add _ _ 4 hlo, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 4]
  omega

private theorem u8_recombine_4_4_final (x y : UInt8) :
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

private theorem u8_recombine_2_6 (y z : UInt8) :
    ((((((y.toNat &&& 0x0F) <<< 2) ||| (z.toNat >>> 6)) &&& 0x03) <<< 6) |||
      (z.toNat &&& 0x3F)) = z.toNat := by
  have hp := pack4_2_props ⟨y.toNat &&& 0x0F, u8_lo4_lt16 y⟩ ⟨z.toNat >>> 6, u8_hi2_lt4 z⟩
  rw [hp.2.2]
  dsimp only
  have hlo := u8_lo6_lt64 z
  rw [shiftLeft_or_eq_add _ _ 6 hlo, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod _ 6]
  omega

private theorem encodeBytesList_split (a : Alphabet) (pad : Bool) (bs : List UInt8) :
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

private theorem encodeBytesList_unpadded_props (a : Alphabet) (bs : List UInt8) :
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

private theorem decodeModelChars_encodeBytesList
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

private theorem decodeDataChars_strict_eq_encode (a : Alphabet) (offset : Nat)
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

private theorem list_all_eq_replicate {cs : List Char} (h : cs.all (· == '=') = true) :
    cs = List.replicate cs.length '=' := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
    exact ⟨h.1, ih h.2⟩

private theorem findFirstEq_lt_length (idx : Nat) (xs : List Char) (q : Nat)
    (h : findFirstEq idx xs = some q) : q < idx + xs.length := by
  induction xs generalizing idx with
  | nil => cases h
  | cons x xs ih =>
    unfold findFirstEq at h
    split at h
    · cases h; simp
    · have := ih (idx + 1) h; simp; omega

private theorem unpadded_len_mod4 (n : Nat) :
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

private theorem decodeModelChars_canonical_unique (decOpts : DecodeOptions)
    (chars : List Char) (bs : List UInt8)
    (hstrict : decOpts.strictCanonicalBits = true)
    (hfixed : decOpts.padding ≠ .optional)
    (hdec : decodeModelChars decOpts chars = .ok bs) :
    chars = encodeBytesList decOpts.alphabet (decOpts.padding == .required) bs := by
  unfold decodeModelChars at hdec
  cases hscan : scanInvalidChar decOpts.alphabet 0 chars with
  | some idx => simp [hscan] at hdec
  | none =>
    simp only [hscan] at hdec
    cases heq : findFirstEq 0 chars with
    | some p =>
      simp only [heq] at hdec
      by_cases hforb : decOpts.padding = .forbidden
      · simp [hforb] at hdec
      · cases hall : (chars.drop p).all (· == '=')
        · simp [hforb, hall] at hdec
        · by_cases hmod : chars.length % 4 ≠ 0
          · simp [hforb, hall, hmod] at hdec
          · by_cases hgt : chars.length - p > 2
            · simp [hforb, hall, hmod, hgt] at hdec
            · have hreq : decOpts.padding = .required := by
                cases hp : decOpts.padding <;> simp_all
              have hreqBool : (decOpts.padding == .required) = true := by rw [hreq]; rfl
              rw [hreqBool]
              simp only [hforb, ↓reduceIte, hall, Bool.not_true, Bool.false_eq_true, hmod,
                gt_iff_lt, hgt] at hdec
              rw [hstrict] at hdec
              have hdata := decodeDataChars_strict_eq_encode decOpts.alphabet 0 (chars.take p) bs hdec
              have hdropRep := list_all_eq_replicate hall
              have hsplit : chars = chars.take p ++ chars.drop p := (List.take_append_drop p chars).symm
              have hlenDrop : (chars.drop p).length = chars.length - p := List.length_drop
              have hpLt : p < chars.length := by
                have := findFirstEq_lt_length 0 chars p heq
                omega
              have hlenTake : (chars.take p).length = p := by
                rw [List.length_take]
                omega
              have hlenData := (encodeBytesList_unpadded_props decOpts.alphabet bs).1
              rw [← hdata, hlenTake] at hlenData
              have hpEq : p = (bs.length * 4 + 2) / 3 := by
                simpa [expectedEncodedLength] using hlenData
              have hpMod := unpadded_len_mod4 bs.length
              have hEqCount : chars.length - p = (3 - bs.length % 3) % 3 := by
                have hmod3 : bs.length % 3 = 0 ∨ bs.length % 3 = 1 ∨ bs.length % 3 = 2 := by omega
                rcases hmod3 with h0 | h1 | h2
                · exfalso
                  have h0' : p % 4 = 0 := by rw [hpEq]; exact hpMod.1 h0
                  omega
                · have hp4 : p % 4 = 2 := by rw [hpEq]; exact hpMod.2.1 h1
                  omega
                · have hp4 : p % 4 = 3 := by rw [hpEq]; exact hpMod.2.2 h2
                  omega
              rw [hsplit, hdata, hdropRep, hlenDrop, hEqCount]
              have henc := encodeBytesList_split decOpts.alphabet true bs
              simpa [expectedPaddingCount] using henc.symm
    | none =>
      simp only [heq] at hdec
      by_cases hmod1 : (chars.length % 4 == 1) = true
      · simp [hmod1] at hdec
      · by_cases hreq : (decOpts.padding = .required && decide (chars.length % 4 ≠ 0)) = true
        · simp only [hmod1, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hdec hreq
          simp [hreq] at hdec
        · simp only [hmod1, Bool.false_eq_true, ↓reduceIte, hreq] at hdec
          rw [hstrict] at hdec
          have hdata := decodeDataChars_strict_eq_encode decOpts.alphabet 0 chars bs hdec
          have hpCases : decOpts.padding = .required ∨ decOpts.padding = .forbidden := by
            cases hpad : decOpts.padding <;> simp_all
          rcases hpCases with hp | hp
          · rw [hp] at hreq
            simp only [Bool.and_eq_true, decide_eq_true_eq, true_and] at hreq
            have hmod4 : chars.length % 4 = 0 := by omega
            have hlenData := (encodeBytesList_unpadded_props decOpts.alphabet bs).1
            have hpEq : chars.length = (bs.length * 4 + 2) / 3 := by
              rw [hdata, hlenData, expectedEncodedLength]; rfl
            have hpMod := unpadded_len_mod4 bs.length
            have hbs3 : bs.length % 3 = 0 := by
              have hmod3 : bs.length % 3 = 0 ∨ bs.length % 3 = 1 ∨ bs.length % 3 = 2 := by omega
              rcases hmod3 with h0 | h1 | h2
              · exact h0
              · have := hpMod.2.1 h1; omega
              · have := hpMod.2.2 h2; omega
            have henc := encodeBytesList_split decOpts.alphabet true bs
            have hrep0 : List.replicate (expectedPaddingCount { alphabet := decOpts.alphabet, pad := true } bs.length) '=' = [] := by
              simp [expectedPaddingCount, hbs3]
            rw [hrep0, List.append_nil] at henc
            have hreqB : (PaddingMode.required == PaddingMode.required) = true := rfl
            rw [hp, hreqB, henc, hdata]
          · have hreqB : (PaddingMode.forbidden == PaddingMode.required) = false := rfl
            rw [hp, hreqB, hdata]

/-- `test_base64_onError_returnsNonEmptyMessage` holds for `defaultApi`. -/
theorem allPass_onError_returnsNonEmptyMessage :
    AllPass (test_base64_onError_returnsNonEmptyMessage defaultApi) := by
  intro opts s
  have hd := decodeWith_matchesModel_aux { alphabet := .standard, padding := .required, strictCanonicalBits := true } s
  have hu := decodeWith_matchesModel_aux { alphabet := .urlSafe, padding := .optional, strictCanonicalBits := true } s
  have hw := decodeWith_matchesModel_aux opts s
  dsimp [test_base64_onError_returnsNonEmptyMessage, defaultApi, Internal.defaultApi,
    bind, pure, Core.NondetTest.assert]
  cases h1 : Internal.decode s with
  | ok _ =>
    cases h2 : Internal.decodeUrl s with
    | ok _ =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨trivial, trivial, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨trivial, trivial, hw.2 e3 h3, trivial⟩
    | error e2 =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨trivial, hu.2 e2 h2, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨trivial, hu.2 e2 h2, hw.2 e3 h3, trivial⟩
  | error e1 =>
    cases h2 : Internal.decodeUrl s with
    | ok _ =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨hd.2 e1 h1, trivial, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨hd.2 e1 h1, trivial, hw.2 e3 h3, trivial⟩
    | error e2 =>
      cases h3 : Internal.decodeWith opts s with
      | ok _ => dsimp only; exact ⟨hd.2 e1 h1, hu.2 e2 h2, trivial, trivial⟩
      | error e3 => dsimp only; exact ⟨hd.2 e1 h1, hu.2 e2 h2, hw.2 e3 h3, trivial⟩

/-- `test_base64_wrappers_matchOptions` holds for `defaultApi`. -/
theorem allPass_wrappers_matchOptions :
    AllPass (test_base64_wrappers_matchOptions defaultApi) := by
  intro bs s
  dsimp [test_base64_wrappers_matchOptions, defaultApi, bind, pure, Core.NondetTest.assert]
  exact ⟨rfl, rfl, rfl, rfl, trivial⟩

/-- `test_base64_encodeWith_matchesModel` holds for `defaultApi`. -/
theorem allPass_encodeWith_matchesModel :
    AllPass (test_base64_encodeWith_matchesModel defaultApi) := by
  intro opts bs
  dsimp [test_base64_encodeWith_matchesModel, defaultApi, Core.NondetTest.assert]
  exact ⟨encodeWith_eq_encodeModel opts bs, trivial⟩

/-- `test_base64_decodeWith_matchesModel` holds for `defaultApi`. -/
theorem allPass_decodeWith_matchesModel :
    AllPass (test_base64_decodeWith_matchesModel defaultApi) := by
  intro opts s
  have h := decodeWith_matchesModel_aux opts s
  dsimp [test_base64_decodeWith_matchesModel, defaultApi, Internal.defaultApi,
    Core.NondetTest.assert]
  cases ha : Internal.decodeWith opts s with
  | ok actual =>
    have ha' : decodeWith opts s = .ok actual := ha
    have hm : decodeModel opts s = .ok actual := by rw [← h.1, ha']; rfl
    simp [hm]
  | error e =>
    have ha' : decodeWith opts s = .error e := ha
    have hm : decodeModel opts s = .error (e.kind, e.offset) := by rw [← h.1, ha']; rfl
    simp [hm, h.2 e ha']

/-- Generalized round-trip theorem: `decodeWith decOpts (encodeWith encOpts bs) = .ok bs` under compatible alphabet and padding options. -/
theorem decodeWith_encodeWith_roundTrip
    (encOpts : EncodeOptions) (decOpts : DecodeOptions) (bs : ByteArray)
    (halph : decOpts.alphabet = encOpts.alphabet)
    (hpad1 : encOpts.pad = false ∨ decOpts.padding ≠ .forbidden ∨ bs.size % 3 = 0)
    (hpad2 : encOpts.pad = true ∨ decOpts.padding ≠ .required ∨ bs.size % 3 = 0) :
    decodeWith decOpts (encodeWith encOpts bs) = .ok bs := by
  have hmod := decodeWith_matchesModel_aux decOpts (encodeWith encOpts bs)
  have hsz : bs.data.toList.length = bs.size := by
    cases bs with
    | mk arr => simp [ByteArray.size]
  have hmc : decodeModelChars decOpts (encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList) =
      .ok bs.data.toList := by
    apply decodeModelChars_encodeBytesList encOpts decOpts bs.data.toList halph
    · simpa [hsz] using hpad1
    · simpa [hsz] using hpad2
  have htoList : (encodeWith encOpts bs).toList = encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList := by
    change (String.ofList (Internal.encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList)).toList =
      encodeBytesList encOpts.alphabet encOpts.pad bs.data.toList
    rw [encodeBytesList_eq, String.toList_ofList]
  have hdm : decodeModel decOpts (encodeWith encOpts bs) = .ok bs := by
    unfold decodeModel
    rw [htoList, hmc]
    cases bs with
    | mk arr => simp [Except.map]
  cases ha : decodeWith decOpts (encodeWith encOpts bs) with
  | ok actual =>
    have : decodeModel decOpts (encodeWith encOpts bs) = .ok actual := by
      rw [← hmod.1, ha]; rfl
    rw [hdm] at this
    cases this
    rfl
  | error e =>
    have : decodeModel decOpts (encodeWith encOpts bs) = .error (e.kind, e.offset) := by
      rw [← hmod.1, ha]; rfl
    rw [hdm] at this
    cases this

/-- Standard `encode` / `decode` round-trip theorem for arbitrary `ByteArray`. -/
theorem decode_encode_roundTrip (bs : ByteArray) :
    decode (encode bs) = .ok bs :=
  decodeWith_encodeWith_roundTrip defaultEncodeOptions defaultDecodeOptions bs rfl
    (Or.inr (Or.inl (by decide))) (Or.inl rfl)

/-- URL-safe `encodeUrl` / `decodeUrl` round-trip theorem for arbitrary `ByteArray`. -/
theorem decodeUrl_encodeUrl_roundTrip (bs : ByteArray) :
    decodeUrl (encodeUrl bs) = .ok bs :=
  decodeWith_encodeWith_roundTrip urlEncodeOptions urlDecodeOptions bs rfl
    (Or.inl rfl) (Or.inr (Or.inl (by decide)))

/-- `test_base64_roundTrip_defaultAndUrl` holds for `defaultApi`. -/
theorem allPass_roundTrip_defaultAndUrl :
    AllPass (test_base64_roundTrip_defaultAndUrl defaultApi) := by
  intro bs
  dsimp [test_base64_roundTrip_defaultAndUrl, defaultApi, bind, pure, Core.NondetTest.assert]
  exact ⟨decode_encode_roundTrip bs, decodeUrl_encodeUrl_roundTrip bs, trivial⟩

/-- `test_base64_roundTrip_compatibleOptions` holds for `defaultApi`. -/
theorem allPass_roundTrip_compatibleOptions :
    AllPass (test_base64_roundTrip_compatibleOptions defaultApi) := by
  intro bs encOpts decOpts halph hpad1 hpad2
  dsimp [test_base64_roundTrip_compatibleOptions, defaultApi, Core.NondetTest.assert]
  exact ⟨decodeWith_encodeWith_roundTrip encOpts decOpts bs halph hpad1 hpad2, trivial⟩

/-- `CanReach` witness for `test_base64_roundTrip_compatibleOptions`. -/
theorem canReach_roundTrip_compatibleOptions :
    CanReach (test_base64_roundTrip_compatibleOptions defaultApi) := by
  dsimp [Core.CanReach, test_base64_roundTrip_compatibleOptions, defaultApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, bind, pure]
  refine ⟨ByteArray.empty, defaultEncodeOptions, defaultDecodeOptions, rfl,
    Or.inr (Or.inl (by decide)), Or.inl rfl, ?_, trivial⟩
  exact decode_encode_roundTrip ByteArray.empty

/-- Output length, alphabet character-set, and trailing `'='` count invariants for `encodeWith`. -/
theorem encodeWith_charset_and_length (opts : EncodeOptions) (bs : ByteArray) :
    let chars := (encodeWith opts bs).toList
    let expLen := expectedEncodedLength opts bs.size
    let expEq := expectedPaddingCount opts bs.size
    chars.length = expLen ∧
    (chars.take (chars.length - expEq)).all (isAlphabetChar opts.alphabet) = true ∧
    (chars.drop (chars.length - expEq)).all (· == '=') = true ∧
    (chars.drop (chars.length - expEq)).length = expEq := by
  have htoList : (encodeWith opts bs).toList = encodeBytesList opts.alphabet opts.pad bs.data.toList := by
    change (String.ofList (Internal.encodeBytesList opts.alphabet opts.pad bs.data.toList)).toList =
      encodeBytesList opts.alphabet opts.pad bs.data.toList
    rw [encodeBytesList_eq, String.toList_ofList]
  have hsplit := encodeBytesList_split opts.alphabet opts.pad bs.data.toList
  have hprops := encodeBytesList_unpadded_props opts.alphabet bs.data.toList
  have hsz : bs.data.toList.length = bs.size := by
    cases bs with
    | mk arr => simp [ByteArray.size]
  have heqCount : expectedPaddingCount { alphabet := opts.alphabet, pad := opts.pad } bs.data.toList.length =
      expectedPaddingCount opts bs.size := by
    simp [expectedPaddingCount, hsz]
  rw [heqCount] at hsplit
  have hlenData : (encodeBytesList opts.alphabet false bs.data.toList).length =
      expectedEncodedLength { alphabet := opts.alphabet, pad := false } bs.size := by
    rw [← hsz]; exact hprops.1
  have hlenTot : (encodeBytesList opts.alphabet false bs.data.toList ++
      List.replicate (expectedPaddingCount opts bs.size) '=').length =
      expectedEncodedLength opts bs.size := by
    simp only [List.length_append, List.length_replicate, hlenData, expectedEncodedLength,
      expectedPaddingCount, Bool.false_eq_true, ↓reduceIte]
    cases opts.pad
    · simp
    · simp only [↓reduceIte]
      have hmod3 : bs.size % 3 = 0 ∨ bs.size % 3 = 1 ∨ bs.size % 3 = 2 := by omega
      rcases hmod3 with h0 | h1 | h2
      · have hk : bs.size = 3 * (bs.size / 3) := by omega
        have ha : (3 * (bs.size / 3) * 4 + 2) / 3 = 4 * (bs.size / 3) := by omega
        have hb : (3 * (bs.size / 3) + 2) / 3 * 4 = 4 * (bs.size / 3) := by omega
        rw [hk, ha, hb]; omega
      · have hk : bs.size = 3 * (bs.size / 3) + 1 := by omega
        have ha : ((3 * (bs.size / 3) + 1) * 4 + 2) / 3 = 4 * (bs.size / 3) + 2 := by omega
        have hb : (3 * (bs.size / 3) + 1 + 2) / 3 * 4 = 4 * (bs.size / 3) + 4 := by omega
        rw [hk, ha, hb]; omega
      · have hk : bs.size = 3 * (bs.size / 3) + 2 := by omega
        have ha : ((3 * (bs.size / 3) + 2) * 4 + 2) / 3 = 4 * (bs.size / 3) + 3 := by omega
        have hb : (3 * (bs.size / 3) + 2 + 2) / 3 * 4 = 4 * (bs.size / 3) + 4 := by omega
        rw [hk, ha, hb]; omega
  have hdiff : (encodeBytesList opts.alphabet false bs.data.toList ++
      List.replicate (expectedPaddingCount opts bs.size) '=').length -
      expectedPaddingCount opts bs.size =
      (encodeBytesList opts.alphabet false bs.data.toList).length := by
    simp [List.length_append, List.length_replicate]
  dsimp only
  rw [htoList, hsplit]
  refine ⟨hlenTot, ?_, ?_, ?_⟩
  · rw [hdiff, List.take_left]; exact hprops.2.1
  · rw [hdiff, List.drop_left]; simp
  · rw [hdiff, List.drop_left, List.length_replicate]

/-- `test_base64_encodeWith_outputInvariants` holds for `defaultApi`. -/
theorem allPass_encodeWith_outputInvariants :
    AllPass (test_base64_encodeWith_outputInvariants defaultApi) := by
  intro encOpts bs
  dsimp [test_base64_encodeWith_outputInvariants, defaultApi, Core.NondetTest.assert]
  have h := encodeWith_charset_and_length encOpts bs
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, trivial⟩

/-- Canonical uniqueness: when `strictCanonicalBits = true` and `padding ≠ .optional`, any accepted string equals the canonical encoding of its decoded bytes. -/
theorem decodeWith_encodeWith_canonical_unique
    (decOpts : DecodeOptions) (s : String) (bs : ByteArray)
    (hstrict : decOpts.strictCanonicalBits = true)
    (hfixed : decOpts.padding ≠ .optional)
    (hdec : decodeWith decOpts s = .ok bs) :
    s = encodeWith { alphabet := decOpts.alphabet, pad := (decOpts.padding == .required) } bs := by
  have hmod := decodeWith_matchesModel_aux decOpts s
  have hdm : decodeModel decOpts s = .ok bs := by rw [← hmod.1, hdec]; rfl
  unfold decodeModel at hdm
  cases hmc : decodeModelChars decOpts s.toList with
  | error e => simp [hmc, Except.map] at hdm
  | ok bsList =>
    simp only [hmc, Except.map, Except.ok.injEq] at hdm
    have huniq := decodeModelChars_canonical_unique decOpts s.toList bsList hstrict hfixed hmc
    have hbs : bs.data.toList = bsList := by
      rw [← hdm]
    rw [← hbs] at huniq
    have hs : s = String.ofList s.toList := by simp [String.ofList_toList]
    rw [hs, huniq]
    change String.ofList (Model.encodeBytesList decOpts.alphabet (decOpts.padding == .required) bs.data.toList) =
      String.ofList (Internal.encodeBytesList decOpts.alphabet (decOpts.padding == .required) bs.data.toList)
    rw [encodeBytesList_eq]

/-- `test_base64_decodeWith_injectiveFixedPadding` holds for `defaultApi`. -/
theorem allPass_decodeWith_injectiveFixedPadding :
    AllPass (test_base64_decodeWith_injectiveFixedPadding defaultApi) := by
  intro decOpts s1 s2 bs1 bs2 ⟨hstrict, hfixed⟩ h1 h2 heq
  dsimp [test_base64_decodeWith_injectiveFixedPadding, defaultApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, bind, pure]
  have hs1 := decodeWith_encodeWith_canonical_unique decOpts s1 bs1 hstrict hfixed h1
  have hs2 := decodeWith_encodeWith_canonical_unique decOpts s2 bs2 hstrict hfixed h2
  refine ⟨?_, trivial⟩
  rw [hs1, hs2, heq]

/-- `CanReach` witness for `test_base64_decodeWith_injectiveFixedPadding`. -/
theorem canReach_decodeWith_injectiveFixedPadding :
    CanReach (test_base64_decodeWith_injectiveFixedPadding defaultApi) := by
  dsimp [Core.CanReach, test_base64_decodeWith_injectiveFixedPadding, defaultApi,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, bind, pure]
  refine ⟨defaultDecodeOptions, "", "", ByteArray.empty, ByteArray.empty,
    ⟨rfl, by decide⟩, rfl, rfl, rfl, rfl, trivial⟩

/-- Structural characterization equivalence for `ValidEncodedChars` and `decodeModelChars`. -/
theorem validEncodedChars_iff_decodeModelChars (opts : DecodeOptions) (chars : List Char) :
    ValidEncodedChars opts chars ↔ (decodeModelChars opts chars).isOk = true := by
  unfold ValidEncodedChars decodeModelChars
  cases hscan : scanInvalidChar opts.alphabet 0 chars with
  | some idx =>
    simp [Except.isOk, Except.toBool]
  | none =>
    simp only [true_and]
    cases heq : findFirstEq 0 chars with
    | some p =>
      simp only []
      by_cases hforb : opts.padding = .forbidden
      · simp [hforb, Except.isOk, Except.toBool]
      · cases hall : (chars.drop p).all (· == '=')
        · simp [hforb, Except.isOk, Except.toBool]
        · by_cases hmod : chars.length % 4 = 0
          · by_cases hle : chars.length - p ≤ 2
            · have hnotgt : ¬(chars.length - p > 2) := by omega
              simp [hforb, hmod, hle, hnotgt]
            · have hgt : chars.length - p > 2 := by omega
              simp [hforb, hmod, hle, hgt, Except.isOk, Except.toBool]
          · simp [hforb, hmod, Except.isOk, Except.toBool]
    | none =>
      by_cases hmod1 : chars.length % 4 = 1
      · simp [hmod1, Except.isOk, Except.toBool]
      · have hmod1b : (chars.length % 4 == 1) = false := by simp [hmod1]
        by_cases hreq : opts.padding = .required
        · by_cases hmod0 : chars.length % 4 = 0
          · simp [hreq, hmod0]
          · simp [hmod1b, hreq, hmod0, Except.isOk, Except.toBool]
        · simp [hmod1b, hreq, hmod1]

/-- `ValidEncoded` holds iff `decodeModel` succeeds on some `ByteArray`. -/
theorem validEncoded_iff_decodeModel (opts : DecodeOptions) (s : String) :
    ValidEncoded opts s ↔ ∃ bs, decodeModel opts s = .ok bs :=
  validEncoded_iff_exists opts s

/-- `test_base64_concreteVectorsAndErrors` holds for `defaultApi`. -/
theorem allPass_concreteVectorsAndErrors :
    AllPass (test_base64_concreteVectorsAndErrors defaultApi) := by
  dsimp [Core.AllPass, test_base64_concreteVectorsAndErrors, defaultApi,
    List.forM, bind, pure, Core.NondetTest.assert]
  repeat'
    first
    | exact True.intro
    | apply And.intro
    | exact makeError_msg_ne_empty _ _ _
    | rfl

end LeanSwe.Base64.Proofs
