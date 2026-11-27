import LeanSweProofs.CryptoHash.Model
import LeanSwe.CryptoHash.Interface
import LeanSweProofs.CryptoHash.SpecTests

namespace LeanSwe.CryptoHash.Proofs

open LeanSwe.CryptoHash

/-- Lowercase ASCII hexadecimal character check. -/
def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Case-insensitive ASCII hexadecimal character check. -/
def isHexChar (c : Char) : Bool :=
  isLowerHexChar c || ('A' ≤ c && c ≤ 'F')

/-- Reference nibble-to-lowercase-hex-character mapping. -/
def lowerHexDigitSpec (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def foldMockBytes (init : UInt64) (bs : List UInt8) : UInt64 :=
  bs.foldl (fun h b => h * 1315423911 + b.toUInt64 + 1) init

private def expandMockBytes : Nat → UInt64 → Array UInt8 → Array UInt8
  | 0, _, acc => acc
  | n + 1, h, acc =>
    let h' := h * 6364136223846793005 + 1442695040888963407
    expandMockBytes n h' (acc.push (UInt8.ofNat ((h'.toNat / 256 + n) % 256)))

/-- Deterministic mock digest byte generator matching `SpecTests`. -/
def mockDigestBytes (alg : HashAlg) (msg : ByteArray) : ByteArray :=
  let algTag : UInt64 := match alg with | .sha256 => 0x53484132 | .sha512 => 0x53484135
  let seed := foldMockBytes (algTag + msg.size.toUInt64 * 2654435761) msg.data.toList
  ByteArray.mk (expandMockBytes (digestLen alg) seed #[])

/-- Deterministic mock HMAC-SHA256 byte generator matching `SpecTests`. -/
def mockHmacBytes (key msg : ByteArray) : ByteArray :=
  let keySeed := foldMockBytes (0x484d4143 + key.size.toUInt64 * 2654435761) key.data.toList
  let msgSeed := foldMockBytes (keySeed ^^^ 0x5c5c5c5c5c5c5c5c + msg.size.toUInt64 * 11400714819323198485) msg.data.toList
  ByteArray.mk (expandMockBytes 32 msgSeed #[])

private theorem expandMockBytes_size (n : Nat) (h : UInt64) (acc : Array UInt8) :
    (expandMockBytes n h acc).size = acc.size + n := by
  induction n generalizing h acc with
  | zero => simp [expandMockBytes]
  | succ k ih =>
    simp [expandMockBytes, ih, Array.size_push]
    omega

private theorem expandMockBytes_getElem?_of_lt (n : Nat) (h : UInt64) (acc : Array UInt8)
    (i : Nat) (hi : i < acc.size) :
    (expandMockBytes n h acc)[i]? = acc[i]? := by
  induction n generalizing h acc with
  | zero => rfl
  | succ k ih =>
    unfold expandMockBytes
    let h' := h * 6364136223846793005 + 1442695040888963407
    let b := UInt8.ofNat ((h'.toNat / 256 + k) % 256)
    have hi' : i < (acc.push b).size := by simp [Array.size_push]; omega
    rw [ih h' (acc.push b) hi', Array.getElem?_push]
    simp [Nat.ne_of_lt hi]

/-- Size of `mockDigestBytes alg msg` equals `digestLen alg`. -/
theorem mockDigestBytes_size (alg : HashAlg) (msg : ByteArray) :
    (mockDigestBytes alg msg).size = digestLen alg := by
  unfold mockDigestBytes
  dsimp only
  rw [ByteArray.size]
  simpa using expandMockBytes_size (digestLen alg) _ #[]

/-- Size of `mockHmacBytes key msg` equals `32`. -/
theorem mockHmacBytes_size (key msg : ByteArray) :
    (mockHmacBytes key msg).size = 32 := by
  unfold mockHmacBytes
  dsimp only
  rw [ByteArray.size]
  simpa using expandMockBytes_size 32 _ #[]

private theorem uint8_of_nibbles (b : UInt8) :
    UInt8.ofNat ((b.toNat / 16) * 16 + b.toNat % 16) = b := by
  have hmod : (b.toNat / 16) * 16 + b.toNat % 16 = b.toNat := by omega
  rw [hmod, UInt8.ofNat_toNat]

/-- High and low nibbles of any `UInt8` are `< 16`. -/
theorem uint8_nibble_bounds (b : UInt8) :
    b.toNat / 16 < 16 ∧ b.toNat % 16 < 16 := by
  have h := b.toNat_lt
  omega

private theorem fin16_hex_roundtrip :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      Internal.hexCharsToByte
        (Internal.lowerHexDigit (b.toNat / 16))
        (Internal.lowerHexDigit (b.toNat % 16)) = some b := by
  decide

private theorem uint8_hex_roundtrip (b : UInt8) :
    Internal.hexCharsToByte
      (Internal.lowerHexDigit (b.toNat / 16))
      (Internal.lowerHexDigit (b.toNat % 16)) = some b := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_hex_roundtrip ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

private theorem fin16_hex_upper_roundtrip :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      Internal.hexCharsToByte
        (Char.toUpper (Internal.lowerHexDigit (b.toNat / 16)))
        (Char.toUpper (Internal.lowerHexDigit (b.toNat % 16))) = some b := by
  decide

private theorem uint8_hex_upper_roundtrip (b : UInt8) :
    Internal.hexCharsToByte
      (Char.toUpper (Internal.lowerHexDigit (b.toNat / 16)))
      (Char.toUpper (Internal.lowerHexDigit (b.toNat % 16))) = some b := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_hex_upper_roundtrip ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

private theorem fin16_isLowerHexChar :
    ∀ i : Fin 16, isLowerHexChar (Internal.lowerHexDigit i.1) = true := by
  decide

/-- `lowerHexDigitSpec` agrees with `Internal.lowerHexDigit` on `Fin 16`. -/
theorem fin16_lowerHexDigit_eq :
    ∀ i : Fin 16, lowerHexDigitSpec i.1 = Internal.lowerHexDigit i.1 := by
  decide

/-- Length of `Internal.formatHexList bs` is `2 * bs.length`. -/
theorem formatHexList_length (bs : List UInt8) :
    (Internal.formatHexList bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
      List.cons_append, List.nil_append, List.length_cons] at ih ⊢
    rw [ih]
    omega

/-- Every character in `Internal.formatHexList bs` satisfies `isLowerHexChar`. -/
theorem formatHexList_all_lowerHex (bs : List UInt8) :
    (Internal.formatHexList bs).all isLowerHexChar = true := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
    have h1 := fin16_isLowerHexChar ⟨b.toNat / 16, hd⟩
    have h2 := fin16_isLowerHexChar ⟨b.toNat % 16, hr⟩
    simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
      List.cons_append, List.nil_append, List.all_cons] at ih ⊢
    simp [h1, h2, ih]

/-- Structural pair-by-pair hexadecimal list decoder. -/
def decodeHexPairs : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest =>
    match Internal.hexCharsToByte hi lo, decodeHexPairs rest with
    | some b, some bs => some (b :: bs)
    | _, _ => none
  | _ => none

/-- `decodeHexPairs` left-inverts `Internal.formatHexList`. -/
theorem decodeHexPairs_formatHexList (bs : List UInt8) :
    decodeHexPairs (Internal.formatHexList bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
      List.cons_append, List.nil_append, decodeHexPairs] at ih ⊢
    rw [uint8_hex_roundtrip b, ih]

/-- `decodeHexPairs` left-inverts uppercase `Internal.formatHexList`. -/
theorem decodeHexPairs_upper_formatHexList (bs : List UInt8) :
    decodeHexPairs ((Internal.formatHexList bs).map Char.toUpper) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
      List.cons_append, List.nil_append, List.map_cons, decodeHexPairs] at ih ⊢
    rw [uint8_hex_upper_roundtrip b, ih]

/-- Indexing high and low nibble hex characters in `Internal.formatHexList`. -/
theorem formatHexList_getElem? (bs : List UInt8) (i : Nat) (hi : i < bs.length) :
    (Internal.formatHexList bs)[2 * i]? = some (Internal.lowerHexDigit (bs[i].toNat / 16)) ∧
    (Internal.formatHexList bs)[2 * i + 1]? = some (Internal.lowerHexDigit (bs[i].toNat % 16)) := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b rest ih =>
    cases i with
    | zero =>
      simp [Internal.formatHexList, Internal.byteToHexChars]
    | succ k =>
      have hk : k < rest.length := by simpa using hi
      have ihk := ih k hk
      simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
        List.cons_append, List.nil_append]
      have hidx1 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [hidx1]
      simp only [List.getElem?_cons_succ]
      simpa [Internal.formatHexList] using ihk

private theorem hexCharToNibble_lt_128 {c : Char} {n : UInt8}
    (h : Internal.hexCharToNibble c = some n) : c.toNat < 128 := by
  unfold Internal.hexCharToNibble at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hle : c.toNat ≤ '9'.toNat := UInt32.le_iff_toNat_le.mp hc.2
    simp at hle
    omega
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hle : c.toNat ≤ 'f'.toNat := UInt32.le_iff_toNat_le.mp hc.2
      simp at hle
      omega
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hle : c.toNat ≤ 'F'.toNat := UInt32.le_iff_toNat_le.mp hc.2
        simp at hle
        omega
      · cases h

private def checkHexNibble (c : Fin 128) : Bool :=
  match Internal.hexCharToNibble (Char.ofNat c.1) with
  | none => true
  | some n => n.toNat < 16 && Internal.lowerHexDigit n.toNat == Char.toLower (Char.ofNat c.1)

private theorem fin128_hex_nibble : ∀ c : Fin 128, checkHexNibble c = true := by
  decide

private theorem hexCharToNibble_bounds_and_lower {c : Char} {n : UInt8}
    (h : Internal.hexCharToNibble c = some n) :
    n.toNat < 16 ∧ Internal.lowerHexDigit n.toNat = Char.toLower c := by
  have hc := hexCharToNibble_lt_128 h
  have hm := fin128_hex_nibble ⟨c.toNat, hc⟩
  unfold checkHexNibble at hm
  have h' : Internal.hexCharToNibble (Char.ofNat c.toNat) = some n := by
    simpa [Char.ofNat_toNat] using h
  rw [h'] at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
  simpa [Char.ofNat_toNat] using hm

private theorem hexCharsToByte_toLower {hi lo : Char} {b : UInt8}
    (h : Internal.hexCharsToByte hi lo = some b) :
    Internal.byteToHexChars b = [Char.toLower hi, Char.toLower lo] := by
  unfold Internal.hexCharsToByte at h
  cases h1 : Internal.hexCharToNibble hi with
  | none => simp [h1] at h
  | some hn =>
    cases h2 : Internal.hexCharToNibble lo with
    | none => simp [h1, h2] at h
    | some ln =>
      simp [h1, h2] at h
      subst h
      obtain ⟨hh_lt, hh_low⟩ := hexCharToNibble_bounds_and_lower h1
      obtain ⟨hl_lt, hl_low⟩ := hexCharToNibble_bounds_and_lower h2
      have hsum_lt : hn.toNat * 16 + ln.toNat < 256 := by omega
      have hdiv : (hn.toNat * 16 + ln.toNat) % 256 / 16 = hn.toNat := by omega
      have hmod : ln.toNat % 16 = ln.toNat := Nat.mod_eq_of_lt hl_lt
      simp [Internal.byteToHexChars, hdiv, hmod, hh_low, hl_low]

/-- Successful `decodeHexPairs` re-formats to `cs.map Char.toLower`. -/
theorem decodeHexPairs_some_format {cs : List Char} {bs : List UInt8}
    (h : decodeHexPairs cs = some bs) :
    Internal.formatHexList bs = cs.map Char.toLower := by
  match cs, bs with
  | [], [] => rfl
  | [], _ :: _ => simp [decodeHexPairs] at h
  | [_], _ => simp [decodeHexPairs] at h
  | hi :: lo :: rest, bs =>
    simp only [decodeHexPairs] at h
    cases hb : Internal.hexCharsToByte hi lo with
    | none => simp [hb] at h
    | some b =>
      cases hrest : decodeHexPairs rest with
      | none => simp [hb, hrest] at h
      | some restBs =>
        simp [hb, hrest] at h
        subst h
        have ih := decodeHexPairs_some_format hrest
        simp only [Internal.formatHexList, List.flatMap_cons, hexCharsToByte_toLower hb,
          List.cons_append, List.nil_append, List.map_cons]
        exact congrArg (fun tl => Char.toLower hi :: Char.toLower lo :: tl) ih

private theorem hexCharToNibble_none_of_not_isHexChar {c : Char}
    (h : isHexChar c = false) : Internal.hexCharToNibble c = none := by
  unfold Internal.hexCharToNibble
  unfold isHexChar isLowerHexChar at h
  cases h09 : ('0' ≤ c && c ≤ '9') <;> cases haf : ('a' ≤ c && c ≤ 'f') <;>
    cases hAF : ('A' ≤ c && c ≤ 'F') <;> simp_all

/-- Non-hex character at `idx` forces `decodeHexPairs cs = none`. -/
theorem decodeHexPairs_none_of_nonHex {cs : List Char} {idx : Nat}
    (hidx : idx < cs.length) (hbad : isHexChar cs[idx] = false) :
    decodeHexPairs cs = none := by
  match cs, idx with
  | [], _ => simp at hidx
  | [_], 0 => rfl
  | [_], _ + 1 => simp at hidx
  | hi :: lo :: rest, 0 =>
    have hnone : Internal.hexCharToNibble hi = none :=
      hexCharToNibble_none_of_not_isHexChar (by simpa using hbad)
    simp [decodeHexPairs, Internal.hexCharsToByte, hnone]
  | hi :: lo :: rest, 1 =>
    have hnone : Internal.hexCharToNibble lo = none :=
      hexCharToNibble_none_of_not_isHexChar (by simpa using hbad)
    simp [decodeHexPairs, Internal.hexCharsToByte, hnone]
  | hi :: lo :: rest, k + 2 =>
    have hk : k < rest.length := by simpa using hidx
    have hbad' : isHexChar rest[k] = false := by simpa using hbad
    have ih := decodeHexPairs_none_of_nonHex hk hbad'
    simp [decodeHexPairs, ih]

private theorem decodeHexPairs_length_even {cs : List Char} {bs : List UInt8}
    (h : decodeHexPairs cs = some bs) : cs.length = 2 * bs.length := by
  match cs, bs with
  | [], [] => rfl
  | [], _ :: _ => simp [decodeHexPairs] at h
  | [_], _ => simp [decodeHexPairs] at h
  | hi :: lo :: rest, bs =>
    simp only [decodeHexPairs] at h
    cases hb : Internal.hexCharsToByte hi lo with
    | none => simp [hb] at h
    | some b =>
      cases hrest : decodeHexPairs rest with
      | none => simp [hb, hrest] at h
      | some restBs =>
        simp [hb, hrest] at h
        subst h
        have ih := decodeHexPairs_length_even hrest
        simp only [List.length_cons] at ih ⊢
        omega

/-- Odd character length forces `decodeHexPairs cs = none`. -/
theorem decodeHexPairs_none_of_odd {cs : List Char}
    (hodd : cs.length % 2 = 1) : decodeHexPairs cs = none := by
  cases h : decodeHexPairs cs with
  | none => rfl
  | some bs =>
    have heven := decodeHexPairs_length_even h
    omega

private theorem decodeHexPairs_length_div2 {cs : List Char} {bs : List UInt8}
    (h : decodeHexPairs cs = some bs) : bs.length * 2 = cs.length := by
  have hev := decodeHexPairs_length_even h
  omega

private theorem hexCharToNibble_isSome_of_isHexChar {c : Char}
    (h : isHexChar c = true) : ∃ n, Internal.hexCharToNibble c = some n := by
  unfold Internal.hexCharToNibble
  unfold isHexChar isLowerHexChar at h
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · simp_all

private theorem hexCharsToByte_isSome_of_isHexChar {hi lo : Char}
    (hhi : isHexChar hi = true) (hlo : isHexChar lo = true) :
    ∃ b, Internal.hexCharsToByte hi lo = some b := by
  obtain ⟨nh, hh⟩ := hexCharToNibble_isSome_of_isHexChar hhi
  obtain ⟨nl, hl⟩ := hexCharToNibble_isSome_of_isHexChar hlo
  refine ⟨UInt8.ofNat (nh.toNat * 16 + nl.toNat), ?_⟩
  unfold Internal.hexCharsToByte
  rw [hh, hl]

/-- Even-length all-hex list decodes via `decodeHexPairs`. -/
theorem decodeHexPairs_some_of_all_hex {cs : List Char}
    (heven : cs.length % 2 = 0) (hall : cs.all isHexChar = true) :
    ∃ bs, decodeHexPairs cs = some bs ∧ 2 * bs.length = cs.length := by
  match cs with
  | [] => exact ⟨[], rfl, rfl⟩
  | [_] => simp at heven
  | hi :: lo :: rest =>
    simp only [List.all_cons] at hall
    have h1 := (Bool.and_eq_true _ _).mp hall
    have h2 := (Bool.and_eq_true _ _).mp h1.2
    obtain ⟨b, hb⟩ := hexCharsToByte_isSome_of_isHexChar h1.1 h2.1
    have heven' : rest.length % 2 = 0 := by
      simp only [List.length_cons] at heven
      omega
    obtain ⟨bs, hbs, hlen⟩ := decodeHexPairs_some_of_all_hex heven' h2.2
    refine ⟨b :: bs, ?_, ?_⟩
    · simp [decodeHexPairs, hb, hbs]
    · simp only [List.length_cons] at hlen ⊢
      omega

/-- Symmetry of `ByteArray` boolean equality. -/
theorem byteArray_beq_symm (a b : ByteArray) : (a == b) = (b == a) := by
  cases h1 : a == b
  · cases h2 : b == a
    · rfl
    · have heq : b = a := eq_of_beq h2
      subst heq
      rw [beq_self_eq_true] at h1
      cases h1
  · have heq : a = b := eq_of_beq h1
    subst heq
    rw [beq_self_eq_true]

private theorem uint8_xor_one_ne (x : UInt8) : (x ^^^ 1 == x) = false := by
  cases heq : x ^^^ 1 == x with
  | false => rfl
  | true =>
    have h := congrArg (fun b : UInt8 => Nat.testBit b.toNat 0) (eq_of_beq heq)
    simp [UInt8.toNat_xor] at h
    omega

/-- Flipping bit 0 of byte 0 in a 32-byte `ByteArray` yields an unequal slice. -/
theorem byteArray_tamper_byte0_ne (ba : ByteArray) (h : ba.size = 32) :
    (ba == ba.set! 0 (ba[0]! ^^^ 1)) = false := by
  cases heq : ba == ba.set! 0 (ba[0]! ^^^ 1) with
  | false => rfl
  | true =>
    have hba : ba = ba.set! 0 (ba[0]! ^^^ 1) := eq_of_beq heq
    have h0 := congrArg (fun x : ByteArray => x[0]!) hba
    have hlt : 0 < ba.size := by omega
    have hset : (ba.set! 0 (ba[0]! ^^^ 1))[0]! = ba[0]! ^^^ 1 := by
      rw [ByteArray.getElem!_set! ba 0 (ba[0]! ^^^ 1) 0 hlt]
      simp
    rw [hset] at h0
    have hne := uint8_xor_one_ne (ba[0]!)
    rw [← h0, beq_self_eq_true] at hne
    cases hne

private theorem expandMockBytes_32_zero (msgSeed : UInt64) :
    (ByteArray.mk (expandMockBytes 32 msgSeed #[]))[0]? =
      let h1 := msgSeed * 6364136223846793005 + 1442695040888963407
      some (UInt8.ofNat ((h1.toNat / 256 + 31) % 256)) := by
  have hmk : (ByteArray.mk (expandMockBytes 32 msgSeed #[]))[0]? = (expandMockBytes 32 msgSeed #[])[0]? := rfl
  rw [hmk, show (32 : Nat) = 31 + 1 from rfl, expandMockBytes]
  exact expandMockBytes_getElem?_of_lt 31 _ _ 0 (by simp)

private theorem mockHmacBytes_byte0 (key msg : ByteArray) :
    (mockHmacBytes key msg)[0]? =
      let keySeed := foldMockBytes (0x484d4143 + key.size.toUInt64 * 2654435761) key.data.toList
      let msgSeed := foldMockBytes (keySeed ^^^ 0x5c5c5c5c5c5c5c5c + msg.size.toUInt64 * 11400714819323198485) msg.data.toList
      let h1 := msgSeed * 6364136223846793005 + 1442695040888963407
      some (UInt8.ofNat ((h1.toNat / 256 + 31) % 256)) := by
  unfold mockHmacBytes
  exact expandMockBytes_32_zero _

/-- Distinct keys `"k2"` and `"k1"` produce unequal mock HMAC tags on `"m1"`. -/
theorem mockHmacBytes_k2_m1_ne :
    (mockHmacBytes "k2".toUTF8 "m1".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8) = false := by
  cases heq : mockHmacBytes "k2".toUTF8 "m1".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8 with
  | false => rfl
  | true =>
    have h := congrArg (fun ba : ByteArray => ba[0]?) (eq_of_beq heq)
    rw [mockHmacBytes_byte0, mockHmacBytes_byte0] at h
    exact absurd h (by decide)

/-- Distinct messages `"m2"` and `"m1"` produce unequal mock HMAC tags under `"k1"`. -/
theorem mockHmacBytes_k1_m2_ne :
    (mockHmacBytes "k1".toUTF8 "m2".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8) = false := by
  cases heq : mockHmacBytes "k1".toUTF8 "m2".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8 with
  | false => rfl
  | true =>
    have h := congrArg (fun ba : ByteArray => ba[0]?) (eq_of_beq heq)
    rw [mockHmacBytes_byte0, mockHmacBytes_byte0] at h
    exact absurd h (by decide)

/-- Round-trip `bs.toArray.toList = bs`. -/
theorem toList_toArray_eq (bs : List UInt8) : bs.toArray.toList = bs := by
  simp

/-- In-bounds `xs[i]!` equals `xs[i]`. -/
theorem list_getElem!_eq (xs : List Char) (i : Nat) (hi : i < xs.length) :
    xs[i]! = xs[i] := by
  simp [hi]


end LeanSwe.CryptoHash.Proofs
