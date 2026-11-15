import LeanSwe.CryptoHash.Interface
import LeanSwe.CryptoHash.SpecTests
import LeanSwe.CryptoHash.Raw.Proofs

namespace LeanSwe.CryptoHash.Proofs

open Core
open Core.NondetTest
open LeanSwe.CryptoHash

private def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def isHexChar (c : Char) : Bool :=
  isLowerHexChar c || ('A' ≤ c && c ≤ 'F')

private def lowerHexDigitSpec (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def foldMockBytes (init : UInt64) (bs : List UInt8) : UInt64 :=
  bs.foldl (fun h b => h * 1315423911 + b.toUInt64 + 1) init

private def expandMockBytes : Nat → UInt64 → Array UInt8 → Array UInt8
  | 0, _, acc => acc
  | n + 1, h, acc =>
    let h' := h * 6364136223846793005 + 1442695040888963407
    expandMockBytes n h' (acc.push (UInt8.ofNat ((h'.toNat / 256 + n) % 256)))

private def mockDigestBytes (alg : HashAlg) (msg : ByteArray) : ByteArray :=
  let algTag : UInt64 := match alg with | .sha256 => 0x53484132 | .sha512 => 0x53484135
  let seed := foldMockBytes (algTag + msg.size.toUInt64 * 2654435761) msg.data.toList
  ByteArray.mk (expandMockBytes (digestLen alg) seed #[])

private def mockHmacBytes (key msg : ByteArray) : ByteArray :=
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

private theorem mockDigestBytes_size (alg : HashAlg) (msg : ByteArray) :
    (mockDigestBytes alg msg).size = digestLen alg := by
  unfold mockDigestBytes
  dsimp only
  rw [ByteArray.size]
  simpa using expandMockBytes_size (digestLen alg) _ #[]

private theorem mockHmacBytes_size (key msg : ByteArray) :
    (mockHmacBytes key msg).size = 32 := by
  unfold mockHmacBytes
  dsimp only
  rw [ByteArray.size]
  simpa using expandMockBytes_size 32 _ #[]

private theorem uint8_of_nibbles (b : UInt8) :
    UInt8.ofNat ((b.toNat / 16) * 16 + b.toNat % 16) = b := by
  have hmod : (b.toNat / 16) * 16 + b.toNat % 16 = b.toNat := by omega
  rw [hmod, UInt8.ofNat_toNat]

private theorem uint8_nibble_bounds (b : UInt8) :
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

private theorem fin16_lowerHexDigit_eq :
    ∀ i : Fin 16, lowerHexDigitSpec i.1 = Internal.lowerHexDigit i.1 := by
  decide

private theorem formatHexList_length (bs : List UInt8) :
    (Internal.formatHexList bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
      List.cons_append, List.nil_append, List.length_cons] at ih ⊢
    rw [ih]
    omega

private theorem formatHexList_all_lowerHex (bs : List UInt8) :
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

private theorem decodeHexPairs_formatHexList (bs : List UInt8) :
    Internal.decodeHexPairs (Internal.formatHexList bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
      List.cons_append, List.nil_append, Internal.decodeHexPairs] at ih ⊢
    rw [uint8_hex_roundtrip b, ih]

private theorem decodeHexPairs_upper_formatHexList (bs : List UInt8) :
    Internal.decodeHexPairs ((Internal.formatHexList bs).map Char.toUpper) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [Internal.formatHexList, List.flatMap_cons, Internal.byteToHexChars,
      List.cons_append, List.nil_append, List.map_cons, Internal.decodeHexPairs] at ih ⊢
    rw [uint8_hex_upper_roundtrip b, ih]

private theorem formatHexList_getElem? (bs : List UInt8) (i : Nat) (hi : i < bs.length) :
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

private theorem decodeHexPairs_some_format {cs : List Char} {bs : List UInt8}
    (h : Internal.decodeHexPairs cs = some bs) :
    Internal.formatHexList bs = cs.map Char.toLower := by
  match cs, bs with
  | [], [] => rfl
  | [], _ :: _ => simp [Internal.decodeHexPairs] at h
  | [_], _ => simp [Internal.decodeHexPairs] at h
  | hi :: lo :: rest, bs =>
    simp only [Internal.decodeHexPairs] at h
    cases hb : Internal.hexCharsToByte hi lo with
    | none => simp [hb] at h
    | some b =>
      cases hrest : Internal.decodeHexPairs rest with
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

private theorem decodeHexPairs_none_of_nonHex {cs : List Char} {idx : Nat}
    (hidx : idx < cs.length) (hbad : isHexChar cs[idx] = false) :
    Internal.decodeHexPairs cs = none := by
  match cs, idx with
  | [], _ => simp at hidx
  | [_], 0 => rfl
  | [_], _ + 1 => simp at hidx
  | hi :: lo :: rest, 0 =>
    have hnone : Internal.hexCharToNibble hi = none :=
      hexCharToNibble_none_of_not_isHexChar (by simpa using hbad)
    simp [Internal.decodeHexPairs, Internal.hexCharsToByte, hnone]
  | hi :: lo :: rest, 1 =>
    have hnone : Internal.hexCharToNibble lo = none :=
      hexCharToNibble_none_of_not_isHexChar (by simpa using hbad)
    simp [Internal.decodeHexPairs, Internal.hexCharsToByte, hnone]
  | hi :: lo :: rest, k + 2 =>
    have hk : k < rest.length := by simpa using hidx
    have hbad' : isHexChar rest[k] = false := by simpa using hbad
    have ih := decodeHexPairs_none_of_nonHex hk hbad'
    simp [Internal.decodeHexPairs, ih]

private theorem decodeHexPairs_length_even {cs : List Char} {bs : List UInt8}
    (h : Internal.decodeHexPairs cs = some bs) : cs.length = 2 * bs.length := by
  match cs, bs with
  | [], [] => rfl
  | [], _ :: _ => simp [Internal.decodeHexPairs] at h
  | [_], _ => simp [Internal.decodeHexPairs] at h
  | hi :: lo :: rest, bs =>
    simp only [Internal.decodeHexPairs] at h
    cases hb : Internal.hexCharsToByte hi lo with
    | none => simp [hb] at h
    | some b =>
      cases hrest : Internal.decodeHexPairs rest with
      | none => simp [hb, hrest] at h
      | some restBs =>
        simp [hb, hrest] at h
        subst h
        have ih := decodeHexPairs_length_even hrest
        simp only [List.length_cons] at ih ⊢
        omega

private theorem decodeHexPairs_none_of_odd {cs : List Char}
    (hodd : cs.length % 2 = 1) : Internal.decodeHexPairs cs = none := by
  cases h : Internal.decodeHexPairs cs with
  | none => rfl
  | some bs =>
    have heven := decodeHexPairs_length_even h
    omega

private theorem decodeHexPairs_length_div2 {cs : List Char} {bs : List UInt8}
    (h : Internal.decodeHexPairs cs = some bs) : bs.length * 2 = cs.length := by
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

private theorem decodeHexPairs_some_of_all_hex {cs : List Char}
    (heven : cs.length % 2 = 0) (hall : cs.all isHexChar = true) :
    ∃ bs, Internal.decodeHexPairs cs = some bs ∧ 2 * bs.length = cs.length := by
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
    · simp [Internal.decodeHexPairs, hb, hbs]
    · simp only [List.length_cons] at hlen ⊢
      omega

private theorem byteArray_beq_symm (a b : ByteArray) : (a == b) = (b == a) := by
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

private theorem byteArray_tamper_byte0_ne (ba : ByteArray) (h : ba.size = 32) :
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

private theorem mockHmacBytes_k2_m1_ne :
    (mockHmacBytes "k2".toUTF8 "m1".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8) = false := by
  cases heq : mockHmacBytes "k2".toUTF8 "m1".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8 with
  | false => rfl
  | true =>
    have h := congrArg (fun ba : ByteArray => ba[0]?) (eq_of_beq heq)
    rw [mockHmacBytes_byte0, mockHmacBytes_byte0] at h
    exact absurd h (by decide)

private theorem mockHmacBytes_k1_m2_ne :
    (mockHmacBytes "k1".toUTF8 "m2".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8) = false := by
  cases heq : mockHmacBytes "k1".toUTF8 "m2".toUTF8 == mockHmacBytes "k1".toUTF8 "m1".toUTF8 with
  | false => rfl
  | true =>
    have h := congrArg (fun ba : ByteArray => ba[0]?) (eq_of_beq heq)
    rw [mockHmacBytes_byte0, mockHmacBytes_byte0] at h
    exact absurd h (by decide)

private theorem toList_toArray_eq (bs : List UInt8) : bs.toArray.toList = bs := by
  simp

private theorem list_getElem!_eq (xs : List Char) (i : Nat) (hi : i < xs.length) :
    xs[i]! = xs[i] := by
  simp [hi]

private theorem hashM_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (alg : HashAlg) (msg bs : ByteArray)
    (hraw : raw.digestRaw alg msg s = (.ok bs, s'))
    (hlen : bs.size = digestLen alg) :
    (Internal.hashM raw alg msg).run s =
      (.ok { alg := alg, bytes := bs }, s') := by
  have hs : (bs.size != digestLen alg) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.hashM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem hashM_raw_err (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (alg : HashAlg) (msg : ByteArray) (err : CryptoHashError)
    (hraw : raw.digestRaw alg msg s = (.error err, s')) :
    (Internal.hashM raw alg msg).run s = (.error err, s') := by
  dsimp [Internal.hashM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  rfl

private theorem hashM_raw_corrupt (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (alg : HashAlg) (msg : ByteArray) (badLen : Nat)
    (hraw : raw.digestRaw alg msg s = (.ok (ByteArray.mk (Array.replicate badLen 0)), s'))
    (hbad : badLen ≠ digestLen alg) :
    (Internal.hashM raw alg msg).run s =
      (.error { kind := .lengthMismatch, message := s!"digest length mismatch: expected {digestLen alg} bytes, got {badLen}" },
        s') := by
  dsimp [Internal.hashM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  have hsz : (ByteArray.mk (Array.replicate badLen 0)).size = badLen := by
    change (Array.replicate badLen (0 : UInt8)).size = badLen
    simp
  have hne : (badLen != digestLen alg) = true := bne_iff_ne.mpr hbad
  simp only [hsz, hne, ↓reduceIte]
  rfl

private theorem hmacSha256M_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (key msg bs : ByteArray)
    (hraw : raw.hmacSha256Raw key msg s = (.ok bs, s'))
    (hlen : bs.size = 32) :
    (Internal.hmacSha256M raw key msg).run s =
      (.ok { alg := .sha256, bytes := bs }, s') := by
  have hs : (bs.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.hmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem hmacSha256M_raw_err (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (key msg : ByteArray) (err : CryptoHashError)
    (hraw : raw.hmacSha256Raw key msg s = (.error err, s')) :
    (Internal.hmacSha256M raw key msg).run s = (.error err, s') := by
  dsimp [Internal.hmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  rfl

private theorem hmacSha256M_raw_corrupt (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (key msg : ByteArray) (badLen : Nat)
    (hraw : raw.hmacSha256Raw key msg s = (.ok (ByteArray.mk (Array.replicate badLen 0)), s'))
    (hbad : badLen ≠ 32) :
    (Internal.hmacSha256M raw key msg).run s =
      (.error { kind := .lengthMismatch, message := s!"HMAC-SHA256 length mismatch: expected 32 bytes, got {badLen}" },
        s') := by
  dsimp [Internal.hmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  rw [hraw]
  have hsz : (ByteArray.mk (Array.replicate badLen 0)).size = badLen := by
    change (Array.replicate badLen (0 : UInt8)).size = badLen
    simp
  have hne : (badLen != 32) = true := bne_iff_ne.mpr hbad
  simp only [hsz, hne, ↓reduceIte]
  rfl

private theorem ctEqM_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (a b : ByteArray)
    (heq : a.size = b.size)
    (hraw : raw.ctEqualRaw a b s = (.ok (a == b), s')) :
    (Internal.ctEqM raw a b).run s = (.ok (a == b), s') := by
  have hne : (a.size != b.size) = false := bne_eq_false_iff_eq.mpr heq
  dsimp [Internal.ctEqM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  exact hraw

private theorem ctEqM_raw_err (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (a b : ByteArray) (err : CryptoHashError)
    (heq : a.size = b.size)
    (hraw : raw.ctEqualRaw a b s = (.error err, s')) :
    (Internal.ctEqM raw a b).run s = (.error err, s') := by
  have hne : (a.size != b.size) = false := bne_eq_false_iff_eq.mpr heq
  dsimp [Internal.ctEqM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  exact hraw

private theorem verifyHmacSha256M_raw_hmacErr (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s s' : MockCryptoHashState) (err : CryptoHashError)
    (key msg : ByteArray) (expected : Digest)
    (halg : expected.alg = .sha256) (hlen : expected.bytes.size = 32)
    (hraw : raw.hmacSha256Raw key msg s = (.error err, s')) :
    (Internal.verifyHmacSha256M raw key msg expected).run s = (.error err, s') := by
  have hf_alg : (expected.alg != .sha256) = false := by rw [halg]; decide
  have hl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hf_alg, hl, Bool.false_eq_true, ↓reduceIte]
  unfold StateT.bind
  rw [show Internal.hmacSha256M raw key msg s = (Internal.hmacSha256M raw key msg).run s from rfl,
    hmacSha256M_raw_err raw s s' key msg err hraw]
  rfl

private theorem verifyHmacSha256M_raw_ctEqErr (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s sH sC : MockCryptoHashState) (err : CryptoHashError)
    (key msg bs : ByteArray) (expected : Digest)
    (halg : expected.alg = .sha256) (hlen : expected.bytes.size = 32)
    (hbs : bs.size = 32)
    (hrawH : raw.hmacSha256Raw key msg s = (.ok bs, sH))
    (hrawC : raw.ctEqualRaw bs expected.bytes sH = (.error err, sC)) :
    (Internal.verifyHmacSha256M raw key msg expected).run s = (.error err, sC) := by
  have hf_alg : (expected.alg != .sha256) = false := by rw [halg]; decide
  have hl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hf_alg, hl, Bool.false_eq_true, ↓reduceIte]
  unfold StateT.bind
  rw [show Internal.hmacSha256M raw key msg s = (Internal.hmacSha256M raw key msg).run s from rfl,
    hmacSha256M_raw_ok raw s sH key msg bs hrawH hbs]
  dsimp only [Bind.bind, Monad.toBind, Id.instMonad]
  have hsz : bs.size = expected.bytes.size := by rw [hbs, hlen]
  exact ctEqM_raw_err raw sH sC bs expected.bytes err hsz hrawC

private theorem verifyHmacSha256M_raw_ok (raw : RawCryptoHashOpsM (StateT MockCryptoHashState Id))
    (s sH sC : MockCryptoHashState)
    (key msg bs : ByteArray) (expected : Digest)
    (halg : expected.alg = .sha256) (hlen : expected.bytes.size = 32)
    (hbs : bs.size = 32)
    (hrawH : raw.hmacSha256Raw key msg s = (.ok bs, sH))
    (hrawC : raw.ctEqualRaw bs expected.bytes sH = (.ok (bs == expected.bytes), sC)) :
    (Internal.verifyHmacSha256M raw key msg expected).run s =
      (.ok (bs == expected.bytes), sC) := by
  have hf_alg : (expected.alg != .sha256) = false := by rw [halg]; decide
  have hl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
  dsimp [Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run]
  simp only [hf_alg, hl, Bool.false_eq_true, ↓reduceIte]
  unfold StateT.bind
  rw [show Internal.hmacSha256M raw key msg s = (Internal.hmacSha256M raw key msg).run s from rfl,
    hmacSha256M_raw_ok raw s sH key msg bs hrawH hbs]
  dsimp only [Bind.bind, Monad.toBind, Id.instMonad]
  have hsz : bs.size = expected.bytes.size := by rw [hbs, hlen]
  exact ctEqM_raw_ok raw sH sC bs expected.bytes hsz hrawC

/-- `defaultApi.mapRawError` satisfies `test_cryptohash_mapRawError_preservesContract`. -/
theorem cryptohash_mapRawError_preservesContract :
    AllPass (test_cryptohash_mapRawError_preservesContract defaultApi) := by
  intro raw
  exact Raw.Proofs.raw_mapRawError_mapsKindsAndNonEmptyMessage raw

set_option maxRecDepth 2048 in
/-- `Internal.mkApiM` satisfies `test_cryptohash_hash_delegatesAndChecksLength`. -/
theorem cryptohash_hash_delegatesAndChecksLength :
    AllPass (test_cryptohash_hash_delegatesAndChecksLength Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ alg msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hash_delegatesAndChecksLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let s₁ : MockCryptoHashState :=
    { digestCalls := dc + 1, hmacCalls := hc, ctEqCalls := cc,
      failDigestWith := none, failHmacWith := fh, failCtEqWith := fc,
      corruptDigestLen := none, corruptHmacLen := ch }
  cases alg
  · rw [hashM_raw_ok _ _ s₁ .sha256 msg (mockDigestBytes .sha256 msg) rfl (mockDigestBytes_size .sha256 msg),
      hashM_raw_ok _ _ s₁ .sha512 msg (mockDigestBytes .sha512 msg) rfl (mockDigestBytes_size .sha512 msg)]
    dsimp only
    refine ⟨⟨rfl, rfl, rfl⟩,
      ⟨rfl, mockDigestBytes_size .sha256 msg, mockDigestBytes_size .sha256 msg,
        by simp [Digest.isValid, mockDigestBytes_size]⟩, ?_⟩
    simp
  · rw [hashM_raw_ok _ _ s₁ .sha512 msg (mockDigestBytes .sha512 msg) rfl (mockDigestBytes_size .sha512 msg),
      hashM_raw_ok _ _ s₁ .sha256 msg (mockDigestBytes .sha256 msg) rfl (mockDigestBytes_size .sha256 msg)]
    dsimp only
    refine ⟨⟨rfl, rfl, rfl⟩,
      ⟨rfl, mockDigestBytes_size .sha512 msg, mockDigestBytes_size .sha512 msg,
        by simp [Digest.isValid, mockDigestBytes_size]⟩, ?_⟩
    simp

/-- Non-vacuity witness for `test_cryptohash_hash_delegatesAndChecksLength`. -/
theorem reach_cryptohash_hash_delegatesAndChecksLength :
    CanReach (test_cryptohash_hash_delegatesAndChecksLength Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl⟩, .sha256, ByteArray.empty,
    cryptohash_hash_delegatesAndChecksLength {} ⟨rfl, rfl⟩ .sha256 ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hash_propagatesRawError`. -/
theorem cryptohash_hash_propagatesRawError :
    AllPass (test_cryptohash_hash_propagatesRawError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail alg msg
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_hash_propagatesRawError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hashM_raw_err _ _ _ alg msg err rfl,
    hashM_raw_err _ _ _ .sha256 msg err rfl,
    hashM_raw_err _ _ _ .sha512 msg err rfl]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_hash_propagatesRawError`. -/
theorem reach_cryptohash_hash_propagatesRawError :
    CanReach (test_cryptohash_hash_propagatesRawError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  exact ⟨err, by decide, { failDigestWith := some err }, rfl, .sha256, ByteArray.empty,
    cryptohash_hash_propagatesRawError err (by decide) { failDigestWith := some err } rfl .sha256 ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hash_rejectsWrongRawLength`. -/
theorem cryptohash_hash_rejectsWrongRawLength :
    AllPass (test_cryptohash_hash_rejectsWrongRawLength Internal.mkApiM) := by
  intro alg badLen hbad ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hash_rejectsWrongRawLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hashM_raw_corrupt _ _ _ alg msg badLen rfl hbad]
  dsimp only
  refine ⟨rfl, ⟨rfl, ?_⟩, trivial⟩
  intro hempty
  have hlen := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen
  have hpos : 0 < (toString ("digest length mismatch: expected " : String)).length := by decide
  omega

/-- Non-vacuity witness for `test_cryptohash_hash_rejectsWrongRawLength`. -/
theorem reach_cryptohash_hash_rejectsWrongRawLength :
    CanReach (test_cryptohash_hash_rejectsWrongRawLength Internal.mkApiM) :=
  ⟨.sha256, 0, by decide, { corruptDigestLen := some 0 }, ⟨rfl, rfl⟩, ByteArray.empty,
    cryptohash_hash_rejectsWrongRawLength .sha256 0 (by decide) { corruptDigestLen := some 0 } ⟨rfl, rfl⟩ ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hmacSha256_delegatesAndChecksLength`. -/
theorem cryptohash_hmacSha256_delegatesAndChecksLength :
    AllPass (test_cryptohash_hmacSha256_delegatesAndChecksLength Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ key msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hmacSha256_delegatesAndChecksLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_ok _ _ _ key msg (mockHmacBytes key msg) rfl (mockHmacBytes_size key msg)]
  dsimp only
  exact ⟨⟨rfl, rfl, rfl⟩,
    ⟨rfl, mockHmacBytes_size key msg, by unfold ValidDigest; rw [mockHmacBytes_size]; rfl,
      by simp [Digest.isValid, digestLen, mockHmacBytes_size]⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_hmacSha256_delegatesAndChecksLength`. -/
theorem reach_cryptohash_hmacSha256_delegatesAndChecksLength :
    CanReach (test_cryptohash_hmacSha256_delegatesAndChecksLength Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl⟩, ByteArray.empty, ByteArray.empty,
    cryptohash_hmacSha256_delegatesAndChecksLength {} ⟨rfl, rfl⟩ ByteArray.empty ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hmacSha256_propagatesRawError`. -/
theorem cryptohash_hmacSha256_propagatesRawError :
    AllPass (test_cryptohash_hmacSha256_propagatesRawError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail key msg
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_hmacSha256_propagatesRawError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_err _ _ _ key msg err rfl]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_hmacSha256_propagatesRawError`. -/
theorem reach_cryptohash_hmacSha256_propagatesRawError :
    CanReach (test_cryptohash_hmacSha256_propagatesRawError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  exact ⟨err, by decide, { failHmacWith := some err }, rfl, ByteArray.empty, ByteArray.empty,
    cryptohash_hmacSha256_propagatesRawError err (by decide) { failHmacWith := some err } rfl ByteArray.empty ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_hmacSha256_rejectsWrongRawLength`. -/
theorem cryptohash_hmacSha256_rejectsWrongRawLength :
    AllPass (test_cryptohash_hmacSha256_rejectsWrongRawLength Internal.mkApiM) := by
  intro badLen hbad ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hfail, hcorr⟩ key msg
  dsimp only at hfail hcorr
  subst hfail
  subst hcorr
  dsimp [test_cryptohash_hmacSha256_rejectsWrongRawLength, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_corrupt _ _ _ key msg badLen rfl hbad]
  dsimp only
  refine ⟨rfl, ⟨rfl, ?_⟩, trivial⟩
  intro hempty
  have hlen := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen
  have hpos : 0 < (toString ("HMAC-SHA256 length mismatch: expected 32 bytes, got " : String)).length := by decide
  omega

/-- Non-vacuity witness for `test_cryptohash_hmacSha256_rejectsWrongRawLength`. -/
theorem reach_cryptohash_hmacSha256_rejectsWrongRawLength :
    CanReach (test_cryptohash_hmacSha256_rejectsWrongRawLength Internal.mkApiM) :=
  ⟨0, by decide, { corruptHmacLen := some 0 }, ⟨rfl, rfl⟩, ByteArray.empty, ByteArray.empty,
    cryptohash_hmacSha256_rejectsWrongRawLength 0 (by decide) { corruptHmacLen := some 0 } ⟨rfl, rfl⟩ ByteArray.empty ByteArray.empty⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall`. -/
theorem cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall :
    AllPass (test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall Internal.mkApiM) := by
  intro s₀ a b hneq
  dsimp [test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall, Internal.mkApiM, Internal.ctEqM,
    Pure.pure, StateT.pure, StateT.run, Core.NondetTest.assert]
  have hne : (a.size != b.size) = true := bne_iff_ne.mpr hneq
  simp only [hne, ↓reduceIte]
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall`. -/
theorem reach_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall :
    CanReach (test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall Internal.mkApiM) :=
  ⟨{}, ByteArray.empty, ByteArray.mk #[0], by decide,
    cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall {} ByteArray.empty (ByteArray.mk #[0]) (by decide)⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_ctEq_equalLengthsDelegates`. -/
theorem cryptohash_ctEq_equalLengthsDelegates :
    AllPass (test_cryptohash_ctEq_equalLengthsDelegates Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail a b heq
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_ctEq_equalLengthsDelegates, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let s₁ : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc, ctEqCalls := cc + 1,
      failDigestWith := fd, failHmacWith := fh, failCtEqWith := none,
      corruptDigestLen := cd, corruptHmacLen := ch }
  rw [ctEqM_raw_ok _ _ s₁ a b heq (by change (if (a.size != b.size) = true then _ else _) = _; simp [bne_eq_false_iff_eq.mpr heq]; rfl),
    ctEqM_raw_ok _ _ s₁ b a heq.symm (by change (if (b.size != a.size) = true then _ else _) = _; simp [bne_eq_false_iff_eq.mpr heq.symm]; rfl),
    ctEqM_raw_ok _ _ s₁ a a rfl (by change (if (a.size != a.size) = true then _ else _) = _; simp; rfl)]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, ⟨congrArg Except.ok (byteArray_beq_symm a b), congrArg Except.ok (beq_self_eq_true a)⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_ctEq_equalLengthsDelegates`. -/
theorem reach_cryptohash_ctEq_equalLengthsDelegates :
    CanReach (test_cryptohash_ctEq_equalLengthsDelegates Internal.mkApiM) :=
  ⟨{}, rfl, ByteArray.empty, ByteArray.empty, rfl,
    cryptohash_ctEq_equalLengthsDelegates {} rfl ByteArray.empty ByteArray.empty rfl⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_ctEq_equalLengthsPropagatesRawError`. -/
theorem cryptohash_ctEq_equalLengthsPropagatesRawError :
    AllPass (test_cryptohash_ctEq_equalLengthsPropagatesRawError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail a b heq
  dsimp only at hfail
  subst hfail
  dsimp [test_cryptohash_ctEq_equalLengthsPropagatesRawError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let s₁ : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc, ctEqCalls := cc + 1,
      failDigestWith := fd, failHmacWith := fh, failCtEqWith := some err,
      corruptDigestLen := cd, corruptHmacLen := ch }
  rw [ctEqM_raw_err _ _ s₁ a b err heq (by change (if (a.size != b.size) = true then _ else _) = _; simp [bne_eq_false_iff_eq.mpr heq]; rfl)]
  dsimp only
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_ctEq_equalLengthsPropagatesRawError`. -/
theorem reach_cryptohash_ctEq_equalLengthsPropagatesRawError :
    CanReach (test_cryptohash_ctEq_equalLengthsPropagatesRawError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  exact ⟨err, by decide, { failCtEqWith := some err }, rfl, ByteArray.empty, ByteArray.empty, rfl,
    cryptohash_ctEq_equalLengthsPropagatesRawError err (by decide) { failCtEqWith := some err } rfl ByteArray.empty ByteArray.empty rfl⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls`. -/
theorem cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls :
    AllPass (test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls Internal.mkApiM) := by
  intro s₀ key msg expected halg
  have hne : (expected.alg != .sha256) = true := by
    cases h : expected.alg with
    | sha256 => exact absurd h halg
    | sha512 => decide
  dsimp [test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls, Internal.mkApiM,
    Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run,
    Core.NondetTest.assert]
  simp only [hne, ↓reduceIte]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, by decide⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls`. -/
theorem reach_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls :
    CanReach (test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls Internal.mkApiM) :=
  ⟨{}, ByteArray.empty, ByteArray.empty, { alg := .sha512, bytes := ByteArray.empty }, by decide,
    cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls {} ByteArray.empty ByteArray.empty { alg := .sha512, bytes := ByteArray.empty } (by decide)⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls`. -/
theorem cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls :
    AllPass (test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls Internal.mkApiM) := by
  intro s₀ key msg expected ⟨halg, hlen⟩
  dsimp only at halg hlen ⊢
  have hf : (expected.alg != .sha256) = false := by rw [halg]; decide
  have ht : (expected.bytes.size != 32) = true := bne_iff_ne.mpr hlen
  dsimp [test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls, AllPassRun,
    Internal.mkApiM, Internal.verifyHmacSha256M, Bind.bind, StateT.bind, Pure.pure, StateT.pure,
    StateT.run, Core.NondetTest.assert]
  simp only [hf, Bool.false_eq_true, ↓reduceIte, ht]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, ?_⟩, trivial⟩
  intro hempty
  have hlen2 := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen2
  have hpos : 0 < (toString ("HMAC-SHA256 length mismatch: expected 32 bytes, got " : String)).length := by decide
  omega

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls`. -/
theorem reach_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls :
    CanReach (test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls Internal.mkApiM) :=
  ⟨{}, ByteArray.empty, ByteArray.empty, { alg := .sha256, bytes := ByteArray.empty }, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls {} ByteArray.empty ByteArray.empty { alg := .sha256, bytes := ByteArray.empty } ⟨rfl, by decide⟩⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_propagatesHmacError`. -/
theorem cryptohash_verifyHmacSha256_propagatesHmacError :
    AllPass (test_cryptohash_verifyHmacSha256_propagatesHmacError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ hfail key msg expected ⟨halg, hlen⟩
  dsimp only at hfail halg hlen
  subst hfail
  dsimp [test_cryptohash_verifyHmacSha256_propagatesHmacError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [verifyHmacSha256M_raw_hmacErr _ _ _ err key msg expected halg hlen rfl]
  dsimp only
  exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_propagatesHmacError`. -/
theorem reach_cryptohash_verifyHmacSha256_propagatesHmacError :
    CanReach (test_cryptohash_verifyHmacSha256_propagatesHmacError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨err, by decide, { failHmacWith := some err }, rfl, ByteArray.empty, ByteArray.empty, d, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_propagatesHmacError err (by decide) { failHmacWith := some err } rfl ByteArray.empty ByteArray.empty d ⟨rfl, by decide⟩⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_propagatesCtEqError`. -/
theorem cryptohash_verifyHmacSha256_propagatesCtEqError :
    AllPass (test_cryptohash_verifyHmacSha256_propagatesCtEqError Internal.mkApiM) := by
  intro err _ ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hf1, hcorr, hf2⟩ key msg expected ⟨halg, hlen⟩
  dsimp only at hf1 hcorr hf2 halg hlen
  subst hf1
  subst hcorr
  subst hf2
  dsimp [test_cryptohash_verifyHmacSha256_propagatesCtEqError, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  let sH : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc + 1, ctEqCalls := cc,
      failDigestWith := fd, failHmacWith := none, failCtEqWith := some err,
      corruptDigestLen := cd, corruptHmacLen := none }
  let sC : MockCryptoHashState := { sH with ctEqCalls := cc + 1 }
  have hbs := mockHmacBytes_size key msg
  have hne : ((mockHmacBytes key msg).size != expected.bytes.size) = false :=
    bne_eq_false_iff_eq.mpr (by rw [hbs, hlen])
  rw [verifyHmacSha256M_raw_ctEqErr _ _ sH sC err key msg (mockHmacBytes key msg) expected halg hlen hbs]
  · dsimp only
    exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩
  · rfl
  · revert hne
    generalize (mockHmacBytes key msg) = x
    intro hne
    change (if (x.size != expected.bytes.size) = true then
      (Except.error { kind := .lengthMismatch, message := "length mismatch" }, sC)
      else (Except.error err, sC)) = _
    simp [hne]

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_propagatesCtEqError`. -/
theorem reach_cryptohash_verifyHmacSha256_propagatesCtEqError :
    CanReach (test_cryptohash_verifyHmacSha256_propagatesCtEqError Internal.mkApiM) := by
  let err : CryptoHashError := { kind := .cryptoError, message := "err" }
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨err, by decide, { failCtEqWith := some err }, ⟨rfl, rfl, rfl⟩, ByteArray.empty, ByteArray.empty, d, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_propagatesCtEqError err (by decide) { failCtEqWith := some err } ⟨rfl, rfl, rfl⟩ ByteArray.empty ByteArray.empty d ⟨rfl, by decide⟩⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered`. -/
theorem cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered :
    AllPass (test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered Internal.mkApiM) := by
  intro ⟨dc, hc, cc, fd, fh, fc, cd, ch⟩ ⟨hf1, hcorr, hf2⟩ key msg expected ⟨halg, hlen⟩
  dsimp only at hf1 hcorr hf2 halg hlen
  subst hf1
  subst hcorr
  subst hf2
  let tagBytes := mockHmacBytes key msg
  have hts : tagBytes.size = 32 := mockHmacBytes_size key msg
  let tampBytes := tagBytes.set! 0 (tagBytes[0]! ^^^ 1)
  have htamp_size : tampBytes.size = 32 := by simp [tampBytes, ByteArray.size_set!, hts]
  have hne_exp : (tagBytes.size != expected.bytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [hts, hlen])
  have hne_tamp : (tagBytes.size != tampBytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [hts, htamp_size])
  let t1Bytes := mockHmacBytes "k1".toUTF8 "m1".toUTF8
  have ht1s : t1Bytes.size = 32 := mockHmacBytes_size "k1".toUTF8 "m1".toUTF8
  let t2Bytes := mockHmacBytes "k2".toUTF8 "m1".toUTF8
  have ht2s : t2Bytes.size = 32 := mockHmacBytes_size "k2".toUTF8 "m1".toUTF8
  have hne_21 : (t2Bytes.size != t1Bytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [ht2s, ht1s])
  let t3Bytes := mockHmacBytes "k1".toUTF8 "m2".toUTF8
  have ht3s : t3Bytes.size = 32 := mockHmacBytes_size "k1".toUTF8 "m2".toUTF8
  have hne_31 : (t3Bytes.size != t1Bytes.size) = false := bne_eq_false_iff_eq.mpr (by rw [ht3s, ht1s])
  let sH : MockCryptoHashState :=
    { digestCalls := dc, hmacCalls := hc + 1, ctEqCalls := cc,
      failDigestWith := fd, failHmacWith := none, failCtEqWith := none,
      corruptDigestLen := cd, corruptHmacLen := none }
  let sC : MockCryptoHashState := { sH with ctEqCalls := cc + 1 }
  dsimp [test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered, AllPass, AllPassRun, Internal.mkApiM,
    Bind.bind, Pure.pure, Core.NondetTest.assert, Core.NondetTest.assume, Core.NondetTest.nondet]
  rw [hmacSha256M_raw_ok _ _ sH key msg tagBytes rfl hts]
  dsimp only
  rw [verifyHmacSha256M_raw_ok _ _ sH sC key msg tagBytes expected halg hlen hts]
  · dsimp only
    rw [verifyHmacSha256M_raw_ok _ _ sH sC key msg tagBytes { alg := .sha256, bytes := tagBytes } rfl hts hts]
    · rw [verifyHmacSha256M_raw_ok _ _ sH sC key msg tagBytes { alg := .sha256, bytes := tampBytes } rfl htamp_size hts]
      · rw [hmacSha256M_raw_ok _ _ sH "k1".toUTF8 "m1".toUTF8 t1Bytes rfl ht1s]
        dsimp only
        rw [verifyHmacSha256M_raw_ok _ _ sH sC "k2".toUTF8 "m1".toUTF8 t2Bytes { alg := .sha256, bytes := t1Bytes } rfl ht1s ht2s]
        · rw [verifyHmacSha256M_raw_ok _ _ sH sC "k1".toUTF8 "m2".toUTF8 t3Bytes { alg := .sha256, bytes := t1Bytes } rfl ht1s ht3s]
          · dsimp only
            exact ⟨⟨rfl, rfl⟩, rfl, congrArg Except.ok (beq_self_eq_true tagBytes),
              congrArg Except.ok (byteArray_tamper_byte0_ne tagBytes hts),
              congrArg Except.ok mockHmacBytes_k2_m1_ne,
              congrArg Except.ok mockHmacBytes_k1_m2_ne, trivial⟩
          · rfl
          · revert hne_31
            generalize t3Bytes = x3; generalize t1Bytes = x1; intro hne_31
            change (if (x3.size != x1.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (x3 == x1), sC)) = _
            simp [hne_31]
        · rfl
        · revert hne_21
          generalize t2Bytes = x2; generalize t1Bytes = x1; intro hne_21
          change (if (x2.size != x1.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (x2 == x1), sC)) = _
          simp [hne_21]
      · rfl
      · revert hne_tamp
        generalize tagBytes = xt; generalize tampBytes = xp; intro hne_tamp
        change (if (xt.size != xp.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (xt == xp), sC)) = _
        simp [hne_tamp]
    · rfl
    · generalize tagBytes = xs
      change (if (xs.size != xs.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (xs == xs), sC)) = _
      simp
  · rfl
  · revert hne_exp
    generalize tagBytes = xe; intro hne_exp
    change (if (xe.size != expected.bytes.size) = true then (Except.error ({ kind := .lengthMismatch, message := "length mismatch" } : CryptoHashError), sC) else (Except.ok (xe == expected.bytes), sC)) = _
    simp [hne_exp]

/-- Non-vacuity witness for `test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered`. -/
theorem reach_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered :
    CanReach (test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered Internal.mkApiM) := by
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨{}, ⟨rfl, rfl, rfl⟩, ByteArray.empty, ByteArray.empty, d, ⟨rfl, by decide⟩,
    cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered {} ⟨rfl, rfl, rfl⟩ ByteArray.empty ByteArray.empty d ⟨rfl, by decide⟩⟩

/-- `defaultApi` satisfies `test_cryptohash_toHex_formatAndRoundTrip`. -/
theorem cryptohash_toHex_formatAndRoundTrip :
    AllPass (test_cryptohash_toHex_formatAndRoundTrip defaultApi) := by
  intro d hd
  dsimp only
  dsimp [test_cryptohash_toHex_formatAndRoundTrip, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.toHex, Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert,
    Core.NondetTest.nondet, Core.NondetTest.assume]
  have hlen : (String.ofList (Internal.formatHexList d.bytes.data.toList)).length = 2 * digestLen d.alg := by
    rw [String.length_ofList, formatHexList_length, Array.length_toList, ← ByteArray.size, hd]
  have hall : (String.ofList (Internal.formatHexList d.bytes.data.toList)).toList.all isLowerHexChar = true := by
    rw [String.toList_ofList]
    exact formatHexList_all_lowerHex d.bytes.data.toList
  have hrt :
      (match Internal.decodeHexPairs (String.ofList (Internal.formatHexList d.bytes.data.toList)).toList with
        | none => Except.error ({ kind := .invalidHex, message := "hex string must have even length and contain only ASCII hex digits" } : CryptoHashError)
        | some bs =>
          let ba := ByteArray.mk bs.toArray
          if (ba.size != digestLen d.alg) = true then
            Except.error ({ kind := .lengthMismatch, message := s!"expected {digestLen d.alg} digest bytes, got {ba.size}" } : CryptoHashError)
          else
            Except.ok ({ alg := d.alg, bytes := ba } : Digest)) = Except.ok d := by
    rw [String.toList_ofList, decodeHexPairs_formatHexList]
    have hba : ByteArray.mk d.bytes.data.toList.toArray = d.bytes := by
      cases d.bytes
      simp
    have hsz : ((ByteArray.mk d.bytes.data.toList.toArray).size != digestLen d.alg) = false := by
      rw [hba]
      exact bne_eq_false_iff_eq.mpr hd
    simp only [hsz, Bool.false_eq_true, ↓reduceIte, hba]
  refine ⟨hlen, hall, hrt, ?_⟩
  intro i hi
  have hi_list : i < d.bytes.data.toList.length := by
    change i < d.bytes.data.size
    change d.bytes.data.size = digestLen d.alg at hd
    omega
  have hget := formatHexList_getElem? d.bytes.data.toList i hi_list
  have hb_eq : d.bytes.data.toList[i] = d.bytes[i]! := by
    have hi_ba : i < d.bytes.size := hd ▸ hi
    rw [getElem!_pos d.bytes i hi_ba]
    rfl
  rw [hb_eq] at hget
  obtain ⟨hd_lt, hr_lt⟩ := uint8_nibble_bounds (d.bytes[i]!)
  have hdg1 := fin16_lowerHexDigit_eq ⟨(d.bytes[i]!).toNat / 16, hd_lt⟩
  have hdg2 := fin16_lowerHexDigit_eq ⟨(d.bytes[i]!).toNat % 16, hr_lt⟩
  dsimp only [lowerHexDigitSpec] at hdg1 hdg2
  rw [String.toList_ofList]
  refine ⟨?_, ?_, trivial⟩
  · rw [hget.1, ← hdg1]
    rfl
  · rw [hget.2, ← hdg2]
    rfl

/-- Non-vacuity witness for `test_cryptohash_toHex_formatAndRoundTrip`. -/
theorem reach_cryptohash_toHex_formatAndRoundTrip :
    CanReach (test_cryptohash_toHex_formatAndRoundTrip defaultApi) := by
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  have h := cryptohash_toHex_formatAndRoundTrip d (by decide)
  dsimp [AllPass, AllPassRun, test_cryptohash_toHex_formatAndRoundTrip,
    Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert, Bind.bind] at h
  exact ⟨d, by decide, h.1, h.2.1, h.2.2.1, 0, by decide, h.2.2.2 0 (by decide)⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips`. -/
theorem cryptohash_fromHex_acceptsUppercaseAndRoundTrips :
    AllPass (test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips defaultApi) := by
  intro d hd
  dsimp only
  dsimp [test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.toHex, Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  rw [String.toList_ofList, String.toList_ofList, decodeHexPairs_upper_formatHexList]
  have hba : ByteArray.mk d.bytes.data.toList.toArray = d.bytes := by
    cases d.bytes
    simp
  have hsz : ((ByteArray.mk d.bytes.data.toList.toArray).size != digestLen d.alg) = false := by
    rw [hba]
    exact bne_eq_false_iff_eq.mpr hd
  simp only [hsz, Bool.false_eq_true, ↓reduceIte, hba]
  exact ⟨trivial, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips`. -/
theorem reach_cryptohash_fromHex_acceptsUppercaseAndRoundTrips :
    CanReach (test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips defaultApi) := by
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨d, by decide, cryptohash_fromHex_acceptsUppercaseAndRoundTrips d (by decide)⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip`. -/
theorem cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip :
    AllPass (test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip defaultApi) := by
  intro alg s
  dsimp [test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip, AllPassRun, defaultApi,
    Internal.mkApiM, Internal.toHex, Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  cases hdec : Internal.decodeHexPairs s.toList with
  | none =>
    refine ⟨?_, trivial⟩
    decide
  | some bs =>
    dsimp only
    by_cases hsz : (ByteArray.mk bs.toArray).size = digestLen alg
    · have hf : ((ByteArray.mk bs.toArray).size != digestLen alg) = false := bne_eq_false_iff_eq.mpr hsz
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      have hvalid : ValidDigest { alg := alg, bytes := ByteArray.mk bs.toArray } := hsz
      have hisValid : Digest.isValid { alg := alg, bytes := ByteArray.mk bs.toArray } = true := by
        simp [Digest.isValid, hsz]
      refine ⟨⟨trivial, hsz, hvalid, hisValid⟩, ?_, trivial⟩
      rw [String.toList_ofList]
      change Internal.formatHexList bs.toArray.toList = s.toList.map Char.toLower
      rw [toList_toArray_eq]
      exact decodeHexPairs_some_format hdec
    · have ht : ((ByteArray.mk bs.toArray).size != digestLen alg) = true := bne_iff_ne.mpr hsz
      simp only [ht, ↓reduceIte]
      refine ⟨?_, trivial⟩
      intro hempty
      have hlen := congrArg String.length hempty
      simp only [String.length_append, String.length_empty] at hlen
      have hpref : (toString "expected ").length = 9 := by decide
      rw [hpref] at hlen
      omega

/-- `defaultApi` satisfies `test_cryptohash_fromHex_rejectsNonHexChar`. -/
theorem cryptohash_fromHex_rejectsNonHexChar :
    AllPass (test_cryptohash_fromHex_rejectsNonHexChar defaultApi) := by
  intro alg s idx ⟨hidx, hbad⟩
  dsimp only at hidx hbad ⊢
  change isHexChar s.toList[idx]! = false at hbad
  dsimp [test_cryptohash_fromHex_rejectsNonHexChar, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  have hidx_list : idx < s.toList.length := by simpa [String.length_toList] using hidx
  have hbad' : isHexChar s.toList[idx] = false := by
    rwa [list_getElem!_eq s.toList idx hidx_list] at hbad
  rw [decodeHexPairs_none_of_nonHex hidx_list hbad']
  exact ⟨⟨rfl, by decide⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_fromHex_rejectsNonHexChar`. -/
theorem reach_cryptohash_fromHex_rejectsNonHexChar :
    CanReach (test_cryptohash_fromHex_rejectsNonHexChar defaultApi) :=
  ⟨.sha256, "z", 0, ⟨by decide, by decide⟩,
    cryptohash_fromHex_rejectsNonHexChar .sha256 "z" 0 ⟨by decide, by decide⟩⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_rejectsOddLengthHex`. -/
theorem cryptohash_fromHex_rejectsOddLengthHex :
    AllPass (test_cryptohash_fromHex_rejectsOddLengthHex defaultApi) := by
  intro alg s ⟨hodd, _⟩
  dsimp only at hodd ⊢
  dsimp [test_cryptohash_fromHex_rejectsOddLengthHex, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  have hodd_list : s.toList.length % 2 = 1 := by simpa [String.length_toList] using hodd
  rw [decodeHexPairs_none_of_odd hodd_list]
  exact ⟨⟨rfl, by decide⟩, trivial⟩

/-- Non-vacuity witness for `test_cryptohash_fromHex_rejectsOddLengthHex`. -/
theorem reach_cryptohash_fromHex_rejectsOddLengthHex :
    CanReach (test_cryptohash_fromHex_rejectsOddLengthHex defaultApi) :=
  ⟨.sha256, "a", ⟨by decide, by decide⟩,
    cryptohash_fromHex_rejectsOddLengthHex .sha256 "a" ⟨by decide, by decide⟩⟩

/-- `defaultApi` satisfies `test_cryptohash_fromHex_rejectsWrongEvenHexLength`. -/
theorem cryptohash_fromHex_rejectsWrongEvenHexLength :
    AllPass (test_cryptohash_fromHex_rejectsWrongEvenHexLength defaultApi) := by
  intro alg s ⟨heven, hlen, hall⟩
  dsimp only at heven hlen hall ⊢
  change s.toList.all isHexChar = true at hall
  dsimp [test_cryptohash_fromHex_rejectsWrongEvenHexLength, AllPassRun, defaultApi, Internal.mkApiM,
    Internal.fromHex, Bind.bind, Pure.pure, Core.NondetTest.assert]
  have heven_list : s.toList.length % 2 = 0 := by simpa [String.length_toList] using heven
  obtain ⟨bs, hbs, h2⟩ := decodeHexPairs_some_of_all_hex heven_list hall
  rw [hbs]
  have hne : ((ByteArray.mk bs.toArray).size != digestLen alg) = true := by
    apply bne_iff_ne.mpr
    intro heq
    have hs_eq : s.length = 2 * digestLen alg := by
      rw [← String.length_toList, ← h2]
      have hbs_len : bs.length = (ByteArray.mk bs.toArray).size := by
        simp [ByteArray.size]
      omega
    exact hlen hs_eq
  simp only [hne, ↓reduceIte]
  refine ⟨⟨trivial, ?_⟩, trivial⟩
  intro hempty
  have hlen2 := congrArg String.length hempty
  simp only [String.length_append, String.length_empty] at hlen2
  have hpref : (toString "expected ").length = 9 := by decide
  rw [hpref] at hlen2
  omega

/-- Non-vacuity witness for `test_cryptohash_fromHex_rejectsWrongEvenHexLength`. -/
theorem reach_cryptohash_fromHex_rejectsWrongEvenHexLength :
    CanReach (test_cryptohash_fromHex_rejectsWrongEvenHexLength defaultApi) :=
  ⟨.sha256, "", ⟨by decide, by decide, by decide⟩,
    cryptohash_fromHex_rejectsWrongEvenHexLength .sha256 "" ⟨by decide, by decide, by decide⟩⟩

private theorem fromHex_toHex_of_validHex (alg : HashAlg) (s expected : String)
    (hlen : s.length = 2 * digestLen alg)
    (hall : s.toList.all isHexChar = true)
    (hlow : s.toList.map Char.toLower = expected.toList) :
    ∃ d, Internal.fromHex alg s = .ok d ∧ Internal.toHex d = expected := by
  have heven : s.toList.length % 2 = 0 := by
    rw [String.length_toList, hlen]
    omega
  obtain ⟨bs, hbs, h2⟩ := decodeHexPairs_some_of_all_hex heven hall
  have hsz : (ByteArray.mk bs.toArray).size = digestLen alg := by
    have hbs_len : bs.length = (ByteArray.mk bs.toArray).size := by
      simp [ByteArray.size]
    have hsl : s.toList.length = 2 * digestLen alg := by
      simpa [String.length_toList] using hlen
    omega
  have hf : ((ByteArray.mk bs.toArray).size != digestLen alg) = false :=
    bne_eq_false_iff_eq.mpr hsz
  refine ⟨{ alg := alg, bytes := ByteArray.mk bs.toArray }, ?_, ?_⟩
  · unfold Internal.fromHex
    rw [hbs]
    simp [hf]
  · unfold Internal.toHex
    change String.ofList (Internal.formatHexList bs.toArray.toList) = expected
    rw [toList_toArray_eq, decodeHexPairs_some_format hbs, hlow, String.ofList_toList]

private def checkUpperLowerHex (c : Fin 128) : Bool :=
  let ch := Char.ofNat c.1
  if isLowerHexChar ch then
    isHexChar (Char.toUpper ch) && Char.toLower (Char.toUpper ch) == ch
  else true

private theorem fin128_upper_lower_hex : ∀ c : Fin 128, checkUpperLowerHex c = true := by
  decide

private theorem isHexChar_toUpper_of_isLowerHex {c : Char} (h : isLowerHexChar c = true) :
    isHexChar (Char.toUpper c) = true ∧ Char.toLower (Char.toUpper c) = c := by
  have hlt : c.toNat < 128 := by
    unfold isLowerHexChar at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨_, hle⟩ | ⟨_, hle⟩
    · have h1 : c.toNat ≤ '9'.toNat := UInt32.le_iff_toNat_le.mp hle
      simp at h1; omega
    · have h1 : c.toNat ≤ 'f'.toNat := UInt32.le_iff_toNat_le.mp hle
      simp at h1; omega
  have hm := fin128_upper_lower_hex ⟨c.toNat, hlt⟩
  unfold checkUpperLowerHex at hm
  dsimp only at hm
  have hc : isLowerHexChar (Char.ofNat c.toNat) = true := by simpa [Char.ofNat_toNat] using h
  rw [hc] at hm
  simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hm
  simpa [Char.ofNat_toNat] using hm

private theorem map_toLower_toUpper_of_all_lowerHex :
    ∀ cs : List Char, cs.all isLowerHexChar = true → cs.map (Char.toLower ∘ Char.toUpper) = cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, Function.comp_apply,
      (isHexChar_toUpper_of_isLowerHex h.1).2,
      map_toLower_toUpper_of_all_lowerHex cs h.2]

private theorem fromHex_toUpper_toHex_of_lowerHex (alg : HashAlg) (s : String)
    (hlen : s.length = 2 * digestLen alg)
    (hall : s.toList.all isLowerHexChar = true) :
    ∃ d, Internal.fromHex alg (String.ofList (s.toList.map Char.toUpper)) = .ok d ∧
      Internal.toHex d = s := by
  have hall_up : (String.ofList (s.toList.map Char.toUpper)).toList.all isHexChar = true := by
    rw [String.toList_ofList, List.all_map]
    rw [List.all_eq_true] at hall ⊢
    intro c hc
    exact (isHexChar_toUpper_of_isLowerHex (hall c hc)).1
  have hlow_up : (String.ofList (s.toList.map Char.toUpper)).toList.map Char.toLower = s.toList := by
    rw [String.toList_ofList, List.map_map]
    exact map_toLower_toUpper_of_all_lowerHex s.toList hall
  have hlen_up : (String.ofList (s.toList.map Char.toUpper)).length = 2 * digestLen alg := by
    rw [String.length_ofList, List.length_map, String.length_toList, hlen]
  exact fromHex_toHex_of_validHex alg (String.ofList (s.toList.map Char.toUpper)) s hlen_up hall_up hlow_up

set_option maxRecDepth 2048 in
/-- `defaultApi` satisfies `empirical_cryptohash_vectorHexRoundTrip`. -/
theorem cryptohash_vectorHexRoundTrip :
    AllPass (empirical_cryptohash_vectorHexRoundTrip defaultApi) := by
  dsimp only [AllPass, AllPassRun, empirical_cryptohash_vectorHexRoundTrip, defaultApi, Internal.mkApiM,
    Core.NondetTest.assert, Bind.bind, Pure.pure]
  obtain ⟨d1, h1_ok, h1_hex⟩ := fromHex_toHex_of_validHex .sha256
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    (by decide) (by decide) (by decide)
  obtain ⟨d2, h2_ok, h2_hex⟩ := fromHex_toHex_of_validHex .sha512
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    (by decide) (by decide) (by decide)
  obtain ⟨d3, h3_ok, h3_hex⟩ := fromHex_toUpper_toHex_of_lowerHex .sha256
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
    (by decide) (by decide)
  rw [h1_ok, h2_ok, h3_ok]
  exact ⟨h1_hex, h2_hex, h3_hex, trivial⟩

end LeanSwe.CryptoHash.Proofs
