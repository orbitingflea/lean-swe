import LeanSwe.Uuid.Interface
import LeanSwe.Uuid.SpecTests

namespace LeanSwe.Uuid.Proofs

open Core
open Core.NondetTest
open LeanSwe.Uuid

private def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def isHexChar (c : Char) : Bool :=
  isLowerHexChar c || ('A' ≤ c && c ≤ 'F')

private theorem eq_of_size_16 (bs : ByteArray) (h : bs.size = 16) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8,
      bs = ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  cases bs with
  | mk arr =>
    cases arr with
    | mk l =>
      change l.length = 16 at h
      match l, h with
      | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], _ =>
        exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩

private theorem uint8_of_nibbles (b : UInt8) :
    UInt8.ofNat ((b.toNat / 16) * 16 + b.toNat % 16) = b := by
  have hmod : (b.toNat / 16) * 16 + b.toNat % 16 = b.toNat := by omega
  rw [hmod, UInt8.ofNat_toNat]

private theorem uint8_nibble_bounds (b : UInt8) :
    b.toNat / 16 < 16 ∧ b.toNat % 16 < 16 := by
  have h := b.toNat_lt
  omega

private theorem fin16_v4_ver :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      ((b &&& 0x0F) ||| 0x40) &&& 0xF0 = 0x40 := by
  decide

private theorem fin16_v4_var :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      ((b &&& 0x3F) ||| 0x80) &&& 0xC0 = 0x80 := by
  decide

private theorem fin16_v4_ver_low :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      ((b &&& 0x0F) ||| 0x40) &&& 0x0F = b &&& 0x0F := by
  decide

private theorem fin16_v4_var_low :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      ((b &&& 0x3F) ||| 0x80) &&& 0x3F = b &&& 0x3F := by
  decide

private theorem uint8_v4_ver (b : UInt8) :
    ((b &&& 0x0F) ||| 0x40) &&& 0xF0 = 0x40 := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_v4_ver ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

private theorem uint8_v4_var (b : UInt8) :
    ((b &&& 0x3F) ||| 0x80) &&& 0xC0 = 0x80 := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_v4_var ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

private theorem uint8_v4_ver_low (b : UInt8) :
    ((b &&& 0x0F) ||| 0x40) &&& 0x0F = b &&& 0x0F := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_v4_ver_low ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

private theorem uint8_v4_var_low (b : UInt8) :
    ((b &&& 0x3F) ||| 0x80) &&& 0x3F = b &&& 0x3F := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_v4_var_low ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

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

private theorem fin16_ver_nibble_char :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      Internal.lowerHexDigit ((((b &&& 0x0F) ||| 0x40)).toNat / 16) = '4' := by
  decide

private theorem fin16_var_nibble_char :
    ∀ hi lo : Fin 16,
      let b := UInt8.ofNat (hi.1 * 16 + lo.1)
      let c := Internal.lowerHexDigit ((((b &&& 0x3F) ||| 0x80)).toNat / 16)
      c = '8' ∨ c = '9' ∨ c = 'a' ∨ c = 'b' := by
  decide

private theorem uint8_ver_nibble_char (b : UInt8) :
    Internal.lowerHexDigit ((((b &&& 0x0F) ||| 0x40)).toNat / 16) = '4' := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_ver_nibble_char ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

private theorem uint8_var_nibble_char (b : UInt8) :
    let c := Internal.lowerHexDigit ((((b &&& 0x3F) ||| 0x80)).toNat / 16)
    c = '8' ∨ c = '9' ∨ c = 'a' ∨ c = 'b' := by
  obtain ⟨hd, hr⟩ := uint8_nibble_bounds b
  have h := fin16_var_nibble_char ⟨b.toNat / 16, hd⟩ ⟨b.toNat % 16, hr⟩
  simpa [uint8_of_nibbles b] using h

private theorem pred_lowerHexDigit (P : Char → Bool)
    (h : ∀ i : Fin 16, P (Internal.lowerHexDigit i.1) = true)
    (n : Nat) (hn : n < 16) : P (Internal.lowerHexDigit n) = true :=
  h ⟨n, hn⟩

private theorem lowerHexDigit_congr (f : Nat → Char)
    (h : ∀ i : Fin 16, f i.1 = Internal.lowerHexDigit i.1)
    (n : Nat) (hn : n < 16) : f n = Internal.lowerHexDigit n :=
  h ⟨n, hn⟩

private theorem hexCharToNibble_lt_128 {c : Char} {n : UInt8}
    (h : Internal.hexCharToNibble c = some n) : c.toNat < 128 := by
  unfold Internal.hexCharToNibble at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hle : c.toNat ≤ '9'.toNat := UInt32.le_iff_toNat_le.mp hc.2
    have h9 : '9'.toNat = 57 := rfl
    omega
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hle : c.toNat ≤ 'f'.toNat := UInt32.le_iff_toNat_le.mp hc.2
      have hf : 'f'.toNat = 102 := rfl
      omega
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hle : c.toNat ≤ 'F'.toNat := UInt32.le_iff_toNat_le.mp hc.2
        have hF : 'F'.toNat = 70 := rfl
        omega
      · cases h

private theorem isHexChar_lt_128 {c : Char} (h : isHexChar c = true) : c.toNat < 128 := by
  unfold isHexChar isLowerHexChar at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (⟨_, hc⟩ | ⟨_, hc⟩) | ⟨_, hc⟩
  · have hle : c.toNat ≤ '9'.toNat := UInt32.le_iff_toNat_le.mp hc
    have h9 : '9'.toNat = 57 := rfl
    omega
  · have hle : c.toNat ≤ 'f'.toNat := UInt32.le_iff_toNat_le.mp hc
    have hf : 'f'.toNat = 102 := rfl
    omega
  · have hle : c.toNat ≤ 'F'.toNat := UInt32.le_iff_toNat_le.mp hc
    have hF : 'F'.toNat = 70 := rfl
    omega

private def nibbleCheck (c : Char) : Bool :=
  match Internal.hexCharToNibble c with
  | none => !isHexChar c
  | some n =>
    isHexChar c &&
    (n.toNat < 16) &&
    (Internal.lowerHexDigit n.toNat == Char.toLower c) &&
    (c == '4' || n.toNat != 4) &&
    (c == '8' || c == '9' || c == 'a' || c == 'b' || c == 'A' || c == 'B' || !(8 ≤ n.toNat && n.toNat ≤ 11))

private theorem ascii_nibbleCheck :
    ∀ hi : Fin 8, ∀ lo : Fin 16,
      nibbleCheck (Char.ofNat (hi.1 * 16 + lo.1)) = true := by
  decide

private theorem char_nibbleCheck {c : Char} (hc : c.toNat < 128) :
    nibbleCheck c = true := by
  have hd : c.toNat / 16 < 8 := by omega
  have hr : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have h := ascii_nibbleCheck ⟨c.toNat / 16, hd⟩ ⟨c.toNat % 16, hr⟩
  have hrec : (c.toNat / 16) * 16 + c.toNat % 16 = c.toNat := by omega
  rw [hrec, Char.ofNat_toNat] at h
  exact h

private theorem isHexChar_false_of_pred {P : Char → Bool}
    (hcongr : ∀ hi : Fin 8, ∀ lo : Fin 16,
      P (Char.ofNat (hi.1 * 16 + lo.1)) = isHexChar (Char.ofNat (hi.1 * 16 + lo.1)))
    {c : Char} (hp : P c = false) : isHexChar c = false := by
  cases hc : isHexChar c with
  | false => rfl
  | true =>
    have hlt := isHexChar_lt_128 hc
    have hd : c.toNat / 16 < 8 := by omega
    have hr : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have h := hcongr ⟨c.toNat / 16, hd⟩ ⟨c.toNat % 16, hr⟩
    have hrec : (c.toNat / 16) * 16 + c.toNat % 16 = c.toNat := by omega
    rw [hrec, Char.ofNat_toNat] at h
    rw [hp, hc] at h
    cases h

private theorem hexCharToNibble_isHex {c : Char} (hn : isHexChar c = false) :
    Internal.hexCharToNibble c = none := by
  cases h : Internal.hexCharToNibble c with
  | none => rfl
  | some n =>
    have hc := hexCharToNibble_lt_128 h
    have hp := char_nibbleCheck hc
    simp [nibbleCheck, h, hn] at hp

private theorem hexCharToNibble_some_props {c : Char} {n : UInt8}
    (h : Internal.hexCharToNibble c = some n) :
    n.toNat < 16 ∧ Internal.lowerHexDigit n.toNat = Char.toLower c := by
  have hc := hexCharToNibble_lt_128 h
  have hp := char_nibbleCheck hc
  simp only [nibbleCheck, h, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨hp.1.1.1.2, hp.1.1.2⟩

private theorem isHexChar_hexCharToNibble_some {c : Char} (h : isHexChar c = true) :
    ∃ n, Internal.hexCharToNibble c = some n := by
  have hc := isHexChar_lt_128 h
  have hp := char_nibbleCheck hc
  cases h1 : Internal.hexCharToNibble c with
  | none => simp [nibbleCheck, h1, h] at hp
  | some n => exact ⟨n, rfl⟩

private theorem fin16_byteToHexChars :
    ∀ h l : Fin 16,
      Internal.byteToHexChars (UInt8.ofNat (h.1 * 16 + l.1)) =
        [Internal.lowerHexDigit h.1, Internal.lowerHexDigit l.1] := by
  decide

private theorem hexCharsToByte_byteToHexChars {hi lo : Char} {b : UInt8}
    (h : Internal.hexCharsToByte hi lo = some b) :
    Internal.byteToHexChars b = [Char.toLower hi, Char.toLower lo] := by
  unfold Internal.hexCharsToByte at h
  cases h1 : Internal.hexCharToNibble hi with
  | none => simp [h1] at h
  | some nh =>
    cases h2 : Internal.hexCharToNibble lo with
    | none => simp [h1, h2] at h
    | some nl =>
      simp only [h1, h2, Option.some.injEq] at h
      subst h
      obtain ⟨hh1, hh2⟩ := hexCharToNibble_some_props h1
      obtain ⟨hl1, hl2⟩ := hexCharToNibble_some_props h2
      have hb := fin16_byteToHexChars ⟨nh.toNat, hh1⟩ ⟨nl.toNat, hl1⟩
      simpa [hh2, hl2] using hb

private theorem fin16_badVer_bits :
    ∀ nh nl : Fin 16, nh.1 ≠ 4 →
      (UInt8.ofNat (nh.1 * 16 + nl.1) &&& 0xF0) ≠ 0x40 := by
  decide

private theorem fin16_badVar_bits :
    ∀ nh nl : Fin 16, ¬(8 ≤ nh.1 ∧ nh.1 ≤ 11) →
      (UInt8.ofNat (nh.1 * 16 + nl.1) &&& 0xC0) ≠ 0x80 := by
  decide

private theorem hexCharsToByte_badVer {hi lo : Char} {b : UInt8}
    (hne : hi ≠ '4')
    (h : Internal.hexCharsToByte hi lo = some b) :
    (b &&& 0xF0) ≠ 0x40 := by
  unfold Internal.hexCharsToByte at h
  cases h1 : Internal.hexCharToNibble hi with
  | none => simp [h1] at h
  | some nh =>
    cases h2 : Internal.hexCharToNibble lo with
    | none => simp [h1, h2] at h
    | some nl =>
      simp only [h1, h2, Option.some.injEq] at h
      subst h
      have hc := hexCharToNibble_lt_128 h1
      have hp := char_nibbleCheck hc
      simp only [nibbleCheck, h1, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        bne_iff_ne, decide_eq_true_eq] at hp
      have hnh4 : nh.toNat ≠ 4 := by
        rcases hp.1.2 with rfl | hne4
        · exact absurd rfl hne
        · exact hne4
      obtain ⟨hl1, _⟩ := hexCharToNibble_some_props h2
      exact fin16_badVer_bits ⟨nh.toNat, hp.1.1.1.2⟩ ⟨nl.toNat, hl1⟩ hnh4

private theorem hexCharsToByte_badVar {hi lo : Char} {b : UInt8}
    (h8 : hi ≠ '8') (h9 : hi ≠ '9') (ha : hi ≠ 'a') (hb : hi ≠ 'b') (hA : hi ≠ 'A') (hB : hi ≠ 'B')
    (h : Internal.hexCharsToByte hi lo = some b) :
    (b &&& 0xC0) ≠ 0x80 := by
  unfold Internal.hexCharsToByte at h
  cases h1 : Internal.hexCharToNibble hi with
  | none => simp [h1] at h
  | some nh =>
    cases h2 : Internal.hexCharToNibble lo with
    | none => simp [h1, h2] at h
    | some nl =>
      simp only [h1, h2, Option.some.injEq] at h
      subst h
      have hc := hexCharToNibble_lt_128 h1
      have hp := char_nibbleCheck hc
      simp only [nibbleCheck, h1, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq, decide_eq_true_eq] at hp
      have hnot : ¬(8 ≤ nh.toNat ∧ nh.toNat ≤ 11) := by
        rcases hp.2 with (((((h'|h')|h')|h')|h')|h')|h'
        · exact absurd h' h8
        · exact absurd h' h9
        · exact absurd h' ha
        · exact absurd h' hb
        · exact absurd h' hA
        · exact absurd h' hB
        · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h'
          omega
      obtain ⟨hl1, _⟩ := hexCharToNibble_some_props h2
      exact fin16_badVar_bits ⟨nh.toNat, hp.1.1.1.2⟩ ⟨nl.toNat, hl1⟩ hnot

private theorem decodeHexPairs_formatHexList :
    ∀ (cs : List Char) (bs : List UInt8),
      Internal.decodeHexPairs cs = some bs →
      Internal.formatHexList bs = cs.map Char.toLower := by
  intro cs
  match cs with
  | [] =>
    intro bs h
    simp [Internal.decodeHexPairs] at h
    subst h
    rfl
  | [c] =>
    intro bs h
    simp [Internal.decodeHexPairs] at h
  | hi :: lo :: rest =>
    intro bs h
    unfold Internal.decodeHexPairs at h
    cases hb : Internal.hexCharsToByte hi lo with
    | none => simp [hb] at h
    | some b =>
      cases hr : Internal.decodeHexPairs rest with
      | none => simp [hb, hr] at h
      | some bs' =>
        simp only [hb, hr, Option.some.injEq] at h
        subst h
        have hhead := hexCharsToByte_byteToHexChars hb
        have htail := decodeHexPairs_formatHexList rest bs' hr
        unfold Internal.formatHexList at htail ⊢
        simp [List.flatMap_cons, hhead, htail]

private theorem decodeHexPairs_none_of_mem_bad :
    ∀ (cs : List Char) (c : Char), c ∈ cs → isHexChar c = false →
      Internal.decodeHexPairs cs = none := by
  intro cs
  match cs with
  | [] => intro c hc _; cases hc
  | [a] => intro _ _ _; rfl
  | hi :: lo :: rest =>
    intro c hc hbad
    unfold Internal.decodeHexPairs
    rcases List.mem_cons.mp hc with rfl | hrest
    · have hn : Internal.hexCharToNibble c = none := hexCharToNibble_isHex hbad
      simp [Internal.hexCharsToByte, hn]
    · rcases List.mem_cons.mp hrest with rfl | htail
      · have hn : Internal.hexCharToNibble c = none := hexCharToNibble_isHex hbad
        cases Internal.hexCharToNibble hi <;> simp [Internal.hexCharsToByte, hn]
      · have hr := decodeHexPairs_none_of_mem_bad rest c htail hbad
        simp [hr]

private theorem nonEmptyMsg_ne_empty {fallback msg : String} (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  by_cases h : msg.isEmpty
  · simp [h, hf]
  · simp [h]
    intro heq
    subst heq
    exact h rfl

private theorem fromRandomBytes16_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    Internal.fromRandomBytes (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
        (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15] } := rfl

private theorem toString16_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    Internal.toString { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } =
      String.ofList (Internal.insertHyphens (Internal.formatHexList
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])) := rfl

private theorem toHex16_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    Internal.toHex { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } =
      String.ofList (Internal.formatHexList
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) := rfl

/-- Proof of `test_uuid_mapRawError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_uuid_mapRawError_returnsNonEmptyMessage :
    AllPass (test_uuid_mapRawError_returnsNonEmptyMessage defaultApi) := by
  intro raw
  cases raw with
  | osError code detail =>
    dsimp [test_uuid_mapRawError_returnsNonEmptyMessage, defaultApi, Internal.mkApi,
      Internal.mkApi, Internal.mkApiM, Internal.mapRawError, Bind.bind, Core.NondetTest.assert]
    refine ⟨⟨rfl, nonEmptyMsg_ne_empty ?_⟩, rfl, trivial⟩
    intro h
    have hlen := congrArg String.length h
    simp at hlen
    exact absurd hlen.1 (by decide)
  | shortRead gotBytes detail =>
    dsimp [test_uuid_mapRawError_returnsNonEmptyMessage, defaultApi, Internal.mkApi,
      Internal.mkApi, Internal.mkApiM, Internal.mapRawError, Bind.bind, Core.NondetTest.assert]
    refine ⟨⟨rfl, nonEmptyMsg_ne_empty ?_⟩, rfl, trivial⟩
    intro h
    have hlen := congrArg String.length h
    simp at hlen
  | userError detail =>
    dsimp [test_uuid_mapRawError_returnsNonEmptyMessage, defaultApi, Internal.mkApi,
      Internal.mkApi, Internal.mkApiM, Internal.mapRawError, Bind.bind, Core.NondetTest.assert]
    refine ⟨⟨rfl, nonEmptyMsg_ne_empty (by decide)⟩, rfl, trivial⟩

/-- Proof of `test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload` for `defaultApi`. -/
theorem proof_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload :
    AllPass (test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload defaultApi) := by
  intro bs hlen
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    eq_of_size_16 bs hlen
  dsimp [test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload, defaultApi,
    Internal.mkApi, Internal.mkApiM, Bind.bind, Core.NondetTest.assert]
  rw [fromRandomBytes16_eq]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact uint8_v4_ver b6
  · exact uint8_v4_var b8
  · exact uint8_v4_ver_low b6
  · exact uint8_v4_var_low b8
  · intro i ⟨hi, hi6, hi8⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 7 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨rfl, trivial⟩

/-- Non-vacuity witness for `test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload`. -/
theorem reach_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload :
    CanReach (test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload defaultApi) := by
  have h := proof_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload
    (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) rfl
  dsimp [test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload, defaultApi,
    Internal.mkApi, Internal.mkApiM, Bind.bind, Core.NondetTest.assert] at h ⊢
  exact ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl,
    h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, 0, by decide, h.2.2.2.2.2 0 (by decide)⟩

/-- Proof of `test_uuid_fromRandomBytes_invalidLen_returnsError` for `defaultApi`. -/
theorem proof_uuid_fromRandomBytes_invalidLen_returnsError :
    AllPass (test_uuid_fromRandomBytes_invalidLen_returnsError defaultApi) := by
  intro bs hne
  dsimp [test_uuid_fromRandomBytes_invalidLen_returnsError, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.fromRandomBytes, Bind.bind, Core.NondetTest.assert]
  have hbne : (bs.size != 16) = true := bne_iff_ne.mpr hne
  rw [hbne]
  refine ⟨⟨rfl, ?_⟩, trivial⟩
  intro h
  have hlen := congrArg String.length h
  simp at hlen

/-- Non-vacuity witness for `test_uuid_fromRandomBytes_invalidLen_returnsError`. -/
theorem reach_uuid_fromRandomBytes_invalidLen_returnsError :
    CanReach (test_uuid_fromRandomBytes_invalidLen_returnsError defaultApi) := by
  refine ⟨ByteArray.empty, by decide, ?_⟩
  dsimp [test_uuid_fromRandomBytes_invalidLen_returnsError, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.fromRandomBytes, Bind.bind, Core.NondetTest.assert]
  exact ⟨⟨rfl, by decide⟩, trivial⟩

private theorem decodeHexPairs_cons (hi lo : Char) (rest : List Char) {b : UInt8}
    (hb : Internal.hexCharsToByte hi lo = some b) :
    Internal.decodeHexPairs (hi :: lo :: rest) = (Internal.decodeHexPairs rest).map (b :: ·) := by
  cases hd : Internal.decodeHexPairs rest with
  | none =>
    change (match Internal.hexCharsToByte hi lo, Internal.decodeHexPairs rest with
      | some b, some bs => some (b :: bs)
      | _, _ => none) = none
    rw [hb, hd]
  | some bs =>
    change (match Internal.hexCharsToByte hi lo, Internal.decodeHexPairs rest with
      | some b, some bs => some (b :: bs)
      | _, _ => none) = some (b :: bs)
    rw [hb, hd]

private theorem decodeHexPairs_byte_cons (x : UInt8) (rest : List Char) :
    Internal.decodeHexPairs
      (Internal.lowerHexDigit (x.toNat / 16) :: Internal.lowerHexDigit (x.toNat % 16) :: rest) =
      (Internal.decodeHexPairs rest).map (x :: ·) :=
  decodeHexPairs_cons _ _ rest (uint8_hex_roundtrip x)

private theorem decodeHexPairs_byte_upper_cons (x : UInt8) (rest : List Char) :
    Internal.decodeHexPairs
      (Char.toUpper (Internal.lowerHexDigit (x.toNat / 16)) ::
        Char.toUpper (Internal.lowerHexDigit (x.toNat % 16)) :: rest) =
      (Internal.decodeHexPairs rest).map (x :: ·) :=
  decodeHexPairs_cons _ _ rest (uint8_hex_upper_roundtrip x)

private theorem decodeHexPairs16_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    Internal.decodeHexPairs (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      some [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  simp only [Internal.formatHexList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Internal.byteToHexChars, List.cons_append, List.nil_append]
  repeat rw [decodeHexPairs_byte_cons]
  rfl

private theorem decodeHexPairs16_upper_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    Internal.decodeHexPairs ((Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).map Char.toUpper) =
      some [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  simp only [Internal.formatHexList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Internal.byteToHexChars, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  repeat rw [decodeHexPairs_byte_upper_cons]
  rfl

private theorem append_ne_empty_of_left {a b : String} (hl : 0 < a.length) : a ++ b ≠ "" := by
  intro h
  have hs := congrArg String.length h
  rw [String.length_append] at hs
  have h0 : ("" : String).length = 0 := rfl
  omega

private theorem mkByteArray16_eq
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    ByteArray.mk ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15].toArray) =
      ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] :=
  rfl

private theorem validateV4BytesList16
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    (hv6 : (b6 &&& 0xF0) = 0x40) (hv8 : (b8 &&& 0xC0) = 0x80) :
    Internal.validateV4BytesList [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } := by
  unfold Internal.validateV4BytesList
  rw [mkByteArray16_eq]
  have hsz : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).size = 16 := rfl
  have h6 : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])[6]! = b6 := rfl
  have h8 : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])[8]! = b8 := rfl
  simp only [hsz, h6, h8, hv6, hv8, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

private theorem parseHexChars16_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    (hv6 : (b6 &&& 0xF0) = 0x40) (hv8 : (b8 &&& 0xC0) = 0x80) :
    Internal.parseHexChars (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } := by
  have hlen : (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).length = 32 := by
    simp [Internal.formatHexList, Internal.byteToHexChars]
  rw [Internal.parseHexChars]
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, decodeHexPairs16_bytes]
  exact validateV4BytesList16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 hv6 hv8

private theorem parseHexChars16_upper_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    (hv6 : (b6 &&& 0xF0) = 0x40) (hv8 : (b8 &&& 0xC0) = 0x80) :
    Internal.parseHexChars ((Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).map Char.toUpper) =
      .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } := by
  have hlen : ((Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).map Char.toUpper).length = 32 := by
    simp [Internal.formatHexList, Internal.byteToHexChars]
  rw [Internal.parseHexChars]
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, decodeHexPairs16_upper_bytes]
  exact validateV4BytesList16 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 hv6 hv8

private theorem stripCanonicalHyphens_five (a b c d e : List Char)
    (ha : a.length = 8) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4) (he : e.length = 12) :
    Internal.stripCanonicalHyphens (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e) =
      some (a ++ b ++ c ++ d ++ e) := by
  unfold Internal.stripCanonicalHyphens
  have hlen : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).length = 36 := by
    simp [ha, hb, hc, hd, he]
  have h8 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e)[8]? = some '-' := by
    simp only [List.append_assoc]
    rw [List.getElem?_append_right (by omega)]
    simp [ha]
  have h13 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e)[13]? = some '-' := by
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b) ++ ('-' :: (c ++ ['-'] ++ d ++ ['-'] ++ e)) := by
      simp [List.append_assoc]
    rw [hsplit, List.getElem?_append_right (by simp [ha, hb])]
    simp [ha, hb]
  have h18 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e)[18]? = some '-' := by
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-'] ++ c) ++ ('-' :: (d ++ ['-'] ++ e)) := by
      simp [List.append_assoc]
    rw [hsplit, List.getElem?_append_right (by simp [ha, hb, hc])]
    simp [ha, hb, hc]
  have h23 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e)[23]? = some '-' := by
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d) ++ ('-' :: e) := by
      simp [List.append_assoc]
    rw [hsplit, List.getElem?_append_right (by simp [ha, hb, hc, hd])]
    simp [ha, hb, hc, hd]
  have ht0 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).take 8 = a := by
    simp only [List.append_assoc]
    exact List.take_left' ha
  have ht1 : ((a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).drop 9).take 4 = b := by
    have hpre : (a ++ ['-']).length = 9 := by simp [ha]
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-']) ++ (b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e) := by
      simp [List.append_assoc]
    rw [hsplit, List.drop_left' hpre]
    simp only [List.append_assoc]
    exact List.take_left' hb
  have ht2 : ((a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).drop 14).take 4 = c := by
    have hpre : (a ++ ['-'] ++ b ++ ['-']).length = 14 := by simp [ha, hb]
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-']) ++ (c ++ ['-'] ++ d ++ ['-'] ++ e) := by
      simp [List.append_assoc]
    rw [hsplit, List.drop_left' hpre]
    simp only [List.append_assoc]
    exact List.take_left' hc
  have ht3 : ((a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).drop 19).take 4 = d := by
    have hpre : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-']).length = 19 := by simp [ha, hb, hc]
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-']) ++ (d ++ ['-'] ++ e) := by
      simp [List.append_assoc]
    rw [hsplit, List.drop_left' hpre]
    simp only [List.append_assoc]
    exact List.take_left' hd
  have ht4 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).drop 24 = e := by
    have hpre : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-']).length = 24 := by
      simp [ha, hb, hc, hd]
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-']) ++ e := rfl
    rw [hsplit, List.drop_left' hpre]
  simp only [hlen, h8, h13, h18, h23, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, ht0, ht1, ht2, ht3, ht4]

private theorem stripCanonicalHyphens_insertHyphens_len {l : List Char} (hl : l.length = 32) :
    Internal.stripCanonicalHyphens (Internal.insertHyphens l) = some l := by
  let a := l.take 8
  let b := (l.drop 8).take 4
  let c := (l.drop 12).take 4
  let d := (l.drop 16).take 4
  let e := l.drop 20
  have ha : a.length = 8 := by simp [a, hl]
  have hb : b.length = 4 := by simp [b, hl]
  have hc : c.length = 4 := by simp [c, hl]
  have hd : d.length = 4 := by simp [d, hl]
  have he : e.length = 12 := by simp [e, hl]
  have hins : Internal.insertHyphens l = a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e := by
    unfold Internal.insertHyphens
    simp only [a, b, c, d, e, List.append_assoc]
  have hsum : a ++ b ++ c ++ d ++ e = l := by
    dsimp only [a, b, c, d, e]
    rw [List.append_assoc (l.take 8), List.append_assoc (l.take 8), List.append_assoc (l.take 8)]
    rw [List.append_assoc ((l.drop 8).take 4), List.append_assoc ((l.drop 8).take 4)]
    rw [List.append_assoc ((l.drop 12).take 4)]
    have hd1 : (l.drop 16).drop 4 = l.drop 20 := List.drop_drop
    have hd2 : (l.drop 12).drop 4 = l.drop 16 := List.drop_drop
    have hd3 : (l.drop 8).drop 4 = l.drop 12 := List.drop_drop
    rw [← hd1, List.take_append_drop, ← hd2, List.take_append_drop, ← hd3, List.take_append_drop]
    exact List.take_append_drop 8 l
  rw [hins, stripCanonicalHyphens_five a b c d e ha hb hc hd he, hsum]

private theorem parseCanonicalChars16_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    (hv6 : (b6 &&& 0xF0) = 0x40) (hv8 : (b8 &&& 0xC0) = 0x80) :
    Internal.parseCanonicalChars (Internal.insertHyphens (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])) =
      .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } := by
  have hl : (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]).length = 32 := by
    simp [Internal.formatHexList, Internal.byteToHexChars]
  have hlen36 : (Internal.insertHyphens (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])).length = 36 := by
    unfold Internal.insertHyphens
    simp [hl]
  rw [Internal.parseCanonicalChars]
  simp only [hlen36, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    stripCanonicalHyphens_insertHyphens_len hl]
  exact parseHexChars16_bytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 hv6 hv8

private theorem parseCanonicalChars16_upper_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    (hv6 : (b6 &&& 0xF0) = 0x40) (hv8 : (b8 &&& 0xC0) = 0x80) :
    Internal.parseCanonicalChars ((Internal.insertHyphens (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])).map Char.toUpper) =
      .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } := by
  let l := Internal.formatHexList
    [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]
  have hl : l.length = 32 := by
    simp [l, Internal.formatHexList, Internal.byteToHexChars]
  have hmap : (Internal.insertHyphens l).map Char.toUpper =
      Internal.insertHyphens (l.map Char.toUpper) := by
    unfold Internal.insertHyphens
    have hdash : ('-' : Char).toUpper = '-' := rfl
    simp only [List.map_append, List.map_cons, List.map_nil, hdash, List.map_take, List.map_drop]
  have hlu : (l.map Char.toUpper).length = 32 := by simp [hl]
  have hlen36 : (Internal.insertHyphens (l.map Char.toUpper)).length = 36 := by
    unfold Internal.insertHyphens
    simp [hlu]
  rw [hmap, Internal.parseCanonicalChars]
  simp only [hlen36, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    stripCanonicalHyphens_insertHyphens_len hlu]
  exact parseHexChars16_upper_bytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 hv6 hv8

private theorem lowerHexDigit_isLowerHexChar (n : Nat) (hn : n < 16) :
    isLowerHexChar (Internal.lowerHexDigit n) = true :=
  pred_lowerHexDigit isLowerHexChar (by decide) n hn

private theorem formatHexList_all_lowerHexChar (bs : List UInt8) :
    (Internal.formatHexList bs).all isLowerHexChar = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [Internal.formatHexList, List.mem_flatMap, Internal.byteToHexChars,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ⟨b, _, rfl | rfl⟩
  · exact lowerHexDigit_isLowerHexChar _ (uint8_nibble_bounds b).1
  · exact lowerHexDigit_isLowerHexChar _ (uint8_nibble_bounds b).2

private theorem insertHyphens_all_lowerHexOrDash (l : List Char)
    (hl : l.all isLowerHexChar = true) :
    (Internal.insertHyphens l).all (fun c => c == '-' || isLowerHexChar c) = true := by
  rw [List.all_eq_true] at hl ⊢
  intro c hc
  unfold Internal.insertHyphens at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (((((((hc | rfl) | hc) | rfl) | hc) | rfl) | hc) | rfl) | hc
  · simp [hl c (List.mem_of_mem_take hc)]
  · simp
  · simp [hl c (List.mem_of_mem_drop (List.mem_of_mem_take hc))]
  · simp
  · simp [hl c (List.mem_of_mem_drop (List.mem_of_mem_take hc))]
  · simp
  · simp [hl c (List.mem_of_mem_drop (List.mem_of_mem_take hc))]
  · simp
  · simp [hl c (List.mem_of_mem_drop hc)]

private theorem insertHyphens_filter_dash (l : List Char)
    (hl : l.all isLowerHexChar = true) :
    (Internal.insertHyphens l).filter (fun c => c != '-') = l := by
  have hnd : ∀ c, isLowerHexChar c = true → (c != '-') = true := by
    intro c hc
    by_cases h : c = '-'
    · subst h; cases hc
    · simp [h]
  have hall : l.all (fun c => c != '-') = true :=
    List.all_eq_true.mpr (fun c hc => hnd c (List.all_eq_true.mp hl c hc))
  have hf_drop_take : ∀ {n m : Nat} {xs : List Char}, xs.all (fun c => c != '-') = true →
      ((xs.drop n).take m).filter (fun c => c != '-') = (xs.drop n).take m := by
    intro n m xs hxs
    rw [List.filter_eq_self]
    intro c hc
    exact List.all_eq_true.mp hxs c (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  have hf_take : ∀ {n : Nat} {xs : List Char}, xs.all (fun c => c != '-') = true →
      (xs.take n).filter (fun c => c != '-') = xs.take n := by
    intro n xs hxs
    rw [List.filter_eq_self]
    intro c hc
    exact List.all_eq_true.mp hxs c (List.mem_of_mem_take hc)
  have hf_drop : ∀ {n : Nat} {xs : List Char}, xs.all (fun c => c != '-') = true →
      (xs.drop n).filter (fun c => c != '-') = xs.drop n := by
    intro n xs hxs
    rw [List.filter_eq_self]
    intro c hc
    exact List.all_eq_true.mp hxs c (List.mem_of_mem_drop hc)
  unfold Internal.insertHyphens
  simp only [List.filter_append, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, List.append_nil, hf_take hall, hf_drop_take hall, hf_drop hall]
  rw [List.append_assoc (l.take 8), List.append_assoc (l.take 8), List.append_assoc (l.take 8)]
  rw [List.append_assoc ((l.drop 8).take 4), List.append_assoc ((l.drop 8).take 4)]
  rw [List.append_assoc ((l.drop 12).take 4)]
  have hd1 : (l.drop 16).drop 4 = l.drop 20 := List.drop_drop
  have hd2 : (l.drop 12).drop 4 = l.drop 16 := List.drop_drop
  have hd3 : (l.drop 8).drop 4 = l.drop 12 := List.drop_drop
  rw [← hd1, List.take_append_drop, ← hd2, List.take_append_drop, ← hd3, List.take_append_drop]
  exact List.take_append_drop 8 l

/-- Proof of `test_uuid_toString_formatAndRoundTrip` for `defaultApi`. -/
theorem proof_uuid_toString_formatAndRoundTrip :
    AllPass (test_uuid_toString_formatAndRoundTrip defaultApi) := by
  intro bs hlen
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    eq_of_size_16 bs hlen
  dsimp [test_uuid_toString_formatAndRoundTrip, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parse, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  rw [fromRandomBytes16_eq]
  dsimp only
  rw [toString16_eq]
  have hv6 : (((b6 &&& 0x0F) ||| 0x40) &&& 0xF0) = 0x40 := uint8_v4_ver b6
  have hv8 : (((b8 &&& 0x3F) ||| 0x80) &&& 0xC0) = 0x80 := uint8_v4_var b8
  have hparse :
      Internal.parseCanonicalChars
        (Internal.insertHyphens (Internal.formatHexList
          [b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
           (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15])) =
        .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
          (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15] } :=
    parseCanonicalChars16_bytes b0 b1 b2 b3 b4 b5 ((b6 &&& 0x0F) ||| 0x40) b7
      ((b8 &&& 0x3F) ||| 0x80) b9 b10 b11 b12 b13 b14 b15 hv6 hv8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rw [← String.length_toList, String.toList_ofList]
    rfl
  · rw [String.toList_ofList]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [String.toList_ofList]
    exact insertHyphens_all_lowerHexOrDash _ (formatHexList_all_lowerHexChar _)
  · rw [String.toList_ofList]
    simp [Internal.insertHyphens, Internal.formatHexList, Internal.byteToHexChars]
    exact uint8_ver_nibble_char b6
  · rw [String.toList_ofList]
    simp [Internal.insertHyphens, Internal.formatHexList, Internal.byteToHexChars]
    exact uint8_var_nibble_char b8
  · rw [String.toList_ofList]
    exact hparse
  · rw [String.toList_ofList, hparse]
    rfl

/-- Non-vacuity witness for `test_uuid_toString_formatAndRoundTrip`. -/
theorem reach_uuid_toString_formatAndRoundTrip :
    CanReach (test_uuid_toString_formatAndRoundTrip defaultApi) :=
  ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl,
    proof_uuid_toString_formatAndRoundTrip
      (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) rfl⟩

/-- Proof of `test_uuid_toHex_formatAndRoundTrip` for `defaultApi`. -/
theorem proof_uuid_toHex_formatAndRoundTrip :
    AllPass (test_uuid_toHex_formatAndRoundTrip defaultApi) := by
  intro bs hlen
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    eq_of_size_16 bs hlen
  dsimp [test_uuid_toHex_formatAndRoundTrip, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parseHex, Internal.parse, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  rw [fromRandomBytes16_eq]
  dsimp only
  rw [toHex16_eq, toString16_eq]
  have hv6 : (((b6 &&& 0x0F) ||| 0x40) &&& 0xF0) = 0x40 := uint8_v4_ver b6
  have hv8 : (((b8 &&& 0x3F) ||| 0x80) &&& 0xC0) = 0x80 := uint8_v4_var b8
  have hparseHex :
      Internal.parseHexChars
        (String.ofList (Internal.formatHexList
          [b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
           (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15])).toList =
        .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
          (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15] } := by
    rw [String.toList_ofList]
    exact parseHexChars16_bytes b0 b1 b2 b3 b4 b5 ((b6 &&& 0x0F) ||| 0x40) b7
      ((b8 &&& 0x3F) ||| 0x80) b9 b10 b11 b12 b13 b14 b15 hv6 hv8
  have hparseCan :
      Internal.parseCanonicalChars
        (Internal.formatHexList
          [b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
           (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15]) =
        .error { kind := .invalidFormat,
                 message := ToString.toString "expected 36 characters for canonical UUID, got " ++
                   ToString.toString (32 : Nat) } := by
    unfold Internal.parseCanonicalChars
    have hlen32 : (Internal.formatHexList
        [b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
         (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15]).length = 32 := by
      simp [Internal.formatHexList, Internal.byteToHexChars]
    simp [hlen32]
  refine ⟨?_, ?_, ?_, hparseHex, ?_, ?_⟩
  · rw [← String.length_toList, String.toList_ofList]
    rfl
  · rw [String.toList_ofList]
    exact formatHexList_all_lowerHexChar _
  · rw [String.toList_ofList, String.toList_ofList]
    exact (insertHyphens_filter_dash _ (formatHexList_all_lowerHexChar _)).symm
  · rw [String.toList_ofList, hparseCan]
    rfl
  · rw [String.toList_ofList, hparseCan]
    exact ⟨⟨rfl, append_ne_empty_of_left (by decide)⟩, trivial⟩

/-- Non-vacuity witness for `test_uuid_toHex_formatAndRoundTrip`. -/
theorem reach_uuid_toHex_formatAndRoundTrip :
    CanReach (test_uuid_toHex_formatAndRoundTrip defaultApi) :=
  ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl,
    proof_uuid_toHex_formatAndRoundTrip
      (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) rfl⟩

/-- Proof of `test_uuid_toHex_bigEndianNibbleOrder` for `defaultApi`. -/
theorem proof_uuid_toHex_bigEndianNibbleOrder :
    AllPass (test_uuid_toHex_bigEndianNibbleOrder defaultApi) := by
  intro bs hlen
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    eq_of_size_16 bs hlen
  dsimp [test_uuid_toHex_bigEndianNibbleOrder, defaultApi, Internal.mkApi, Internal.mkApiM,
    Bind.bind, Core.NondetTest.assert]
  rw [fromRandomBytes16_eq]
  dsimp only
  intro i hi
  rw [toHex16_eq, String.toList_ofList]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Internal.formatHexList, Internal.byteToHexChars, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.cons_append, List.nil_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd]
    exact ⟨rfl, rfl, trivial⟩

/-- Non-vacuity witness for `test_uuid_toHex_bigEndianNibbleOrder`. -/
theorem reach_uuid_toHex_bigEndianNibbleOrder :
    CanReach (test_uuid_toHex_bigEndianNibbleOrder defaultApi) := by
  have h := proof_uuid_toHex_bigEndianNibbleOrder
    (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) rfl 0 (by decide)
  dsimp [test_uuid_toHex_bigEndianNibbleOrder, defaultApi, Internal.mkApi, Internal.mkApiM,
    Bind.bind, Core.NondetTest.assert] at h ⊢
  exact ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl, 0, by decide, h⟩

/-- Proof of `test_uuid_parse_acceptsUppercaseHex` for `defaultApi`. -/
theorem proof_uuid_parse_acceptsUppercaseHex :
    AllPass (test_uuid_parse_acceptsUppercaseHex defaultApi) := by
  intro bs hlen
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    eq_of_size_16 bs hlen
  dsimp [test_uuid_parse_acceptsUppercaseHex, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parse, Internal.parseHex, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  rw [fromRandomBytes16_eq]
  dsimp only
  rw [toString16_eq, toHex16_eq]
  have hv6 : (((b6 &&& 0x0F) ||| 0x40) &&& 0xF0) = 0x40 := uint8_v4_ver b6
  have hv8 : (((b8 &&& 0x3F) ||| 0x80) &&& 0xC0) = 0x80 := uint8_v4_var b8
  have hparseStr :
      Internal.parseCanonicalChars
        ((Internal.insertHyphens (Internal.formatHexList
          [b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
           (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15])).map Char.toUpper) =
        .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
          (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15] } :=
    parseCanonicalChars16_upper_bytes b0 b1 b2 b3 b4 b5 ((b6 &&& 0x0F) ||| 0x40) b7
      ((b8 &&& 0x3F) ||| 0x80) b9 b10 b11 b12 b13 b14 b15 hv6 hv8
  have hparseHex :
      Internal.parseHexChars
        ((Internal.formatHexList
          [b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
           (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15]).map Char.toUpper) =
        .ok { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, (b6 &&& 0x0F) ||| 0x40, b7,
          (b8 &&& 0x3F) ||| 0x80, b9, b10, b11, b12, b13, b14, b15] } :=
    parseHexChars16_upper_bytes b0 b1 b2 b3 b4 b5 ((b6 &&& 0x0F) ||| 0x40) b7
      ((b8 &&& 0x3F) ||| 0x80) b9 b10 b11 b12 b13 b14 b15 hv6 hv8
  refine ⟨?_, ?_, ?_, trivial⟩
  · rw [String.toList_ofList, String.toList_ofList]
    exact hparseStr
  · rw [String.toList_ofList, String.toList_ofList, hparseStr]
    rfl
  · rw [String.toList_ofList, String.toList_ofList]
    exact hparseHex

/-- Non-vacuity witness for `test_uuid_parse_acceptsUppercaseHex`. -/
theorem reach_uuid_parse_acceptsUppercaseHex :
    CanReach (test_uuid_parse_acceptsUppercaseHex defaultApi) := by
  have h := proof_uuid_parse_acceptsUppercaseHex
    (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) rfl
  dsimp [test_uuid_parse_acceptsUppercaseHex, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parse, Internal.parseHex, Internal.isValid, Bind.bind, Core.NondetTest.assert] at h ⊢
  exact ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl, h⟩

private theorem insertHyphens_five (a b c d e : List Char)
    (ha : a.length = 8) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4) :
    Internal.insertHyphens (a ++ b ++ c ++ d ++ e) =
      a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e := by
  unfold Internal.insertHyphens
  have hab : (a ++ b).length = 12 := by simp [ha, hb]
  have habc : (a ++ b ++ c).length = 16 := by simp [ha, hb, hc]
  have habcd : (a ++ b ++ c ++ d).length = 20 := by simp [ha, hb, hc, hd]
  have h0 : (a ++ (b ++ c ++ d ++ e)).take 8 = a := List.take_left' ha
  have h1 : ((a ++ (b ++ c ++ d ++ e)).drop 8).take 4 = b := by
    rw [List.drop_left' ha, List.append_assoc b, List.append_assoc b]
    exact List.take_left' hb
  have h2 : (((a ++ b) ++ (c ++ d ++ e)).drop 12).take 4 = c := by
    rw [List.drop_left' hab, List.append_assoc c]
    exact List.take_left' hc
  have h3 : (((a ++ b ++ c) ++ (d ++ e)).drop 16).take 4 = d := by
    rw [List.drop_left' habc]
    exact List.take_left' hd
  have h4 : ((a ++ b ++ c ++ d) ++ e).drop 20 = e := List.drop_left' habcd
  simp only [List.append_assoc] at h0 h1 h2 h3 h4 ⊢
  rw [h0, h1, h2, h3, h4]

private theorem list_split_idx {α : Type} (l : List α) (k : Nat) (hk : k < l.length) :
    l = l.take k ++ l[k] :: l.drop (k + 1) := by
  have h1 : l.take k ++ l.drop k = l := List.take_append_drop k l
  have h2 : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hk
  rw [h2] at h1
  exact h1.symm

private theorem stripCanonicalHyphens_insertHyphens {cs hex : List Char}
    (h : Internal.stripCanonicalHyphens cs = some hex) :
    Internal.insertHyphens (hex.map Char.toLower) = cs.map Char.toLower := by
  unfold Internal.stripCanonicalHyphens at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hlen hhy
      simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, not_or, Decidable.not_not] at hlen hhy
      obtain ⟨⟨⟨h8, h13⟩, h18⟩, h23⟩ := hhy
      simp only [Option.some.injEq] at h
      subst h
      have hg8 : cs[8] = '-' := Option.some.inj (List.getElem?_eq_getElem (by omega : 8 < cs.length) ▸ h8)
      have hg13 : cs[13] = '-' := Option.some.inj (List.getElem?_eq_getElem (by omega : 13 < cs.length) ▸ h13)
      have hg18 : cs[18] = '-' := Option.some.inj (List.getElem?_eq_getElem (by omega : 18 < cs.length) ▸ h18)
      have hg23 : cs[23] = '-' := Option.some.inj (List.getElem?_eq_getElem (by omega : 23 < cs.length) ▸ h23)
      have ha : ((cs.take 8).map Char.toLower).length = 8 := by simp [hlen]
      have hb : (((cs.drop 9).take 4).map Char.toLower).length = 4 := by simp [hlen]
      have hc : (((cs.drop 14).take 4).map Char.toLower).length = 4 := by simp [hlen]
      have hd : (((cs.drop 19).take 4).map Char.toLower).length = 4 := by simp [hlen]
      simp only [List.map_append]
      rw [insertHyphens_five _ _ _ _ _ ha hb hc hd]
      have s8 := list_split_idx cs 8 (by omega)
      have s13 := list_split_idx (cs.drop 9) 4 (by simp [hlen])
      have s18 := list_split_idx (cs.drop 14) 4 (by simp [hlen])
      have s23 := list_split_idx (cs.drop 19) 4 (by simp [hlen])
      simp only [List.getElem_drop, List.drop_drop] at s13 s18 s23
      have hg13' : cs[9 + 4] = '-' := hg13
      have hg18' : cs[14 + 4] = '-' := hg18
      have hg23' : cs[19 + 4] = '-' := hg23
      rw [hg8] at s8
      rw [hg13'] at s13
      rw [hg18'] at s18
      rw [hg23'] at s23
      rw [s23] at s18
      rw [s18] at s13
      rw [s13] at s8
      have hcs : cs = cs.take 8 ++ ['-'] ++ (cs.drop 9).take 4 ++ ['-'] ++
          (cs.drop 14).take 4 ++ ['-'] ++ (cs.drop 19).take 4 ++ ['-'] ++ cs.drop 24 := by
        simpa [List.append_assoc] using s8
      conv => rhs; rw [hcs]
      have hdash : ('-' : Char).toLower = '-' := rfl
      simp only [List.map_append, List.map_cons, List.map_nil, hdash, List.append_assoc]

private theorem parseHexChars_ok_props {cs : List Char} {u : Uuid}
    (h : Internal.parseHexChars cs = .ok u) :
    u.bytes.size = 16 ∧
    (u.bytes[6]! &&& 0xF0) = 0x40 ∧
    (u.bytes[8]! &&& 0xC0) = 0x80 ∧
    Internal.formatHexList u.bytes.data.toList = cs.map Char.toLower := by
  unfold Internal.parseHexChars at h
  by_cases hlen : (cs.length != 32) = true
  · simp [hlen] at h
  · simp only [Bool.not_eq_true] at hlen
    simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h
    cases hd : Internal.decodeHexPairs cs with
    | none => simp [hd] at h
    | some bs =>
      simp only [hd] at h
      unfold Internal.validateV4BytesList at h
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · simp only [Except.ok.injEq] at h
            subst h
            rename_i hsz hv6 hv8
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsz hv6 hv8
            exact ⟨hsz, hv6, hv8, decodeHexPairs_formatHexList cs bs hd⟩

private theorem parseHexChars_err_msg {cs : List Char} {e : UuidError}
    (h : Internal.parseHexChars cs = .error e) : e.message ≠ "" := by
  unfold Internal.parseHexChars at h
  split at h
  · simp only [Except.error.injEq] at h
    subst h
    exact append_ne_empty_of_left (by decide)
  · split at h
    · simp only [Except.error.injEq] at h
      subst h
      decide
    · unfold Internal.validateV4BytesList at h
      dsimp only at h
      split at h
      · simp only [Except.error.injEq] at h
        subst h
        exact append_ne_empty_of_left (by decide)
      · split at h
        · simp only [Except.error.injEq] at h
          subst h
          decide
        · split at h
          · simp only [Except.error.injEq] at h
            subst h
            decide
          · cases h

/-- Proof of `test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip` for `defaultApi`. -/
theorem proof_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip :
    AllPass (test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip defaultApi) := by
  intro s
  dsimp [test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip, defaultApi,
    Internal.mkApi, Internal.mkApiM, Internal.parse, Internal.isValid, Internal.toString,
    Bind.bind, Core.NondetTest.assert]
  cases hp : Internal.parseCanonicalChars s.toList with
  | error e =>
    have hmsg : e.message ≠ "" := by
      unfold Internal.parseCanonicalChars at hp
      split at hp
      · simp only [Except.error.injEq] at hp
        subst hp
        exact append_ne_empty_of_left (by decide)
      · split at hp
        · simp only [Except.error.injEq] at hp
          subst hp
          decide
        · exact parseHexChars_err_msg hp
    simp [hmsg, Except.isOk, Except.toBool]
  | ok u =>
    unfold Internal.parseCanonicalChars at hp
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · rename_i hex hs
        obtain ⟨hsz, hv6, hv8, hfmt⟩ := parseHexChars_ok_props hp
        have hins := stripCanonicalHyphens_insertHyphens hs
        refine ⟨rfl, hsz, hv6, hv8, ?_, trivial⟩
        simp [hsz, String.toList_ofList, hfmt, hins]

/-- Proof of `test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip` for `defaultApi`. -/
theorem proof_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip :
    AllPass (test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip defaultApi) := by
  intro s
  dsimp [test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip, defaultApi,
    Internal.mkApi, Internal.mkApiM, Internal.parseHex, Internal.toHex,
    Bind.bind, Core.NondetTest.assert]
  cases hp : Internal.parseHexChars s.toList with
  | error e => exact ⟨parseHexChars_err_msg hp, trivial⟩
  | ok u =>
    obtain ⟨hsz, hv6, hv8, hfmt⟩ := parseHexChars_ok_props hp
    refine ⟨hsz, hv6, hv8, ?_, trivial⟩
    rw [String.toList_ofList, hfmt]

/-- Proof of `test_uuid_parse_rejectsInvalidLength` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsInvalidLength :
    AllPass (test_uuid_parse_rejectsInvalidLength defaultApi) := by
  intro s hne
  dsimp [test_uuid_parse_rejectsInvalidLength, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parse, Internal.isValid, Internal.parseCanonicalChars,
    Bind.bind, Core.NondetTest.assert]
  have hlen : s.toList.length ≠ 36 := by
    rw [String.length_toList]
    exact hne
  have hbne : (s.toList.length != 36) = true := bne_iff_ne.mpr hlen
  simp only [hbne, ↓reduceIte, Except.isOk, Except.toBool]
  exact ⟨⟨trivial, append_ne_empty_of_left (by decide), trivial⟩, trivial⟩

/-- Non-vacuity witness for `test_uuid_parse_rejectsInvalidLength`. -/
theorem reach_uuid_parse_rejectsInvalidLength :
    CanReach (test_uuid_parse_rejectsInvalidLength defaultApi) := by
  refine ⟨"", by decide, ?_⟩
  exact proof_uuid_parse_rejectsInvalidLength "" (by decide)

private theorem stripCanonicalHyphens_mem_of_idx {cs hex : List Char}
    (hs : Internal.stripCanonicalHyphens cs = some hex)
    {idx : Nat} (hi : idx < 36) (h8 : idx ≠ 8) (h13 : idx ≠ 13) (h18 : idx ≠ 18) (h23 : idx ≠ 23) :
    cs[idx]! ∈ hex := by
  unfold Internal.stripCanonicalHyphens at hs
  split at hs
  · cases hs
  · split at hs
    · cases hs
    · rename_i hlen _
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
      simp only [Option.some.injEq] at hs
      subst hs
      have hidx : idx < cs.length := hlen ▸ hi
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
      dsimp only [Option.getD_some]
      simp only [List.mem_append]
      rcases (by omega : idx < 8 ∨ (9 ≤ idx ∧ idx < 13) ∨ (14 ≤ idx ∧ idx < 18) ∨ (19 ≤ idx ∧ idx < 23) ∨ (24 ≤ idx ∧ idx < 36)) with
        h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left; left; left; left
        exact List.mem_take_iff_getElem.mpr ⟨idx, by simp [hlen]; omega, rfl⟩
      · left; left; left; right
        refine List.mem_take_iff_getElem.mpr ⟨idx - 9, by simp [hlen]; omega, ?_⟩
        simp [List.getElem_drop]; congr 1; omega
      · left; left; right
        refine List.mem_take_iff_getElem.mpr ⟨idx - 14, by simp [hlen]; omega, ?_⟩
        simp [List.getElem_drop]; congr 1; omega
      · left; right
        refine List.mem_take_iff_getElem.mpr ⟨idx - 19, by simp [hlen]; omega, ?_⟩
        simp [List.getElem_drop]; congr 1; omega
      · right
        refine List.mem_drop_iff_getElem.mpr ⟨idx - 24, by simp [hlen]; omega, ?_⟩
        congr 1; omega

/-- Proof of `test_uuid_parse_rejectsNonHexChar` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsNonHexChar :
    AllPass (test_uuid_parse_rejectsNonHexChar defaultApi) := by
  intro s hlen idx ⟨hi, h8, h13, h18, h23⟩ hbad
  dsimp [test_uuid_parse_rejectsNonHexChar, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parse, Internal.isValid, Bind.bind, Core.NondetTest.assert]
  have hclen : s.toList.length = 36 := by rw [String.length_toList]; exact hlen
  have hbne : (s.toList.length != 36) = false := by simp [hclen]
  have hbad' : isHexChar s.toList[idx]! = false := isHexChar_false_of_pred (by decide) hbad
  cases hs : Internal.stripCanonicalHyphens s.toList with
  | none =>
    simp [Internal.parseCanonicalChars, hclen, hs, Except.isOk, Except.toBool]
  | some hex =>
    have hmem := stripCanonicalHyphens_mem_of_idx hs hi h8 h13 h18 h23
    have hdec := decodeHexPairs_none_of_mem_bad hex s.toList[idx]! hmem hbad'
    by_cases hhl : (hex.length != 32) = true
    · simp only [Internal.parseCanonicalChars, hbne, hs, Internal.parseHexChars, hhl, ↓reduceIte,
        Bool.false_eq_true, Except.isOk, Except.toBool]
      exact ⟨⟨trivial, append_ne_empty_of_left (by decide), trivial⟩, trivial⟩
    · simp only [Bool.not_eq_true] at hhl
      simp [Internal.parseCanonicalChars, hclen, hs, Internal.parseHexChars, hhl, hdec,
        Except.isOk, Except.toBool]

/-- Non-vacuity witness for `test_uuid_parse_rejectsNonHexChar`. -/
theorem reach_uuid_parse_rejectsNonHexChar :
    CanReach (test_uuid_parse_rejectsNonHexChar defaultApi) := by
  refine ⟨"g0000000-0000-4000-8000-000000000000", by decide, 0, by decide, by decide, ?_⟩
  exact proof_uuid_parse_rejectsNonHexChar "g0000000-0000-4000-8000-000000000000"
    (by decide) 0 (by decide) (by decide)

/-- Proof of `test_uuid_parse_rejectsMissingHyphen` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsMissingHyphen :
    AllPass (test_uuid_parse_rejectsMissingHyphen defaultApi) := by
  intro s hlen hmiss
  dsimp [test_uuid_parse_rejectsMissingHyphen, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parse, Internal.isValid, Internal.parseCanonicalChars,
    Bind.bind, Core.NondetTest.assert]
  have hclen : s.toList.length = 36 := by rw [String.length_toList]; exact hlen
  have hbne : (s.toList.length != 36) = false := by simp [hclen]
  have hs : Internal.stripCanonicalHyphens s.toList = none := by
    unfold Internal.stripCanonicalHyphens
    rw [hbne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hhy : (s.toList[8]? != some '-' || s.toList[13]? != some '-' ||
        s.toList[18]? != some '-' || s.toList[23]? != some '-') = true := by
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
      rcases hmiss with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    simp [hhy]
  simp [hclen, hs, Except.isOk, Except.toBool]

/-- Non-vacuity witness for `test_uuid_parse_rejectsMissingHyphen`. -/
theorem reach_uuid_parse_rejectsMissingHyphen :
    CanReach (test_uuid_parse_rejectsMissingHyphen defaultApi) := by
  refine ⟨"000000000000040008000000000000000000", by decide, by decide, ?_⟩
  exact proof_uuid_parse_rejectsMissingHyphen "000000000000040008000000000000000000"
    (by decide) (by decide)

private theorem hexCharToNibble_lowerHexDigit_some (n : Nat) (hn : n < 16) :
    ∃ m, Internal.hexCharToNibble (Internal.lowerHexDigit n) = some m := by
  have h : ∀ k : Fin 16, (Internal.hexCharToNibble (Internal.lowerHexDigit k.1)).isSome = true := by
    decide
  exact Option.isSome_iff_exists.mp (h ⟨n, hn⟩)

private theorem hexCharsToByte_isSome_of_hex {hi lo : Char}
    (h1 : isHexChar hi = true) (h2 : ∃ m, Internal.hexCharToNibble lo = some m) :
    ∃ b, Internal.hexCharsToByte hi lo = some b := by
  obtain ⟨nh, hn1⟩ := isHexChar_hexCharToNibble_some h1
  obtain ⟨nl, hn2⟩ := h2
  exact ⟨UInt8.ofNat (nh.toNat * 16 + nl.toNat),
    by unfold Internal.hexCharsToByte; simp [hn1, hn2]⟩

private theorem parseHexChars_badVer
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    {badVer : Char} (hver : isHexChar badVer = true) (hne : badVer ≠ '4') :
    ∃ e, Internal.parseHexChars
      ((Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
        Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
        Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
        [badVer, Internal.lowerHexDigit (b6.toNat % 16)] ++
        Internal.byteToHexChars b7 ++ Internal.byteToHexChars b8 ++
        Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
        Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
        Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
        Internal.byteToHexChars b15)) = .error e ∧
      e.kind = .invalidVersion ∧ e.message ≠ "" := by
  obtain ⟨bv, hbv⟩ := hexCharsToByte_isSome_of_hex hver
    (hexCharToNibble_lowerHexDigit_some (b6.toNat % 16) (uint8_nibble_bounds b6).2)
  have hne40 := hexCharsToByte_badVer hne hbv
  have hne40b : ((bv &&& 0xF0) != 0x40) = true := bne_iff_ne.mpr hne40
  have hlen : ((Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
      Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
      Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
      [badVer, Internal.lowerHexDigit (b6.toNat % 16)] ++
      Internal.byteToHexChars b7 ++ Internal.byteToHexChars b8 ++
      Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
      Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
      Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
      Internal.byteToHexChars b15).length != 32) = false := by
    simp [Internal.byteToHexChars]
  have hdec : Internal.decodeHexPairs
      (Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
       Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
       Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
       [badVer, Internal.lowerHexDigit (b6.toNat % 16)] ++
       Internal.byteToHexChars b7 ++ Internal.byteToHexChars b8 ++
       Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
       Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
       Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
       Internal.byteToHexChars b15) =
      some [b0, b1, b2, b3, b4, b5, bv, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
    simp only [Internal.byteToHexChars, List.cons_append, List.nil_append]
    repeat rw [decodeHexPairs_byte_cons]
    rw [decodeHexPairs_cons _ _ _ hbv]
    repeat rw [decodeHexPairs_byte_cons]
    rfl
  refine ⟨{ kind := .invalidVersion, message := "UUID version nibble must be 4" }, ?_, rfl, by decide⟩
  rw [Internal.parseHexChars, hlen]
  simp only [Bool.false_eq_true, ↓reduceIte, hdec]
  unfold Internal.validateV4BytesList
  rw [mkByteArray16_eq]
  have hsz : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, bv, b7, b8, b9, b10, b11, b12, b13, b14, b15]).size = 16 := rfl
  have h6 : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, bv, b7, b8, b9, b10, b11, b12, b13, b14, b15])[6]! = bv := rfl
  simp only [hsz, h6, hne40b, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

private theorem parseHexChars_badVar
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    (hv6 : (b6 &&& 0xF0) = 0x40)
    {badVar : Char} (hvar : isHexChar badVar = true)
    (h8 : badVar ≠ '8') (h9 : badVar ≠ '9') (ha : badVar ≠ 'a')
    (hb : badVar ≠ 'b') (hA : badVar ≠ 'A') (hB : badVar ≠ 'B') :
    ∃ e, Internal.parseHexChars
      ((Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
        Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
        Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
        Internal.byteToHexChars b6 ++ Internal.byteToHexChars b7 ++
        [badVar, Internal.lowerHexDigit (b8.toNat % 16)] ++
        Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
        Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
        Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
        Internal.byteToHexChars b15)) = .error e ∧
      e.kind = .invalidVersion ∧ e.message ≠ "" := by
  obtain ⟨bv, hbv⟩ := hexCharsToByte_isSome_of_hex hvar
    (hexCharToNibble_lowerHexDigit_some (b8.toNat % 16) (uint8_nibble_bounds b8).2)
  have hne80 := hexCharsToByte_badVar h8 h9 ha hb hA hB hbv
  have hne80b : ((bv &&& 0xC0) != 0x80) = true := bne_iff_ne.mpr hne80
  have hv6b : ((b6 &&& 0xF0) != 0x40) = false := by simp [hv6]
  have hlen : ((Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
      Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
      Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
      Internal.byteToHexChars b6 ++ Internal.byteToHexChars b7 ++
      [badVar, Internal.lowerHexDigit (b8.toNat % 16)] ++
      Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
      Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
      Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
      Internal.byteToHexChars b15).length != 32) = false := by
    simp [Internal.byteToHexChars]
  have hdec : Internal.decodeHexPairs
      (Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
       Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
       Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
       Internal.byteToHexChars b6 ++ Internal.byteToHexChars b7 ++
       [badVar, Internal.lowerHexDigit (b8.toNat % 16)] ++
       Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
       Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
       Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
       Internal.byteToHexChars b15) =
      some [b0, b1, b2, b3, b4, b5, b6, b7, bv, b9, b10, b11, b12, b13, b14, b15] := by
    simp only [Internal.byteToHexChars, List.cons_append, List.nil_append]
    repeat rw [decodeHexPairs_byte_cons]
    rw [decodeHexPairs_cons _ _ _ hbv]
    repeat rw [decodeHexPairs_byte_cons]
    rfl
  refine ⟨{ kind := .invalidVersion, message := "UUID variant bits must be RFC 4122 (10xx)" },
    ?_, rfl, by decide⟩
  rw [Internal.parseHexChars, hlen]
  simp only [Bool.false_eq_true, ↓reduceIte, hdec]
  unfold Internal.validateV4BytesList
  rw [mkByteArray16_eq]
  have hsz : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, bv, b9, b10, b11, b12, b13, b14, b15]).size = 16 := rfl
  have h6 : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, bv, b9, b10, b11, b12, b13, b14, b15])[6]! = b6 := rfl
  have h8' : (ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, bv, b9, b10, b11, b12, b13, b14, b15])[8]! = bv := rfl
  simp only [hsz, h6, h8', hv6b, hne80b, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

private theorem formatHexList16_eq
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    Internal.formatHexList [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
      Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
      Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
      Internal.byteToHexChars b6 ++ Internal.byteToHexChars b7 ++
      Internal.byteToHexChars b8 ++ Internal.byteToHexChars b9 ++
      Internal.byteToHexChars b10 ++ Internal.byteToHexChars b11 ++
      Internal.byteToHexChars b12 ++ Internal.byteToHexChars b13 ++
      Internal.byteToHexChars b14 ++ Internal.byteToHexChars b15 := by
  simp [Internal.formatHexList, List.append_assoc]

private theorem list_set_append_right {α : Type} (a b : List α) (x : α) (k : Nat) :
    (a ++ b).set (a.length + k) x = a ++ b.set k x := by
  induction a with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.length_cons, Nat.add_right_comm, List.cons_append, List.set_cons_succ, ih]

private theorem parse_badVer_badVar_errors
    (bs : ByteArray) (hlen : bs.size = 16)
    {badVer : Char} (hverHex : isHexChar badVer = true) (hverNe : badVer ≠ '4')
    {badVar : Char} (hvarHex : isHexChar badVar = true)
    (h8 : badVar ≠ '8') (h9 : badVar ≠ '9') (ha : badVar ≠ 'a')
    (hb : badVar ≠ 'b') (hA : badVar ≠ 'A') (hB : badVar ≠ 'B') :
    ∃ u e1 e2,
      Internal.fromRandomBytes bs = .ok u ∧
      Internal.parse (String.ofList ((Internal.toString u).toList.set 14 badVer)) = .error e1 ∧
      (e1.kind = .invalidVersion ∧ e1.message ≠ "" ∧
        Internal.isValid (String.ofList ((Internal.toString u).toList.set 14 badVer)) = false) ∧
      Internal.parse (String.ofList ((Internal.toString u).toList.set 19 badVar)) = .error e2 ∧
      (e2.kind = .invalidVersion ∧ e2.message ≠ "" ∧
        Internal.isValid (String.ofList ((Internal.toString u).toList.set 19 badVar)) = false) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    eq_of_size_16 bs hlen
  have hv6 : (((b6 &&& 0x0F) ||| 0x40) &&& 0xF0) = 0x40 := uint8_v4_ver b6
  let b6' := (b6 &&& 0x0F) ||| 0x40
  let b8' := (b8 &&& 0x3F) ||| 0x80
  have h1 := parseHexChars_badVer b0 b1 b2 b3 b4 b5 b6' b7 b8' b9 b10 b11 b12 b13 b14 b15 hverHex hverNe
  have h2 := parseHexChars_badVar b0 b1 b2 b3 b4 b5 b6' b7 b8' b9 b10 b11 b12 b13 b14 b15 hv6 hvarHex
    h8 h9 ha hb hA hB
  let e1 := h1.choose
  have he1 := h1.choose_spec.1
  have hk1 := h1.choose_spec.2.1
  have hm1 := h1.choose_spec.2.2
  let e2 := h2.choose
  have he2 := h2.choose_spec.1
  have hk2 := h2.choose_spec.2.1
  have hm2 := h2.choose_spec.2.2
  let a := Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
    Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3
  let b := Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5
  let c := Internal.byteToHexChars b6' ++ Internal.byteToHexChars b7
  let c' := [badVer, Internal.lowerHexDigit (b6'.toNat % 16)] ++ Internal.byteToHexChars b7
  let d := Internal.byteToHexChars b8' ++ Internal.byteToHexChars b9
  let d' := [badVar, Internal.lowerHexDigit (b8'.toNat % 16)] ++ Internal.byteToHexChars b9
  let e := Internal.byteToHexChars b10 ++ Internal.byteToHexChars b11 ++
    Internal.byteToHexChars b12 ++ Internal.byteToHexChars b13 ++
    Internal.byteToHexChars b14 ++ Internal.byteToHexChars b15
  have haL : a.length = 8 := by simp [a, Internal.byteToHexChars]
  have hbL : b.length = 4 := by simp [b, Internal.byteToHexChars]
  have hcL : c.length = 4 := by simp [c, Internal.byteToHexChars]
  have hc'L : c'.length = 4 := by simp [c', Internal.byteToHexChars]
  have hdL : d.length = 4 := by simp [d, Internal.byteToHexChars]
  have hd'L : d'.length = 4 := by simp [d', Internal.byteToHexChars]
  have heL : e.length = 12 := by simp [e, Internal.byteToHexChars]
  have hfmt : Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15] =
      a ++ b ++ c ++ d ++ e := by
    rw [formatHexList16_eq]
    simp only [a, b, c, d, e, List.append_assoc]
  have hins : Internal.insertHyphens (a ++ b ++ c ++ d ++ e) =
      a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e :=
    insertHyphens_five a b c d e haL hbL hcL hdL
  have hset14 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).set 14 badVer =
      a ++ ['-'] ++ b ++ ['-'] ++ c' ++ ['-'] ++ d ++ ['-'] ++ e := by
    have hpre : (a ++ ['-'] ++ b ++ ['-']).length + 0 = 14 := by simp [haL, hbL]
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-']) ++ (c ++ ['-'] ++ d ++ ['-'] ++ e) := by
      simp [List.append_assoc]
    have hsplit' : a ++ ['-'] ++ b ++ ['-'] ++ c' ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-']) ++ (c' ++ ['-'] ++ d ++ ['-'] ++ e) := by
      simp [List.append_assoc]
    rw [hsplit, hsplit', ← hpre, list_set_append_right]
    have hcset : (c ++ ['-'] ++ d ++ ['-'] ++ e).set 0 badVer = c' ++ ['-'] ++ d ++ ['-'] ++ e := by
      simp [c, c', Internal.byteToHexChars]
    simpa [List.append_assoc] using congrArg ((a ++ ['-'] ++ b ++ ['-']) ++ ·) hcset
  have hset19 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e).set 19 badVar =
      a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d' ++ ['-'] ++ e := by
    have hpre : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-']).length + 0 = 19 := by simp [haL, hbL, hcL]
    have hsplit : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-']) ++ (d ++ ['-'] ++ e) := by
      simp [List.append_assoc]
    have hsplit' : a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d' ++ ['-'] ++ e =
        (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-']) ++ (d' ++ ['-'] ++ e) := by
      simp [List.append_assoc]
    rw [hsplit, hsplit', ← hpre, list_set_append_right]
    have hdset : (d ++ ['-'] ++ e).set 0 badVar = d' ++ ['-'] ++ e := by
      simp [d, d', Internal.byteToHexChars]
    simpa [List.append_assoc] using congrArg ((a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-']) ++ ·) hdset
  have hp1 : Internal.parseCanonicalChars
      (String.ofList ((String.ofList (Internal.insertHyphens (Internal.formatHexList
        [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15]))).toList.set 14 badVer)).toList =
      .error e1 := by
    rw [String.toList_ofList, String.toList_ofList, hfmt, hins, hset14]
    have hlen36 : (a ++ ['-'] ++ b ++ ['-'] ++ c' ++ ['-'] ++ d ++ ['-'] ++ e).length = 36 := by
      simp [haL, hbL, hc'L, hdL, heL]
    rw [Internal.parseCanonicalChars]
    simp only [hlen36, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      stripCanonicalHyphens_five a b c' d e haL hbL hc'L hdL heL]
    have heq : a ++ b ++ c' ++ d ++ e =
        Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
        Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
        Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
        [badVer, Internal.lowerHexDigit (b6'.toNat % 16)] ++
        Internal.byteToHexChars b7 ++ Internal.byteToHexChars b8' ++
        Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
        Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
        Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
        Internal.byteToHexChars b15 := by
      simp only [a, b, c', d, e, List.append_assoc]
    rw [heq]
    exact he1
  have hp2 : Internal.parseCanonicalChars
      (String.ofList ((String.ofList (Internal.insertHyphens (Internal.formatHexList
        [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15]))).toList.set 19 badVar)).toList =
      .error e2 := by
    rw [String.toList_ofList, String.toList_ofList, hfmt, hins, hset19]
    have hlen36 : (a ++ ['-'] ++ b ++ ['-'] ++ c ++ ['-'] ++ d' ++ ['-'] ++ e).length = 36 := by
      simp [haL, hbL, hcL, hd'L, heL]
    rw [Internal.parseCanonicalChars]
    simp only [hlen36, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      stripCanonicalHyphens_five a b c d' e haL hbL hcL hd'L heL]
    have heq : a ++ b ++ c ++ d' ++ e =
        Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
        Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
        Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
        Internal.byteToHexChars b6' ++ Internal.byteToHexChars b7 ++
        [badVar, Internal.lowerHexDigit (b8'.toNat % 16)] ++
        Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
        Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
        Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
        Internal.byteToHexChars b15 := by
      simp only [a, b, c, d', e, List.append_assoc]
    rw [heq]
    exact he2
  let u : Uuid := { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15] }
  refine ⟨u, e1, e2, fromRandomBytes16_eq b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15, ?_⟩
  have hto : Internal.toString u = String.ofList (Internal.insertHyphens (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15])) :=
    toString16_eq b0 b1 b2 b3 b4 b5 b6' b7 b8' b9 b10 b11 b12 b13 b14 b15
  rw [hto]
  refine ⟨by rw [Internal.parse, hp1], by rw [Internal.isValid, Internal.parse, hp1]; exact ⟨hk1, hm1, rfl⟩,
    by rw [Internal.parse, hp2], by rw [Internal.isValid, Internal.parse, hp2]; exact ⟨hk2, hm2, rfl⟩⟩

private theorem parse_badVer_badVar_spec
    (bs : ByteArray) (hlen : bs.size = 16)
    {badVer : Char} (hverHex : isHexChar badVer = true) (hverNe : badVer ≠ '4')
    {badVar : Char} (hvarHex : isHexChar badVar = true)
    (h8 : badVar ≠ '8') (h9 : badVar ≠ '9') (ha : badVar ≠ 'a')
    (hb : badVar ≠ 'b') (hA : badVar ≠ 'A') (hB : badVar ≠ 'B') :
    match Internal.fromRandomBytes bs with
    | .error _ => False
    | .ok u =>
      (match Internal.parse (String.ofList ((Internal.toString u).toList.set 14 badVer)) with
       | .ok _ => False
       | .error e => e.kind = .invalidVersion ∧ e.message ≠ "" ∧
           Internal.isValid (String.ofList ((Internal.toString u).toList.set 14 badVer)) = false) ∧
      (match Internal.parse (String.ofList ((Internal.toString u).toList.set 19 badVar)) with
       | .ok _ => False
       | .error e => e.kind = .invalidVersion ∧ e.message ≠ "" ∧
           Internal.isValid (String.ofList ((Internal.toString u).toList.set 19 badVar)) = false) := by
  obtain ⟨u, e1, e2, hu, hp1, h1, hp2, h2⟩ :=
    parse_badVer_badVar_errors bs hlen hverHex hverNe hvarHex h8 h9 ha hb hA hB
  rw [hu]
  dsimp only
  rw [hp1, hp2]
  exact ⟨h1, h2⟩

/-- Proof of `test_uuid_parse_rejectsNonV4VersionOrVariant` for `defaultApi`. -/
theorem proof_uuid_parse_rejectsNonV4VersionOrVariant :
    AllPass (test_uuid_parse_rejectsNonV4VersionOrVariant defaultApi) := by
  intro bs hlen badVer ⟨hverHex, hverNe⟩ badVar ⟨hvarHex, h8, h9, ha, hb, hA, hB⟩
  have h := parse_badVer_badVar_spec bs hlen hverHex hverNe hvarHex h8 h9 ha hb hA hB
  dsimp [test_uuid_parse_rejectsNonV4VersionOrVariant, defaultApi, Internal.mkApi, Internal.mkApiM,
    Bind.bind, Core.NondetTest.assert]
  cases hfr : Internal.fromRandomBytes bs with
  | error _ => intro hf; exact False.elim hf
  | ok u =>
    rw [hfr] at h
    dsimp only at h ⊢
    cases hp1 : Internal.parse (String.ofList ((Internal.toString u).toList.set 14 badVer)) with
    | ok _ => rw [hp1] at h; exact False.elim h.1
    | error e1 =>
      rw [hp1] at h
      dsimp only at h ⊢
      cases hp2 : Internal.parse (String.ofList ((Internal.toString u).toList.set 19 badVar)) with
      | ok _ => rw [hp2] at h; exact False.elim h.2
      | error e2 =>
        rw [hp2] at h
        dsimp only at h ⊢
        simp only [and_true]
        exact ⟨h.1, h.2⟩

/-- Non-vacuity witness for `test_uuid_parse_rejectsNonV4VersionOrVariant`. -/
theorem reach_uuid_parse_rejectsNonV4VersionOrVariant :
    CanReach (test_uuid_parse_rejectsNonV4VersionOrVariant defaultApi) := by
  obtain ⟨bs, hlen⟩ : ∃ bs : ByteArray, bs.size = 16 :=
    ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩
  have h := parse_badVer_badVar_spec bs hlen (badVer := '5') (by decide) (by decide)
    (badVar := '0') (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  dsimp [CanReach, test_uuid_parse_rejectsNonV4VersionOrVariant, defaultApi,
    Internal.mkApi, Internal.mkApiM, Bind.bind, Core.NondetTest.nondet, Core.NondetTest.assume,
    Core.NondetTest.assert]
  refine ⟨bs, hlen, '5', by decide, '0', by decide, ?_⟩
  cases hfr : Internal.fromRandomBytes bs with
  | error _ => rw [hfr] at h; exact False.elim h
  | ok u =>
    rw [hfr] at h
    dsimp only at h ⊢
    cases hp1 : Internal.parse (String.ofList ((Internal.toString u).toList.set 14 '5')) with
    | ok _ => rw [hp1] at h; exact False.elim h.1
    | error e1 =>
      rw [hp1] at h
      dsimp only at h ⊢
      cases hp2 : Internal.parse (String.ofList ((Internal.toString u).toList.set 19 '0')) with
      | ok _ => rw [hp2] at h; exact False.elim h.2
      | error e2 =>
        rw [hp2] at h
        dsimp only at h ⊢
        simp only [and_true]
        exact ⟨h.1, h.2⟩

/-- Proof of `test_uuid_parseHex_rejectsInvalidLength` for `defaultApi`. -/
theorem proof_uuid_parseHex_rejectsInvalidLength :
    AllPass (test_uuid_parseHex_rejectsInvalidLength defaultApi) := by
  intro s hne
  dsimp [test_uuid_parseHex_rejectsInvalidLength, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parseHex, Internal.parseHexChars, Bind.bind, Core.NondetTest.assert]
  have hlen : s.toList.length ≠ 32 := by
    rw [String.length_toList]
    exact hne
  have hbne : (s.toList.length != 32) = true := bne_iff_ne.mpr hlen
  simp only [hbne, ↓reduceIte]
  exact ⟨⟨trivial, append_ne_empty_of_left (by decide)⟩, trivial⟩

/-- Non-vacuity witness for `test_uuid_parseHex_rejectsInvalidLength`. -/
theorem reach_uuid_parseHex_rejectsInvalidLength :
    CanReach (test_uuid_parseHex_rejectsInvalidLength defaultApi) := by
  refine ⟨"", by decide, ?_⟩
  exact proof_uuid_parseHex_rejectsInvalidLength "" (by decide)

/-- Proof of `test_uuid_parseHex_rejectsNonHexChar` for `defaultApi`. -/
theorem proof_uuid_parseHex_rejectsNonHexChar :
    AllPass (test_uuid_parseHex_rejectsNonHexChar defaultApi) := by
  intro s hlen idx ⟨hidx, hbad⟩
  dsimp [test_uuid_parseHex_rejectsNonHexChar, defaultApi, Internal.mkApi, Internal.mkApiM,
    Internal.parseHex, Internal.parseHexChars, Bind.bind, Core.NondetTest.assert]
  have hclen : s.toList.length = 32 := by rw [String.length_toList]; exact hlen
  have hbne : (s.toList.length != 32) = false := by simp [hclen]
  have hbad' : isHexChar s.toList[idx]! = false := isHexChar_false_of_pred (by decide) hbad
  have hmem : s.toList[idx]! ∈ s.toList := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (hclen ▸ hidx)]
    exact List.getElem_mem _
  have hdec := decodeHexPairs_none_of_mem_bad s.toList s.toList[idx]! hmem hbad'
  simp only [hbne, Bool.false_eq_true, ↓reduceIte, hdec]
  decide

/-- Non-vacuity witness for `test_uuid_parseHex_rejectsNonHexChar`. -/
theorem reach_uuid_parseHex_rejectsNonHexChar :
    CanReach (test_uuid_parseHex_rejectsNonHexChar defaultApi) := by
  refine ⟨"g0000000000040008000000000000000", by decide, 0, by decide, ?_⟩
  exact proof_uuid_parseHex_rejectsNonHexChar "g0000000000040008000000000000000"
    (by decide) 0 (by decide)

private theorem parseHex_badVer_badVar_errors
    (bs : ByteArray) (hlen : bs.size = 16)
    {badVer : Char} (hverHex : isHexChar badVer = true) (hverNe : badVer ≠ '4')
    {badVar : Char} (hvarHex : isHexChar badVar = true)
    (h8 : badVar ≠ '8') (h9 : badVar ≠ '9') (ha : badVar ≠ 'a')
    (hb : badVar ≠ 'b') (hA : badVar ≠ 'A') (hB : badVar ≠ 'B') :
    ∃ u e1 e2,
      Internal.fromRandomBytes bs = .ok u ∧
      Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 12 badVer)) = .error e1 ∧
      (e1.kind = .invalidVersion ∧ e1.message ≠ "") ∧
      Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 16 badVar)) = .error e2 ∧
      (e2.kind = .invalidVersion ∧ e2.message ≠ "") := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    eq_of_size_16 bs hlen
  have hv6 : (((b6 &&& 0x0F) ||| 0x40) &&& 0xF0) = 0x40 := uint8_v4_ver b6
  let b6' := (b6 &&& 0x0F) ||| 0x40
  let b8' := (b8 &&& 0x3F) ||| 0x80
  have h1 := parseHexChars_badVer b0 b1 b2 b3 b4 b5 b6' b7 b8' b9 b10 b11 b12 b13 b14 b15 hverHex hverNe
  have h2 := parseHexChars_badVar b0 b1 b2 b3 b4 b5 b6' b7 b8' b9 b10 b11 b12 b13 b14 b15 hv6 hvarHex
    h8 h9 ha hb hA hB
  let e1 := h1.choose
  have he1 := h1.choose_spec.1
  have hk1 := h1.choose_spec.2.1
  have hm1 := h1.choose_spec.2.2
  let e2 := h2.choose
  have he2 := h2.choose_spec.1
  have hk2 := h2.choose_spec.2.1
  have hm2 := h2.choose_spec.2.2
  let pre12 := Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
    Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
    Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5
  let suf12 := Internal.byteToHexChars b7 ++ Internal.byteToHexChars b8' ++
    Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
    Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
    Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
    Internal.byteToHexChars b15
  have hpre12L : pre12.length + 0 = 12 := by simp [pre12, Internal.byteToHexChars]
  have hset12 : (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15]).set 12 badVer =
      Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
      Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
      Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
      [badVer, Internal.lowerHexDigit (b6'.toNat % 16)] ++
      Internal.byteToHexChars b7 ++ Internal.byteToHexChars b8' ++
      Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
      Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
      Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
      Internal.byteToHexChars b15 := by
    rw [formatHexList16_eq]
    have hsplit : Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
        Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
        Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
        Internal.byteToHexChars b6' ++ Internal.byteToHexChars b7 ++
        Internal.byteToHexChars b8' ++ Internal.byteToHexChars b9 ++
        Internal.byteToHexChars b10 ++ Internal.byteToHexChars b11 ++
        Internal.byteToHexChars b12 ++ Internal.byteToHexChars b13 ++
        Internal.byteToHexChars b14 ++ Internal.byteToHexChars b15 =
        pre12 ++ (Internal.byteToHexChars b6' ++ suf12) := by
      simp [pre12, suf12, List.append_assoc]
    rw [hsplit, ← hpre12L, list_set_append_right]
    have h6set : (Internal.byteToHexChars b6' ++ suf12).set 0 badVer =
        [badVer, Internal.lowerHexDigit (b6'.toNat % 16)] ++ suf12 := by
      simp [Internal.byteToHexChars]
    rw [h6set]
    simp [pre12, suf12, List.append_assoc]
  let pre16 := Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
    Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
    Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
    Internal.byteToHexChars b6' ++ Internal.byteToHexChars b7
  let suf16 := Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
    Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
    Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
    Internal.byteToHexChars b15
  have hpre16L : pre16.length + 0 = 16 := by simp [pre16, Internal.byteToHexChars]
  have hset16 : (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15]).set 16 badVar =
      Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
      Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
      Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
      Internal.byteToHexChars b6' ++ Internal.byteToHexChars b7 ++
      [badVar, Internal.lowerHexDigit (b8'.toNat % 16)] ++
      Internal.byteToHexChars b9 ++ Internal.byteToHexChars b10 ++
      Internal.byteToHexChars b11 ++ Internal.byteToHexChars b12 ++
      Internal.byteToHexChars b13 ++ Internal.byteToHexChars b14 ++
      Internal.byteToHexChars b15 := by
    rw [formatHexList16_eq]
    have hsplit : Internal.byteToHexChars b0 ++ Internal.byteToHexChars b1 ++
        Internal.byteToHexChars b2 ++ Internal.byteToHexChars b3 ++
        Internal.byteToHexChars b4 ++ Internal.byteToHexChars b5 ++
        Internal.byteToHexChars b6' ++ Internal.byteToHexChars b7 ++
        Internal.byteToHexChars b8' ++ Internal.byteToHexChars b9 ++
        Internal.byteToHexChars b10 ++ Internal.byteToHexChars b11 ++
        Internal.byteToHexChars b12 ++ Internal.byteToHexChars b13 ++
        Internal.byteToHexChars b14 ++ Internal.byteToHexChars b15 =
        pre16 ++ (Internal.byteToHexChars b8' ++ suf16) := by
      simp [pre16, suf16, List.append_assoc]
    have h16 := list_set_append_right pre16 (Internal.byteToHexChars b8' ++ suf16) badVar 0
    rw [hpre16L] at h16
    rw [hsplit, h16]
    have h8set : (Internal.byteToHexChars b8' ++ suf16).set 0 badVar =
        [badVar, Internal.lowerHexDigit (b8'.toNat % 16)] ++ suf16 := by
      simp [Internal.byteToHexChars]
    rw [h8set]
    simp [pre16, suf16, List.append_assoc]
  have hp1 : Internal.parseHexChars
      (String.ofList ((String.ofList (Internal.formatHexList
        [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15])).toList.set 12 badVer)).toList =
      .error e1 := by
    rw [String.toList_ofList, String.toList_ofList, hset12]
    exact he1
  have hp2 : Internal.parseHexChars
      (String.ofList ((String.ofList (Internal.formatHexList
        [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15])).toList.set 16 badVar)).toList =
      .error e2 := by
    rw [String.toList_ofList, String.toList_ofList, hset16]
    exact he2
  let u : Uuid := { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15] }
  refine ⟨u, e1, e2, fromRandomBytes16_eq b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15, ?_⟩
  have hto : Internal.toHex u = String.ofList (Internal.formatHexList
      [b0, b1, b2, b3, b4, b5, b6', b7, b8', b9, b10, b11, b12, b13, b14, b15]) :=
    toHex16_eq b0 b1 b2 b3 b4 b5 b6' b7 b8' b9 b10 b11 b12 b13 b14 b15
  rw [hto]
  exact ⟨by rw [Internal.parseHex, hp1], ⟨hk1, hm1⟩, by rw [Internal.parseHex, hp2], ⟨hk2, hm2⟩⟩

private theorem parseHex_badVer_badVar_spec
    (bs : ByteArray) (hlen : bs.size = 16)
    {badVer : Char} (hverHex : isHexChar badVer = true) (hverNe : badVer ≠ '4')
    {badVar : Char} (hvarHex : isHexChar badVar = true)
    (h8 : badVar ≠ '8') (h9 : badVar ≠ '9') (ha : badVar ≠ 'a')
    (hb : badVar ≠ 'b') (hA : badVar ≠ 'A') (hB : badVar ≠ 'B') :
    match Internal.fromRandomBytes bs with
    | .error _ => False
    | .ok u =>
      (match Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 12 badVer)) with
       | .ok _ => False
       | .error e => e.kind = .invalidVersion ∧ e.message ≠ "") ∧
      (match Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 16 badVar)) with
       | .ok _ => False
       | .error e => e.kind = .invalidVersion ∧ e.message ≠ "") := by
  obtain ⟨u, e1, e2, hu, hp1, h1, hp2, h2⟩ :=
    parseHex_badVer_badVar_errors bs hlen hverHex hverNe hvarHex h8 h9 ha hb hA hB
  rw [hu]
  dsimp only
  rw [hp1, hp2]
  exact ⟨h1, h2⟩

/-- Proof of `test_uuid_parseHex_rejectsNonV4VersionOrVariant` for `defaultApi`. -/
theorem proof_uuid_parseHex_rejectsNonV4VersionOrVariant :
    AllPass (test_uuid_parseHex_rejectsNonV4VersionOrVariant defaultApi) := by
  intro bs hlen badVer ⟨hverHex, hverNe⟩ badVar ⟨hvarHex, h8, h9, ha, hb, hA, hB⟩
  have h := parseHex_badVer_badVar_spec bs hlen hverHex hverNe hvarHex h8 h9 ha hb hA hB
  dsimp [test_uuid_parseHex_rejectsNonV4VersionOrVariant, defaultApi, Internal.mkApi, Internal.mkApiM,
    Bind.bind, Core.NondetTest.assert]
  cases hfr : Internal.fromRandomBytes bs with
  | error _ => intro hf; exact False.elim hf
  | ok u =>
    rw [hfr] at h
    dsimp only at h ⊢
    cases hp1 : Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 12 badVer)) with
    | ok _ => rw [hp1] at h; exact False.elim h.1
    | error e1 =>
      rw [hp1] at h
      dsimp only at h ⊢
      cases hp2 : Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 16 badVar)) with
      | ok _ => rw [hp2] at h; exact False.elim h.2
      | error e2 =>
        rw [hp2] at h
        dsimp only at h ⊢
        simp only [and_true]
        exact ⟨h.1, h.2⟩

/-- Non-vacuity witness for `test_uuid_parseHex_rejectsNonV4VersionOrVariant`. -/
theorem reach_uuid_parseHex_rejectsNonV4VersionOrVariant :
    CanReach (test_uuid_parseHex_rejectsNonV4VersionOrVariant defaultApi) := by
  obtain ⟨bs, hlen⟩ : ∃ bs : ByteArray, bs.size = 16 :=
    ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩
  have h := parseHex_badVer_badVar_spec bs hlen (badVer := '5') (by decide) (by decide)
    (badVar := '0') (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  dsimp [CanReach, test_uuid_parseHex_rejectsNonV4VersionOrVariant, defaultApi,
    Internal.mkApi, Internal.mkApiM, Bind.bind, Core.NondetTest.nondet, Core.NondetTest.assume,
    Core.NondetTest.assert]
  refine ⟨bs, hlen, '5', by decide, '0', by decide, ?_⟩
  cases hfr : Internal.fromRandomBytes bs with
  | error _ => rw [hfr] at h; exact False.elim h
  | ok u =>
    rw [hfr] at h
    dsimp only at h ⊢
    cases hp1 : Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 12 '5')) with
    | ok _ => rw [hp1] at h; exact False.elim h.1
    | error e1 =>
      rw [hp1] at h
      dsimp only at h ⊢
      cases hp2 : Internal.parseHex (String.ofList ((Internal.toHex u).toList.set 16 '0')) with
      | ok _ => rw [hp2] at h; exact False.elim h.2
      | error e2 =>
        rw [hp2] at h
        dsimp only at h ⊢
        simp only [and_true]
        exact ⟨h.1, h.2⟩

private theorem deterministicEntropyBytes_16_eq (d : Nat) :
    LeanSwe.LinuxSyscall.TimeRand.deterministicEntropyBytes d 16 =
      ByteArray.mk #[
        UInt8.ofNat ((d / 1) % 256),
        UInt8.ofNat ((d / 256) % 256),
        UInt8.ofNat ((d / 65536) % 256),
        UInt8.ofNat ((d / 16777216) % 256),
        UInt8.ofNat ((d * 131 + 4 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 5 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 6 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 7 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 8 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 9 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 10 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 11 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 12 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 13 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 14 * 17 + 0x5A) % 256),
        UInt8.ofNat ((d * 131 + 15 * 17 + 0x5A) % 256)
      ] := rfl

private def mkModelV4Uuid (d : Nat) : Uuid :=
  { bytes := ByteArray.mk #[
      UInt8.ofNat ((d / 1) % 256),
      UInt8.ofNat ((d / 256) % 256),
      UInt8.ofNat ((d / 65536) % 256),
      UInt8.ofNat ((d / 16777216) % 256),
      UInt8.ofNat ((d * 131 + 4 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 5 * 17 + 0x5A) % 256),
      (UInt8.ofNat ((d * 131 + 6 * 17 + 0x5A) % 256) &&& (0x0F : UInt8)) ||| (0x40 : UInt8),
      UInt8.ofNat ((d * 131 + 7 * 17 + 0x5A) % 256),
      (UInt8.ofNat ((d * 131 + 8 * 17 + 0x5A) % 256) &&& (0x3F : UInt8)) ||| (0x80 : UInt8),
      UInt8.ofNat ((d * 131 + 9 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 10 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 11 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 12 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 13 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 14 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 15 * 17 + 0x5A) % 256)
    ] }

private theorem fromRandomBytes_det16 (d : Nat) :
    Internal.fromRandomBytes (LeanSwe.LinuxSyscall.TimeRand.deterministicEntropyBytes d 16) =
      .ok (mkModelV4Uuid d) := by
  rw [deterministicEntropyBytes_16_eq]
  exact fromRandomBytes16_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem mkModelV4Uuid_parse (d : Nat) :
    Internal.parse (Internal.toString (mkModelV4Uuid d)) = .ok (mkModelV4Uuid d) := by
  have hto : Internal.toString (mkModelV4Uuid d) = String.ofList (Internal.insertHyphens (Internal.formatHexList [
      UInt8.ofNat ((d / 1) % 256),
      UInt8.ofNat ((d / 256) % 256),
      UInt8.ofNat ((d / 65536) % 256),
      UInt8.ofNat ((d / 16777216) % 256),
      UInt8.ofNat ((d * 131 + 4 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 5 * 17 + 0x5A) % 256),
      (UInt8.ofNat ((d * 131 + 6 * 17 + 0x5A) % 256) &&& (0x0F : UInt8)) ||| (0x40 : UInt8),
      UInt8.ofNat ((d * 131 + 7 * 17 + 0x5A) % 256),
      (UInt8.ofNat ((d * 131 + 8 * 17 + 0x5A) % 256) &&& (0x3F : UInt8)) ||| (0x80 : UInt8),
      UInt8.ofNat ((d * 131 + 9 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 10 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 11 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 12 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 13 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 14 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 15 * 17 + 0x5A) % 256)
    ])) := toString16_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [Internal.parse, hto, String.toList_ofList]
  exact parseCanonicalChars16_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (uint8_v4_ver _) (uint8_v4_var _)

private theorem mkModelV4Uuid_parseHex (d : Nat) :
    Internal.parseHex (Internal.toHex (mkModelV4Uuid d)) = .ok (mkModelV4Uuid d) := by
  have hto : Internal.toHex (mkModelV4Uuid d) = String.ofList (Internal.formatHexList [
      UInt8.ofNat ((d / 1) % 256),
      UInt8.ofNat ((d / 256) % 256),
      UInt8.ofNat ((d / 65536) % 256),
      UInt8.ofNat ((d / 16777216) % 256),
      UInt8.ofNat ((d * 131 + 4 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 5 * 17 + 0x5A) % 256),
      (UInt8.ofNat ((d * 131 + 6 * 17 + 0x5A) % 256) &&& (0x0F : UInt8)) ||| (0x40 : UInt8),
      UInt8.ofNat ((d * 131 + 7 * 17 + 0x5A) % 256),
      (UInt8.ofNat ((d * 131 + 8 * 17 + 0x5A) % 256) &&& (0x3F : UInt8)) ||| (0x80 : UInt8),
      UInt8.ofNat ((d * 131 + 9 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 10 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 11 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 12 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 13 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 14 * 17 + 0x5A) % 256),
      UInt8.ofNat ((d * 131 + 15 * 17 + 0x5A) % 256)
    ]) := toHex16_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [Internal.parseHex, hto, String.toList_ofList]
  exact parseHexChars16_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (uint8_v4_ver _) (uint8_v4_var _)

private theorem mkModelV4Uuid_ne_succ (d : Nat) :
    mkModelV4Uuid d ≠ mkModelV4Uuid (d + 1) := by
  intro h
  have hb0 := congrArg (fun u => u.bytes[0]!.toNat) h
  change (UInt8.ofNat ((d / 1) % 256)).toNat = (UInt8.ofNat (((d + 1) / 1) % 256)).toNat at hb0
  simp only [UInt8.toNat_ofNat', Nat.mod_mod] at hb0
  omega

private theorem appendBytes_size (a b : ByteArray) :
    (Internal.appendBytes a b).size = a.size + b.size := by
  cases a with
  | mk arrA =>
    cases b with
    | mk arrB =>
      unfold Internal.appendBytes
      by_cases h0 : (ByteArray.mk arrA).size == 0
      · have ha : arrA.size = 0 := beq_iff_eq.mp h0
        simp only [h0, ↓reduceIte]
        change arrB.size = arrA.size + arrB.size
        omega
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        change (arrA.toList ++ arrB.toList).toArray.size = arrA.size + arrB.size
        simp

private theorem appendBytes_empty_left (b : ByteArray) :
    Internal.appendBytes ByteArray.empty b = b := rfl

private theorem appendBytes_nonempty_left (a b : ByteArray) (ha : 0 < a.size) :
    Internal.appendBytes a b = ByteArray.mk (a.data.toList ++ b.data.toList).toArray := by
  unfold Internal.appendBytes
  have hne : (a.size == 0) = false := beq_false_of_ne (by omega)
  rw [hne]
  rfl

private theorem gatherRandomBytes16_step_succ {m : Type → Type} [Monad m]
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m) (fuel' : Nat)
    (acc : ByteArray) (hacc : acc.size < 16) (last? : Option LeanSwe.LinuxSyscall.Errno) :
    Internal.gatherRandomBytes16 sys (fuel' + 1) acc last? =
      (do
        let r ← sys.getrandom (UInt32.ofNat (16 - acc.size)) {}
        match Internal.stepRandomBytes16 (16 - acc.size) acc r with
        | .error err => pure (.error err)
        | .ok (.inl doneBytes) => pure (.ok doneBytes)
        | .ok (.inr (nextAcc, nextLast)) => Internal.gatherRandomBytes16 sys fuel' nextAcc nextLast) := by
  rw [Internal.gatherRandomBytes16.eq_def]
  have h16 : (acc.size == 16) = false := beq_false_of_ne (by omega)
  have hgt : decide (acc.size > 16) = false := decide_eq_false (by omega)
  simp only [h16, hgt, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem gatherRandomBytes16_zero_lt {m : Type → Type} [Monad m]
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM m)
    (acc : ByteArray) (hacc : acc.size < 16) (last? : Option LeanSwe.LinuxSyscall.Errno) :
    Internal.gatherRandomBytes16 sys 0 acc last? =
      match last? with
      | some e => pure (.error (Internal.mapErrnoToUuidError e))
      | none => pure (.error (Internal.mapRawError (.shortRead acc.size
          s!"getrandom retry budget exhausted after {acc.size} of 16 bytes"))) := by
  rw [Internal.gatherRandomBytes16.eq_def]
  have h16 : (acc.size == 16) = false := beq_false_of_ne (by omega)
  have hgt : decide (acc.size > 16) = false := decide_eq_false (by omega)
  simp only [h16, hgt, Bool.false_eq_true, ↓reduceIte]
  cases last? <;> rfl

private theorem mkApiM_modelOps_getUuid_run (s : LeanSwe.LinuxSyscall.TimeRand.TimeRandState) :
    (Internal.mkApiM LeanSwe.LinuxSyscall.TimeRand.modelOps).getUuid s =
      (.ok (mkModelV4Uuid s.entropyDraws),
        { s with crngReady := true, entropyDraws := s.entropyDraws + 1 }) := by
  have hmax : Internal.MAX_GETRANDOM_ATTEMPTS = 32 := rfl
  cases s with
  | mk mono rt crng dr amb =>
    cases crng <;>
    · dsimp [Internal.mkApiM, Internal.mkApi, Bind.bind, Pure.pure,
        StateT.bind, StateT.pure]
      rw [hmax, gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
      dsimp [Internal.stepRandomBytes16, Internal.appendBytes,
        LeanSwe.LinuxSyscall.TimeRand.modelOps, Bind.bind, Pure.pure,
        StateT.bind, StateT.pure, MonadStateOf.get, get, StateT.get,
        MonadStateOf.set, set, StateT.set]
      exact congrArg
        (fun x => (x, LeanSwe.LinuxSyscall.TimeRand.TimeRandState.mk mono rt true (dr + 1) amb))
        (fromRandomBytes_det16 dr)

/-- Proof of `test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid` for `mkApiM`. -/
theorem proof_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid :
    AllPass (test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid Internal.mkApiM) := by
  intro s₀
  dsimp [test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid, Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, Core.NondetTest.assert]
  have h1 := mkApiM_modelOps_getUuid_run s₀
  have h2 := mkApiM_modelOps_getUuid_run { s₀ with crngReady := true, entropyDraws := s₀.entropyDraws + 1 }
  dsimp only at h1 h2
  rw [h1]
  dsimp only
  rw [h2]
  dsimp only [Internal.mkApiM, Internal.mkApi]
  have hne := mkModelV4Uuid_ne_succ s₀.entropyDraws
  have hp1 := mkModelV4Uuid_parse s₀.entropyDraws
  have hp2 := mkModelV4Uuid_parse (s₀.entropyDraws + 1)
  have hh1 := mkModelV4Uuid_parseHex s₀.entropyDraws
  have hh2 := mkModelV4Uuid_parseHex (s₀.entropyDraws + 1)
  have hv6 : ∀ d, ((mkModelV4Uuid d).bytes[6]! &&& (0xF0 : UInt8)) = 0x40 := fun d =>
    uint8_v4_ver _
  have hv8 : ∀ d, ((mkModelV4Uuid d).bytes[8]! &&& (0xC0 : UInt8)) = 0x80 := fun d =>
    uint8_v4_var _
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, hne, ?_, ?_,
    ⟨rfl, hv6 s₀.entropyDraws, hv8 s₀.entropyDraws⟩,
    ⟨rfl, hv6 (s₀.entropyDraws + 1), hv8 (s₀.entropyDraws + 1)⟩,
    ⟨by rw [Internal.isValid, hp1]; rfl, by rw [Internal.isValid, hp2]; rfl⟩, trivial⟩
  · intro h
    have := congrArg Internal.parse h
    rw [hp1, hp2] at this
    exact hne (Except.ok.inj this)
  · intro h
    have := congrArg Internal.parseHex h
    rw [hh1, hh2] at this
    exact hne (Except.ok.inj this)

/-- Non-vacuity witness for `test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid`. -/
theorem reach_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid :
    CanReach (test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid Internal.mkApiM) :=
  ⟨{}, proof_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid {}⟩

/-- Proof of `test_uuid_getUuid_usesExact16BytesFromGetrandom` for `mkApiM`. -/
theorem proof_uuid_getUuid_usesExact16BytesFromGetrandom :
    AllPass (test_uuid_getUuid_usesExact16BytesFromGetrandom Internal.mkApiM) := by
  intro bs hlen
  dsimp [test_uuid_getUuid_usesExact16BytesFromGetrandom, Internal.mkApiM, Internal.mkApi,
    Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Core.NondetTest.assert]
  have hmax : Internal.MAX_GETRANDOM_ATTEMPTS = 32 := rfl
  rw [hmax, gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
  dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure, StateT.modifyGet,
    Internal.stepRandomBytes16]
  have hbs16 : (bs.size == 16) = true := beq_iff_eq.mpr hlen
  have hbs0 : (bs.size == 0) = false := beq_false_of_ne (by omega)
  have hbsgt : decide (bs.size > 16 - ByteArray.empty.size) = false := by
    have : ¬(bs.size > 16 - ByteArray.empty.size) := by change ¬(bs.size > 16 - 0); omega
    exact decide_eq_false this
  have happ : Internal.appendBytes ByteArray.empty bs = bs := rfl
  have hcond : (bs.size == 0 || decide (bs.size > 16 - ByteArray.empty.size)) = false := by
    rw [hbs0, hbsgt]; rfl
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte, happ, hbs16]
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_uuid_getUuid_usesExact16BytesFromGetrandom`. -/
theorem reach_uuid_getUuid_usesExact16BytesFromGetrandom :
    CanReach (test_uuid_getUuid_usesExact16BytesFromGetrandom Internal.mkApiM) :=
  ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl,
    proof_uuid_getUuid_usesExact16BytesFromGetrandom
      (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) rfl⟩

private theorem scriptedGetrandomOps_cons (x : Except LeanSwe.LinuxSyscall.Errno ByteArray)
    (xs : List (Except LeanSwe.LinuxSyscall.Errno ByteArray))
    (len : UInt32) (flags : LeanSwe.LinuxSyscall.TimeRand.GrndFlags) :
    scriptedGetrandomOps.getrandom len flags (x :: xs) = (x, xs) := rfl

private theorem countingFixedGetrandomOps_run (fixed : Except LeanSwe.LinuxSyscall.Errno ByteArray)
    (len : UInt32) (flags : LeanSwe.LinuxSyscall.TimeRand.GrndFlags) (c : Nat) :
    (countingFixedGetrandomOps fixed).getrandom len flags c = (fixed, c + 1) := rfl

private theorem gather_script_eintr_loop (k fuel : Nat) (hk : k + 1 ≤ fuel)
    (acc b2 : ByteArray) (hacc0 : 0 < acc.size) (hb20 : 0 < b2.size) (hsum : acc.size + b2.size = 16)
    (last? : Option LeanSwe.LinuxSyscall.Errno) :
    Internal.gatherRandomBytes16 scriptedGetrandomOps fuel acc last?
      (List.replicate k (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++ [.ok b2]) =
      (.ok (ByteArray.mk (acc.data.toList ++ b2.data.toList).toArray), []) := by
  induction k generalizing fuel last? with
  | zero =>
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [gatherRandomBytes16_step_succ _ _ acc (by omega)]
    dsimp only [Bind.bind, StateT.bind, List.replicate_zero, List.nil_append]
    rw [scriptedGetrandomOps_cons]
    have hb20' : (b2.size == 0) = false := beq_false_of_ne (by omega)
    have hb2gt : decide (b2.size > 16 - acc.size) = false := decide_eq_false (by omega)
    have happ := appendBytes_nonempty_left acc b2 hacc0
    have hnext16 : ((Internal.appendBytes acc b2).size == 16) = true := by
      rw [appendBytes_size, hsum]
      rfl
    have hcond : (b2.size == 0 || decide (b2.size > 16 - acc.size)) = false := by
      rw [hb20', hb2gt]; rfl
    dsimp only [Internal.stepRandomBytes16]
    rw [hcond]
    simp only [Bool.false_eq_true, ↓reduceIte, hnext16, Pure.pure, StateT.pure]
    rw [happ]
  | succ k' ih =>
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [gatherRandomBytes16_step_succ _ _ acc (by omega)]
    dsimp only [Bind.bind, StateT.bind, List.replicate_succ, List.cons_append]
    rw [scriptedGetrandomOps_cons]
    have heintr : (LeanSwe.LinuxSyscall.Errno.EINTR == LeanSwe.LinuxSyscall.Errno.EINTR) = true := rfl
    dsimp only [Internal.stepRandomBytes16]
    rw [heintr]
    exact ih fuel' (by omega) (some LeanSwe.LinuxSyscall.Errno.EINTR)

/-- Proof of `test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr` for `mkApiM`. -/
theorem proof_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr :
    AllPass (test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr Internal.mkApiM) := by
  intro b1 b2 eintrCount ⟨hb1, hb2, hsum⟩ heintr
  dsimp [test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr, Internal.mkApiM, Internal.mkApi,
    Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, Core.NondetTest.assert]
  have hmax : Internal.MAX_GETRANDOM_ATTEMPTS = 32 := rfl
  rw [hmax, gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
  dsimp only [Bind.bind, StateT.bind, List.cons_append]
  rw [scriptedGetrandomOps_cons]
  have hb10 : (b1.size == 0) = false := beq_false_of_ne (by omega)
  have hb1gt : decide (b1.size > 16 - ByteArray.empty.size) = false := by
    have : ¬(b1.size > 16 - ByteArray.empty.size) := by change ¬(b1.size > 16 - 0); omega
    exact decide_eq_false this
  have happ0 : Internal.appendBytes ByteArray.empty b1 = b1 := rfl
  have hb116 : (b1.size == 16) = false := beq_false_of_ne (by omega)
  have hcond : (b1.size == 0 || decide (b1.size > 16 - ByteArray.empty.size)) = false := by
    rw [hb10, hb1gt]; rfl
  dsimp only [Internal.stepRandomBytes16]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte, happ0, hb116]
  rw [gather_script_eintr_loop eintrCount 31 (by omega) b1 b2 hb1 hb2 hsum none]
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity witness for `test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr`. -/
theorem reach_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr :
    CanReach (test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr Internal.mkApiM) :=
  ⟨ByteArray.mk #[1, 2, 3, 4], ByteArray.mk #[5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], 1,
    by decide, by decide,
    proof_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr
      (ByteArray.mk #[1, 2, 3, 4])
      (ByteArray.mk #[5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16])
      1 (by decide) (by decide)⟩

private theorem mapRawError_message_ne_empty (r : UuidRawError) :
    (Internal.mapRawError r).message ≠ "" := by
  have h := proof_uuid_mapRawError_returnsNonEmptyMessage r
  dsimp [test_uuid_mapRawError_returnsNonEmptyMessage, defaultApi, Internal.mkApi,
    Bind.bind, Core.NondetTest.assert] at h
  exact h.1.2

/-- Proof of `test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry` for `mkApiM`. -/
theorem proof_uuid_getUuid_mapsNonEintrErrnoWithoutRetry :
    AllPass (test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry Internal.mkApiM) := by
  intro e hne
  dsimp [test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry, Internal.mkApiM, Internal.mkApi,
    Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, Core.NondetTest.assert]
  have hmax : Internal.MAX_GETRANDOM_ATTEMPTS = 32 := rfl
  rw [hmax, gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
  dsimp only [Bind.bind, StateT.bind]
  rw [countingFixedGetrandomOps_run]
  have heq : (e == LeanSwe.LinuxSyscall.Errno.EINTR) = false := beq_false_of_ne hne
  dsimp only [Internal.stepRandomBytes16]
  rw [heq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  dsimp only [Pure.pure, StateT.pure]
  refine ⟨rfl, ⟨Internal.mapErrnoToUuidError e, rfl, rfl, rfl, mapRawError_message_ne_empty _⟩, trivial⟩

/-- Non-vacuity witness for `test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry`. -/
theorem reach_uuid_getUuid_mapsNonEintrErrnoWithoutRetry :
    CanReach (test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry Internal.mkApiM) :=
  ⟨LeanSwe.LinuxSyscall.Errno.EIO, by decide,
    proof_uuid_getUuid_mapsNonEintrErrnoWithoutRetry LeanSwe.LinuxSyscall.Errno.EIO (by decide)⟩

private theorem gather_fixed_eintr_loop (fuel c : Nat) :
    Internal.gatherRandomBytes16
      (countingFixedGetrandomOps (.error LeanSwe.LinuxSyscall.Errno.EINTR))
      fuel ByteArray.empty (some LeanSwe.LinuxSyscall.Errno.EINTR) c =
      (.error (Internal.mapErrnoToUuidError LeanSwe.LinuxSyscall.Errno.EINTR), c + fuel) := by
  induction fuel generalizing c with
  | zero =>
    rw [gatherRandomBytes16_zero_lt _ _ (by decide)]
    rfl
  | succ fuel' ih =>
    rw [gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
    dsimp only [Bind.bind, StateT.bind]
    rw [countingFixedGetrandomOps_run]
    have heintr : (LeanSwe.LinuxSyscall.Errno.EINTR == LeanSwe.LinuxSyscall.Errno.EINTR) = true := rfl
    dsimp only [Internal.stepRandomBytes16]
    rw [heintr]
    simp only [↓reduceIte]
    rw [ih (c + 1)]
    congr 1
    omega

/-- Proof of `test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed` for `mkApiM`. -/
theorem proof_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed :
    AllPass (test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed Internal.mkApiM) := by
  intro bigChunk hbig
  dsimp [test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed,
    Internal.mkApiM, Internal.mkApi, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure,
    Core.NondetTest.assert]
  have hmax : Internal.MAX_GETRANDOM_ATTEMPTS = 32 := rfl
  have heintrStep :
      Internal.gatherRandomBytes16
        (countingFixedGetrandomOps (.error LeanSwe.LinuxSyscall.Errno.EINTR))
        Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none 0 =
        (.error (Internal.mapErrnoToUuidError LeanSwe.LinuxSyscall.Errno.EINTR), Internal.MAX_GETRANDOM_ATTEMPTS) := by
    rw [hmax, gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
    dsimp only [Bind.bind, StateT.bind]
    rw [countingFixedGetrandomOps_run]
    have heintr : (LeanSwe.LinuxSyscall.Errno.EINTR == LeanSwe.LinuxSyscall.Errno.EINTR) = true := rfl
    dsimp only [Internal.stepRandomBytes16]
    rw [heintr]
    simp only [↓reduceIte]
    exact gather_fixed_eintr_loop 31 1
  have hemptyStep :
      Internal.gatherRandomBytes16
        (countingFixedGetrandomOps (.ok ByteArray.empty))
        Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none 0 =
        (.error (Internal.mapRawError (.shortRead 0
          s!"unexpected getrandom chunk length 0 (expected 1..16)")), 1) := by
    rw [hmax, gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
    dsimp only [Bind.bind, StateT.bind]
    rw [countingFixedGetrandomOps_run]
    dsimp only [Internal.stepRandomBytes16, Pure.pure, StateT.pure]
    rfl
  obtain ⟨errBig, hbigEq, hbigKind, hbigErrno, hbigMsg⟩ :
      ∃ err, Internal.gatherRandomBytes16
        (countingFixedGetrandomOps (.ok bigChunk))
        Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none 0 = (.error err, 1) ∧
        err.kind = .entropyFailed ∧ err.errnoCode = none ∧ err.message ≠ "" := by
    rw [hmax, gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]
    dsimp only [Bind.bind, StateT.bind]
    rw [countingFixedGetrandomOps_run]
    have hgt : decide (bigChunk.size > 16 - ByteArray.empty.size) = true :=
      decide_eq_true (by change bigChunk.size > 16 - 0; omega)
    dsimp only [Internal.stepRandomBytes16]
    rw [hgt, Bool.or_true]
    simp only [↓reduceIte]
    dsimp only [Pure.pure, StateT.pure]
    exact ⟨_, rfl, rfl, rfl, mapRawError_message_ne_empty _⟩
  rw [heintrStep, hemptyStep, hbigEq]
  refine ⟨⟨rfl, _, rfl, rfl, rfl, mapRawError_message_ne_empty _⟩,
    ⟨rfl, _, rfl, rfl, rfl, mapRawError_message_ne_empty _⟩,
    ⟨rfl, errBig, rfl, hbigKind, hbigErrno, hbigMsg⟩, trivial⟩

/-- Non-vacuity witness for `test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed`. -/
theorem reach_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed :
    CanReach (test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed Internal.mkApiM) :=
  ⟨ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], by decide,
    proof_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed
      (ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]) (by decide)⟩

private theorem fromRandomBytes_error_kind (bs : ByteArray) :
    match LeanSwe.Uuid.fromRandomBytes bs with
    | .error e => e.kind = .invalidLength
    | .ok _ => True := by
  change match Internal.fromRandomBytes bs with | .error e => e.kind = .invalidLength | .ok _ => True
  unfold Internal.fromRandomBytes
  by_cases h : (bs.size != 16)
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

private theorem validateV4BytesList_error_kind (bs : List UInt8) :
    match Internal.validateV4BytesList bs with
    | .error e => e.kind = .invalidFormat ∨ e.kind = .invalidVersion
    | .ok _ => True := by
  unfold Internal.validateV4BytesList
  dsimp only
  by_cases h1 : (ByteArray.mk bs.toArray).size != 16
  · simp only [h1, ↓reduceIte]; simp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : ((ByteArray.mk bs.toArray)[6]! &&& (0xF0 : UInt8)) != (0x40 : UInt8)
    · simp only [h2, ↓reduceIte]; simp
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : ((ByteArray.mk bs.toArray)[8]! &&& (0xC0 : UInt8)) != (0x80 : UInt8)
      · simp only [h3, ↓reduceIte]; simp
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]

private theorem parseHexChars_error_kind (cs : List Char) :
    match Internal.parseHexChars cs with
    | .error e => e.kind = .invalidFormat ∨ e.kind = .invalidVersion
    | .ok _ => True := by
  unfold Internal.parseHexChars
  by_cases h1 : cs.length != 32
  · simp only [h1, ↓reduceIte]; simp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases Internal.decodeHexPairs cs with
    | none => simp
    | some bs => exact validateV4BytesList_error_kind bs

private theorem parseCanonicalChars_error_kind (cs : List Char) :
    match Internal.parseCanonicalChars cs with
    | .error e => e.kind = .invalidFormat ∨ e.kind = .invalidVersion
    | .ok _ => True := by
  unfold Internal.parseCanonicalChars
  by_cases h1 : cs.length != 36
  · simp only [h1, ↓reduceIte]; simp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases Internal.stripCanonicalHyphens cs with
    | none => simp
    | some hex => exact parseHexChars_error_kind hex

private theorem mapRawError_kind (r : UuidRawError) :
    (Internal.mapRawError r).kind = .entropyFailed := by
  cases r <;> rfl

private theorem stepRandomBytes16_error_and_size (acc : ByteArray) (hacc : acc.size ≤ 16)
    (r : Except LeanSwe.LinuxSyscall.Errno ByteArray) :
    match Internal.stepRandomBytes16 (16 - acc.size) acc r with
    | .error err => err.kind = .entropyFailed
    | .ok (.inl bs) => bs.size = 16
    | .ok (.inr (nextAcc, _)) => nextAcc.size ≤ 16 := by
  cases r with
  | error e =>
    dsimp [Internal.stepRandomBytes16]
    by_cases he : e == LeanSwe.LinuxSyscall.Errno.EINTR
    · simp only [he, ↓reduceIte]; exact hacc
    · simp only [he, Bool.false_eq_true, ↓reduceIte]; exact mapRawError_kind _
  | ok chunk =>
    dsimp [Internal.stepRandomBytes16]
    by_cases h0 : chunk.size = 0
    · have hc : (chunk.size == 0 || decide (chunk.size > 16 - acc.size)) = true := by
        simp [h0]
      simp only [hc, ↓reduceIte]
      exact mapRawError_kind _
    · by_cases hgt : chunk.size > 16 - acc.size
      · have hc : (chunk.size == 0 || decide (chunk.size > 16 - acc.size)) = true := by
          simp [hgt]
        simp only [hc, ↓reduceIte]
        exact mapRawError_kind _
      · have hle : chunk.size ≤ 16 - acc.size := by omega
        have hc : (chunk.size == 0 || decide (chunk.size > 16 - acc.size)) = false := by
          have h0f : (chunk.size == 0) = false := beq_false_of_ne h0
          have hgf : decide (chunk.size > 16 - acc.size) = false := decide_eq_false hgt
          rw [h0f, hgf]; rfl
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        by_cases h16 : (Internal.appendBytes acc chunk).size == 16
        · simp only [h16, ↓reduceIte]
          exact beq_iff_eq.mp h16
        · simp only [h16, Bool.false_eq_true, ↓reduceIte]
          rw [appendBytes_size]
          omega

private theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (hx : x w = EST.Out.ok a w') :
    (x >>= f) w = f a w' := by
  change EST.bind x f w = f a w'
  dsimp only [EST.bind]
  rw [hx]

private theorem liftM_baseIO_ok {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = EST.Out.ok a w' := by
  cases h : act w
  exact ⟨_, _, by change EST.Out.ok _ _ = _; rfl⟩

private theorem gatherRandomBytes16_ok_or_entropyFailed
    (sys : LeanSwe.LinuxSyscall.TimeRand.TimeRandOps)
    (hsys : ∀ len flags (w : Void IO.RealWorld),
      ∃ r w', sys.getrandom len flags w = EST.Out.ok r w')
    (fuel : Nat) (acc : ByteArray) (hacc : acc.size ≤ 16)
    (last? : Option LeanSwe.LinuxSyscall.Errno) (w : Void IO.RealWorld) :
    match (Internal.gatherRandomBytes16 sys fuel acc last?) w with
    | EST.Out.ok (.error err) _ => err.kind = .entropyFailed
    | EST.Out.ok (.ok bs) _ => bs.size = 16
    | EST.Out.error _ _ => False := by
  induction fuel generalizing acc last? w with
  | zero =>
    by_cases h16 : acc.size = 16
    · rw [Internal.gatherRandomBytes16.eq_def]
      have hb : (acc.size == 16) = true := beq_iff_eq.mpr h16
      simp only [hb, ↓reduceIte]
      dsimp only [Pure.pure, EST.pure]
      exact h16
    · rw [gatherRandomBytes16_zero_lt _ acc (by omega)]
      cases last? with
      | none => exact mapRawError_kind _
      | some e => exact rfl
  | succ fuel' ih =>
    by_cases h16 : acc.size = 16
    · rw [Internal.gatherRandomBytes16.eq_def]
      have hb : (acc.size == 16) = true := beq_iff_eq.mpr h16
      simp only [hb, ↓reduceIte]
      exact h16
    · rw [gatherRandomBytes16_step_succ _ _ acc (by omega)]
      obtain ⟨r, w', hr⟩ := hsys (UInt32.ofNat (16 - acc.size)) {} w
      rw [io_bind_eq _ _ w hr]
      have hs := stepRandomBytes16_error_and_size acc hacc r
      cases hsRes : Internal.stepRandomBytes16 (16 - acc.size) acc r with
      | error err =>
        rw [hsRes] at hs
        exact hs
      | ok x =>
        cases x with
        | inl bs =>
          rw [hsRes] at hs
          exact hs
        | inr p =>
          rcases p with ⟨nextAcc, nextLast⟩
          rw [hsRes] at hs
          exact ih nextAcc hs nextLast w'

private theorem defaultOps_getrandom_noThrow
    (len : UInt32) (flags : LeanSwe.LinuxSyscall.TimeRand.GrndFlags) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.LinuxSyscall.TimeRand.defaultOps.getrandom len flags w = EST.Out.ok r w' :=
  liftM_baseIO_ok _ w

private theorem getUuid_ok_or_entropyFailed (w : Void IO.RealWorld) :
    match LeanSwe.Uuid.getUuid w with
    | .ok (.error e) _ => e.kind = .entropyFailed
    | .ok (.ok _) _ => True
    | .error _ _ => False := by
  have hgDef : LeanSwe.Uuid.getUuid =
      (Internal.gatherRandomBytes16 LeanSwe.LinuxSyscall.TimeRand.defaultOps
        Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none >>= fun res =>
          match res with
          | .error err => pure (.error err)
          | .ok bs => pure (Internal.fromRandomBytes bs)) := rfl
  rw [hgDef]
  have h := gatherRandomBytes16_ok_or_entropyFailed
    LeanSwe.LinuxSyscall.TimeRand.defaultOps defaultOps_getrandom_noThrow
    Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty (by decide) none w
  cases hg : (Internal.gatherRandomBytes16 LeanSwe.LinuxSyscall.TimeRand.defaultOps
      Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none) w with
  | error e _ =>
    rw [hg] at h
    exact False.elim h
  | ok res w' =>
    rw [hg] at h
    rw [io_bind_eq _ _ w hg]
    cases res with
    | error err => exact h
    | ok bs =>
      have hbs16 : bs.size = 16 := h
      have hbeq : (bs.size == 16) = true := beq_iff_eq.mpr hbs16
      have hne : (bs.size != 16) = false := by
        change (!(bs.size == 16)) = false
        rw [hbeq]
        rfl
      dsimp only [Internal.fromRandomBytes]
      rw [hne]
      trivial

/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.entropyFailed`. -/
theorem uuid_fromRandomBytes_never_entropyFailed (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.fromRandomBytes bs) := by
  have h := fromRandomBytes_error_kind bs
  dsimp [NeverErrorKindPure]
  cases hf : LeanSwe.Uuid.fromRandomBytes bs with
  | ok _ => trivial
  | error e => rw [hf] at h; dsimp only; rw [h]; decide

/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.invalidFormat`. -/
theorem uuid_fromRandomBytes_never_invalidFormat (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .invalidFormat (LeanSwe.Uuid.fromRandomBytes bs) := by
  have h := fromRandomBytes_error_kind bs
  dsimp [NeverErrorKindPure]
  cases hf : LeanSwe.Uuid.fromRandomBytes bs with
  | ok _ => trivial
  | error e => rw [hf] at h; dsimp only; rw [h]; decide

/-- Proof that `LeanSwe.Uuid.fromRandomBytes` never returns `.invalidVersion`. -/
theorem uuid_fromRandomBytes_never_invalidVersion (bs : ByteArray) :
    NeverErrorKindPure UuidError.kind .invalidVersion (LeanSwe.Uuid.fromRandomBytes bs) := by
  have h := fromRandomBytes_error_kind bs
  dsimp [NeverErrorKindPure]
  cases hf : LeanSwe.Uuid.fromRandomBytes bs with
  | ok _ => trivial
  | error e => rw [hf] at h; dsimp only; rw [h]; decide

/-- Proof that `LeanSwe.Uuid.parse` never returns `.entropyFailed`. -/
theorem uuid_parse_never_entropyFailed (s : String) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.parse s) := by
  have h := parseCanonicalChars_error_kind s.toList
  dsimp [NeverErrorKindPure, LeanSwe.Uuid.parse, LeanSwe.Uuid.defaultApi,
    Internal.mkApi, Internal.parse] at h ⊢
  cases hp : Internal.parseCanonicalChars s.toList with
  | ok _ => trivial
  | error e =>
    rw [hp] at h
    dsimp only
    rcases h with h1 | h2
    · rw [h1]; decide
    · rw [h2]; decide

/-- Proof that `LeanSwe.Uuid.parse` never returns `.invalidLength`. -/
theorem uuid_parse_never_invalidLength (s : String) :
    NeverErrorKindPure UuidError.kind .invalidLength (LeanSwe.Uuid.parse s) := by
  have h := parseCanonicalChars_error_kind s.toList
  dsimp [NeverErrorKindPure, LeanSwe.Uuid.parse, LeanSwe.Uuid.defaultApi,
    Internal.mkApi, Internal.parse] at h ⊢
  cases hp : Internal.parseCanonicalChars s.toList with
  | ok _ => trivial
  | error e =>
    rw [hp] at h
    dsimp only
    rcases h with h1 | h2
    · rw [h1]; decide
    · rw [h2]; decide

/-- Proof that `LeanSwe.Uuid.parseHex` never returns `.entropyFailed`. -/
theorem uuid_parseHex_never_entropyFailed (s : String) :
    NeverErrorKindPure UuidError.kind .entropyFailed (LeanSwe.Uuid.parseHex s) := by
  have h := parseHexChars_error_kind s.toList
  dsimp [NeverErrorKindPure, LeanSwe.Uuid.parseHex, LeanSwe.Uuid.defaultApi,
    Internal.mkApi, Internal.parseHex] at h ⊢
  cases hp : Internal.parseHexChars s.toList with
  | ok _ => trivial
  | error e =>
    rw [hp] at h
    dsimp only
    rcases h with h1 | h2
    · rw [h1]; decide
    · rw [h2]; decide

/-- Proof that `LeanSwe.Uuid.parseHex` never returns `.invalidLength`. -/
theorem uuid_parseHex_never_invalidLength (s : String) :
    NeverErrorKindPure UuidError.kind .invalidLength (LeanSwe.Uuid.parseHex s) := by
  have h := parseHexChars_error_kind s.toList
  dsimp [NeverErrorKindPure, LeanSwe.Uuid.parseHex, LeanSwe.Uuid.defaultApi,
    Internal.mkApi, Internal.parseHex] at h ⊢
  cases hp : Internal.parseHexChars s.toList with
  | ok _ => trivial
  | error e =>
    rw [hp] at h
    dsimp only
    rcases h with h1 | h2
    · rw [h1]; decide
    · rw [h2]; decide

/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidLength`. -/
theorem uuid_getUuid_never_invalidLength (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidLength LeanSwe.Uuid.getUuid w := by
  have h := getUuid_ok_or_entropyFailed w
  dsimp [NeverErrorKindIO]
  cases hg : LeanSwe.Uuid.getUuid w with
  | ok res _ =>
    rw [hg] at h
    cases res with
    | ok _ => trivial
    | error e => dsimp only; rw [h]; decide
  | error _ _ => rw [hg] at h; exact False.elim h

/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidFormat`. -/
theorem uuid_getUuid_never_invalidFormat (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidFormat LeanSwe.Uuid.getUuid w := by
  have h := getUuid_ok_or_entropyFailed w
  dsimp [NeverErrorKindIO]
  cases hg : LeanSwe.Uuid.getUuid w with
  | ok res _ =>
    rw [hg] at h
    cases res with
    | ok _ => trivial
    | error e => dsimp only; rw [h]; decide
  | error _ _ => rw [hg] at h; exact False.elim h

/-- Proof that `LeanSwe.Uuid.getUuid` never returns `.invalidVersion`. -/
theorem uuid_getUuid_never_invalidVersion (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidVersion LeanSwe.Uuid.getUuid w := by
  have h := getUuid_ok_or_entropyFailed w
  dsimp [NeverErrorKindIO]
  cases hg : LeanSwe.Uuid.getUuid w with
  | ok res _ =>
    rw [hg] at h
    cases res with
    | ok _ => trivial
    | error e => dsimp only; rw [h]; decide
  | error _ _ => rw [hg] at h; exact False.elim h

/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidLength`. -/
theorem uuid_v4_never_invalidLength (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidLength LeanSwe.Uuid.v4 w :=
  uuid_getUuid_never_invalidLength w

/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidFormat`. -/
theorem uuid_v4_never_invalidFormat (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidFormat LeanSwe.Uuid.v4 w :=
  uuid_getUuid_never_invalidFormat w

/-- Proof that `LeanSwe.Uuid.v4` never returns `.invalidVersion`. -/
theorem uuid_v4_never_invalidVersion (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind .invalidVersion LeanSwe.Uuid.v4 w :=
  uuid_getUuid_never_invalidVersion w

end LeanSwe.Uuid.Proofs


