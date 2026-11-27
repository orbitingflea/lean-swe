import Lean.Data.Json.Basic
import LeanSwe.Json.Impl
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex
import LeanSwe.Json.Proofs.Utf8Ws

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- `String.fromUTF8? acc = some s` holds iff `acc = s.toByteArray`. -/
theorem fromUTF8?_eq_some_iff {acc : ByteArray} {s : String} :
    String.fromUTF8? acc = some s ↔ acc = s.toByteArray := by
  constructor
  · intro h
    simp only [String.fromUTF8?] at h
    split at h <;> simp at h
    subst h
    rfl
  · rintro rfl
    simp only [String.fromUTF8?, s.isValidUTF8, ↓reduceDIte, Option.some.injEq, ← String.toByteArray_inj]
    rfl

/-- `(Char.ofNat n).toNat = n` for any valid Unicode scalar value `n`. -/
theorem char_toNat_ofNat_valid {n : Nat} (h : n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat Char.ofNatAux
  have hv : n.isValidChar := h
  simp only [hv, ↓reduceDIte]
  rfl

/-- `pushUtf8Char acc c` equals `acc ++ [c].utf8Encode`. -/
theorem pushUtf8Char_eq_utf8Encode (acc : ByteArray) (c : Char) :
    pushUtf8Char acc c = acc ++ [c].utf8Encode := by
  rw [List.utf8Encode_singleton, String.utf8EncodeChar_eq_utf8EncodeCharFast]
  unfold pushUtf8Char String.utf8EncodeCharFast
  dsimp only
  split
  · apply ByteArray.ext; apply Array.ext'; simp
  · split
    · apply ByteArray.ext; apply Array.ext'; simp
    · split
      · apply ByteArray.ext; apply Array.ext'; simp
      · apply ByteArray.ext; apply Array.ext'; simp

/-- Check whether `c` is an uppercase hexadecimal character `'A'..'F'`. -/
def isUpperHexChar (c : Char) : Bool :=
  'A' ≤ c && c ≤ 'F'

/-- `renderHexNibble` always produces an ASCII character `< 0x80` inverted by `hexValByte?`. -/
theorem renderHexNibble_ascii_hexVal (upper : Bool) {n : Nat} (hn : n < 16) :
    (renderHexNibble upper n).toNat < 0x80 ∧
      hexValByte? (renderHexNibble upper n).val.toUInt8 = some n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
    cases upper <;> decide
  | _ + 16 => omega

/-- Any byte `b` accepted by `hexValByte?` is `< 0x80` and matches `renderHexNibble` with `isUpperHexChar`. -/
theorem hexValByte?_some_spec {b : UInt8} {d : Nat} (h : hexValByte? b = some d) :
    b < 0x80 ∧ d < 16 ∧
      ∀ {c : Char}, c.toNat = b.toNat → renderHexNibble (isUpperHexChar c) d = c := by
  unfold hexValByte? at h
  by_cases h1 : (0x30 ≤ b && b ≤ 0x39) = true
  · rw [ite_eq_left h1] at h; injection h with hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h1
    change 48 ≤ b.toNat ∧ b.toNat ≤ 57 at h1
    have hb80 : b < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; change b.toNat < 128; omega
    refine ⟨hb80, by omega, fun {c} hc => ?_⟩
    have hlt10 : d < 10 := by omega
    simp only [renderHexNibble, hlt10, ↓reduceIte]
    apply Char.ext; apply UInt32.toNat_inj.mp
    change (Char.ofNat (0x30 + d)).toNat = c.toNat
    rw [char_toNat_ofNat_valid (Or.inl (by omega)), hc]; omega
  · rw [ite_eq_right h1] at h
    by_cases h2 : (0x61 ≤ b && b ≤ 0x66) = true
    · rw [ite_eq_left h2] at h; injection h with hd
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h2
      change 97 ≤ b.toNat ∧ b.toNat ≤ 102 at h2
      have hb80 : b < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; change b.toNat < 128; omega
      refine ⟨hb80, by omega, fun {c} hc => ?_⟩
      have hnot10 : ¬(d < 10) := by omega
      have hup : isUpperHexChar c = false := by
        unfold isUpperHexChar
        rw [Bool.eq_false_iff, Ne, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
          Char.le_def, Char.le_def, UInt32.le_iff_toNat_le, UInt32.le_iff_toNat_le]
        change ¬(0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46); omega
      simp only [renderHexNibble, hnot10, hup, Bool.false_eq_true, ↓reduceIte]
      apply Char.ext; apply UInt32.toNat_inj.mp
      change (Char.ofNat (0x61 + (d - 10))).toNat = c.toNat
      rw [char_toNat_ofNat_valid (Or.inl (by omega)), hc]; omega
    · rw [ite_eq_right h2] at h
      by_cases h3 : (0x41 ≤ b && b ≤ 0x46) = true
      · rw [ite_eq_left h3] at h; injection h with hd
        simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at h3
        change 65 ≤ b.toNat ∧ b.toNat ≤ 70 at h3
        have hb80 : b < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; change b.toNat < 128; omega
        refine ⟨hb80, by omega, fun {c} hc => ?_⟩
        have hnot10 : ¬(d < 10) := by omega
        have hup : isUpperHexChar c = true := by
          unfold isUpperHexChar
          simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le]
          change 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x46; omega
        simp only [renderHexNibble, hnot10, hup, ↓reduceIte]
        apply Char.ext; apply UInt32.toNat_inj.mp
        change (Char.ofNat (0x41 + (d - 10))).toNat = c.toNat
        rw [char_toNat_ofNat_valid (Or.inl (by omega)), hc]; omega
      · rw [ite_eq_right h3] at h; cases h

/-- Soundness of `parseHex4?` on the four hex characters of `renderHex4`. -/
theorem parseHex4?_of_renderHex4 {bytes : ByteArray} {pos : Nat} (casing : HexCase4)
    {u16 : Nat} (hu : u16 < 0x10000) {after : List Char}
    (hSlice : ByteSliceAt bytes pos
      (renderHexNibble casing.u0 ((u16 / 4096) % 16) ::
       renderHexNibble casing.u1 ((u16 / 256) % 16) ::
       renderHexNibble casing.u2 ((u16 / 16) % 16) ::
       renderHexNibble casing.u3 (u16 % 16) :: after)) :
    parseHex4? bytes pos = some u16 ∧ ByteSliceAt bytes (pos + 4) after := by
  obtain ⟨ha0, hv0⟩ := renderHexNibble_ascii_hexVal casing.u0 (Nat.mod_lt (u16 / 4096) (by decide))
  obtain ⟨ha1, hv1⟩ := renderHexNibble_ascii_hexVal casing.u1 (Nat.mod_lt (u16 / 256) (by decide))
  obtain ⟨ha2, hv2⟩ := renderHexNibble_ascii_hexVal casing.u2 (Nat.mod_lt (u16 / 16) (by decide))
  obtain ⟨ha3, hv3⟩ := renderHexNibble_ascii_hexVal casing.u3 (Nat.mod_lt u16 (by decide))
  obtain ⟨hlt0, hg0, hs1⟩ := byteSliceAt_ascii_cons hSlice ha0
  obtain ⟨hlt1, hg1, hs2⟩ := byteSliceAt_ascii_cons hs1 ha1
  rw [show pos + 1 + 1 = pos + 2 by omega] at hs2
  obtain ⟨hlt2, hg2, hs3⟩ := byteSliceAt_ascii_cons hs2 ha2
  rw [show pos + 2 + 1 = pos + 3 by omega] at hs3
  obtain ⟨hlt3, hg3, hs4⟩ := byteSliceAt_ascii_cons hs3 ha3
  have hbnd : pos + 4 ≤ bytes.size := by omega
  refine ⟨?_, by simpa [Nat.add_assoc] using hs4⟩
  unfold parseHex4?
  simp only [hbnd, ↓reduceDIte, hg0, hg1, hg2, hg3, hv0, hv1, hv2, hv3, bind, Option.bind, Option.some.injEq]
  omega

/-- Completeness of `parseHex4?` on `ByteSliceAt`, recovering `HexCase4` and advancing by 4 bytes. -/
theorem parseHex4?_complete {bytes : ByteArray} {pos : Nat} {cs : List Char} {u16 : Nat}
    (hSlice : ByteSliceAt bytes pos cs) (hHex : parseHex4? bytes pos = some u16) :
    ∃ (casing : HexCase4) (c0 c1 c2 c3 : Char) (rest : List Char),
      u16 < 0x10000 ∧
      cs = c0 :: c1 :: c2 :: c3 :: rest ∧
      renderHex4 casing u16 = ['\\', 'u', c0, c1, c2, c3] ∧
      ByteSliceAt bytes (pos + 4) rest := by
  unfold parseHex4? at hHex
  split at hHex <;> try cases hHex
  rename_i hbnd
  simp only [bind, Option.bind] at hHex
  cases hd0 : hexValByte? (bytes[pos]'(by omega)) <;> simp [hd0] at hHex
  cases hd1 : hexValByte? (bytes[pos + 1]'(by omega)) <;> simp [hd1] at hHex
  cases hd2 : hexValByte? (bytes[pos + 2]'(by omega)) <;> simp [hd2] at hHex
  cases hd3 : hexValByte? (bytes[pos + 3]'(by omega)) <;> simp [hd3] at hHex
  rename_i d0 d1 d2 d3
  subst hHex
  obtain ⟨hb0, hlt0, hr0⟩ := hexValByte?_some_spec hd0
  obtain ⟨hb1, hlt1, hr1⟩ := hexValByte?_some_spec hd1
  obtain ⟨hb2, hlt2, hr2⟩ := hexValByte?_some_spec hd2
  obtain ⟨hb3, hlt3, hr3⟩ := hexValByte?_some_spec hd3
  obtain ⟨c0, r0, rfl, hc0, _, hs1⟩ := byteSliceAt_head_lt_128 hSlice (by omega) hb0
  obtain ⟨c1, r1, rfl, hc1, _, hs2⟩ := byteSliceAt_head_lt_128 hs1 (by omega) hb1
  have hs2' : ByteSliceAt bytes (pos + 2) r1 := by simpa [Nat.add_assoc] using hs2
  obtain ⟨c2, r2, rfl, hc2, _, hs3⟩ := byteSliceAt_head_lt_128 hs2' (by omega) hb2
  have hs3' : ByteSliceAt bytes (pos + 3) r2 := by simpa [Nat.add_assoc] using hs3
  obtain ⟨c3, r3, rfl, hc3, _, hs4⟩ := byteSliceAt_head_lt_128 hs3' (by omega) hb3
  let u16Val := d0 * 4096 + d1 * 256 + d2 * 16 + d3
  have hd0Eq : (u16Val / 4096) % 16 = d0 := by omega
  have hd1Eq : (u16Val / 256) % 16 = d1 := by omega
  have hd2Eq : (u16Val / 16) % 16 = d2 := by omega
  have hd3Eq : u16Val % 16 = d3 := by omega
  refine ⟨⟨isUpperHexChar c0, isUpperHexChar c1, isUpperHexChar c2, isUpperHexChar c3⟩,
    c0, c1, c2, c3, r3, by omega, rfl, ?_, by simpa [Nat.add_assoc] using hs4⟩
  rw [renderHex4, hd0Eq, hd1Eq, hd2Eq, hd3Eq, hr0 hc0, hr1 hc1, hr2 hc2, hr3 hc3]

/-- Every UTF-8 byte of a valid unescaped JSON string character (`0x20 ≤ c.toNat`, `c ≠ '"'`, `c ≠ '\\'`) is raw-safe. -/
theorem utf8EncodeChar_raw_safe {c : Char} (hge : 0x20 ≤ c.toNat) (hq : c ≠ '"') (hb : c ≠ '\\') :
    ∀ b ∈ String.utf8EncodeChar c, ¬(b < 0x20) ∧ (b == 0x22) = false ∧ (b == 0x5c) = false := by
  by_cases hascii : c.toNat < 0x80
  · have hc1 : c.utf8Size = 1 := by
      simp only [Char.utf8Size]
      have hle : c.val ≤ 0x7f := by rw [UInt32.le_iff_toNat_le]; change c.toNat ≤ 0x7f; omega
      simp [hle]
    rw [String.utf8EncodeChar_eq_singleton hc1]
    intro b hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    have htoNat : c.val.toUInt8.toNat = c.toNat := by
      rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [UInt8.lt_iff_toNat_lt, htoNat]; change ¬(c.toNat < 0x20); omega
    · apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, htoNat]
      intro heq; exact hq (Char.ext (UInt32.toNat_inj.mp heq))
    · apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj, htoNat]
      intro heq; exact hb (Char.ext (UInt32.toNat_inj.mp heq))
  · intro b hmem
    have h128 := utf8EncodeChar_nonAscii_ge_128 (by omega) b hmem
    rw [UInt8.le_iff_toNat_le] at h128
    refine ⟨?_, ?_, ?_⟩
    · rw [UInt8.lt_iff_toNat_lt]; change ¬(b.toNat < 32); change 128 ≤ b.toNat at h128; omega
    · apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj]; change b.toNat ≠ 34; change 128 ≤ b.toNat at h128; omega
    · apply Bool.eq_false_iff.mpr; rw [Ne, beq_iff_eq, ← UInt8.toNat_inj]; change b.toNat ≠ 92; change 128 ≤ b.toNat at h128; omega

/-- `parseStringBody` steps across any list of raw-safe bytes, appending `bs.toByteArray` onto `acc`. -/
theorem parseStringBody_rawByteList :
    ∀ (bs : List UInt8) (pre suf acc : ByteArray),
      (∀ b ∈ bs, ¬(b < 0x20) ∧ (b == 0x22) = false ∧ (b == 0x5c) = false) →
      parseStringBody (pre ++ bs.toByteArray ++ suf) pre.size acc =
        parseStringBody (pre ++ bs.toByteArray ++ suf) (pre.size + bs.length) (acc ++ bs.toByteArray)
  | [], pre, suf, acc, _ => by simp [ByteArray.append_empty]
  | b :: btl, pre, suf, acc, hsafe => by
    obtain ⟨hge20, hne22, hne5c⟩ := hsafe b List.mem_cons_self
    have hbytes : pre ++ (b :: btl).toByteArray ++ suf =
        (pre ++ [b].toByteArray) ++ btl.toByteArray ++ suf := by
      apply ByteArray.ext; apply Array.ext'; simp
    have hlt : pre.size < (pre ++ (b :: btl).toByteArray ++ suf).size := by
      simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons]; omega
    have hget : (pre ++ (b :: btl).toByteArray ++ suf)[pre.size]'hlt = b := by
      rw [ByteArray.getElem_append_left (hlt := by simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons]; omega)]
      rw [ByteArray.getElem_append_right (hle := Nat.le_refl _)]
      simp
    conv => lhs; unfold parseStringBody
    simp only [hlt, ↓reduceDIte, hget, hne22, hge20, hne5c, Bool.false_eq_true, ↓reduceIte]
    rw [← ByteArray.append_toByteArray_singleton, hbytes]
    have hpreSz : (pre ++ [b].toByteArray).size = pre.size + 1 := by
      simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons, List.length_nil]
    rw [← hpreSz, parseStringBody_rawByteList btl (pre ++ [b].toByteArray) suf (acc ++ [b].toByteArray)
      (fun x hx => hsafe x (List.mem_cons_of_mem _ hx))]
    have hposEq : (pre ++ [b].toByteArray).size + btl.length = pre.size + (b :: btl).length := by
      rw [hpreSz, List.length_cons]; omega
    have haccEq : (acc ++ [b].toByteArray) ++ btl.toByteArray = acc ++ (b :: btl).toByteArray := by
      apply ByteArray.ext; apply Array.ext'; simp
    rw [hposEq, haccEq]

/-- Single-character raw step for `parseStringBody` on `ByteSliceAt bytes pos (c :: rest)`. -/
theorem parseStringBody_rawChar_step {bytes : ByteArray} {pos : Nat} {c : Char} {rest : List Char}
    (hSlice : ByteSliceAt bytes pos (c :: rest)) (acc : ByteArray)
    (hge : 0x20 ≤ c.toNat) (hq : c ≠ '"') (hb : c ≠ '\\') :
    parseStringBody bytes pos acc =
        parseStringBody bytes (pos + [c].utf8Encode.size) (acc ++ [c].utf8Encode) ∧
      ByteSliceAt bytes (pos + [c].utf8Encode.size) rest := by
  refine ⟨?_, byteSliceAt_append_chars (mid := [c]) hSlice⟩
  rcases hSlice with ⟨pre, rfl, rfl⟩
  rw [List.utf8Encode_cons, List.utf8Encode_singleton, ← ByteArray.append_assoc, List.size_toByteArray]
  exact parseStringBody_rawByteList (String.utf8EncodeChar c) pre rest.utf8Encode acc
    (utf8EncodeChar_raw_safe hge hq hb)

/-- Soundness of `parseStringBody` on a rendered `CharEscapeStyle` fragment. -/
theorem parseStringBody_renderCharWithStyle {bytes : ByteArray} {pos : Nat}
    (c : Char) (st : CharEscapeStyle) {frag : List Char} (after : List Char) (acc : ByteArray)
    (hr : renderCharWithStyle c st = some frag)
    (hSlice : ByteSliceAt bytes pos (frag ++ after)) :
    ∃ nextPos,
      parseStringBody bytes pos acc = parseStringBody bytes nextPos (acc ++ [c].utf8Encode) ∧
      ByteSliceAt bytes nextPos after := by
  cases st with
  | raw =>
    simp only [renderCharWithStyle, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hr
    split at hr <;> cases hr
    rename_i hcond
    rcases hcond with ⟨⟨hge, hq⟩, hb⟩
    obtain ⟨hEq, hNext⟩ := parseStringBody_rawChar_step hSlice acc hge hq hb
    exact ⟨_, hEq, hNext⟩
  | shortEscape =>
    have hShort : ∀ (esc : Char) (chByte : UInt8),
        frag = ['\\', esc] → esc.toNat < 0x80 → c.toNat < 0x80 → c.val.toUInt8 = chByte →
        (if esc.val.toUInt8 == 0x22 then some (0x22 : UInt8)
         else if esc.val.toUInt8 == 0x5c then some 0x5c
         else if esc.val.toUInt8 == 0x2f then some 0x2f
         else if esc.val.toUInt8 == 0x62 then some 0x08
         else if esc.val.toUInt8 == 0x66 then some 0x0c
         else if esc.val.toUInt8 == 0x6e then some 0x0a
         else if esc.val.toUInt8 == 0x72 then some 0x0d
         else if esc.val.toUInt8 == 0x74 then some 0x09
         else none) = some chByte →
        ∃ nextPos,
          parseStringBody bytes pos acc = parseStringBody bytes nextPos (acc ++ [c].utf8Encode) ∧
          ByteSliceAt bytes nextPos after := by
      intro esc chByte hfrag hescA hcA hchEq hsimp
      subst hfrag
      obtain ⟨hlt0, hg0, hs1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
      obtain ⟨hlt1, hg1, hs2⟩ := byteSliceAt_ascii_cons hs1 hescA
      have hc1 : c.utf8Size = 1 := by
        simp only [Char.utf8Size]
        have hle : c.val ≤ 0x7f := by rw [UInt32.le_iff_toNat_le]; change c.toNat ≤ 0x7f; omega
        simp [hle]
      have henc : acc.push chByte = acc ++ [c].utf8Encode := by
        rw [← hchEq, ← ByteArray.append_toByteArray_singleton, List.utf8Encode_singleton,
          String.utf8EncodeChar_eq_singleton hc1]
      refine ⟨pos + 2, ?_, by simpa [Nat.add_assoc] using hs2⟩
      conv => lhs; unfold parseStringBody
      have hb0 : ('\\').val.toUInt8 = 0x5c := rfl
      simp only [hlt0, hlt1, ↓reduceDIte, hg0, hg1, hb0,
        (by decide : ((0x5c : UInt8) == 0x22) = false),
        (by decide : ¬((0x5c : UInt8) < 0x20)),
        (by decide : ((0x5c : UInt8) == 0x5c) = true), Bool.false_eq_true, ↓reduceIte, hsimp, henc]
    unfold renderCharWithStyle at hr
    by_cases h1 : c == '"'; · rw [ite_eq_left h1] at hr; cases hr; have hcEq := beq_iff_eq.mp h1; subst hcEq; exact hShort '"' 0x22 rfl (by decide) (by decide) rfl rfl
    · rw [ite_eq_right h1] at hr
      by_cases h2 : c == '\\'; · rw [ite_eq_left h2] at hr; cases hr; have hcEq := beq_iff_eq.mp h2; subst hcEq; exact hShort '\\' 0x5c rfl (by decide) (by decide) rfl rfl
      · rw [ite_eq_right h2] at hr
        by_cases h3 : c == '/'; · rw [ite_eq_left h3] at hr; cases hr; have hcEq := beq_iff_eq.mp h3; subst hcEq; exact hShort '/' 0x2f rfl (by decide) (by decide) rfl rfl
        · rw [ite_eq_right h3] at hr
          by_cases h4 : c == '\x08'; · rw [ite_eq_left h4] at hr; cases hr; have hcEq := beq_iff_eq.mp h4; subst hcEq; exact hShort 'b' 0x08 rfl (by decide) (by decide) rfl rfl
          · rw [ite_eq_right h4] at hr
            by_cases h5 : c == '\x0c'; · rw [ite_eq_left h5] at hr; cases hr; have hcEq := beq_iff_eq.mp h5; subst hcEq; exact hShort 'f' 0x0c rfl (by decide) (by decide) rfl rfl
            · rw [ite_eq_right h5] at hr
              by_cases h6 : c == '\n'; · rw [ite_eq_left h6] at hr; cases hr; have hcEq := beq_iff_eq.mp h6; subst hcEq; exact hShort 'n' 0x0a rfl (by decide) (by decide) rfl rfl
              · rw [ite_eq_right h6] at hr
                by_cases h7 : c == '\r'; · rw [ite_eq_left h7] at hr; cases hr; have hcEq := beq_iff_eq.mp h7; subst hcEq; exact hShort 'r' 0x0d rfl (by decide) (by decide) rfl rfl
                · rw [ite_eq_right h7] at hr
                  by_cases h8 : c == '\t'; · rw [ite_eq_left h8] at hr; cases hr; have hcEq := beq_iff_eq.mp h8; subst hcEq; exact hShort 't' 0x09 rfl (by decide) (by decide) rfl rfl
                  · rw [ite_eq_right h8] at hr; cases hr
  | unicodeHex casing =>
    simp only [renderCharWithStyle] at hr
    split at hr <;> cases hr
    rename_i hltBmp
    have hv : ¬(0xD800 ≤ c.toNat ∧ c.toNat < 0xDC00) ∧ ¬(0xDC00 ≤ c.toNat ∧ c.toNat < 0xE000) := by
      rcases char_toNat_valid_bounds c with h1 | ⟨h2, _⟩ <;> omega
    simp only [renderHex4, List.cons_append, List.nil_append] at hSlice
    obtain ⟨hlt0, hg0, hs1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
    obtain ⟨hlt1, hg1, hs2⟩ := byteSliceAt_ascii_cons hs1 (by decide)
    rw [show pos + 1 + 1 = pos + 2 by omega] at hs2
    obtain ⟨hHex, hs6⟩ := parseHex4?_of_renderHex4 casing hltBmp hs2
    refine ⟨pos + 6, ?_, by simpa [Nat.add_assoc] using hs6⟩
    conv => lhs; unfold parseStringBody
    have hb0 : ('\\').val.toUInt8 = 0x5c := rfl
    have hb1 : ('u').val.toUInt8 = 0x75 := rfl
    simp only [hlt0, hlt1, ↓reduceDIte, hg0, hg1, hb0, hb1,
      (by decide : ((0x5c : UInt8) == 0x22) = false),
      (by decide : ¬((0x5c : UInt8) < 0x20)),
      (by decide : ((0x5c : UInt8) == 0x5c) = true),
      (by decide : ((0x75 : UInt8) == 0x22) = false),
      (by decide : ((0x75 : UInt8) == 0x5c) = false),
      (by decide : ((0x75 : UInt8) == 0x2f) = false),
      (by decide : ((0x75 : UInt8) == 0x62) = false),
      (by decide : ((0x75 : UInt8) == 0x66) = false),
      (by decide : ((0x75 : UInt8) == 0x6e) = false),
      (by decide : ((0x75 : UInt8) == 0x72) = false),
      (by decide : ((0x75 : UInt8) == 0x74) = false),
      (by decide : ((0x75 : UInt8) == 0x75) = true), Bool.false_eq_true, ↓reduceIte,
      hHex, Bool.and_eq_true, decide_eq_true_eq, hv.1, hv.2, Char.ofNat_toNat,
      pushUtf8Char_eq_utf8Encode]
  | surrogatePair hiCase loCase =>
    simp only [renderCharWithStyle] at hr
    split at hr <;> cases hr
    rename_i hgeSup
    have hltMax : c.toNat < 0x110000 := by
      rcases char_toNat_valid_bounds c with h1 | ⟨_, h2⟩ <;> omega
    let v := c.toNat - 0x10000
    let hi := 0xD800 + v / 1024
    let lo := 0xDC00 + v % 1024
    have hhiLt : hi < 0x10000 := by omega
    have hloLt : lo < 0x10000 := by omega
    have hhiRange : 0xD800 ≤ hi ∧ hi < 0xDC00 := by omega
    have hloRange : 0xDC00 ≤ lo ∧ lo < 0xE000 := by omega
    have hcp : 0x10000 + (hi - 0xD800) * 1024 + (lo - 0xDC00) = c.toNat := by omega
    simp only [renderHex4, List.cons_append, List.nil_append] at hSlice
    obtain ⟨hlt0, hg0, hs1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
    obtain ⟨hlt1, hg1, hs2⟩ := byteSliceAt_ascii_cons hs1 (by decide)
    rw [show pos + 1 + 1 = pos + 2 by omega] at hs2
    obtain ⟨hHexHi, hs6⟩ := parseHex4?_of_renderHex4 hiCase hhiLt hs2
    rw [show pos + 2 + 4 = pos + 6 by omega] at hs6
    obtain ⟨hlt6, hg6, hs7⟩ := byteSliceAt_ascii_cons hs6 (by decide)
    rw [show pos + 6 + 1 = pos + 7 by omega] at hs7
    obtain ⟨hlt7, hg7, hs8⟩ := byteSliceAt_ascii_cons hs7 (by decide)
    rw [show pos + 7 + 1 = pos + 8 by omega] at hs8
    obtain ⟨hHexLo, hs12⟩ := parseHex4?_of_renderHex4 loCase hloLt hs8
    rw [show pos + 8 + 4 = pos + 12 by omega] at hs12
    have hPairBnd : pos + 12 ≤ bytes.size := by have := byteSliceAt_size hs12; omega
    refine ⟨pos + 12, ?_, hs12⟩
    conv => lhs; unfold parseStringBody
    have hb0 : ('\\').val.toUInt8 = 0x5c := rfl
    have hb1 : ('u').val.toUInt8 = 0x75 := rfl
    simp only [hlt0, hlt1, hPairBnd, ↓reduceDIte, hg0, hg1, hg6, hg7, hb0, hb1,
      (by decide : ((0x5c : UInt8) == 0x22) = false),
      (by decide : ¬((0x5c : UInt8) < 0x20)),
      (by decide : ((0x5c : UInt8) == 0x5c) = true),
      (by decide : ((0x75 : UInt8) == 0x22) = false),
      (by decide : ((0x75 : UInt8) == 0x5c) = false),
      (by decide : ((0x75 : UInt8) == 0x2f) = false),
      (by decide : ((0x75 : UInt8) == 0x62) = false),
      (by decide : ((0x75 : UInt8) == 0x66) = false),
      (by decide : ((0x75 : UInt8) == 0x6e) = false),
      (by decide : ((0x75 : UInt8) == 0x72) = false),
      (by decide : ((0x75 : UInt8) == 0x74) = false),
      (by decide : ((0x75 : UInt8) == 0x75) = true), Bool.false_eq_true, ↓reduceIte,
      hHexHi, hHexLo, Bool.and_eq_true, decide_eq_true_eq, hhiRange, hloRange, and_self,
      hcp, Char.ofNat_toNat, pushUtf8Char_eq_utf8Encode]

/-- Soundness of `parseStringBody` across `renderStringChars`. -/
theorem parseStringBody_renderStringChars :
    ∀ (cs : List Char) (styles : List CharEscapeStyle) {body : List Char},
      renderStringChars cs styles = some body →
      ∀ {bytes : ByteArray} {pos : Nat} (pref after : List Char),
        ByteSliceAt bytes pos (body ++ '"' :: after) →
        ∃ endPos,
          parseStringBody bytes pos pref.utf8Encode = .ok (String.ofList (pref ++ cs), endPos) ∧
          pos < endPos ∧ endPos ≤ bytes.size ∧
          ByteSliceAt bytes endPos after
  | [], [], _, hr, bytes, pos, pref, after, hSlice => by
    simp only [renderStringChars, Option.some.injEq] at hr
    subst hr
    simp only [List.nil_append, List.append_nil] at hSlice ⊢
    obtain ⟨hlt, hget, hsNext⟩ := byteSliceAt_ascii_cons hSlice (by decide)
    have hfrom : String.fromUTF8? pref.utf8Encode = some (String.ofList pref) :=
      fromUTF8?_eq_some_iff.mpr String.toByteArray_ofList.symm
    refine ⟨pos + 1, ?_, by omega, by omega, hsNext⟩
    unfold parseStringBody
    simp [hlt, hget, hfrom]
  | c :: cs, st :: sts, _, hr, bytes, pos, pref, after, hSlice => by
    simp only [renderStringChars, bind, Option.bind] at hr
    cases hc : renderCharWithStyle c st with
    | none => simp [hc] at hr
    | some hd =>
      cases htl : renderStringChars cs sts with
      | none => simp [hc, htl] at hr
      | some tl =>
        simp only [hc, htl, Option.some.injEq] at hr
        subst hr
        rw [List.append_assoc] at hSlice
        obtain ⟨midPos, hstep, hMidSlice⟩ := parseStringBody_renderCharWithStyle c st (tl ++ '"' :: after) pref.utf8Encode hc hSlice
        rw [← List.utf8Encode_append] at hstep
        obtain ⟨endPos, hEnd, hLt, hLe, hAfterSlice⟩ :=
          parseStringBody_renderStringChars cs sts htl (pref ++ [c]) after hMidSlice
        have hGe : pos ≤ midPos := by
          have hs1 := byteSliceAt_size hSlice
          have hs2 := byteSliceAt_size hMidSlice
          rw [List.utf8Encode_append, ByteArray.size_append] at hs1
          omega
        refine ⟨endPos, ?_, by omega, hLe, hAfterSlice⟩
        rw [hstep]
        simpa [List.append_assoc] using hEnd
  | [], _ :: _, _, hr, _, _, _, _, _ => by simp [renderStringChars] at hr
  | _ :: _, [], _, hr, _, _, _, _, _ => by simp [renderStringChars] at hr

/-- Soundness of `parseStringAt` on any rendered string literal `renderStringLiteral s styles = some lit`. -/
theorem parseStringAt_of_renderStringLiteral {bytes : ByteArray} {pos : Nat}
    {s : String} {styles : List CharEscapeStyle} {lit : String} (after : List Char)
    (hr : renderStringLiteral s styles = some lit)
    (hSlice : ByteSliceAt bytes pos (lit.toList ++ after)) :
    ∃ pSub, parseStringAt bytes pos = .ok (s, pSub) ∧ ByteSliceAt bytes pSub.1 after := by
  simp only [renderStringLiteral, bind, Option.bind] at hr
  cases hb : renderStringChars s.toList styles with
  | none => simp [hb] at hr
  | some body =>
    simp only [hb, Option.some.injEq] at hr
    subst hr
    have hlist : ("\"" ++ String.ofList body ++ "\"").toList ++ after = '"' :: (body ++ '"' :: after) := by
      simp [String.toList_append, String.toList_ofList]
    rw [hlist] at hSlice
    obtain ⟨hlt, hget, hs1⟩ := byteSliceAt_ascii_cons hSlice (by decide)
    obtain ⟨endPos, hBody, hGt, hLe, hAfter⟩ := parseStringBody_renderStringChars s.toList styles hb [] after hs1
    simp only [List.utf8Encode_nil, List.nil_append, String.ofList_toList] at hBody
    have hp : pos < endPos ∧ endPos ≤ bytes.size := ⟨by omega, hLe⟩
    refine ⟨⟨endPos, hp⟩, ?_, hAfter⟩
    unfold parseStringAt
    simp [hlt, hget, hBody, hp]


end LeanSwe.Json.Proofs
