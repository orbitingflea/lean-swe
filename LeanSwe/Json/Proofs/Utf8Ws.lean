import Lean.Data.Json.Basic
import LeanSwe.Json.Impl
import LeanSwe.Json.Model
import LeanSwe.Json.Proofs.ScalarLex

namespace LeanSwe.Json.Proofs

open LeanSwe.Json
open LeanSwe.Json.Internal
open LeanSwe.Json.Model

/-- Invariant stating that `bytes` splits at byte index `pos` into a prefix and `cs.utf8Encode`. -/
def ByteSliceAt (bytes : ByteArray) (pos : Nat) (cs : List Char) : Prop :=
  ∃ pre : ByteArray, pre.size = pos ∧ bytes = pre ++ cs.utf8Encode

/-- `raw.toUTF8` starts at byte index `0` with `raw.toList`. -/
theorem byteSliceAt_toUTF8_zero (raw : String) :
    ByteSliceAt raw.toUTF8 0 raw.toList := by
  refine ⟨ByteArray.empty, ByteArray.size_empty, ?_⟩
  rw [ByteArray.empty_append, String.toUTF8_eq_toByteArray, ← String.toByteArray_ofList, String.ofList_toList]

/-- Under `ByteSliceAt bytes pos cs`, `pos ≤ bytes.size` and `bytes.size = pos + cs.utf8Encode.size`. -/
theorem byteSliceAt_size {bytes : ByteArray} {pos : Nat} {cs : List Char}
    (h : ByteSliceAt bytes pos cs) : bytes.size = pos + cs.utf8Encode.size := by
  rcases h with ⟨pre, rfl, rfl⟩
  exact ByteArray.size_append

/-- Under `ByteSliceAt bytes pos []`, `pos = bytes.size`. -/
theorem byteSliceAt_nil_eq_size {bytes : ByteArray} {pos : Nat}
    (h : ByteSliceAt bytes pos []) : pos = bytes.size := by
  have hs := byteSliceAt_size h
  simp [List.utf8Encode_nil, ByteArray.size_empty] at hs
  omega

/-- Every UTF-8 encoded character has positive byte length `1 ≤ c.utf8Size`. -/
theorem utf8Encode_singleton_size_pos (c : Char) : 1 ≤ [c].utf8Encode.size := by
  rw [List.utf8Encode_singleton, List.size_toByteArray, String.length_utf8EncodeChar]
  have hp := Char.utf8Size_pos c
  omega

/-- Under `ByteSliceAt bytes pos (c :: rest)`, `pos < bytes.size`. -/
theorem byteSliceAt_cons_lt_size {bytes : ByteArray} {pos : Nat} {c : Char} {rest : List Char}
    (h : ByteSliceAt bytes pos (c :: rest)) : pos < bytes.size := by
  have hs := byteSliceAt_size h
  rw [List.utf8Encode_cons, ByteArray.size_append] at hs
  have hp := utf8Encode_singleton_size_pos c
  omega

/-- Every byte in `String.utf8EncodeChar c` for non-ASCII `c` (`0x80 ≤ c.toNat`) is `≥ 0x80`. -/
theorem utf8EncodeChar_nonAscii_ge_128 {c : Char} (hge : 0x80 ≤ c.toNat) :
    ∀ b ∈ String.utf8EncodeChar c, (0x80 : UInt8) ≤ b := by
  rw [String.utf8EncodeChar_eq_utf8EncodeCharFast]
  unfold String.utf8EncodeCharFast
  have hnot1 : ¬(c.val ≤ 0x7f) := by
    rw [UInt32.le_iff_toNat_le]; change ¬(c.toNat ≤ 0x7f); omega
  simp only [hnot1, ↓reduceIte]
  have hgeOrC0 : ∀ x : UInt8, (0x80 : UInt8) ≤ (x &&& 0x1f ||| 0xc0) := by decide
  have hgeOrE0 : ∀ x : UInt8, (0x80 : UInt8) ≤ (x &&& 0x0f ||| 0xe0) := by decide
  have hgeOrF0 : ∀ x : UInt8, (0x80 : UInt8) ≤ (x &&& 0x07 ||| 0xf0) := by decide
  have hgeOr80 : ∀ x : UInt8, (0x80 : UInt8) ≤ (x &&& 0x3f ||| 0x80) := by decide
  split
  · intro b hb; simp at hb; rcases hb with rfl | rfl; exact hgeOrC0 _; exact hgeOr80 _
  · split
    · intro b hb; simp at hb; rcases hb with rfl | rfl | rfl
      · exact hgeOrE0 _
      · exact hgeOr80 _
      · exact hgeOr80 _
    · intro b hb; simp at hb; rcases hb with rfl | rfl | rfl | rfl
      · exact hgeOrF0 _
      · exact hgeOr80 _
      · exact hgeOr80 _
      · exact hgeOr80 _

/-- Under `ByteSliceAt bytes pos (c :: rest)` with `c.toNat < 0x80`, `bytes[pos] = c.val.toUInt8` and `ByteSliceAt bytes (pos + 1) rest`. -/
theorem byteSliceAt_ascii_cons {bytes : ByteArray} {pos : Nat} {c : Char} {rest : List Char}
    (h : ByteSliceAt bytes pos (c :: rest)) (hascii : c.toNat < 0x80) :
    ∃ (hlt : pos < bytes.size),
      bytes[pos]'hlt = c.val.toUInt8 ∧ ByteSliceAt bytes (pos + 1) rest := by
  have hlt := byteSliceAt_cons_lt_size h
  refine ⟨hlt, ?_, ?_⟩
  · rcases h with ⟨pre, rfl, hbytes⟩
    have hc1 : c.utf8Size = 1 := by
      simp only [Char.utf8Size]
      have hle : c.val ≤ 0x7f := by rw [UInt32.le_iff_toNat_le]; change c.toNat ≤ 0x7f; omega
      simp [hle]
    have henc : [c].utf8Encode = [c.val.toUInt8].toByteArray := by
      rw [List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton hc1]
    rw [List.utf8Encode_cons, henc, ← ByteArray.append_assoc] at hbytes
    subst hbytes
    rw [ByteArray.getElem_append_left (hlt := by simp only [ByteArray.size_append, List.size_toByteArray, List.length_singleton]; omega)]
    rw [ByteArray.getElem_append_right (hle := Nat.le_refl _)]
    simp
  · rcases h with ⟨pre, rfl, rfl⟩
    have hc1 : c.utf8Size = 1 := by
      simp only [Char.utf8Size]
      have hle : c.val ≤ 0x7f := by rw [UInt32.le_iff_toNat_le]; change c.toNat ≤ 0x7f; omega
      simp [hle]
    have henc : [c].utf8Encode = [c.val.toUInt8].toByteArray := by
      rw [List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton hc1]
    refine ⟨pre ++ [c.val.toUInt8].toByteArray,
      by simp only [ByteArray.size_append, List.size_toByteArray, List.length_singleton], ?_⟩
    rw [List.utf8Encode_cons, henc, ByteArray.append_assoc]

/-- Under `ByteSliceAt bytes pos (c :: rest)` with `0x80 ≤ c.toNat`, `0x80 ≤ bytes[pos]`. -/
theorem byteSliceAt_nonAscii_ge_128 {bytes : ByteArray} {pos : Nat} {c : Char} {rest : List Char}
    (h : ByteSliceAt bytes pos (c :: rest)) (hge : 0x80 ≤ c.toNat) (hlt : pos < bytes.size) :
    (0x80 : UInt8) ≤ bytes[pos]'hlt := by
  rcases h with ⟨pre, rfl, hbytes⟩
  rw [List.utf8Encode_cons, List.utf8Encode_singleton, ← ByteArray.append_assoc] at hbytes
  subst hbytes
  have hne : (String.utf8EncodeChar c).length > 0 := by
    rw [String.length_utf8EncodeChar]; exact Char.utf8Size_pos c
  rw [ByteArray.getElem_append_left (hlt := by simp only [ByteArray.size_append, List.size_toByteArray]; omega)]
  rw [ByteArray.getElem_append_right (hle := Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem_toByteArray]
  exact utf8EncodeChar_nonAscii_ge_128 hge _ (List.getElem_mem _)

/-- Under `ByteSliceAt bytes pos cs` and `hlt : pos < bytes.size`, if `bytes[pos] < 0x80` then `cs` begins with that exact ASCII `Char`. -/
theorem byteSliceAt_head_lt_128 {bytes : ByteArray} {pos : Nat} {cs : List Char}
    (h : ByteSliceAt bytes pos cs) (hlt : pos < bytes.size)
    (hb : (bytes[pos]'hlt) < (0x80 : UInt8)) :
    ∃ c rest, cs = c :: rest ∧ c.toNat = (bytes[pos]'hlt).toNat ∧
      c.toNat < 0x80 ∧ ByteSliceAt bytes (pos + 1) rest := by
  cases cs with
  | nil =>
    have heq := byteSliceAt_nil_eq_size h
    omega
  | cons c rest =>
    by_cases hascii : c.toNat < 0x80
    · obtain ⟨_, hget, hnext⟩ := byteSliceAt_ascii_cons h hascii
      have htoNat : (c.val.toUInt8).toNat = c.toNat := by
        rw [UInt32.toNat_toUInt8]
        exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
      exact ⟨c, rest, rfl, by rw [hget, htoNat], hascii, hnext⟩
    · have hge128 := byteSliceAt_nonAscii_ge_128 h (by omega) hlt
      exact absurd hb (UInt8.not_lt.mpr hge128)

/-- Advance `ByteSliceAt` across any multi-character prefix `mid : List Char`. -/
theorem byteSliceAt_append_chars {bytes : ByteArray} {pos : Nat} {mid rest : List Char}
    (h : ByteSliceAt bytes pos (mid ++ rest)) :
    ByteSliceAt bytes (pos + mid.utf8Encode.size) rest := by
  rcases h with ⟨pre, rfl, rfl⟩
  refine ⟨pre ++ mid.utf8Encode, ByteArray.size_append, ?_⟩
  rw [List.utf8Encode_append, ByteArray.append_assoc]

/-- Split leading RFC 8259 JSON whitespace characters from a character list. -/
def splitJsonWs : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isJsonWsChar c then
      let p := splitJsonWs cs
      (c :: p.1, p.2)
    else ([], c :: cs)

/-- `splitJsonWs cs` splits `cs` into a whitespace prefix and `dropJsonWs cs`. -/
theorem splitJsonWs_props (cs : List Char) :
    let (ws, rest) := splitJsonWs cs
    cs = ws ++ rest ∧ ws.all isJsonWsChar = true ∧ rest = dropJsonWs cs ∧
      (match rest with | [] => True | c :: _ => isJsonWsChar c = false) := by
  induction cs with
  | nil => simp [splitJsonWs, dropJsonWs]
  | cons c tl ih =>
    by_cases hw : isJsonWsChar c = true
    · simp only [splitJsonWs, dropJsonWs, hw, ↓reduceIte]
      rcases ih with ⟨heq, hall, hdrop, hhead⟩
      exact ⟨by rw [List.cons_append, ← heq], by simp [hw, hall], hdrop, hhead⟩
    · simp only [Bool.not_eq_true] at hw
      simp [splitJsonWs, dropJsonWs, hw]

/-- `splitJsonWs (ws ++ rest) = (ws, rest)` when `ws` is all JSON whitespace and `rest` does not begin with JSON whitespace. -/
theorem splitJsonWs_ws_append {ws rest : List Char}
    (hws : ws.all isJsonWsChar = true)
    (hrest : match rest with | [] => True | c :: _ => isJsonWsChar c = false) :
    splitJsonWs (ws ++ rest) = (ws, rest) := by
  induction ws with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c tl => simp [splitJsonWs, hrest]
  | cons c tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hws
    simp [splitJsonWs, hws.1, ih hws.2]

/-- Equivalence between `isWsByte` on ASCII byte `< 0x80` and `isJsonWsChar`. -/
theorem isWsByte_ascii_eq {c : Char} (hascii : c.toNat < 0x80) :
    isWsByte c.val.toUInt8 = isJsonWsChar c := by
  unfold isWsByte isJsonWsChar
  have htoNat : (c.val.toUInt8).toNat = c.toNat := by
    rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
  have h1 : (c.val.toUInt8 == 0x20) = (c == ' ') := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← UInt8.toNat_inj, htoNat, ← Char.toNat_inj]; rfl
  have h2 : (c.val.toUInt8 == 0x09) = (c == '\t') := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← UInt8.toNat_inj, htoNat, ← Char.toNat_inj]; rfl
  have h3 : (c.val.toUInt8 == 0x0a) = (c == '\n') := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← UInt8.toNat_inj, htoNat, ← Char.toNat_inj]; rfl
  have h4 : (c.val.toUInt8 == 0x0d) = (c == '\r') := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← UInt8.toNat_inj, htoNat, ← Char.toNat_inj]; rfl
  rw [h1, h2, h3, h4]

/-- Exact characterization of `skipWsSub` on `ByteSliceAt bytes pos cs`. -/
theorem skipWsSub_spec :
    ∀ (cs : List Char) {bytes : ByteArray} {pos : Nat} (hPos : pos ≤ bytes.size),
      ByteSliceAt bytes pos cs →
      let (ws, rest) := splitJsonWs cs
      (skipWsSub bytes pos hPos).1 = pos + ws.length ∧
        isJsonWs (String.ofList ws) = true ∧
        rest = dropJsonWs cs ∧
        ByteSliceAt bytes (skipWsSub bytes pos hPos).1 rest
  | [], bytes, pos, hPos, hSlice => by
    have heq := byteSliceAt_nil_eq_size hSlice
    have hnot : ¬(pos < bytes.size) := by omega
    simp [splitJsonWs, dropJsonWs, skipWsSub, hnot, isJsonWs, hSlice]
  | c :: tl, bytes, pos, hPos, hSlice => by
    have hlt := byteSliceAt_cons_lt_size hSlice
    by_cases hws : isJsonWsChar c = true
    · have hascii : c.toNat < 0x80 := by
        simp only [isJsonWsChar, Bool.or_eq_true, beq_iff_eq] at hws
        rcases hws with ((rfl | rfl) | rfl) | rfl <;> decide
      obtain ⟨_, hget, hNextSlice⟩ := byteSliceAt_ascii_cons hSlice hascii
      have hbWs : isWsByte (bytes[pos]'hlt) = true := by
        rw [hget, isWsByte_ascii_eq hascii, hws]
      have ih := skipWsSub_spec tl hlt hNextSlice
      rcases hsp : splitJsonWs tl with ⟨wsTl, restTl⟩
      rw [hsp] at ih
      rcases ih with ⟨hpEq, hwsTl, hdropTl, hRestSlice⟩
      simp only [splitJsonWs, hws, ↓reduceIte, hsp]
      unfold skipWsSub
      simp only [hlt, ↓reduceDIte, hbWs, ↓reduceIte]
      have hSubEq : (skipWsSub bytes (pos + 1) (Nat.succ_le_of_lt hlt)).1 = (skipWsSub bytes (pos + 1) hlt).1 := rfl
      refine ⟨by rw [hSubEq, hpEq]; simp [Nat.add_assoc, Nat.add_comm 1], ?_, ?_, ?_⟩
      · simp only [isJsonWs, String.toList_ofList, List.all_cons, hws, Bool.true_and]
        simpa [isJsonWs, String.toList_ofList] using hwsTl
      · simp [dropJsonWs, hws, hdropTl]
      · rwa [hSubEq]
    · simp only [Bool.not_eq_true] at hws
      have hbNotWs : isWsByte (bytes[pos]'hlt) = false := by
        by_cases hascii : c.toNat < 0x80
        · obtain ⟨_, hget, _⟩ := byteSliceAt_ascii_cons hSlice hascii
          rw [hget, isWsByte_ascii_eq hascii, hws]
        · have hge128 := byteSliceAt_nonAscii_ge_128 hSlice (by omega) hlt
          cases hb : isWsByte (bytes[pos]'hlt)
          · rfl
          · simp only [isWsByte, Bool.or_eq_true, beq_iff_eq] at hb
            rcases hb with ((hb | hb) | hb) | hb <;> (rw [hb] at hge128; revert hge128; decide)
      simp only [splitJsonWs, hws, Bool.false_eq_true, ↓reduceIte]
      unfold skipWsSub
      simp [hlt, hbNotWs, isJsonWs, dropJsonWs, hws, hSlice]

/-- Exact characterization of `matchesKeyword.go` against an ASCII character list. -/
theorem matchesKeyword_ascii_spec (kwChars : List Char)
    (hAscii : ∀ c ∈ kwChars, c.toNat < 0x80) :
    ∀ {bytes : ByteArray} {pos : Nat} {cs : List Char},
      ByteSliceAt bytes pos cs →
      (matchesKeyword bytes pos (String.ofList kwChars).toUTF8 = true ↔
        ∃ rest, cs = kwChars ++ rest ∧ ByteSliceAt bytes (pos + kwChars.length) rest) := by
  intro bytes pos cs hSlice
  have hkwBytes : (String.ofList kwChars).toUTF8 = (kwChars.map (fun c => c.val.toUInt8)).toByteArray := by
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
    induction kwChars with
    | nil => rfl
    | cons kc ktl ih =>
      have hk1 : kc.utf8Size = 1 := by
        simp only [Char.utf8Size]
        have hkc := hAscii kc List.mem_cons_self
        have hle : kc.val ≤ 0x7f := by rw [UInt32.le_iff_toNat_le]; change kc.toNat ≤ 0x7f; omega
        simp [hle]
      have hSingle : [kc].utf8Encode = [kc.val.toUInt8].toByteArray := by
        rw [List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton hk1]
      rw [List.utf8Encode_cons, hSingle,
        ih (fun c hc => hAscii c (List.mem_cons_of_mem _ hc)), List.map_cons]
      ext
      · simp
      · simp
  have hkwSize : (String.ofList kwChars).toUTF8.size = kwChars.length := by
    rw [hkwBytes, List.size_toByteArray, List.length_map]
  unfold matchesKeyword
  rw [hkwBytes]
  have hGo : ∀ (rem : List Char) (idx : Nat) (csRem : List Char)
      (hRemAscii : ∀ c ∈ rem, c.toNat < 0x80)
      (hBnd : pos + (kwChars.map (fun c => c.val.toUInt8)).toByteArray.size ≤ bytes.size)
      (hEqLen : idx + rem.length = kwChars.length)
      (hRemAt : ∀ j (hj : j < rem.length),
        (kwChars.map (fun c => c.val.toUInt8)).toByteArray[idx + j]'(by simp only [List.size_toByteArray, List.length_map]; omega) =
          (rem[j]'hj).val.toUInt8),
      ByteSliceAt bytes (pos + idx) csRem →
      (matchesKeyword.go bytes pos (kwChars.map (fun c => c.val.toUInt8)).toByteArray idx hBnd = true ↔
        ∃ rest, csRem = rem ++ rest ∧ ByteSliceAt bytes (pos + kwChars.length) rest) := by
    intro rem
    induction rem with
    | nil =>
      intro idx csRem _ hBnd hEqLen _ hSl
      have hidx : idx = kwChars.length := by simp at hEqLen; exact hEqLen
      subst hidx
      unfold matchesKeyword.go
      have hnot : ¬(kwChars.length < (kwChars.map (fun c => c.val.toUInt8)).toByteArray.size) := by
        simp only [List.size_toByteArray, List.length_map, Nat.lt_irrefl, not_false_eq_true]
      simp only [hnot, ↓reduceDIte, true_iff]
      exact ⟨csRem, rfl, hSl⟩
    | cons kc ktl ih =>
      intro idx csRem hRemAscii hBnd hEqLen hRemAt hSl
      have hiLt : idx < (kwChars.map (fun c => c.val.toUInt8)).toByteArray.size := by
        have hEqLen' := hEqLen
        simp only [List.length_cons] at hEqLen'
        simp only [List.size_toByteArray, List.length_map]; omega
      have hk0 := hRemAt 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hk0
      have hkcAscii : kc.toNat < 0x80 := hRemAscii kc List.mem_cons_self
      unfold matchesKeyword.go
      simp only [hiLt, ↓reduceDIte, hk0]
      have hPosLt : pos + idx < bytes.size := by
        have hBnd' := hBnd
        simp only [List.size_toByteArray, List.length_map] at hBnd'; omega
      by_cases hmatch : (bytes[pos + idx]'hPosLt == kc.val.toUInt8) = true
      · simp only [hmatch, ↓reduceIte]
        have hbEq : bytes[pos + idx]'hPosLt = kc.val.toUInt8 := beq_iff_eq.mp hmatch
        have hbLt128 : bytes[pos + idx]'hPosLt < 0x80 := by
          rw [hbEq, UInt8.lt_iff_toNat_lt, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by change kc.toNat < 256; omega)]
          exact hkcAscii
        obtain ⟨c0, tl0, hcsEq, hc0Nat, _, hNextSl⟩ := byteSliceAt_head_lt_128 hSl hPosLt hbLt128
        have hc0Eq : c0 = kc := by
          apply Char.ext; apply UInt32.toNat_inj.mp
          change c0.toNat = kc.toNat
          rw [hc0Nat, hbEq, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt (by change kc.toNat < 256; omega)]
          rfl
        subst hc0Eq hcsEq
        have hNextSl' : ByteSliceAt bytes (pos + (idx + 1)) tl0 := by
          simpa [Nat.add_assoc] using hNextSl
        rw [ih (idx + 1) tl0 (fun c hc => hRemAscii c (List.mem_cons_of_mem _ hc)) hBnd
          (by simp at hEqLen; omega)
          (fun j hj => by
            have := hRemAt (j + 1) (by simp; omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
          hNextSl']
        simp
      · simp only [Bool.not_eq_true] at hmatch
        simp only [hmatch, Bool.false_eq_true, ↓reduceIte, false_iff]
        rintro ⟨rest, rfl, _⟩
        obtain ⟨_, hget, _⟩ := byteSliceAt_ascii_cons hSl hkcAscii
        rw [hget, beq_self_eq_true] at hmatch
        cases hmatch
  by_cases hBnd : pos + (kwChars.map (fun c => c.val.toUInt8)).toByteArray.size ≤ bytes.size
  · simp only [hBnd, ↓reduceDIte]
    exact hGo kwChars 0 cs hAscii hBnd (by simp)
      (fun j hj => by simp [List.getElem_toByteArray]) (by simpa using hSlice)
  · simp only [hBnd, ↓reduceDIte, Bool.false_eq_true, false_iff]
    rintro ⟨rest, rfl, _⟩
    have hs := byteSliceAt_size hSlice
    rw [List.utf8Encode_append, ByteArray.size_append] at hs
    have hlen : kwChars.utf8Encode.size = kwChars.length := by
      have := hkwSize
      rwa [String.toUTF8_eq_toByteArray, String.toByteArray_ofList] at this
    simp only [List.size_toByteArray, List.length_map] at hBnd
    omega

end LeanSwe.Json.Proofs
