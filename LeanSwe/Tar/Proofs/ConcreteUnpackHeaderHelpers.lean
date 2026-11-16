import LeanSwe.Tar.Proofs.ConcreteUnpackHelpers

set_option Elab.async false

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Base 512-byte USTAR header used throughout Test 5. -/
def baseHdr5 : ByteArray :=
  mkUstarHeader "a.txt" 420 0 0 0 0 48 "" "" "" ""

/-- Unpatched `baseHdr5` prior to `patchHeaderChecksum`. -/
def baseHdr5Pre : ByteArray :=
  mkUstarHeaderPre "a.txt" 420 0 0 0 0 48 "" "" "" ""

/-- `baseHdr5.size = 512`. -/
theorem baseHdr5_size : baseHdr5.size = 512 :=
  mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _

/-- `baseHdr5Pre.size = 512`. -/
theorem baseHdr5Pre_size : baseHdr5Pre.size = 512 :=
  mkUstarHeaderPre_size _ _ _ _ _ _ _ _ _ _ _

private theorem baseHdr5_eq_patch : baseHdr5 = patchHeaderChecksum baseHdr5Pre :=
  rfl

private theorem byteArray_set!_size (b : ByteArray) (k : Nat) (v : UInt8) :
    (b.set! k v).size = b.size :=
  Array.size_setIfInBounds

private theorem byteArray_set!_getElem_val {b : ByteArray} {k i : Nat} {v : UInt8}
    (hk : k < b.size) (hi : i < b.size) :
    (b.set! k v)[i]'(by rw [byteArray_set!_size]; exact hi) =
      if k = i then v else b[i]'hi := by
  have hi' : i < b.data.size := hi
  change (b.data.setIfInBounds k v)[i]'(by rw [Array.size_setIfInBounds]; exact hi') = _
  by_cases h : k = i
  · subst h
    simp only [↓reduceIte]
    exact Array.getElem_setIfInBounds_self (by rw [Array.size_setIfInBounds]; exact hk)
  · simp only [h, ↓reduceIte]
    exact Array.getElem_setIfInBounds_ne hi' (by omega)

private theorem baseHdr5_outside_chk {i : Nat} (hi : i < 512) (hnot : ¬(148 ≤ i ∧ i < 156)) :
    baseHdr5[i]'(by rw [baseHdr5_size]; exact hi) =
      baseHdr5Pre[i]'(by rw [baseHdr5Pre_size]; exact hi) := by
  have h1 : baseHdr5.extract 0 (0 + 512) = patchHeaderChecksum baseHdr5Pre := by
    rw [Nat.zero_add, ← baseHdr5_size, ByteArray.extract_zero_size]
    exact baseHdr5_eq_patch
  have hp := parseChecksumOctal_patchHeaderChecksum baseHdr5Pre_size (by rw [baseHdr5_size]; omega) h1
  simpa using hp.2.2 i hi hnot

private theorem baseHdr5_byte_257 :
    baseHdr5[257]'(by rw [baseHdr5_size]; omega) = 0x75 := by
  rw [baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  rfl

private theorem baseHdr5_byte_156 :
    baseHdr5[156]'(by rw [baseHdr5_size]; omega) = 48 := by
  rw [baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left rfl]

private theorem atxt_utf8_bytes :
    "a.txt".toUTF8 = { data := #[0x61, 0x2e, 0x74, 0x78, 0x74] } := by
  rw [toUTF8_eq_toByteArray]
  decide

private theorem atxt_utf8_size : ("a.txt".toUTF8).size = 5 := by
  rw [atxt_utf8_bytes]
  rfl

private theorem baseHdr5_atxt_byte {i : Nat} (hi : i < 5) :
    baseHdr5[i]'(by rw [baseHdr5_size]; omega) =
      ("a.txt".toUTF8)[i]'(by rw [atxt_utf8_size]; exact hi) := by
  rw [baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have hlt : i < min 100 ("a.txt".toUTF8).size := by rw [atxt_utf8_size]; omega
  rw [dite_eq_left hlt]

private theorem baseHdr5_byte_5 :
    baseHdr5[5]'(by rw [baseHdr5_size]; omega) = 0 := by
  rw [baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have hnot0 : ¬(5 < min 100 ("a.txt".toUTF8).size) := by rw [atxt_utf8_size]; omega
  rw [dite_eq_right hnot0, dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega)]

private theorem twoZeroBlocks_pos : 0 < twoZeroBlocks.size := by
  rw [twoZeroBlocks_size]
  omega

private theorem twoZeroBlocks_mod : twoZeroBlocks.size % 512 = 0 := by
  rw [twoZeroBlocks_size]

private theorem extract_hdr_rest_head (hdr rest : ByteArray) (hhdr : hdr.size = 512) :
    (hdr ++ rest).extract 0 512 = hdr := by
  have h := extract_append_mid ByteArray.empty hdr rest
  simp only [ByteArray.size_empty, Nat.zero_add, ByteArray.empty_append] at h
  rw [hhdr] at h
  exact h

private theorem byteArray_toList_getElem_zero {b : ByteArray}
    (h0 : 0 < b.size) (h0' : 0 < b.toList.length) :
    b.toList[0]'h0' = b[0]'h0 := by
  simp only [byteArray_toList_eq, Array.getElem_toList]
  rfl

private theorem unpackWith_hdr_rest_start (opts : UnpackOptions) {hdr rest : ByteArray}
    (hhdr : hdr.size = 512) (hrest_pos : 0 < rest.size) (hrest_mod : rest.size % 512 = 0) :
    Impl.unpackWith opts (hdr ++ rest) = unpackLoop opts (hdr ++ rest) 0 none [] [] 0 := by
  let bytes := hdr ++ rest
  have hsz : bytes.size = 512 + rest.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hne : bytes.size ≠ 0 := by rw [hsz]; omega
  have hmod : bytes.size % 512 = 0 := by rw [hsz]; omega
  have h1 : (bytes.size == 0) = false := beq_false_of_ne hne
  have h2 : (bytes.size % 512 != 0) = false := by simp [bne, hmod]
  unfold Impl.unpackWith
  change (if (bytes.size == 0 || bytes.size % 512 != 0) = true then _ else _) = _
  rw [h1, h2]
  rfl

private theorem unpackWith_hdr_rest_parseHeader_err {hdr rest : ByteArray}
    (hhdr : hdr.size = 512) (hrest_pos : 0 < rest.size) (hrest_mod : rest.size % 512 = 0)
    (h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0)
    {e : TarError} (hparse : parseUstarHeader (hdr ++ rest) 0 = .error e) :
    Impl.unpackWith {} (hdr ++ rest) = .error e := by
  let bytes := hdr ++ rest
  have hbytes_sz : bytes.size = 512 + rest.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hnz : isZeroRange bytes 0 512 = false := by
    apply isZeroRange_false_of_ne (i := 257) (by omega) (by rw [hbytes_sz]; omega)
    have hl : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) := by
      simp only [Nat.zero_add, bytes]
      exact getElem_append_left (by rw [hhdr]; omega)
    rw [hl]
    exact h257
  have hnotge : ¬(0 ≥ bytes.size) := by rw [hbytes_sz]; omega
  have hnotgt : ¬(0 + 512 > bytes.size) := by rw [hbytes_sz]; omega
  have hnz' : ¬(isZeroRange bytes 0 512 = true) := by rw [hnz]; simp
  change Impl.unpackWith {} bytes = .error e
  rw [unpackWith_hdr_rest_start {} hhdr hrest_pos hrest_mod, unpackLoop.eq_1, ite_eq_right hnotge,
    unpackStep.eq_1, ite_eq_right hnotge, ite_eq_right hnz', ite_eq_right hnotgt]
  have hp : parseUstarHeader bytes 0 = .error e := hparse
  rw [hp]

private theorem unpackWith_hdr_rest_decode_err {hdr rest : ByteArray}
    (hhdr : hdr.size = 512) (hrest_pos : 0 < rest.size) (hrest_mod : rest.size % 512 = 0)
    (h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0)
    {fields : UstarHeaderFields} (hparse : parseUstarHeader (hdr ++ rest) 0 = .ok fields)
    (hnot78 : (fields.typeflag == 0x78) = false)
    {e : TarError} (hdec : decodeTarEntry {} (hdr ++ rest) 0 fields none [] 0 0 = .error e) :
    Impl.unpackWith {} (hdr ++ rest) = .error e := by
  let bytes := hdr ++ rest
  have hbytes_sz : bytes.size = 512 + rest.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hnz : isZeroRange bytes 0 512 = false := by
    apply isZeroRange_false_of_ne (i := 257) (by omega) (by rw [hbytes_sz]; omega)
    have hl : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) := by
      simp only [Nat.zero_add, bytes]
      exact getElem_append_left (by rw [hhdr]; omega)
    rw [hl]
    exact h257
  have hnotge : ¬(0 ≥ bytes.size) := by rw [hbytes_sz]; omega
  have hnotgt : ¬(0 + 512 > bytes.size) := by rw [hbytes_sz]; omega
  have hnz' : ¬(isZeroRange bytes 0 512 = true) := by rw [hnz]; simp
  have hnot78' : ¬((fields.typeflag == 0x78) = true) := by rw [hnot78]; simp
  have hlen0 : ([] : List TarEntry).length = 0 := rfl
  change Impl.unpackWith {} bytes = .error e
  rw [unpackWith_hdr_rest_start {} hhdr hrest_pos hrest_mod, unpackLoop.eq_1, ite_eq_right hnotge,
    unpackStep.eq_1, ite_eq_right hnotge, ite_eq_right hnz', ite_eq_right hnotgt]
  have hp : parseUstarHeader bytes 0 = .ok fields := hparse
  have hd : decodeTarEntry {} bytes 0 fields none [] 0 0 = .error e := hdec
  rw [hp]
  dsimp only
  rw [ite_eq_right hnot78', hlen0, hd]

private theorem unpackWith_hdr_twoZero_regular_ok {hdr : ByteArray}
    (hhdr : hdr.size = 512) (h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0)
    {fields : UstarHeaderFields} (hparse : parseUstarHeader (hdr ++ twoZeroBlocks) 0 = .ok fields)
    (hnot78 : (fields.typeflag == 0x78) = false)
    {entry : TarEntry} (hsz0 : entry.data.size = 0)
    (hdec : decodeTarEntry {} (hdr ++ twoZeroBlocks) 0 fields none [] 0 0 = .ok (entry, 0)) :
    Impl.unpackWith {} (hdr ++ twoZeroBlocks) = .ok [entry] := by
  let bytes := hdr ++ twoZeroBlocks
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hnz : isZeroRange bytes 0 512 = false := by
    apply isZeroRange_false_of_ne (i := 257) (by omega) (by rw [hbytes_sz]; omega)
    have hl : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) := by
      simp only [Nat.zero_add, bytes]
      exact getElem_append_left (by rw [hhdr]; omega)
    rw [hl]
    exact h257
  have hnotge : ¬(0 ≥ bytes.size) := by rw [hbytes_sz]; omega
  have hnotgt : ¬(0 + 512 > bytes.size) := by rw [hbytes_sz]; omega
  have hnz' : ¬(isZeroRange bytes 0 512 = true) := by rw [hnz]; simp
  have hnot78' : ¬((fields.typeflag == 0x78) = true) := by rw [hnot78]; simp
  have hadv : 0 + 512 + 0 > 0 := by omega
  have hlen0 : ([] : List TarEntry).length = 0 := rfl
  change Impl.unpackWith {} bytes = .ok [entry]
  rw [unpackWith_hdr_rest_start {} hhdr twoZeroBlocks_pos twoZeroBlocks_mod, unpackLoop.eq_1, ite_eq_right hnotge,
    unpackStep.eq_1, ite_eq_right hnotge, ite_eq_right hnz', ite_eq_right hnotgt]
  have hp : parseUstarHeader bytes 0 = .ok fields := hparse
  have hd : decodeTarEntry {} bytes 0 fields none [] 0 0 = .ok (entry, 0) := hdec
  rw [hp]
  dsimp only
  rw [ite_eq_right hnot78', hlen0, hd]
  dsimp only
  rw [ite_eq_left hadv]
  simp only [Nat.zero_add, hsz0]
  rw [← hhdr]
  change unpackLoop {} (hdr ++ (zeroBlock ++ zeroBlock)) hdr.size none [entry.path] [entry] 0 = .ok [entry]
  rw [unpackLoop_at_twoZeroBlocks]
  rfl

private theorem extract_patch_eq_slice {hdrPre rest target : ByteArray} {a w : Nat}
    (hhdr : hdrPre.size = 512) (haw : a + w ≤ 512) (ht : target.size = w)
    (hnot : ∀ k : Nat, k < w → ¬(148 ≤ a + k ∧ a + k < 156))
    (hpt : ∀ (k : Nat) (hk : k < w),
      hdrPre[a + k]'(by rw [hhdr]; omega) = target[k]'(by rw [ht]; exact hk)) :
    (patchHeaderChecksum hdrPre ++ rest).extract a (a + w) = target := by
  let hdr := patchHeaderChecksum hdrPre
  have hpatch_sz : hdr.size = 512 := by rw [patchHeaderChecksum_size, hhdr]
  have hext0 : (hdr ++ rest).extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]
    exact extract_hdr_rest_head hdr rest hpatch_sz
  have hp := parseChecksumOctal_patchHeaderChecksum hhdr
    (by rw [ByteArray.size_append, hpatch_sz]; omega) hext0
  have heq : (hdr ++ rest).extract a (a + w) = (hdr ++ rest).extract (0 + a) (0 + (a + w)) := by
    simp only [Nat.zero_add]
  rw [heq]
  apply extract_eq_of_getElem (offset := 0) (by omega)
    (by rw [ByteArray.size_append, hpatch_sz]; omega) (by rw [ht]; omega)
  intro k hk
  have hkw : k < w := by omega
  have h1 := hp.2.2 (a + k) (by omega) (hnot k hkw)
  simp only [Nat.zero_add] at h1
  have hlhs : (hdr ++ rest)[0 + a + k]'(by rw [ByteArray.size_append, hpatch_sz]; omega) =
      (hdr ++ rest)[a + k]'(by rw [ByteArray.size_append, hpatch_sz]; omega) := by
    congr 1; omega
  rw [hlhs, h1]
  exact hpt k hkw

private theorem extract_patch_eq_baseHdr5 {hdrPre rest : ByteArray} {a b : Nat}
    (hhdr : hdrPre.size = 512) (hab : a ≤ b) (hb : b ≤ 512)
    (hnot : ∀ k : Nat, k < b - a → ¬(148 ≤ a + k ∧ a + k < 156))
    (hagree : ∀ (k : Nat) (hk : k < b - a),
      hdrPre[a + k]'(by rw [hhdr]; omega) = baseHdr5[a + k]'(by rw [baseHdr5_size]; omega)) :
    (patchHeaderChecksum hdrPre ++ rest).extract a b = baseHdr5.extract a b := by
  have heq : b = a + (b - a) := by omega
  have htsz : (baseHdr5.extract a (a + (b - a))).size = b - a := by
    rw [ByteArray.size_extract, baseHdr5_size]; omega
  rw [heq]
  apply extract_patch_eq_slice hhdr (by omega) htsz hnot
  intro k hk
  rw [hagree k hk]
  have hk' : k < (baseHdr5.extract a (a + (b - a))).size := by rw [htsz]; exact hk
  exact (ByteArray.getElem_extract hk').symm

private theorem baseHdr5_extract_mode :
    baseHdr5.extract 100 108 = encodeOctalField ((420 : UInt32) &&& 0o7777).toNat 7 := by
  have hsz : (encodeOctalField ((420 : UInt32) &&& 0o7777).toNat 7).size = 8 :=
    encodeOctalField_size _ 7
  have h108 : baseHdr5.extract 100 108 = baseHdr5.extract (0 + 100) (0 + 108) := by simp
  rw [h108]
  apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [baseHdr5_size]; omega) hsz
  intro k hk
  have hl : baseHdr5[0 + 100 + k]'(by rw [baseHdr5_size]; omega) =
      baseHdr5[100 + k]'(by rw [baseHdr5_size]; omega) := rfl
  rw [hl, baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have h1 : 100 ≤ 100 + k ∧ 100 + k < 108 := by omega
  rw [dite_eq_right (by omega), dite_eq_left h1]
  simp only [(by omega : 100 + k - 100 = k)]

private theorem baseHdr5_extract_uid :
    baseHdr5.extract 108 116 = encodeOctalField 0 7 := by
  have hsz : (encodeOctalField 0 7).size = 8 := encodeOctalField_size _ 7
  have h116 : baseHdr5.extract 108 116 = baseHdr5.extract (0 + 108) (0 + 116) := by simp
  rw [h116]
  apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [baseHdr5_size]; omega) hsz
  intro k hk
  have hl : baseHdr5[0 + 108 + k]'(by rw [baseHdr5_size]; omega) =
      baseHdr5[108 + k]'(by rw [baseHdr5_size]; omega) := rfl
  rw [hl, baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have h2 : 108 ≤ 108 + k ∧ 108 + k < 116 := by omega
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h2]
  simp only [(by omega : 108 + k - 108 = k)]

private theorem baseHdr5_extract_gid :
    baseHdr5.extract 116 124 = encodeOctalField 0 7 := by
  have hsz : (encodeOctalField 0 7).size = 8 := encodeOctalField_size _ 7
  have h124 : baseHdr5.extract 116 124 = baseHdr5.extract (0 + 116) (0 + 124) := by simp
  rw [h124]
  apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [baseHdr5_size]; omega) hsz
  intro k hk
  have hl : baseHdr5[0 + 116 + k]'(by rw [baseHdr5_size]; omega) =
      baseHdr5[116 + k]'(by rw [baseHdr5_size]; omega) := rfl
  rw [hl, baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have h3 : 116 ≤ 116 + k ∧ 116 + k < 124 := by omega
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h3]
  simp only [(by omega : 116 + k - 116 = k)]

private theorem baseHdr5_extract_size :
    baseHdr5.extract 124 136 = encodeOctalField 0 11 := by
  have hsz : (encodeOctalField 0 11).size = 12 := encodeOctalField_size _ 11
  have h136 : baseHdr5.extract 124 136 = baseHdr5.extract (0 + 124) (0 + 136) := by simp
  rw [h136]
  apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [baseHdr5_size]; omega) hsz
  intro k hk
  have hl : baseHdr5[0 + 124 + k]'(by rw [baseHdr5_size]; omega) =
      baseHdr5[124 + k]'(by rw [baseHdr5_size]; omega) := rfl
  rw [hl, baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have h4 : 124 ≤ 124 + k ∧ 124 + k < 136 := by omega
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_left h4]
  simp only [(by omega : 124 + k - 124 = k)]

private theorem baseHdr5_extract_mtime :
    baseHdr5.extract 136 148 = encodeOctalField 0 11 := by
  have hsz : (encodeOctalField 0 11).size = 12 := encodeOctalField_size _ 11
  have h148 : baseHdr5.extract 136 148 = baseHdr5.extract (0 + 136) (0 + 148) := by simp
  rw [h148]
  apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [baseHdr5_size]; omega) hsz
  intro k hk
  have hl : baseHdr5[0 + 136 + k]'(by rw [baseHdr5_size]; omega) =
      baseHdr5[136 + k]'(by rw [baseHdr5_size]; omega) := rfl
  rw [hl, baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have h5 : 136 ≤ 136 + k ∧ 136 + k < 148 := by omega
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h5]
  simp only [(by omega : 136 + k - 136 = k)]

private theorem baseHdr5_extract_magic :
    baseHdr5.extract 257 263 = "ustar\x00".toUTF8 := by
  have hsz : "ustar\x00".toUTF8.size = 6 := by rw [toUTF8_eq_toByteArray]; decide
  have h263 : baseHdr5.extract 257 263 = baseHdr5.extract (0 + 257) (0 + 263) := by simp
  rw [h263]
  apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [baseHdr5_size]; omega) hsz
  intro k hk
  have hl : baseHdr5[0 + 257 + k]'(by rw [baseHdr5_size]; omega) =
      baseHdr5[257 + k]'(by rw [baseHdr5_size]; omega) := rfl
  rw [hl, baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have h8 : 257 ≤ 257 + k ∧ 257 + k < 263 := by omega
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h8]
  simp only [(by omega : 257 + k - 257 = k)]

private theorem baseHdr5_extract_ver :
    baseHdr5.extract 263 265 = "00".toUTF8 := by
  have hsz : "00".toUTF8.size = 2 := by rw [toUTF8_eq_toByteArray]; decide
  have h265 : baseHdr5.extract 263 265 = baseHdr5.extract (0 + 263) (0 + 265) := by simp
  rw [h265]
  apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [baseHdr5_size]; omega) hsz
  intro k hk
  have hl : baseHdr5[0 + 263 + k]'(by rw [baseHdr5_size]; omega) =
      baseHdr5[263 + k]'(by rw [baseHdr5_size]; omega) := rfl
  rw [hl, baseHdr5_outside_chk (by omega) (by omega)]
  unfold baseHdr5Pre
  rw [mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega)]
  have h9 : 263 ≤ 263 + k ∧ 263 + k < 265 := by omega
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left h9]
  simp only [(by omega : 263 + k - 263 = k)]

private theorem baseHdr5_extract_strings :
    baseHdr5.extract 0 100 = padRightBytes 100 "a.txt".toUTF8 ∧
    baseHdr5.extract 157 257 = padRightBytes 100 "".toUTF8 ∧
    baseHdr5.extract 265 297 = padRightBytes 32 "".toUTF8 ∧
    baseHdr5.extract 297 329 = padRightBytes 32 "".toUTF8 ∧
    baseHdr5.extract 345 500 = padRightBytes 155 "".toUTF8 := by
  have hext : baseHdr5.extract 0 (0 + 512) = baseHdr5 := by
    rw [Nat.zero_add, ← baseHdr5_size, ByteArray.extract_zero_size]
  simpa using mkUstarHeader_extract_strings (by rw [baseHdr5_size]; omega) hext
    (by rw [atxt_utf8_size]; omega)
    (by rw [toUTF8_eq_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray]; decide)
    (by rw [toUTF8_eq_toByteArray]; decide)

private theorem patch_agree_magic {hdrPre : ByteArray} (rest : ByteArray) (hhdr : hdrPre.size = 512)
    (h257 : ∀ (k : Nat) (hk : k < 8), hdrPre[257 + k]'(by rw [hhdr]; omega) =
      baseHdr5[257 + k]'(by rw [baseHdr5_size]; omega)) :
    hasValidMagic (patchHeaderChecksum hdrPre ++ rest) 0 = true := by
  have hm : (patchHeaderChecksum hdrPre ++ rest).extract 257 263 = "ustar\x00".toUTF8 := by
    rw [extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega)
      (fun k hk => h257 k (by omega))]
    exact baseHdr5_extract_magic
  have hv : (patchHeaderChecksum hdrPre ++ rest).extract 263 265 = "00".toUTF8 := by
    rw [extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega)
      (fun k hk => by simpa only [← Nat.add_assoc] using h257 (6 + k) (by omega))]
    exact baseHdr5_extract_ver
  unfold hasValidMagic
  simp only [Nat.zero_add]
  rw [hm, hv, toUTF8_toList, toUTF8_toList]
  decide

private theorem patch_agree_mode {hdrPre : ByteArray} (rest : ByteArray) (hhdr : hdrPre.size = 512)
    (hagree : ∀ (k : Nat) (hk : k < 8), hdrPre[100 + k]'(by rw [hhdr]; omega) =
      baseHdr5[100 + k]'(by rw [baseHdr5_size]; omega)) :
    parseUstarNumeric (patchHeaderChecksum hdrPre ++ rest) 100 108 0 false u32Limit "mode" =
      .ok ((420 : UInt32) &&& 0o7777).toNat := by
  have hext : (patchHeaderChecksum hdrPre ++ rest).extract 100 108 =
      encodeOctalField ((420 : UInt32) &&& 0o7777).toNat 7 := by
    rw [extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hagree]
    exact baseHdr5_extract_mode
  have h108 : (108 : Nat) = 100 + (7 + 1) := by omega
  rw [h108]
  exact parseUstarNumeric_encodeOctalField (by omega) (by decide) (by decide) (by simpa [h108] using hext)

private theorem patch_agree_uid {hdrPre : ByteArray} (rest : ByteArray) (hhdr : hdrPre.size = 512)
    (hagree : ∀ (k : Nat) (hk : k < 8), hdrPre[108 + k]'(by rw [hhdr]; omega) =
      baseHdr5[108 + k]'(by rw [baseHdr5_size]; omega)) :
    parseUstarNumeric (patchHeaderChecksum hdrPre ++ rest) 108 116 0 true u64Limit "uid" = .ok 0 := by
  have hext : (patchHeaderChecksum hdrPre ++ rest).extract 108 116 = encodeOctalField 0 7 := by
    rw [extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hagree]
    exact baseHdr5_extract_uid
  have h116 : (116 : Nat) = 108 + (7 + 1) := by omega
  rw [h116]
  exact parseUstarNumeric_encodeOctalField (by omega) (by decide) (by decide) (by simpa [h116] using hext)

private theorem patch_agree_gid {hdrPre : ByteArray} (rest : ByteArray) (hhdr : hdrPre.size = 512)
    (hagree : ∀ (k : Nat) (hk : k < 8), hdrPre[116 + k]'(by rw [hhdr]; omega) =
      baseHdr5[116 + k]'(by rw [baseHdr5_size]; omega)) :
    parseUstarNumeric (patchHeaderChecksum hdrPre ++ rest) 116 124 0 true u64Limit "gid" = .ok 0 := by
  have hext : (patchHeaderChecksum hdrPre ++ rest).extract 116 124 = encodeOctalField 0 7 := by
    rw [extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hagree]
    exact baseHdr5_extract_gid
  have h124 : (124 : Nat) = 116 + (7 + 1) := by omega
  rw [h124]
  exact parseUstarNumeric_encodeOctalField (by omega) (by decide) (by decide) (by simpa [h124] using hext)

private theorem patch_agree_size {hdrPre : ByteArray} (rest : ByteArray) (hhdr : hdrPre.size = 512)
    (hagree : ∀ (k : Nat) (hk : k < 12), hdrPre[124 + k]'(by rw [hhdr]; omega) =
      baseHdr5[124 + k]'(by rw [baseHdr5_size]; omega)) :
    parseUstarNumeric (patchHeaderChecksum hdrPre ++ rest) 124 136 0 false u64Limit "size" = .ok 0 := by
  have hext : (patchHeaderChecksum hdrPre ++ rest).extract 124 136 = encodeOctalField 0 11 := by
    rw [extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hagree]
    exact baseHdr5_extract_size
  have h136 : (136 : Nat) = 124 + (11 + 1) := by omega
  rw [h136]
  exact parseUstarNumeric_encodeOctalField (by omega) (by decide) (by decide) (by simpa [h136] using hext)

private theorem patch_agree_mtime {hdrPre : ByteArray} (rest : ByteArray) (hhdr : hdrPre.size = 512)
    (hagree : ∀ (k : Nat) (hk : k < 12), hdrPre[136 + k]'(by rw [hhdr]; omega) =
      baseHdr5[136 + k]'(by rw [baseHdr5_size]; omega)) :
    parseUstarNumeric (patchHeaderChecksum hdrPre ++ rest) 136 148 0 true u64Limit "mtime" = .ok 0 := by
  have hext : (patchHeaderChecksum hdrPre ++ rest).extract 136 148 = encodeOctalField 0 11 := by
    rw [extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hagree]
    exact baseHdr5_extract_mtime
  have h148 : (148 : Nat) = 136 + (11 + 1) := by omega
  rw [h148]
  exact parseUstarNumeric_encodeOctalField (by omega) (by decide) (by decide) (by simpa [h148] using hext)

private theorem patch_agree_regular_strings {hdrPre : ByteArray} (rest : ByteArray) (hhdr : hdrPre.size = 512)
    (hname : ∀ (k : Nat) (hk : k < 100), hdrPre[0 + k]'(by rw [hhdr]; omega) =
      baseHdr5[0 + k]'(by rw [baseHdr5_size]; omega))
    (huname : ∀ (k : Nat) (hk : k < 32), hdrPre[265 + k]'(by rw [hhdr]; omega) =
      baseHdr5[265 + k]'(by rw [baseHdr5_size]; omega))
    (hgname : ∀ (k : Nat) (hk : k < 32), hdrPre[297 + k]'(by rw [hhdr]; omega) =
      baseHdr5[297 + k]'(by rw [baseHdr5_size]; omega))
    (hpfx : ∀ (k : Nat) (hk : k < 155), hdrPre[345 + k]'(by rw [hhdr]; omega) =
      baseHdr5[345 + k]'(by rw [baseHdr5_size]; omega)) :
    decodeCStringUtf8 (patchHeaderChecksum hdrPre ++ rest) 0 100 0 "name" = .ok "a.txt" ∧
    decodeCStringUtf8 (patchHeaderChecksum hdrPre ++ rest) 265 297 0 "uname" = .ok "" ∧
    decodeCStringUtf8 (patchHeaderChecksum hdrPre ++ rest) 297 329 0 "gname" = .ok "" ∧
    decodeCStringUtf8 (patchHeaderChecksum hdrPre ++ rest) 345 500 0 "prefix" = .ok "" := by
  let bytes := patchHeaderChecksum hdrPre ++ rest
  have hpatch_sz : (patchHeaderChecksum hdrPre).size = 512 := by
    rw [patchHeaderChecksum_size, hhdr]
  have hbytes_sz : bytes.size = 512 + rest.size := by
    simp only [bytes, ByteArray.size_append, hpatch_sz]
  have hempty_sz : "".toUTF8.size = 0 := by
    rw [toUTF8_eq_toByteArray]; rfl
  have hne_atxt : (!decide (hasNulString "a.txt" = true)) = true := by decide
  have hne_emp : (!decide (hasNulString "" = true)) = true := by decide
  have hext_nm : bytes.extract 0 (0 + 100) = padRightBytes 100 "a.txt".toUTF8 := by
    rw [Nat.zero_add, extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hname]
    exact baseHdr5_extract_strings.1
  have hext_un : bytes.extract 265 (265 + 32) = padRightBytes 32 "".toUTF8 := by
    have h297 : (265 + 32 : Nat) = 297 := rfl
    rw [h297, extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) huname]
    exact baseHdr5_extract_strings.2.2.1
  have hext_gn : bytes.extract 297 (297 + 32) = padRightBytes 32 "".toUTF8 := by
    have h329 : (297 + 32 : Nat) = 329 := rfl
    rw [h329, extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hgname]
    exact baseHdr5_extract_strings.2.2.2.1
  have hext_pf : bytes.extract 345 (345 + 155) = padRightBytes 155 "".toUTF8 := by
    have h500 : (345 + 155 : Nat) = 500 := rfl
    rw [h500, extract_patch_eq_baseHdr5 hhdr (by omega) (by omega) (fun k hk => by omega) hpfx]
    exact baseHdr5_extract_strings.2.2.2.2
  have h0_100 : (100 : Nat) = 0 + 100 := rfl
  have h297 : (297 : Nat) = 265 + 32 := rfl
  have h329 : (329 : Nat) = 297 + 32 := rfl
  have h500 : (500 : Nat) = 345 + 155 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change decodeCStringUtf8 bytes 0 100 0 "name" = .ok "a.txt"
    rw [h0_100]
    exact decodeCStringUtf8_padRightBytes hne_atxt (by rw [atxt_utf8_size]; omega)
      (by rw [hbytes_sz]; omega) hext_nm
  · change decodeCStringUtf8 bytes 265 297 0 "uname" = .ok ""
    rw [h297]
    exact decodeCStringUtf8_padRightBytes hne_emp (by rw [hempty_sz]; omega)
      (by rw [hbytes_sz]; omega) hext_un
  · change decodeCStringUtf8 bytes 297 329 0 "gname" = .ok ""
    rw [h329]
    exact decodeCStringUtf8_padRightBytes hne_emp (by rw [hempty_sz]; omega)
      (by rw [hbytes_sz]; omega) hext_gn
  · change decodeCStringUtf8 bytes 345 500 0 "prefix" = .ok ""
    rw [h500]
    exact decodeCStringUtf8_padRightBytes hne_emp (by rw [hempty_sz]; omega)
      (by rw [hbytes_sz]; omega) hext_pf

private theorem parseUstarHeader_patch_check {hdrPre rest : ByteArray}
    (hhdr : hdrPre.size = 512)
    (hbd : 512 ≤ (patchHeaderChecksum hdrPre ++ rest).size) :
    ustarChecksumAt (patchHeaderChecksum hdrPre ++ rest) 0 = ustarChecksum hdrPre ∧
    parseChecksumOctal (patchHeaderChecksum hdrPre ++ rest) 148 156 0 =
      .ok (ustarChecksumAt (patchHeaderChecksum hdrPre ++ rest) 0) := by
  have hpatch_sz : (patchHeaderChecksum hdrPre).size = 512 := by
    rw [patchHeaderChecksum_size, hhdr]
  have hext0 : (patchHeaderChecksum hdrPre ++ rest).extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]
    exact extract_hdr_rest_head (patchHeaderChecksum hdrPre) rest hpatch_sz
  have hp := parseChecksumOctal_patchHeaderChecksum hhdr hbd hext0
  exact ⟨hp.1, hp.2.1⟩

private theorem encodeOctalField_append_space (chk : Nat) (ds : List UInt8)
    (hds_eq : encodeOctalField.loop 6 chk [0] = ds ++ [0]) (hds_len : ds.length = 6) :
    encodeOctalField chk 6 ++ ByteArray.mk #[0x20] = (ds ++ [0, 0x20]).toByteArray := by
  have hfld : encodeOctalField chk 6 = (ds ++ [0]).toByteArray := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    unfold encodeOctalField
    rw [hds_eq]
    change (ds ++ [0]).toArray.toList = (ds ++ [0]).toByteArray.data.toList
    rw [List.toList_toArray, ← byteArray_toList_eq, toByteArray_toList]
  rw [hfld]
  apply ByteArray.ext; apply Array.ext
  · rw [← ByteArray.size, ByteArray.size_append, List.size_toByteArray, ← ByteArray.size, List.size_toByteArray]
    simp [hds_len]; rfl
  · intro i hi1 hi2
    have hi1' : i < ((ds ++ [0]).toByteArray ++ ByteArray.mk #[0x20]).size := hi1
    have hi2' : i < (ds ++ [0, 0x20]).toByteArray.size := hi2
    have hi2_len : i < (ds ++ [0, 0x20]).length := by
      rw [List.size_toByteArray] at hi2'; exact hi2'
    rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
      ← ByteArray.getElem_eq_getElem_data (h := hi2'), List.getElem_toByteArray]
    have h2 : ds ++ [0, 0x20] = (ds ++ [0]) ++ [0x20] := by simp [List.append_assoc]
    have hlen : (ds ++ [0]).length = 7 := by simp [hds_len]
    by_cases hlt : i < 7
    · rw [getElem_append_left (by rw [List.size_toByteArray, hlen]; exact hlt)
          (hab := by rw [ByteArray.size_append, List.size_toByteArray, hlen]; change i < 7 + 1; omega),
        List.getElem_toByteArray]
      have hcongr : (ds ++ [0, 0x20])[i]'hi2_len = ((ds ++ [0]) ++ [0x20])[i]'(by rw [← h2]; exact hi2_len) := by
        congr 1
      rw [hcongr]
      exact (List.getElem_append_left (by rw [hlen]; exact hlt)
        (h' := by rw [← h2]; exact hi2_len)).symm
    · have hi7 : i = 7 := by
        rw [ByteArray.size_append, List.size_toByteArray, hlen] at hi1'
        change i < 7 + 1 at hi1'
        omega
      subst hi7
      rw [getElem_append_right (by rw [List.size_toByteArray, hlen]; omega)]
      have hsub : 7 - (ds ++ [0]).toByteArray.size = 0 := by rw [List.size_toByteArray, hlen]
      simp only [hsub]
      have hcongr : (ds ++ [0, 0x20])[7]'hi2_len = ((ds ++ [0]) ++ [0x20])[7]'(by rw [← h2]; exact hi2_len) := by
        congr 1
      rw [hcongr, List.getElem_append_right (by rw [hlen]; omega)]
      simp only [hlen, Nat.sub_self]
      rfl

private theorem badChkVal_abstract (baseHdr baseHdrPre : ByteArray)
    (hbase_sz : baseHdr.size = 512) (hpre_sz : baseHdrPre.size = 512)
    (hbase_eq : baseHdr = patchHeaderChecksum baseHdrPre)
    (hb257 : baseHdr[257]'(by rw [hbase_sz]; omega) = 0x75) :
    ∃ e, Impl.unpackWith {} (baseHdr.set! 148 55 ++ twoZeroBlocks) = .error e ∧
      e.kind = .checksumMismatch ∧ e.message ≠ "" := by
  let hdr := baseHdr.set! 148 55
  let bytes := hdr ++ twoZeroBlocks
  have hhdr : hdr.size = 512 := (byteArray_set!_size _ _ _).trans hbase_sz
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    change (baseHdr.set! 148 55)[257]'(by rw [hhdr]; omega) ≠ 0
    rw [byteArray_set!_getElem_val (by rw [hbase_sz]; omega) (by rw [hbase_sz]; omega)]
    rw [ite_eq_right (by omega), hb257]
    decide
  have hext0 : (baseHdr ++ twoZeroBlocks).extract 0 (0 + 512) = patchHeaderChecksum baseHdrPre := by
    rw [Nat.zero_add, extract_hdr_rest_head baseHdr twoZeroBlocks hbase_sz]
    exact hbase_eq
  have hp := parseChecksumOctal_patchHeaderChecksum hpre_sz
    (by rw [ByteArray.size_append, hbase_sz]; omega) hext0
  have hext_base_chk : (baseHdr ++ twoZeroBlocks).extract 148 156 =
      encodeOctalField (ustarChecksumAt (baseHdr ++ twoZeroBlocks) 0) 6 ++ ByteArray.mk #[0x20] := by
    have hcf_sz : (encodeOctalField (ustarChecksum baseHdrPre) 6 ++ ByteArray.mk #[0x20]).size = 8 := by
      rw [ByteArray.size_append, encodeOctalField_size]; rfl
    have hext_off : (baseHdr ++ twoZeroBlocks).extract 148 156 =
        (baseHdr ++ twoZeroBlocks).extract (0 + 148) (0 + 156) := by
      rw [Nat.zero_add]
    rw [hext_off, hp.1]
    apply extract_eq_of_getElem (offset := 0) (by omega)
      (by rw [ByteArray.size_append, hbase_sz]; omega) hcf_sz
    intro k hk
    have hk8 : k < 8 := by rw [← hcf_sz]; exact hk
    have hb_l : (baseHdr ++ twoZeroBlocks)[0 + 148 + k]'(by
        rw [ByteArray.size_append, hbase_sz]; omega) =
        baseHdr[148 + k]'(by rw [hbase_sz]; omega) := by
      have hsub : 0 + 148 + k = 148 + k := by omega
      simp only [hsub]
      exact getElem_append_left (by rw [hbase_sz]; omega)
        (hab := by rw [ByteArray.size_append, hbase_sz]; omega)
    have hbd_b : 148 + min 8 (encodeOctalField (ustarChecksum baseHdrPre) 6 ++ ByteArray.mk #[0x20]).size ≤
        baseHdrPre.size := by
      rw [hpre_sz, hcf_sz]; omega
    have h1 : baseHdr[148 + k]'(by rw [hbase_sz]; omega) =
        (blitFixed baseHdrPre 148 8 (encodeOctalField (ustarChecksum baseHdrPre) 6 ++ ByteArray.mk #[0x20]))[148 + k]'(by
          rw [blitFixed_size, hpre_sz]; omega) := by
      simp only [hbase_eq, patchHeaderChecksum]
    have h2 : (blitFixed baseHdrPre 148 8 (encodeOctalField (ustarChecksum baseHdrPre) 6 ++ ByteArray.mk #[0x20]))[148 + k]'(by
        rw [blitFixed_size, hpre_sz]; omega) =
        (encodeOctalField (ustarChecksum baseHdrPre) 6 ++ ByteArray.mk #[0x20])[k]'hk := by
      rw [blitFixed_getElem hbd_b (by rw [hpre_sz]; omega)]
      have hc : 148 ≤ 148 + k ∧ 148 + k < 148 + min 8 (encodeOctalField (ustarChecksum baseHdrPre) 6 ++ ByteArray.mk #[0x20]).size := by
        rw [hcf_sz]; omega
      rw [dite_eq_left hc]
      simp only [Nat.add_sub_cancel_left]
      rfl
    exact hb_l.trans (h1.trans h2)
  let chk := ustarChecksumAt (baseHdr ++ twoZeroBlocks) 0
  rcases encodeOctalField_loop_spec 6 chk [0] with ⟨ds, hds_eq, hds_len, hds_dig, _⟩
  cases hds : ds with
  | nil => simp [hds] at hds_len
  | cons d0 ds' =>
    have hds'_len : ds'.length = 5 := by simp [hds] at hds_len; omega
    have hraw_base : (baseHdr ++ twoZeroBlocks).extract 148 156 =
        (d0 :: (ds' ++ [0, 0x20])).toByteArray := by
      rw [hext_base_chk, encodeOctalField_append_space chk ds hds_eq hds_len, hds]
      rfl
    have hext_bad : bytes.extract 148 156 = (55 :: (ds' ++ [0, 0x20])).toByteArray := by
      have htsz : (55 :: (ds' ++ [0, 0x20])).toByteArray.size = 8 := by
        rw [List.size_toByteArray]; simp [hds'_len]
      have hext_off : bytes.extract 148 156 = bytes.extract (0 + 148) (0 + 156) := by
        simp only [Nat.zero_add]
      rw [hext_off]
      apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [hbytes_sz]; omega) htsz
      intro k hk
      have hk8 : k < 8 := by omega
      have hb_eq : bytes[0 + 148 + k]'(by rw [hbytes_sz]; omega) = hdr[148 + k]'(by rw [hhdr]; omega) := by
        have h1 : bytes[0 + 148 + k]'(by rw [hbytes_sz]; omega) =
            bytes[148 + k]'(by rw [hbytes_sz]; omega) := rfl
        rw [h1]
        exact getElem_append_left (by rw [hhdr]; omega) (hab := by rw [hbytes_sz]; omega)
      rw [hb_eq]
      change (baseHdr.set! 148 55)[148 + k]'(by rw [hhdr]; omega) = _
      rw [byteArray_set!_getElem_val (by rw [hbase_sz]; omega) (by rw [hbase_sz]; omega)]
      by_cases hk0 : k = 0
      · subst hk0
        simp only [Nat.add_zero, ↓reduceIte]
        rw [List.getElem_toByteArray]
        rfl
      · have hne : 148 ≠ 148 + k := by omega
        rw [ite_eq_right hne]
        have hbase_idx : baseHdr[148 + k]'(by rw [hbase_sz]; omega) =
            ((baseHdr ++ twoZeroBlocks).extract 148 156)[k]'(by
              rw [ByteArray.size_extract, ByteArray.size_append, hbase_sz]; omega) := by
          rw [ByteArray.getElem_extract, getElem_append_left (by rw [hbase_sz]; omega)
            (hab := by rw [ByteArray.size_append, hbase_sz]; omega)]
        rw [hbase_idx]
        have hk_ba : k < (d0 :: (ds' ++ [0, 0x20])).toByteArray.size := by
          rw [List.size_toByteArray]; simp [hds'_len]; omega
        have hcongr := congrArg (fun ba : ByteArray => if h : k < ba.size then ba[k]'h else 0) hraw_base
        have hk_ext : k < ((baseHdr ++ twoZeroBlocks).extract 148 156).size := by
          rw [ByteArray.size_extract, ByteArray.size_append, hbase_sz]; omega
        simp only [hk_ext, hk_ba, ↓reduceDIte] at hcongr
        rw [hcongr, List.getElem_toByteArray, List.getElem_toByteArray]
        cases k with
        | zero => exact absurd rfl hk0
        | succ m => rfl
    have hdig_ds' : ∀ b ∈ ds', (0x30 ≤ b && b ≤ 0x37) = true := by
      intro b hb
      have ⟨hlo, hhi⟩ := hds_dig b (by simp [hds, hb])
      simp [hlo, hhi]
    have hparse_bad : parseChecksumOctal bytes 148 156 0 =
        .ok ((55 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0) := by
      unfold parseChecksumOctal
      rw [hext_bad, toByteArray_toList]
      dsimp only
      have h55_ne_sp : ((55 : UInt8) == 0x20) = false := rfl
      have h55_dig : (0x30 ≤ (55 : UInt8) && (55 : UInt8) ≤ 0x37) = true := rfl
      have hdrop : (55 :: (ds' ++ [0, 0x20])).dropWhile (· == 0x20) = 55 :: (ds' ++ [0, 0x20]) := by
        simp [h55_ne_sp]
      have htake : (55 :: (ds' ++ [0, 0x20])).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = 55 :: ds' := by
        change ((55 :: ds') ++ [0, 0x20]).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = 55 :: ds'
        rw [List.takeWhile_append, list_takeWhile_eq_self _ (55 :: ds') (by
          intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact h55_dig
          · exact hdig_ds' b hb)]
        simp
      have hdrop2 : (55 :: (ds' ++ [0, 0x20])).drop (55 :: ds').length = [0, 0x20] := by
        change ((55 :: ds') ++ [0, 0x20]).drop (55 :: ds').length = [0, 0x20]
        simp
      rw [hdrop, htake, hdrop2]
      simp
    have hfold_ge : (55 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0 ≥ 7 * 8 ^ 5 := by
      have hgen : ∀ (xs : List UInt8) (init : Nat),
          xs.foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) init ≥ init * 8 ^ xs.length := by
        intro xs
        induction xs with
        | nil => intro init; simp
        | cons x xs ih =>
          intro init
          simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
          have hstep := ih (init * 8 + (x.toNat - 0x30))
          have hmul : init * (8 ^ xs.length * 8) = (init * 8) * 8 ^ xs.length := by
            rw [Nat.mul_comm (8 ^ xs.length) 8, ← Nat.mul_assoc]
          have hle : (init * 8) * 8 ^ xs.length ≤ (init * 8 + (x.toNat - 0x30)) * 8 ^ xs.length :=
            Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
          omega
      have h0 : ((55 : UInt8).toNat - 0x30) = 7 := rfl
      simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add, h0]
      have hg := hgen ds' 7
      rw [hds'_len] at hg
      exact hg
    have hchk_congr : ustarChecksumAt bytes 0 = chk := by
      apply ustarChecksumAt_congr (s1 := 0) (s2 := 0) (by rw [hbytes_sz]; omega)
        (by rw [ByteArray.size_append, hbase_sz]; omega)
      intro i hi hnot
      simp only [Nat.zero_add]
      have hl : bytes[i]'(by rw [hbytes_sz]; omega) = hdr[i]'(by rw [hhdr]; omega) :=
        getElem_append_left (by rw [hhdr]; omega) (hab := by rw [hbytes_sz]; omega)
      have hr : (baseHdr ++ twoZeroBlocks)[i]'(by
          rw [ByteArray.size_append, hbase_sz]; omega) =
          baseHdr[i]'(by rw [hbase_sz]; omega) :=
        getElem_append_left (by rw [hbase_sz]; omega)
          (hab := by rw [ByteArray.size_append, hbase_sz]; omega)
      rw [hl, hr]
      change (baseHdr.set! 148 55)[i]'(by rw [hhdr]; omega) = baseHdr[i]'(by rw [hbase_sz]; omega)
      rw [byteArray_set!_getElem_val (by rw [hbase_sz]; omega) (by rw [hbase_sz]; exact hi),
        ite_eq_right (by omega)]
    have hchk_le : chk ≤ 512 * 255 := by
      have hc : chk = ustarChecksum baseHdrPre := hp.1
      rw [hc]
      exact ustarChecksum_le baseHdrPre
    have hne : ((55 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0 != ustarChecksumAt bytes 0) = true := by
      rw [hchk_congr]
      have hpow : 7 * 8 ^ 5 = 229376 := by decide
      have hlim : 512 * 255 = 130560 := by decide
      have hne_nat : (55 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0 ≠ chk := by omega
      exact bne_iff_ne.mpr hne_nat
    have hparse_err : parseUstarHeader bytes 0 =
        .error { kind := .checksumMismatch, message := "USTAR header checksum mismatch", offset := some 0 } := by
      unfold parseUstarHeader
      simp only [Nat.zero_add] at hparse_bad ⊢
      rw [hparse_bad]
      dsimp only
      rw [ite_eq_left hne]
    have hu := unpackWith_hdr_rest_parseHeader_err hhdr twoZeroBlocks_pos twoZeroBlocks_mod h257 hparse_err
    refine ⟨_, hu, rfl, by decide⟩

/-- Case 1 of Test 5: `badChkVal` fails with `.checksumMismatch`. -/
theorem test5_badChkVal_err :
    ∃ e, Impl.unpackWith {} (baseHdr5.set! 148 55 ++ twoZeroBlocks) = .error e ∧
      e.kind = .checksumMismatch ∧ e.message ≠ "" :=
  badChkVal_abstract baseHdr5 baseHdr5Pre baseHdr5_size baseHdr5Pre_size baseHdr5_eq_patch baseHdr5_byte_257

private theorem badChkSyntax_abstract (hdr : ByteArray) (hhdr : hdr.size = 512)
    (h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0)
    (h148 : hdr[148]'(by rw [hhdr]; omega) = 88) :
    ∃ e, Impl.unpackWith {} (hdr ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let bytes := hdr ++ twoZeroBlocks
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hraw_len : (bytes.extract 148 156).toList.length = 8 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (bytes.extract 148 156).size = 8
    rw [ByteArray.size_extract, hbytes_sz]
    omega
  have hhead : ((bytes.extract 148 156).toList).head? = some 88 := by
    have h0_eq := byteArray_toList_getElem_zero (b := bytes.extract 148 156)
      (by rw [ByteArray.size_extract, hbytes_sz]; omega) (by rw [hraw_len]; omega)
    have hb148 : bytes[148 + 0]'(by rw [hbytes_sz]; omega) = 88 := by
      have h1 : bytes[148 + 0]'(by rw [hbytes_sz]; omega) = hdr[148]'(by rw [hhdr]; omega) :=
        getElem_append_left (by rw [hhdr]; omega) (hab := by rw [hbytes_sz]; omega)
      rw [h1, h148]
    cases hl : (bytes.extract 148 156).toList with
    | nil => rw [hl] at hraw_len; cases hraw_len
    | cons hd tl =>
      have hhd0 : hd = (bytes.extract 148 156)[0]'(by rw [ByteArray.size_extract, hbytes_sz]; omega) := by
        have hhd_lhs : hd = (hd :: tl)[0]'(Nat.zero_lt_succ _) := rfl
        have hhd_mid : (hd :: tl)[0]'(Nat.zero_lt_succ _) =
            (bytes.extract 148 156).toList[0]'(by rw [hraw_len]; omega) := by
          simp only [hl]
        exact hhd_lhs.trans (hhd_mid.trans h0_eq)
      rw [ByteArray.getElem_extract, hb148] at hhd0
      rw [hhd0]
      rfl
  have hparse_chk : parseChecksumOctal bytes 148 156 0 =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    unfold parseChecksumOctal
    cases hl : (bytes.extract 148 156).toList with
    | nil => rw [hl] at hraw_len; cases hraw_len
    | cons hd _tl =>
      rw [hl] at hhead
      have hhd : hd = 88 := Option.some.inj hhead
      subst hhd
      have hne_sp : ((88 : UInt8) == 0x20) = false := rfl
      have hnot_dig : (0x30 ≤ (88 : UInt8) && (88 : UInt8) ≤ 0x37) = false := rfl
      simp only [List.dropWhile_cons, hne_sp, Bool.false_eq_true, ↓reduceIte,
        List.takeWhile_cons, hnot_dig, List.isEmpty_nil]
  have hparse_err : parseUstarHeader bytes 0 =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hparse_chk]
  exact ⟨_, unpackWith_hdr_rest_parseHeader_err hhdr twoZeroBlocks_pos twoZeroBlocks_mod h257 hparse_err,
    rfl, by decide⟩

/-- Case 2 of Test 5: `badChkSyntax` fails with `.invalidHeader`. -/
theorem test5_badChkSyntax_err :
    ∃ e, Impl.unpackWith {} (baseHdr5.set! 148 88 ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let hdr := baseHdr5.set! 148 88
  have hhdr : hdr.size = 512 := (byteArray_set!_size _ _ _).trans baseHdr5_size
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    change (baseHdr5.set! 148 88)[257]'(by rw [hhdr]; omega) ≠ 0
    rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; omega)]
    rw [ite_eq_right (by omega), baseHdr5_byte_257]
    decide
  have h148 : hdr[148]'(by rw [hhdr]; omega) = 88 := by
    change (baseHdr5.set! 148 88)[148]'(by rw [hhdr]; omega) = 88
    rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; omega)]
    rw [ite_eq_left rfl]
  exact badChkSyntax_abstract hdr hhdr h257 h148

private theorem allNulChk_abstract (hdr : ByteArray) (hhdr : hdr.size = 512)
    (h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0)
    (hext_nul : (hdr ++ twoZeroBlocks).extract 148 156 = { data := Array.replicate 8 0 }) :
    ∃ e, Impl.unpackWith {} (hdr ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let nul8 : ByteArray := { data := Array.replicate 8 0 }
  have hnul_list : nul8.data.toList = [0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hparse_err : parseUstarHeader (hdr ++ twoZeroBlocks) 0 =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    unfold parseUstarHeader parseChecksumOctal
    simp only [Nat.zero_add]
    rw [hext_nul, byteArray_toList_eq, hnul_list]
    rfl
  exact ⟨_, unpackWith_hdr_rest_parseHeader_err hhdr twoZeroBlocks_pos twoZeroBlocks_mod h257 hparse_err,
    rfl, by decide⟩

/-- Case 3 of Test 5: `allNulChk` fails with `.invalidHeader`. -/
theorem test5_allNulChk_err :
    ∃ e, Impl.unpackWith {} (blitFixed baseHdr5 148 8 { data := Array.replicate 8 0 } ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let nul8 : ByteArray := { data := Array.replicate 8 0 }
  let hdr := blitFixed baseHdr5 148 8 nul8
  let bytes := hdr ++ twoZeroBlocks
  have hnul_sz : nul8.size = 8 := by decide
  have hhdr : hdr.size = 512 := (blitFixed_size _ _ _ _).trans baseHdr5_size
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hbd_blit : 148 + min 8 nul8.size ≤ baseHdr5.size := by
    rw [baseHdr5_size, hnul_sz]; omega
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    change (blitFixed baseHdr5 148 8 nul8)[257]'(by rw [hhdr]; omega) ≠ 0
    rw [blitFixed_getElem hbd_blit (by rw [baseHdr5_size]; omega)]
    rw [dite_eq_right (by rw [hnul_sz]; omega), baseHdr5_byte_257]
    decide
  have hext_nul : bytes.extract 148 156 = nul8 := by
    have h156 : bytes.extract 148 156 = bytes.extract (0 + 148) (0 + 156) := by simp only [Nat.zero_add]
    rw [h156]
    apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [hbytes_sz]; omega) hnul_sz
    intro k hk
    have hk8 : k < 8 := by omega
    have hl : bytes[0 + 148 + k]'(by rw [hbytes_sz]; omega) = hdr[148 + k]'(by rw [hhdr]; omega) := by
      have h1 : bytes[0 + 148 + k]'(by rw [hbytes_sz]; omega) =
          bytes[148 + k]'(by rw [hbytes_sz]; omega) := rfl
      rw [h1]
      exact getElem_append_left (by rw [hhdr]; omega) (hab := by rw [hbytes_sz]; omega)
    rw [hl]
    change (blitFixed baseHdr5 148 8 nul8)[148 + k]'(by rw [hhdr]; omega) = _
    rw [blitFixed_getElem hbd_blit (by rw [baseHdr5_size]; omega)]
    have hc : 148 ≤ 148 + k ∧ 148 + k < 148 + min 8 nul8.size := by rw [hnul_sz]; omega
    rw [dite_eq_left hc]
    simp only [(by omega : 148 + k - 148 = k)]
  exact allNulChk_abstract hdr hhdr h257 hext_nul

private theorem badMagic_abstract (hdrPre : ByteArray) (hpre : hdrPre.size = 512)
    (hpre_257 : hdrPre[257]'(by rw [hpre]; omega) = 0x6e)
    (hm_slice : ∀ (k : Nat) (hk : k < 6), hdrPre[257 + k]'(by rw [hpre]; omega) =
      ({ data := #[0x6e, 0x6f, 0x74, 0x75, 0x73, 0x74] } : ByteArray)[k]'(by show k < 6; exact hk)) :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum hdrPre ++ twoZeroBlocks) =
      .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let hdr := patchHeaderChecksum hdrPre
  let bytes := hdr ++ twoZeroBlocks
  have hhdr : hdr.size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head hdr twoZeroBlocks hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), hpre_257]
    decide
  let tgt : ByteArray := { data := #[0x6e, 0x6f, 0x74, 0x75, 0x73, 0x74] }
  have hext_magic : bytes.extract 257 263 = tgt := by
    have h263 : (263 : Nat) = 257 + 6 := by omega
    rw [h263]
    exact extract_patch_eq_slice hpre (by omega) (by decide : tgt.size = 6) (fun k hk => by omega) hm_slice
  have hm1 : (tgt.toList == ([117, 115, 116, 97, 114, 0] : List UInt8)) = false := by
    rw [byteArray_toList_eq]; decide
  have hm2 : (tgt.toList == ([117, 115, 116, 97, 114, 32] : List UInt8)) = false := by
    rw [byteArray_toList_eq]; decide
  have hbad_magic : hasValidMagic bytes 0 = false := by
    unfold hasValidMagic
    simp only [Nat.zero_add, hext_magic]
    rw [hm1, hm2]
    rfl
  have hparse_err : parseUstarHeader bytes 0 =
      .error { kind := .invalidHeader, message := "invalid USTAR magic or version", offset := some 0 } := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hchk.2]
    dsimp only
    rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_left (by rw [hbad_magic]; rfl)]
  exact ⟨_, unpackWith_hdr_rest_parseHeader_err hhdr twoZeroBlocks_pos twoZeroBlocks_mod h257 hparse_err,
    rfl, by decide⟩

/-- Case 4 of Test 5: `badMagic` fails with `.invalidHeader`. -/
theorem test5_badMagic_err :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum (blitFixed baseHdr5 257 6 "notust".toUTF8) ++ twoZeroBlocks) =
      .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let src := "notust".toUTF8
  have hsrc_bytes : src = { data := #[0x6e, 0x6f, 0x74, 0x75, 0x73, 0x74] } := by
    dsimp [src]; rw [toUTF8_eq_toByteArray]; decide
  have hsrc_sz : src.size = 6 := by rw [hsrc_bytes]; rfl
  have hpre : (blitFixed baseHdr5 257 6 src).size = 512 := (blitFixed_size _ _ _ _).trans baseHdr5_size
  have hbd_blit : 257 + min 6 src.size ≤ baseHdr5.size := by rw [baseHdr5_size, hsrc_sz]; omega
  refine badMagic_abstract (blitFixed baseHdr5 257 6 src) hpre ?_ ?_
  · rw [blitFixed_getElem hbd_blit (by rw [baseHdr5_size]; omega)]
    rw [dite_eq_left (by rw [hsrc_sz]; omega)]
    simp only [Nat.sub_self, hsrc_bytes]; rfl
  · intro k hk
    rw [blitFixed_getElem hbd_blit (by rw [baseHdr5_size]; omega)]
    rw [dite_eq_left (by rw [hsrc_sz]; omega)]
    simp only [(by omega : 257 + k - 257 = k), hsrc_bytes]

private theorem blitFixed_baseHdr5_257 (off w : Nat) (src : ByteArray)
    (hoff : off + min w src.size ≤ 257) :
    (blitFixed baseHdr5 off w src)[257]'(by rw [blitFixed_size, baseHdr5_size]; omega) = 0x75 := by
  rw [blitFixed_getElem (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; omega)]
  rw [dite_eq_right (by omega), baseHdr5_byte_257]

private theorem blitFixed_baseHdr5_outside (off w : Nat) (src : ByteArray)
    (hbd : off + min w src.size ≤ 512) (i : Nat) (hi : i < 512)
    (hdisj : i < off ∨ off + min w src.size ≤ i) :
    (blitFixed baseHdr5 off w src)[i]'(by rw [blitFixed_size, baseHdr5_size]; exact hi) =
      baseHdr5[i]'(by rw [baseHdr5_size]; exact hi) := by
  rw [blitFixed_getElem (by rw [baseHdr5_size]; exact hbd) (by rw [baseHdr5_size]; exact hi)]
  rw [dite_eq_right (by omega)]

private theorem negBase256_abstract (hdrPre : ByteArray) (hpre : hdrPre.size = 512)
    (h257_pre : hdrPre[257]'(by rw [hpre]; omega) = 0x75)
    (hmag : ∀ (k : Nat) (_hk : k < 8), hdrPre[257 + k]'(by rw [hpre]; omega) =
      baseHdr5[257 + k]'(by rw [baseHdr5_size]; omega))
    (hmod_pre : ∀ (k : Nat) (_hk : k < 8), hdrPre[100 + k]'(by rw [hpre]; omega) =
      baseHdr5[100 + k]'(by rw [baseHdr5_size]; omega))
    (huid_pre : ∀ (k : Nat) (_hk : k < 8), hdrPre[108 + k]'(by rw [hpre]; omega) =
      baseHdr5[108 + k]'(by rw [baseHdr5_size]; omega))
    (hgid_pre : ∀ (k : Nat) (_hk : k < 8), hdrPre[116 + k]'(by rw [hpre]; omega) =
      baseHdr5[116 + k]'(by rw [baseHdr5_size]; omega))
    (hsize_pre : ∀ (k : Nat) (hk : k < 12), hdrPre[124 + k]'(by rw [hpre]; omega) =
      ({ data := Array.replicate 12 255 } : ByteArray)[k]'(by show k < (Array.replicate 12 (255 : UInt8)).size; simp; exact hk)) :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum hdrPre ++ twoZeroBlocks) =
      .error e ∧ e.kind = .sizeOverflow ∧ e.message ≠ "" := by
  let src : ByteArray := { data := Array.replicate 12 255 }
  let hdr := patchHeaderChecksum hdrPre
  let bytes := hdr ++ twoZeroBlocks
  have hsrc_sz : src.size = 12 := by decide
  have hhdr : hdr.size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head hdr twoZeroBlocks hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), h257_pre]
    decide
  have hmagic : hasValidMagic bytes 0 = true := patch_agree_magic twoZeroBlocks hpre hmag
  have hmode := patch_agree_mode twoZeroBlocks hpre hmod_pre
  have huid := patch_agree_uid twoZeroBlocks hpre huid_pre
  have hgid := patch_agree_gid twoZeroBlocks hpre hgid_pre
  have hext_size : bytes.extract 124 136 = src := by
    have h136 : (136 : Nat) = 124 + 12 := by omega
    rw [h136]
    exact extract_patch_eq_slice hpre (by omega) hsrc_sz (fun k hk => by omega) hsize_pre
  have hsrc_list : src.data.toList = List.replicate 12 255 := by decide
  have hparse_size : parseUstarNumeric bytes 124 136 0 false u64Limit "size" =
      .error { kind := .sizeOverflow, message := "negative base-256 USTAR size", offset := some 0 } := by
    unfold parseUstarNumeric
    rw [hext_size, byteArray_toList_eq, hsrc_list]
    rfl
  have hparse_err : parseUstarHeader bytes 0 =
      .error { kind := .sizeOverflow, message := "negative base-256 USTAR size", offset := some 0 } := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hchk.2]
    dsimp only
    rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_right (by rw [hmagic]; decide),
      hmode, huid, hgid, hparse_size]
  exact ⟨_, unpackWith_hdr_rest_parseHeader_err hhdr twoZeroBlocks_pos twoZeroBlocks_mod h257 hparse_err,
    rfl, by decide⟩

/-- Case 5 of Test 5: `negBase256` fails with `.sizeOverflow`. -/
theorem test5_negBase256_err :
    ∃ e, Impl.unpackWith {}
        (patchHeaderChecksum (blitFixed baseHdr5 124 12 { data := Array.replicate 12 255 }) ++ twoZeroBlocks) =
      .error e ∧ e.kind = .sizeOverflow ∧ e.message ≠ "" := by
  let src : ByteArray := { data := Array.replicate 12 255 }
  have hsrc_sz : src.size = 12 := by decide
  have hpre : (blitFixed baseHdr5 124 12 src).size = 512 := (blitFixed_size _ _ _ _).trans baseHdr5_size
  have hbd_blit : 124 + min 12 src.size ≤ 512 := by rw [hsrc_sz]; omega
  refine negBase256_abstract (blitFixed baseHdr5 124 12 src) hpre
    (blitFixed_baseHdr5_257 124 12 src (by rw [hsrc_sz]; omega))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (257 + k) (by omega) (Or.inr (by omega)))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (100 + k) (by omega) (Or.inl (by omega)))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (108 + k) (by omega) (Or.inl (by omega)))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (116 + k) (by omega) (Or.inl (by omega)))
    ?_
  intro k hk
  rw [blitFixed_getElem (by rw [baseHdr5_size]; exact hbd_blit) (by rw [baseHdr5_size]; omega)]
  rw [dite_eq_left (by rw [hsrc_sz]; omega)]
  simp only [(by omega : 124 + k - 124 = k)]
  rfl

private theorem decodeTarEntry_regular_a_txt {bytes : ByteArray}
    (hbytes_sz : bytes.size = 512 + twoZeroBlocks.size)
    (uid : Nat)
    (hstrs : decodeCStringUtf8 bytes 0 100 0 "name" = .ok "a.txt" ∧
      decodeCStringUtf8 bytes 265 297 0 "uname" = .ok "" ∧
      decodeCStringUtf8 bytes 297 329 0 "gname" = .ok "" ∧
      decodeCStringUtf8 bytes 345 500 0 "prefix" = .ok "") :
    let fields : UstarHeaderFields :=
      { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := uid, gid := 0, size := 0, mtime := 0, typeflag := 48 }
    let entry : TarEntry :=
      { path := "a.txt", kind := .regular, mode := 420, uid := uid, gid := 0, mtime := 0,
        uname := "", gname := "", data := ByteArray.empty, linkTarget := "" }
    decodeTarEntry {} bytes 0 fields none [] 0 0 = .ok (entry, 0) := by
  intro fields entry
  rw [decodeTarEntry.eq_1]
  have hval : validateEntryPath false false .regular "a.txt" = .ok "a.txt" := rfl
  have htf : (fields.typeflag == 0x30 || fields.typeflag == 0x00) = true := rfl
  have hreg_ne : ¬((EntryKind.regular != EntryKind.regular && 0 != 0) = true) := by decide
  have hmaxe : ¬(0 + 1 > ({} : UnpackOptions).maxEntries) := by decide
  have hmaxb : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes) := by decide
  have hpad0 : pad512 0 = 0 := rfl
  have htrunc : ¬(512 + 0 > bytes.size) := by rw [hbytes_sz, twoZeroBlocks_size]; omega
  have hseen : ¬(([].contains "a.txt") = true) := by decide
  have hmod : (((420 : UInt32) &&& 0o7777).toNat &&& 0o7777).toUInt32 = 420 := by decide
  dsimp only [fields]
  rw [ite_eq_left htf]
  dsimp only
  simp only [Nat.zero_add, Option.getD_none, hpad0]
  have hpath : (if ("" : String).isEmpty then "a.txt" else "" ++ "/" ++ "a.txt") = "a.txt" := rfl
  rw [ite_eq_right hreg_ne, ite_eq_right hmaxe, ite_eq_right hmaxb, ite_eq_right htrunc,
    hstrs.1, hstrs.2.2.2, hstrs.2.1, hstrs.2.2.1]
  dsimp only
  rw [hpath, hval]
  dsimp only
  rw [ite_eq_right hseen]
  dsimp only [entry]
  simp only [hmod]
  rfl

private theorem uidRegular_abstract (hdrPre : ByteArray) (uidVal : Nat) (hpre : hdrPre.size = 512)
    (hagree : ∀ (i : Nat) (hi : i < 512), ¬(108 ≤ i ∧ i < 116) →
      hdrPre[i]'(by rw [hpre]; exact hi) = baseHdr5[i]'(by rw [baseHdr5_size]; exact hi))
    (huid : parseUstarNumeric (patchHeaderChecksum hdrPre ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" =
      .ok uidVal) :
    ∃ res, Impl.unpackWith {} (patchHeaderChecksum hdrPre ++ twoZeroBlocks) =
      .ok res ∧ TarEquiv [{ path := "a.txt", kind := .regular, uid := uidVal }] res := by
  let hdr := patchHeaderChecksum hdrPre
  let bytes := hdr ++ twoZeroBlocks
  have hhdr : hdr.size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head hdr twoZeroBlocks hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), hagree 257 (by omega) (by omega), baseHdr5_byte_257]
    decide
  have hmagic := patch_agree_magic twoZeroBlocks hpre fun k hk => hagree (257 + k) (by omega) (by omega)
  have hmode := patch_agree_mode twoZeroBlocks hpre fun k hk => hagree (100 + k) (by omega) (by omega)
  have hgid := patch_agree_gid twoZeroBlocks hpre fun k hk => hagree (116 + k) (by omega) (by omega)
  have hsize := patch_agree_size twoZeroBlocks hpre fun k hk => hagree (124 + k) (by omega) (by omega)
  have hmtime := patch_agree_mtime twoZeroBlocks hpre fun k hk => hagree (136 + k) (by omega) (by omega)
  have h156 : bytes[156]'(by rw [hbytes_sz]; omega) = 48 := by
    rw [hp.2.2 156 (by omega) (by omega), hagree 156 (by omega) (by omega), baseHdr5_byte_156]
  let fields : UstarHeaderFields :=
    { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := uidVal, gid := 0, size := 0, mtime := 0, typeflag := 48 }
  have hparse : parseUstarHeader bytes 0 = .ok fields := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hchk.2]
    dsimp only
    rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_right (by rw [hmagic]; decide),
      hmode, huid, hgid, hsize, hmtime]
    have hlt156 : 156 < bytes.size := by rw [hbytes_sz]; omega
    rw [dite_eq_left hlt156, h156]
  have hstrs := patch_agree_regular_strings twoZeroBlocks hpre
    (fun k hk => hagree (0 + k) (by omega) (by omega))
    (fun k hk => hagree (265 + k) (by omega) (by omega))
    (fun k hk => hagree (297 + k) (by omega) (by omega))
    (fun k hk => hagree (345 + k) (by omega) (by omega))
  let entry : TarEntry :=
    { path := "a.txt", kind := .regular, mode := 420, uid := uidVal, gid := 0, mtime := 0,
      uname := "", gname := "", data := ByteArray.empty, linkTarget := "" }
  have hdec := decodeTarEntry_regular_a_txt hbytes_sz uidVal hstrs
  refine ⟨[entry], unpackWith_hdr_twoZero_regular_ok hhdr h257 hparse rfl rfl hdec, ?_⟩
  exact tarEquiv_singleton_self entry

private theorem extract_patch_blit108 (src : ByteArray) (hsrc_sz : src.size = 8) :
    (patchHeaderChecksum (blitFixed baseHdr5 108 8 src) ++ twoZeroBlocks).extract 108 116 = src := by
  have hpre : (blitFixed baseHdr5 108 8 src).size = 512 := (blitFixed_size _ _ _ _).trans baseHdr5_size
  have hbd_blit : 108 + min 8 src.size ≤ 512 := by rw [hsrc_sz]; omega
  have h116 : (116 : Nat) = 108 + 8 := by omega
  rw [h116]
  refine extract_patch_eq_slice hpre (by omega) hsrc_sz (fun k hk => by omega) ?_
  intro k hk
  change (blitFixed baseHdr5 108 8 src)[108 + k]'(by rw [hpre]; omega) = src[k]'(by rw [hsrc_sz]; exact hk)
  rw [blitFixed_getElem (by rw [baseHdr5_size]; exact hbd_blit) (by rw [baseHdr5_size]; omega)]
  rw [dite_eq_left (by rw [hsrc_sz]; omega)]
  simp only [(by omega : 108 + k - 108 = k)]

/-- Case 6 of Test 5: `posBase256Uid` succeeds with `uid := 42`. -/
theorem test5_posBase256Uid_ok :
    ∃ res, Impl.unpackWith {}
        (patchHeaderChecksum (blitFixed baseHdr5 108 8 { data := #[128, 0, 0, 0, 0, 0, 0, 42] }) ++ twoZeroBlocks) =
      .ok res ∧ TarEquiv [{ path := "a.txt", kind := .regular, uid := 42 }] res := by
  let src : ByteArray := { data := #[128, 0, 0, 0, 0, 0, 0, 42] }
  let hdrPre := blitFixed baseHdr5 108 8 src
  have hsrc_sz : src.size = 8 := by decide
  have hpre : hdrPre.size = 512 := (blitFixed_size _ _ _ _).trans baseHdr5_size
  have hbd_blit : 108 + min 8 src.size ≤ 512 := by rw [hsrc_sz]; omega
  have hext_uid := extract_patch_blit108 src hsrc_sz
  have huid : parseUstarNumeric (patchHeaderChecksum hdrPre ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 42 := by
    unfold parseUstarNumeric
    rw [hext_uid, byteArray_toList_eq]
    have h42 : ¬((42 : Nat) ≥ u64Limit) := by decide
    have hmsb : ((128 : UInt8) &&& 128 != 0) = true := rfl
    have hsign : ¬(((128 : UInt8) &&& 64 != 0) = true) := by decide
    have hval42 : List.foldl (fun acc (b : UInt8) => acc * 256 + b.toNat)
        ((128 : UInt8) &&& 127).toNat [0, 0, 0, 0, 0, 0, 42] = 42 := rfl
    simp only [src]
    rw [ite_eq_left hmsb, ite_eq_right hsign, hval42, ite_eq_right h42]
  refine uidRegular_abstract hdrPre 42 hpre ?_ huid
  intro i hi hnot
  exact blitFixed_baseHdr5_outside 108 8 src hbd_blit i hi (by omega)

private theorem nulSize_abstract (hdrPre : ByteArray) (hpre : hdrPre.size = 512)
    (h257_pre : hdrPre[257]'(by rw [hpre]; omega) = 0x75)
    (hmag : ∀ (k : Nat) (_hk : k < 8), hdrPre[257 + k]'(by rw [hpre]; omega) =
      baseHdr5[257 + k]'(by rw [baseHdr5_size]; omega))
    (hmod_pre : ∀ (k : Nat) (_hk : k < 8), hdrPre[100 + k]'(by rw [hpre]; omega) =
      baseHdr5[100 + k]'(by rw [baseHdr5_size]; omega))
    (huid_pre : ∀ (k : Nat) (_hk : k < 8), hdrPre[108 + k]'(by rw [hpre]; omega) =
      baseHdr5[108 + k]'(by rw [baseHdr5_size]; omega))
    (hgid_pre : ∀ (k : Nat) (_hk : k < 8), hdrPre[116 + k]'(by rw [hpre]; omega) =
      baseHdr5[116 + k]'(by rw [baseHdr5_size]; omega))
    (hsize_pre : ∀ (k : Nat) (hk : k < 12), hdrPre[124 + k]'(by rw [hpre]; omega) =
      ({ data := Array.replicate 12 0 } : ByteArray)[k]'(by show k < (Array.replicate 12 (0 : UInt8)).size; simp; exact hk)) :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum hdrPre ++ twoZeroBlocks) =
      .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let src : ByteArray := { data := Array.replicate 12 0 }
  let hdr := patchHeaderChecksum hdrPre
  let bytes := hdr ++ twoZeroBlocks
  have hsrc_sz : src.size = 12 := by decide
  have hhdr : hdr.size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head hdr twoZeroBlocks hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), h257_pre]
    decide
  have hmagic : hasValidMagic bytes 0 = true := patch_agree_magic twoZeroBlocks hpre hmag
  have hmode := patch_agree_mode twoZeroBlocks hpre hmod_pre
  have huid := patch_agree_uid twoZeroBlocks hpre huid_pre
  have hgid := patch_agree_gid twoZeroBlocks hpre hgid_pre
  have hext_size : bytes.extract 124 136 = src := by
    have h136 : (136 : Nat) = 124 + 12 := by omega
    rw [h136]
    exact extract_patch_eq_slice hpre (by omega) hsrc_sz (fun k hk => by omega) hsize_pre
  have hsrc_list : src.data.toList = List.replicate 12 0 := by decide
  have hparse_size : parseUstarNumeric bytes 124 136 0 false u64Limit "size" =
      .error { kind := .invalidHeader, message := "missing USTAR size", offset := some 0 } := by
    unfold parseUstarNumeric
    rw [hext_size, byteArray_toList_eq, hsrc_list]
    rfl
  have hparse_err : parseUstarHeader bytes 0 =
      .error { kind := .invalidHeader, message := "missing USTAR size", offset := some 0 } := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hchk.2]
    dsimp only
    rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_right (by rw [hmagic]; decide),
      hmode, huid, hgid, hparse_size]
  exact ⟨_, unpackWith_hdr_rest_parseHeader_err hhdr twoZeroBlocks_pos twoZeroBlocks_mod h257 hparse_err,
    rfl, by decide⟩

/-- Case 7 of Test 5: `nulSize` fails with `.invalidHeader`. -/
theorem test5_nulSize_err :
    ∃ e, Impl.unpackWith {}
        (patchHeaderChecksum (blitFixed baseHdr5 124 12 { data := Array.replicate 12 0 }) ++ twoZeroBlocks) =
      .error e ∧ e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let src : ByteArray := { data := Array.replicate 12 0 }
  have hsrc_sz : src.size = 12 := by decide
  have hpre : (blitFixed baseHdr5 124 12 src).size = 512 := (blitFixed_size _ _ _ _).trans baseHdr5_size
  have hbd_blit : 124 + min 12 src.size ≤ 512 := by rw [hsrc_sz]; omega
  refine nulSize_abstract (blitFixed baseHdr5 124 12 src) hpre
    (blitFixed_baseHdr5_257 124 12 src (by rw [hsrc_sz]; omega))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (257 + k) (by omega) (Or.inr (by omega)))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (100 + k) (by omega) (Or.inl (by omega)))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (108 + k) (by omega) (Or.inl (by omega)))
    (fun k hk => blitFixed_baseHdr5_outside 124 12 src hbd_blit (116 + k) (by omega) (Or.inl (by omega)))
    ?_
  intro k hk
  rw [blitFixed_getElem (by rw [baseHdr5_size]; exact hbd_blit) (by rw [baseHdr5_size]; omega)]
  rw [dite_eq_left (by rw [hsrc_sz]; omega)]
  simp only [(by omega : 124 + k - 124 = k)]
  rfl

/-- Case 8 of Test 5: `nulUid` succeeds with `uid := 0`. -/
theorem test5_nulUid_ok :
    ∃ res, Impl.unpackWith {}
        (patchHeaderChecksum (blitFixed baseHdr5 108 8 { data := Array.replicate 8 0 }) ++ twoZeroBlocks) =
      .ok res ∧ TarEquiv [{ path := "a.txt", kind := .regular }] res := by
  let src : ByteArray := { data := Array.replicate 8 0 }
  let hdrPre := blitFixed baseHdr5 108 8 src
  have hsrc_sz : src.size = 8 := by decide
  have hpre : hdrPre.size = 512 := (blitFixed_size _ _ _ _).trans baseHdr5_size
  have hbd_blit : 108 + min 8 src.size ≤ 512 := by rw [hsrc_sz]; omega
  have hext_uid := extract_patch_blit108 src hsrc_sz
  have hsrc_list : src.data.toList = List.replicate 8 0 := by decide
  have huid : parseUstarNumeric (patchHeaderChecksum hdrPre ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 := by
    unfold parseUstarNumeric
    rw [hext_uid, byteArray_toList_eq, hsrc_list]
    rfl
  refine uidRegular_abstract hdrPre 0 hpre ?_ huid
  intro i hi hnot
  exact blitFixed_baseHdr5_outside 108 8 src hbd_blit i hi (by omega)

private theorem parseUstarHeader_set156_abstract (hdrPre rest : ByteArray) (tf : UInt8)
    (hpre : hdrPre.size = 512) (hrest_pos : 0 < rest.size)
    (hagree : ∀ (i : Nat) (hi : i < 512), i ≠ 156 →
      hdrPre[i]'(by rw [hpre]; exact hi) = baseHdr5[i]'(by rw [baseHdr5_size]; exact hi))
    (h156_pre : hdrPre[156]'(by rw [hpre]; omega) = tf) :
    let bytes := patchHeaderChecksum hdrPre ++ rest
    (patchHeaderChecksum hdrPre).size = 512 ∧
    (patchHeaderChecksum hdrPre)[257]'(by rw [patchHeaderChecksum_size, hpre]; omega) ≠ 0 ∧
    parseUstarHeader bytes 0 = .ok
      { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := tf } := by
  intro bytes
  have hhdr : (patchHeaderChecksum hdrPre).size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hbytes_sz : bytes.size = 512 + rest.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head _ rest hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : (patchHeaderChecksum hdrPre)[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) =
        (patchHeaderChecksum hdrPre)[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), hagree 257 (by omega) (by omega), baseHdr5_byte_257]
    decide
  have hmagic : hasValidMagic bytes 0 = true :=
    patch_agree_magic rest hpre fun k hk => hagree (257 + k) (by omega) (by omega)
  have hmode := patch_agree_mode rest hpre fun k hk => hagree (100 + k) (by omega) (by omega)
  have huid := patch_agree_uid rest hpre fun k hk => hagree (108 + k) (by omega) (by omega)
  have hgid := patch_agree_gid rest hpre fun k hk => hagree (116 + k) (by omega) (by omega)
  have hsize := patch_agree_size rest hpre fun k hk => hagree (124 + k) (by omega) (by omega)
  have hmtime := patch_agree_mtime rest hpre fun k hk => hagree (136 + k) (by omega) (by omega)
  have h156 : bytes[156]'(by rw [hbytes_sz]; omega) = tf := by
    rw [hp.2.2 156 (by omega) (by omega), h156_pre]
  refine ⟨hhdr, h257, ?_⟩
  unfold parseUstarHeader
  simp only [Nat.zero_add]
  rw [hchk.2]
  dsimp only
  rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_right (by rw [hmagic]; decide),
    hmode, huid, hgid, hsize, hmtime]
  have hlt156 : 156 < bytes.size := by rw [hbytes_sz]; omega
  rw [dite_eq_left hlt156, h156]

private theorem parseUstarHeader_set156 (rest : ByteArray) (tf : UInt8)
    (hrest_pos : 0 < rest.size) (_hrest_mod : rest.size % 512 = 0) :
    let hdrPre := baseHdr5.set! 156 tf
    let bytes := patchHeaderChecksum hdrPre ++ rest
    hdrPre.size = 512 ∧
    (patchHeaderChecksum hdrPre).size = 512 ∧
    (patchHeaderChecksum hdrPre)[257]'(by
      rw [patchHeaderChecksum_size, byteArray_set!_size, baseHdr5_size]; omega) ≠ 0 ∧
    parseUstarHeader bytes 0 = .ok
      { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := tf } := by
  intro hdrPre _bytes
  have hpre : hdrPre.size = 512 := (byteArray_set!_size _ _ _).trans baseHdr5_size
  have hagree : ∀ (i : Nat) (hi : i < 512), i ≠ 156 →
      hdrPre[i]'(by rw [hpre]; exact hi) = baseHdr5[i]'(by rw [baseHdr5_size]; exact hi) := by
    intro i hi hne
    change (baseHdr5.set! 156 tf)[i]'(by rw [hpre]; exact hi) = _
    rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; exact hi)]
    exact ite_eq_right (by omega)
  have h156 : hdrPre[156]'(by rw [hpre]; omega) = tf := by
    change (baseHdr5.set! 156 tf)[156]'(by rw [hpre]; omega) = tf
    rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; omega)]
    simp
  have hab := parseUstarHeader_set156_abstract hdrPre rest tf hpre hrest_pos hagree h156
  exact ⟨hpre, hab.1, hab.2.1, hab.2.2⟩

/-- Case 9 of Test 5: `hardlink` fails with `.unsupportedEntry`. -/
theorem test5_hardlink_err :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum (baseHdr5.set! 156 49) ++ twoZeroBlocks) = .error e ∧
      e.kind = .unsupportedEntry ∧ e.message ≠ "" := by
  have hp := parseUstarHeader_set156 twoZeroBlocks 49 twoZeroBlocks_pos twoZeroBlocks_mod
  let hdr := patchHeaderChecksum (baseHdr5.set! 156 49)
  let fields : UstarHeaderFields :=
    { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 49 }
  have hdec : decodeTarEntry {} (hdr ++ twoZeroBlocks) 0 fields none [] 0 0 =
      .error {
        kind := .unsupportedEntry,
        message := "unsupported tar entry typeflag: " ++ toString (49 : UInt8).toNat,
        offset := some 0 } := by
    rw [decodeTarEntry.eq_1]
    have h1 : (fields.typeflag == 0x30 || fields.typeflag == 0x00) = false := rfl
    have h2 : (fields.typeflag == 0x35) = false := rfl
    have h3 : (fields.typeflag == 0x32) = false := rfl
    simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
    rfl
  exact ⟨_, unpackWith_hdr_rest_decode_err hp.2.1 twoZeroBlocks_pos twoZeroBlocks_mod hp.2.2.1 hp.2.2.2
    rfl hdec, rfl, by decide⟩

/-- Case 10 of Test 5: `globalPax` fails with `.unsupportedEntry`. -/
theorem test5_globalPax_err :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum (baseHdr5.set! 156 103) ++ twoZeroBlocks) = .error e ∧
      e.kind = .unsupportedEntry ∧ e.message ≠ "" := by
  have hp := parseUstarHeader_set156 twoZeroBlocks 103 twoZeroBlocks_pos twoZeroBlocks_mod
  let hdr := patchHeaderChecksum (baseHdr5.set! 156 103)
  let fields : UstarHeaderFields :=
    { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 103 }
  have hdec : decodeTarEntry {} (hdr ++ twoZeroBlocks) 0 fields none [] 0 0 =
      .error {
        kind := .unsupportedEntry,
        message := "unsupported tar entry typeflag: " ++ toString (103 : UInt8).toNat,
        offset := some 0 } := by
    rw [decodeTarEntry.eq_1]
    have h1 : (fields.typeflag == 0x30 || fields.typeflag == 0x00) = false := rfl
    have h2 : (fields.typeflag == 0x35) = false := rfl
    have h3 : (fields.typeflag == 0x32) = false := rfl
    simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
    rfl
  exact ⟨_, unpackWith_hdr_rest_decode_err hp.2.1 twoZeroBlocks_pos twoZeroBlocks_mod hp.2.2.1 hp.2.2.2
    rfl hdec, rfl, by decide⟩

private theorem badDir_abstract (hdrPre : ByteArray) (hpre : hdrPre.size = 512)
    (hpre_get : ∀ (i : Nat) (hi : i < 512), ¬(124 ≤ i ∧ i < 136) → i ≠ 156 →
      hdrPre[i]'(by rw [hpre]; exact hi) = baseHdr5[i]'(by rw [baseHdr5_size]; exact hi))
    (hsize_pre : ∀ (k : Nat) (hk : k < 12), hdrPre[124 + k]'(by rw [hpre]; omega) =
      (encodeOctalField 5 11)[k]'(by rw [encodeOctalField_size]; exact hk))
    (h156_pre : hdrPre[156]'(by rw [hpre]; omega) = 53) :
    ∃ e, Impl.unpackWith {}
        (patchHeaderChecksum hdrPre ++ padBlock512 "12345".toUTF8 ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let src := encodeOctalField 5 11
  let hdr := patchHeaderChecksum hdrPre
  let rest := padBlock512 "12345".toUTF8 ++ twoZeroBlocks
  let bytes := hdr ++ rest
  have hsrc_sz : src.size = 12 := encodeOctalField_size _ 11
  have hhdr : hdr.size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hpad5_sz : (padBlock512 "12345".toUTF8).size = 512 := by
    rw [padBlock512_size]
    have hsz : "12345".toUTF8.size = 5 := by rw [toUTF8_eq_toByteArray]; decide
    rw [hsz]
    decide
  have hrest_sz : rest.size = 512 + 1024 := by
    simp only [rest, ByteArray.size_append, hpad5_sz, twoZeroBlocks_size]
  have hrest_pos : 0 < rest.size := by omega
  have hrest_mod : rest.size % 512 = 0 := by omega
  have hbytes_sz : bytes.size = 512 + rest.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head hdr rest hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), hpre_get 257 (by omega) (by omega) (by omega), baseHdr5_byte_257]
    decide
  have hmagic := patch_agree_magic rest hpre fun k hk => hpre_get (257 + k) (by omega) (by omega) (by omega)
  have hmode := patch_agree_mode rest hpre fun k hk => hpre_get (100 + k) (by omega) (by omega) (by omega)
  have huid := patch_agree_uid rest hpre fun k hk => hpre_get (108 + k) (by omega) (by omega) (by omega)
  have hgid := patch_agree_gid rest hpre fun k hk => hpre_get (116 + k) (by omega) (by omega) (by omega)
  have hext_size : bytes.extract 124 136 = src := by
    have h136 : (136 : Nat) = 124 + 12 := by omega
    rw [h136]
    exact extract_patch_eq_slice hpre (by omega) hsrc_sz (fun k hk => by omega) hsize_pre
  have hsize : parseUstarNumeric bytes 124 136 0 false u64Limit "size" = .ok 5 := by
    have h136 : (136 : Nat) = 124 + (11 + 1) := by omega
    rw [h136]
    exact parseUstarNumeric_encodeOctalField (by omega) (by decide) (by decide) (by simpa [h136] using hext_size)
  have hmtime := patch_agree_mtime rest hpre fun k hk => hpre_get (136 + k) (by omega) (by omega) (by omega)
  have h156 : bytes[156]'(by rw [hbytes_sz]; omega) = 53 := by
    rw [hp.2.2 156 (by omega) (by omega), h156_pre]
  let fields : UstarHeaderFields :=
    { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 5, mtime := 0, typeflag := 53 }
  have hparse : parseUstarHeader bytes 0 = .ok fields := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hchk.2]
    dsimp only
    rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_right (by rw [hmagic]; decide),
      hmode, huid, hgid, hsize, hmtime]
    have hlt156 : 156 < bytes.size := by rw [hbytes_sz]; omega
    rw [dite_eq_left hlt156, h156]
  have hdec : decodeTarEntry {} bytes 0 fields none [] 0 0 =
      .error { kind := .invalidHeader, message := "non-regular tar entry has non-zero size", offset := some 0 } := by
    rw [decodeTarEntry.eq_1]
    have h1 : ¬((fields.typeflag == 0x30 || fields.typeflag == 0x00) = true) := by decide
    have h2 : (fields.typeflag == 0x35) = true := rfl
    have hdir : (EntryKind.directory != EntryKind.regular && ({} : PaxOverrides).size?.getD 5 != 0) = true := rfl
    dsimp only [fields]
    rw [ite_eq_right h1, ite_eq_left h2]
    dsimp only
    rw [Option.getD_none, ite_eq_left hdir]
  have hassoc : (hdr ++ padBlock512 "12345".toUTF8 ++ twoZeroBlocks) = bytes := by
    simp only [bytes, rest, ByteArray.append_assoc]
  rw [hassoc]
  exact ⟨_, unpackWith_hdr_rest_decode_err hhdr hrest_pos hrest_mod h257 hparse rfl hdec,
    rfl, by decide⟩

/-- Case 11 of Test 5: `badDir` fails with `.invalidHeader`. -/
theorem test5_badDir_err :
    ∃ e, Impl.unpackWith {}
        (patchHeaderChecksum (blitFixed (baseHdr5.set! 156 53) 124 12 (encodeOctalField 5 11)) ++
          padBlock512 "12345".toUTF8 ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ e.message ≠ "" := by
  let b156 := baseHdr5.set! 156 53
  let src := encodeOctalField 5 11
  have hb156_sz : b156.size = 512 := (byteArray_set!_size _ _ _).trans baseHdr5_size
  have hsrc_sz : src.size = 12 := encodeOctalField_size _ 11
  have hpre : (blitFixed b156 124 12 src).size = 512 := (blitFixed_size _ _ _ _).trans hb156_sz
  have hbd_blit : 124 + min 12 src.size ≤ b156.size := by rw [hb156_sz, hsrc_sz]; omega
  refine badDir_abstract (blitFixed b156 124 12 src) hpre ?_ ?_ ?_
  · intro i hi hnot124 hne156
    rw [blitFixed_getElem hbd_blit (by rw [hb156_sz]; exact hi)]
    have hnot' : ¬(124 ≤ i ∧ i < 124 + min 12 src.size) := by rw [hsrc_sz]; exact hnot124
    rw [dite_eq_right hnot']
    change (baseHdr5.set! 156 53)[i]'(by rw [hb156_sz]; exact hi) = _
    rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; exact hi)]
    exact ite_eq_right (by omega)
  · intro k hk
    rw [blitFixed_getElem hbd_blit (by rw [hb156_sz]; omega)]
    rw [dite_eq_left (by rw [hsrc_sz]; omega)]
    simp only [(by omega : 124 + k - 124 = k)]
    rfl
  · rw [blitFixed_getElem hbd_blit (by rw [hb156_sz]; omega)]
    rw [dite_eq_right (by rw [hsrc_sz]; omega)]
    change (baseHdr5.set! 156 53)[156]'(by rw [hb156_sz]; omega) = 53
    rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; omega)]
    simp

private theorem badUtf8Name_abstract (hdrPre : ByteArray) (hpre : hdrPre.size = 512)
    (hagree : ∀ (i : Nat) (hi : i < 512), i ≠ 0 →
      hdrPre[i]'(by rw [hpre]; exact hi) = baseHdr5[i]'(by rw [baseHdr5_size]; exact hi))
    (h0_pre : hdrPre[0]'(by rw [hpre]; omega) = 255) :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum hdrPre ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidEncoding ∧ e.message ≠ "" := by
  let hdr := patchHeaderChecksum hdrPre
  let bytes := hdr ++ twoZeroBlocks
  have hhdr : hdr.size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head hdr twoZeroBlocks hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), hagree 257 (by omega) (by omega), baseHdr5_byte_257]
    decide
  have hmagic := patch_agree_magic twoZeroBlocks hpre fun k hk => hagree (257 + k) (by omega) (by omega)
  have hmode := patch_agree_mode twoZeroBlocks hpre fun k hk => hagree (100 + k) (by omega) (by omega)
  have huid := patch_agree_uid twoZeroBlocks hpre fun k hk => hagree (108 + k) (by omega) (by omega)
  have hgid := patch_agree_gid twoZeroBlocks hpre fun k hk => hagree (116 + k) (by omega) (by omega)
  have hsize := patch_agree_size twoZeroBlocks hpre fun k hk => hagree (124 + k) (by omega) (by omega)
  have hmtime := patch_agree_mtime twoZeroBlocks hpre fun k hk => hagree (136 + k) (by omega) (by omega)
  have h156 : bytes[156]'(by rw [hbytes_sz]; omega) = 48 := by
    rw [hp.2.2 156 (by omega) (by omega), hagree 156 (by omega) (by omega), baseHdr5_byte_156]
  let fields : UstarHeaderFields :=
    { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 48 }
  have hparse : parseUstarHeader bytes 0 = .ok fields := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hchk.2]
    dsimp only
    rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_right (by rw [hmagic]; decide),
      hmode, huid, hgid, hsize, hmtime]
    have hlt156 : 156 < bytes.size := by rw [hbytes_sz]; omega
    rw [dite_eq_left hlt156, h156]
  have hb0 : bytes[0]'(by rw [hbytes_sz]; omega) = 255 := by
    rw [hp.2.2 0 (by omega) (by omega), h0_pre]
  have hbk : ∀ (k : Nat) (_hk1 : 1 ≤ k) (hk5 : k < 5),
      bytes[k]'(by rw [hbytes_sz]; omega) = ("a.txt".toUTF8)[k]'(by rw [atxt_utf8_size]; exact hk5) := by
    intro k hk1 hk5
    have hk0 : bytes[k]'(by rw [hbytes_sz]; omega) = bytes[0 + k]'(by rw [hbytes_sz]; omega) := by
      congr 1; omega
    rw [hk0, hp.2.2 k (by omega) (by omega), hagree k (by omega) (by omega)]
    exact baseHdr5_atxt_byte hk5
  have hb5 : bytes[5]'(by rw [hbytes_sz]; omega) = 0 := by
    rw [hp.2.2 5 (by omega) (by omega), hagree 5 (by omega) (by omega)]
    exact baseHdr5_byte_5
  have hfind5 : extractCStringBytes.findNul bytes 100 0 = 5 := by
    have h1 : bytes[1]'(by rw [hbytes_sz]; omega) = 0x2e := by
      rw [hbk 1 (by omega) (by omega)]; rfl
    have h2 : bytes[2]'(by rw [hbytes_sz]; omega) = 0x74 := by
      rw [hbk 2 (by omega) (by omega)]; rfl
    have h3 : bytes[3]'(by rw [hbytes_sz]; omega) = 0x78 := by
      rw [hbk 3 (by omega) (by omega)]; rfl
    have h4 : bytes[4]'(by rw [hbytes_sz]; omega) = 0x74 := by
      rw [hbk 4 (by omega) (by omega)]; rfl
    have hne0 : ¬((bytes[0]'(by rw [hbytes_sz]; omega) == 0) = true) := by rw [hb0]; decide
    have hne1 : ¬((bytes[1]'(by rw [hbytes_sz]; omega) == 0) = true) := by rw [h1]; decide
    have hne2 : ¬((bytes[2]'(by rw [hbytes_sz]; omega) == 0) = true) := by rw [h2]; decide
    have hne3 : ¬((bytes[3]'(by rw [hbytes_sz]; omega) == 0) = true) := by rw [h3]; decide
    have hne4 : ¬((bytes[4]'(by rw [hbytes_sz]; omega) == 0) = true) := by rw [h4]; decide
    have heq5 : (bytes[5]'(by rw [hbytes_sz]; omega) == 0) = true := by rw [hb5]; rfl
    have hlt0 : 0 < bytes.size := by rw [hbytes_sz]; omega
    have hlt1 : 1 < bytes.size := by rw [hbytes_sz]; omega
    have hlt2 : 2 < bytes.size := by rw [hbytes_sz]; omega
    have hlt3 : 3 < bytes.size := by rw [hbytes_sz]; omega
    have hlt4 : 4 < bytes.size := by rw [hbytes_sz]; omega
    have hlt5 : 5 < bytes.size := by rw [hbytes_sz]; omega
    rw [extractCStringBytes.findNul.eq_1, ite_eq_right (by decide), dite_eq_left hlt0, ite_eq_right hne0]
    rw [extractCStringBytes.findNul.eq_1, ite_eq_right (by decide), dite_eq_left hlt1, ite_eq_right hne1]
    rw [extractCStringBytes.findNul.eq_1, ite_eq_right (by decide), dite_eq_left hlt2, ite_eq_right hne2]
    rw [extractCStringBytes.findNul.eq_1, ite_eq_right (by decide), dite_eq_left hlt3, ite_eq_right hne3]
    rw [extractCStringBytes.findNul.eq_1, ite_eq_right (by decide), dite_eq_left hlt4, ite_eq_right hne4]
    rw [extractCStringBytes.findNul.eq_1, ite_eq_right (by decide), dite_eq_left hlt5, ite_eq_left heq5]
  have hext5 : bytes.extract 0 5 = { data := #[255, 0x2e, 0x74, 0x78, 0x74] } := by
    let target : ByteArray := { data := #[255, 0x2e, 0x74, 0x78, 0x74] }
    have ht_sz : target.size = 5 := by decide
    have hext_off : bytes.extract 0 5 = bytes.extract (0 + 0) (0 + 5) := by simp only [Nat.zero_add]
    rw [hext_off]
    apply extract_eq_of_getElem (offset := 0) (by omega) (by rw [hbytes_sz]; omega) ht_sz
    intro k hk
    have hk5 : k < 5 := by omega
    have hl : bytes[0 + 0 + k]'(by rw [hbytes_sz]; omega) = bytes[k]'(by rw [hbytes_sz]; omega) := by
      congr 1; omega
    rw [hl]
    rcases k with _ | k'
    · rw [hb0]; rfl
    · rcases k' with _ | k''
      · rw [hbk 1 (by omega) (by omega)]; rfl
      · rcases k'' with _ | k'''
        · rw [hbk 2 (by omega) (by omega)]; rfl
        · rcases k''' with _ | k4
          · rw [hbk 3 (by omega) (by omega)]; rfl
          · rcases k4 with _ | _
            · rw [hbk 4 (by omega) (by omega)]; rfl
            · omega
  have hdec_nm : decodeCStringUtf8 bytes 0 100 0 "name" =
      .error { kind := .invalidEncoding, message := "invalid UTF-8 in USTAR name", offset := some 0 } := by
    unfold decodeCStringUtf8 extractCStringBytes
    dsimp only
    rw [hfind5, hext5]
    rfl
  have hdec : decodeTarEntry {} bytes 0 fields none [] 0 0 =
      .error { kind := .invalidEncoding, message := "invalid UTF-8 in USTAR name", offset := some 0 } := by
    rw [decodeTarEntry.eq_1]
    have htf : (fields.typeflag == 0x30 || fields.typeflag == 0x00) = true := rfl
    have hreg_ne : ¬((EntryKind.regular != EntryKind.regular && 0 != 0) = true) := by decide
    have hmaxe : ¬(0 + 1 > ({} : UnpackOptions).maxEntries) := by decide
    have hmaxb : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes) := by decide
    have hpad0 : pad512 0 = 0 := rfl
    have htrunc : ¬(512 + 0 > bytes.size) := by rw [hbytes_sz, twoZeroBlocks_size]; omega
    dsimp only [fields]
    rw [ite_eq_left htf]
    dsimp only
    simp only [Nat.zero_add, Option.getD_none, hpad0]
    rw [ite_eq_right hreg_ne, ite_eq_right hmaxe, ite_eq_right hmaxb, ite_eq_right htrunc, hdec_nm]
  exact ⟨_, unpackWith_hdr_rest_decode_err hhdr twoZeroBlocks_pos twoZeroBlocks_mod h257 hparse rfl hdec,
    rfl, by decide⟩

/-- Case 17 of Test 5: `badUtf8Name` fails with `.invalidEncoding`. -/
theorem test5_badUtf8Name_err :
    ∃ e, Impl.unpackWith {} (patchHeaderChecksum (baseHdr5.set! 0 255) ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidEncoding ∧ e.message ≠ "" := by
  have hpre : (baseHdr5.set! 0 255).size = 512 := (byteArray_set!_size _ _ _).trans baseHdr5_size
  refine badUtf8Name_abstract (baseHdr5.set! 0 255) hpre ?_ ?_
  · intro i hi hne
    rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; exact hi)]
    exact ite_eq_right (by omega)
  · rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; omega)]
    simp

private theorem garbageLink_abstract (hdrPre : ByteArray) (hpre : hdrPre.size = 512)
    (hagree : ∀ (i : Nat) (hi : i < 512), i ≠ 157 →
      hdrPre[i]'(by rw [hpre]; exact hi) = baseHdr5[i]'(by rw [baseHdr5_size]; exact hi)) :
    ∃ res, Impl.unpackWith {} (patchHeaderChecksum hdrPre ++ twoZeroBlocks) =
      .ok res ∧ TarEquiv [{ path := "a.txt", kind := .regular }] res := by
  let hdr := patchHeaderChecksum hdrPre
  let bytes := hdr ++ twoZeroBlocks
  have hhdr : hdr.size = 512 := (patchHeaderChecksum_size _).trans hpre
  have hbytes_sz : bytes.size = 512 + twoZeroBlocks.size := by
    simp only [bytes, ByteArray.size_append, hhdr]
  have hchk := parseUstarHeader_patch_check hpre (by rw [hbytes_sz]; omega)
  have hext0 : bytes.extract 0 (0 + 512) = patchHeaderChecksum hdrPre := by
    rw [Nat.zero_add]; exact extract_hdr_rest_head hdr twoZeroBlocks hhdr
  have hp := parseChecksumOctal_patchHeaderChecksum hpre (by rw [hbytes_sz]; omega) hext0
  have h257 : hdr[257]'(by rw [hhdr]; omega) ≠ 0 := by
    have h1 : bytes[0 + 257]'(by rw [hbytes_sz]; omega) = hdr[257]'(by rw [hhdr]; omega) :=
      getElem_append_left (by rw [hhdr]; omega)
    rw [← h1, hp.2.2 257 (by omega) (by omega), hagree 257 (by omega) (by omega), baseHdr5_byte_257]
    decide
  have hmagic := patch_agree_magic twoZeroBlocks hpre fun k hk => hagree (257 + k) (by omega) (by omega)
  have hmode := patch_agree_mode twoZeroBlocks hpre fun k hk => hagree (100 + k) (by omega) (by omega)
  have huid := patch_agree_uid twoZeroBlocks hpre fun k hk => hagree (108 + k) (by omega) (by omega)
  have hgid := patch_agree_gid twoZeroBlocks hpre fun k hk => hagree (116 + k) (by omega) (by omega)
  have hsize := patch_agree_size twoZeroBlocks hpre fun k hk => hagree (124 + k) (by omega) (by omega)
  have hmtime := patch_agree_mtime twoZeroBlocks hpre fun k hk => hagree (136 + k) (by omega) (by omega)
  have h156 : bytes[156]'(by rw [hbytes_sz]; omega) = 48 := by
    rw [hp.2.2 156 (by omega) (by omega), hagree 156 (by omega) (by omega), baseHdr5_byte_156]
  let fields : UstarHeaderFields :=
    { mode := ((420 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 48 }
  have hparse : parseUstarHeader bytes 0 = .ok fields := by
    unfold parseUstarHeader
    simp only [Nat.zero_add]
    rw [hchk.2]
    dsimp only
    rw [bne_self_eq_false, ite_eq_right (by decide), ite_eq_right (by rw [hmagic]; decide),
      hmode, huid, hgid, hsize, hmtime]
    have hlt156 : 156 < bytes.size := by rw [hbytes_sz]; omega
    rw [dite_eq_left hlt156, h156]
  have hstrs := patch_agree_regular_strings twoZeroBlocks hpre
    (fun k hk => hagree (0 + k) (by omega) (by omega))
    (fun k hk => hagree (265 + k) (by omega) (by omega))
    (fun k hk => hagree (297 + k) (by omega) (by omega))
    (fun k hk => hagree (345 + k) (by omega) (by omega))
  let entry : TarEntry :=
    { path := "a.txt", kind := .regular, mode := 420, uid := 0, gid := 0, mtime := 0,
      uname := "", gname := "", data := ByteArray.empty, linkTarget := "" }
  have hdec := decodeTarEntry_regular_a_txt hbytes_sz 0 hstrs
  refine ⟨[entry], unpackWith_hdr_twoZero_regular_ok hhdr h257 hparse rfl rfl hdec, ?_⟩
  exact tarEquiv_singleton_self entry

/-- Case 18 of Test 5: `garbageLink` succeeds ignoring `linkname` for regular entries. -/
theorem test5_garbageLink_ok :
    ∃ res, Impl.unpackWith {} (patchHeaderChecksum (baseHdr5.set! 157 255) ++ twoZeroBlocks) =
      .ok res ∧ TarEquiv [{ path := "a.txt", kind := .regular }] res := by
  have hpre : (baseHdr5.set! 157 255).size = 512 := (byteArray_set!_size _ _ _).trans baseHdr5_size
  refine garbageLink_abstract (baseHdr5.set! 157 255) hpre ?_
  intro i hi hne
  rw [byteArray_set!_getElem_val (by rw [baseHdr5_size]; omega) (by rw [baseHdr5_size]; exact hi)]
  exact ite_eq_right (by omega)

end LeanSwe.Tar.Proofs
