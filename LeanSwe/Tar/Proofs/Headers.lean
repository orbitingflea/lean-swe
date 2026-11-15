import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem byteArray_size_set! (b : ByteArray) (k : Nat) (v : UInt8) :
    (b.set! k v).size = b.size :=
  Array.size_setIfInBounds

private theorem byteArray_getElem_of_eq {a b : ByteArray} (h : a = b) {i : Nat}
    (ha : i < a.size) (hb : i < b.size) : a[i]'ha = b[i]'hb := by
  subst h; rfl

/-- `(padBlock512 bs).size` is always a multiple of `512`. -/
theorem padBlock512_size_mod (bs : ByteArray) : (padBlock512 bs).size % 512 = 0 := by
  rw [padBlock512_size]
  exact pad512_mod bs.size

/-- Extract a contiguous subslice from `bytes.extract offset (offset + e) = L ++ (M ++ R)`. -/
theorem extract_sub_eq {bytes L M R : ByteArray} {offset e a w : Nat}
    (he : bytes.extract offset (offset + e) = L ++ (M ++ R))
    (ha : L.size = a) (hw : M.size = w) (hb : a + w ≤ e) :
    bytes.extract (offset + a) (offset + a + w) = M := by
  have hsub : bytes.extract (offset + a) (offset + a + w) =
      (bytes.extract offset (offset + e)).extract a (a + w) := by
    rw [ByteArray.extract_extract]
    exact congrArg (bytes.extract (offset + a)) (by omega)
  rw [hsub, he, ← ha, ← hw]
  rw [ByteArray.extract_append]
  have hz1 : L.size - L.size = 0 := Nat.sub_self _
  have hz2 : L.size + M.size - L.size = M.size := Nat.add_sub_cancel_left _ _
  have he1 : L.extract L.size (L.size + M.size) = ByteArray.empty :=
    ByteArray.extract_eq_empty_iff.mpr (by omega)
  rw [hz1, hz2, he1, ByteArray.empty_append]
  exact extract_append_exact_left M R

/-- Upper bound `ustarChecksumAt bytes start ≤ 512 * 255`. -/
theorem ustarChecksumAt_le (bytes : ByteArray) (start : Nat) :
    ustarChecksumAt bytes start ≤ 512 * 255 := by
  unfold ustarChecksumAt
  have hgo : ∀ i acc : Nat, i ≤ 512 →
      ustarChecksumAt.go bytes start i acc ≤ acc + (512 - i) * 255 := by
    intro i acc hi
    induction hdiff : 512 - i generalizing i acc with
    | zero =>
      have heq : i = 512 := by omega
      subst heq
      rw [ustarChecksumAt.go.eq_1]
      simp
    | succ d ih =>
      have hlt : ¬(i ≥ 512) := by omega
      rw [ustarChecksumAt.go.eq_1]
      simp only [hlt, ↓reduceIte]
      let step := if (decide (148 ≤ i) && decide (i < 156)) = true then 0x20 else
        if h : start + i < bytes.size then (bytes[start + i]'h).toNat else 0
      have hstep : step ≤ 255 := by
        dsimp [step]
        split
        · omega
        · split
          · rename_i h
            have hlt256 := UInt8.toNat_lt (bytes[start + i]'h)
            omega
          · omega
      have hrec := ih (i + 1) (acc + step) (by omega) (by omega)
      exact Nat.le_trans hrec (by omega)
  simpa using hgo 0 0 (Nat.zero_le 512)

/-- `ustarChecksumAt bytes start < 8 ^ 6`. -/
theorem ustarChecksumAt_lt (bytes : ByteArray) (start : Nat) :
    ustarChecksumAt bytes start < 8 ^ 6 := by
  have hle := ustarChecksumAt_le bytes start
  omega

/-- Upper bound `ustarChecksum hdr ≤ 512 * 255`. -/
theorem ustarChecksum_le (hdr : ByteArray) : ustarChecksum hdr ≤ 512 * 255 := by
  unfold ustarChecksum
  have hgo : ∀ i acc : Nat, i ≤ 512 →
      ustarChecksum.go hdr i acc ≤ acc + (512 - i) * 255 := by
    intro i acc hi
    induction hdiff : 512 - i generalizing i acc with
    | zero =>
      have heq : i = 512 := by omega
      subst heq
      rw [ustarChecksum.go.eq_1]
      simp
    | succ d ih =>
      have hlt : ¬(i ≥ 512) := by omega
      rw [ustarChecksum.go.eq_1]
      simp only [hlt, ↓reduceIte]
      let step := if (decide (148 ≤ i) && decide (i < 156)) = true then 0x20 else
        if h : i < hdr.size then (hdr[i]'h).toNat else 0
      have hstep : step ≤ 255 := by
        dsimp [step]
        split
        · omega
        · split
          · rename_i h
            have hlt256 := UInt8.toNat_lt (hdr[i]'h)
            omega
          · omega
      have hrec := ih (i + 1) (acc + step) (by omega) (by omega)
      exact Nat.le_trans hrec (by omega)
  simpa using hgo 0 0 (Nat.zero_le 512)

/-- `ustarChecksum hdr < 8 ^ 6`. -/
theorem ustarChecksum_lt (hdr : ByteArray) : ustarChecksum hdr < 8 ^ 6 := by
  have hle := ustarChecksum_le hdr
  omega

/-- `ustarChecksumAt` depends only on bytes `[0..512)` outside `[148..156)`. -/
theorem ustarChecksumAt_congr {b1 b2 : ByteArray} {s1 s2 : Nat}
    (hb1 : s1 + 512 ≤ b1.size) (hb2 : s2 + 512 ≤ b2.size)
    (heq : ∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      b1[s1 + i]'(by omega) = b2[s2 + i]'(by omega)) :
    ustarChecksumAt b1 s1 = ustarChecksumAt b2 s2 := by
  unfold ustarChecksumAt
  have hgo : ∀ i acc : Nat, i ≤ 512 →
      ustarChecksumAt.go b1 s1 i acc = ustarChecksumAt.go b2 s2 i acc := by
    intro i acc hi
    induction hdiff : 512 - i generalizing i acc with
    | zero =>
      have h512 : i = 512 := by omega
      subst h512
      conv => lhs; rw [ustarChecksumAt.go.eq_1]
      conv => rhs; rw [ustarChecksumAt.go.eq_1]
      simp only [Nat.le_refl, ↓reduceIte]
    | succ d ih =>
      have hi512 : i < 512 := by omega
      have hlt : ¬(i ≥ 512) := by omega
      conv => lhs; rw [ustarChecksumAt.go.eq_1]
      conv => rhs; rw [ustarChecksumAt.go.eq_1]
      simp only [hlt, ↓reduceIte]
      by_cases hchk : 148 ≤ i ∧ i < 156
      · have hcond : (decide (148 ≤ i) && decide (i < 156)) = true := by
          simp [hchk.1, hchk.2]
        simp only [hcond, ↓reduceIte]
        exact ih (i + 1) (acc + 0x20) (by omega) (by omega)
      · have hcond : (decide (148 ≤ i) && decide (i < 156)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Decidable.not_and_iff_not_or_not.mp hchk
        have hi1 : s1 + i < b1.size := by omega
        have hi2 : s2 + i < b2.size := by omega
        have hbyte : b1[s1 + i]'hi1 = b2[s2 + i]'hi2 := heq i hi512 hchk
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, hi1, hi2, ↓reduceDIte, hbyte]
        exact ih (i + 1) (acc + (b2[s2 + i]'hi2).toNat) (by omega) (by omega)
  exact hgo 0 0 (Nat.zero_le 512)

/-- `ustarChecksumAt` coincides with `ustarChecksum` when bytes `[0..512)` outside `[148..156)` match. -/
theorem ustarChecksumAt_eq_ustarChecksum {bytes hdr : ByteArray} {offset : Nat}
    (hby : offset + 512 ≤ bytes.size) (hhdr : 512 ≤ hdr.size)
    (heq : ∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      bytes[offset + i]'(by omega) = hdr[i]'(by omega)) :
    ustarChecksumAt bytes offset = ustarChecksum hdr := by
  unfold ustarChecksumAt ustarChecksum
  have hgo : ∀ i acc : Nat, i ≤ 512 →
      ustarChecksumAt.go bytes offset i acc = ustarChecksum.go hdr i acc := by
    intro i acc hi
    induction hdiff : 512 - i generalizing i acc with
    | zero =>
      have h512 : i = 512 := by omega
      subst h512
      conv => lhs; rw [ustarChecksumAt.go.eq_1]
      conv => rhs; rw [ustarChecksum.go.eq_1]
      simp only [Nat.le_refl, ↓reduceIte]
    | succ d ih =>
      have hi512 : i < 512 := by omega
      have hlt : ¬(i ≥ 512) := by omega
      conv => lhs; rw [ustarChecksumAt.go.eq_1]
      conv => rhs; rw [ustarChecksum.go.eq_1]
      simp only [hlt, ↓reduceIte]
      by_cases hchk : 148 ≤ i ∧ i < 156
      · have hcond : (decide (148 ≤ i) && decide (i < 156)) = true := by
          simp [hchk.1, hchk.2]
        simp only [hcond, ↓reduceIte]
        exact ih (i + 1) (acc + 0x20) (by omega) (by omega)
      · have hcond : (decide (148 ≤ i) && decide (i < 156)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Decidable.not_and_iff_not_or_not.mp hchk
        have hi1 : offset + i < bytes.size := by omega
        have hi2 : i < hdr.size := by omega
        have hbyte : bytes[offset + i]'hi1 = hdr[i]'hi2 := heq i hi512 hchk
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, hi1, hi2, ↓reduceDIte, hbyte]
        exact ih (i + 1) (acc + (hdr[i]'hi2).toNat) (by omega) (by omega)
  exact hgo 0 0 (Nat.zero_le 512)

/-- `(buildUstarHeader ...).size = 512`. -/
theorem buildUstarHeader_size (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    (buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx).size = 512 := by
  unfold buildUstarHeader
  dsimp only
  simp only [ByteArray.size_append, padRightBytes_size]
  have h1 : (ByteArray.mk #[typeflag]).size = 1 := rfl
  have h2 : (ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]).size = 6 := rfl
  have h3 : (ByteArray.mk #[0x30, 0x30]).size = 2 := rfl
  have h4 : (ByteArray.mk (Array.replicate 16 (0 : UInt8))).size = 16 := by decide
  have h5 : (ByteArray.mk (Array.replicate 12 (0 : UInt8))).size = 12 := by decide
  rw [h1, h2, h3, h4, h5]

private theorem encodeOctalField_6_sp_size (chk : Nat) :
    (encodeOctalField chk 6 ++ ByteArray.mk #[0x20]).size = 8 := by
  rw [ByteArray.size_append, encodeOctalField_size]
  rfl

private theorem padRightBytes_8_exact {bs : ByteArray} (h : bs.size = 8) :
    padRightBytes 8 bs = bs := by
  unfold padRightBytes
  have hge : bs.size ≥ 8 := by omega
  simp only [hge, ↓reduceIte]
  rw [← h]
  exact ByteArray.extract_zero_size

private theorem padRightBytes_12_exact {bs : ByteArray} (h : bs.size = 12) :
    padRightBytes 12 bs = bs := by
  unfold padRightBytes
  have hge : bs.size ≥ 12 := by omega
  simp only [hge, ↓reduceIte]
  rw [← h]
  exact ByteArray.extract_zero_size

/-- Variant of `parseChecksumOctal_encodeOctalField` accepting an arbitrary error offset. -/
theorem parseChecksumOctal_encodeOctalField_at {bytes : ByteArray} {start chk errOffset : Nat}
    (hchk : chk < 8 ^ 6)
    (hext : bytes.extract start (start + 8) =
      encodeOctalField chk 6 ++ ByteArray.mk #[0x20]) :
    parseChecksumOctal bytes start (start + 8) errOffset = .ok chk := by
  have h0 := parseChecksumOctal_encodeOctalField hchk hext
  unfold parseChecksumOctal at h0 ⊢
  dsimp only at h0 ⊢
  split at h0
  · simp at h0
  · split at h0
    · simp at h0
    · rename_i hne hno
      simp [hne, hno]
      exact Except.ok.inj h0

private theorem buildUstarHeader_parts (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    ∃ (chk : Nat) (hdrPre : ByteArray),
      let fName := padRightBytes 100 name.toUTF8
      let fMode := encodeOctalField (mode &&& 0o7777).toNat 7
      let fUid := encodeOctalField uid 7
      let fGid := encodeOctalField gid 7
      let fSize := encodeOctalField size 11
      let fMtime := encodeOctalField mtime 11
      let fChkSpaces := ByteArray.mk (Array.replicate 8 0x20)
      let fChk := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
      let fType := ByteArray.mk #[typeflag]
      let fLink := padRightBytes 100 linkname.toUTF8
      let fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]
      let fVer := ByteArray.mk #[0x30, 0x30]
      let fUname := padRightBytes 32 uname.toUTF8
      let fGname := padRightBytes 32 gname.toUTF8
      let fDev := ByteArray.mk (Array.replicate 16 0)
      let fPrefix := padRightBytes 155 pfx.toUTF8
      let fPad := ByteArray.mk (Array.replicate 12 0)
      chk < 8 ^ 6 ∧
      hdrPre = fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChkSpaces ++
        fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad ∧
      chk = ustarChecksumAt hdrPre 0 ∧
      buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx =
        fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++
          fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad := by
  unfold buildUstarHeader
  have hM := padRightBytes_8_exact (encodeOctalField_size (mode &&& 0o7777).toNat 7)
  have hU := padRightBytes_8_exact (encodeOctalField_size uid 7)
  have hG := padRightBytes_8_exact (encodeOctalField_size gid 7)
  have hS := padRightBytes_12_exact (encodeOctalField_size size 11)
  have hT := padRightBytes_12_exact (encodeOctalField_size mtime 11)
  dsimp only
  rw [hM, hU, hG, hS, hT]
  let fName := padRightBytes 100 name.toUTF8
  let fMode := encodeOctalField (mode &&& 0o7777).toNat 7
  let fUid := encodeOctalField uid 7
  let fGid := encodeOctalField gid 7
  let fSize := encodeOctalField size 11
  let fMtime := encodeOctalField mtime 11
  let fChkSpaces := ByteArray.mk (Array.replicate 8 0x20)
  let fType := ByteArray.mk #[typeflag]
  let fLink := padRightBytes 100 linkname.toUTF8
  let fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]
  let fVer := ByteArray.mk #[0x30, 0x30]
  let fUname := padRightBytes 32 uname.toUTF8
  let fGname := padRightBytes 32 gname.toUTF8
  let fDev := ByteArray.mk (Array.replicate 16 0)
  let fPrefix := padRightBytes 155 pfx.toUTF8
  let fPad := ByteArray.mk (Array.replicate 12 0)
  let hdrPre := fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChkSpaces ++
    fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad
  refine ⟨ustarChecksumAt hdrPre 0, hdrPre, ustarChecksumAt_lt hdrPre 0, rfl, rfl, ?_⟩
  rw [padRightBytes_8_exact (encodeOctalField_6_sp_size _)]

private theorem append_mid_getElem_eq (a b1 b2 c : ByteArray) {i : Nat}
    (h1 : i < (a ++ (b1 ++ c)).size) (h2 : i < (a ++ (b2 ++ c)).size)
    (hb : b1.size = b2.size) (hnot : ¬(a.size ≤ i ∧ i < a.size + b1.size)) :
    (a ++ (b1 ++ c))[i]'h1 = (a ++ (b2 ++ c))[i]'h2 := by
  rcases Nat.lt_or_ge i a.size with hlt | hge
  · have h1L : (a ++ (b1 ++ c))[i]'h1 = a[i]'hlt := getElem_append_left (a := a) (b := b1 ++ c) hlt
    have h2L : (a ++ (b2 ++ c))[i]'h2 = a[i]'hlt := getElem_append_left (a := a) (b := b2 ++ c) hlt
    rw [h1L, h2L]
  · have h1R : (a ++ (b1 ++ c))[i]'h1 = (b1 ++ c)[i - a.size]'(by rw [ByteArray.size_append] at h1; omega) :=
      getElem_append_right (a := a) (b := b1 ++ c) hge h1
    have h2R : (a ++ (b2 ++ c))[i]'h2 = (b2 ++ c)[i - a.size]'(by rw [ByteArray.size_append] at h2; omega) :=
      getElem_append_right (a := a) (b := b2 ++ c) hge h2
    have hge_b : b1.size ≤ i - a.size := by omega
    have hb1c : i - a.size < (b1 ++ c).size := by rw [ByteArray.size_append] at h1; exact Nat.sub_lt_left_of_lt_add hge h1
    have hb2c : i - a.size < (b2 ++ c).size := by rw [ByteArray.size_append] at h2; exact Nat.sub_lt_left_of_lt_add hge h2
    have h1c : (b1 ++ c)[i - a.size]'hb1c =
        c[i - a.size - b1.size]'(by rw [ByteArray.size_append] at hb1c; omega) :=
      getElem_append_right (a := b1) (b := c) (i := i - a.size) hge_b hb1c
    have h2c : (b2 ++ c)[i - a.size]'hb2c =
        c[i - a.size - b2.size]'(by rw [ByteArray.size_append] at hb2c; omega) :=
      getElem_append_right (a := b2) (b := c) (i := i - a.size) (by omega) hb2c
    rw [h1R, h2R, h1c, h2c]
    simp only [hb]

/-- Decompose `buildUstarHeader` checksum and prove `parseUstarHeader` succeeds on valid USTAR field bounds. -/
theorem parseUstarHeader_buildUstarHeader {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (huid : uid < ustarOctal7Limit) (hgid : gid < ustarOctal7Limit)
    (hsize : size < ustarOctal11Limit) (hmtime : mtime < ustarOctal11Limit)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    parseUstarHeader bytes offset = .ok
      { mode := (mode &&& 0o7777).toNat
      , uid := uid
      , gid := gid
      , size := size
      , mtime := mtime
      , typeflag := typeflag } := by
  rcases buildUstarHeader_parts name mode uid gid size mtime typeflag linkname uname gname pfx with
    ⟨chk, hdrPre, hchk_lt, hpre_def, hchk_pre, hbuild_eq⟩
  let fName := padRightBytes 100 name.toUTF8
  let fMode := encodeOctalField (mode &&& 0o7777).toNat 7
  let fUid := encodeOctalField uid 7
  let fGid := encodeOctalField gid 7
  let fSize := encodeOctalField size 11
  let fMtime := encodeOctalField mtime 11
  let fChkSpaces := ByteArray.mk (Array.replicate 8 0x20)
  let fChk := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  let fType := ByteArray.mk #[typeflag]
  let fLink := padRightBytes 100 linkname.toUTF8
  let fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]
  let fVer := ByteArray.mk #[0x30, 0x30]
  let fUname := padRightBytes 32 uname.toUTF8
  let fGname := padRightBytes 32 gname.toUTF8
  let fDev := ByteArray.mk (Array.replicate 16 0)
  let fPrefix := padRightBytes 155 pfx.toUTF8
  let fPad := ByteArray.mk (Array.replicate 12 0)
  have hName_sz : fName.size = 100 := padRightBytes_size 100 _
  have hMode_sz : fMode.size = 8 := encodeOctalField_size _ 7
  have hUid_sz : fUid.size = 8 := encodeOctalField_size _ 7
  have hGid_sz : fGid.size = 8 := encodeOctalField_size _ 7
  have hSize_sz : fSize.size = 12 := encodeOctalField_size _ 11
  have hMtime_sz : fMtime.size = 12 := encodeOctalField_size _ 11
  have hChkSp_sz : fChkSpaces.size = 8 := by decide
  have hChk_sz : fChk.size = 8 := encodeOctalField_6_sp_size chk
  have hType_sz : fType.size = 1 := rfl
  have hLink_sz : fLink.size = 100 := padRightBytes_size 100 _
  have hMagic_sz : fMagic.size = 6 := rfl
  have hVer_sz : fVer.size = 2 := rfl
  have hUname_sz : fUname.size = 32 := padRightBytes_size 32 _
  have hGname_sz : fGname.size = 32 := padRightBytes_size 32 _
  have hDev_sz : fDev.size = 16 := by decide
  have hPfx_sz : fPrefix.size = 155 := padRightBytes_size 155 _
  have hPad_sz : fPad.size = 12 := by decide
  have hext' : bytes.extract offset (offset + 512) =
      fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++
        fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad :=
    hext.trans hbuild_eq
  let pre148 := fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime
  let suf356 := fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad
  have hpre148_sz : pre148.size = 148 := by
    simp only [pre148, ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz, hSize_sz, hMtime_sz]
  have hsuf356_sz : suf356.size = 356 := by
    simp only [suf356, ByteArray.size_append, hType_sz, hLink_sz, hMagic_sz, hVer_sz,
      hUname_sz, hGname_sz, hDev_sz, hPfx_sz, hPad_sz]
  have hext_split : bytes.extract offset (offset + 512) = pre148 ++ (fChk ++ suf356) := by
    rw [hext']
    simp only [pre148, suf356, ByteArray.append_assoc]
  have hpre_split : hdrPre = pre148 ++ (fChkSpaces ++ suf356) := by
    rw [hpre_def]
    simp only [pre148, suf356, fName, fMode, fUid, fGid, fSize, fMtime, fChkSpaces,
      fType, fLink, fMagic, fVer, fUname, fGname, fDev, fPrefix, fPad, ByteArray.append_assoc]
  have hhdrPre_sz : hdrPre.size = 512 := by
    rw [hpre_split, ByteArray.size_append, hpre148_sz, ByteArray.size_append, hChkSp_sz, hsuf356_sz]
  have hext_sz : (bytes.extract offset (offset + 512)).size = 512 := by
    rw [ByteArray.size_extract]; omega
  have hchk_eq : ustarChecksumAt bytes offset = chk := by
    rw [hchk_pre]
    apply ustarChecksumAt_congr (s2 := 0) hbd (by rw [hhdrPre_sz]; omega)
    intro i hi hnot
    have hi_e : i < (bytes.extract offset (offset + 512)).size := by rw [hext_sz]; exact hi
    have hbs_i : bytes[offset + i]'(by omega) = (bytes.extract offset (offset + 512))[i]'hi_e :=
      (ByteArray.getElem_extract hi_e).symm
    rw [hbs_i]
    have hi_sp : i < (pre148 ++ (fChk ++ suf356)).size := by
      rw [ByteArray.size_append, hpre148_sz, ByteArray.size_append, hChk_sz, hsuf356_sz]; exact hi
    have hi_pr : i < (pre148 ++ (fChkSpaces ++ suf356)).size := by
      rw [← hpre_split, hhdrPre_sz]; exact hi
    simp only [Nat.zero_add]
    rw [byteArray_getElem_of_eq hext_split hi_e hi_sp,
      byteArray_getElem_of_eq hpre_split (by rw [hhdrPre_sz]; exact hi) hi_pr]
    exact append_mid_getElem_eq pre148 fChk fChkSpaces suf356 hi_sp hi_pr
      (by rw [hChk_sz, hChkSp_sz]) (by rw [hpre148_sz, hChk_sz]; exact hnot)
  have hext_chk : bytes.extract (offset + 148) (offset + 148 + 8) = fChk :=
    extract_sub_eq hext_split hpre148_sz hChk_sz (by omega)
  have hparse_chk : parseChecksumOctal bytes (offset + 148) (offset + 156) offset = .ok chk := by
    have h156 : offset + 156 = offset + 148 + 8 := by omega
    rw [h156]
    exact parseChecksumOctal_encodeOctalField_at hchk_lt hext_chk
  have hext_mode : bytes.extract (offset + 100) (offset + 100 + 8) = fMode := by
    have hs : bytes.extract offset (offset + 512) =
        fName ++ (fMode ++ (fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ suf356)) := by
      rw [hext']; simp only [suf356, ByteArray.append_assoc]
    exact extract_sub_eq hs hName_sz hMode_sz (by omega)
  have hext_uid : bytes.extract (offset + 108) (offset + 108 + 8) = fUid := by
    have hs : bytes.extract offset (offset + 512) =
        (fName ++ fMode) ++ (fUid ++ (fGid ++ fSize ++ fMtime ++ fChk ++ suf356)) := by
      rw [hext']; simp only [suf356, ByteArray.append_assoc]
    exact extract_sub_eq hs (by simp only [ByteArray.size_append, hName_sz, hMode_sz]) hUid_sz (by omega)
  have hext_gid : bytes.extract (offset + 116) (offset + 116 + 8) = fGid := by
    have hs : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid) ++ (fGid ++ (fSize ++ fMtime ++ fChk ++ suf356)) := by
      rw [hext']; simp only [suf356, ByteArray.append_assoc]
    exact extract_sub_eq hs
      (by simp only [ByteArray.size_append, hName_sz, hMode_sz, hUid_sz]) hGid_sz (by omega)
  have hext_size : bytes.extract (offset + 124) (offset + 124 + 12) = fSize := by
    have hs : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid ++ fGid) ++ (fSize ++ (fMtime ++ fChk ++ suf356)) := by
      rw [hext']; simp only [suf356, ByteArray.append_assoc]
    exact extract_sub_eq hs
      (by simp only [ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz]) hSize_sz (by omega)
  have hext_mtime : bytes.extract (offset + 136) (offset + 136 + 12) = fMtime := by
    have hs : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid ++ fGid ++ fSize) ++ (fMtime ++ (fChk ++ suf356)) := by
      rw [hext']; simp only [suf356, ByteArray.append_assoc]
    exact extract_sub_eq hs
      (by simp only [ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz, hSize_sz])
      hMtime_sz (by omega)
  have hext_magic : bytes.extract (offset + 257) (offset + 257 + 6) = fMagic := by
    have hs : bytes.extract offset (offset + 512) =
        (pre148 ++ fChk ++ fType ++ fLink) ++
          (fMagic ++ (fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad)) := by
      rw [hext']; simp only [pre148, ByteArray.append_assoc]
    exact extract_sub_eq hs
      (by simp only [ByteArray.size_append, hpre148_sz, hChk_sz, hType_sz, hLink_sz])
      hMagic_sz (by omega)
  have hext_ver : bytes.extract (offset + 263) (offset + 263 + 2) = fVer := by
    have hs : bytes.extract offset (offset + 512) =
        (pre148 ++ fChk ++ fType ++ fLink ++ fMagic) ++
          (fVer ++ (fUname ++ fGname ++ fDev ++ fPrefix ++ fPad)) := by
      rw [hext']; simp only [pre148, ByteArray.append_assoc]
    exact extract_sub_eq hs
      (by simp only [ByteArray.size_append, hpre148_sz, hChk_sz, hType_sz, hLink_sz, hMagic_sz])
      hVer_sz (by omega)
  have hmagic : hasValidMagic bytes offset = true := by
    unfold hasValidMagic
    have h263 : offset + 263 = offset + 257 + 6 := by omega
    have h265 : offset + 265 = offset + 263 + 2 := by omega
    rw [h263, hext_magic, h265, hext_ver]
    simp only [fMagic, fVer, byteArray_toList_eq]
    decide
  have hmode_lt_o7 : (mode &&& 0o7777).toNat < 8 ^ 7 := by
    have : (mode &&& 0o7777).toNat = mode.toNat &&& 0o7777 := rfl
    rw [this]
    have hlt : mode.toNat &&& 0o7777 < 2 ^ 12 := Nat.and_lt_two_pow (n := 12) mode.toNat (by decide)
    omega
  have hmode_lt_u32 : (mode &&& 0o7777).toNat < u32Limit := by
    have : u32Limit = 2 ^ 32 := rfl; omega
  have huid_o7 : uid < 8 ^ 7 := by have : ustarOctal7Limit = 8 ^ 7 := rfl; omega
  have hgid_o7 : gid < 8 ^ 7 := by have : ustarOctal7Limit = 8 ^ 7 := rfl; omega
  have huid_u64 : uid < u64Limit := by have h1 : ustarOctal7Limit = 8 ^ 7 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hgid_u64 : gid < u64Limit := by have h1 : ustarOctal7Limit = 8 ^ 7 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hsize_o11 : size < 8 ^ 11 := by have : ustarOctal11Limit = 8 ^ 11 := rfl; omega
  have hmtime_o11 : mtime < 8 ^ 11 := by have : ustarOctal11Limit = 8 ^ 11 := rfl; omega
  have hsize_u64 : size < u64Limit := by have h1 : ustarOctal11Limit = 8 ^ 11 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hmtime_u64 : mtime < u64Limit := by have h1 : ustarOctal11Limit = 8 ^ 11 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hparse_mode : parseUstarNumeric bytes (offset + 100) (offset + 108) offset false u32Limit "mode" =
      .ok (mode &&& 0o7777).toNat := by
    rw [(by omega : offset + 108 = offset + 100 + (7 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hmode_lt_o7 hmode_lt_u32 hext_mode
  have hparse_uid : parseUstarNumeric bytes (offset + 108) (offset + 116) offset true u64Limit "uid" =
      .ok uid := by
    rw [(by omega : offset + 116 = offset + 108 + (7 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) huid_o7 huid_u64 hext_uid
  have hparse_gid : parseUstarNumeric bytes (offset + 116) (offset + 124) offset true u64Limit "gid" =
      .ok gid := by
    rw [(by omega : offset + 124 = offset + 116 + (7 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hgid_o7 hgid_u64 hext_gid
  have hparse_size : parseUstarNumeric bytes (offset + 124) (offset + 136) offset false u64Limit "size" =
      .ok size := by
    rw [(by omega : offset + 136 = offset + 124 + (11 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hsize_o11 hsize_u64 hext_size
  have hparse_mtime : parseUstarNumeric bytes (offset + 136) (offset + 148) offset true u64Limit "mtime" =
      .ok mtime := by
    rw [(by omega : offset + 148 = offset + 136 + (11 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hmtime_o11 hmtime_u64 hext_mtime
  have htype_byte : bytes[offset + 156]'(by omega) = typeflag := by
    have hi_e : 156 < (bytes.extract offset (offset + 512)).size := by rw [hext_sz]; omega
    have h1 : bytes[offset + 156]'(by omega) = (bytes.extract offset (offset + 512))[156]'hi_e :=
      (ByteArray.getElem_extract hi_e).symm
    have hs : bytes.extract offset (offset + 512) =
        (pre148 ++ fChk) ++ (fType ++ (fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad)) := by
      rw [hext']; simp only [pre148, ByteArray.append_assoc]
    have hpre156_sz : (pre148 ++ fChk).size = 156 := by
      rw [ByteArray.size_append, hpre148_sz, hChk_sz]
    have hi_sp : 156 < ((pre148 ++ fChk) ++ (fType ++ (fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad))).size := by
      rw [← hs]; exact hi_e
    rw [h1, byteArray_getElem_of_eq hs hi_e hi_sp, getElem_append_right (by rw [hpre156_sz]; omega)]
    have hsub0 : 156 - (pre148 ++ fChk).size = 0 := by rw [hpre156_sz]
    simp only [hsub0]
    rw [getElem_append_left (by rw [hType_sz]; omega)]
    rfl
  unfold parseUstarHeader
  have hlt_bd : offset + 156 < bytes.size := by omega
  simp only [hparse_chk, hchk_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    hmagic, Bool.not_true, hparse_mode, hparse_uid, hparse_gid, hparse_size, hparse_mtime,
    hlt_bd, ↓reduceDIte, htype_byte]

/-- String field extractors for `buildUstarHeader` slices inside `bytes`. -/
theorem buildUstarHeader_extract_strings {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hext : bytes.extract offset (offset + 512) =
      buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    bytes.extract offset (offset + 100) = padRightBytes 100 name.toUTF8 ∧
    bytes.extract (offset + 157) (offset + 257) = padRightBytes 100 linkname.toUTF8 ∧
    bytes.extract (offset + 265) (offset + 297) = padRightBytes 32 uname.toUTF8 ∧
    bytes.extract (offset + 297) (offset + 329) = padRightBytes 32 gname.toUTF8 ∧
    bytes.extract (offset + 345) (offset + 500) = padRightBytes 155 pfx.toUTF8 := by
  rcases buildUstarHeader_parts name mode uid gid size mtime typeflag linkname uname gname pfx with
    ⟨chk, _, _, _, _, hbuild_eq⟩
  let fName := padRightBytes 100 name.toUTF8
  let fMode := encodeOctalField (mode &&& 0o7777).toNat 7
  let fUid := encodeOctalField uid 7
  let fGid := encodeOctalField gid 7
  let fSize := encodeOctalField size 11
  let fMtime := encodeOctalField mtime 11
  let fChk := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  let fType := ByteArray.mk #[typeflag]
  let fLink := padRightBytes 100 linkname.toUTF8
  let fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]
  let fVer := ByteArray.mk #[0x30, 0x30]
  let fUname := padRightBytes 32 uname.toUTF8
  let fGname := padRightBytes 32 gname.toUTF8
  let fDev := ByteArray.mk (Array.replicate 16 0)
  let fPrefix := padRightBytes 155 pfx.toUTF8
  let fPad := ByteArray.mk (Array.replicate 12 0)
  have hName_sz : fName.size = 100 := padRightBytes_size 100 _
  have hMode_sz : fMode.size = 8 := encodeOctalField_size _ 7
  have hUid_sz : fUid.size = 8 := encodeOctalField_size _ 7
  have hGid_sz : fGid.size = 8 := encodeOctalField_size _ 7
  have hSize_sz : fSize.size = 12 := encodeOctalField_size _ 11
  have hMtime_sz : fMtime.size = 12 := encodeOctalField_size _ 11
  have hChk_sz : fChk.size = 8 := encodeOctalField_6_sp_size chk
  have hType_sz : fType.size = 1 := rfl
  have hLink_sz : fLink.size = 100 := padRightBytes_size 100 _
  have hMagic_sz : fMagic.size = 6 := rfl
  have hVer_sz : fVer.size = 2 := rfl
  have hUname_sz : fUname.size = 32 := padRightBytes_size 32 _
  have hGname_sz : fGname.size = 32 := padRightBytes_size 32 _
  have hDev_sz : fDev.size = 16 := by decide
  have hPfx_sz : fPrefix.size = 155 := padRightBytes_size 155 _
  have hdef : bytes.extract offset (offset + 512) =
      fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++
        fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad :=
    hext.trans hbuild_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h0 : bytes.extract offset (offset + 512) =
        ByteArray.empty ++ (fName ++ (fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++
          fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad)) := by
      rw [hdef, ByteArray.empty_append]; simp only [ByteArray.append_assoc]
    have h0_sz : ByteArray.empty.size = 0 := rfl
    have he := extract_sub_eq h0 h0_sz hName_sz (by omega)
    simpa only [Nat.add_zero] using he
  · have h157 : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType) ++
          (fLink ++ (fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad)) := by
      rw [hdef]; simp only [ByteArray.append_assoc]
    have hsz : (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType).size = 157 := by
      simp only [ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz, hSize_sz,
        hMtime_sz, hChk_sz, hType_sz]
    have he := extract_sub_eq h157 hsz hLink_sz (by omega)
    rw [Nat.add_assoc] at he
    exact he
  · have h265 : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink ++ fMagic ++ fVer) ++
          (fUname ++ (fGname ++ fDev ++ fPrefix ++ fPad)) := by
      rw [hdef]; simp only [ByteArray.append_assoc]
    have hsz : (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink ++ fMagic ++ fVer).size = 265 := by
      simp only [ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz, hSize_sz,
        hMtime_sz, hChk_sz, hType_sz, hLink_sz, hMagic_sz, hVer_sz]
    have he := extract_sub_eq h265 hsz hUname_sz (by omega)
    rw [Nat.add_assoc] at he
    exact he
  · have h297 : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink ++ fMagic ++ fVer ++ fUname) ++
          (fGname ++ (fDev ++ fPrefix ++ fPad)) := by
      rw [hdef]; simp only [ByteArray.append_assoc]
    have hsz : (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink ++ fMagic ++ fVer ++ fUname).size = 297 := by
      simp only [ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz, hSize_sz,
        hMtime_sz, hChk_sz, hType_sz, hLink_sz, hMagic_sz, hVer_sz, hUname_sz]
    have he := extract_sub_eq h297 hsz hGname_sz (by omega)
    rw [Nat.add_assoc] at he
    exact he
  · have h345 : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev) ++
          (fPrefix ++ fPad) := by
      rw [hdef]; simp only [ByteArray.append_assoc]
    have hsz : (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev).size = 345 := by
      simp only [ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz, hSize_sz,
        hMtime_sz, hChk_sz, hType_sz, hLink_sz, hMagic_sz, hVer_sz, hUname_sz, hGname_sz, hDev_sz]
    have h345' : bytes.extract offset (offset + 512) =
        (fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev) ++
          (fPrefix ++ (fPad ++ ByteArray.empty)) := by
      rw [h345, ByteArray.append_empty]
    have he := extract_sub_eq h345' hsz hPfx_sz (by omega)
    rw [Nat.add_assoc] at he
    exact he

/-- `isZeroRange bytes offset len = true` iff `[offset .. offset + len)` is within bounds and all zero (for `len > 0`). -/
theorem isZeroRange_eq_true_iff (bytes : ByteArray) (offset len : Nat) (hlen : 0 < len) :
    isZeroRange bytes offset len = true ↔
      offset + len ≤ bytes.size ∧
      ∀ i : Nat, i < len → ∀ hi : offset + i < bytes.size, bytes[offset + i]'hi = 0 := by
  unfold isZeroRange
  have hgo : ∀ k : Nat, k ≤ len → (k = 0 ∨ offset + k ≤ bytes.size) →
      (isZeroRange.go bytes offset len k = true ↔
        offset + len ≤ bytes.size ∧
        ∀ i : Nat, k ≤ i → i < len → ∀ hi : offset + i < bytes.size, bytes[offset + i]'hi = 0) := by
    intro k hk hpre
    induction hdiff : len - k generalizing k with
    | zero =>
      have hke : k = len := by omega
      subst hke
      rw [isZeroRange.go.eq_1]
      simp only [Nat.le_refl, ↓reduceIte, true_iff]
      refine ⟨by rcases hpre with h0 | hbd; omega; exact hbd, fun i h1 h2 => by omega⟩
    | succ d ih =>
      have hnot : ¬(k ≥ len) := by omega
      rw [isZeroRange.go.eq_1]
      simp only [hnot, ↓reduceIte]
      by_cases hbd : offset + k < bytes.size
      · simp only [hbd, ↓reduceDIte]
        by_cases hz : bytes[offset + k]'hbd = 0
        · have hbeq : (bytes[offset + k]'hbd == 0) = true := beq_iff_eq.mpr hz
          simp only [hbeq, ↓reduceIte]
          rw [ih (k + 1) (by omega) (Or.inr (by omega)) (by omega)]
          constructor
          · rintro ⟨hsz, hall⟩
            refine ⟨hsz, ?_⟩
            intro i hki hilen hi
            by_cases hik : i = k
            · subst hik; exact hz
            · exact hall i (by omega) hilen hi
          · rintro ⟨hsz, hall⟩
            exact ⟨hsz, fun i hki hilen hi => hall i (by omega) hilen hi⟩
        · have hbeq : (bytes[offset + k]'hbd == 0) = false := beq_false_of_ne hz
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Bool.false_eq_true, false_iff]
          rintro ⟨_, hall⟩
          exact hz (hall k (Nat.le_refl k) (by omega) hbd)
      · simp only [hbd, ↓reduceDIte, Bool.false_eq_true, false_iff]
        rintro ⟨hsz, _⟩
        omega
  constructor
  · intro h
    have ⟨hsz, hall⟩ := (hgo 0 (Nat.zero_le len) (Or.inl rfl)).mp h
    exact ⟨hsz, fun i hi => hall i (Nat.zero_le i) hi⟩
  · rintro ⟨hsz, hall⟩
    exact (hgo 0 (Nat.zero_le len) (Or.inl rfl)).mpr ⟨hsz, fun i _ hi => hall i hi⟩

/-- `isZeroRange` returns `false` if any byte in `[offset .. offset + len)` is non-zero. -/
theorem isZeroRange_false_of_ne {bytes : ByteArray} {offset len i : Nat}
    (hlt : i < len) (hbd : offset + i < bytes.size) (hne : bytes[offset + i]'hbd ≠ 0) :
    isZeroRange bytes offset len = false := by
  exact Bool.eq_false_iff.mpr (fun h =>
    hne (((isZeroRange_eq_true_iff bytes offset len (by omega)).mp h).2 i hlt hbd))

/-- A `buildUstarHeader` block at `offset` is never all-zero (magic byte `257` is `0x75`). -/
theorem isZeroRange_buildUstarHeader_false {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    isZeroRange bytes offset 512 = false := by
  rcases buildUstarHeader_parts name mode uid gid size mtime typeflag linkname uname gname pfx with
    ⟨chk, _, _, _, _, hbuild_eq⟩
  have hext_sz : (bytes.extract offset (offset + 512)).size = 512 := by
    rw [ByteArray.size_extract]; omega
  have hi257 : 257 < (bytes.extract offset (offset + 512)).size := by rw [hext_sz]; omega
  have hbuild_sz : (buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx).size = 512 :=
    buildUstarHeader_size ..
  have hb257 : bytes[offset + 257]'(by omega) =
      (buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx)[257]'(by
        rw [hbuild_sz]; omega) := by
    have h1 := ByteArray.getElem_extract hi257
    have h2 := byteArray_getElem_of_eq hext hi257 (by rw [hbuild_sz]; omega)
    exact h1.symm.trans h2
  let fName := padRightBytes 100 name.toUTF8
  let fMode := encodeOctalField (mode &&& 0o7777).toNat 7
  let fUid := encodeOctalField uid 7
  let fGid := encodeOctalField gid 7
  let fSize := encodeOctalField size 11
  let fMtime := encodeOctalField mtime 11
  let fChk := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  let fType := ByteArray.mk #[typeflag]
  let fLink := padRightBytes 100 linkname.toUTF8
  let fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]
  let fVer := ByteArray.mk #[0x30, 0x30]
  let fUname := padRightBytes 32 uname.toUTF8
  let fGname := padRightBytes 32 gname.toUTF8
  let fDev := ByteArray.mk (Array.replicate 16 0)
  let fPrefix := padRightBytes 155 pfx.toUTF8
  let fPad := ByteArray.mk (Array.replicate 12 0)
  let p257 := fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++ fType ++ fLink
  let r255 := fMagic ++ (fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad)
  have hName_sz : fName.size = 100 := padRightBytes_size 100 _
  have hMode_sz : fMode.size = 8 := encodeOctalField_size _ 7
  have hUid_sz : fUid.size = 8 := encodeOctalField_size _ 7
  have hGid_sz : fGid.size = 8 := encodeOctalField_size _ 7
  have hSize_sz : fSize.size = 12 := encodeOctalField_size _ 11
  have hMtime_sz : fMtime.size = 12 := encodeOctalField_size _ 11
  have hChk_sz : fChk.size = 8 := encodeOctalField_6_sp_size chk
  have hType_sz : fType.size = 1 := rfl
  have hLink_sz : fLink.size = 100 := padRightBytes_size 100 _
  have hp_sz : p257.size = 257 := by
    simp only [p257, ByteArray.size_append, hName_sz, hMode_sz, hUid_sz, hGid_sz,
      hSize_sz, hMtime_sz, hChk_sz, hType_sz, hLink_sz]
  have hsplit : buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx = p257 ++ r255 := by
    rw [hbuild_eq]
    simp only [p257, r255, fName, fMode, fUid, fGid, fSize, fMtime, fChk, fType, fLink,
      fMagic, fVer, fUname, fGname, fDev, fPrefix, fPad, ByteArray.append_assoc]
  have hr_sz : r255.size = 255 := by
    have h1 : (p257 ++ r255).size = 512 := by rw [← hsplit, hbuild_sz]
    rw [ByteArray.size_append, hp_sz] at h1
    omega
  have hval : (buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx)[257]'(by
      rw [hbuild_sz]; omega) = 0x75 := by
    have hi_pr : 257 < (p257 ++ r255).size := by rw [ByteArray.size_append, hp_sz, hr_sz]; omega
    rw [byteArray_getElem_of_eq hsplit _ hi_pr, getElem_append_right (by rw [hp_sz]; exact Nat.le_refl _)]
    have hsub0 : 257 - p257.size = 0 := by rw [hp_sz]
    simp only [hsub0]
    have hMagic_sz : fMagic.size = 6 := rfl
    have hr_bd : 0 < (fMagic ++ (fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad)).size := by
      change 0 < r255.size; rw [hr_sz]; omega
    rw [getElem_append_left (by rw [hMagic_sz]; omega) hr_bd]
    rfl
  exact isZeroRange_false_of_ne (i := 257) (by omega) (by omega) (by rw [hb257, hval]; decide)

/-- `allZeroTrailer` returns `true` across any all-zero multiple-of-512 tail starting at `offset`. -/
theorem allZeroTrailer_of_zeros {bytes : ByteArray} {offset : Nat}
    (hmod : (bytes.size - offset) % 512 = 0)
    (hz : ∀ i : Nat, offset ≤ i → i < bytes.size → ∀ hi : i < bytes.size, bytes[i]'hi = 0) :
    allZeroTrailer bytes offset = true := by
  induction hq : (bytes.size - offset) / 512 generalizing offset with
  | zero =>
    have hge : offset ≥ bytes.size := by omega
    rw [allZeroTrailer.eq_1]
    simp [hge]
  | succ k ih =>
    have h512 : offset + 512 ≤ bytes.size := by omega
    have hnotge : ¬(offset ≥ bytes.size) := by omega
    rw [allZeroTrailer.eq_1]
    have hzr : isZeroRange bytes offset 512 = true := by
      refine (isZeroRange_eq_true_iff bytes offset 512 (by omega)).mpr ⟨h512, ?_⟩
      intro i hi hi'
      exact hz (offset + i) (by omega) (by omega) hi'
    have hmod' : (bytes.size - (offset + 512)) % 512 = 0 := by omega
    have hq' : (bytes.size - (offset + 512)) / 512 = k := by omega
    simp only [hnotge, ↓reduceIte, hzr, Bool.true_and]
    exact ih hmod' (fun i h1 h2 hi => hz i (by omega) h2 hi) hq'

/-- Appending two `zeroBlock`s to `pre` makes `allZeroTrailer (pre ++ (zeroBlock ++ zeroBlock)) pre.size = true`. -/
theorem allZeroTrailer_twoZeroBlocks (pre : ByteArray) :
    allZeroTrailer (pre ++ (zeroBlock ++ zeroBlock)) pre.size = true := by
  have hz2 : (zeroBlock ++ zeroBlock).size = 1024 := by
    rw [ByteArray.size_append, zeroBlock_size]
  have hsz : (pre ++ (zeroBlock ++ zeroBlock)).size = pre.size + 1024 := by
    rw [ByteArray.size_append, hz2]
  apply allZeroTrailer_of_zeros
  · rw [hsz]; omega
  · intro i h1 h2 hi
    rw [getElem_append_right h1]
    have hlt1024 : i - pre.size < 1024 := by rw [hsz] at h2; omega
    rcases Nat.lt_or_ge (i - pre.size) 512 with h512 | hge
    · have hl : i - pre.size < zeroBlock.size := by rw [zeroBlock_size]; exact h512
      have hab : i - pre.size < (zeroBlock ++ zeroBlock).size := by rw [hz2]; omega
      rw [getElem_append_left hl hab]
      exact zeroBlock_getElem _
    · have hr : zeroBlock.size ≤ i - pre.size := by rw [zeroBlock_size]; exact hge
      rw [getElem_append_right hr]
      exact zeroBlock_getElem _

private theorem blitFixed_go_size (off width : Nat) (src : ByteArray) (k : Nat) (buf : ByteArray) :
    (blitFixed.go off width src k buf).size = buf.size := by
  fun_induction blitFixed.go off width src k buf with
  | case1 => rfl
  | case2 =>
    rename_i ih
    exact ih.trans (byteArray_size_set! _ _ _)
  | case3 => rfl
  | case4 => rfl

private theorem blitFixed_go_getElem {dst src : ByteArray} {off width k : Nat} {buf : ByteArray}
    (hbuf : buf.size = dst.size) (hbd : off + min width src.size ≤ dst.size)
    {i : Nat} (hi : i < dst.size) :
    (blitFixed.go off width src k buf)[i]'(by rw [blitFixed_go_size, hbuf]; exact hi) =
      if h : k ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size then
        src[i - off]'(by omega)
      else
        buf[i]'(by rw [hbuf]; exact hi) := by
  induction hdiff : width - k generalizing k buf with
  | zero =>
    have hk : k ≥ width := by omega
    have heq : blitFixed.go off width src k buf = buf := by
      rw [blitFixed.go.eq_1]; simp [hk]
    rw [byteArray_getElem_of_eq heq _ (by rw [hbuf]; exact hi)]
    by_cases h : k ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size
    · omega
    · simp only [h, ↓reduceDIte]
  | succ d ih =>
    have hlt : ¬(k ≥ width) := by omega
    have heq0 : blitFixed.go off width src k buf =
        if h : k < src.size then
          if h2 : off + k < buf.size then
            blitFixed.go off width src (k + 1) (buf.set! (off + k) (src[k]'h))
          else buf
        else buf := by
      conv => lhs; rw [blitFixed.go.eq_1]
      simp [hlt]
    by_cases hsrc : k < src.size
    · have hidx : off + k < buf.size := by rw [hbuf]; omega
      have heq1 : blitFixed.go off width src k buf =
          blitFixed.go off width src (k + 1) (buf.set! (off + k) (src[k]'hsrc)) := by
        rw [heq0]; simp [hsrc, hidx]
      have hb' : (buf.set! (off + k) (src[k]'hsrc)).size = dst.size := by
        rw [byteArray_size_set!, hbuf]
      rw [byteArray_getElem_of_eq heq1 _ (by rw [blitFixed_go_size, hb']; exact hi)]
      rw [ih (by rw [hb']) (by omega)]
      have hset : (buf.set! (off + k) (src[k]'hsrc))[i]'(by rw [hb']; exact hi) =
          if off + k = i then src[k]'hsrc else buf[i]'(by rw [hbuf]; exact hi) := by
        have hi_b : i < buf.data.size := by rw [← ByteArray.size, hbuf]; exact hi
        change (buf.data.setIfInBounds (off + k) (src[k]'hsrc))[i]'(by
          rw [Array.size_setIfInBounds]; exact hi_b) = _
        by_cases heq : off + k = i
        · subst heq
          simp only [↓reduceIte]
          exact Array.getElem_setIfInBounds_self (by rw [Array.size_setIfInBounds, ← ByteArray.size]; exact hidx)
        · simp only [heq, ↓reduceIte]
          exact Array.getElem_setIfInBounds_ne hi_b (by omega)
      by_cases hcond : k ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size
      · rw [dite_eq_left hcond]
        by_cases hik : i = off + k
        · have hk1 : ¬(k + 1 ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size) := by omega
          rw [dite_eq_right hk1, hset, ite_eq_left hik.symm]
          simp only [(by omega : i - off = k)]
        · have hk1 : k + 1 ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size := by omega
          rw [dite_eq_left hk1]
      · rw [dite_eq_right hcond]
        have hk1 : ¬(k + 1 ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size) := by omega
        rw [dite_eq_right hk1, hset, ite_eq_right (by omega)]
    · have heq1 : blitFixed.go off width src k buf = buf := by
        rw [heq0]; simp [hsrc]
      rw [byteArray_getElem_of_eq heq1 _ (by rw [hbuf]; exact hi)]
      have hnot : ¬(k ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size) := by omega
      simp only [hnot, ↓reduceDIte]

/-- Byte-level specification of `blitFixed dst off width src` when `off + min width src.size ≤ dst.size`. -/
theorem blitFixed_getElem {dst src : ByteArray} {off width i : Nat}
    (hbd : off + min width src.size ≤ dst.size) (hi : i < dst.size) :
    (blitFixed dst off width src)[i]'(by rw [blitFixed_size]; exact hi) =
      if h : off ≤ i ∧ i < off + min width src.size then
        src[i - off]'(by omega)
      else
        dst[i]'hi := by
  unfold blitFixed
  rw [blitFixed_go_getElem rfl hbd hi]
  by_cases h : off ≤ i ∧ i < off + min width src.size
  · have h0 : 0 ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size := ⟨Nat.zero_le _, h.1, h.2⟩
    rw [dite_eq_left h0, dite_eq_left h]
  · have h0 : ¬(0 ≤ i - off ∧ off ≤ i ∧ i < off + min width src.size) := by omega
    rw [dite_eq_right h0, dite_eq_right h]

private theorem byteArray_set!_getElem {b : ByteArray} {k i : Nat} {v : UInt8}
    (hk : k < b.size) (hi : i < b.size) :
    (b.set! k v)[i]'(by rw [byteArray_size_set!]; exact hi) =
      if k = i then v else b[i]'hi := by
  have hi' : i < b.data.size := hi
  change (b.data.setIfInBounds k v)[i]'(by rw [Array.size_setIfInBounds]; exact hi') = _
  by_cases h : k = i
  · subst h
    simp only [↓reduceIte]
    exact Array.getElem_setIfInBounds_self (by rw [Array.size_setIfInBounds]; exact hk)
  · simp only [h, ↓reduceIte]
    exact Array.getElem_setIfInBounds_ne hi' (by omega)

/-- Size of `mkUstarHeader ...` is `512`. -/
theorem mkUstarHeader_size (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    (mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx).size = 512 := by
  unfold mkUstarHeader
  simp only [blitFixed_size, byteArray_size_set!, zeroBlock_size]

/-- Size of `patchHeaderChecksum hdr` is `hdr.size`. -/
theorem patchHeaderChecksum_size (hdr : ByteArray) :
    (patchHeaderChecksum hdr).size = hdr.size :=
  blitFixed_size hdr 148 8 _

/-- `parseChecksumOctal` and `ustarChecksumAt` match on `patchHeaderChecksum hdr` when `hdr.size = 512`. -/
theorem parseChecksumOctal_patchHeaderChecksum {bytes hdr : ByteArray} {offset : Nat}
    (hhdr : hdr.size = 512) (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = patchHeaderChecksum hdr) :
    ustarChecksumAt bytes offset = ustarChecksum hdr ∧
    parseChecksumOctal bytes (offset + 148) (offset + 156) offset = .ok (ustarChecksumAt bytes offset) ∧
    (∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      bytes[offset + i]'(by omega) = hdr[i]'(by omega)) := by
  let chk := ustarChecksum hdr
  let chkField := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  have hcf_sz : chkField.size = 8 := encodeOctalField_6_sp_size chk
  have hbd_blit : 148 + min 8 chkField.size ≤ hdr.size := by rw [hhdr, hcf_sz]; omega
  have hext_sz : (bytes.extract offset (offset + 512)).size = 512 := by
    rw [ByteArray.size_extract]; omega
  have hpatch_sz : (patchHeaderChecksum hdr).size = 512 := by
    rw [patchHeaderChecksum_size, hhdr]
  have hout : ∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      bytes[offset + i]'(by omega) = hdr[i]'(by omega) := by
    intro i hi hnot
    have hi_e : i < (bytes.extract offset (offset + 512)).size := by rw [hext_sz]; exact hi
    have hb_e : bytes[offset + i]'(by omega) = (bytes.extract offset (offset + 512))[i]'hi_e :=
      (ByteArray.getElem_extract hi_e).symm
    have hp_e : (bytes.extract offset (offset + 512))[i]'hi_e =
        (patchHeaderChecksum hdr)[i]'(by rw [hpatch_sz]; exact hi) :=
      byteArray_getElem_of_eq hext hi_e (by rw [hpatch_sz]; exact hi)
    rw [hb_e, hp_e]
    change (blitFixed hdr 148 8 chkField)[i]'(by rw [blitFixed_size, hhdr]; exact hi) = hdr[i]'(by omega)
    rw [blitFixed_getElem hbd_blit (by omega)]
    have hnot' : ¬(148 ≤ i ∧ i < 148 + min 8 chkField.size) := by rw [hcf_sz]; omega
    simp only [hnot', ↓reduceDIte]
  have hchk_eq : ustarChecksumAt bytes offset = ustarChecksum hdr :=
    ustarChecksumAt_eq_ustarChecksum hbd (by omega) hout
  have hext_chk : bytes.extract (offset + 148) (offset + 156) = chkField := by
    apply ByteArray.ext; apply Array.ext
    · show (bytes.extract (offset + 148) (offset + 156)).size = chkField.size
      rw [ByteArray.size_extract, hcf_sz]; omega
    · intro i hi1 hi2
      have hi1' : i < (bytes.extract (offset + 148) (offset + 156)).size := hi1
      have hi2' : i < 8 := by rw [← hcf_sz]; exact hi2
      rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
        ← ByteArray.getElem_eq_getElem_data (h := hi2),
        ByteArray.getElem_extract (by rw [ByteArray.size_extract]; omega)]
      have hi_e : 148 + i < (bytes.extract offset (offset + 512)).size := by
        rw [hext_sz]; omega
      have h1 : bytes[offset + (148 + i)]'(by omega) = (bytes.extract offset (offset + 512))[148 + i]'hi_e :=
        (ByteArray.getElem_extract hi_e).symm
      have h2 : (bytes.extract offset (offset + 512))[148 + i]'hi_e =
          (patchHeaderChecksum hdr)[148 + i]'(by rw [hpatch_sz]; omega) :=
        byteArray_getElem_of_eq hext hi_e (by rw [hpatch_sz]; omega)
      have h3 : (patchHeaderChecksum hdr)[148 + i]'(by rw [hpatch_sz]; omega) =
          chkField[i]'hi2 := by
        change (blitFixed hdr 148 8 chkField)[148 + i]'(by rw [blitFixed_size, hhdr]; omega) = _
        rw [blitFixed_getElem hbd_blit (by omega)]
        have hc : 148 ≤ 148 + i ∧ 148 + i < 148 + min 8 chkField.size := by rw [hcf_sz]; omega
        rw [dite_eq_left hc]
        simp only [(by omega : 148 + i - 148 = i)]
      have hsub_idx : bytes[offset + 148 + i]'(by omega) = bytes[offset + (148 + i)]'(by omega) := by
        congr 1; omega
      exact hsub_idx.trans (h1.trans (h2.trans h3))
  refine ⟨hchk_eq, ?_, hout⟩
  have h156 : offset + 156 = offset + 148 + 8 := by omega
  rw [hchk_eq, h156]
  exact parseChecksumOctal_encodeOctalField_at (ustarChecksum_lt hdr) hext_chk

/-- `parseUstarHeader` succeeds on `mkUstarHeader` when field bounds hold. -/
theorem parseUstarHeader_mkUstarHeader {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (huid : uid < ustarOctal7Limit) (hgid : gid < ustarOctal7Limit)
    (hsize : size < ustarOctal11Limit) (hmtime : mtime < ustarOctal11Limit)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    parseUstarHeader bytes offset = .ok
      { mode := (mode &&& 0o7777).toNat
      , uid := uid
      , gid := gid
      , size := size
      , mtime := mtime
      , typeflag := typeflag } := by
  let b0 := zeroBlock
  let b1 := blitFixed b0 0 100 name.toUTF8
  let b2 := blitFixed b1 100 8 (encodeOctalField (mode &&& 0o7777).toNat 7)
  let b3 := blitFixed b2 108 8 (encodeOctalField uid 7)
  let b4 := blitFixed b3 116 8 (encodeOctalField gid 7)
  let b5 := blitFixed b4 124 12 (encodeOctalField size 11)
  let b6 := blitFixed b5 136 12 (encodeOctalField mtime 11)
  let b7 := b6.set! 156 typeflag
  let b8 := blitFixed b7 157 100 linkname.toUTF8
  let b9 := blitFixed b8 257 6 "ustar\x00".toUTF8
  let b10 := blitFixed b9 263 2 "00".toUTF8
  let b11 := blitFixed b10 265 32 uname.toUTF8
  let b12 := blitFixed b11 297 32 gname.toUTF8
  let b13 := blitFixed b12 345 155 pfx.toUTF8
  have hb0 : b0.size = 512 := zeroBlock_size
  have hb1 : b1.size = 512 := (blitFixed_size ..).trans hb0
  have hb2 : b2.size = 512 := (blitFixed_size ..).trans hb1
  have hb3 : b3.size = 512 := (blitFixed_size ..).trans hb2
  have hb4 : b4.size = 512 := (blitFixed_size ..).trans hb3
  have hb5 : b5.size = 512 := (blitFixed_size ..).trans hb4
  have hb6 : b6.size = 512 := (blitFixed_size ..).trans hb5
  have hb7 : b7.size = 512 := (byteArray_size_set! ..).trans hb6
  have hb8 : b8.size = 512 := (blitFixed_size ..).trans hb7
  have hb9 : b9.size = 512 := (blitFixed_size ..).trans hb8
  have hb10 : b10.size = 512 := (blitFixed_size ..).trans hb9
  have hb11 : b11.size = 512 := (blitFixed_size ..).trans hb10
  have hb12 : b12.size = 512 := (blitFixed_size ..).trans hb11
  have hb13 : b13.size = 512 := (blitFixed_size ..).trans hb12
  have hext_patch : bytes.extract offset (offset + 512) = patchHeaderChecksum b13 := hext
  have ⟨hchk_eq, hparse_chk, hout⟩ := parseChecksumOctal_patchHeaderChecksum hb13 hbd hext_patch
  have hb13_get : ∀ (i : Nat) (hi : i < 512),
      b13[i]'(by rw [hb13]; exact hi) =
        if h : 345 ≤ i ∧ i < 345 + min 155 pfx.toUTF8.size then pfx.toUTF8[i - 345]'(by omega)
        else if h : 297 ≤ i ∧ i < 297 + min 32 gname.toUTF8.size then gname.toUTF8[i - 297]'(by omega)
        else if h : 265 ≤ i ∧ i < 265 + min 32 uname.toUTF8.size then uname.toUTF8[i - 265]'(by omega)
        else if h : 263 ≤ i ∧ i < 263 + min 2 "00".toUTF8.size then "00".toUTF8[i - 263]'(by omega)
        else if h : 257 ≤ i ∧ i < 257 + min 6 "ustar\x00".toUTF8.size then "ustar\x00".toUTF8[i - 257]'(by omega)
        else if h : 157 ≤ i ∧ i < 157 + min 100 linkname.toUTF8.size then linkname.toUTF8[i - 157]'(by omega)
        else if 156 = i then typeflag
        else if h : 136 ≤ i ∧ i < 136 + min 12 (encodeOctalField mtime 11).size then (encodeOctalField mtime 11)[i - 136]'(by omega)
        else if h : 124 ≤ i ∧ i < 124 + min 12 (encodeOctalField size 11).size then (encodeOctalField size 11)[i - 124]'(by omega)
        else if h : 116 ≤ i ∧ i < 116 + min 8 (encodeOctalField gid 7).size then (encodeOctalField gid 7)[i - 116]'(by omega)
        else if h : 108 ≤ i ∧ i < 108 + min 8 (encodeOctalField uid 7).size then (encodeOctalField uid 7)[i - 108]'(by omega)
        else if h : 100 ≤ i ∧ i < 100 + min 8 (encodeOctalField (mode &&& 0o7777).toNat 7).size then (encodeOctalField (mode &&& 0o7777).toNat 7)[i - 100]'(by omega)
        else if h : 0 ≤ i ∧ i < 0 + min 100 name.toUTF8.size then name.toUTF8[i - 0]'(by omega)
        else 0 := by
    intro i hi
    rw [blitFixed_getElem (by rw [hb12]; omega) (by rw [hb12]; exact hi)]
    by_cases c13 : 345 ≤ i ∧ i < 345 + min 155 pfx.toUTF8.size
    · rw [dite_eq_left c13, dite_eq_left c13]
    rw [dite_eq_right c13, dite_eq_right c13]
    rw [blitFixed_getElem (by rw [hb11]; omega) (by rw [hb11]; exact hi)]
    by_cases c12 : 297 ≤ i ∧ i < 297 + min 32 gname.toUTF8.size
    · rw [dite_eq_left c12, dite_eq_left c12]
    rw [dite_eq_right c12, dite_eq_right c12]
    rw [blitFixed_getElem (by rw [hb10]; omega) (by rw [hb10]; exact hi)]
    by_cases c11 : 265 ≤ i ∧ i < 265 + min 32 uname.toUTF8.size
    · rw [dite_eq_left c11, dite_eq_left c11]
    rw [dite_eq_right c11, dite_eq_right c11]
    rw [blitFixed_getElem (by rw [hb9]; omega) (by rw [hb9]; exact hi)]
    by_cases c10 : 263 ≤ i ∧ i < 263 + min 2 "00".toUTF8.size
    · rw [dite_eq_left c10, dite_eq_left c10]
    rw [dite_eq_right c10, dite_eq_right c10]
    rw [blitFixed_getElem (by rw [hb8]; omega) (by rw [hb8]; exact hi)]
    by_cases c9 : 257 ≤ i ∧ i < 257 + min 6 "ustar\x00".toUTF8.size
    · rw [dite_eq_left c9, dite_eq_left c9]
    rw [dite_eq_right c9, dite_eq_right c9]
    rw [blitFixed_getElem (by rw [hb7]; omega) (by rw [hb7]; exact hi)]
    by_cases c8 : 157 ≤ i ∧ i < 157 + min 100 linkname.toUTF8.size
    · rw [dite_eq_left c8, dite_eq_left c8]
    rw [dite_eq_right c8, dite_eq_right c8]
    change (b6.set! 156 typeflag)[i]'(by rw [byteArray_size_set!, hb6]; exact hi) = _
    rw [byteArray_set!_getElem (by rw [hb6]; omega) (by rw [hb6]; exact hi)]
    by_cases c7 : 156 = i
    · rw [ite_eq_left c7, ite_eq_left c7]
    rw [ite_eq_right c7, ite_eq_right c7]
    rw [blitFixed_getElem (by rw [hb5]; omega) (by rw [hb5]; exact hi)]
    by_cases c6 : 136 ≤ i ∧ i < 136 + min 12 (encodeOctalField mtime 11).size
    · rw [dite_eq_left c6, dite_eq_left c6]
    rw [dite_eq_right c6, dite_eq_right c6]
    rw [blitFixed_getElem (by rw [hb4]; omega) (by rw [hb4]; exact hi)]
    by_cases c5 : 124 ≤ i ∧ i < 124 + min 12 (encodeOctalField size 11).size
    · rw [dite_eq_left c5, dite_eq_left c5]
    rw [dite_eq_right c5, dite_eq_right c5]
    rw [blitFixed_getElem (by rw [hb3]; omega) (by rw [hb3]; exact hi)]
    by_cases c4 : 116 ≤ i ∧ i < 116 + min 8 (encodeOctalField gid 7).size
    · rw [dite_eq_left c4, dite_eq_left c4]
    rw [dite_eq_right c4, dite_eq_right c4]
    rw [blitFixed_getElem (by rw [hb2]; omega) (by rw [hb2]; exact hi)]
    by_cases c3 : 108 ≤ i ∧ i < 108 + min 8 (encodeOctalField uid 7).size
    · rw [dite_eq_left c3, dite_eq_left c3]
    rw [dite_eq_right c3, dite_eq_right c3]
    rw [blitFixed_getElem (by rw [hb1]; omega) (by rw [hb1]; exact hi)]
    by_cases c2 : 100 ≤ i ∧ i < 100 + min 8 (encodeOctalField (mode &&& 0o7777).toNat 7).size
    · rw [dite_eq_left c2, dite_eq_left c2]
    rw [dite_eq_right c2, dite_eq_right c2]
    rw [blitFixed_getElem (by rw [hb0]; omega) (by rw [hb0]; exact hi)]
    by_cases c1 : 0 ≤ i ∧ i < 0 + min 100 name.toUTF8.size
    · rw [dite_eq_left c1, dite_eq_left c1]
    rw [dite_eq_right c1, dite_eq_right c1]
    exact zeroBlock_getElem _
  have hslice : ∀ {a w : Nat} {target : ByteArray} (hw : target.size = w) (hb : a + w ≤ 512)
      (hchk_out : ∀ k, k < w → ¬(148 ≤ a + k ∧ a + k < 156))
      (hbyte : ∀ (k : Nat) (hk : k < w),
        b13[a + k]'(by rw [hb13]; omega) = target[k]'(by rw [hw]; exact hk)),
      bytes.extract (offset + a) (offset + a + w) = target := by
    intro a w target hw hb hchk_out hbyte
    apply ByteArray.ext; apply Array.ext
    · show (bytes.extract (offset + a) (offset + a + w)).size = target.size
      rw [ByteArray.size_extract, hw]; omega
    · intro k hk1 hk2
      have hk1' : k < (bytes.extract (offset + a) (offset + a + w)).size := hk1
      have hk2' : k < w := by rw [← hw]; exact hk2
      rw [← ByteArray.getElem_eq_getElem_data (h := hk1'),
        ← ByteArray.getElem_eq_getElem_data (h := hk2),
        ByteArray.getElem_extract (by rw [ByteArray.size_extract]; omega)]
      have hidx : bytes[offset + a + k]'(by omega) = bytes[offset + (a + k)]'(by omega) := by
        congr 1; omega
      rw [hidx, hout (a + k) (by omega) (hchk_out k hk2')]
      exact hbyte k hk2'
  have hext_mode : bytes.extract (offset + 100) (offset + 108) = encodeOctalField (mode &&& 0o7777).toNat 7 := by
    have h108 : offset + 108 = offset + 100 + 8 := by omega
    rw [h108]
    apply hslice (encodeOctalField_size _ 7) (by omega) (fun k hk => by omega)
    intro k hk
    rw [hb13_get (100 + k) (by omega)]
    have hsz : (encodeOctalField (mode &&& 0o7777).toNat 7).size = 8 := encodeOctalField_size _ 7
    have h12 : 100 ≤ 100 + k ∧ 100 + k < 100 + min 8 (encodeOctalField (mode &&& 0o7777).toNat 7).size := by
      rw [hsz]; omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h12]
    simp only [(by omega : 100 + k - 100 = k)]
  have hext_uid : bytes.extract (offset + 108) (offset + 116) = encodeOctalField uid 7 := by
    have h116 : offset + 116 = offset + 108 + 8 := by omega
    rw [h116]
    apply hslice (encodeOctalField_size _ 7) (by omega) (fun k hk => by omega)
    intro k hk
    rw [hb13_get (108 + k) (by omega)]
    have hsz : (encodeOctalField uid 7).size = 8 := encodeOctalField_size _ 7
    have h11 : 108 ≤ 108 + k ∧ 108 + k < 108 + min 8 (encodeOctalField uid 7).size := by rw [hsz]; omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h11]
    simp only [(by omega : 108 + k - 108 = k)]
  have hext_gid : bytes.extract (offset + 116) (offset + 124) = encodeOctalField gid 7 := by
    have h124 : offset + 124 = offset + 116 + 8 := by omega
    rw [h124]
    apply hslice (encodeOctalField_size _ 7) (by omega) (fun k hk => by omega)
    intro k hk
    rw [hb13_get (116 + k) (by omega)]
    have hsz : (encodeOctalField gid 7).size = 8 := encodeOctalField_size _ 7
    have h10 : 116 ≤ 116 + k ∧ 116 + k < 116 + min 8 (encodeOctalField gid 7).size := by rw [hsz]; omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_left h10]
    simp only [(by omega : 116 + k - 116 = k)]
  have hext_size : bytes.extract (offset + 124) (offset + 136) = encodeOctalField size 11 := by
    have h136 : offset + 136 = offset + 124 + 12 := by omega
    rw [h136]
    apply hslice (encodeOctalField_size _ 11) (by omega) (fun k hk => by omega)
    intro k hk
    rw [hb13_get (124 + k) (by omega)]
    have hsz : (encodeOctalField size 11).size = 12 := encodeOctalField_size _ 11
    have h9 : 124 ≤ 124 + k ∧ 124 + k < 124 + min 12 (encodeOctalField size 11).size := by rw [hsz]; omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_left h9]
    simp only [(by omega : 124 + k - 124 = k)]
  have hext_mtime : bytes.extract (offset + 136) (offset + 148) = encodeOctalField mtime 11 := by
    have h148 : offset + 148 = offset + 136 + 12 := by omega
    rw [h148]
    apply hslice (encodeOctalField_size _ 11) (by omega) (fun k hk => by omega)
    intro k hk
    rw [hb13_get (136 + k) (by omega)]
    have hsz : (encodeOctalField mtime 11).size = 12 := encodeOctalField_size _ 11
    have h8 : 136 ≤ 136 + k ∧ 136 + k < 136 + min 12 (encodeOctalField mtime 11).size := by rw [hsz]; omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left h8]
    simp only [(by omega : 136 + k - 136 = k)]
  have hext_magic : bytes.extract (offset + 257) (offset + 263) = "ustar\x00".toUTF8 := by
    have h263 : offset + 263 = offset + 257 + 6 := by omega
    rw [h263]
    apply hslice (by decide : "ustar\x00".toUTF8.size = 6) (by omega) (fun k hk => by omega)
    intro k hk
    rw [hb13_get (257 + k) (by omega)]
    have hsz : "ustar\x00".toUTF8.size = 6 := by decide
    have h5 : 257 ≤ 257 + k ∧ 257 + k < 257 + min 6 "ustar\x00".toUTF8.size := by rw [hsz]; omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h5]
    simp only [(by omega : 257 + k - 257 = k)]
  have hext_ver : bytes.extract (offset + 263) (offset + 265) = "00".toUTF8 := by
    have h265 : offset + 265 = offset + 263 + 2 := by omega
    rw [h265]
    apply hslice (by decide : "00".toUTF8.size = 2) (by omega) (fun k hk => by omega)
    intro k hk
    rw [hb13_get (263 + k) (by omega)]
    have hsz : "00".toUTF8.size = 2 := by decide
    have h4 : 263 ≤ 263 + k ∧ 263 + k < 263 + min 2 "00".toUTF8.size := by rw [hsz]; omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h4]
    simp only [(by omega : 263 + k - 263 = k)]
  have hmagic : hasValidMagic bytes offset = true := by
    unfold hasValidMagic
    rw [hext_magic, hext_ver, toUTF8_toList, toUTF8_toList]
    decide
  have hmode_lt_o7 : (mode &&& 0o7777).toNat < 8 ^ 7 := by
    have : (mode &&& 0o7777).toNat = mode.toNat &&& 0o7777 := rfl
    rw [this]
    have hlt : mode.toNat &&& 0o7777 < 2 ^ 12 := Nat.and_lt_two_pow (n := 12) mode.toNat (by decide)
    omega
  have hmode_lt_u32 : (mode &&& 0o7777).toNat < u32Limit := by
    have : u32Limit = 2 ^ 32 := rfl; omega
  have huid_o7 : uid < 8 ^ 7 := by have : ustarOctal7Limit = 8 ^ 7 := rfl; omega
  have hgid_o7 : gid < 8 ^ 7 := by have : ustarOctal7Limit = 8 ^ 7 := rfl; omega
  have huid_u64 : uid < u64Limit := by have h1 : ustarOctal7Limit = 8 ^ 7 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hgid_u64 : gid < u64Limit := by have h1 : ustarOctal7Limit = 8 ^ 7 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hsize_o11 : size < 8 ^ 11 := by have : ustarOctal11Limit = 8 ^ 11 := rfl; omega
  have hmtime_o11 : mtime < 8 ^ 11 := by have : ustarOctal11Limit = 8 ^ 11 := rfl; omega
  have hsize_u64 : size < u64Limit := by have h1 : ustarOctal11Limit = 8 ^ 11 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hmtime_u64 : mtime < u64Limit := by have h1 : ustarOctal11Limit = 8 ^ 11 := rfl; have h2 : u64Limit = 2 ^ 64 := rfl; omega
  have hparse_mode : parseUstarNumeric bytes (offset + 100) (offset + 108) offset false u32Limit "mode" =
      .ok (mode &&& 0o7777).toNat := by
    rw [(by omega : offset + 108 = offset + 100 + (7 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hmode_lt_o7 hmode_lt_u32 hext_mode
  have hparse_uid : parseUstarNumeric bytes (offset + 108) (offset + 116) offset true u64Limit "uid" =
      .ok uid := by
    rw [(by omega : offset + 116 = offset + 108 + (7 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) huid_o7 huid_u64 hext_uid
  have hparse_gid : parseUstarNumeric bytes (offset + 116) (offset + 124) offset true u64Limit "gid" =
      .ok gid := by
    rw [(by omega : offset + 124 = offset + 116 + (7 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hgid_o7 hgid_u64 hext_gid
  have hparse_size : parseUstarNumeric bytes (offset + 124) (offset + 136) offset false u64Limit "size" =
      .ok size := by
    rw [(by omega : offset + 136 = offset + 124 + (11 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hsize_o11 hsize_u64 hext_size
  have hparse_mtime : parseUstarNumeric bytes (offset + 136) (offset + 148) offset true u64Limit "mtime" =
      .ok mtime := by
    rw [(by omega : offset + 148 = offset + 136 + (11 + 1))]
    exact parseUstarNumeric_encodeOctalField (by omega) hmtime_o11 hmtime_u64 hext_mtime
  have htype_byte : bytes[offset + 156]'(by omega) = typeflag := by
    rw [hout 156 (by omega) (by omega), hb13_get 156 (by omega)]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left rfl]
  unfold parseUstarHeader
  have hlt_bd : offset + 156 < bytes.size := by omega
  simp only [hparse_chk, hchk_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    hmagic, Bool.not_true, hparse_mode, hparse_uid, hparse_gid, hparse_size, hparse_mtime,
    hlt_bd, ↓reduceDIte, htype_byte]

end LeanSwe.Tar.Proofs
