import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- `(padBlock512 bs).size` is always a multiple of `512`. -/
theorem padBlock512_size_mod (bs : ByteArray) : (padBlock512 bs).size % 512 = 0 := by
  rw [padBlock512_size]
  exact pad512_mod bs.size

/-- Extract a contiguous subslice from `bytes.extract offset (offset + e) = L ++ (M ++ R)`. -/
theorem extract_sub_eq {bytes L M R : ByteArray} {offset e a w : Nat}
    (he : bytes.extract offset (offset + e) = L ++ (M ++ R))
    (ha : L.size = a) (hw : M.size = w) (hb : a + w ≤ e) :
    bytes.extract (offset + a) (offset + a + w) = M :=
  byteArray_extract_sub he ha hw hb

/-- Upper bound `ustarChecksumAt bytes start ≤ 512 * 255`. -/
theorem ustarChecksumAt_le (bytes : ByteArray) (start : Nat) :
    ustarChecksumAt bytes start ≤ 512 * 255 := by
  unfold ustarChecksumAt
  have hgo : ∀ rem idx acc : Nat,
      ustarChecksumAt.go bytes start rem idx acc ≤ acc + rem * 255 := by
    intro rem
    induction rem with
    | zero =>
      intro idx acc
      rw [ustarChecksumAt.go.eq_1]
      simp
    | succ d ih =>
      intro idx acc
      rw [ustarChecksumAt.go.eq_2]
      let b : Nat :=
        if (decide (148 ≤ idx) && decide (idx < 156)) = true then 0x20 else
          if h : start + idx < bytes.size then (bytes[start + idx]'h).toNat else 0
      have hb : b ≤ 255 := by
        dsimp [b]
        split
        · omega
        · split
          · rename_i h
            have hlt256 := UInt8.toNat_lt (bytes[start + idx]'h)
            omega
          · omega
      have hrec : ustarChecksumAt.go bytes start d (idx + 1) (acc + b) ≤ acc + b + d * 255 := ih (idx + 1) (acc + b)
      exact Nat.le_trans hrec (by omega)
  simpa using hgo 512 0 0

/-- `ustarChecksumAt bytes start < 8 ^ 6`. -/
theorem ustarChecksumAt_lt (bytes : ByteArray) (start : Nat) :
    ustarChecksumAt bytes start < 8 ^ 6 := by
  have hle := ustarChecksumAt_le bytes start
  omega

/-- `ustarChecksum hdr = ustarChecksumAt hdr 0`. -/
theorem ustarChecksum_eq_ustarChecksumAt (hdr : ByteArray) :
    ustarChecksum hdr = ustarChecksumAt hdr 0 := by
  unfold ustarChecksum ustarChecksumAt
  have hgo : ∀ rem idx acc : Nat, rem + idx = 512 →
      ustarChecksum.go hdr idx acc = ustarChecksumAt.go hdr 0 rem idx acc := by
    intro rem
    induction rem with
    | zero =>
      intro idx acc hsum
      have h512 : idx = 512 := by omega
      subst h512
      rw [ustarChecksum.go.eq_1, ustarChecksumAt.go.eq_1]
      simp only [Nat.le_refl, ↓reduceIte]
    | succ d ih =>
      intro idx acc hsum
      have hlt : ¬(idx ≥ 512) := by omega
      rw [ustarChecksum.go.eq_1, ustarChecksumAt.go.eq_2]
      simp only [hlt, ↓reduceIte, Nat.zero_add]
      by_cases hchk : 148 ≤ idx ∧ idx < 156
      · have hcond : (decide (148 ≤ idx) && decide (idx < 156)) = true := by simp [hchk.1, hchk.2]
        simp only [hcond, ↓reduceIte]
        exact ih (idx + 1) (acc + 0x20) (by omega)
      · have hcond : (decide (148 ≤ idx) && decide (idx < 156)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Decidable.not_and_iff_not_or_not.mp hchk
        simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        by_cases hi_bd : idx < hdr.size
        · simp only [hi_bd, ↓reduceDIte]
          exact ih (idx + 1) (acc + (hdr[idx]'hi_bd).toNat) (by omega)
        · simp only [hi_bd, ↓reduceDIte]
          exact ih (idx + 1) (acc + 0) (by omega)
  exact hgo 512 0 0 rfl

/-- Upper bound `ustarChecksum hdr ≤ 512 * 255`. -/
theorem ustarChecksum_le (hdr : ByteArray) : ustarChecksum hdr ≤ 512 * 255 := by
  rw [ustarChecksum_eq_ustarChecksumAt]
  exact ustarChecksumAt_le hdr 0

/-- `ustarChecksum hdr < 8 ^ 6`. -/
theorem ustarChecksum_lt (hdr : ByteArray) : ustarChecksum hdr < 8 ^ 6 := by
  rw [ustarChecksum_eq_ustarChecksumAt]
  exact ustarChecksumAt_lt hdr 0

/-- `ustarChecksumAt` depends only on bytes `[0..512)` outside `[148..156)`. -/
theorem ustarChecksumAt_congr {b1 b2 : ByteArray} {s1 s2 : Nat}
    (hb1 : s1 + 512 ≤ b1.size) (hb2 : s2 + 512 ≤ b2.size)
    (heq : ∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      b1[s1 + i]'(by omega) = b2[s2 + i]'(by omega)) :
    ustarChecksumAt b1 s1 = ustarChecksumAt b2 s2 := by
  unfold ustarChecksumAt
  have hgo : ∀ rem idx acc : Nat, rem + idx = 512 →
      ustarChecksumAt.go b1 s1 rem idx acc = ustarChecksumAt.go b2 s2 rem idx acc := by
    intro rem
    induction rem with
    | zero =>
      intro idx acc _
      rw [ustarChecksumAt.go.eq_1, ustarChecksumAt.go.eq_1]
    | succ d ih =>
      intro idx acc hsum
      have hi512 : idx < 512 := by omega
      rw [ustarChecksumAt.go.eq_2, ustarChecksumAt.go.eq_2]
      by_cases hchk : 148 ≤ idx ∧ idx < 156
      · have hcond : (decide (148 ≤ idx) && decide (idx < 156)) = true := by simp [hchk.1, hchk.2]
        simp only [hcond, ↓reduceIte]
        exact ih (idx + 1) (acc + 0x20) (by omega)
      · have hcond : (decide (148 ≤ idx) && decide (idx < 156)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact Decidable.not_and_iff_not_or_not.mp hchk
        have hi1 : s1 + idx < b1.size := by omega
        have hi2 : s2 + idx < b2.size := by omega
        have hbyte : b1[s1 + idx]'hi1 = b2[s2 + idx]'hi2 := heq idx hi512 hchk
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, hi1, hi2, ↓reduceDIte, hbyte]
        exact ih (idx + 1) (acc + (b2[s2 + idx]'hi2).toNat) (by omega)
  exact hgo 512 0 0 rfl

/-- `ustarChecksumAt` coincides with `ustarChecksum` when bytes `[0..512)` outside `[148..156)` match. -/
theorem ustarChecksumAt_eq_ustarChecksum {bytes hdr : ByteArray} {offset : Nat}
    (hby : offset + 512 ≤ bytes.size) (hhdr : 512 ≤ hdr.size)
    (heq : ∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      bytes[offset + i]'(by omega) = hdr[i]'(by omega)) :
    ustarChecksumAt bytes offset = ustarChecksum hdr := by
  rw [ustarChecksum_eq_ustarChecksumAt]
  exact ustarChecksumAt_congr hby (by omega) (fun i hi hnot => by
    simp only [Nat.zero_add]
    exact heq i hi hnot)

/-- `isZeroRange bytes offset len = true` iff `[offset .. offset + len)` is within bounds and all zero (for `len > 0`). -/
theorem isZeroRange_eq_true_iff (bytes : ByteArray) (offset len : Nat) (hlen : 0 < len) :
    isZeroRange bytes offset len = true ↔
      offset + len ≤ bytes.size ∧
      ∀ i : Nat, i < len → ∀ hi : offset + i < bytes.size, bytes[offset + i]'hi = 0 := by
  unfold isZeroRange
  have hgo : ∀ rem k : Nat, rem + k = len → (k = 0 ∨ offset + k ≤ bytes.size) →
      (isZeroRange.go bytes offset rem k = true ↔
        offset + len ≤ bytes.size ∧
        ∀ i : Nat, k ≤ i → i < len → ∀ hi : offset + i < bytes.size, bytes[offset + i]'hi = 0) := by
    intro rem
    induction rem with
    | zero =>
      intro k hsum hpre
      have hke : k = len := by omega
      subst hke
      rw [isZeroRange.go.eq_1]
      simp only [true_iff]
      refine ⟨by rcases hpre with h0 | hbd; omega; exact hbd, fun i h1 h2 => by omega⟩
    | succ d ih =>
      intro k hsum _
      rw [isZeroRange.go.eq_2]
      by_cases hbd : offset + k < bytes.size
      · simp only [hbd, ↓reduceDIte]
        by_cases hz : bytes[offset + k]'hbd = 0
        · have hbeq : (bytes[offset + k]'hbd == 0) = true := beq_iff_eq.mpr hz
          simp only [hbeq, ↓reduceIte]
          rw [ih (k + 1) (by omega) (Or.inr (by omega))]
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
    have ⟨hsz, hall⟩ := (hgo len 0 rfl (Or.inl rfl)).mp h
    exact ⟨hsz, fun i hi => hall i (Nat.zero_le i) hi⟩
  · rintro ⟨hsz, hall⟩
    exact (hgo len 0 rfl (Or.inl rfl)).mpr ⟨hsz, fun i _ hi => hall i hi⟩

/-- `isZeroRange` returns `false` if any byte in `[offset .. offset + len)` is non-zero. -/
theorem isZeroRange_false_of_ne {bytes : ByteArray} {offset len i : Nat}
    (hlt : i < len) (hbd : offset + i < bytes.size) (hne : bytes[offset + i]'hbd ≠ 0) :
    isZeroRange bytes offset len = false :=
  Bool.eq_false_iff.mpr (fun h =>
    hne (((isZeroRange_eq_true_iff bytes offset len (by omega)).mp h).2 i hlt hbd))

/-- `allZeroTrailer` returns `true` across any all-zero multiple-of-512 tail starting at `offset`. -/
theorem allZeroTrailer_of_zeros {bytes : ByteArray} {offset : Nat}
    (hmod : (bytes.size - offset) % 512 = 0)
    (hz : ∀ i : Nat, offset ≤ i → i < bytes.size → ∀ hi : i < bytes.size, bytes[i]'hi = 0) :
    allZeroTrailer bytes offset = true := by
  unfold allZeroTrailer
  have hgo : ∀ rem off : Nat, rem = (bytes.size - off + 511) / 512 →
      (bytes.size - off) % 512 = 0 →
      (∀ i : Nat, off ≤ i → i < bytes.size → ∀ hi : i < bytes.size, bytes[i]'hi = 0) →
      allZeroTrailer.go bytes rem off = true := by
    intro rem
    induction rem with
    | zero =>
      intro off hrem hmod' _
      have hge : off ≥ bytes.size := by omega
      rw [allZeroTrailer.go.eq_1]
    | succ k ih =>
      intro off hrem hmod' hz'
      rw [allZeroTrailer.go.eq_2]
      have h512 : off + 512 ≤ bytes.size := by omega
      have hnotge : ¬(off ≥ bytes.size) := by omega
      have hzr : isZeroRange bytes off 512 = true := by
        refine (isZeroRange_eq_true_iff bytes off 512 (by omega)).mpr ⟨h512, ?_⟩
        intro i hi hi'
        exact hz' (off + i) (by omega) (by omega) hi'
      simp only [hnotge, ↓reduceIte, hzr, Bool.true_and]
      exact ih (off + 512) (by omega) (by omega) (fun i h1 h2 hi => hz' i (by omega) h2 hi)
  exact hgo ((bytes.size - offset + 511) / 512) offset rfl hmod hz

/-- Appending two `zeroBlock`s to `pre` makes `allZeroTrailer (pre ++ (zeroBlock ++ zeroBlock)) pre.size = true`. -/
theorem allZeroTrailer_twoZeroBlocks (pre : ByteArray) :
    allZeroTrailer (pre ++ (zeroBlock ++ zeroBlock)) pre.size = true := by
  have hz2 : (zeroBlock ++ zeroBlock).size = 1024 := twoZeroBlocks_size
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

/-- Symbolic 16-field representation of a 512-byte USTAR header block. -/
structure RawUstarHeader where
  /-- Name field `[0..100)`. -/
  fName : ByteArray
  /-- Mode field `[100..108)`. -/
  fMode : ByteArray
  /-- UID field `[108..116)`. -/
  fUid : ByteArray
  /-- GID field `[116..124)`. -/
  fGid : ByteArray
  /-- Size field `[124..136)`. -/
  fSize : ByteArray
  /-- Mtime field `[136..148)`. -/
  fMtime : ByteArray
  /-- Checksum field `[148..156)`. -/
  fChk : ByteArray
  /-- Typeflag byte `[156]`. -/
  fType : UInt8
  /-- Linkname field `[157..257)`. -/
  fLink : ByteArray
  /-- Magic field `[257..263)`. -/
  fMagic : ByteArray
  /-- Version field `[263..265)`. -/
  fVer : ByteArray
  /-- User name field `[265..297)`. -/
  fUname : ByteArray
  /-- Group name field `[297..329)`. -/
  fGname : ByteArray
  /-- Device major/minor padding `[329..345)`. -/
  fDev : ByteArray
  /-- Path prefix field `[345..500)`. -/
  fPrefix : ByteArray
  /-- Trailing 12-byte padding `[500..512)`. -/
  fPad : ByteArray

/-- Size invariants ensuring `RawUstarHeader.toBytes` is an exact 512-byte USTAR layout. -/
structure RawUstarHeader.WellSized (h : RawUstarHeader) : Prop where
  /-- `fName` has size 100. -/
  szName : h.fName.size = 100
  /-- `fMode` has size 8. -/
  szMode : h.fMode.size = 8
  /-- `fUid` has size 8. -/
  szUid : h.fUid.size = 8
  /-- `fGid` has size 8. -/
  szGid : h.fGid.size = 8
  /-- `fSize` has size 12. -/
  szSize : h.fSize.size = 12
  /-- `fMtime` has size 12. -/
  szMtime : h.fMtime.size = 12
  /-- `fChk` has size 8. -/
  szChk : h.fChk.size = 8
  /-- `fLink` has size 100. -/
  szLink : h.fLink.size = 100
  /-- `fMagic` has size 6. -/
  szMagic : h.fMagic.size = 6
  /-- `fVer` has size 2. -/
  szVer : h.fVer.size = 2
  /-- `fUname` has size 32. -/
  szUname : h.fUname.size = 32
  /-- `fGname` has size 32. -/
  szGname : h.fGname.size = 32
  /-- `fDev` has size 16. -/
  szDev : h.fDev.size = 16
  /-- `fPrefix` has size 155. -/
  szPrefix : h.fPrefix.size = 155
  /-- `fPad` has size 12. -/
  szPad : h.fPad.size = 12

/-- Serialize a `RawUstarHeader` to a flat `ByteArray`. -/
def RawUstarHeader.toBytes (h : RawUstarHeader) : ByteArray :=
  h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
    ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
    h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad

/-- Replace the checksum field of a `RawUstarHeader`. -/
def RawUstarHeader.withChk (h : RawUstarHeader) (chk : ByteArray) : RawUstarHeader :=
  { h with fChk := chk }

/-- `RawUstarHeader.withChk` preserves `WellSized` when `chk.size = 8`. -/
theorem RawUstarHeader.withChk_wellSized {h : RawUstarHeader} (hw : h.WellSized)
    {chk : ByteArray} (hchk : chk.size = 8) : (h.withChk chk).WellSized where
  szName := hw.szName
  szMode := hw.szMode
  szUid := hw.szUid
  szGid := hw.szGid
  szSize := hw.szSize
  szMtime := hw.szMtime
  szChk := hchk
  szLink := hw.szLink
  szMagic := hw.szMagic
  szVer := hw.szVer
  szUname := hw.szUname
  szGname := hw.szGname
  szDev := hw.szDev
  szPrefix := hw.szPrefix
  szPad := hw.szPad

/-- Size of `(h.toBytes)` is `512` when `h.WellSized`. -/
theorem RawUstarHeader.toBytes_size {h : RawUstarHeader} (hw : h.WellSized) :
    h.toBytes.size = 512 := by
  unfold RawUstarHeader.toBytes
  have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
  simp only [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize,
    hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic, hw.szVer, hw.szUname, hw.szGname,
    hw.szDev, hw.szPrefix, hw.szPad]

/-- Construct a `RawUstarHeader` from symbolic USTAR field values and a checksum field. -/
def RawUstarHeader.ofFields (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) (chkField : ByteArray) :
    RawUstarHeader where
  fName := padRightBytes 100 name.toUTF8
  fMode := encodeOctalField (mode &&& 0o7777).toNat 7
  fUid := encodeOctalField uid 7
  fGid := encodeOctalField gid 7
  fSize := encodeOctalField size 11
  fMtime := encodeOctalField mtime 11
  fChk := chkField
  fType := typeflag
  fLink := padRightBytes 100 linkname.toUTF8
  fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]
  fVer := ByteArray.mk #[0x30, 0x30]
  fUname := padRightBytes 32 uname.toUTF8
  fGname := padRightBytes 32 gname.toUTF8
  fDev := ByteArray.mk (Array.replicate 16 0)
  fPrefix := padRightBytes 155 pfx.toUTF8
  fPad := ByteArray.mk (Array.replicate 12 0)

/-- `RawUstarHeader.ofFields` is `WellSized` whenever `chkField.size = 8`. -/
theorem RawUstarHeader.ofFields_wellSized {name : String} {mode : UInt32} {uid gid size mtime : Nat}
    {typeflag : UInt8} {linkname uname gname pfx : String} {chkField : ByteArray}
    (hchk : chkField.size = 8) :
    (RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx chkField).WellSized where
  szName := padRightBytes_size 100 _
  szMode := encodeOctalField_size _ 7
  szUid := encodeOctalField_size _ 7
  szGid := encodeOctalField_size _ 7
  szSize := encodeOctalField_size _ 11
  szMtime := encodeOctalField_size _ 11
  szChk := hchk
  szLink := padRightBytes_size 100 _
  szMagic := rfl
  szVer := rfl
  szUname := padRightBytes_size 32 _
  szGname := padRightBytes_size 32 _
  szDev := by simp [RawUstarHeader.ofFields, ByteArray.size]
  szPrefix := padRightBytes_size 155 _
  szPad := by simp [RawUstarHeader.ofFields, ByteArray.size]

/-- All-zero `RawUstarHeader` corresponding to `zeroBlock`. -/
def RawUstarHeader.zeros : RawUstarHeader where
  fName := ByteArray.mk (Array.replicate 100 0)
  fMode := ByteArray.mk (Array.replicate 8 0)
  fUid := ByteArray.mk (Array.replicate 8 0)
  fGid := ByteArray.mk (Array.replicate 8 0)
  fSize := ByteArray.mk (Array.replicate 12 0)
  fMtime := ByteArray.mk (Array.replicate 12 0)
  fChk := ByteArray.mk (Array.replicate 8 0)
  fType := 0
  fLink := ByteArray.mk (Array.replicate 100 0)
  fMagic := ByteArray.mk (Array.replicate 6 0)
  fVer := ByteArray.mk (Array.replicate 2 0)
  fUname := ByteArray.mk (Array.replicate 32 0)
  fGname := ByteArray.mk (Array.replicate 32 0)
  fDev := ByteArray.mk (Array.replicate 16 0)
  fPrefix := ByteArray.mk (Array.replicate 155 0)
  fPad := ByteArray.mk (Array.replicate 12 0)

/-- `RawUstarHeader.zeros` is `WellSized`. -/
theorem RawUstarHeader.zeros_wellSized : RawUstarHeader.zeros.WellSized where
  szName := by decide
  szMode := by decide
  szUid := by decide
  szGid := by decide
  szSize := by decide
  szMtime := by decide
  szChk := by decide
  szLink := by decide
  szMagic := by decide
  szVer := by decide
  szUname := by decide
  szGname := by decide
  szDev := by decide
  szPrefix := by decide
  szPad := by decide

private theorem encodeOctalField_6_sp_size (chk : Nat) :
    (encodeOctalField chk 6 ++ ByteArray.mk #[0x20]).size = 8 := by
  rw [ByteArray.size_append, encodeOctalField_size]
  rfl

private theorem padRightBytes_exact_len {bs : ByteArray} {w : Nat} (h : bs.size = w) :
    padRightBytes w bs = bs := by
  unfold padRightBytes
  have hge : bs.size ≥ w := by omega
  simp only [hge, ↓reduceIte]
  rw [← h]
  exact ByteArray.extract_zero_size

/-- `buildUstarHeader` equals `(RawUstarHeader.ofFields ... chkField).toBytes`. -/
theorem buildUstarHeader_eq_raw (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    let hdrPre := (RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
      (ByteArray.mk (Array.replicate 8 0x20))).toBytes
    let chkField := encodeOctalField (ustarChecksumAt hdrPre 0) 6 ++ ByteArray.mk #[0x20]
    buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx =
      (RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx chkField).toBytes := by
  unfold buildUstarHeader RawUstarHeader.ofFields RawUstarHeader.toBytes
  rfl

private theorem replicate_zero_append (a b : Nat) :
    ByteArray.mk (Array.replicate a 0) ++ ByteArray.mk (Array.replicate b 0) =
      ByteArray.mk (Array.replicate (a + b) 0) := by
  apply ByteArray.ext; apply Array.ext
  · show (ByteArray.mk (Array.replicate a 0) ++ ByteArray.mk (Array.replicate b 0)).size =
      (ByteArray.mk (Array.replicate (a + b) 0)).size
    rw [ByteArray.size_append]
    simp [ByteArray.size]
  · intro i hi1 hi2
    have hi1' : i < (ByteArray.mk (Array.replicate a 0) ++ ByteArray.mk (Array.replicate b 0)).size := hi1
    have hsz : (ByteArray.mk (Array.replicate (a + b) 0)).size = a + b := by simp [ByteArray.size]
    have hi2' : i < a + b := by rw [← hsz]; exact hi2
    rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
      ← ByteArray.getElem_eq_getElem_data (h := hi2)]
    change _ = (Array.replicate (a + b) (0 : UInt8))[i]'hi2
    rw [Array.getElem_replicate]
    by_cases hlt : i < a
    · have ha : i < (ByteArray.mk (Array.replicate a 0)).size := by simp [ByteArray.size]; exact hlt
      rw [getElem_append_left ha]
      change (Array.replicate a (0 : UInt8))[i]'ha = 0
      rw [Array.getElem_replicate]
    · have hge : (ByteArray.mk (Array.replicate a 0)).size ≤ i := by simp [ByteArray.size]; omega
      rw [getElem_append_right hge]
      change (Array.replicate b (0 : UInt8))[i - (ByteArray.mk (Array.replicate a 0)).size]'_ = 0
      rw [Array.getElem_replicate]

/-- `zeroBlock` equals `RawUstarHeader.zeros.toBytes`. -/
theorem zeroBlock_eq_raw : zeroBlock = RawUstarHeader.zeros.toBytes := by
  unfold RawUstarHeader.zeros RawUstarHeader.toBytes
  have h1 : ByteArray.mk #[0] = ByteArray.mk (Array.replicate 1 0) := by decide
  dsimp only
  rw [h1]
  simp only [replicate_zero_append]
  have h512 : 100 + 8 + 8 + 8 + 12 + 12 + 8 + 1 + 100 + 6 + 2 + 32 + 32 + 16 + 155 + 12 = 512 := rfl
  rw [h512]
  rfl

/-- Overwrite a contiguous middle slice `M` inside `L ++ (M ++ R)` with `blitFixed M 0 w src`. -/
theorem blitFixed_append_mid (L M R src : ByteArray) {off w : Nat}
    (hL : L.size = off) (hM : M.size = w) :
    blitFixed (L ++ (M ++ R)) off w src = L ++ (blitFixed M 0 w src ++ R) := by
  have hbd1 : off + min w src.size ≤ (L ++ (M ++ R)).size := by
    simp only [ByteArray.size_append, hL, hM]; omega
  have hbd2 : 0 + min w src.size ≤ M.size := by rw [hM]; omega
  apply ByteArray.ext; apply Array.ext
  · show (blitFixed (L ++ (M ++ R)) off w src).size = (L ++ (blitFixed M 0 w src ++ R)).size
    simp only [blitFixed_size, ByteArray.size_append]
  · intro i hi1 hi2
    have hi1' : i < (L ++ (M ++ R)).size := by
      rw [← blitFixed_size (dst := L ++ (M ++ R)) (offset := off) (width := w) (src := src)]; exact hi1
    have hi2' : i < (L ++ (blitFixed M 0 w src ++ R)).size := hi2
    rw [← ByteArray.getElem_eq_getElem_data (h := hi1),
      ← ByteArray.getElem_eq_getElem_data (h := hi2')]
    rw [blitFixed_getElem hbd1 hi1']
    rcases Nat.lt_or_ge i off with hlt | hge
    · have hnot : ¬(off ≤ i ∧ i < off + min w src.size) := by omega
      simp only [hnot, ↓reduceDIte]
      rw [getElem_append_left (by rw [hL]; exact hlt), getElem_append_left (by rw [hL]; exact hlt)]
    · have hLle : L.size ≤ i := by omega
      rw [getElem_append_right hLle, getElem_append_right hLle]
      rcases Nat.lt_or_ge i (off + w) with hmid | hright
      · have hMlt : i - L.size < M.size := by rw [hL, hM]; omega
        have hMlt' : i - L.size < (blitFixed M 0 w src).size := by rw [blitFixed_size]; exact hMlt
        rw [getElem_append_left hMlt, getElem_append_left hMlt', blitFixed_getElem hbd2 hMlt]
        by_cases hcond : off ≤ i ∧ i < off + min w src.size
        · have hcond' : 0 ≤ i - L.size ∧ i - L.size < 0 + min w src.size := by rw [hL]; omega
          rw [dite_eq_left hcond, dite_eq_left hcond']
          congr 1; omega
        · have hcond' : ¬(0 ≤ i - L.size ∧ i - L.size < 0 + min w src.size) := by rw [hL]; omega
          rw [dite_eq_right hcond, dite_eq_right hcond']
      · have hnot : ¬(off ≤ i ∧ i < off + min w src.size) := by omega
        rw [dite_eq_right hnot]
        have hMle : M.size ≤ i - L.size := by rw [hL, hM]; omega
        have hMle' : (blitFixed M 0 w src).size ≤ i - L.size := by rw [blitFixed_size]; exact hMle
        rw [getElem_append_right hMle, getElem_append_right hMle']
        congr 1; rw [blitFixed_size]

/-- `blitFixed` on an all-zero buffer of length `w` at offset `0` produces `padRightBytes w src`. -/
theorem blitFixed_zeroReplicate (w : Nat) (src : ByteArray) :
    blitFixed (ByteArray.mk (Array.replicate w 0)) 0 w src = padRightBytes w src := by
  have hz : (ByteArray.mk (Array.replicate w 0)).size = w := by simp [ByteArray.size]
  have hbd : 0 + min w src.size ≤ (ByteArray.mk (Array.replicate w 0)).size := by rw [hz]; omega
  apply ByteArray.ext; apply Array.ext
  · show (blitFixed (ByteArray.mk (Array.replicate w 0)) 0 w src).size = (padRightBytes w src).size
    rw [blitFixed_size, hz, padRightBytes_size]
  · intro i hi1 hi2
    have hi1' : i < (ByteArray.mk (Array.replicate w 0)).size := by rw [← blitFixed_size]; exact hi1
    have hi2' : i < (padRightBytes w src).size := hi2
    have hiw : i < w := by rw [← hz]; exact hi1'
    rw [← ByteArray.getElem_eq_getElem_data (h := hi1),
      ← ByteArray.getElem_eq_getElem_data (h := hi2')]
    rw [blitFixed_getElem hbd hi1', padRightBytes_getElem w src hiw]
    by_cases hlt : i < src.size
    · have hcond : 0 ≤ i ∧ i < 0 + min w src.size := by omega
      rw [dite_eq_left hcond]
      simp [hlt]
    · have hcond : ¬(0 ≤ i ∧ i < 0 + min w src.size) := by omega
      rw [dite_eq_right hcond]
      simp only [hlt]
      change (Array.replicate w (0 : UInt8))[i]'hi1' = 0
      rw [Array.getElem_replicate]

/-- `blitFixed M 0 w src = src` when `M.size = w` and `src.size = w`. -/
theorem blitFixed_exact {M src : ByteArray} {w : Nat} (hM : M.size = w) (hsrc : src.size = w) :
    blitFixed M 0 w src = src := by
  have hbd : 0 + min w src.size ≤ M.size := by rw [hM, hsrc]; omega
  apply ByteArray.ext; apply Array.ext
  · show (blitFixed M 0 w src).size = src.size
    rw [blitFixed_size, hM, hsrc]
  · intro i hi1 hi2
    have hi1' : i < M.size := by rw [← blitFixed_size]; exact hi1
    have hi2' : i < src.size := hi2
    rw [← ByteArray.getElem_eq_getElem_data (h := hi1),
      ← ByteArray.getElem_eq_getElem_data (h := hi2')]
    rw [blitFixed_getElem hbd hi1']
    have hc : 0 ≤ i ∧ i < 0 + min w src.size := by rw [hsrc] at hi2'; omega
    rw [dite_eq_left hc]
    rfl

/-- `set!` inside the middle slice `M` of `L ++ (M ++ R)` updates `M` cleanly. -/
theorem set!_append_mid (L M R : ByteArray) (k : Nat) (v : UInt8) (hk : k < M.size) :
    (L ++ (M ++ R)).set! (L.size + k) v = L ++ (M.set! k v ++ R) := by
  have htot : L.size + k < (L ++ (M ++ R)).size := by simp only [ByteArray.size_append]; omega
  apply ByteArray.ext; apply Array.ext
  · show ((L ++ (M ++ R)).set! (L.size + k) v).size = (L ++ (M.set! k v ++ R)).size
    simp only [byteArray_size_set!, ByteArray.size_append]
  · intro i hi1 hi2
    have hi_tot : i < (L ++ (M ++ R)).size := by
      rw [← byteArray_size_set! (L ++ (M ++ R)) (L.size + k) v]; exact hi1
    have hi2' : i < (L ++ (M.set! k v ++ R)).size := hi2
    rw [← ByteArray.getElem_eq_getElem_data (h := hi1),
      ← ByteArray.getElem_eq_getElem_data (h := hi2')]
    rw [byteArray_getElem_set! htot hi_tot]
    rcases Nat.lt_or_ge i L.size with hlt | hge
    · have hne : L.size + k ≠ i := by omega
      rw [ite_eq_right hne, getElem_append_left hlt, getElem_append_left hlt]
    · rw [getElem_append_right hge hi2', getElem_append_right hge hi_tot]
      rcases Nat.lt_or_ge (i - L.size) M.size with hm_lt | hm_ge
      · have hm_lt' : i - L.size < (M.set! k v).size := by rw [byteArray_size_set!]; exact hm_lt
        rw [getElem_append_left hm_lt', getElem_append_left hm_lt, byteArray_getElem_set! hk hm_lt]
        by_cases hik : k = i - L.size
        · rw [ite_eq_left (by omega : L.size + k = i), ite_eq_left hik]
        · rw [ite_eq_right (by omega : L.size + k ≠ i), ite_eq_right hik]
      · have hne : L.size + k ≠ i := by omega
        have hm_ge' : (M.set! k v).size ≤ i - L.size := by rw [byteArray_size_set!]; exact hm_ge
        rw [ite_eq_right hne, getElem_append_right hm_ge', getElem_append_right hm_ge]
        congr 1; rw [byteArray_size_set!]

private theorem split_toBytes_name (h : RawUstarHeader) :
    h.toBytes = ByteArray.empty ++ (h.fName ++ (h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++
      h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes
  rw [ByteArray.empty_append]
  simp only [ByteArray.append_assoc]

private theorem split_toBytes_mode (h : RawUstarHeader) :
    h.toBytes = h.fName ++ (h.fMode ++ (h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++
      h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_uid (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode) ++ (h.fUid ++ (h.fGid ++ h.fSize ++ h.fMtime ++
      h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_gid (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid) ++ (h.fGid ++ (h.fSize ++ h.fMtime ++
      h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_size (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid) ++ (h.fSize ++ (h.fMtime ++
      h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_mtime (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize) ++ (h.fMtime ++
      (h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_chk (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) ++
      (h.fChk ++ (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_type (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk) ++
      (ByteArray.mk #[h.fType] ++ (h.fLink ++ h.fMagic ++ h.fVer ++
      h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_link (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
        ByteArray.mk #[h.fType]) ++
      (h.fLink ++ (h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_magic (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
        ByteArray.mk #[h.fType] ++ h.fLink) ++
      (h.fMagic ++ (h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_ver (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
        ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic) ++
      (h.fVer ++ (h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_uname (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
        ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer) ++
      (h.fUname ++ (h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_gname (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
        ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname) ++
      (h.fGname ++ (h.fDev ++ h.fPrefix ++ h.fPad)) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

private theorem split_toBytes_prefix (h : RawUstarHeader) :
    h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
        ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev) ++
      (h.fPrefix ++ h.fPad) := by
  unfold RawUstarHeader.toBytes; simp only [ByteArray.append_assoc]

/-- Blit `src` into field `fName` of `h.toBytes` (assuming `fName` is 100 zero bytes). -/
theorem blitFixed_raw_name {h : RawUstarHeader} (h0 : h.fName = ByteArray.mk (Array.replicate 100 0))
    (src : ByteArray) :
    blitFixed h.toBytes 0 100 src = ({ h with fName := padRightBytes 100 src }).toBytes := by
  rw [split_toBytes_name h,
    blitFixed_append_mid ByteArray.empty h.fName _ src (off := 0) (w := 100) rfl (by rw [h0]; decide)]
  rw [h0, blitFixed_zeroReplicate, split_toBytes_name { h with fName := padRightBytes 100 src }]

/-- Blit `src` into `fMode` of `h.toBytes` when `src.size = 8`. -/
theorem blitFixed_raw_mode {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 8) :
    blitFixed h.toBytes 100 8 src = ({ h with fMode := src }).toBytes := by
  rw [split_toBytes_mode h, blitFixed_append_mid h.fName h.fMode _ src hw.szName hw.szMode]
  rw [blitFixed_exact hw.szMode hsrc, split_toBytes_mode { h with fMode := src }]

/-- Blit `src` into `fUid` of `h.toBytes` when `src.size = 8`. -/
theorem blitFixed_raw_uid {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 8) :
    blitFixed h.toBytes 108 8 src = ({ h with fUid := src }).toBytes := by
  rw [split_toBytes_uid h, blitFixed_append_mid (h.fName ++ h.fMode) h.fUid _ src
    (by simp [ByteArray.size_append, hw.szName, hw.szMode]) hw.szUid]
  rw [blitFixed_exact hw.szUid hsrc, split_toBytes_uid { h with fUid := src }]

/-- Blit `src` into `fGid` of `h.toBytes` when `src.size = 8`. -/
theorem blitFixed_raw_gid {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 8) :
    blitFixed h.toBytes 116 8 src = ({ h with fGid := src }).toBytes := by
  rw [split_toBytes_gid h, blitFixed_append_mid (h.fName ++ h.fMode ++ h.fUid) h.fGid _ src
    (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid]) hw.szGid]
  rw [blitFixed_exact hw.szGid hsrc, split_toBytes_gid { h with fGid := src }]

/-- Blit `src` into `fSize` of `h.toBytes` when `src.size = 12`. -/
theorem blitFixed_raw_size {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 12) :
    blitFixed h.toBytes 124 12 src = ({ h with fSize := src }).toBytes := by
  rw [split_toBytes_size h, blitFixed_append_mid (h.fName ++ h.fMode ++ h.fUid ++ h.fGid) h.fSize _ src
    (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid]) hw.szSize]
  rw [blitFixed_exact hw.szSize hsrc, split_toBytes_size { h with fSize := src }]

/-- Blit `src` into `fMtime` of `h.toBytes` when `src.size = 12`. -/
theorem blitFixed_raw_mtime {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 12) :
    blitFixed h.toBytes 136 12 src = ({ h with fMtime := src }).toBytes := by
  rw [split_toBytes_mtime h, blitFixed_append_mid (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize) h.fMtime _ src
    (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize]) hw.szMtime]
  rw [blitFixed_exact hw.szMtime hsrc, split_toBytes_mtime { h with fMtime := src }]

/-- Set `fType` byte at offset `156` in `h.toBytes`. -/
theorem set!_raw_type {h : RawUstarHeader} (hw : h.WellSized) (v : UInt8) :
    h.toBytes.set! 156 v = ({ h with fType := v }).toBytes := by
  have h156 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk).size = 156 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk]
  have hz : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk).size + 0 = 156 := by omega
  rw [split_toBytes_type h, ← hz, set!_append_mid _ (ByteArray.mk #[h.fType]) _ 0 v (by simp [ByteArray.size])]
  rw [split_toBytes_type { h with fType := v }]
  rfl

/-- Set a byte inside `fChk` at offset `148 + k` (`k < 8`) in `h.toBytes`. -/
theorem set!_raw_chk {h : RawUstarHeader} (hw : h.WellSized) {k : Nat} (hk : k < 8) (v : UInt8) :
    h.toBytes.set! (148 + k) v = ({ h with fChk := h.fChk.set! k v }).toBytes := by
  have h148 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime).size = 148 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  rw [split_toBytes_chk h, ← h148, set!_append_mid _ h.fChk _ k v (by rw [hw.szChk]; exact hk)]
  rw [split_toBytes_chk { h with fChk := h.fChk.set! k v }]

/-- Blit `src` into `fLink` of `h.toBytes` (assuming `fLink` is 100 zero bytes). -/
theorem blitFixed_raw_link {h : RawUstarHeader} (hw : h.WellSized)
    (h0 : h.fLink = ByteArray.mk (Array.replicate 100 0)) (src : ByteArray) :
    blitFixed h.toBytes 157 100 src = ({ h with fLink := padRightBytes 100 src }).toBytes := by
  have h157 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType]).size = 157 := by
    have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype]
  rw [split_toBytes_link h, blitFixed_append_mid _ h.fLink _ src h157 hw.szLink]
  rw [h0, blitFixed_zeroReplicate, split_toBytes_link { h with fLink := padRightBytes 100 src }]

/-- Blit `src` into `fMagic` of `h.toBytes` when `src.size = 6`. -/
theorem blitFixed_raw_magic {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 6) :
    blitFixed h.toBytes 257 6 src = ({ h with fMagic := src }).toBytes := by
  have h257 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
      ByteArray.mk #[h.fType] ++ h.fLink).size = 257 := by
    have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink]
  rw [split_toBytes_magic h, blitFixed_append_mid _ h.fMagic _ src h257 hw.szMagic]
  rw [blitFixed_exact hw.szMagic hsrc, split_toBytes_magic { h with fMagic := src }]

/-- Blit `src` into `fVer` of `h.toBytes` when `src.size = 2`. -/
theorem blitFixed_raw_ver {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 2) :
    blitFixed h.toBytes 263 2 src = ({ h with fVer := src }).toBytes := by
  have h263 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
      ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic).size = 263 := by
    have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic]
  rw [split_toBytes_ver h, blitFixed_append_mid _ h.fVer _ src h263 hw.szVer]
  rw [blitFixed_exact hw.szVer hsrc, split_toBytes_ver { h with fVer := src }]

/-- Blit `src` into `fUname` of `h.toBytes` (assuming `fUname` is 32 zero bytes). -/
theorem blitFixed_raw_uname {h : RawUstarHeader} (hw : h.WellSized)
    (h0 : h.fUname = ByteArray.mk (Array.replicate 32 0)) (src : ByteArray) :
    blitFixed h.toBytes 265 32 src = ({ h with fUname := padRightBytes 32 src }).toBytes := by
  have h265 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
      ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer).size = 265 := by
    have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic, hw.szVer]
  rw [split_toBytes_uname h, blitFixed_append_mid _ h.fUname _ src h265 hw.szUname]
  rw [h0, blitFixed_zeroReplicate, split_toBytes_uname { h with fUname := padRightBytes 32 src }]

/-- Blit `src` into `fGname` of `h.toBytes` (assuming `fGname` is 32 zero bytes). -/
theorem blitFixed_raw_gname {h : RawUstarHeader} (hw : h.WellSized)
    (h0 : h.fGname = ByteArray.mk (Array.replicate 32 0)) (src : ByteArray) :
    blitFixed h.toBytes 297 32 src = ({ h with fGname := padRightBytes 32 src }).toBytes := by
  have h297 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
      ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname).size = 297 := by
    have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic, hw.szVer, hw.szUname]
  rw [split_toBytes_gname h, blitFixed_append_mid _ h.fGname _ src h297 hw.szGname]
  rw [h0, blitFixed_zeroReplicate, split_toBytes_gname { h with fGname := padRightBytes 32 src }]

/-- Blit `src` into `fPrefix` of `h.toBytes` (assuming `fPrefix` is 155 zero bytes). -/
theorem blitFixed_raw_prefix {h : RawUstarHeader} (hw : h.WellSized)
    (h0 : h.fPrefix = ByteArray.mk (Array.replicate 155 0)) (src : ByteArray) :
    blitFixed h.toBytes 345 155 src = ({ h with fPrefix := padRightBytes 155 src }).toBytes := by
  have h345 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
      ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev).size = 345 := by
    have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic, hw.szVer, hw.szUname, hw.szGname, hw.szDev]
  rw [split_toBytes_prefix h, blitFixed_append_mid _ h.fPrefix _ src h345 hw.szPrefix]
  rw [h0, blitFixed_zeroReplicate, split_toBytes_prefix { h with fPrefix := padRightBytes 155 src }]

/-- `patchHeaderChecksum` on `h.toBytes` updates `fChk` to the encoded checksum of `h.toBytes`. -/
theorem patchHeaderChecksum_raw {h : RawUstarHeader} (hw : h.WellSized) :
    patchHeaderChecksum h.toBytes =
      (h.withChk (encodeOctalField (ustarChecksum h.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
  unfold patchHeaderChecksum RawUstarHeader.withChk
  let chkF := encodeOctalField (ustarChecksum h.toBytes) 6 ++ ByteArray.mk #[0x20]
  change blitFixed h.toBytes 148 8 chkF = ({ h with fChk := chkF }).toBytes
  have h148 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime).size = 148 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  have hchk_sz : chkF.size = 8 := encodeOctalField_6_sp_size _
  rw [split_toBytes_chk h, blitFixed_append_mid _ h.fChk _ chkF h148 hw.szChk,
    blitFixed_exact hw.szChk hchk_sz, split_toBytes_chk { h with fChk := chkF }]

/-- `bytes[offset + i]` agrees outside `[148..156)` whenever `bytes.extract offset (offset + 512) = (h.withChk c).toBytes`. -/
theorem raw_withChk_outside_eq {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader}
    {c1 c2 : ByteArray} (hw : h.WellSized) (hc1 : c1.size = 8) (hc2 : c2.size = 8)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = (h.withChk c1).toBytes)
    {i : Nat} (hi : i < 512) (hnot : ¬(148 ≤ i ∧ i < 156)) :
    bytes[offset + i]'(by omega) = (h.withChk c2).toBytes[i]'(by
      rw [RawUstarHeader.toBytes_size (h.withChk_wellSized hw hc2)]; exact hi) := by
  have hext_sz : (bytes.extract offset (offset + 512)).size = 512 := by
    rw [ByteArray.size_extract]; omega
  have hi_e : i < (bytes.extract offset (offset + 512)).size := by rw [hext_sz]; exact hi
  have hbs : bytes[offset + i]'(by omega) = (bytes.extract offset (offset + 512))[i]'hi_e :=
    (ByteArray.getElem_extract hi_e).symm
  rw [hbs]
  have hw1 := h.withChk_wellSized hw hc1
  have hw2 := h.withChk_wellSized hw hc2
  have hi1 : i < (h.withChk c1).toBytes.size := by rw [RawUstarHeader.toBytes_size hw1]; exact hi
  have hi2 : i < (h.withChk c2).toBytes.size := by rw [RawUstarHeader.toBytes_size hw2]; exact hi
  rw [byteArray_getElem_of_eq hext hi_e hi1]
  let L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime
  let R := ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  have hL : L.size = 148 := by
    simp [L, ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  have hs1 : (h.withChk c1).toBytes = L ++ (c1 ++ R) := split_toBytes_chk (h.withChk c1)
  have hs2 : (h.withChk c2).toBytes = L ++ (c2 ++ R) := split_toBytes_chk (h.withChk c2)
  have hi1' : i < (L ++ (c1 ++ R)).size := by rw [← hs1]; exact hi1
  have hi2' : i < (L ++ (c2 ++ R)).size := by rw [← hs2]; exact hi2
  rw [byteArray_getElem_of_eq hs1 hi1 hi1', byteArray_getElem_of_eq hs2 hi2 hi2']
  rcases Nat.lt_or_ge i L.size with hlt | hge
  · rw [getElem_append_left hlt, getElem_append_left hlt]
  · rw [getElem_append_right hge hi1', getElem_append_right hge hi2']
    have hc_ge1 : c1.size ≤ i - L.size := by omega
    have hc_ge2 : c2.size ≤ i - L.size := by omega
    rw [getElem_append_right hc_ge1, getElem_append_right hc_ge2]
    congr 1; omega

/-- `ustarChecksumAt` on a slice equal to `(h.withChk chk).toBytes` depends only on `h` outside `fChk`. -/
theorem raw_ustarChecksumAt_eq {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader}
    {c1 c2 : ByteArray} (hw : h.WellSized) (hc1 : c1.size = 8) (hc2 : c2.size = 8)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = (h.withChk c1).toBytes) :
    ustarChecksumAt bytes offset = ustarChecksum (h.withChk c2).toBytes :=
  ustarChecksumAt_eq_ustarChecksum hbd
    (by rw [RawUstarHeader.toBytes_size (h.withChk_wellSized hw hc2)]; exact Nat.le_refl _)
    (fun _ hi hnot => raw_withChk_outside_eq hw hc1 hc2 hbd hext hi hnot)

/-- Extract any field slice from `bytes.extract offset (offset + 512) = h.toBytes`. -/
theorem raw_extract_fields {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader} (hw : h.WellSized)
    (hext : bytes.extract offset (offset + 512) = h.toBytes) :
    bytes.extract offset (offset + 100) = h.fName ∧
    bytes.extract (offset + 100) (offset + 108) = h.fMode ∧
    bytes.extract (offset + 108) (offset + 116) = h.fUid ∧
    bytes.extract (offset + 116) (offset + 124) = h.fGid ∧
    bytes.extract (offset + 124) (offset + 136) = h.fSize ∧
    bytes.extract (offset + 136) (offset + 148) = h.fMtime ∧
    bytes.extract (offset + 148) (offset + 156) = h.fChk ∧
    bytes.extract (offset + 157) (offset + 257) = h.fLink ∧
    bytes.extract (offset + 257) (offset + 263) = h.fMagic ∧
    bytes.extract (offset + 263) (offset + 265) = h.fVer ∧
    bytes.extract (offset + 265) (offset + 297) = h.fUname ∧
    bytes.extract (offset + 297) (offset + 329) = h.fGname ∧
    bytes.extract (offset + 345) (offset + 500) = h.fPrefix := by
  have htype : (ByteArray.mk #[h.fType]).size = 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_zero] using extract_sub_eq (a := 0) (w := 100) (hext.trans (split_toBytes_name h)) rfl hw.szName (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_mode h)) hw.szName hw.szMode (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_uid h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode]) hw.szUid (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_gid h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid]) hw.szGid (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_size h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid]) hw.szSize (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_mtime h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize]) hw.szMtime (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_chk h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]) hw.szChk (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_link h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype]) hw.szLink (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_magic h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink]) hw.szMagic (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_ver h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic]) hw.szVer (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_uname h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic, hw.szVer]) hw.szUname (by omega)
  · simpa only [Nat.add_assoc] using extract_sub_eq (hext.trans (split_toBytes_gname h))
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic, hw.szVer, hw.szUname]) hw.szGname (by omega)
  · have hs : bytes.extract offset (offset + 512) = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev) ++ (h.fPrefix ++ (h.fPad ++ ByteArray.empty)) := by
      rw [hext, split_toBytes_prefix h, ByteArray.append_empty]
    simpa only [Nat.add_assoc] using extract_sub_eq hs
      (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, htype, hw.szLink, hw.szMagic, hw.szVer, hw.szUname, hw.szGname, hw.szDev]) hw.szPrefix (by omega)

/-- Read `fType` byte at `offset + 156` when `bytes.extract offset (offset + 512) = h.toBytes`. -/
theorem raw_getElem_type {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader} (hw : h.WellSized)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = h.toBytes) :
    bytes[offset + 156]'(by omega) = h.fType := by
  have hext_sz : (bytes.extract offset (offset + 512)).size = 512 := by rw [ByteArray.size_extract]; omega
  have hi_e : 156 < (bytes.extract offset (offset + 512)).size := by rw [hext_sz]; omega
  have hi_h : 156 < h.toBytes.size := by rw [RawUstarHeader.toBytes_size hw]; omega
  rw [← ByteArray.getElem_extract hi_e, byteArray_getElem_of_eq hext hi_e hi_h]
  let L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk
  have hL : L.size = 156 := by
    simp [L, ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk]
  have hs : h.toBytes = L ++ (ByteArray.mk #[h.fType] ++ _) := split_toBytes_type h
  have hi_s : 156 < (L ++ (ByteArray.mk #[h.fType] ++ (h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad))).size := by
    rw [← hs]; exact hi_h
  rw [byteArray_getElem_of_eq hs hi_h hi_s, getElem_append_right (by rw [hL]; exact Nat.le_refl _)]
  have h0 : 156 - L.size = 0 := by rw [hL]
  simp only [h0]
  have hft : (ByteArray.mk #[h.fType]).size = 1 := rfl
  rw [getElem_append_left (by rw [hft]; omega) (hab := by rw [ByteArray.size_append, hft]; omega)]
  rfl

/-- `parseUstarNumeric` depends only on the extracted slice `bytes.extract start stop`. -/
theorem parseUstarNumeric_congr {b1 b2 : ByteArray} {s1 e1 s2 e2 off1 off2 : Nat}
    {allow : Bool} {lim : Nat} {fn : String}
    (hext : b1.extract s1 e1 = b2.extract s2 e2)
    (hoff : off1 = off2) :
    parseUstarNumeric b1 s1 e1 off1 allow lim fn = parseUstarNumeric b2 s2 e2 off2 allow lim fn := by
  subst hoff
  unfold parseUstarNumeric
  rw [hext]

/-- `parseUstarHeader` succeeds on `buildUstarHeader` with valid USTAR checksum, magic, and field codecs. -/
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
  let h0 := RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
    (ByteArray.mk (Array.replicate 8 0x20))
  let chk := ustarChecksumAt h0.toBytes 0
  let chkField := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  let h := h0.withChk chkField
  have hw0 : h0.WellSized := RawUstarHeader.ofFields_wellSized (by decide)
  have hcf_sz : chkField.size = 8 := encodeOctalField_6_sp_size chk
  have hw : h.WellSized := h0.withChk_wellSized hw0 hcf_sz
  have hbuild_eq : buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx = h.toBytes :=
    buildUstarHeader_eq_raw name mode uid gid size mtime typeflag linkname uname gname pfx
  have hext' : bytes.extract offset (offset + 512) = h.toBytes := hext.trans hbuild_eq
  have hchk_lt : chk < 8 ^ 6 := ustarChecksumAt_lt h0.toBytes 0
  have hchk_eq : ustarChecksumAt bytes offset = chk := by
    have h1 := raw_ustarChecksumAt_eq (c1 := chkField) (c2 := ByteArray.mk (Array.replicate 8 0x20))
      hw0 hcf_sz (by decide) hbd hext'
    have h0_eq : h0.withChk (ByteArray.mk (Array.replicate 8 0x20)) = h0 := rfl
    rw [h0_eq, ustarChecksum_eq_ustarChecksumAt] at h1
    exact h1
  have ⟨_, hext_mode, hext_uid, hext_gid, hext_size, hext_mtime, hext_chk, _,
      hext_magic, hext_ver, _, _, _⟩ := raw_extract_fields hw hext'
  have hchk_eq_chk : h.fChk = encodeOctalField chk 6 ++ ByteArray.mk #[0x20] := rfl
  have hext_chk' : bytes.extract (offset + 148) (offset + 148 + 8) =
      encodeOctalField chk 6 ++ ByteArray.mk #[0x20] := by
    rw [← (by omega : offset + 156 = offset + 148 + 8), hext_chk, hchk_eq_chk]
  have hparse_chk : parseChecksumOctal bytes (offset + 148) (offset + 156) offset = .ok chk := by
    rw [(by omega : offset + 156 = offset + 148 + 8)]
    exact parseChecksumOctal_encodeOctalField hchk_lt hext_chk'
  have hmagic : hasValidMagic bytes offset = true := by
    unfold hasValidMagic
    have h263 : offset + 263 = offset + 257 + 6 := by omega
    have h265 : offset + 265 = offset + 263 + 2 := by omega
    have hm : h.fMagic = ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00] := rfl
    have hv : h.fVer = ByteArray.mk #[0x30, 0x30] := rfl
    rw [h263, hext_magic, h265, hext_ver, hm, hv]
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
  have htype_byte : bytes[offset + 156]'(by omega) = typeflag := raw_getElem_type hw hbd hext'
  unfold parseUstarHeader
  have hlt_bd : offset + 156 < bytes.size := by omega
  simp only [hparse_chk, hchk_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    hmagic, Bool.not_true, hparse_mode, hparse_uid, hparse_gid, hparse_size, hparse_mtime,
    hlt_bd, ↓reduceDIte, htype_byte, bind, Except.bind, pure, Except.pure]

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
  let h0 := RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
    (ByteArray.mk (Array.replicate 8 0x20))
  let chkField := encodeOctalField (ustarChecksumAt h0.toBytes 0) 6 ++ ByteArray.mk #[0x20]
  let h := h0.withChk chkField
  have hw : h.WellSized := h0.withChk_wellSized
    (RawUstarHeader.ofFields_wellSized (by decide)) (encodeOctalField_6_sp_size _)
  have hext' : bytes.extract offset (offset + 512) = h.toBytes :=
    hext.trans (buildUstarHeader_eq_raw name mode uid gid size mtime typeflag linkname uname gname pfx)
  have ⟨hn, _, _, _, _, _, _, hl, _, _, hu, hg, hp⟩ := raw_extract_fields hw hext'
  exact ⟨hn, hl, hu, hg, hp⟩

/-- A `buildUstarHeader` block at `offset` is never all-zero (magic byte `257` is `0x75`). -/
theorem isZeroRange_buildUstarHeader_false {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    isZeroRange bytes offset 512 = false := by
  let h0 := RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
    (ByteArray.mk (Array.replicate 8 0x20))
  let chkField := encodeOctalField (ustarChecksumAt h0.toBytes 0) 6 ++ ByteArray.mk #[0x20]
  let h := h0.withChk chkField
  have hw : h.WellSized := h0.withChk_wellSized
    (RawUstarHeader.ofFields_wellSized (by decide)) (encodeOctalField_6_sp_size _)
  have hext' : bytes.extract offset (offset + 512) = h.toBytes :=
    hext.trans (buildUstarHeader_eq_raw name mode uid gid size mtime typeflag linkname uname gname pfx)
  have hext_magic := (raw_extract_fields hw hext').2.2.2.2.2.2.2.2.1
  have h257_m : 0 < h.fMagic.size := by rw [hw.szMagic]; omega
  have h257_e : 0 < (bytes.extract (offset + 257) (offset + 263)).size := by rw [hext_magic]; exact h257_m
  have hb257 : bytes[offset + 257]'(by omega) = 0x75 := by
    have hg := ByteArray.getElem_extract h257_e
    rw [byteArray_getElem_of_eq hext_magic h257_e h257_m] at hg
    have hm0 : h.fMagic[0]'h257_m = 0x75 := rfl
    rw [hm0] at hg
    simpa using hg.symm
  exact isZeroRange_false_of_ne (i := 257) (by omega) (by omega) (by rw [hb257]; decide)

/-- `(buildUstarHeader ...).size = 512`. -/
theorem buildUstarHeader_size (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    (buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx).size = 512 := by
  rw [buildUstarHeader_eq_raw]
  exact RawUstarHeader.toBytes_size (RawUstarHeader.ofFields_wellSized (encodeOctalField_6_sp_size _))

/-- `mkUstarHeader` produces the exact same 512-byte header as `buildUstarHeader`. -/
theorem mkUstarHeader_eq_buildUstarHeader (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx =
      buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx := by
  have hm : "ustar\x00".toUTF8 = ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00] := by decide
  have hv : "00".toUTF8 = ByteArray.mk #[0x30, 0x30] := by decide
  have hm6 : "ustar\x00".toUTF8.size = 6 := by decide
  have hv2 : "00".toUTF8.size = 2 := by decide
  let r0 := RawUstarHeader.zeros
  let r1 := { r0 with fName := padRightBytes 100 name.toUTF8 }
  let r2 := { r1 with fMode := encodeOctalField (mode &&& 0o7777).toNat 7 }
  let r3 := { r2 with fUid := encodeOctalField uid 7 }
  let r4 := { r3 with fGid := encodeOctalField gid 7 }
  let r5 := { r4 with fSize := encodeOctalField size 11 }
  let r6 := { r5 with fMtime := encodeOctalField mtime 11 }
  let r7 := { r6 with fType := typeflag }
  let r8 := { r7 with fLink := padRightBytes 100 linkname.toUTF8 }
  let r9 := { r8 with fMagic := "ustar\x00".toUTF8 }
  let r10 := { r9 with fVer := "00".toUTF8 }
  let r11 := { r10 with fUname := padRightBytes 32 uname.toUTF8 }
  let r12 := { r11 with fGname := padRightBytes 32 gname.toUTF8 }
  let r13 := { r12 with fPrefix := padRightBytes 155 pfx.toUTF8 }
  have hw0 : r0.WellSized := RawUstarHeader.zeros_wellSized
  have hw1 : r1.WellSized := { hw0 with szName := padRightBytes_size 100 _ }
  have hw2 : r2.WellSized := { hw1 with szMode := encodeOctalField_size _ 7 }
  have hw3 : r3.WellSized := { hw2 with szUid := encodeOctalField_size _ 7 }
  have hw4 : r4.WellSized := { hw3 with szGid := encodeOctalField_size _ 7 }
  have hw5 : r5.WellSized := { hw4 with szSize := encodeOctalField_size _ 11 }
  have hw6 : r6.WellSized := { hw5 with szMtime := encodeOctalField_size _ 11 }
  have hw7 : r7.WellSized := { hw6 with }
  have hw8 : r8.WellSized := { hw7 with szLink := padRightBytes_size 100 _ }
  have hw9 : r9.WellSized := { hw8 with szMagic := hm6 }
  have hw10 : r10.WellSized := { hw9 with szVer := hv2 }
  have hw11 : r11.WellSized := { hw10 with szUname := padRightBytes_size 32 _ }
  have hw12 : r12.WellSized := { hw11 with szGname := padRightBytes_size 32 _ }
  have hw13 : r13.WellSized := { hw12 with szPrefix := padRightBytes_size 155 _ }
  have hb0 : zeroBlock = r0.toBytes := zeroBlock_eq_raw
  have hb1 : blitFixed r0.toBytes 0 100 name.toUTF8 = r1.toBytes := blitFixed_raw_name rfl _
  have hb2 : blitFixed r1.toBytes 100 8 (encodeOctalField (mode &&& 0o7777).toNat 7) = r2.toBytes :=
    blitFixed_raw_mode hw1 (encodeOctalField_size _ 7)
  have hb3 : blitFixed r2.toBytes 108 8 (encodeOctalField uid 7) = r3.toBytes :=
    blitFixed_raw_uid hw2 (encodeOctalField_size _ 7)
  have hb4 : blitFixed r3.toBytes 116 8 (encodeOctalField gid 7) = r4.toBytes :=
    blitFixed_raw_gid hw3 (encodeOctalField_size _ 7)
  have hb5 : blitFixed r4.toBytes 124 12 (encodeOctalField size 11) = r5.toBytes :=
    blitFixed_raw_size hw4 (encodeOctalField_size _ 11)
  have hb6 : blitFixed r5.toBytes 136 12 (encodeOctalField mtime 11) = r6.toBytes :=
    blitFixed_raw_mtime hw5 (encodeOctalField_size _ 11)
  have hb7 : r6.toBytes.set! 156 typeflag = r7.toBytes := set!_raw_type hw6 typeflag
  have hb8 : blitFixed r7.toBytes 157 100 linkname.toUTF8 = r8.toBytes := blitFixed_raw_link hw7 rfl _
  have hb9 : blitFixed r8.toBytes 257 6 "ustar\x00".toUTF8 = r9.toBytes := blitFixed_raw_magic hw8 hm6
  have hb10 : blitFixed r9.toBytes 263 2 "00".toUTF8 = r10.toBytes := blitFixed_raw_ver hw9 hv2
  have hb11 : blitFixed r10.toBytes 265 32 uname.toUTF8 = r11.toBytes := blitFixed_raw_uname hw10 rfl _
  have hb12 : blitFixed r11.toBytes 297 32 gname.toUTF8 = r12.toBytes := blitFixed_raw_gname hw11 rfl _
  have hb13 : blitFixed r12.toBytes 345 155 pfx.toUTF8 = r13.toBytes := blitFixed_raw_prefix hw12 rfl _
  have h13 : (let b0 := zeroBlock; let b1 := blitFixed b0 0 100 name.toUTF8
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
      blitFixed b12 345 155 pfx.toUTF8) = r13.toBytes := by
    dsimp only; rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13]
  unfold mkUstarHeader
  change patchHeaderChecksum _ = _
  rw [h13, patchHeaderChecksum_raw hw13, buildUstarHeader_eq_raw]
  let hSp := RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
    (ByteArray.mk (Array.replicate 8 0x20))
  have hr13_eq : r13 = hSp.withChk (ByteArray.mk (Array.replicate 8 0)) := by
    dsimp only [r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, r0,
      RawUstarHeader.zeros, hSp, RawUstarHeader.withChk, RawUstarHeader.ofFields]
    rw [hm, hv]
  have hwSp : hSp.WellSized := RawUstarHeader.ofFields_wellSized (by decide)
  have hsz_13 : r13.toBytes.size = 512 := RawUstarHeader.toBytes_size hw13
  have hsz_sp : hSp.toBytes.size = 512 := RawUstarHeader.toBytes_size hwSp
  have hchk_eq : ustarChecksum r13.toBytes = ustarChecksumAt hSp.toBytes 0 := by
    rw [ustarChecksum_eq_ustarChecksumAt]
    refine ustarChecksumAt_congr (by omega) (by omega) ?_
    intro i hi hnot
    have hhext : r13.toBytes.extract 0 512 = (hSp.withChk (ByteArray.mk (Array.replicate 8 0))).toBytes := by
      rw [← hsz_13, ByteArray.extract_zero_size, hr13_eq]
    have hraw : r13.toBytes[0 + i]'(by omega) = hSp.toBytes[i]'(by omega) :=
      raw_withChk_outside_eq (c2 := ByteArray.mk (Array.replicate 8 0x20))
        hwSp (by decide) (by decide) (by omega) hhext hi hnot
    simpa [Nat.zero_add] using hraw
  rw [hchk_eq, hr13_eq]
  dsimp only [RawUstarHeader.withChk, RawUstarHeader.ofFields, hSp]

/-- Size of `mkUstarHeader ...` is `512`. -/
theorem mkUstarHeader_size (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    (mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx).size = 512 := by
  rw [mkUstarHeader_eq_buildUstarHeader]
  exact buildUstarHeader_size ..

/-- Size of `patchHeaderChecksum hdr` is `hdr.size`. -/
theorem patchHeaderChecksum_size (hdr : ByteArray) :
    (patchHeaderChecksum hdr).size = hdr.size :=
  blitFixed_size hdr 148 8 _

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
      , typeflag := typeflag } :=
  parseUstarHeader_buildUstarHeader huid hgid hsize hmtime hbd
    (hext.trans (mkUstarHeader_eq_buildUstarHeader ..))

/-- Extracting a suffix starting at `a.size` from `a ++ b` slices `b` from `0`. -/
theorem extract_append_right (a b : ByteArray) (k : Nat) :
    (a ++ b).extract a.size (a.size + k) = b.extract 0 k := by
  rw [ByteArray.extract_append]
  have hemp : a.extract a.size (a.size + k) = ByteArray.empty :=
    ByteArray.extract_eq_empty_iff.mpr (Nat.min_le_right _ _)
  simp [hemp, ByteArray.empty_append]

/-- Extracting the exact middle factor from `a ++ b ++ c`. -/
theorem extract_append_mid (a b c : ByteArray) :
    (a ++ b ++ c).extract a.size (a.size + b.size) = b := by
  rw [ByteArray.append_assoc, extract_append_right, extract_append_exact_left]

private theorem unpackLoopFuel_indep (n fuel1 fuel2 : Nat)
    (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat)
    (hrem : bytes.size - offset ≤ n)
    (hf1 : n + 1 ≤ fuel1) (hf2 : n + 1 ≤ fuel2) :
    unpackLoopFuel fuel1 opts bytes offset pendingPax seen acc totalBytes =
      unpackLoopFuel fuel2 opts bytes offset pendingPax seen acc totalBytes := by
  induction n generalizing fuel1 fuel2 offset pendingPax seen acc totalBytes with
  | zero =>
    obtain ⟨f1, rfl⟩ : ∃ f1, fuel1 = f1 + 1 := ⟨fuel1 - 1, by omega⟩
    obtain ⟨f2, rfl⟩ : ∃ f2, fuel2 = f2 + 1 := ⟨fuel2 - 1, by omega⟩
    have hge : offset ≥ bytes.size := by omega
    simp [unpackLoopFuel.eq_2, hge]
  | succ n ih =>
    obtain ⟨f1, rfl⟩ : ∃ f1, fuel1 = f1 + 1 := ⟨fuel1 - 1, by omega⟩
    obtain ⟨f2, rfl⟩ : ∃ f2, fuel2 = f2 + 1 := ⟨fuel2 - 1, by omega⟩
    simp only [unpackLoopFuel.eq_2]
    by_cases hge : offset ≥ bytes.size
    · simp [hge]
    · simp only [hge, ↓reduceIte]
      cases hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes with
      | error e => rfl
      | ok s =>
        cases s with
        | done res => rfl
        | cont nextOff nextPax nextSeen nextAcc nextTotal =>
          dsimp only
          by_cases hadv : offset < nextOff
          · simp only [hadv, ↓reduceIte]
            exact ih f1 f2 nextOff nextPax nextSeen nextAcc nextTotal (by omega) (by omega) (by omega)
          · simp [hadv]

/-- If `offset ≥ bytes.size`, `unpackLoop` returns `truncatedArchive`. -/
theorem unpackLoop_at_ge (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) (hge : offset ≥ bytes.size) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes =
      .error { kind := .truncatedArchive, message := "tar archive missing end-of-archive zero blocks",
               offset := some offset } := by
  have hzero : bytes.size - offset = 0 := by omega
  simp [unpackLoop, hzero, unpackLoopFuel.eq_2, hge]

/-- If `unpackStep` completes with `.done res`, `unpackLoop` returns `.ok res`. -/
theorem unpackLoop_step_done (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) (res : List TarEntry)
    (hoff : offset < bytes.size)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes = .ok (.done res)) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes = .ok res := by
  have hge : ¬(offset ≥ bytes.size) := by omega
  simp [unpackLoop, unpackLoopFuel.eq_2, hge, hstep]

/-- If `unpackStep` errors, `unpackLoop` returns that error. -/
theorem unpackLoop_step_err (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) (err : TarError)
    (hoff : offset < bytes.size)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes = .error err) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes = .error err := by
  have hge : ¬(offset ≥ bytes.size) := by omega
  simp [unpackLoop, unpackLoopFuel.eq_2, hge, hstep]

/-- If `unpackStep` advances strictly, `unpackLoop` reduces to `unpackLoop` at `nextOff`. -/
theorem unpackLoop_step_continue (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat)
    (nextOff : Nat) (nextPax : Option PaxOverrides) (nextSeen : List String)
    (nextAcc : List TarEntry) (nextTotal : Nat)
    (hoff : offset < bytes.size)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes =
      .ok (.cont nextOff nextPax nextSeen nextAcc nextTotal))
    (hadv : nextOff > offset) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes =
      unpackLoop opts bytes nextOff nextPax nextSeen nextAcc nextTotal := by
  have hge : ¬(offset ≥ bytes.size) := by omega
  have heq : unpackLoop opts bytes offset pendingPax seen acc totalBytes =
      unpackLoopFuel (bytes.size - offset) opts bytes nextOff nextPax nextSeen nextAcc nextTotal := by
    simp [unpackLoop, unpackLoopFuel.eq_2, hge, hstep, hadv]
  rw [heq]
  exact unpackLoopFuel_indep (bytes.size - nextOff) (bytes.size - offset) (bytes.size - nextOff + 1)
    opts bytes nextOff nextPax nextSeen nextAcc nextTotal (Nat.le_refl _) (by omega) (Nat.le_refl _)

end LeanSwe.Tar.Proofs
