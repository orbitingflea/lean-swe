import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- `(padBlock512 bs).size` is always a multiple of `512`. -/
theorem padBlock512_size_mod (bs : ByteArray) : (padBlock512 bs).size % 512 = 0 := by
  rw [padBlock512_size]; exact pad512_mod bs.size

/-- Upper bound `ustarChecksumAt bytes start ≤ 512 * 255`. -/
theorem ustarChecksumAt_le (bytes : ByteArray) (start : Nat) :
    ustarChecksumAt bytes start ≤ 512 * 255 := by
  unfold ustarChecksumAt
  have hgo : ∀ rem idx acc : Nat, ustarChecksumAt.go bytes start rem idx acc ≤ acc + rem * 255 := by
    intro rem; induction rem with
    | zero => intros; simp [ustarChecksumAt.go.eq_1]
    | succ d ih =>
      intro idx acc; rw [ustarChecksumAt.go.eq_2]
      refine Nat.le_trans (ih (idx + 1) _) ?_
      split
      · omega
      · split
        · rename_i h; have := UInt8.toNat_lt (bytes[start + idx]'h); omega
        · omega
  simpa using hgo 512 0 0

/-- `ustarChecksumAt bytes start < 8 ^ 6`. -/
theorem ustarChecksumAt_lt (bytes : ByteArray) (start : Nat) :
    ustarChecksumAt bytes start < 8 ^ 6 := by
  have := ustarChecksumAt_le bytes start; omega

/-- `ustarChecksum hdr = ustarChecksumAt hdr 0`. -/
theorem ustarChecksum_eq_ustarChecksumAt (hdr : ByteArray) :
    ustarChecksum hdr = ustarChecksumAt hdr 0 := by
  unfold ustarChecksum ustarChecksumAt
  have hgo : ∀ rem idx acc : Nat, rem + idx = 512 →
      ustarChecksum.go hdr idx acc = ustarChecksumAt.go hdr 0 rem idx acc := by
    intro rem; induction rem with
    | zero =>
      intro idx acc hsum; obtain rfl : idx = 512 := by omega
      rw [ustarChecksum.go.eq_1, ustarChecksumAt.go.eq_1]; simp
    | succ d ih =>
      intro idx acc hsum
      rw [ustarChecksum.go.eq_1, ustarChecksumAt.go.eq_2]
      simp only [show ¬(idx ≥ 512) by omega, ↓reduceIte, Nat.zero_add]
      split
      · exact ih (idx + 1) _ (by omega)
      · split <;> exact ih (idx + 1) _ (by omega)
  exact hgo 512 0 0 rfl

/-- `ustarChecksum hdr < 8 ^ 6`. -/
theorem ustarChecksum_lt (hdr : ByteArray) : ustarChecksum hdr < 8 ^ 6 := by
  rw [ustarChecksum_eq_ustarChecksumAt]; exact ustarChecksumAt_lt hdr 0

/-- `ustarChecksumAt` depends only on bytes `[0..512)` outside `[148..156)`. -/
theorem ustarChecksumAt_congr {b1 b2 : ByteArray} {s1 s2 : Nat}
    (hb1 : s1 + 512 ≤ b1.size) (hb2 : s2 + 512 ≤ b2.size)
    (heq : ∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      b1[s1 + i]'(by omega) = b2[s2 + i]'(by omega)) :
    ustarChecksumAt b1 s1 = ustarChecksumAt b2 s2 := by
  unfold ustarChecksumAt
  have hgo : ∀ rem idx acc : Nat, rem + idx = 512 →
      ustarChecksumAt.go b1 s1 rem idx acc = ustarChecksumAt.go b2 s2 rem idx acc := by
    intro rem; induction rem with
    | zero => intros; rfl
    | succ d ih =>
      intro idx acc hsum; rw [ustarChecksumAt.go.eq_2, ustarChecksumAt.go.eq_2]
      by_cases hchk : 148 ≤ idx ∧ idx < 156
      · simp [hchk.1, hchk.2, ih (idx + 1) _ (by omega)]
      · have hcond : (decide (148 ≤ idx) && decide (idx < 156)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        simp only [hcond, Bool.false_eq_true, ↓reduceIte, show s1 + idx < b1.size by omega,
          show s2 + idx < b2.size by omega, ↓reduceDIte, heq idx (by omega) hchk]
        exact ih (idx + 1) _ (by omega)
  exact hgo 512 0 0 rfl

/-- `ustarChecksumAt` coincides with `ustarChecksum` when bytes `[0..512)` outside `[148..156)` match. -/
theorem ustarChecksumAt_eq_ustarChecksum {bytes hdr : ByteArray} {offset : Nat}
    (hby : offset + 512 ≤ bytes.size) (hhdr : 512 ≤ hdr.size)
    (heq : ∀ (i : Nat) (hi : i < 512), ¬(148 ≤ i ∧ i < 156) →
      bytes[offset + i]'(by omega) = hdr[i]'(by omega)) :
    ustarChecksumAt bytes offset = ustarChecksum hdr := by
  rw [ustarChecksum_eq_ustarChecksumAt]
  exact ustarChecksumAt_congr hby (by omega) fun i hi hnot => by simpa using heq i hi hnot

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
    intro rem; induction rem with
    | zero =>
      intro k hsum hpre; obtain rfl : k = len := by omega
      simp only [isZeroRange.go.eq_1, true_iff]
      exact ⟨by rcases hpre with rfl | hbd <;> omega, fun _ h1 h2 => by omega⟩
    | succ d ih =>
      intro k hsum _; rw [isZeroRange.go.eq_2]
      by_cases hbd : offset + k < bytes.size
      · simp only [hbd, ↓reduceDIte]
        by_cases hz : bytes[offset + k]'hbd = 0
        · simp only [beq_iff_eq.mpr hz, ↓reduceIte, ih (k + 1) (by omega) (Or.inr (by omega))]
          exact ⟨fun ⟨hs, ha⟩ => ⟨hs, fun i hki hil hi => if hik : i = k then hik ▸ hz else ha i (by omega) hil hi⟩,
            fun ⟨hs, ha⟩ => ⟨hs, fun i hki hil hi => ha i (by omega) hil hi⟩⟩
        · simp only [beq_false_of_ne hz, Bool.false_eq_true, ↓reduceIte, false_iff]
          exact fun ⟨_, ha⟩ => hz (ha k (Nat.le_refl k) (by omega) hbd)
      · simp only [hbd, ↓reduceDIte, Bool.false_eq_true, false_iff]; omega
  simpa using hgo len 0 rfl (Or.inl rfl)

/-- `isZeroRange` returns `false` if any byte in `[offset .. offset + len)` is non-zero. -/
theorem isZeroRange_false_of_ne {bytes : ByteArray} {offset len i : Nat}
    (hlt : i < len) (hbd : offset + i < bytes.size) (hne : bytes[offset + i]'hbd ≠ 0) :
    isZeroRange bytes offset len = false :=
  Bool.eq_false_iff.mpr fun h => hne (((isZeroRange_eq_true_iff bytes offset len (by omega)).mp h).2 i hlt hbd)

/-- `allZeroTrailer` returns `true` across any all-zero multiple-of-512 tail starting at `offset`. -/
theorem allZeroTrailer_of_zeros {bytes : ByteArray} {offset : Nat}
    (hmod : (bytes.size - offset) % 512 = 0)
    (hz : ∀ i : Nat, offset ≤ i → i < bytes.size → ∀ hi : i < bytes.size, bytes[i]'hi = 0) :
    allZeroTrailer bytes offset = true := by
  unfold allZeroTrailer
  have hgo : ∀ rem off : Nat, rem = (bytes.size - off + 511) / 512 → (bytes.size - off) % 512 = 0 →
      (∀ i : Nat, off ≤ i → i < bytes.size → ∀ hi : i < bytes.size, bytes[i]'hi = 0) →
      allZeroTrailer.go bytes rem off = true := by
    intro rem; induction rem with
    | zero => intros; rfl
    | succ k ih =>
      intro off hrem hmod' hz'; rw [allZeroTrailer.go.eq_2]
      have hzr : isZeroRange bytes off 512 = true :=
        (isZeroRange_eq_true_iff bytes off 512 (by omega)).mpr ⟨by omega, fun i _ hi' => hz' (off + i) (by omega) (by omega) hi'⟩
      simp only [show ¬(off ≥ bytes.size) by omega, ↓reduceIte, hzr, Bool.true_and]
      exact ih (off + 512) (by omega) (by omega) fun i h1 h2 hi => hz' i (by omega) h2 hi
  exact hgo _ offset rfl hmod hz

/-- Symbolic 16-field representation of a 512-byte USTAR header block. -/
structure RawUstarHeader where
  /-- Name field `[0..100)`. -/ fName : ByteArray
  /-- Mode field `[100..108)`. -/ fMode : ByteArray
  /-- UID field `[108..116)`. -/ fUid : ByteArray
  /-- GID field `[116..124)`. -/ fGid : ByteArray
  /-- Size field `[124..136)`. -/ fSize : ByteArray
  /-- Mtime field `[136..148)`. -/ fMtime : ByteArray
  /-- Checksum field `[148..156)`. -/ fChk : ByteArray
  /-- Typeflag byte `[156]`. -/ fType : UInt8
  /-- Linkname field `[157..257)`. -/ fLink : ByteArray
  /-- Magic field `[257..263)`. -/ fMagic : ByteArray
  /-- Version field `[263..265)`. -/ fVer : ByteArray
  /-- User name field `[265..297)`. -/ fUname : ByteArray
  /-- Group name field `[297..329)`. -/ fGname : ByteArray
  /-- Device major/minor padding `[329..345)`. -/ fDev : ByteArray
  /-- Path prefix field `[345..500)`. -/ fPrefix : ByteArray
  /-- Trailing 12-byte padding `[500..512)`. -/ fPad : ByteArray

/-- Size invariants ensuring `RawUstarHeader.toBytes` is an exact 512-byte USTAR layout. -/
structure RawUstarHeader.WellSized (h : RawUstarHeader) : Prop where
  /-- `fName` has size 100. -/ szName : h.fName.size = 100
  /-- `fMode` has size 8. -/ szMode : h.fMode.size = 8
  /-- `fUid` has size 8. -/ szUid : h.fUid.size = 8
  /-- `fGid` has size 8. -/ szGid : h.fGid.size = 8
  /-- `fSize` has size 12. -/ szSize : h.fSize.size = 12
  /-- `fMtime` has size 12. -/ szMtime : h.fMtime.size = 12
  /-- `fChk` has size 8. -/ szChk : h.fChk.size = 8
  /-- `fLink` has size 100. -/ szLink : h.fLink.size = 100
  /-- `fMagic` has size 6. -/ szMagic : h.fMagic.size = 6
  /-- `fVer` has size 2. -/ szVer : h.fVer.size = 2
  /-- `fUname` has size 32. -/ szUname : h.fUname.size = 32
  /-- `fGname` has size 32. -/ szGname : h.fGname.size = 32
  /-- `fDev` has size 16. -/ szDev : h.fDev.size = 16
  /-- `fPrefix` has size 155. -/ szPrefix : h.fPrefix.size = 155
  /-- `fPad` has size 12. -/ szPad : h.fPad.size = 12

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
    {chk : ByteArray} (hchk : chk.size = 8) : (h.withChk chk).WellSized :=
  { hw with szChk := hchk }

/-- Size of `(h.toBytes)` is `512` when `h.WellSized`. -/
theorem RawUstarHeader.toBytes_size {h : RawUstarHeader} (hw : h.WellSized) :
    h.toBytes.size = 512 := by
  unfold RawUstarHeader.toBytes
  simp only [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize,
    hw.szMtime, hw.szChk, show (ByteArray.mk #[h.fType]).size = 1 from rfl,
    hw.szLink, hw.szMagic, hw.szVer, hw.szUname, hw.szGname, hw.szDev, hw.szPrefix, hw.szPad]

/-- Construct a `RawUstarHeader` from symbolic USTAR field values and a checksum field. -/
def RawUstarHeader.ofFields (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) (chkField : ByteArray) : RawUstarHeader :=
  { fName := padRightBytes 100 name.toUTF8, fMode := encodeOctalField (mode &&& 0o7777).toNat 7
  , fUid := encodeOctalField uid 7, fGid := encodeOctalField gid 7
  , fSize := encodeOctalField size 11, fMtime := encodeOctalField mtime 11
  , fChk := chkField, fType := typeflag, fLink := padRightBytes 100 linkname.toUTF8
  , fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00], fVer := ByteArray.mk #[0x30, 0x30]
  , fUname := padRightBytes 32 uname.toUTF8, fGname := padRightBytes 32 gname.toUTF8
  , fDev := ByteArray.mk (Array.replicate 16 0), fPrefix := padRightBytes 155 pfx.toUTF8
  , fPad := ByteArray.mk (Array.replicate 12 0) }

/-- `RawUstarHeader.ofFields` is `WellSized` whenever `chkField.size = 8`. -/
theorem RawUstarHeader.ofFields_wellSized {name : String} {mode : UInt32} {uid gid size mtime : Nat}
    {typeflag : UInt8} {linkname uname gname pfx : String} {chkField : ByteArray} (hchk : chkField.size = 8) :
    (RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx chkField).WellSized :=
  { szName := padRightBytes_size 100 _, szMode := encodeOctalField_size _ 7, szUid := encodeOctalField_size _ 7
  , szGid := encodeOctalField_size _ 7, szSize := encodeOctalField_size _ 11, szMtime := encodeOctalField_size _ 11
  , szChk := hchk, szLink := padRightBytes_size 100 _, szMagic := rfl, szVer := rfl
  , szUname := padRightBytes_size 32 _, szGname := padRightBytes_size 32 _, szDev := rfl
  , szPrefix := padRightBytes_size 155 _, szPad := rfl }

/-- All-zero `RawUstarHeader` corresponding to `zeroBlock`. -/
def RawUstarHeader.zeros : RawUstarHeader :=
  { fName := ByteArray.mk (Array.replicate 100 0), fMode := ByteArray.mk (Array.replicate 8 0)
  , fUid := ByteArray.mk (Array.replicate 8 0), fGid := ByteArray.mk (Array.replicate 8 0)
  , fSize := ByteArray.mk (Array.replicate 12 0), fMtime := ByteArray.mk (Array.replicate 12 0)
  , fChk := ByteArray.mk (Array.replicate 8 0), fType := 0, fLink := ByteArray.mk (Array.replicate 100 0)
  , fMagic := ByteArray.mk (Array.replicate 6 0), fVer := ByteArray.mk (Array.replicate 2 0)
  , fUname := ByteArray.mk (Array.replicate 32 0), fGname := ByteArray.mk (Array.replicate 32 0)
  , fDev := ByteArray.mk (Array.replicate 16 0), fPrefix := ByteArray.mk (Array.replicate 155 0)
  , fPad := ByteArray.mk (Array.replicate 12 0) }

/-- `RawUstarHeader.zeros` is `WellSized`. -/
theorem RawUstarHeader.zeros_wellSized : RawUstarHeader.zeros.WellSized :=
  { szName := rfl, szMode := rfl, szUid := rfl, szGid := rfl, szSize := rfl, szMtime := rfl, szChk := rfl
  , szLink := rfl, szMagic := rfl, szVer := rfl, szUname := rfl, szGname := rfl, szDev := rfl, szPrefix := rfl, szPad := rfl }

private theorem encodeOctalField_6_sp_size (chk : Nat) :
    (encodeOctalField chk 6 ++ ByteArray.mk #[0x20]).size = 8 := by
  rw [ByteArray.size_append, encodeOctalField_size]; rfl

/-- `buildUstarHeader` equals `(RawUstarHeader.ofFields ... chkField).toBytes`. -/
theorem buildUstarHeader_eq_raw (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    let hdrPre := (RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
      (ByteArray.mk (Array.replicate 8 0x20))).toBytes
    let chkField := encodeOctalField (ustarChecksumAt hdrPre 0) 6 ++ ByteArray.mk #[0x20]
    buildUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx =
      (RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx chkField).toBytes :=
  rfl

private theorem replicate_zero_append (a b : Nat) :
    ByteArray.mk (Array.replicate a 0) ++ ByteArray.mk (Array.replicate b 0) =
      ByteArray.mk (Array.replicate (a + b) 0) := by
  have ha : (ByteArray.mk (Array.replicate a 0)).size = a := Array.size_replicate
  have hb : (ByteArray.mk (Array.replicate b 0)).size = b := Array.size_replicate
  have hab : (ByteArray.mk (Array.replicate (a + b) 0)).size = a + b := Array.size_replicate
  apply ByteArray.ext_getElem (by rw [ByteArray.size_append, ha, hb, hab])
  intro i hi1 hi2
  rw [byteArray_getElem_append hi1]
  change (if h : i < _ then _ else _) = (Array.replicate (a + b) (0 : UInt8))[i]'hi2
  rw [Array.getElem_replicate]
  split <;> exact Array.getElem_replicate ..

/-- `zeroBlock` equals `RawUstarHeader.zeros.toBytes`. -/
theorem zeroBlock_eq_raw : zeroBlock = RawUstarHeader.zeros.toBytes := by
  unfold RawUstarHeader.zeros RawUstarHeader.toBytes
  dsimp only
  rw [show ByteArray.mk #[0] = ByteArray.mk (Array.replicate 1 0) from rfl]
  simp only [replicate_zero_append]
  rfl

/-- Overwrite a contiguous middle slice `M` inside `L ++ (M ++ R)` with `blitFixed M 0 w src`. -/
theorem blitFixed_append_mid (L M R src : ByteArray) {off w : Nat}
    (hL : L.size = off) (hM : M.size = w) :
    blitFixed (L ++ (M ++ R)) off w src = L ++ (blitFixed M 0 w src ++ R) := by
  subst hL hM
  have hbd1 : L.size + min M.size src.size ≤ (L ++ (M ++ R)).size := by simp [ByteArray.size_append]; omega
  have hbd2 : 0 + min M.size src.size ≤ M.size := by omega
  apply ByteArray.ext_getElem (by simp [ByteArray.size_append])
  intro i hi1 _
  rw [blitFixed_getElem hbd1 (by simpa using hi1)]
  rcases Nat.lt_or_ge i L.size with hlt | hge
  · rw [dite_eq_right (by omega), ByteArray.getElem_append_left hlt, ByteArray.getElem_append_left hlt]
  · rw [ByteArray.getElem_append_right hge, ByteArray.getElem_append_right hge]
    rcases Nat.lt_or_ge (i - L.size) M.size with hmid | hright
    · rw [ByteArray.getElem_append_left hmid, ByteArray.getElem_append_left (by rw [blitFixed_size]; exact hmid),
        blitFixed_getElem hbd2 hmid]
      by_cases hc : L.size ≤ i ∧ i < L.size + min M.size src.size
      · rw [dite_eq_left hc, dite_eq_left (by omega)]; congr 1
      · rw [dite_eq_right hc, dite_eq_right (by omega)]
    · rw [dite_eq_right (by omega), ByteArray.getElem_append_right hright,
        ByteArray.getElem_append_right (by rw [blitFixed_size]; exact hright)]
      congr 1; simp

/-- `blitFixed M 0 w src = src` when `M.size = w` and `src.size = w`. -/
theorem blitFixed_exact {M src : ByteArray} {w : Nat} (hM : M.size = w) (hsrc : src.size = w) :
    blitFixed M 0 w src = src := by
  subst hM
  simpa [ByteArray.empty_append, ByteArray.append_empty] using
    blitFixed_mid_exact ByteArray.empty M ByteArray.empty src hsrc.symm

/-- `set!` inside the middle slice `M` of `L ++ (M ++ R)` updates `M` cleanly. -/
theorem set!_append_mid (L M R : ByteArray) (k : Nat) (v : UInt8) (hk : k < M.size) :
    (L ++ (M ++ R)).set! (L.size + k) v = L ++ (M.set! k v ++ R) := by
  have htot : L.size + k < (L ++ (M ++ R)).size := by simp [ByteArray.size_append]; omega
  apply ByteArray.ext_getElem (by simp [ByteArray.size_append])
  intro i hi1 _
  have hi_tot : i < (L ++ (M ++ R)).size := by simpa using hi1
  rw [byteArray_getElem_set! htot hi_tot]
  rcases Nat.lt_or_ge i L.size with hlt | hge
  · rw [ite_eq_right (by omega), ByteArray.getElem_append_left hlt, ByteArray.getElem_append_left hlt]
  · rw [ByteArray.getElem_append_right hge, ByteArray.getElem_append_right hge]
    rcases Nat.lt_or_ge (i - L.size) M.size with hm_lt | hm_ge
    · rw [ByteArray.getElem_append_left hm_lt, ByteArray.getElem_append_left (by rw [byteArray_size_set!]; exact hm_lt),
        byteArray_getElem_set! hk hm_lt]
      by_cases hik : k = i - L.size
      · rw [ite_eq_left (by omega), ite_eq_left hik]
      · rw [ite_eq_right (by omega), ite_eq_right hik]
    · rw [ite_eq_right (by omega), ByteArray.getElem_append_right hm_ge,
        ByteArray.getElem_append_right (by rw [byteArray_size_set!]; exact hm_ge)]
      congr 1; simp

local macro "split_raw_eq" : tactic =>
  `(tactic| (unfold RawUstarHeader.toBytes; simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.append_assoc]))

private theorem blitFixed_mid_zeros_at {L R src : ByteArray} {off w : Nat} (hL : L.size = off) :
    blitFixed (L ++ ByteArray.mk (Array.replicate w 0) ++ R) off w src = L ++ padRightBytes w src ++ R :=
  hL ▸ blitFixed_mid_zeros L R src w

private theorem blitFixed_mid_exact_at {L M R src : ByteArray} {off w : Nat}
    (hL : L.size = off) (hM : M.size = w) (hS : src.size = w) :
    blitFixed (L ++ M ++ R) off w src = L ++ src ++ R := by
  subst hL hM; exact blitFixed_mid_exact L M R src hS.symm

/-- Blit `src` into `fUid` of `h.toBytes` when `src.size = 8`. -/
theorem blitFixed_raw_uid {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 8) :
    blitFixed h.toBytes 108 8 src = ({ h with fUid := src }).toBytes := by
  have hs : h.toBytes = (h.fName ++ h.fMode) ++ h.fUid ++ (h.fGid ++ h.fSize ++ h.fMtime ++
      h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad) := by split_raw_eq
  rw [hs, blitFixed_mid_exact_at (by simp [ByteArray.size_append, hw.szName, hw.szMode]) hw.szUid hsrc]; split_raw_eq

/-- Blit `src` into `fSize` of `h.toBytes` when `src.size = 12`. -/
theorem blitFixed_raw_size {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 12) :
    blitFixed h.toBytes 124 12 src = ({ h with fSize := src }).toBytes := by
  have hs : h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid) ++ h.fSize ++ (h.fMtime ++
      h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad) := by split_raw_eq
  rw [hs, blitFixed_mid_exact_at (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid]) hw.szSize hsrc]; split_raw_eq

/-- Set `fType` byte at offset `156` in `h.toBytes`. -/
theorem set!_raw_type {h : RawUstarHeader} (hw : h.WellSized) (v : UInt8) :
    h.toBytes.set! 156 v = ({ h with fType := v }).toBytes := by
  have hs : h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk) ++
      (ByteArray.mk #[h.fType] ++ (h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by split_raw_eq
  have h156 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk).size + 0 = 156 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk]
  rw [hs, ← h156, set!_append_mid _ (ByteArray.mk #[h.fType]) _ 0 v (by simp [ByteArray.size])]
  split_raw_eq; rfl

/-- Set a byte inside `fChk` at offset `148 + k` (`k < 8`) in `h.toBytes`. -/
theorem set!_raw_chk {h : RawUstarHeader} (hw : h.WellSized) {k : Nat} (hk : k < 8) (v : UInt8) :
    h.toBytes.set! (148 + k) v = ({ h with fChk := h.fChk.set! k v }).toBytes := by
  have hs : h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) ++
      (h.fChk ++ (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by split_raw_eq
  have h148 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime).size = 148 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  rw [hs, ← h148, set!_append_mid _ h.fChk _ k v (by rw [hw.szChk]; exact hk)]; split_raw_eq

/-- Blit `src` into `fMagic` of `h.toBytes` when `src.size = 6`. -/
theorem blitFixed_raw_magic {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 6) :
    blitFixed h.toBytes 257 6 src = ({ h with fMagic := src }).toBytes := by
  have hs : h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink) ++
      h.fMagic ++ (h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad) := by split_raw_eq
  rw [hs, blitFixed_mid_exact_at
    (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk,
      show (ByteArray.mk #[h.fType]).size = 1 from rfl, hw.szLink]) hw.szMagic hsrc]; split_raw_eq

/-- `patchHeaderChecksum` on `h.toBytes` updates `fChk` to the encoded checksum of `h.toBytes`. -/
theorem patchHeaderChecksum_raw {h : RawUstarHeader} (hw : h.WellSized) :
    patchHeaderChecksum h.toBytes =
      (h.withChk (encodeOctalField (ustarChecksum h.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
  unfold patchHeaderChecksum RawUstarHeader.withChk; dsimp only
  generalize hc : encodeOctalField (ustarChecksum h.toBytes) 6 ++ ByteArray.mk #[0x20] = chkF
  have hchk_sz : chkF.size = 8 := hc ▸ encodeOctalField_6_sp_size _
  have hs : h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) ++ h.fChk ++
      (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad) := by split_raw_eq
  have h148 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime).size = 148 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  rw [hs, ← h148, ← hw.szChk, blitFixed_mid_exact _ _ _ _ (hw.szChk.trans hchk_sz.symm)]
  split_raw_eq

/-- `bytes[offset + i]` agrees outside `[148..156)` whenever `bytes.extract offset (offset + 512) = (h.withChk c).toBytes`. -/
theorem raw_withChk_outside_eq {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader}
    {c1 c2 : ByteArray} (hw : h.WellSized) (hc1 : c1.size = 8) (hc2 : c2.size = 8)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = (h.withChk c1).toBytes)
    {i : Nat} (hi : i < 512) (hnot : ¬(148 ≤ i ∧ i < 156)) :
    bytes[offset + i]'(by omega) = (h.withChk c2).toBytes[i]'(by
      rw [RawUstarHeader.toBytes_size (h.withChk_wellSized hw hc2)]; exact hi) := by
  have hi_e : i < (bytes.extract offset (offset + 512)).size := by rw [ByteArray.size_extract]; omega
  have hw1 := h.withChk_wellSized hw hc1
  have hw2 := h.withChk_wellSized hw hc2
  have hi1 : i < (h.withChk c1).toBytes.size := by rw [RawUstarHeader.toBytes_size hw1]; exact hi
  have hi2 : i < (h.withChk c2).toBytes.size := by rw [RawUstarHeader.toBytes_size hw2]; exact hi
  rw [← ByteArray.getElem_extract hi_e, byteArray_getElem_of_eq hext hi_e hi1]
  have hs1 : (h.withChk c1).toBytes =
      (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) ++
      (c1 ++ (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
    dsimp only [RawUstarHeader.withChk]; split_raw_eq
  have hs2 : (h.withChk c2).toBytes =
      (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) ++
      (c2 ++ (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
    dsimp only [RawUstarHeader.withChk]; split_raw_eq
  have hL : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime).size = 148 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  have hR : (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad).size = 356 := by
    simp [ByteArray.size_append, show (ByteArray.mk #[h.fType]).size = 1 from rfl,
      hw.szLink, hw.szMagic, hw.szVer, hw.szUname, hw.szGname, hw.szDev, hw.szPrefix, hw.szPad]
  generalize (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) = L at hs1 hs2 hL
  generalize (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad) = R at hs1 hs2 hR
  rw [byteArray_getElem_of_eq hs1 hi1 (by rw [← hs1]; exact hi1),
    byteArray_getElem_of_eq hs2 hi2 (by rw [← hs2]; exact hi2)]
  rcases Nat.lt_or_ge i L.size with hlt | hge
  · rw [ByteArray.getElem_append_left hlt, ByteArray.getElem_append_left hlt]
  · rw [ByteArray.getElem_append_right hge, ByteArray.getElem_append_right hge,
      ByteArray.getElem_append_right (by omega), ByteArray.getElem_append_right (by omega)]
    congr 1; omega

/-- `ustarChecksumAt` on a slice equal to `(h.withChk chk).toBytes` depends only on `h` outside `fChk`. -/
theorem raw_ustarChecksumAt_eq {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader}
    {c1 c2 : ByteArray} (hw : h.WellSized) (hc1 : c1.size = 8) (hc2 : c2.size = 8)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = (h.withChk c1).toBytes) :
    ustarChecksumAt bytes offset = ustarChecksum (h.withChk c2).toBytes :=
  ustarChecksumAt_eq_ustarChecksum hbd
    (by rw [RawUstarHeader.toBytes_size (h.withChk_wellSized hw hc2)]; exact Nat.le_refl _)
    fun _ hi hnot => raw_withChk_outside_eq hw hc1 hc2 hbd hext hi hnot

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
  have ht : (ByteArray.mk #[h.fType]).size = 1 := rfl
  let t15 := h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t14 := h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t13 := h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t12 := h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t11 := h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t10 := h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t8 := h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t7 := h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t6 := h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t5 := h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  let t4 := h.fDev ++ h.fPrefix ++ h.fPad
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_zero] using byteArray_extract_sub (L := ByteArray.empty) (M := h.fName) (R := t15) (a := 0) (w := 100) (hext.trans (by dsimp only [t15]; split_raw_eq)) rfl hw.szName (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName) (M := h.fMode) (R := t14) (hext.trans (by dsimp only [t14]; split_raw_eq)) hw.szName hw.szMode (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode) (M := h.fUid) (R := t13) (hext.trans (by dsimp only [t13]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode]) hw.szUid (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid) (M := h.fGid) (R := t12) (hext.trans (by dsimp only [t12]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid]) hw.szGid (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid) (M := h.fSize) (R := t11) (hext.trans (by dsimp only [t11]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid]) hw.szSize (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize) (M := h.fMtime) (R := t10) (hext.trans (by dsimp only [t10]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize]) hw.szMtime (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) (M := h.fChk) (R := ByteArray.mk #[h.fType] ++ h.fLink ++ t8) (hext.trans (by dsimp only [t8]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]) hw.szChk (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType]) (M := h.fLink) (R := t8) (hext.trans (by dsimp only [t8]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, ht]) hw.szLink (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink) (M := h.fMagic) (R := t7) (hext.trans (by dsimp only [t7]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, ht, hw.szLink]) hw.szMagic (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic) (M := h.fVer) (R := t6) (hext.trans (by dsimp only [t6]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, ht, hw.szLink, hw.szMagic]) hw.szVer (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer) (M := h.fUname) (R := t5) (hext.trans (by dsimp only [t5]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, ht, hw.szLink, hw.szMagic, hw.szVer]) hw.szUname (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname) (M := h.fGname) (R := t4) (hext.trans (by dsimp only [t4]; split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, ht, hw.szLink, hw.szMagic, hw.szVer, hw.szUname]) hw.szGname (by omega)
  · simpa only [Nat.add_assoc] using byteArray_extract_sub (L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev) (M := h.fPrefix) (R := h.fPad) (hext.trans (by split_raw_eq)) (by simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk, ht, hw.szLink, hw.szMagic, hw.szVer, hw.szUname, hw.szGname, hw.szDev]) hw.szPrefix (by omega)

/-- Read `fType` byte at `offset + 156` when `bytes.extract offset (offset + 512) = h.toBytes`. -/
theorem raw_getElem_type {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader} (hw : h.WellSized)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = h.toBytes) :
    bytes[offset + 156]'(by omega) = h.fType := by
  have hi_e : 156 < (bytes.extract offset (offset + 512)).size := by rw [ByteArray.size_extract]; omega
  have hi_h : 156 < h.toBytes.size := by rw [RawUstarHeader.toBytes_size hw]; omega
  rw [← ByteArray.getElem_extract hi_e, byteArray_getElem_of_eq hext hi_e hi_h]
  let L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk
  have hL : L.size = 156 := by simp [L, ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk]
  have hs : h.toBytes = L ++ (ByteArray.mk #[h.fType] ++ (h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad)) := by
    dsimp only [L]; split_raw_eq
  rw [byteArray_getElem_of_eq hs hi_h (by rw [← hs]; exact hi_h), ByteArray.getElem_append_right (by omega)]
  simp only [show 156 - L.size = 0 by omega]
  rw [ByteArray.getElem_append_left (by simp [ByteArray.size])]
  rfl

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
      { mode := (mode &&& 0o7777).toNat, uid := uid, gid := gid
      , size := size, mtime := mtime, typeflag := typeflag } := by
  let h0 := RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
    (ByteArray.mk (Array.replicate 8 0x20))
  let chk := ustarChecksumAt h0.toBytes 0
  let chkField := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  let h := h0.withChk chkField
  have hw0 : h0.WellSized := RawUstarHeader.ofFields_wellSized rfl
  have hw : h.WellSized := h0.withChk_wellSized hw0 (encodeOctalField_6_sp_size chk)
  have hext' : bytes.extract offset (offset + 512) = h.toBytes :=
    hext.trans (buildUstarHeader_eq_raw name mode uid gid size mtime typeflag linkname uname gname pfx)
  have hchk_eq : ustarChecksumAt bytes offset = chk := by
    have h1 := raw_ustarChecksumAt_eq (c1 := chkField) (c2 := ByteArray.mk (Array.replicate 8 0x20))
      hw0 (encodeOctalField_6_sp_size chk) rfl hbd hext'
    simpa [show h0.withChk (ByteArray.mk (Array.replicate 8 0x20)) = h0 from rfl, ustarChecksum_eq_ustarChecksumAt] using h1
  have ⟨_, hext_mode, hext_uid, hext_gid, hext_size, hext_mtime, hext_chk, _,
      hext_magic, hext_ver, _, _, _⟩ := raw_extract_fields hw hext'
  have hparse_chk : parseChecksumOctal bytes (offset + 148) (offset + 156) offset = .ok chk := by
    rw [show offset + 156 = offset + 148 + 8 by omega]
    exact parseChecksumOctal_encodeOctalField (ustarChecksumAt_lt h0.toBytes 0)
      (by rw [← (by omega : offset + 156 = offset + 148 + 8), hext_chk]; rfl)
  have hmagic : hasValidMagic bytes offset = true := by
    unfold hasValidMagic; rw [hext_magic, hext_ver]; rfl
  have hmode_lt : (mode &&& 0o7777).toNat < 4096 := by
    change mode.toNat &&& 0o7777 < 2 ^ 12; exact Nat.and_lt_two_pow mode.toNat (by decide)
  have hu32 : u32Limit = 2 ^ 32 := rfl; have hu64 : u64Limit = 2 ^ 64 := rfl
  have ho7 : ustarOctal7Limit = 8 ^ 7 := rfl; have ho11 : ustarOctal11Limit = 8 ^ 11 := rfl
  have hnum {s d val lim : Nat} {al : Bool} {fn : String} (hd : 1 ≤ d) (hv : val < 8 ^ d) (hl : val < lim)
      (he : bytes.extract (offset + s) (offset + (s + d + 1)) = encodeOctalField val d) :
      parseUstarNumeric bytes (offset + s) (offset + (s + d + 1)) offset al lim fn = .ok val := by
    rw [show offset + (s + d + 1) = offset + s + (d + 1) by omega] at he ⊢
    exact parseUstarNumeric_encodeOctalField hd hv hl he
  have hparse_mode := hnum (s := 100) (d := 7) (al := false) (lim := u32Limit) (fn := "mode") (by omega) (by omega) (by omega) hext_mode
  have hparse_uid := hnum (s := 108) (d := 7) (al := true) (lim := u64Limit) (fn := "uid") (by omega) (by omega) (by omega) hext_uid
  have hparse_gid := hnum (s := 116) (d := 7) (al := true) (lim := u64Limit) (fn := "gid") (by omega) (by omega) (by omega) hext_gid
  have hparse_size := hnum (s := 124) (d := 11) (al := false) (lim := u64Limit) (fn := "size") (by omega) (by omega) (by omega) hext_size
  have hparse_mtime := hnum (s := 136) (d := 11) (al := true) (lim := u64Limit) (fn := "mtime") (by omega) (by omega) (by omega) hext_mtime
  unfold parseUstarHeader
  simp only [hparse_chk, hchk_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    hmagic, Bool.not_true, hparse_mode, hparse_uid, hparse_gid, hparse_size, hparse_mtime,
    show offset + 156 < bytes.size by omega, ↓reduceDIte, raw_getElem_type hw hbd hext',
    bind, Except.bind, pure, Except.pure]; rfl

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
  have hw := h0.withChk_wellSized (RawUstarHeader.ofFields_wellSized rfl)
    (encodeOctalField_6_sp_size (ustarChecksumAt h0.toBytes 0))
  have ⟨hn, _, _, _, _, _, _, hl, _, _, hu, hg, hp⟩ := raw_extract_fields hw
    (hext.trans (buildUstarHeader_eq_raw name mode uid gid size mtime typeflag linkname uname gname pfx))
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
  have hw := h0.withChk_wellSized (RawUstarHeader.ofFields_wellSized rfl)
    (encodeOctalField_6_sp_size (ustarChecksumAt h0.toBytes 0))
  have hext_magic : bytes.extract (offset + 257) (offset + 263) =
      ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00] :=
    (raw_extract_fields hw (hext.trans
      (buildUstarHeader_eq_raw name mode uid gid size mtime typeflag linkname uname gname pfx))).2.2.2.2.2.2.2.2.1.trans rfl
  have h257_e : 0 < (bytes.extract (offset + 257) (offset + 263)).size := by rw [hext_magic]; decide
  have hb257 : bytes[offset + 257]'(by omega) = 0x75 := by
    have hg := ByteArray.getElem_extract h257_e
    rw [byteArray_getElem_of_eq hext_magic h257_e (by decide)] at hg
    exact (by simpa using hg.symm : _ = (ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00])[0]'(by decide))
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
  let hSp := RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx
    (ByteArray.mk (Array.replicate 8 0x20))
  let h0 := hSp.withChk (ByteArray.mk (Array.replicate 8 0))
  have hwSp : hSp.WellSized := RawUstarHeader.ofFields_wellSized rfl
  have hc0 : (ByteArray.mk (Array.replicate 8 0)).size = 8 := rfl
  have hw0 : h0.WellSized := hSp.withChk_wellSized hwSp hc0
  have hpre :
      blitFixed (blitFixed (blitFixed (blitFixed (blitFixed (blitFixed ((blitFixed (blitFixed (blitFixed
        (blitFixed (blitFixed (blitFixed zeroBlock 0 100 name.toUTF8) 100 8 (encodeOctalField (mode &&& 0o7777).toNat 7))
        108 8 (encodeOctalField uid 7)) 116 8 (encodeOctalField gid 7)) 124 12 (encodeOctalField size 11))
        136 12 (encodeOctalField mtime 11)).set! 156 typeflag) 157 100 linkname.toUTF8)
        257 6 "ustar\x00".toUTF8) 263 2 "00".toUTF8) 265 32 uname.toUTF8) 297 32 gname.toUTF8) 345 155 pfx.toUTF8 = h0.toBytes := by
    have h0_eq : zeroBlock = ByteArray.empty ++ ByteArray.mk (Array.replicate 100 0) ++
        (ByteArray.mk (Array.replicate 8 0) ++ (ByteArray.mk (Array.replicate 8 0) ++ (ByteArray.mk (Array.replicate 8 0) ++
         (ByteArray.mk (Array.replicate 12 0) ++ (ByteArray.mk (Array.replicate 12 0) ++ (ByteArray.mk (Array.replicate 8 0) ++
         (ByteArray.mk #[0] ++ (ByteArray.mk (Array.replicate 100 0) ++ (ByteArray.mk (Array.replicate 6 0) ++
         (ByteArray.mk (Array.replicate 2 0) ++ (ByteArray.mk (Array.replicate 32 0) ++ (ByteArray.mk (Array.replicate 32 0) ++
         (ByteArray.mk (Array.replicate 16 0) ++ (ByteArray.mk (Array.replicate 155 0) ++ ByteArray.mk (Array.replicate 12 0))))))))))))))) := by
      rw [zeroBlock_eq_raw]; unfold RawUstarHeader.zeros RawUstarHeader.toBytes
      simp only [ByteArray.empty_append, ByteArray.append_assoc]
    have hsz : ∀ (w : Nat), (ByteArray.mk (Array.replicate w 0)).size = w := fun _ => Array.size_replicate
    have ht : (ByteArray.mk #[typeflag]).size = 1 := rfl
    have hset0 : (ByteArray.mk #[0]).set! 0 typeflag = ByteArray.mk #[typeflag] := rfl
    have hm : "ustar\x00".utf8ByteSize = 6 := rfl; have hv : "00".utf8ByteSize = 2 := rfl
    have hme : ∀ {L M R src : ByteArray} {off w : Nat}, L.size = off → M.size = w → src.size = w →
        blitFixed (L ++ (M ++ R)) off w src = (L ++ src) ++ R := fun hL hM hS => by
      rw [← ByteArray.append_assoc]; exact blitFixed_mid_exact_at hL hM hS
    have hmz : ∀ {L R src : ByteArray} {off w : Nat}, L.size = off →
        blitFixed (L ++ (ByteArray.mk (Array.replicate w 0) ++ R)) off w src = (L ++ padRightBytes w src) ++ R := fun hL => by
      rw [← ByteArray.append_assoc]; exact blitFixed_mid_zeros_at hL
    have hs156 : ∀ {L R : ByteArray}, L.size = 156 →
        (L ++ (ByteArray.mk #[0] ++ R)).set! 156 typeflag = (L ++ ByteArray.mk #[typeflag]) ++ R := fun {L R} hL => by
      rw [← (by omega : L.size + 0 = 156), set!_append_mid _ _ _ 0 typeflag (by decide), hset0, ByteArray.append_assoc]
    rw [h0_eq, blitFixed_mid_zeros_at (show ByteArray.empty.size = 0 from rfl), ByteArray.empty_append,
      hme (padRightBytes_size 100 _) (hsz 8) (encodeOctalField_size _ 7),
      hme (by simp [ByteArray.size_append]) (hsz 8) (encodeOctalField_size _ 7),
      hme (by simp [ByteArray.size_append]) (hsz 8) (encodeOctalField_size _ 7),
      hme (by simp [ByteArray.size_append]) (hsz 12) (encodeOctalField_size _ 11),
      hme (by simp [ByteArray.size_append]) (hsz 12) (encodeOctalField_size _ 11),
      ← ByteArray.append_assoc,
      hs156 (by simp [ByteArray.size_append, hsz]),
      hmz (by simp [ByteArray.size_append, hsz, ht]),
      hme (by simp [ByteArray.size_append, hsz, ht]) (hsz 6) rfl,
      hme (by simp [ByteArray.size_append, hsz, ht, hm]) (hsz 2) rfl,
      hmz (by simp [ByteArray.size_append, hsz, ht, hm, hv]),
      hmz (by simp [ByteArray.size_append, hsz, ht, hm, hv]),
      ← ByteArray.append_assoc,
      hmz (by simp [ByteArray.size_append, hsz, ht, hm, hv])]
    unfold h0 hSp RawUstarHeader.withChk RawUstarHeader.ofFields RawUstarHeader.toBytes
    simp only [ByteArray.append_assoc]; rfl
  unfold mkUstarHeader; dsimp only; rw [hpre]
  change patchHeaderChecksum h0.toBytes = _
  rw [patchHeaderChecksum_raw hw0, buildUstarHeader_eq_raw]
  have hchk_eq : ustarChecksum h0.toBytes = ustarChecksumAt hSp.toBytes 0 := by
    have hsz : h0.toBytes.size = 512 := RawUstarHeader.toBytes_size hw0
    have h1 := raw_ustarChecksumAt_eq (bytes := h0.toBytes) (offset := 0) (h := hSp)
      (c1 := ByteArray.mk (Array.replicate 8 0)) (c2 := ByteArray.mk (Array.replicate 8 0x20))
      hwSp hc0 rfl (by omega) (by rw [Nat.zero_add, ← hsz, ByteArray.extract_zero_size])
    have hSp_id : hSp.withChk (ByteArray.mk (Array.replicate 8 0x20)) = hSp := rfl
    rw [ustarChecksum_eq_ustarChecksumAt, h1, hSp_id, ustarChecksum_eq_ustarChecksumAt]
  have hwith_idem (c1 c2 : ByteArray) : (hSp.withChk c1).withChk c2 =
      RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx c2 := rfl
  rw [hchk_eq, hwith_idem]

/-- Size of `mkUstarHeader ...` is `512`. -/
theorem mkUstarHeader_size (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    (mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx).size = 512 := by
  rw [mkUstarHeader_eq_buildUstarHeader]; exact buildUstarHeader_size ..

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
      { mode := (mode &&& 0o7777).toNat, uid := uid, gid := gid
      , size := size, mtime := mtime, typeflag := typeflag } :=
  parseUstarHeader_buildUstarHeader huid hgid hsize hmtime hbd
    (hext.trans (mkUstarHeader_eq_buildUstarHeader ..))

/-- Extracting a suffix starting at `a.size` from `a ++ b` slices `b` from `0`. -/
theorem extract_append_right (a b : ByteArray) (k : Nat) :
    (a ++ b).extract a.size (a.size + k) = b.extract 0 k :=
  byteArray_extract_append_right a b k

/-- Extracting the exact middle factor from `a ++ b ++ c`. -/
theorem extract_append_mid (a b c : ByteArray) :
    (a ++ b ++ c).extract a.size (a.size + b.size) = b :=
  byteArray_extract_mid a b c

private theorem unpackLoopFuel_indep (n fuel1 fuel2 : Nat)
    (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat)
    (hrem : bytes.size - offset ≤ n) (hf1 : n + 1 ≤ fuel1) (hf2 : n + 1 ≤ fuel2) :
    unpackLoopFuel fuel1 opts bytes offset pendingPax seen acc totalBytes =
      unpackLoopFuel fuel2 opts bytes offset pendingPax seen acc totalBytes := by
  induction n generalizing fuel1 fuel2 offset pendingPax seen acc totalBytes with
  | zero =>
    obtain ⟨f1, rfl⟩ : ∃ f1, fuel1 = f1 + 1 := ⟨fuel1 - 1, by omega⟩
    obtain ⟨f2, rfl⟩ : ∃ f2, fuel2 = f2 + 1 := ⟨fuel2 - 1, by omega⟩
    simp [unpackLoopFuel.eq_2, show offset ≥ bytes.size by omega]
  | succ n ih =>
    obtain ⟨f1, rfl⟩ : ∃ f1, fuel1 = f1 + 1 := ⟨fuel1 - 1, by omega⟩
    obtain ⟨f2, rfl⟩ : ∃ f2, fuel2 = f2 + 1 := ⟨fuel2 - 1, by omega⟩
    simp only [unpackLoopFuel.eq_2]
    by_cases hge : offset ≥ bytes.size
    · simp [hge]
    · simp only [hge, ↓reduceIte]
      cases unpackStep opts bytes offset pendingPax seen acc totalBytes with
      | error _ => rfl
      | ok s =>
        cases s with
        | done _ => rfl
        | cont nextOff nextPax nextSeen nextAcc nextTotal =>
          dsimp only; split
          · exact ih f1 f2 nextOff nextPax nextSeen nextAcc nextTotal (by omega) (by omega) (by omega)
          · rfl

/-- If `offset ≥ bytes.size`, `unpackLoop` returns `truncatedArchive`. -/
theorem unpackLoop_at_ge (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hge : offset ≥ bytes.size) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes =
      .error { kind := .truncatedArchive, message := "tar archive missing end-of-archive zero blocks", offset := some offset } := by
  simp [unpackLoop, show bytes.size - offset = 0 by omega, unpackLoopFuel.eq_2, hge]

/-- If `unpackStep` completes with `.done res`, `unpackLoop` returns `.ok res`. -/
theorem unpackLoop_step_done (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (res : List TarEntry) (hoff : offset < bytes.size)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes = .ok (.done res)) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes = .ok res := by
  simp [unpackLoop, unpackLoopFuel.eq_2, show ¬(offset ≥ bytes.size) by omega, hstep]

/-- If `unpackStep` errors, `unpackLoop` returns that error. -/
theorem unpackLoop_step_err (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (err : TarError) (hoff : offset < bytes.size)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes = .error err) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes = .error err := by
  simp [unpackLoop, unpackLoopFuel.eq_2, show ¬(offset ≥ bytes.size) by omega, hstep]

/-- If `unpackStep` advances strictly, `unpackLoop` reduces to `unpackLoop` at `nextOff`. -/
theorem unpackLoop_step_continue (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (nextOff : Nat) (nextPax : Option PaxOverrides) (nextSeen : List String) (nextAcc : List TarEntry)
    (nextTotal : Nat) (hoff : offset < bytes.size)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes =
      .ok (.cont nextOff nextPax nextSeen nextAcc nextTotal)) (hadv : nextOff > offset) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes =
      unpackLoop opts bytes nextOff nextPax nextSeen nextAcc nextTotal := by
  have heq : unpackLoop opts bytes offset pendingPax seen acc totalBytes =
      unpackLoopFuel (bytes.size - offset) opts bytes nextOff nextPax nextSeen nextAcc nextTotal := by
    simp [unpackLoop, unpackLoopFuel.eq_2, show ¬(offset ≥ bytes.size) by omega, hstep, hadv]
  rw [heq]
  exact unpackLoopFuel_indep (bytes.size - nextOff) (bytes.size - offset) (bytes.size - nextOff + 1)
    opts bytes nextOff nextPax nextSeen nextAcc nextTotal (Nat.le_refl _) (by omega) (Nat.le_refl _)

end LeanSwe.Tar.Proofs
