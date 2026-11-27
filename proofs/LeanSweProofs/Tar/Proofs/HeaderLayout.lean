import LeanSweProofs.Tar.Proofs.ByteModel

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem encodeOctalField_loop_length (k v : Nat) (acc : List UInt8) :
    (encodeOctalField.loop k v acc).length = k + acc.length := by
  induction k generalizing v acc with
  | zero => simp [encodeOctalField.loop]
  | succ k' ih =>
    unfold encodeOctalField.loop
    rw [ih, List.length_cons]
    omega

@[simp] private theorem encodeOctalField_size (val digits : Nat) :
    (encodeOctalField val digits).size = digits + 1 := by
  unfold encodeOctalField
  change (encodeOctalField.loop digits val [0]).toArray.size = digits + 1
  simp [encodeOctalField_loop_length]

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

private theorem ustarChecksumAt_congr {b1 b2 : ByteArray} {s1 s2 : Nat}
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

private theorem ustarChecksumAt_eq_ustarChecksum {bytes hdr : ByteArray} {offset : Nat}
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

private structure RawUstarHeader where
  fName : ByteArray
  fMode : ByteArray
  fUid : ByteArray
  fGid : ByteArray
  fSize : ByteArray
  fMtime : ByteArray
  fChk : ByteArray
  fType : UInt8
  fLink : ByteArray
  fMagic : ByteArray
  fVer : ByteArray
  fUname : ByteArray
  fGname : ByteArray
  fDev : ByteArray
  fPrefix : ByteArray
  fPad : ByteArray

private structure RawUstarHeader.WellSized (h : RawUstarHeader) : Prop where
  szName : h.fName.size = 100
  szMode : h.fMode.size = 8
  szUid : h.fUid.size = 8
  szGid : h.fGid.size = 8
  szSize : h.fSize.size = 12
  szMtime : h.fMtime.size = 12
  szChk : h.fChk.size = 8
  szLink : h.fLink.size = 100
  szMagic : h.fMagic.size = 6
  szVer : h.fVer.size = 2
  szUname : h.fUname.size = 32
  szGname : h.fGname.size = 32
  szDev : h.fDev.size = 16
  szPrefix : h.fPrefix.size = 155
  szPad : h.fPad.size = 12

private def RawUstarHeader.toBytes (h : RawUstarHeader) : ByteArray :=
  h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
    ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
    h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad

private def RawUstarHeader.withChk (h : RawUstarHeader) (chk : ByteArray) : RawUstarHeader :=
  { h with fChk := chk }

private theorem RawUstarHeader.withChk_wellSized {h : RawUstarHeader} (hw : h.WellSized)
    {chk : ByteArray} (hchk : chk.size = 8) : (h.withChk chk).WellSized :=
  { hw with szChk := hchk }

private theorem RawUstarHeader.toBytes_size {h : RawUstarHeader} (hw : h.WellSized) :
    h.toBytes.size = 512 := by
  unfold RawUstarHeader.toBytes
  simp only [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize,
    hw.szMtime, hw.szChk, show (ByteArray.mk #[h.fType]).size = 1 from rfl,
    hw.szLink, hw.szMagic, hw.szVer, hw.szUname, hw.szGname, hw.szDev, hw.szPrefix, hw.szPad]

private def RawUstarHeader.ofFields (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) (chkField : ByteArray) : RawUstarHeader :=
  { fName := padRightBytes 100 name.toUTF8, fMode := encodeOctalField (mode &&& 0o7777).toNat 7
  , fUid := encodeOctalField uid 7, fGid := encodeOctalField gid 7
  , fSize := encodeOctalField size 11, fMtime := encodeOctalField mtime 11
  , fChk := chkField, fType := typeflag, fLink := padRightBytes 100 linkname.toUTF8
  , fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00], fVer := ByteArray.mk #[0x30, 0x30]
  , fUname := padRightBytes 32 uname.toUTF8, fGname := padRightBytes 32 gname.toUTF8
  , fDev := ByteArray.mk (Array.replicate 16 0), fPrefix := padRightBytes 155 pfx.toUTF8
  , fPad := ByteArray.mk (Array.replicate 12 0) }

private theorem RawUstarHeader.ofFields_wellSized {name : String} {mode : UInt32} {uid gid size mtime : Nat}
    {typeflag : UInt8} {linkname uname gname pfx : String} {chkField : ByteArray} (hchk : chkField.size = 8) :
    (RawUstarHeader.ofFields name mode uid gid size mtime typeflag linkname uname gname pfx chkField).WellSized :=
  { szName := padRightBytes_size 100 _, szMode := encodeOctalField_size _ 7, szUid := encodeOctalField_size _ 7
  , szGid := encodeOctalField_size _ 7, szSize := encodeOctalField_size _ 11, szMtime := encodeOctalField_size _ 11
  , szChk := hchk, szLink := padRightBytes_size 100 _, szMagic := rfl, szVer := rfl
  , szUname := padRightBytes_size 32 _, szGname := padRightBytes_size 32 _, szDev := rfl
  , szPrefix := padRightBytes_size 155 _, szPad := rfl }

private def RawUstarHeader.zeros : RawUstarHeader :=
  { fName := ByteArray.mk (Array.replicate 100 0), fMode := ByteArray.mk (Array.replicate 8 0)
  , fUid := ByteArray.mk (Array.replicate 8 0), fGid := ByteArray.mk (Array.replicate 8 0)
  , fSize := ByteArray.mk (Array.replicate 12 0), fMtime := ByteArray.mk (Array.replicate 12 0)
  , fChk := ByteArray.mk (Array.replicate 8 0), fType := 0, fLink := ByteArray.mk (Array.replicate 100 0)
  , fMagic := ByteArray.mk (Array.replicate 6 0), fVer := ByteArray.mk (Array.replicate 2 0)
  , fUname := ByteArray.mk (Array.replicate 32 0), fGname := ByteArray.mk (Array.replicate 32 0)
  , fDev := ByteArray.mk (Array.replicate 16 0), fPrefix := ByteArray.mk (Array.replicate 155 0)
  , fPad := ByteArray.mk (Array.replicate 12 0) }

private theorem encodeOctalField_6_sp_size (chk : Nat) :
    (encodeOctalField chk 6 ++ ByteArray.mk #[0x20]).size = 8 := by
  rw [ByteArray.size_append, encodeOctalField_size]; rfl

private theorem buildUstarHeader_eq_raw (name : String) (mode : UInt32) (uid gid size mtime : Nat)
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

private theorem zeroBlock_eq_raw : zeroBlock = RawUstarHeader.zeros.toBytes := by
  unfold RawUstarHeader.zeros RawUstarHeader.toBytes
  dsimp only
  rw [show ByteArray.mk #[0] = ByteArray.mk (Array.replicate 1 0) from rfl]
  simp only [replicate_zero_append]
  rfl

private theorem set!_append_mid (L M R : ByteArray) (k : Nat) (v : UInt8) (hk : k < M.size) :
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

private theorem blitFixed_raw_chk {h : RawUstarHeader} (hw : h.WellSized)
    {chkF : ByteArray} (hchk : chkF.size = 8) :
    blitFixed h.toBytes 148 8 chkF = (h.withChk chkF).toBytes := by
  unfold RawUstarHeader.withChk
  have hs : h.toBytes = (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime) ++ h.fChk ++
      (ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad) := by
    split_raw_eq
  have h148 : (h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime).size = 148 := by
    simp [ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  rw [hs, ← h148, ← hw.szChk, blitFixed_mid_exact _ _ _ _ (hw.szChk.trans hchk.symm)]
  split_raw_eq

private theorem raw_withChk_outside_eq {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader}
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

private theorem raw_ustarChecksumAt_eq {bytes : ByteArray} {offset : Nat} {h : RawUstarHeader}
    {c1 c2 : ByteArray} (hw : h.WellSized) (hc1 : c1.size = 8) (hc2 : c2.size = 8)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = (h.withChk c1).toBytes) :
    ustarChecksumAt bytes offset = ustarChecksum (h.withChk c2).toBytes :=
  ustarChecksumAt_eq_ustarChecksum hbd
    (by rw [RawUstarHeader.toBytes_size (h.withChk_wellSized hw hc2)]; exact Nat.le_refl _)
    fun _ hi hnot => raw_withChk_outside_eq hw hc1 hc2 hbd hext hi hnot

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
  rw [blitFixed_raw_chk hw0 (encodeOctalField_6_sp_size _), buildUstarHeader_eq_raw]
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
