import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.ConcreteUnpack

/-!
Concrete verification of `test_tar_unpackWith_checksumNumericAndUnsupported_validated`
using `RawUstarHeader` algebraic decomposition and bounded arithmetic.
-/

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem byteArray_set_append_left (a b : ByteArray) (i : Nat) (v : UInt8) (hi : i < a.size) :
    (a ++ b).set! i v = a.set! i v ++ b := by
  have h : (ByteArray.empty ++ (a ++ b)).set! (ByteArray.empty.size + i) v =
      ByteArray.empty ++ (a.set! i v ++ b) :=
    set!_append_mid ByteArray.empty a b i v hi
  simpa using h

private theorem byteArray_blitFixed_same_size {M src : ByteArray} {w : Nat}
    (hM : M.size = w) (hs : src.size = w) :
    blitFixed M 0 w src = src := by
  apply ByteArray.ext
  apply Array.ext
  · rw [← ByteArray.size, ← ByteArray.size, blitFixed_size, hM, hs]
  · intro i hi1 hi2
    have hi_s : i < src.size := hi2
    have hi_m : i < M.size := by rw [hM, ← hs]; exact hi_s
    have hbd : 0 + min w src.size ≤ M.size := by rw [hs, hM]; omega
    have hg := blitFixed_getElem hbd hi_m
    have hcond : 0 ≤ i ∧ i < 0 + min w src.size := ⟨Nat.zero_le _, by rw [hs]; omega⟩
    rw [dite_eq_left_of_eq_true (eq_true hcond)] at hg
    simp only [Nat.sub_zero] at hg
    rw [← ByteArray.getElem_eq_getElem_data, ← ByteArray.getElem_eq_getElem_data]
    exact hg

private theorem blitFixed_raw_chk {h : RawUstarHeader} (hw : h.WellSized)
    {src : ByteArray} (hsrc : src.size = 8) :
    blitFixed h.toBytes 148 8 src = (h.withChk src).toBytes := by
  let L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime
  let R := ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
    h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  have hL : L.size = 148 := by
    simp only [L, ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid,
      hw.szSize, hw.szMtime]
  have hbytes : h.toBytes = L ++ (h.fChk ++ R) := by
    simp [RawUstarHeader.toBytes, L, R, ByteArray.append_assoc]
  have hres : (h.withChk src).toBytes = L ++ (src ++ R) := by
    simp [RawUstarHeader.toBytes, RawUstarHeader.withChk, L, R, ByteArray.append_assoc]
  rw [hbytes, blitFixed_append_mid L h.fChk R src hL hw.szChk,
    byteArray_blitFixed_same_size hw.szChk hsrc, hres]

private theorem set!_raw_name {h : RawUstarHeader} (hw : h.WellSized)
    {k : Nat} (hk : k < 100) (v : UInt8) :
    h.toBytes.set! k v =
      { h with fName := h.fName.set! k v }.toBytes := by
  let R := h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++
    ByteArray.mk #[h.fType] ++ h.fLink ++ h.fMagic ++ h.fVer ++
    h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  have hbytes : h.toBytes = h.fName ++ R := by
    simp [RawUstarHeader.toBytes, R, ByteArray.append_assoc]
  have hres : { h with fName := h.fName.set! k v }.toBytes = h.fName.set! k v ++ R := by
    simp [RawUstarHeader.toBytes, R, ByteArray.append_assoc]
  have hk' : k < h.fName.size := by rw [hw.szName]; exact hk
  rw [hbytes, byteArray_set_append_left h.fName R k v hk', hres]

private theorem set!_raw_link {h : RawUstarHeader} (hw : h.WellSized)
    {k : Nat} (hk : k < 100) (v : UInt8) :
    h.toBytes.set! (157 + k) v =
      { h with fLink := h.fLink.set! k v }.toBytes := by
  let L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++
    h.fChk ++ ByteArray.mk #[h.fType]
  let R := h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad
  have hL : L.size = 157 := by
    simp only [L, ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid,
      hw.szSize, hw.szMtime, hw.szChk]
    rfl
  have hbytes : h.toBytes = L ++ (h.fLink ++ R) := by
    simp [RawUstarHeader.toBytes, L, R, ByteArray.append_assoc]
  have hres : { h with fLink := h.fLink.set! k v }.toBytes = L ++ (h.fLink.set! k v ++ R) := by
    simp [RawUstarHeader.toBytes, L, R, ByteArray.append_assoc]
  have hk' : k < h.fLink.size := by rw [hw.szLink]; exact hk
  rw [hbytes, ← hL, set!_append_mid L h.fLink R k v hk', hres]

private theorem ustarChecksum_go_le (hdr : ByteArray) (n idx acc : Nat)
    (hrem : 512 - idx = n) :
    ustarChecksum.go hdr idx acc ≤ acc + n * 255 := by
  induction n generalizing idx acc with
  | zero =>
    have hge : idx ≥ 512 := by omega
    rw [ustarChecksum.go.eq_1]
    simp only [hge, ↓reduceIte]
    omega
  | succ n' ih =>
    have hnot : ¬(idx ≥ 512) := by omega
    rw [ustarChecksum.go.eq_1]
    simp only [hnot, ↓reduceIte]
    by_cases hmid : (decide (148 ≤ idx) && decide (idx < 156)) = true
    · simp only [hmid, ↓reduceIte]
      have hbound := ih (idx + 1) (acc + 32) (by omega)
      omega
    · simp only [hmid, Bool.false_eq_true, ↓reduceIte]
      have hbyte : (if h : idx < hdr.size then hdr[idx].toNat else 0) ≤ 255 := by
        split
        · have h256 : hdr[idx].toNat < 256 := UInt8.toNat_lt _
          omega
        · omega
      have hbound := ih (idx + 1) (acc + (if h : idx < hdr.size then hdr[idx].toNat else 0)) (by omega)
      omega

private theorem ustarChecksum_le_130560 (hdr : ByteArray) :
    ustarChecksum hdr ≤ 130560 := by
  unfold ustarChecksum
  have h := ustarChecksum_go_le hdr 512 0 0 rfl
  omega

private theorem foldl_octal_ge (xs : List UInt8) (init : Nat) :
    init * 8 ^ xs.length ≤ xs.foldl (fun acc b => acc * 8 + (b.toNat - 48)) init := by
  induction xs generalizing init with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have hstep := ih (init * 8 + (b.toNat - 48))
    have hmono : init * (8 ^ bs.length * 8) ≤ (init * 8 + (b.toNat - 48)) * 8 ^ bs.length := by
      calc init * (8 ^ bs.length * 8)
          = (init * 8) * 8 ^ bs.length := by rw [Nat.mul_comm (8 ^ bs.length) 8, ← Nat.mul_assoc]
        _ ≤ (init * 8 + (b.toNat - 48)) * 8 ^ bs.length := Nat.mul_le_mul_right _ (by omega)
    omega

private theorem encodeOctalField_6_sp_size (v : Nat) :
    (encodeOctalField v 6 ++ ByteArray.mk #[0x20]).size = 8 := by
  rw [ByteArray.size_append, encodeOctalField_size]
  rfl

private theorem aTxt_utf8_size : ("a.txt" : String).toUTF8.size = 5 := by
  rw [toUTF8_eq_toByteArray, List.size_toByteArray]
  decide

private theorem empty_utf8_size : ("" : String).toUTF8.size = 0 := by
  rw [toUTF8_eq_toByteArray, List.size_toByteArray]
  decide

private def baseRaw (chk : ByteArray) : RawUstarHeader :=
  RawUstarHeader.ofFields "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" chk

private theorem baseRaw_wellSized {chk : ByteArray} (hchk : chk.size = 8) :
    (baseRaw chk).WellSized :=
  RawUstarHeader.ofFields_wellSized hchk

private noncomputable def baseChkField : ByteArray :=
  let hdrPre := (baseRaw (ByteArray.mk (Array.replicate 8 0x20))).toBytes
  encodeOctalField (ustarChecksumAt hdrPre 0) 6 ++ ByteArray.mk #[0x20]

private theorem baseChkField_eq :
    baseChkField = encodeOctalField
      (ustarChecksum (baseRaw (ByteArray.mk (Array.replicate 8 0x20))).toBytes) 6 ++ ByteArray.mk #[0x20] := by
  dsimp only [baseChkField]
  rw [ustarChecksum_eq_ustarChecksumAt]

private theorem baseChkField_size : baseChkField.size = 8 :=
  encodeOctalField_6_sp_size _

private theorem baseHdr_eq_raw :
    mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" =
      (baseRaw baseChkField).toBytes := by
  rw [mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_eq_raw]
  rfl

private theorem unpackLoopFuel_eq_of_ge (fuel1 fuel2 : Nat) (opts : UnpackOptions) (bytes : ByteArray) :
    ∀ (offset : Nat) (pendingPax : Option PaxOverrides) (seen : List String)
      (acc : List TarEntry) (totalBytes : Nat),
      bytes.size - offset + 1 ≤ fuel1 →
      bytes.size - offset + 1 ≤ fuel2 →
      unpackLoopFuel fuel1 opts bytes offset pendingPax seen acc totalBytes =
        unpackLoopFuel fuel2 opts bytes offset pendingPax seen acc totalBytes := by
  induction fuel1 generalizing fuel2 with
  | zero =>
    intro offset _ _ _ _ h1 _
    omega
  | succ f1 ih =>
    cases fuel2 with
    | zero =>
      intro offset _ _ _ _ _ h2
      omega
    | succ f2 =>
      intro offset pendingPax seen acc totalBytes h1 h2
      rw [unpackLoopFuel.eq_2, unpackLoopFuel.eq_2]
      by_cases hge : offset ≥ bytes.size
      · simp [hge]
      · simp only [hge, ↓reduceIte]
        cases hst : unpackStep opts bytes offset pendingPax seen acc totalBytes with
        | error e => simp
        | ok st =>
          cases st with
          | done res => simp
          | cont no np ns na nt =>
            dsimp only
            by_cases hgt : no > offset
            · simp only [hgt, ↓reduceIte]
              exact ih f2 no np ns na nt (by omega) (by omega)
            · simp [hgt]

private theorem unpackWith_eq_unpackLoop {opts : UnpackOptions} {hdr post : ByteArray}
    (hhdr : hdr.size = 512) (hpost : post.size % 512 = 0) :
    unpackWith opts (hdr ++ post) = unpackLoop opts (hdr ++ post) 0 none [] [] 0 := by
  unfold LeanSwe.Tar.unpackWith Impl.unpackWith
  have hsz : (hdr ++ post).size = 512 + post.size := by rw [ByteArray.size_append, hhdr]
  have hne0 : ((hdr ++ post).size == 0) = false := beq_false_of_ne (by omega)
  have hmod : ((hdr ++ post).size % 512 != 0) = false := by
    have hm : (hdr ++ post).size % 512 = 0 := by rw [hsz]; omega
    exact Bool.eq_false_iff.mpr (fun h => (bne_iff_ne.mp h) hm)
  simp only [hne0, hmod, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

private theorem unpackLoop_step_error {opts : UnpackOptions} {bytes : ByteArray}
    {offset : Nat} {pendingPax : Option PaxOverrides} {seen : List String}
    {acc : List TarEntry} {totalBytes : Nat} {err : TarError}
    (hbd : offset < bytes.size)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes = .error err) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes = .error err := by
  unfold unpackLoop
  have hfuel : bytes.size - offset + 1 = (bytes.size - offset).succ := rfl
  rw [hfuel, unpackLoopFuel.eq_2]
  have hnot_ge : ¬(offset ≥ bytes.size) := by omega
  simp [hnot_ge, hstep]

private theorem unpackLoop_step_cont {opts : UnpackOptions} {bytes : ByteArray}
    {offset : Nat} {pendingPax : Option PaxOverrides} {seen : List String}
    {acc : List TarEntry} {totalBytes : Nat}
    {nextOffset : Nat} {nextPax : Option PaxOverrides} {nextSeen : List String}
    {nextAcc : List TarEntry} {nextTotal : Nat}
    (hbd : offset < bytes.size) (hgt : nextOffset > offset)
    (hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes =
      .ok (.cont nextOffset nextPax nextSeen nextAcc nextTotal)) :
    unpackLoop opts bytes offset pendingPax seen acc totalBytes =
      unpackLoop opts bytes nextOffset nextPax nextSeen nextAcc nextTotal := by
  unfold unpackLoop
  have hfuel : bytes.size - offset + 1 = (bytes.size - offset).succ := rfl
  rw [hfuel, unpackLoopFuel.eq_2]
  have hnot_ge : ¬(offset ≥ bytes.size) := by omega
  simp only [hnot_ge, ↓reduceIte, hstep, hgt]
  exact unpackLoopFuel_eq_of_ge (bytes.size - offset) (bytes.size - nextOffset + 1)
    opts bytes nextOffset nextPax nextSeen nextAcc nextTotal (by omega) (by omega)

private theorem isZeroRange_raw_zero_false {h : RawUstarHeader} (hw : h.WellSized)
    {post : ByteArray} (h0 : ∃ hsz : 0 < h.fName.size, h.fName[0]'hsz ≠ 0) :
    isZeroRange (h.toBytes ++ post) 0 512 = false := by
  rcases h0 with ⟨hsz, hne⟩
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 + 512 ≤ (h.toBytes ++ post).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  have hext512 : (h.toBytes ++ post).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left hhdr_sz.symm
  have hext_name := (raw_extract_fields hw hext512).1
  have hb0_e : 0 < ((h.toBytes ++ post).extract 0 100).size := by rw [hext_name]; exact hsz
  have hb0 : (h.toBytes ++ post)[0]'(by omega) = h.fName[0]'hsz := by
    have hg := ByteArray.getElem_extract hb0_e
    rw [byteArray_getElem_of_eq hext_name hb0_e hsz] at hg
    simpa using hg.symm
  exact isZeroRange_false_of_ne (i := 0) (by omega) (by omega) (by rw [hb0]; exact hne)

private theorem baseRaw_fName_nonzero :
    ∃ hsz : 0 < (padRightBytes 100 ("a.txt" : String).toUTF8).size,
      (padRightBytes 100 ("a.txt" : String).toUTF8)[0]'hsz ≠ 0 := by
  have hsz : 0 < (padRightBytes 100 ("a.txt" : String).toUTF8).size := by
    rw [padRightBytes_size]; omega
  refine ⟨hsz, ?_⟩
  rw [padRightBytes_getElem 100 _ (by omega)]
  have h5 : 0 < ("a.txt" : String).toUTF8.size := by rw [aTxt_utf8_size]; omega
  simp only [h5, ↓reduceDIte]
  have hb : ("a.txt" : String).toUTF8[0]'(by decide) = 0x61 := by decide
  rw [hb]
  decide

private theorem parseUstarHeader_patched_steps {r : RawUstarHeader} (hrw : r.WellSized)
    {post : ByteArray} {uidVal : Nat} {resSize : Except TarError Nat}
    (hm : r.fMagic = ("ustar\x00" : String).toUTF8)
    (hv : r.fVer = ("00" : String).toUTF8)
    (hmode : r.fMode = encodeOctalField 0o644 7)
    (huid : parseUstarNumeric ((r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes ++ post) 108 116 0 true u64Limit "uid" = .ok uidVal)
    (hgid : r.fGid = encodeOctalField 0 7)
    (hsize : parseUstarNumeric ((r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes ++ post) 124 136 0 false u64Limit "size" = resSize)
    (hmtime : r.fMtime = encodeOctalField 0 11) :
    let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
    let bytes := h.toBytes ++ post
    parseUstarHeader bytes 0 =
      resSize.bind fun uSize =>
        .ok { mode := 0o644, uid := uidVal, gid := 0, size := uSize, mtime := 0, typeflag := r.fType } := by
  intro h bytes
  have huid' : parseUstarNumeric bytes 108 116 0 true u64Limit "uid" = .ok uidVal := huid
  have hsize' : parseUstarNumeric bytes 124 136 0 false u64Limit "size" = resSize := hsize
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 + 512 ≤ bytes.size := by rw [ByteArray.size_append, hhdr_sz]; omega
  have hext512 : bytes.extract 0 512 = h.toBytes := ByteArray.extract_append_eq_left hhdr_sz.symm
  have ⟨_, hext_mode, _, hext_gid, _, hext_mtime, hext_chk, _, hext_magic, hext_ver, _, _, _⟩ :=
    raw_extract_fields hw hext512
  simp only [Nat.zero_add, h, RawUstarHeader.withChk] at hext_mode hext_gid hext_mtime hext_chk hext_magic hext_ver
  have hchk_ok : parseChecksumOctal bytes 148 156 0 = .ok (ustarChecksum r.toBytes) :=
    parseChecksumOctal_encodeOctalField (ustarChecksum_lt _) hext_chk
  have hcsum_eq : ustarChecksumAt bytes 0 = ustarChecksum r.toBytes := by
    have heq : (r.withChk r.fChk).toBytes = r.toBytes := rfl
    have hraw := raw_ustarChecksumAt_eq hrw (encodeOctalField_6_sp_size _) hrw.szChk hbd hext512
    rw [heq] at hraw
    exact hraw
  have hmagic_true : hasValidMagic bytes 0 = true := by
    unfold hasValidMagic
    simp only [Nat.zero_add, hext_magic, hext_ver, hm, hv]
    decide
  have hmode_ok : parseUstarNumeric bytes 100 108 0 false u32Limit "mode" = .ok 0o644 := by
    rw [hmode] at hext_mode
    exact parseUstarNumeric_encodeOctalField (val := 0o644) (digits := 7) (limit := u32Limit)
      (by omega) (by decide) (by decide) hext_mode
  have hgid_ok : parseUstarNumeric bytes 116 124 0 true u64Limit "gid" = .ok 0 := by
    rw [hgid] at hext_gid
    exact parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_gid
  have hmtime_ok : parseUstarNumeric bytes 136 148 0 true u64Limit "mtime" = .ok 0 := by
    rw [hmtime] at hext_mtime
    exact parseUstarNumeric_encodeOctalField (val := 0) (digits := 11) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_mtime
  have htype : bytes[156]'(by omega) = r.fType := raw_getElem_type hw hbd hext512
  have h156 : 156 < bytes.size := by omega
  unfold parseUstarHeader
  simp only [Nat.zero_add, hchk_ok]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hcsum_eq]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hmagic_true, Bool.not_true,
    hmode_ok, huid', hgid_ok, hsize']
  cases resSize with
  | error e => rfl
  | ok v => simp only [hmtime_ok, h156, ↓reduceDIte, htype]

private theorem unpackStep_parseUstarHeader_err {opts : UnpackOptions} {h : RawUstarHeader}
    (hw : h.WellSized) {post : ByteArray} {err : TarError}
    (hnz : ∃ hsz : 0 < h.fName.size, h.fName[0]'hsz ≠ 0)
    (hparse : parseUstarHeader (h.toBytes ++ post) 0 = .error err) :
    unpackStep opts (h.toBytes ++ post) 0 none [] [] 0 = .error err := by
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hsz : (h.toBytes ++ post).size = 512 + post.size := by rw [ByteArray.size_append, hhdr_sz]
  have hnot_ge : ¬(0 ≥ (h.toBytes ++ post).size) := by omega
  have hnot_gt : ¬(0 + 512 > (h.toBytes ++ post).size) := by omega
  have hiz := isZeroRange_raw_zero_false hw (post := post) hnz
  unfold unpackStep
  simp only [hnot_ge, ↓reduceIte, hiz, Bool.false_eq_true, hnot_gt, hparse]

private theorem unpackWith_raw_parse_err {opts : UnpackOptions} {h : RawUstarHeader}
    (hw : h.WellSized) {post : ByteArray} {err : TarError}
    (hpost : post.size % 512 = 0)
    (hnz : ∃ hsz : 0 < h.fName.size, h.fName[0]'hsz ≠ 0)
    (hparse : parseUstarHeader (h.toBytes ++ post) 0 = .error err) :
    unpackWith opts (h.toBytes ++ post) = .error err := by
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 < (h.toBytes ++ post).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  rw [unpackWith_eq_unpackLoop hhdr_sz hpost]
  exact unpackLoop_step_error hbd (unpackStep_parseUstarHeader_err hw hnz hparse)

private theorem byteArray_set0_toList {b : ByteArray} (v : UInt8) (h0 : 0 < b.size) :
    (b.set! 0 v).data.toList = v :: b.data.toList.tail := by
  have hne : b.data.toList ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [Array.length_toList] at hlen
    change b.size = 0 at hlen
    omega
  cases hl : b.data.toList with
  | nil => exact absurd hl hne
  | cons x xs =>
    apply List.ext_getElem
    · have hsz : (b.set! 0 v).size = b.size := by rw [ByteArray.size_set!]
      have hbl : b.data.toList.length = b.size := Array.length_toList
      rw [Array.length_toList]
      change (b.set! 0 v).size = xs.length + 1
      rw [hsz, ← hbl, hl, List.length_cons]
    · intro i hi1 _
      have hi_s : i < (b.set! 0 v).size := by simpa [Array.length_toList] using hi1
      have hi_b : i < b.size := by
        have hsz : (b.set! 0 v).size = b.size := by rw [ByteArray.size_set!]
        omega
      rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data (h := hi_s)]
      rw [ByteArray.getElem_set! (h := h0) (hj := hi_b)]
      cases i with
      | zero => simp
      | succ k =>
        have hk : k + 1 < b.size := hi_b
        have hk_l : k + 1 < b.data.toList.length := by simpa [Array.length_toList] using hk
        have hg : b[k + 1]'hk = (b.data.toList)[k + 1]'hk_l := by
          rw [ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
        simp [hg, hl]

private theorem test5_case01_badChkVal (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 148 0x37 ++ twoZeroBlocks) = .error err ∧
      err.kind = .checksumMismatch ∧ (!err.message.isEmpty) = true := by
  have heq_raw : (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 148 0x37 =
      (baseRaw (baseChkField.set! 0 0x37)).toBytes := by
    rw [baseHdr_eq_raw]
    have hhw := baseRaw_wellSized baseChkField_size
    simpa [baseRaw, RawUstarHeader.ofFields] using set!_raw_chk hhw (k := 0) (by omega) 0x37
  rw [heq_raw]
  have hchk_sz : (baseChkField.set! 0 0x37).size = 8 := by rw [ByteArray.size_set!, baseChkField_size]
  let h := baseRaw (baseChkField.set! 0 0x37)
  have hw : h.WellSized := baseRaw_wellSized hchk_sz
  let hdrPre := (baseRaw (ByteArray.mk (Array.replicate 8 0x20))).toBytes
  let chkVal := ustarChecksum hdrPre
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hbd : 0 + 512 ≤ (h.toBytes ++ twoZeroBlocks).size := by
    rw [ByteArray.size_append, RawUstarHeader.toBytes_size hw]; omega
  have hext_chk : (h.toBytes ++ twoZeroBlocks).extract 148 156 = baseChkField.set! 0 0x37 := by
    simpa [h, baseRaw, RawUstarHeader.ofFields] using (raw_extract_fields hw hext512).2.2.2.2.2.2.1
  rcases encodeOctalField_loop_spec 6 chkVal [0] with ⟨ds, heq_ds, hlen_ds, hdigs_ds, _⟩
  cases hds : ds with
  | nil => simp [hds] at hlen_ds
  | cons d0 ds' =>
    have hds'_len : ds'.length = 5 := by simp [hds] at hlen_ds; omega
    have hlist_base : baseChkField.data.toList = (d0 :: ds') ++ [0, 0x20] := by
      rw [baseChkField_eq, byteArray_data_toList_append]
      have h1 : (encodeOctalField chkVal 6).data.toList = (d0 :: ds') ++ [0] := by
        unfold encodeOctalField; rw [heq_ds, hds]
      rw [h1, List.append_assoc]
      rfl
    have hlist_mut : (baseChkField.set! 0 0x37).data.toList = (0x37 :: ds') ++ [0, 0x20] := by
      rw [byteArray_set0_toList 0x37 (by rw [baseChkField_size]; omega), hlist_base]
      simp
    have hdigs' : ∀ d ∈ (0x37 :: ds'), (0x30 ≤ d && d ≤ 0x37) = true := by
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · decide
      · have ⟨hlo, hhi⟩ := hdigs_ds b (by simp [hds, hb])
        simp [hlo, hhi]
    have hparse_chk : parseChecksumOctal (h.toBytes ++ twoZeroBlocks) 148 156 0 =
        .ok ((0x37 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 48)) 0) := by
      unfold parseChecksumOctal
      dsimp only
      rw [hext_chk, hlist_mut]
      have hdrop : (((0x37 : UInt8) :: ds') ++ [0, 0x20]).dropWhile (· == 32) = (0x37 :: ds') ++ [0, 0x20] := by
        simp
      have htake : (((0x37 : UInt8) :: ds') ++ [0, 0x20]).takeWhile (fun b => 48 ≤ b && b ≤ 55) = 0x37 :: ds' := by
        rw [List.takeWhile_append, list_takeWhile_eq_self _ (0x37 :: ds') hdigs']
        simp
      rw [hdrop, htake]
      have hdrop2 : (((0x37 : UInt8) :: ds') ++ [0, 0x20]).drop (0x37 :: ds').length = [0, 0x20] := by simp
      have hne_empty : ((0x37 : UInt8) :: ds').isEmpty = false := rfl
      have hall : ([0, 0x20] : List UInt8).all (fun b => b == 32 || b == 0) = true := by decide
      simp only [hdrop2, hne_empty, Bool.false_eq_true, ↓reduceIte, hall, Bool.not_true]
    have hstored_ge : 229376 ≤ (0x37 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 48)) 0 := by
      simp only [List.foldl_cons]
      have hge := foldl_octal_ge ds' (0 * 8 + ((0x37 : UInt8).toNat - 48))
      rw [hds'_len] at hge
      have hge_val : (0 * 8 + ((0x37 : UInt8).toNat - 48)) * 8 ^ 5 = 229376 := by decide
      rw [hge_val] at hge
      exact hge
    have hcsum_eq : ustarChecksumAt (h.toBytes ++ twoZeroBlocks) 0 = chkVal := by
      have hw0 := baseRaw_wellSized (chk := ByteArray.mk (Array.replicate 8 0x20)) (by decide)
      have heq_w2 : (baseRaw (ByteArray.mk (Array.replicate 8 0x20))).withChk
          (ByteArray.mk (Array.replicate 8 0x20)) = baseRaw (ByteArray.mk (Array.replicate 8 0x20)) := rfl
      have hr := raw_ustarChecksumAt_eq hw0 hchk_sz (by decide) hbd
        (c1 := baseChkField.set! 0 0x37) (c2 := ByteArray.mk (Array.replicate 8 0x20)) hext512
      rw [heq_w2] at hr
      exact hr
    have hchk_le : chkVal ≤ 130560 := ustarChecksum_le_130560 hdrPre
    have hne : ((0x37 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 48)) 0 !=
        ustarChecksumAt (h.toBytes ++ twoZeroBlocks) 0) = true := by
      rw [hcsum_eq]
      exact bne_iff_ne.mpr (by omega)
    have hparse : parseUstarHeader (h.toBytes ++ twoZeroBlocks) 0 =
        .error { kind := .checksumMismatch, message := "USTAR header checksum mismatch", offset := some 0 } := by
      unfold parseUstarHeader
      rw [hparse_chk]
      dsimp only [bind, Except.bind]
      simp only [hne, ↓reduceIte]
      rfl
    refine ⟨_, unpackWith_raw_parse_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero hparse, rfl, rfl⟩

private theorem test5_case02_badChkSyntax (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 148 0x58 ++ twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  have heq_raw : (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 148 0x58 =
      (baseRaw (baseChkField.set! 0 0x58)).toBytes := by
    rw [baseHdr_eq_raw]
    have hhw := baseRaw_wellSized baseChkField_size
    simpa [baseRaw, RawUstarHeader.ofFields] using set!_raw_chk hhw (k := 0) (by omega) 0x58
  rw [heq_raw]
  have hchk_sz : (baseChkField.set! 0 0x58).size = 8 := by rw [ByteArray.size_set!, baseChkField_size]
  let h := baseRaw (baseChkField.set! 0 0x58)
  have hw : h.WellSized := baseRaw_wellSized hchk_sz
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_chk : (h.toBytes ++ twoZeroBlocks).extract 148 156 = baseChkField.set! 0 0x58 := by
    simpa [h, baseRaw, RawUstarHeader.ofFields] using (raw_extract_fields hw hext512).2.2.2.2.2.2.1
  have hlist : (baseChkField.set! 0 0x58).data.toList = 0x58 :: baseChkField.data.toList.tail :=
    byteArray_set0_toList 0x58 (by rw [baseChkField_size]; omega)
  have hparse_chk : parseChecksumOctal (h.toBytes ++ twoZeroBlocks) 148 156 0 =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    unfold parseChecksumOctal
    dsimp only
    rw [hext_chk, hlist]
    simp
  have hparse : parseUstarHeader (h.toBytes ++ twoZeroBlocks) 0 =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    unfold parseUstarHeader
    simp [hparse_chk]
  refine ⟨_, unpackWith_raw_parse_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero hparse, rfl, rfl⟩

private theorem test5_case03_allNulChk (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 148 8 (ByteArray.mk (Array.replicate 8 0)) ++
        twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  have heq_raw : blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 148 8
      (ByteArray.mk (Array.replicate 8 0)) = (baseRaw (ByteArray.mk (Array.replicate 8 0))).toBytes := by
    rw [baseHdr_eq_raw]
    have hhw := baseRaw_wellSized baseChkField_size
    simpa [baseRaw, RawUstarHeader.ofFields, RawUstarHeader.withChk] using
      blitFixed_raw_chk hhw (src := ByteArray.mk (Array.replicate 8 0)) rfl
  rw [heq_raw]
  let h := baseRaw (ByteArray.mk (Array.replicate 8 0))
  have hw : h.WellSized := baseRaw_wellSized rfl
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_chk : (h.toBytes ++ twoZeroBlocks).extract 148 156 = ByteArray.mk (Array.replicate 8 0) := by
    simpa [h, baseRaw, RawUstarHeader.ofFields] using (raw_extract_fields hw hext512).2.2.2.2.2.2.1
  have hparse_chk : parseChecksumOctal (h.toBytes ++ twoZeroBlocks) 148 156 0 =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    unfold parseChecksumOctal
    rw [hext_chk]
    rfl
  have hparse : parseUstarHeader (h.toBytes ++ twoZeroBlocks) 0 =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    unfold parseUstarHeader
    simp [hparse_chk]
  refine ⟨_, unpackWith_raw_parse_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero hparse, rfl, rfl⟩

private theorem parseUstarHeader_raw_badMagic {r : RawUstarHeader} (hrw : r.WellSized)
    {post : ByteArray}
    (hm : (r.fMagic.data.toList == [117, 115, 116, 97, 114, 0] && r.fVer.data.toList == [48, 48] ||
      r.fMagic.data.toList == [117, 115, 116, 97, 114, 32] && r.fVer.data.toList == [32, 0]) = false) :
    let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
    parseUstarHeader (h.toBytes ++ post) 0 =
      .error { kind := .invalidHeader, message := "invalid USTAR magic or version", offset := some 0 } := by
  intro h
  let bytes := h.toBytes ++ post
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 + 512 ≤ bytes.size := by rw [ByteArray.size_append, hhdr_sz]; omega
  have hext512 : bytes.extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left hhdr_sz.symm
  have ⟨_, _, _, _, _, _, hext_chk, _, hext_magic, hext_ver, _, _, _⟩ := raw_extract_fields hw hext512
  simp only [Nat.zero_add, h, RawUstarHeader.withChk] at hext_chk hext_magic hext_ver
  have hchk_ok : parseChecksumOctal bytes 148 156 0 = .ok (ustarChecksum r.toBytes) :=
    parseChecksumOctal_encodeOctalField (ustarChecksum_lt _) hext_chk
  have hcsum_eq : ustarChecksumAt bytes 0 = ustarChecksum r.toBytes := by
    have heq : (r.withChk r.fChk).toBytes = r.toBytes := rfl
    have hraw := raw_ustarChecksumAt_eq hrw (encodeOctalField_6_sp_size _) hrw.szChk hbd hext512
    rw [heq] at hraw
    exact hraw
  have hmagic_false : hasValidMagic bytes 0 = false := by
    unfold hasValidMagic
    simp only [Nat.zero_add, hext_magic, hext_ver]
    exact hm
  change parseUstarHeader bytes 0 = _
  unfold parseUstarHeader
  simp only [Nat.zero_add, hchk_ok]
  dsimp only [bind, Except.bind]
  rw [hcsum_eq]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hmagic_false]
  rfl

private theorem test5_case04_badMagic (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      (patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 257 6 "notust".toUTF8) ++
        twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  have hm6 : ("notust" : String).toUTF8.size = 6 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  let r : RawUstarHeader := { baseRaw baseChkField with fMagic := ("notust" : String).toUTF8 }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with szMagic := hm6 }
  have heq_raw : patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 257 6 "notust".toUTF8) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, blitFixed_raw_magic (baseRaw_wellSized baseChkField_size) hm6]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hparse := parseUstarHeader_raw_badMagic hrw (post := twoZeroBlocks) (by decide)
  refine ⟨_, unpackWith_raw_parse_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero hparse, rfl, rfl⟩

private theorem test5_case05_negBase256 (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      (patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 124 12
        (ByteArray.mk (Array.replicate 12 0xff))) ++ twoZeroBlocks) = .error err ∧
      err.kind = .sizeOverflow ∧ (!err.message.isEmpty) = true := by
  let r : RawUstarHeader := { baseRaw baseChkField with fSize := ByteArray.mk (Array.replicate 12 0xff) }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with szSize := rfl }
  have heq_raw : patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 124 12
      (ByteArray.mk (Array.replicate 12 0xff))) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, blitFixed_raw_size (baseRaw_wellSized baseChkField_size) rfl]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = encodeOctalField 0 7 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = ByteArray.mk (Array.replicate 12 0xff) := by
    simpa [h, RawUstarHeader.withChk, r] using (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_uid
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" =
      .error { kind := .sizeOverflow, message := "negative base-256 USTAR size", offset := some 0 } := by
    unfold parseUstarNumeric
    rw [hext_size]
    rfl
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [Except.bind] at hparse
  refine ⟨_, unpackWith_raw_parse_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero hparse, rfl, rfl⟩

private theorem test5_case07_nulSize (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      (patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 124 12
        (ByteArray.mk (Array.replicate 12 0))) ++ twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  let r : RawUstarHeader := { baseRaw baseChkField with fSize := ByteArray.mk (Array.replicate 12 0) }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with szSize := rfl }
  have heq_raw : patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 124 12
      (ByteArray.mk (Array.replicate 12 0))) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, blitFixed_raw_size (baseRaw_wellSized baseChkField_size) rfl]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = encodeOctalField 0 7 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = ByteArray.mk (Array.replicate 12 0) := by
    simpa [h, RawUstarHeader.withChk, r] using (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_uid
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" =
      .error { kind := .invalidHeader, message := "missing USTAR size", offset := some 0 } := by
    unfold parseUstarNumeric
    rw [hext_size]
    rfl
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [Except.bind] at hparse
  refine ⟨_, unpackWith_raw_parse_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero hparse, rfl, rfl⟩

private theorem base_decodeTarEntry_ok {h : RawUstarHeader} (hw : h.WellSized) {post : ByteArray}
    (hname : h.fName = padRightBytes 100 ("a.txt" : String).toUTF8)
    (huname : h.fUname = padRightBytes 32 ("" : String).toUTF8)
    (hgname : h.fGname = padRightBytes 32 ("" : String).toUTF8)
    (hpfx : h.fPrefix = padRightBytes 155 ("" : String).toUTF8)
    (uidVal : Nat) :
    decodeTarEntry {} (h.toBytes ++ post) 0
      { mode := 0o644, uid := uidVal, gid := 0, size := 0, mtime := 0, typeflag := 0x30 }
      none [] 0 0 =
      .ok ({ path := "a.txt", kind := .regular, mode := 0o644, uid := uidVal, gid := 0, mtime := 0,
             uname := "", gname := "", data := ByteArray.empty }, 0) := by
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 + 512 ≤ (h.toBytes ++ post).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  have hext512 : (h.toBytes ++ post).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left hhdr_sz.symm
  have ⟨hext_name, _, _, _, _, _, _, _, _, _, hext_uname, hext_gname, hext_pfx⟩ :=
    raw_extract_fields hw hext512
  simp only [Nat.zero_add] at hext_name hext_uname hext_gname hext_pfx
  rw [hname] at hext_name
  rw [huname] at hext_uname
  rw [hgname] at hext_gname
  rw [hpfx] at hext_pfx
  have hdn : decodeCStringUtf8 (h.toBytes ++ post) 0 100 0 "name" = .ok "a.txt" :=
    decodeCStringUtf8_padRightBytes (start := 0) (w := 100) (s := "a.txt") (fieldName := "name")
      (by decide) (by rw [aTxt_utf8_size]; omega) (by omega) hext_name
  have hdu : decodeCStringUtf8 (h.toBytes ++ post) 265 297 0 "uname" = .ok "" :=
    decodeCStringUtf8_padRightBytes (start := 265) (w := 32) (s := "") (fieldName := "uname")
      (by decide) (by rw [empty_utf8_size]; omega) (by omega) hext_uname
  have hdg : decodeCStringUtf8 (h.toBytes ++ post) 297 329 0 "gname" = .ok "" :=
    decodeCStringUtf8_padRightBytes (start := 297) (w := 32) (s := "") (fieldName := "gname")
      (by decide) (by rw [empty_utf8_size]; omega) (by omega) hext_gname
  have hdp : decodeCStringUtf8 (h.toBytes ++ post) 345 500 0 "prefix" = .ok "" :=
    decodeCStringUtf8_padRightBytes (start := 345) (w := 155) (s := "") (fieldName := "prefix")
      (by decide) (by rw [empty_utf8_size]; omega) (by omega) hext_pfx
  have hp0 : pad512 0 = 0 := rfl
  unfold decodeTarEntry
  simp only [Nat.zero_add, beq_self_eq_true, Bool.true_or, ↓reduceIte, Option.getD_none,
    bne_self_eq_false, hp0, hdn, hdu, hdg, hdp]
  have hle_ent : ¬(1 > ({} : UnpackOptions).maxEntries) := by change ¬(1 > 100000); omega
  have hle_tot : ¬(0 > ({} : UnpackOptions).maxTotalBytes) := by change ¬(0 > 256 * 1024 * 1024); omega
  have hnot_gt : ¬(512 + 0 > (h.toBytes ++ post).size) := by omega
  simp only [hle_ent, hle_tot, hnot_gt, ↓reduceIte]
  rfl

private theorem unpackWith_base_regular_ok {h : RawUstarHeader} (hw : h.WellSized)
    (hname : h.fName = padRightBytes 100 ("a.txt" : String).toUTF8)
    (huname : h.fUname = padRightBytes 32 ("" : String).toUTF8)
    (hgname : h.fGname = padRightBytes 32 ("" : String).toUTF8)
    (hpfx : h.fPrefix = padRightBytes 155 ("" : String).toUTF8)
    (uidVal : Nat)
    (hparse : parseUstarHeader (h.toBytes ++ twoZeroBlocks) 0 =
      .ok { mode := 0o644, uid := uidVal, gid := 0, size := 0, mtime := 0, typeflag := 0x30 }) :
    unpackWith {} (h.toBytes ++ twoZeroBlocks) =
      .ok [{ path := "a.txt", kind := .regular, mode := 0o644, uid := uidVal, gid := 0, mtime := 0,
             uname := "", gname := "", data := ByteArray.empty }] := by
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 < (h.toBytes ++ twoZeroBlocks).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  rw [unpackWith_eq_unpackLoop hhdr_sz (by rw [twoZeroBlocks_size])]
  have hiz : isZeroRange (h.toBytes ++ twoZeroBlocks) 0 512 = false := by
    apply isZeroRange_raw_zero_false hw
    rw [hname]
    exact baseRaw_fName_nonzero
  have hdec := base_decodeTarEntry_ok hw (post := twoZeroBlocks) hname huname hgname hpfx uidVal
  let entry : TarEntry := { path := "a.txt", kind := .regular, uid := uidVal }
  have hstep : unpackStep {} (h.toBytes ++ twoZeroBlocks) 0 none [] [] 0 =
      .ok (.cont 512 none ["a.txt"] [entry] 0) := by
    unfold unpackStep
    have hnot_ge : ¬(0 ≥ (h.toBytes ++ twoZeroBlocks).size) := by omega
    have hnot_gt : ¬(0 + 512 > (h.toBytes ++ twoZeroBlocks).size) := by
      rw [ByteArray.size_append, hhdr_sz]; omega
    simp only [hnot_ge, ↓reduceIte, hiz, Bool.false_eq_true, hnot_gt, hparse,
      show ((0x30 : UInt8) == 120) = false from rfl, List.length_nil, hdec, entry]
    rfl
  rw [unpackLoop_step_cont hbd (by omega) hstep, ← hhdr_sz]
  simpa [twoZeroBlocks] using unpackLoop_at_twoZeroBlocks {} h.toBytes ["a.txt"] [entry] 0

private theorem test5_case06_posBase256Uid :
    let posBase256Uid := patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "")
      108 8 (ByteArray.mk #[0x80, 0, 0, 0, 0, 0, 0, 42]))
    ∃ res, unpackWith {} (posBase256Uid ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular, uid := 42 }] res := by
  dsimp only
  let r : RawUstarHeader := { baseRaw baseChkField with fUid := ByteArray.mk #[0x80, 0, 0, 0, 0, 0, 0, 42] }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with szUid := rfl }
  have heq_raw : patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 108 8
      (ByteArray.mk #[0x80, 0, 0, 0, 0, 0, 0, 42])) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, blitFixed_raw_uid (baseRaw_wellSized baseChkField_size) rfl]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = ByteArray.mk #[0x80, 0, 0, 0, 0, 0, 0, 42] := by
    simpa [h, RawUstarHeader.withChk, r] using (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = encodeOctalField 0 11 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 42 := by
    unfold parseUstarNumeric
    rw [hext_uid]
    have hl : (ByteArray.mk #[0x80, 0, 0, 0, 0, 0, 0, 42]).data.toList = [0x80, 0, 0, 0, 0, 0, 0, 42] := rfl
    rw [hl]
    have h1 : ((0x80 : UInt8) &&& 128 != 0) = true := by decide
    have h2 : ((0x80 : UInt8) &&& 64 != 0) = false := by decide
    have h3 : [0, 0, 0, 0, 0, 0, (42 : UInt8)].foldl (fun acc b => acc * 256 + b.toNat)
        ((0x80 : UInt8) &&& 127).toNat = 42 := by decide
    have h4 : ¬(42 ≥ u64Limit) := by simp [u64Limit]
    simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true]
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 11) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_size
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [bind, Except.bind, pure, Except.pure] at hparse
  have hok := unpackWith_base_regular_ok hw rfl rfl rfl rfl 42 hparse
  refine ⟨_, hok, ?_⟩
  simp only [TarEquiv, entryEquivBool, show (EntryKind.regular == EntryKind.regular) = true from rfl,
    beq_self_eq_true, Bool.and_self]
  trivial

private theorem test5_case08_nulUid :
    let nulUid := patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "")
      108 8 (ByteArray.mk (Array.replicate 8 0)))
    ∃ res, unpackWith {} (nulUid ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular, uid := 0 }] res := by
  dsimp only
  let r : RawUstarHeader := { baseRaw baseChkField with fUid := ByteArray.mk (Array.replicate 8 0) }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with szUid := rfl }
  have heq_raw : patchHeaderChecksum (blitFixed (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 108 8
      (ByteArray.mk (Array.replicate 8 0))) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, blitFixed_raw_uid (baseRaw_wellSized baseChkField_size) rfl]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = ByteArray.mk (Array.replicate 8 0) := by
    simpa [h, RawUstarHeader.withChk, r] using (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = encodeOctalField 0 11 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 := by
    unfold parseUstarNumeric
    rw [hext_uid]
    rfl
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 11) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_size
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [bind, Except.bind, pure, Except.pure] at hparse
  have hok := unpackWith_base_regular_ok hw rfl rfl rfl rfl 0 hparse
  refine ⟨_, hok, ?_⟩
  simp only [TarEquiv, entryEquivBool, show (EntryKind.regular == EntryKind.regular) = true from rfl,
    beq_self_eq_true, Bool.and_self]
  trivial

private theorem test5_case09_hardlink (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      (patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 156 0x31) ++
        twoZeroBlocks) = .error err ∧
      err.kind = .unsupportedEntry ∧ (!err.message.isEmpty) = true := by
  let r : RawUstarHeader := { baseRaw baseChkField with fType := 0x31 }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with }
  have heq_raw : patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 156 0x31) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, set!_raw_type (baseRaw_wellSized baseChkField_size) 0x31]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = encodeOctalField 0 7 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = encodeOctalField 0 11 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_uid
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 11) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_size
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [bind, Except.bind, pure, Except.pure] at hparse
  change parseUstarHeader (h.toBytes ++ twoZeroBlocks) 0 =
    .ok { mode := 0o644, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x31 } at hparse
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 < (h.toBytes ++ twoZeroBlocks).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  rw [unpackWith_eq_unpackLoop hhdr_sz (by rw [twoZeroBlocks_size])]
  have hiz := isZeroRange_raw_zero_false hw (post := twoZeroBlocks) baseRaw_fName_nonzero
  have hstep : unpackStep opts (h.toBytes ++ twoZeroBlocks) 0 none [] [] 0 =
      .error { kind := .unsupportedEntry, message := "unsupported tar entry typeflag: 49", offset := some 0 } := by
    unfold unpackStep
    have hnot_ge : ¬(0 ≥ (h.toBytes ++ twoZeroBlocks).size) := by omega
    have hnot_gt : ¬(0 + 512 > (h.toBytes ++ twoZeroBlocks).size) := by
      rw [ByteArray.size_append, hhdr_sz]; omega
    simp only [hnot_ge, ↓reduceIte, hiz, Bool.false_eq_true, hnot_gt, hparse,
      show ((49 : UInt8) == 120) = false from rfl]
    unfold decodeTarEntry
    rfl
  exact ⟨_, unpackLoop_step_error hbd hstep, rfl, rfl⟩

private theorem test5_case10_globalPax (opts : UnpackOptions) :
    ∃ err, unpackWith opts
      (patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 156 0x67) ++
        twoZeroBlocks) = .error err ∧
      err.kind = .unsupportedEntry ∧ (!err.message.isEmpty) = true := by
  let r : RawUstarHeader := { baseRaw baseChkField with fType := 0x67 }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with }
  have heq_raw : patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 156 0x67) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, set!_raw_type (baseRaw_wellSized baseChkField_size) 0x67]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = encodeOctalField 0 7 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = encodeOctalField 0 11 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_uid
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 11) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_size
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [bind, Except.bind, pure, Except.pure] at hparse
  change parseUstarHeader (h.toBytes ++ twoZeroBlocks) 0 =
    .ok { mode := 0o644, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x67 } at hparse
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 < (h.toBytes ++ twoZeroBlocks).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  rw [unpackWith_eq_unpackLoop hhdr_sz (by rw [twoZeroBlocks_size])]
  have hiz := isZeroRange_raw_zero_false hw (post := twoZeroBlocks) baseRaw_fName_nonzero
  have hstep : unpackStep opts (h.toBytes ++ twoZeroBlocks) 0 none [] [] 0 =
      .error { kind := .unsupportedEntry, message := "unsupported tar entry typeflag: 103", offset := some 0 } := by
    unfold unpackStep
    have hnot_ge : ¬(0 ≥ (h.toBytes ++ twoZeroBlocks).size) := by omega
    have hnot_gt : ¬(0 + 512 > (h.toBytes ++ twoZeroBlocks).size) := by
      rw [ByteArray.size_append, hhdr_sz]; omega
    simp only [hnot_ge, ↓reduceIte, hiz, Bool.false_eq_true, hnot_gt, hparse,
      show ((103 : UInt8) == 120) = false from rfl]
    unfold decodeTarEntry
    rfl
  exact ⟨_, unpackLoop_step_error hbd hstep, rfl, rfl⟩

private theorem test5_case11_badDir (opts : UnpackOptions) :
    let badDir := patchHeaderChecksum (blitFixed ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 156 0x35)
      124 12 (encodeOctalField 5 11))
    ∃ err, unpackWith opts (badDir ++ padBlock512 "12345".toUTF8 ++ twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  dsimp only
  let r0 : RawUstarHeader := { baseRaw baseChkField with fType := 0x35 }
  have hr0 : r0.WellSized := { baseRaw_wellSized baseChkField_size with }
  let r : RawUstarHeader := { r0 with fSize := encodeOctalField 5 11 }
  have hrw : r.WellSized := { hr0 with szSize := encodeOctalField_size 5 11 }
  have heq_raw : patchHeaderChecksum (blitFixed ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 156 0x35)
      124 12 (encodeOctalField 5 11)) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, set!_raw_type (baseRaw_wellSized baseChkField_size) 0x35,
      blitFixed_raw_size hr0 (encodeOctalField_size 5 11)]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw, ByteArray.append_assoc]
  let post := padBlock512 "12345".toUTF8 ++ twoZeroBlocks
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have h5 : ("12345" : String).toUTF8.size = 5 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hpost_mod : post.size % 512 = 0 := by
    have hpb : (padBlock512 ("12345" : String).toUTF8).size = 512 := by
      rw [padBlock512_size, h5]; rfl
    simp only [post, ByteArray.size_append, hpb, twoZeroBlocks_size]
  have hext512 : (h.toBytes ++ post).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ post).extract 108 116 = encodeOctalField 0 7 := by
    simpa [h, RawUstarHeader.withChk, r, r0, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ post).extract 124 136 = encodeOctalField 5 11 := by
    simpa [h, RawUstarHeader.withChk, r] using (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ post) 108 116 0 true u64Limit "uid" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_uid
  have hsize : parseUstarNumeric (h.toBytes ++ post) 124 136 0 false u64Limit "size" = .ok 5 :=
    parseUstarNumeric_encodeOctalField (val := 5) (digits := 11) (limit := u64Limit)
      (by omega) (by decide) (by simp [u64Limit]) hext_size
  have hparse := parseUstarHeader_patched_steps hrw (post := post) rfl rfl rfl huid rfl hsize rfl
  dsimp only [bind, Except.bind, pure, Except.pure] at hparse
  change parseUstarHeader (h.toBytes ++ post) 0 =
    .ok { mode := 0o644, uid := 0, gid := 0, size := 5, mtime := 0, typeflag := 0x35 } at hparse
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 < (h.toBytes ++ post).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  rw [unpackWith_eq_unpackLoop hhdr_sz hpost_mod]
  have hiz := isZeroRange_raw_zero_false hw (post := post) baseRaw_fName_nonzero
  have hstep : unpackStep opts (h.toBytes ++ post) 0 none [] [] 0 =
      .error { kind := .invalidHeader, message := "non-regular tar entry has non-zero size", offset := some 0 } := by
    unfold unpackStep
    have hnot_ge : ¬(0 ≥ (h.toBytes ++ post).size) := by omega
    have hnot_gt : ¬(0 + 512 > (h.toBytes ++ post).size) := by
      rw [ByteArray.size_append, hhdr_sz]; omega
    simp only [hnot_ge, ↓reduceIte, hiz, Bool.false_eq_true, hnot_gt, hparse,
      show ((0x35 : UInt8) == 120) = false from rfl]
    unfold decodeTarEntry
    rfl
  exact ⟨_, unpackLoop_step_error hbd hstep, rfl, rfl⟩

private theorem extract_append_left_of_le (a b : ByteArray) {k : Nat} (hk : k ≤ a.size) :
    (a ++ b).extract 0 k = a.extract 0 k := by
  apply ByteArray.ext
  apply Array.ext
  · have hs1 : ((a ++ b).extract 0 k).data.size = ((a ++ b).extract 0 k).size := rfl
    have hs2 : (a.extract 0 k).data.size = (a.extract 0 k).size := rfl
    rw [hs1, hs2, ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_append]
    omega
  · intro i hi1 hi2
    have hi_a : i < (a.extract 0 k).size := hi2
    have hi_ab : i < ((a ++ b).extract 0 k).size := hi1
    rw [← ByteArray.getElem_eq_getElem_data, ← ByteArray.getElem_eq_getElem_data]
    rw [ByteArray.getElem_extract hi_ab, ByteArray.getElem_extract hi_a]
    simp only [Nat.zero_add]
    have hle : (a.extract 0 k).size ≤ k := by rw [ByteArray.size_extract]; omega
    exact ByteArray.getElem_append_left (by omega)

private theorem pad512_ge_self (n : Nat) : n ≤ pad512 n := by
  unfold pad512
  omega

private theorem unpackWith_mkPaxFrame_paxError {opts : UnpackOptions} {pax post : ByteArray}
    {err : TarError} (hsz : pax.size ≤ maxPaxHeaderBytes) (hpost : post.size % 512 = 0)
    (hpax : parsePaxPayload pax 0 = .error err) :
    unpackWith opts (mkPaxFrame pax ++ post) = .error err := by
  let paxHdr := mkUstarHeader "././@PaxHeader" 420 0 0 pax.size 0 120 "" "" "" ""
  have hhdr_sz : paxHdr.size = 512 := by
    dsimp only [paxHdr]
    rw [mkUstarHeader_eq_buildUstarHeader]
    exact buildUstarHeader_size _ _ _ _ _ _ _ _ _ _ _
  have heq_bytes : mkPaxFrame pax ++ post = paxHdr ++ (padBlock512 pax ++ post) := by
    simp [mkPaxFrame, paxHdr, ByteArray.append_assoc]
  have htail_mod : (padBlock512 pax ++ post).size % 512 = 0 := by
    rw [ByteArray.size_append, padBlock512_size]
    have hm := pad512_mod pax.size
    omega
  rw [heq_bytes, unpackWith_eq_unpackLoop hhdr_sz htail_mod]
  let bytes := paxHdr ++ (padBlock512 pax ++ post)
  have hbd512 : 0 + 512 ≤ bytes.size := by rw [ByteArray.size_append, hhdr_sz]; omega
  have hext512 : bytes.extract 0 512 = paxHdr := ByteArray.extract_append_eq_left hhdr_sz.symm
  have hiz := isZeroRange_mkUstarHeader_false hbd512 hext512
  have hlim : pax.size < ustarOctal11Limit := by
    have hm : maxPaxHeaderBytes = 1048576 := rfl
    have hu : ustarOctal11Limit = 8 ^ 11 := rfl
    omega
  have hparse := parseUstarHeader_mkUstarHeader (by decide) (by decide) hlim (by decide) hbd512 hext512
  have hpge := pad512_ge_self pax.size
  have hext_pax : bytes.extract 512 (512 + pax.size) = pax := by
    have h1 : bytes.extract paxHdr.size (paxHdr.size + pax.size) =
        (padBlock512 pax ++ post).extract 0 pax.size :=
      extract_append_right paxHdr (padBlock512 pax ++ post) pax.size
    rw [hhdr_sz] at h1
    rw [h1]
    have hle_pb : pax.size ≤ (padBlock512 pax).size := by rw [padBlock512_size]; exact hpge
    have h2 : (padBlock512 pax ++ post).extract 0 pax.size = (padBlock512 pax).extract 0 pax.size :=
      extract_append_left_of_le (padBlock512 pax) post hle_pb
    rw [h2, padBlock512_extract_prefix]
  have hstep : unpackStep opts bytes 0 none [] [] 0 = .error err := by
    unfold unpackStep
    have hnot_ge : ¬(0 ≥ bytes.size) := by omega
    have hnot_gt : ¬(0 + 512 > bytes.size) := by omega
    have hnot_max : ¬(pax.size > maxPaxHeaderBytes) := by omega
    have hnot_next : ¬(0 + 512 + pad512 pax.size > bytes.size) := by
      simp only [bytes, ByteArray.size_append, hhdr_sz, padBlock512_size]; omega
    simp only [hnot_ge, ↓reduceIte, hiz, Bool.false_eq_true, hnot_gt, hparse,
      show ((120 : UInt8) == 120) = true from rfl, Option.isSome_none, hnot_max,
      Nat.zero_add, hnot_next, hext_pax, hpax]
  exact unpackLoop_step_error (Nat.lt_of_lt_of_le (by omega) hbd512) hstep

private theorem test5_case12_paxSparse (opts : UnpackOptions) :
    ∃ err, unpackWith opts (mkPaxFrame (encodePaxRecord "GNU.sparse.major" "1") ++
      mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks) = .error err ∧
      err.kind = .unsupportedEntry ∧ (!err.message.isEmpty) = true := by
  have hpost : (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks).size % 512 = 0 := by
    rw [ByteArray.size_append, mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_size, twoZeroBlocks_size]
  have hpax : parsePaxPayload (encodePaxRecord "GNU.sparse.major" "1") 0 =
      .error { kind := .unsupportedEntry, message := "GNU sparse PAX archives are unsupported", offset := some 0 } := rfl
  rw [ByteArray.append_assoc]
  exact ⟨_, unpackWith_mkPaxFrame_paxError (by decide) hpost hpax, rfl, rfl⟩

private theorem test5_case13_paxNulUname (opts : UnpackOptions) :
    ∃ err, unpackWith opts (mkPaxFrame (encodePaxRecord "uname" "a\x00b") ++
      mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  have hpost : (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks).size % 512 = 0 := by
    rw [ByteArray.size_append, mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_size, twoZeroBlocks_size]
  have hpax : parsePaxPayload (encodePaxRecord "uname" "a\x00b") 0 =
      .error { kind := .invalidHeader, message := "NUL byte in PAX uname", offset := some 0 } := rfl
  rw [ByteArray.append_assoc]
  exact ⟨_, unpackWith_mkPaxFrame_paxError (by decide) hpost hpax, rfl, rfl⟩

private theorem test5_case14_paxDupPath (opts : UnpackOptions) :
    ∃ err, unpackWith opts (mkPaxFrame (encodePaxRecord "path" "a" ++ encodePaxRecord "path" "b") ++
      mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  have hpost : (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks).size % 512 = 0 := by
    rw [ByteArray.size_append, mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_size, twoZeroBlocks_size]
  have hpax : parsePaxPayload (encodePaxRecord "path" "a" ++ encodePaxRecord "path" "b") 0 =
      .error { kind := .invalidHeader, message := "duplicate PAX key: path", offset := some 0 } := rfl
  rw [ByteArray.append_assoc]
  exact ⟨_, unpackWith_mkPaxFrame_paxError (by decide) hpost hpax, rfl, rfl⟩

private theorem test5_case15_paxLeadZero (opts : UnpackOptions) :
    ∃ err, unpackWith opts (mkPaxFrame "09 path=a\n".toUTF8 ++
      mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks) = .error err ∧
      err.kind = .invalidHeader ∧ (!err.message.isEmpty) = true := by
  have hpost : (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks).size % 512 = 0 := by
    rw [ByteArray.size_append, mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_size, twoZeroBlocks_size]
  have hpax : parsePaxPayload "09 path=a\n".toUTF8 0 =
      .error { kind := .invalidHeader, message := "invalid PAX record length", offset := some 0 } := rfl
  rw [ByteArray.append_assoc]
  exact ⟨_, unpackWith_mkPaxFrame_paxError (by decide) hpost hpax, rfl, rfl⟩

private theorem unpackStep_nonPax_ok
    (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hbd : offset + 512 ≤ bytes.size)
    (hnz : isZeroRange bytes offset 512 = false)
    {hdr : UstarHeaderFields} (htf_not78 : (hdr.typeflag == 0x78) = false)
    (hparse : parseUstarHeader bytes offset = .ok hdr)
    {entry : TarEntry} {stepSize : Nat}
    (hdec : decodeTarEntry opts bytes offset hdr pendingPax seen acc.length totalBytes = .ok (entry, stepSize)) :
    unpackStep opts bytes offset pendingPax seen acc totalBytes =
      .ok (.cont (offset + 512 + stepSize) none (entry.path :: seen) (entry :: acc)
        (totalBytes + entry.data.size)) := by
  have hnotge : ¬(offset ≥ bytes.size) := by omega
  have hnotgt512 : ¬(offset + 512 > bytes.size) := by omega
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt512, hparse, htf_not78, hdec]

private def case16Pax : ByteArray :=
  encodePaxRecord "mtime" "1794744353.8699822" ++ encodePaxRecord "SCHILY.xattr.user" "ok"

private def case16ValidPax : ByteArray := mkPaxFrame case16Pax

private def case16BaseHdr : ByteArray := mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" ""

private theorem test5_case16_validPax :
    let validPax := mkPaxFrame (encodePaxRecord "mtime" "1794744353.8699822" ++ encodePaxRecord "SCHILY.xattr.user" "ok")
    let baseHdr := mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" ""
    ∃ res, unpackWith {} (validPax ++ baseHdr ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular, mtime := 1794744353 }] res := by
  change ∃ res, unpackWith {} (case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks) = .ok res ∧
    TarEquiv [{ path := "a.txt", kind := .regular, mtime := 1794744353 }] res
  have hpax_sz_eq : case16Pax.size = 52 := by decide
  have hvp_sz : case16ValidPax.size = 1024 := by
    dsimp only [case16ValidPax, mkPaxFrame]
    rw [ByteArray.size_append, mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_size,
      padBlock512_size, hpax_sz_eq]
    decide
  have hbase_sz : case16BaseHdr.size = 512 := by
    dsimp only [case16BaseHdr]; rw [mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_size]
  have hfull_sz : (case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks).size = 2560 := by
    rw [ByteArray.size_append, ByteArray.size_append, hvp_sz, hbase_sz, twoZeroBlocks_size]
  have hunp : unpackWith {} (case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks) =
      unpackLoop {} (case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks) 0 none [] [] 0 := by
    unfold LeanSwe.Tar.unpackWith Impl.unpackWith
    have hne0 : ((case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks).size == 0) = false := by
      rw [hfull_sz]; decide
    have hmod : ((case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks).size % 512 != 0) = false := by
      rw [hfull_sz]; decide
    simp only [hne0, hmod, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  have hpax_sz : case16Pax.size ≤ maxPaxHeaderBytes := by rw [hpax_sz_eq]; decide
  have hpax_ok : parsePaxPayload case16Pax 0 = .ok { mtime? := some 1794744353 } := rfl
  have hstep1 : unpackLoop {} (case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks) 0 none [] [] 0 =
      unpackLoop {} (case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks) 1024
        (some { mtime? := some 1794744353 }) [] [] 0 := by
    have hpre := unpackLoop_mkPaxFrame_step {} ByteArray.empty (case16BaseHdr ++ twoZeroBlocks) case16Pax [] [] 0
      hpax_sz { mtime? := some 1794744353 } hpax_ok
    have hzero : ByteArray.empty.size = 0 := rfl
    have hvp_pad : 512 + pad512 case16Pax.size = 1024 := by rw [hpax_sz_eq]; decide
    rw [hzero, Nat.zero_add, hvp_pad, ByteArray.empty_append, ← ByteArray.append_assoc] at hpre
    exact hpre
  let bytes := case16ValidPax ++ case16BaseHdr ++ twoZeroBlocks
  have hbd2 : 1024 + 512 ≤ bytes.size := by rw [show bytes.size = 2560 from hfull_sz]; omega
  have hext2 : bytes.extract 1024 (1024 + 512) = case16BaseHdr := by
    have ha : bytes = case16ValidPax ++ (case16BaseHdr ++ twoZeroBlocks) := ByteArray.append_assoc
    rw [ha, ← hvp_sz, extract_append_right]
    exact ByteArray.extract_append_eq_left hbase_sz.symm
  have hiz2 := isZeroRange_mkUstarHeader_false hbd2 hext2
  have hparse2 := parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide) hbd2 hext2
  have hp0 : pad512 0 = 0 := rfl
  have hdec2 := decodeTarEntry_mkUstarHeader_regular {} bytes case16BaseHdr 1024
    (some { mtime? := some 1794744353 }) [] 0 0 hbd2 hext2 rfl
    (by rw [aTxt_utf8_size]; omega) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl (by change 0 + 1 ≤ 100000; omega) (by change 0 + 0 ≤ 256 * 1024 * 1024; omega)
    (by dsimp only [Option.bind, Option.getD]; rw [hp0]; omega)
  dsimp only [Option.bind, Option.getD] at hdec2
  rw [hp0, ite_eq_left (by decide : ((0 == 0) = true)),
    String.ofList_toList,
    show (((0o644 : UInt32) &&& 0o7777).toNat.toUInt32) = 0o644 from by decide] at hdec2
  let entry : TarEntry := { path := "a.txt", kind := .regular, mtime := 1794744353 }
  have hstep2 : unpackStep {} bytes 1024 (some { mtime? := some 1794744353 }) [] [] 0 =
      .ok (.cont (1024 + 512) none ["a.txt"] [entry] 0) := by
    have hs := unpackStep_nonPax_ok {} bytes 1024 (some { mtime? := some 1794744353 }) [] [] 0
      hbd2 hiz2 (show ((0x30 : UInt8) == 0x78) = false from rfl) hparse2
      (by simpa only [List.length_nil] using hdec2)
    rw [hs, show (1024 : Nat) + 512 + 0 = 1024 + 512 from rfl,
      show (0 : Nat) + (ByteArray.empty).size = 0 from rfl]
  have hdone : unpackLoop {} bytes (1024 + 512) none ["a.txt"] [entry] 0 = .ok [entry] := by
    have ha : bytes = (case16ValidPax ++ case16BaseHdr) ++ (zeroBlock ++ zeroBlock) := by
      simp only [bytes, twoZeroBlocks]
    have hszp : (case16ValidPax ++ case16BaseHdr).size = 1024 + 512 := by
      rw [ByteArray.size_append, hvp_sz, hbase_sz]
    rw [ha, ← hszp]
    exact unpackLoop_at_twoZeroBlocks {} (case16ValidPax ++ case16BaseHdr) ["a.txt"] [entry] 0
  have hres : unpackWith {} bytes = .ok [entry] := by
    have hbd_res : 1024 < bytes.size := by rw [show bytes.size = 2560 from hfull_sz]; omega
    rw [hunp, hstep1, unpackLoop_step_cont hbd_res (by omega) hstep2, hdone]
  refine ⟨_, hres, ?_⟩
  dsimp only [entry]
  simp only [TarEquiv, entryEquivBool, show (EntryKind.regular == EntryKind.regular) = true from rfl,
    beq_self_eq_true, Bool.and_self]
  trivial

private def badNamePat : ByteArray :=
  (padRightBytes 100 ("a.txt" : String).toUTF8).set! 0 0xff

private theorem badNamePat_size : badNamePat.size = 100 := by
  dsimp only [badNamePat]; rw [ByteArray.size_set!, padRightBytes_size]

private theorem badNamePat_0 : badNamePat[0]'(by rw [badNamePat_size]; decide) = 0xff := by decide
private theorem badNamePat_1 : badNamePat[1]'(by rw [badNamePat_size]; decide) = 0x2e := by decide
private theorem badNamePat_2 : badNamePat[2]'(by rw [badNamePat_size]; decide) = 0x74 := by decide
private theorem badNamePat_3 : badNamePat[3]'(by rw [badNamePat_size]; decide) = 0x78 := by decide
private theorem badNamePat_4 : badNamePat[4]'(by rw [badNamePat_size]; decide) = 0x74 := by decide
private theorem badNamePat_5 : badNamePat[5]'(by rw [badNamePat_size]; decide) = 0x00 := by decide
private theorem badNamePat_0_ne : badNamePat[0]'(by rw [badNamePat_size]; decide) ≠ 0 := by decide

private theorem extractCStringBytes_badUtf8Name {bytes : ByteArray}
    (hbd : 100 ≤ bytes.size) (hext : bytes.extract 0 100 = badNamePat) :
    extractCStringBytes bytes 0 100 = ByteArray.mk #[0xff, 0x2e, 0x74, 0x78, 0x74] := by
  have hpat_sz := badNamePat_size
  have hget : ∀ i (hi : i < 100), bytes[i]'(by omega) = badNamePat[i]'(by rw [hpat_sz]; exact hi) := by
    intro i hi
    have hie : i < (bytes.extract 0 100).size := by rw [hext, hpat_sz]; exact hi
    have h0 := ByteArray.getElem_extract hie
    rw [byteArray_getElem_of_eq hext hie (by rw [hpat_sz]; exact hi)] at h0
    simp only [Nat.zero_add] at h0
    exact h0.symm
  have hb0 : bytes[0]'(by omega) = 0xff := by rw [hget 0 (by omega)]; exact badNamePat_0
  have hb1 : bytes[1]'(by omega) = 0x2e := by rw [hget 1 (by omega)]; exact badNamePat_1
  have hb2 : bytes[2]'(by omega) = 0x74 := by rw [hget 2 (by omega)]; exact badNamePat_2
  have hb3 : bytes[3]'(by omega) = 0x78 := by rw [hget 3 (by omega)]; exact badNamePat_3
  have hb4 : bytes[4]'(by omega) = 0x74 := by rw [hget 4 (by omega)]; exact badNamePat_4
  have hb5 : bytes[5]'(by omega) = 0x00 := by rw [hget 5 (by omega)]; exact badNamePat_5
  have hfind : extractCStringBytes.findNul bytes 100 100 0 = 5 := by
    rw [extractCStringBytes.findNul.eq_2]; simp [show (0 : Nat) < bytes.size by omega, hb0]
    rw [extractCStringBytes.findNul.eq_2]; simp [show (1 : Nat) < bytes.size by omega, hb1]
    rw [extractCStringBytes.findNul.eq_2]; simp [show (2 : Nat) < bytes.size by omega, hb2]
    rw [extractCStringBytes.findNul.eq_2]; simp [show (3 : Nat) < bytes.size by omega, hb3]
    rw [extractCStringBytes.findNul.eq_2]; simp [show (4 : Nat) < bytes.size by omega, hb4]
    rw [extractCStringBytes.findNul.eq_2]; simp [show (5 : Nat) < bytes.size by omega, hb5]
  unfold extractCStringBytes
  rw [Nat.sub_zero, hfind]
  have hext5 : bytes.extract 0 5 = badNamePat.extract 0 5 := by
    have h1 : bytes.extract 0 5 = (bytes.extract 0 100).extract 0 5 := by
      rw [ByteArray.extract_extract]; simp
    rw [h1, hext]
  rw [hext5]
  decide

private theorem test5_case17_badUtf8Name :
    ∃ err, unpackWith {}
      (patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 0 0xff) ++
        twoZeroBlocks) = .error err ∧
      err.kind = .invalidEncoding ∧ (!err.message.isEmpty) = true := by
  have hbn_sz : badNamePat.size = 100 := by
    dsimp only [badNamePat]; rw [ByteArray.size_set!, padRightBytes_size]
  let r : RawUstarHeader := { baseRaw baseChkField with fName := badNamePat }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with szName := hbn_sz }
  have heq_raw : patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 0 0xff) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw, set!_raw_name (baseRaw_wellSized baseChkField_size) (by omega) 0xff]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_name : (h.toBytes ++ twoZeroBlocks).extract 0 100 = badNamePat := by
    simpa [Nat.zero_add, h, RawUstarHeader.withChk, r] using (raw_extract_fields hw hext512).1
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = encodeOctalField 0 7 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = encodeOctalField 0 11 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.1
  have hext_uname : (h.toBytes ++ twoZeroBlocks).extract 265 297 = padRightBytes 32 ("" : String).toUTF8 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.2.2.2.2.2.2.1
  have hext_gname : (h.toBytes ++ twoZeroBlocks).extract 297 329 = padRightBytes 32 ("" : String).toUTF8 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.2.2.2.2.2.2.2.1
  have hext_pfx : (h.toBytes ++ twoZeroBlocks).extract 345 500 = padRightBytes 155 ("" : String).toUTF8 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.2.2.2.2.2.2.2.2
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_uid
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 11) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_size
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [bind, Except.bind, pure, Except.pure] at hparse
  change parseUstarHeader (h.toBytes ++ twoZeroBlocks) 0 =
    .ok { mode := 0o644, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x30 } at hparse
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hbd : 0 < (h.toBytes ++ twoZeroBlocks).size := by rw [ByteArray.size_append, hhdr_sz]; omega
  rw [unpackWith_eq_unpackLoop hhdr_sz (by rw [twoZeroBlocks_size])]
  have hnz : ∃ hsz : 0 < h.fName.size, h.fName[0]'hsz ≠ 0 := by
    have hsz : 0 < h.fName.size := by rw [hw.szName]; omega
    refine ⟨hsz, ?_⟩
    have hget0 : h.fName[0]'hsz = badNamePat[0]'(by rw [badNamePat_size]; decide) := rfl
    rw [hget0]
    exact badNamePat_0_ne
  have hiz := isZeroRange_raw_zero_false hw (post := twoZeroBlocks) hnz
  have hdn : decodeCStringUtf8 (h.toBytes ++ twoZeroBlocks) 0 100 0 "name" =
      .error { kind := .invalidEncoding, message := "invalid UTF-8 in USTAR name", offset := some 0 } := by
    unfold decodeCStringUtf8
    rw [extractCStringBytes_badUtf8Name (by rw [ByteArray.size_append, hhdr_sz]; omega) hext_name]
    rfl
  have hdu : decodeCStringUtf8 (h.toBytes ++ twoZeroBlocks) 265 297 0 "uname" = .ok "" :=
    decodeCStringUtf8_padRightBytes (start := 265) (w := 32) (s := "") (fieldName := "uname")
      (by decide) (by rw [empty_utf8_size]; omega) (by rw [ByteArray.size_append, hhdr_sz]; omega) hext_uname
  have hdg : decodeCStringUtf8 (h.toBytes ++ twoZeroBlocks) 297 329 0 "gname" = .ok "" :=
    decodeCStringUtf8_padRightBytes (start := 297) (w := 32) (s := "") (fieldName := "gname")
      (by decide) (by rw [empty_utf8_size]; omega) (by rw [ByteArray.size_append, hhdr_sz]; omega) hext_gname
  have hdp : decodeCStringUtf8 (h.toBytes ++ twoZeroBlocks) 345 500 0 "prefix" = .ok "" :=
    decodeCStringUtf8_padRightBytes (start := 345) (w := 155) (s := "") (fieldName := "prefix")
      (by decide) (by rw [empty_utf8_size]; omega) (by rw [ByteArray.size_append, hhdr_sz]; omega) hext_pfx
  have hle_ent : ¬(1 > ({} : UnpackOptions).maxEntries) := by change ¬(1 > 100000); omega
  have hle_tot : ¬(0 > ({} : UnpackOptions).maxTotalBytes) := by change ¬(0 > 256 * 1024 * 1024); omega
  have hp0 : pad512 0 = 0 := rfl
  have hnot_pay : ¬(512 + 0 > (h.toBytes ++ twoZeroBlocks).size) := by rw [ByteArray.size_append, hhdr_sz]; omega
  have hstep : unpackStep {} (h.toBytes ++ twoZeroBlocks) 0 none [] [] 0 =
      .error { kind := .invalidEncoding, message := "invalid UTF-8 in USTAR name", offset := some 0 } := by
    unfold unpackStep
    have hnot_ge : ¬(0 ≥ (h.toBytes ++ twoZeroBlocks).size) := by omega
    have hnot_gt : ¬(0 + 512 > (h.toBytes ++ twoZeroBlocks).size) := by
      rw [ByteArray.size_append, hhdr_sz]; omega
    simp only [hnot_ge, ↓reduceIte, hiz, Bool.false_eq_true, hnot_gt, hparse,
      show ((0x30 : UInt8) == 120) = false from rfl]
    unfold decodeTarEntry
    simp only [Nat.zero_add, List.length_nil, beq_self_eq_true, Bool.true_or, ↓reduceIte, Option.getD_none,
      bne_self_eq_false, hle_ent, hle_tot, hp0, hnot_pay, hdn, hdu, hdg, hdp]
    rfl
  exact ⟨_, unpackLoop_step_error hbd hstep, rfl, rfl⟩

private theorem test5_case18_garbageLink :
    let garbageLink := patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 157 0xff)
    ∃ res, unpackWith {} (garbageLink ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular }] res := by
  dsimp only
  let badLink := (padRightBytes 100 ("" : String).toUTF8).set! 0 0xff
  have hbl_sz : badLink.size = 100 := by rw [ByteArray.size_set!, padRightBytes_size]
  let r : RawUstarHeader := { baseRaw baseChkField with fLink := badLink }
  have hrw : r.WellSized := { baseRaw_wellSized baseChkField_size with szLink := hbl_sz }
  have heq_raw : patchHeaderChecksum ((mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "").set! 157 0xff) =
      (r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])).toBytes := by
    rw [baseHdr_eq_raw]
    have h := set!_raw_link (baseRaw_wellSized baseChkField_size) (k := 0) (by omega) 0xff
    simp only [Nat.add_zero] at h
    rw [h]
    exact patchHeaderChecksum_raw hrw
  rw [heq_raw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size _)
  have hext512 : (h.toBytes ++ twoZeroBlocks).extract 0 512 = h.toBytes :=
    ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hext_uid : (h.toBytes ++ twoZeroBlocks).extract 108 116 = encodeOctalField 0 7 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.1
  have hext_size : (h.toBytes ++ twoZeroBlocks).extract 124 136 = encodeOctalField 0 11 := by
    simpa [h, RawUstarHeader.withChk, r, baseRaw, RawUstarHeader.ofFields] using
      (raw_extract_fields hw hext512).2.2.2.2.1
  have huid : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 108 116 0 true u64Limit "uid" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 7) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_uid
  have hsize : parseUstarNumeric (h.toBytes ++ twoZeroBlocks) 124 136 0 false u64Limit "size" = .ok 0 :=
    parseUstarNumeric_encodeOctalField (val := 0) (digits := 11) (limit := u64Limit)
      (by omega) (Nat.pow_pos (by omega)) (by simp [u64Limit]) hext_size
  have hparse := parseUstarHeader_patched_steps hrw (post := twoZeroBlocks) rfl rfl rfl huid rfl hsize rfl
  dsimp only [bind, Except.bind, pure, Except.pure] at hparse
  have hok := unpackWith_base_regular_ok hw rfl rfl rfl rfl 0 hparse
  refine ⟨_, hok, ?_⟩
  simp only [TarEquiv, entryEquivBool, show (EntryKind.regular == EntryKind.regular) = true from rfl,
    beq_self_eq_true, Bool.and_self]
  trivial

private theorem allPass_test5_for (api : TarApi)
    (hapi : api.unpackWith = LeanSwe.Tar.unpackWith ∧ api.unpack = LeanSwe.Tar.unpackWith {}) :
    Core.AllPass (test_tar_unpackWith_checksumNumericAndUnsupported_validated api) := by
  rcases hapi with ⟨hapi_w, hapi_u⟩
  unfold test_tar_unpackWith_checksumNumericAndUnsupported_validated
  dsimp only
  rcases test5_case01_badChkVal {} with ⟨e1, h1u, h1k, h1m⟩
  rcases test5_case02_badChkSyntax {} with ⟨e2, h2u, h2k, h2m⟩
  rcases test5_case03_allNulChk {} with ⟨e3, h3u, h3k, h3m⟩
  rcases test5_case04_badMagic {} with ⟨e4, h4u, h4k, h4m⟩
  rcases test5_case05_negBase256 {} with ⟨e5, h5u, h5k, h5m⟩
  rcases test5_case06_posBase256Uid with ⟨r6, h6u, h6t⟩
  rcases test5_case07_nulSize {} with ⟨e7, h7u, h7k, h7m⟩
  rcases test5_case08_nulUid with ⟨r8, h8u, h8t⟩
  rcases test5_case09_hardlink {} with ⟨e9, h9u, h9k, h9m⟩
  rcases test5_case10_globalPax {} with ⟨e10, h10u, h10k, h10m⟩
  rcases test5_case11_badDir {} with ⟨e11, h11u, h11k, h11m⟩
  rcases test5_case12_paxSparse {} with ⟨e12, h12u, h12k, h12m⟩
  rcases test5_case13_paxNulUname {} with ⟨e13, h13u, h13k, h13m⟩
  rcases test5_case14_paxDupPath {} with ⟨e14, h14u, h14k, h14m⟩
  rcases test5_case15_paxLeadZero {} with ⟨e15, h15u, h15k, h15m⟩
  rcases test5_case16_validPax with ⟨r16, h16u, h16t⟩
  rcases test5_case17_badUtf8Name with ⟨e17, h17u, h17k, h17m⟩
  rcases test5_case18_garbageLink with ⟨r18, h18u, h18t⟩
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h1u) h1k h1m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h2u) h2k h2m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h3u) h3k h3m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h4u) h4k h4m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h5u) h5k h5m ?_
  rw [hapi_u, h6u]
  dsimp only
  refine allPass_assert_bind _ _ |>.mpr ⟨h6t, ?_⟩
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h7u) h7k h7m ?_
  rw [h8u]
  dsimp only
  refine allPass_assert_bind _ _ |>.mpr ⟨h8t, ?_⟩
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h9u) h9k h9m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h10u) h10k h10m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h11u) h11k h11m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h12u) h12k h12m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h13u) h13k h13m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h14u) h14k h14m ?_
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h15u) h15k h15m ?_
  rw [h16u]
  dsimp only
  refine allPass_assert_bind _ _ |>.mpr ⟨h16t, ?_⟩
  refine allPass_checkUnpackError_bind (by rw [hapi_w]; exact h17u) h17k h17m ?_
  rw [h18u]
  dsimp only
  dsimp only [Core.AllPass]
  exact ⟨h18t, trivial⟩

/-- Semantic validation theorem for `test_tar_unpackWith_checksumNumericAndUnsupported_validated`. -/
theorem allPass_unpackWith_checksumNumericAndUnsupported_validated :
    Core.AllPass (test_tar_unpackWith_checksumNumericAndUnsupported_validated defaultApi) :=
  allPass_test5_for defaultApi ⟨rfl, rfl⟩

end LeanSwe.Tar.Proofs
