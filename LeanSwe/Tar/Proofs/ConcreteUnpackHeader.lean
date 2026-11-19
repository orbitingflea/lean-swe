import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.ConcreteUnpack

namespace LeanSwe.Tar.Proofs

open Core Core.NondetTest LeanSwe.Tar LeanSwe.Tar.Model LeanSwe.Tar.Impl

private theorem blitFixed_raw_chk {h : RawUstarHeader} (hw : h.WellSized) {src : ByteArray} (hsrc : src.size = 8) :
    blitFixed h.toBytes 148 8 src = (h.withChk src).toBytes := by
  let L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime
  have hL : L.size = 148 := by simp [L, ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime]
  simpa [RawUstarHeader.toBytes, RawUstarHeader.withChk, L, ByteArray.append_assoc, blitFixed_exact hw.szChk hsrc] using blitFixed_append_mid L h.fChk _ src hL hw.szChk
private theorem set!_raw_name0 {h : RawUstarHeader} (hw : h.WellSized) (v : UInt8) :
    h.toBytes.set! 0 v = { h with fName := h.fName.set! 0 v }.toBytes := by
  simpa [RawUstarHeader.toBytes, ByteArray.append_assoc] using set!_append_mid ByteArray.empty h.fName _ 0 v (by rw [hw.szName]; decide)
private theorem set!_raw_link0 {h : RawUstarHeader} (hw : h.WellSized) (v : UInt8) :
    h.toBytes.set! 157 v = { h with fLink := h.fLink.set! 0 v }.toBytes := by
  let L := h.fName ++ h.fMode ++ h.fUid ++ h.fGid ++ h.fSize ++ h.fMtime ++ h.fChk ++ ByteArray.mk #[h.fType]
  have hL : L.size = 157 := by simp [L, ByteArray.size_append, hw.szName, hw.szMode, hw.szUid, hw.szGid, hw.szSize, hw.szMtime, hw.szChk]; rfl
  have hs := set!_append_mid L h.fLink (h.fMagic ++ h.fVer ++ h.fUname ++ h.fGname ++ h.fDev ++ h.fPrefix ++ h.fPad) 0 v (by rw [hw.szLink]; decide)
  rw [hL, Nat.add_zero] at hs; simpa [RawUstarHeader.toBytes, L, ByteArray.append_assoc] using hs

private theorem foldl_octal_ge (xs : List UInt8) (init : Nat) :
    init * 8 ^ xs.length ≤ xs.foldl (fun acc b => acc * 8 + (b.toNat - 48)) init := by
  induction xs generalizing init with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]; have hstep := ih (init * 8 + (b.toNat - 48))
    have hm : init * (8 ^ bs.length * 8) ≤ (init * 8 + (b.toNat - 48)) * 8 ^ bs.length := by
      rw [Nat.mul_comm (8 ^ bs.length) 8, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    omega
private theorem byteArray_set0_toList {b : ByteArray} (v : UInt8) (h0 : 0 < b.size) : (b.set! 0 v).data.toList = v :: b.data.toList.tail := by
  rcases b with ⟨⟨_ | ⟨x, xs⟩⟩⟩
  · exact absurd h0 (by decide)
  · simp [ByteArray.set!, Array.setIfInBounds]
private theorem encodeOctalField_6_sp_size (v : Nat) : (encodeOctalField v 6 ++ ByteArray.mk #[0x20]).size = 8 := by
  rw [ByteArray.size_append, encodeOctalField_size]; rfl

private def baseRaw (chk : ByteArray) : RawUstarHeader := RawUstarHeader.ofFields "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" chk
private theorem baseRaw_wellSized {chk : ByteArray} (hchk : chk.size = 8) : (baseRaw chk).WellSized := RawUstarHeader.ofFields_wellSized hchk
private def baseChkField : ByteArray :=
  encodeOctalField (ustarChecksumAt (baseRaw (ByteArray.mk (Array.replicate 8 0x20))).toBytes 0) 6 ++ ByteArray.mk #[0x20]
private theorem baseChkField_size : baseChkField.size = 8 := encodeOctalField_6_sp_size _
private theorem baseRaw_hw : (baseRaw baseChkField).WellSized := baseRaw_wellSized baseChkField_size
private theorem baseHdr_eq_raw : mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" = (baseRaw baseChkField).toBytes := by
  rw [mkUstarHeader_eq_buildUstarHeader, buildUstarHeader_eq_raw]; rfl

private theorem isZeroRange_raw_zero_false {h : RawUstarHeader} (hw : h.WellSized)
    {post : ByteArray} (h0 : ∃ hsz : 0 < h.fName.size, h.fName[0]'hsz ≠ 0) : isZeroRange (h.toBytes ++ post) 0 512 = false := by
  rcases h0 with ⟨hsz, hne⟩; have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  have hext_name := (raw_extract_fields hw (ByteArray.extract_append_eq_left (b := post) hhdr_sz.symm)).1
  have hb0_e : 0 < ((h.toBytes ++ post).extract 0 100).size := by rw [hext_name]; exact hsz
  have hb0 : (h.toBytes ++ post)[0]'(by rw [ByteArray.size_append, hhdr_sz]; omega) = h.fName[0]'hsz := by
    have hg := ByteArray.getElem_extract hb0_e; rw [byteArray_getElem_of_eq hext_name hb0_e hsz] at hg; simpa using hg.symm
  exact isZeroRange_false_of_ne (i := 0) (by omega) (by rw [ByteArray.size_append, hhdr_sz]; omega) (by rw [hb0]; exact hne)
private theorem baseRaw_fName_nonzero :
    ∃ hsz : 0 < (padRightBytes 100 ("a.txt" : String).toUTF8).size, (padRightBytes 100 ("a.txt" : String).toUTF8)[0]'hsz ≠ 0 := by
  refine ⟨by rw [padRightBytes_size]; omega, ?_⟩; rw [padRightBytes_getElem 100 _ (by omega)]
  have h5 : 0 < ("a.txt" : String).toUTF8.size := by decide
  have hb : ("a.txt" : String).toUTF8[0]'(by decide) = 0x61 := by decide
  simp only [h5, ↓reduceDIte, hb]; decide

private theorem unpackWith_raw_err {h : RawUstarHeader} (hw : h.WellSized) {post : ByteArray} {err : TarError}
    (hpost : post.size % 512 = 0) (hnz : ∃ hsz : 0 < h.fName.size, h.fName[0]'hsz ≠ 0)
    (herr : parseUstarHeader (h.toBytes ++ post) 0 = .error err ∨
      ∃ hdr, (hdr.typeflag == 0x78) = false ∧ parseUstarHeader (h.toBytes ++ post) 0 = .ok hdr ∧
        decodeTarEntry {} (h.toBytes ++ post) 0 hdr none [] 0 0 = .error err) : Impl.unpackWith {} (h.toBytes ++ post) = .error err := by
  obtain ⟨bytes, hbytes⟩ : ∃ b, b = h.toBytes ++ post := ⟨_, rfl⟩; rw [← hbytes] at herr ⊢
  have hsz : bytes.size = 512 + post.size := by rw [hbytes, ByteArray.size_append, RawUstarHeader.toBytes_size hw]
  rw [unpackWith_eq_unpackLoop (by rw [hsz]; omega) (by rw [hsz]; omega)]
  refine unpackLoop_step_err {} bytes 0 none [] [] 0 err (by rw [hsz]; omega) ?_
  have hiz : isZeroRange bytes 0 512 = false := by rw [hbytes]; exact isZeroRange_raw_zero_false hw hnz
  have hng1 : ¬(0 ≥ bytes.size) := by rw [hsz]; omega
  have hng2 : ¬(0 + 512 > bytes.size) := by rw [hsz]; omega
  unfold unpackStep; simp only [hng1, ↓reduceIte, hiz, Bool.false_eq_true, hng2, List.length_nil]
  rcases herr with hp | ⟨hdr, htf, hp, hd⟩
  · rw [hp]
  · rw [hp]; dsimp only; rw [htf, ite_eq_right Bool.false_ne_true, hd]

private theorem parseUstarHeader_patched {r : RawUstarHeader} (hrw : r.WellSized)
    {post : ByteArray} (tf : UInt8) (magOk : Bool) {resUid resSize : Except TarError Nat}
    (hmag : ((r.fMagic.data.toList == [0x75, 0x73, 0x74, 0x61, 0x72, 0x00] && r.fVer.data.toList == [0x30, 0x30]) ||
             (r.fMagic.data.toList == [0x75, 0x73, 0x74, 0x61, 0x72, 0x20] && r.fVer.data.toList == [0x20, 0x00])) = magOk := by rfl)
    (hmode : r.fMode = encodeOctalField 0o644 7 := by rfl) (hgid : r.fGid = encodeOctalField 0 7 := by rfl)
    (hmtime : r.fMtime = encodeOctalField 0 11 := by rfl) (htf : r.fType = tf := by rfl)
    (huid : ∀ b : ByteArray, b.extract (0 + 108) (0 + 116) = r.fUid → parseUstarNumeric b (0 + 108) (0 + 116) 0 true u64Limit "uid" = resUid :=
      by intro b hx; unfold parseUstarNumeric; rw [hx]; rfl)
    (hsize : ∀ b : ByteArray, b.extract (0 + 124) (0 + 136) = r.fSize → parseUstarNumeric b (0 + 124) (0 + 136) 0 false u64Limit "size" = resSize :=
      by intro b hx; unfold parseUstarNumeric; rw [hx]; rfl) :
    parseUstarHeader (patchHeaderChecksum r.toBytes ++ post) 0 =
      if !magOk then .error { kind := .invalidHeader, message := "invalid USTAR magic or version", offset := some 0 }
      else resUid.bind fun u => resSize.bind fun s => .ok { mode := 0o644, uid := u, gid := 0, size := s, mtime := 0, typeflag := tf } := by
  rw [patchHeaderChecksum_raw hrw]
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size (ustarChecksum r.toBytes))
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  obtain ⟨bytes, hbytes⟩ : ∃ b, b = h.toBytes ++ post := ⟨_, rfl⟩; rw [← hbytes]
  have hbd : 0 + 512 ≤ bytes.size := by rw [hbytes, ByteArray.size_append, hhdr_sz]; omega
  have hext512 : bytes.extract 0 512 = h.toBytes := by rw [hbytes]; exact ByteArray.extract_append_eq_left hhdr_sz.symm
  have ⟨_, hext_mode, hext_uid, hext_gid, hext_size, hext_mtime, hext_chk, _, hext_magic, hext_ver, _, _, _⟩ := raw_extract_fields hw hext512
  have hchk_ok : parseChecksumOctal bytes (0 + 148) (0 + 156) 0 = .ok (ustarChecksum r.toBytes) :=
    parseChecksumOctal_encodeOctalField (ustarChecksum_lt _) hext_chk
  have hcsum_eq : ustarChecksumAt bytes 0 = ustarChecksum r.toBytes :=
    raw_ustarChecksumAt_eq hrw (encodeOctalField_6_sp_size (ustarChecksum r.toBytes)) hrw.szChk hbd hext512
  have hmagic_eq : hasValidMagic bytes 0 = magOk := by
    unfold hasValidMagic; rw [hext_magic, hext_ver, show h.fMagic = r.fMagic from rfl, show h.fVer = r.fVer from rfl]; exact hmag
  unfold parseUstarHeader; rw [hchk_ok]; dsimp only [bind, Except.bind, pure, Except.pure]
  cases magOk
  · simp only [hcsum_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hmagic_eq, Bool.not_false]; rfl
  · have hmode_ok : parseUstarNumeric bytes (0 + 100) (0 + 108) 0 false u32Limit "mode" = .ok 0o644 := by
      unfold parseUstarNumeric; rw [hext_mode, show h.fMode = r.fMode from rfl, hmode]; rfl
    have hgid_ok : parseUstarNumeric bytes (0 + 116) (0 + 124) 0 true u64Limit "gid" = .ok 0 := by
      unfold parseUstarNumeric; rw [hext_gid, show h.fGid = r.fGid from rfl, hgid]; rfl
    have hmtime_ok : parseUstarNumeric bytes (0 + 136) (0 + 148) 0 true u64Limit "mtime" = .ok 0 := by
      unfold parseUstarNumeric; rw [hext_mtime, show h.fMtime = r.fMtime from rfl, hmtime]; rfl
    have htype : bytes[0 + 156]'(by omega) = tf := (raw_getElem_type hw hbd hext512).trans htf
    have h156 : 0 + 156 < bytes.size := by omega
    simp only [hcsum_eq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hmagic_eq, Bool.not_true, hmode_ok, huid bytes hext_uid]
    cases resUid with
    | error _ => rfl
    | ok u => dsimp only; simp only [hgid_ok, hsize bytes hext_size]; cases resSize with
      | error _ => rfl
      | ok s => simp only [hmtime_ok, h156, ↓reduceDIte, htype]

private theorem unpackWith_patched_err {r : RawUstarHeader} (hrw : r.WellSized) {post : ByteArray} {err : TarError}
    (hpost : post.size % 512 = 0) (hnz : ∃ hsz : 0 < r.fName.size, r.fName[0]'hsz ≠ 0)
    (herr : parseUstarHeader (patchHeaderChecksum r.toBytes ++ post) 0 = .error err ∨
      ∃ hdr, (hdr.typeflag == 0x78) = false ∧ parseUstarHeader (patchHeaderChecksum r.toBytes ++ post) 0 = .ok hdr ∧
        decodeTarEntry {} (patchHeaderChecksum r.toBytes ++ post) 0 hdr none [] 0 0 = .error err) :
    Impl.unpackWith {} (patchHeaderChecksum r.toBytes ++ post) = .error err := by
  rw [patchHeaderChecksum_raw hrw] at herr ⊢
  exact unpackWith_raw_err (r.withChk_wellSized hrw (encodeOctalField_6_sp_size (ustarChecksum r.toBytes))) hpost hnz herr

private theorem decodeTarEntry_raw_reg0 {h : RawUstarHeader} (hw : h.WellSized) (uidVal : Nat) {resName : Except TarError String}
    (hu : h.fUname = padRightBytes 32 ("" : String).toUTF8 := by rfl) (hg : h.fGname = padRightBytes 32 ("" : String).toUTF8 := by rfl)
    (hp : h.fPrefix = padRightBytes 155 ("" : String).toUTF8 := by rfl)
    (hdn : ∀ b : ByteArray, b.size = 1536 → b.extract 0 100 = h.fName → decodeCStringUtf8 b 0 100 0 "name" = resName) :
    decodeTarEntry {} (h.toBytes ++ twoZeroBlocks) 0 { mode := 0o644, uid := uidVal, gid := 0, size := 0, mtime := 0, typeflag := 0x30 } none [] 0 0 =
    match resName with
    | .error e => .error e
    | .ok nm => match validateEntryPath false false .regular nm with
      | .error err => .error { err with offset := some 0 } | .ok np => .ok ({ path := np, kind := .regular, mode := 0o644, uid := uidVal }, 0) := by
  obtain ⟨bytes, hbytes⟩ : ∃ b, b = h.toBytes ++ twoZeroBlocks := ⟨_, rfl⟩; rw [← hbytes]
  have hsz : bytes.size = 1536 := by rw [hbytes, ByteArray.size_append, RawUstarHeader.toBytes_size hw, twoZeroBlocks_size]
  have hext512 : bytes.extract 0 512 = h.toBytes := by rw [hbytes]; exact ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have ⟨hx_nm, _, _, _, _, _, _, _, _, _, hx_un, hx_gn, hx_pf⟩ := raw_extract_fields hw hext512
  have hdu := decodeCStringUtf8_padRightBytes (fieldName := "uname") (offset := 0) (start := 265) (w := 32) rfl (by decide) (by rw [hsz]; omega) (hx_un.trans hu)
  have hdg := decodeCStringUtf8_padRightBytes (fieldName := "gname") (offset := 0) (start := 297) (w := 32) rfl (by decide) (by rw [hsz]; omega) (hx_gn.trans hg)
  have hdp := decodeCStringUtf8_padRightBytes (fieldName := "prefix") (offset := 0) (start := 345) (w := 155) rfl (by decide) (by rw [hsz]; omega) (hx_pf.trans hp)
  unfold decodeTarEntry; have he1 : ¬(1 > ({} : UnpackOptions).maxEntries) := by decide
  have he2 : ¬(0 > ({} : UnpackOptions).maxTotalBytes) := by decide
  have he3 : ¬(0 + 512 + 0 > bytes.size) := by rw [hsz]; omega
  simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, Option.getD_none, bne_self_eq_false,
    he1, he2, pad512_zero, he3, Nat.zero_add, hdn bytes hsz hx_nm, hdu, hdg, hdp]
  cases resName with
  | error _ => rfl
  | ok nm => simp only [show ("" : String).isEmpty = true from rfl, ↓reduceIte]; cases validateEntryPath false false .regular nm <;> rfl

private theorem unpackWith_patched_regular_ok {r : RawUstarHeader} (hrw : r.WellSized) (uidVal : Nat)
    (hn : r.fName = padRightBytes 100 ("a.txt" : String).toUTF8 := by rfl)
    (hu : r.fUname = padRightBytes 32 ("" : String).toUTF8 := by rfl)
    (hg : r.fGname = padRightBytes 32 ("" : String).toUTF8 := by rfl)
    (hp : r.fPrefix = padRightBytes 155 ("" : String).toUTF8 := by rfl)
    (hparse : parseUstarHeader (patchHeaderChecksum r.toBytes ++ twoZeroBlocks) 0 =
      .ok { mode := 0o644, uid := uidVal, gid := 0, size := 0, mtime := 0, typeflag := 0x30 }) :
    Impl.unpackWith {} (patchHeaderChecksum r.toBytes ++ twoZeroBlocks) = .ok [{ path := "a.txt", kind := .regular, mode := 0o644, uid := uidVal }] := by
  rw [patchHeaderChecksum_raw hrw] at hparse ⊢
  let h := r.withChk (encodeOctalField (ustarChecksum r.toBytes) 6 ++ ByteArray.mk #[0x20])
  have hw : h.WellSized := r.withChk_wellSized hrw (encodeOctalField_6_sp_size (ustarChecksum r.toBytes))
  have hdec := decodeTarEntry_raw_reg0 hw uidVal hu hg hp fun _ hbs hx =>
    decodeCStringUtf8_padRightBytes (offset := 0) (start := 0) (w := 100) rfl (by decide) (by rw [hbs]; omega) (hx.trans hn)
  have hhdr_sz : h.toBytes.size = 512 := RawUstarHeader.toBytes_size hw
  obtain ⟨bytes, hbytes⟩ : ∃ b, b = h.toBytes ++ twoZeroBlocks := ⟨_, rfl⟩; rw [← hbytes] at hparse hdec ⊢
  have hsz : bytes.size = 1536 := by rw [hbytes, ByteArray.size_append, hhdr_sz, twoZeroBlocks_size]
  have hiz : isZeroRange bytes 0 512 = false := by rw [hbytes]; exact isZeroRange_raw_zero_false hw (by rw [show h.fName = r.fName from rfl, hn]; exact baseRaw_fName_nonzero)
  have hstep : unpackStep {} bytes 0 none [] [] 0 = .ok (.cont 512 none ["a.txt"] [{ path := "a.txt", kind := .regular, mode := 0o644, uid := uidVal }] 0) := by
    unfold unpackStep; have h1 : ¬(0 ≥ bytes.size) := by rw [hsz]; omega
    have h2 : ¬(0 + 512 > bytes.size) := by rw [hsz]; omega
    simp only [h1, ↓reduceIte, hiz, Bool.false_eq_true, h2, hparse, show ((0x30 : UInt8) == 0x78) = false from rfl, List.length_nil, hdec]; rfl
  rw [unpackWith_eq_unpackLoop (by rw [hsz]; omega) (by rw [hsz]),
    unpackLoop_step_continue {} bytes 0 none [] [] 0 512 none ["a.txt"] _ 0 (by rw [hsz]; omega) hstep (by omega), hbytes]
  simpa only [twoZeroBlocks, hhdr_sz, List.reverse_singleton] using
    unpackLoop_at_twoZeroBlocks {} h.toBytes ["a.txt"] [{ path := "a.txt", kind := .regular, mode := 0o644, uid := uidVal }] 0

private theorem test5_c01 {bh : ByteArray} (hbh : bh = mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") :
    Impl.unpackWith {} (bh.set! 148 0x37 ++ twoZeroBlocks) =
      .error { kind := .checksumMismatch, message := "USTAR header checksum mismatch", offset := some 0 } := by
  have heq : bh.set! 148 0x37 = (baseRaw (baseChkField.set! 0 0x37)).toBytes := by
    rw [hbh, baseHdr_eq_raw]; simpa [baseRaw, RawUstarHeader.ofFields] using set!_raw_chk baseRaw_hw (k := 0) (by omega) 0x37
  rw [heq]; have hchk_sz : (baseChkField.set! 0 0x37).size = 8 := by rw [byteArray_size_set!, baseChkField_size]
  let h := baseRaw (baseChkField.set! 0 0x37); have hw : h.WellSized := baseRaw_wellSized hchk_sz
  let hdrPre := (baseRaw (ByteArray.mk (Array.replicate 8 0x20))).toBytes; let chkVal := ustarChecksumAt hdrPre 0
  obtain ⟨bytes, hbytes⟩ : ∃ b, b = h.toBytes ++ twoZeroBlocks := ⟨_, rfl⟩
  have hext512 : bytes.extract 0 512 = h.toBytes := by rw [hbytes]; exact ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  have hbd : 0 + 512 ≤ bytes.size := by rw [hbytes, ByteArray.size_append, RawUstarHeader.toBytes_size hw]; omega
  have hext_chk : bytes.extract 148 156 = baseChkField.set! 0 0x37 := (raw_extract_fields hw hext512).2.2.2.2.2.2.1
  rcases encodeOctalField_loop_spec 6 chkVal [0] with ⟨ds, heq_ds, hlen_ds, hdigs_ds, _⟩
  rcases ds with _ | ⟨d0, ds'⟩; · cases hlen_ds
  have hds'_len : ds'.length = 5 := by simp at hlen_ds; omega
  have hlist_mut : (baseChkField.set! 0 0x37).data.toList = (0x37 :: ds') ++ [0, 0x20] := by
    rw [byteArray_set0_toList 0x37 (by rw [baseChkField_size]; omega)]
    have h1 : (encodeOctalField chkVal 6).data.toList = (d0 :: ds') ++ [0] := by unfold encodeOctalField; rw [heq_ds]
    have hb : baseChkField.data.toList = (d0 :: ds') ++ [0, 0x20] := by dsimp only [baseChkField]; rw [byteArray_data_toList_append, h1, List.append_assoc]; rfl
    rw [hb]; simp
  have hdigs' : ∀ d ∈ ds', (0x30 ≤ d && d ≤ 0x37) = true := fun b hb => by
    have ⟨hlo, hhi⟩ := hdigs_ds b (List.mem_cons_of_mem d0 hb); simp [hlo, hhi]
  have hparse_chk : parseChecksumOctal bytes 148 156 0 = .ok ((0x37 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 48)) 0) := by
    unfold parseChecksumOctal; dsimp only; rw [hext_chk, hlist_mut]
    have htake : (ds' ++ ([0, 0x20] : List UInt8)).takeWhile (fun b => 48 ≤ b && b ≤ 55) = ds' := by
      rw [List.takeWhile_append, list_takeWhile_eq_self _ ds' hdigs']; simp
    simp [htake]
  have hstored_ge : 229376 ≤ (0x37 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 48)) 0 := by
    simp only [List.foldl_cons]; have hge := foldl_octal_ge ds' (0 * 8 + ((0x37 : UInt8).toNat - 48))
    rw [hds'_len, show (0 * 8 + ((0x37 : UInt8).toNat - 48)) * 8 ^ 5 = 229376 by decide] at hge; exact hge
  have hcsum_eq : ustarChecksumAt bytes 0 = chkVal := by
    have hr := raw_ustarChecksumAt_eq (baseRaw_wellSized (chk := ByteArray.mk (Array.replicate 8 0x20)) (by decide))
      hchk_sz (by decide) hbd (c1 := baseChkField.set! 0 0x37) (c2 := ByteArray.mk (Array.replicate 8 0x20)) hext512
    rw [show (baseRaw (ByteArray.mk (Array.replicate 8 0x20))).withChk (ByteArray.mk (Array.replicate 8 0x20)) =
      baseRaw (ByteArray.mk (Array.replicate 8 0x20)) from rfl, ustarChecksum_eq_ustarChecksumAt] at hr; exact hr
  have hchk_le : chkVal ≤ 512 * 255 := ustarChecksumAt_le hdrPre 0
  have hne : ((0x37 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 48)) 0 != ustarChecksumAt bytes 0) = true := by rw [hcsum_eq]; exact bne_iff_ne.mpr (by omega)
  refine unpackWith_raw_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero (Or.inl ?_)
  rw [← hbytes]; unfold parseUstarHeader; rw [Nat.zero_add, Nat.zero_add, hparse_chk]
  dsimp only [bind, Except.bind]; rw [hne, ite_eq_left rfl]; rfl

private theorem test5_chk_err {chk : ByteArray} (hchk : chk.size = 8) {e : TarError}
    (hp : ∀ b : ByteArray, b.extract (0 + 148) (0 + 156) = chk → parseChecksumOctal b (0 + 148) (0 + 156) 0 = .error e) :
    Impl.unpackWith {} ((baseRaw chk).toBytes ++ twoZeroBlocks) = .error e := by
  have hw := baseRaw_wellSized hchk; obtain ⟨bytes, hbytes⟩ : ∃ b, b = (baseRaw chk).toBytes ++ twoZeroBlocks := ⟨_, rfl⟩
  have hext512 : bytes.extract 0 512 = (baseRaw chk).toBytes := by rw [hbytes]; exact ByteArray.extract_append_eq_left (RawUstarHeader.toBytes_size hw).symm
  refine unpackWith_raw_err hw (by rw [twoZeroBlocks_size]) baseRaw_fName_nonzero (Or.inl ?_)
  rw [← hbytes]; unfold parseUstarHeader; rw [hp bytes (raw_extract_fields hw hext512).2.2.2.2.2.2.1]; rfl

private def badNamePat : ByteArray := (padRightBytes 100 ("a.txt" : String).toUTF8).set! 0 0xff
private theorem badNamePat_size : badNamePat.size = 100 := by dsimp only [badNamePat]; rw [byteArray_size_set!, padRightBytes_size]
private theorem extractCStringBytes_badUtf8Name {bytes : ByteArray} (hbd : 100 ≤ bytes.size) (hext : bytes.extract 0 100 = badNamePat) :
    extractCStringBytes bytes 0 100 = ByteArray.mk #[0xff, 0x2e, 0x74, 0x78, 0x74] := by
  have hpre : bytes.extract 0 6 = ByteArray.mk #[0xff, 0x2e, 0x74, 0x78, 0x74, 0x00] := by
    have h1 : bytes.extract 0 6 = (bytes.extract 0 100).extract 0 6 := by rw [ByteArray.extract_extract]; simp
    rw [h1, hext]; decide
  have hstep : ∀ k (hk : k < 6) (r : Nat), extractCStringBytes.findNul bytes 100 (r + 1) k =
      if (ByteArray.mk #[0xff, 0x2e, 0x74, 0x78, 0x74, 0x00])[k]'hk == 0 then k else extractCStringBytes.findNul bytes 100 r (k + 1) := by
    intro k hk r; have hie : k < (bytes.extract 0 6).size := by rw [hpre]; exact hk
    have h0 := ByteArray.getElem_extract hie; rw [byteArray_getElem_of_eq hpre hie hk] at h0; simp only [Nat.zero_add] at h0
    rw [extractCStringBytes.findNul.eq_2]; simp only [show k < bytes.size by omega, ↓reduceDIte, ← h0]
  have hfind : extractCStringBytes.findNul bytes 100 100 0 = 5 := by
    rw [hstep 0 (by decide), ite_eq_right (by decide), hstep 1 (by decide), ite_eq_right (by decide),
      hstep 2 (by decide), ite_eq_right (by decide), hstep 3 (by decide), ite_eq_right (by decide),
      hstep 4 (by decide), ite_eq_right (by decide), hstep 5 (by decide), ite_eq_left (by decide)]
  unfold extractCStringBytes; rw [Nat.sub_zero, hfind]
  have h1 : bytes.extract 0 5 = (bytes.extract 0 100).extract 0 5 := by rw [ByteArray.extract_extract]; simp
  rw [h1, hext]; decide

private theorem test5_for (api : TarApi) (hu : api.unpackWith = Impl.unpackWith) (hup : api.unpack = Impl.unpackWith {}) :
    AllPass (test_tar_unpackWith_checksumNumericAndUnsupported_validated api) := by
  obtain ⟨bh, hbh⟩ : ∃ b, b = mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  have hbh_post : (bh ++ twoZeroBlocks).size % 512 = 0 := by rw [ByteArray.size_append, hbh, mkUstarHeader_size, twoZeroBlocks_size]
  have hz2_mod : twoZeroBlocks.size % 512 = 0 := by rw [twoZeroBlocks_size]
  have hpax_err : ∀ {e : TarError} (pax : ByteArray), pax.size ≤ maxPaxHeaderBytes → parsePaxPayload pax 0 = .error e →
      Impl.unpackWith {} (mkPaxFrame pax ++ bh ++ twoZeroBlocks) = .error e := by
    intro e pax hp hpe; rw [ByteArray.append_assoc]; exact unpackWith_mkPaxFrame_err {} pax (bh ++ twoZeroBlocks) hp hbh_post hpe
  have hc02 : Impl.unpackWith {} (bh.set! 148 0x58 ++ twoZeroBlocks) = .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    have heq : bh.set! 148 0x58 = (baseRaw (baseChkField.set! 0 0x58)).toBytes := by
      rw [hbh, baseHdr_eq_raw]; simpa [baseRaw, RawUstarHeader.ofFields] using set!_raw_chk baseRaw_hw (k := 0) (by omega) 0x58
    rw [heq]; refine test5_chk_err (by rw [byteArray_size_set!, baseChkField_size]) fun b hx => ?_
    unfold parseChecksumOctal; rw [hx, byteArray_set0_toList 0x58 (by rw [baseChkField_size]; omega)]; simp
  have hc03 : Impl.unpackWith {} (blitFixed bh 148 8 (ByteArray.mk (Array.replicate 8 0)) ++ twoZeroBlocks) =
      .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some 0 } := by
    have heq : blitFixed bh 148 8 (ByteArray.mk (Array.replicate 8 0)) = (baseRaw (ByteArray.mk (Array.replicate 8 0))).toBytes := by
      rw [hbh, baseHdr_eq_raw]; simpa [baseRaw, RawUstarHeader.ofFields, RawUstarHeader.withChk] using blitFixed_raw_chk baseRaw_hw (src := ByteArray.mk (Array.replicate 8 0)) rfl
    rw [heq]; exact test5_chk_err rfl fun b hx => by unfold parseChecksumOctal; rw [hx]; rfl
  have hc04 : Impl.unpackWith {} (patchHeaderChecksum (blitFixed bh 257 6 "notust".toUTF8) ++ twoZeroBlocks) =
      .error { kind := .invalidHeader, message := "invalid USTAR magic or version", offset := some 0 } := by
    have hrw : ({ baseRaw baseChkField with fMagic := "notust".toUTF8 } : RawUstarHeader).WellSized := { baseRaw_hw with szMagic := rfl }
    rw [hbh, baseHdr_eq_raw, blitFixed_raw_magic baseRaw_hw rfl]
    exact unpackWith_patched_err hrw hz2_mod baseRaw_fName_nonzero (Or.inl (parseUstarHeader_patched hrw 0x30 false (resUid := .ok 0) (resSize := .ok 0)))
  have hbadSz : ∀ (sz : ByteArray) (hsz : sz.size = 12) {e : TarError},
      (∀ b : ByteArray, b.extract (0 + 124) (0 + 136) = sz → parseUstarNumeric b (0 + 124) (0 + 136) 0 false u64Limit "size" = .error e) →
      Impl.unpackWith {} (patchHeaderChecksum (blitFixed bh 124 12 sz) ++ twoZeroBlocks) = .error e := by
    intro sz hsz e hp; have hrw : ({ baseRaw baseChkField with fSize := sz } : RawUstarHeader).WellSized := { baseRaw_hw with szSize := hsz }
    rw [hbh, baseHdr_eq_raw, blitFixed_raw_size baseRaw_hw hsz]
    exact unpackWith_patched_err hrw hz2_mod baseRaw_fName_nonzero (Or.inl (by simpa [bind, Except.bind] using parseUstarHeader_patched hrw 0x30 true (resUid := .ok 0) (hsize := hp)))
  have hokUid : ∀ (ub : ByteArray) (hub : ub.size = 8) (u : Nat),
      (∀ b : ByteArray, b.extract (0 + 108) (0 + 116) = ub → parseUstarNumeric b (0 + 108) (0 + 116) 0 true u64Limit "uid" = .ok u) →
      Impl.unpackWith {} (patchHeaderChecksum (blitFixed bh 108 8 ub) ++ twoZeroBlocks) = .ok [{ path := "a.txt", kind := .regular, uid := u }] := by
    intro ub hub u hp; have hrw : ({ baseRaw baseChkField with fUid := ub } : RawUstarHeader).WellSized := { baseRaw_hw with szUid := hub }
    rw [hbh, baseHdr_eq_raw, blitFixed_raw_uid baseRaw_hw hub]
    exact unpackWith_patched_regular_ok hrw u (hparse := by simpa [bind, Except.bind] using parseUstarHeader_patched hrw 0x30 true (huid := hp) (resSize := .ok 0))
  have hunsup : ∀ (tf : UInt8), (tf == 0x78) = false →
      (if tf == 0x30 || tf == 0x00 then some EntryKind.regular else if tf == 0x35 then some .directory else if tf == 0x32 then some .symlink else none) = none →
      Impl.unpackWith {} (patchHeaderChecksum (bh.set! 156 tf) ++ twoZeroBlocks) =
        .error { kind := .unsupportedEntry, message := s!"unsupported tar entry typeflag: {tf.toNat}", offset := some 0 } := by
    intro tf h78 hk; have hrw : ({ baseRaw baseChkField with fType := tf } : RawUstarHeader).WellSized := { baseRaw_hw with }
    rw [hbh, baseHdr_eq_raw, set!_raw_type baseRaw_hw tf]
    refine unpackWith_patched_err hrw hz2_mod baseRaw_fName_nonzero (Or.inr ⟨_, h78, by simpa [bind, Except.bind] using parseUstarHeader_patched hrw tf true (resUid := .ok 0) (resSize := .ok 0), ?_⟩)
    unfold decodeTarEntry; dsimp only; rw [hk]
  have hc11 : Impl.unpackWith {} (patchHeaderChecksum (blitFixed (bh.set! 156 0x35) 124 12 (encodeOctalField 5 11)) ++
      padBlock512 "12345".toUTF8 ++ twoZeroBlocks) = .error { kind := .invalidHeader, message := "non-regular tar entry has non-zero size", offset := some 0 } := by
    have hrw1 : ({ baseRaw baseChkField with fType := 0x35 } : RawUstarHeader).WellSized := { baseRaw_hw with }
    have hrw : ({ baseRaw baseChkField with fType := 0x35, fSize := encodeOctalField 5 11 } : RawUstarHeader).WellSized := { hrw1 with szSize := encodeOctalField_size 5 11 }
    rw [ByteArray.append_assoc, hbh, baseHdr_eq_raw, set!_raw_type baseRaw_hw 0x35, blitFixed_raw_size hrw1 (encodeOctalField_size 5 11)]
    have hpm : (padBlock512 "12345".toUTF8 ++ twoZeroBlocks).size % 512 = 0 := by rw [ByteArray.size_append, padBlock512_size, twoZeroBlocks_size]; rfl
    exact unpackWith_patched_err hrw hpm baseRaw_fName_nonzero (Or.inr ⟨_, rfl, by simpa [bind, Except.bind] using parseUstarHeader_patched hrw 0x35 true (resUid := .ok 0) (resSize := .ok 5), rfl⟩)
  have hc17 : Impl.unpackWith {} (patchHeaderChecksum (bh.set! 0 0xff) ++ twoZeroBlocks) = .error { kind := .invalidEncoding, message := "invalid UTF-8 in USTAR name", offset := some 0 } := by
    let r : RawUstarHeader := { baseRaw baseChkField with fName := badNamePat }; have hrw : r.WellSized := { baseRaw_hw with szName := badNamePat_size }
    rw [hbh, baseHdr_eq_raw, set!_raw_name0 baseRaw_hw 0xff]
    have hbn0 : badNamePat[0]'(by rw [badNamePat_size]; decide) = 0xff := by decide
    have hnz : ∃ hsz : 0 < r.fName.size, r.fName[0]'hsz ≠ 0 := ⟨by rw [badNamePat_size]; decide, by change badNamePat[0]'_ ≠ 0; rw [hbn0]; decide⟩
    refine unpackWith_patched_err hrw hz2_mod hnz (Or.inr ⟨_, rfl, by simpa [bind, Except.bind] using parseUstarHeader_patched hrw 0x30 true (resUid := .ok 0) (resSize := .ok 0), ?_⟩)
    rw [patchHeaderChecksum_raw hrw]; exact decodeTarEntry_raw_reg0 (r.withChk_wellSized hrw (encodeOctalField_6_sp_size (ustarChecksum r.toBytes))) 0 rfl rfl rfl fun b hbs hx => by
      unfold decodeCStringUtf8; rw [extractCStringBytes_badUtf8Name (by rw [hbs]; omega) hx]
  have hc18 : Impl.unpackWith {} (patchHeaderChecksum (bh.set! 157 0xff) ++ twoZeroBlocks) = .ok [{ path := "a.txt", kind := .regular }] := by
    have hrw : ({ baseRaw baseChkField with fLink := (padRightBytes 100 ("" : String).toUTF8).set! 0 0xff } : RawUstarHeader).WellSized :=
      { baseRaw_hw with szLink := by rw [byteArray_size_set!, padRightBytes_size] }
    rw [hbh, baseHdr_eq_raw, set!_raw_link0 baseRaw_hw 0xff]
    exact unpackWith_patched_regular_ok hrw 0 (hparse := by simpa [bind, Except.bind] using parseUstarHeader_patched hrw 0x30 true (resUid := .ok 0) (resSize := .ok 0))
  unfold test_tar_unpackWith_checksumNumericAndUnsupported_validated; dsimp only; rw [← hbh, hup]
  refine allPass_err_for hu (test5_c01 hbh) rfl rfl ?_
  refine allPass_err_for hu hc02 rfl rfl ?_
  refine allPass_err_for hu hc03 rfl rfl ?_
  refine allPass_err_for hu hc04 rfl rfl ?_
  refine allPass_err_for hu (hbadSz (ByteArray.mk (Array.replicate 12 0xff)) rfl fun b hx => by unfold parseUstarNumeric; rw [hx]; rfl) rfl rfl ?_
  refine allPass_ok_bind_fn rfl (hokUid (ByteArray.mk #[0x80, 0, 0, 0, 0, 0, 0, 42]) rfl 42 fun b hx => by unfold parseUstarNumeric; rw [hx]; simp [u64Limit]) (tarEquiv_singleton_self _) ?_
  refine allPass_err_for hu (hbadSz (ByteArray.mk (Array.replicate 12 0)) rfl fun b hx => by unfold parseUstarNumeric; rw [hx]; rfl) rfl rfl ?_
  refine allPass_ok_bind_fn rfl (hokUid (ByteArray.mk (Array.replicate 8 0)) rfl 0 fun b hx => by unfold parseUstarNumeric; rw [hx]; rfl) (tarEquiv_singleton_self _) ?_
  refine allPass_err_for hu (hunsup 0x31 rfl rfl) rfl rfl ?_
  refine allPass_err_for hu (hunsup 0x67 rfl rfl) rfl rfl ?_
  refine allPass_err_for hu hc11 rfl rfl ?_
  refine allPass_err_for hu (hpax_err (encodePaxRecord "GNU.sparse.major" "1") (by decide) rfl) rfl rfl ?_
  refine allPass_err_for hu (hpax_err (encodePaxRecord "uname" "a\x00b") (by decide) rfl) rfl rfl ?_
  refine allPass_err_for hu (hpax_err (encodePaxRecord "path" "a" ++ encodePaxRecord "path" "b") (by decide) rfl) rfl rfl ?_
  refine allPass_err_for hu (hpax_err "09 path=a\n".toUTF8 (by decide) rfl) rfl rfl ?_
  refine allPass_ok_bind_fn rfl (unpackWith_pax_emptyRegular_ok {} _ _ bh "a.txt" "a.txt" { mtime? := some 1794744353 } rfl hbh) (tarEquiv_singleton_self _) ?_
  refine allPass_err_for hu hc17 rfl rfl ?_
  exact allPass_ok_last_impl hc18 (tarEquiv_singleton_self _)

/-- Semantic validation theorem for `test_tar_unpackWith_checksumNumericAndUnsupported_validated`. -/
theorem allPass_unpackWith_checksumNumericAndUnsupported_validated :
    AllPass (test_tar_unpackWith_checksumNumericAndUnsupported_validated defaultApi) := test5_for defaultApi rfl rfl

end LeanSwe.Tar.Proofs
