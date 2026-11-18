import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout

/-!
# Concrete Unpack Proofs for `LeanSwe.Tar`

Proves the framing/trailer, resource-limit (including crafted `size >= 2^33` PAX bombs),
and wire-security concrete `AllPass` specifications (`SpecTests`), plus reusable unpack-stepping
infrastructure shared with `ConcreteUnpackHeader`.
-/

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem defaultApi_unpack_eq (bytes : ByteArray) :
    defaultApi.unpack bytes = Impl.unpackWith {} bytes := rfl

private theorem defaultApi_unpackWith_eq (opts : UnpackOptions) (bytes : ByteArray) :
    defaultApi.unpackWith opts bytes = Impl.unpackWith opts bytes := rfl

private theorem allPass_have {α : Type _} (v : α) (f : α → AllPassRun Unit) :
    AllPass (have x := v; f x) ↔ ∀ x, x = v → AllPass (f x) :=
  ⟨fun h _ hx => hx ▸ h, fun h => h v rfl⟩

private theorem allPass_checkUnpackError_exists_bind {opts : UnpackOptions}
    {bytes : ByteArray} {expectedKind : TarErrorKind}
    (h : ∃ e, Impl.unpackWith opts bytes = .error e ∧
      e.kind = expectedKind ∧ (!e.message.isEmpty) = true)
    (k : Unit → AllPassRun Unit) (hkRest : AllPass (k ())) :
    AllPass (Bind.bind (checkUnpackError defaultApi opts bytes expectedKind) k) := by
  rcases h with ⟨e, he, hk, hm⟩
  exact allPass_checkUnpackError_bind (by rw [defaultApi_unpackWith_eq]; exact he) hk hm hkRest

private theorem allPass_checkUnpackError_of_err (opts : UnpackOptions)
    (bytes : ByteArray) (expectedKind : TarErrorKind)
    (h : ∃ e, Impl.unpackWith opts bytes = .error e ∧
      e.kind = expectedKind ∧ (!e.message.isEmpty) = true) :
    AllPass (checkUnpackError defaultApi opts bytes expectedKind) := by
  rcases h with ⟨e, he, hk, hm⟩
  dsimp only [checkUnpackError]
  rw [defaultApi_unpackWith_eq, he]
  exact ⟨⟨hk, by simpa using hm⟩, trivial⟩

/-- Extract string fields from a `mkUstarHeader` block inside `bytes`. -/
theorem mkUstarHeader_extract_strings {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hext : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    bytes.extract offset (offset + 100) = padRightBytes 100 name.toUTF8 ∧
    bytes.extract (offset + 157) (offset + 257) = padRightBytes 100 linkname.toUTF8 ∧
    bytes.extract (offset + 265) (offset + 297) = padRightBytes 32 uname.toUTF8 ∧
    bytes.extract (offset + 297) (offset + 329) = padRightBytes 32 gname.toUTF8 ∧
    bytes.extract (offset + 345) (offset + 500) = padRightBytes 155 pfx.toUTF8 :=
  buildUstarHeader_extract_strings (hext.trans (mkUstarHeader_eq_buildUstarHeader ..))

/-- A `mkUstarHeader` block at `offset` is never all-zero. -/
theorem isZeroRange_mkUstarHeader_false {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    isZeroRange bytes offset 512 = false :=
  isZeroRange_buildUstarHeader_false hbd (hext.trans (mkUstarHeader_eq_buildUstarHeader ..))

private theorem encodePaxRecord_size_lt_512 {key value : String}
    (hmin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hmax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ 100) :
    0 < (encodePaxRecord key value).size ∧ (encodePaxRecord key value).size < 512 := by
  have hmax_pax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : maxPaxHeaderBytes = 1048576 := rfl
    omega
  rcases encodePaxRecord_parts hmin hmax_pax with ⟨r, hr_eq, hr5, _, hsz⟩
  have hr_sz : (toString r).toUTF8.size = decDigitsLen r := rfl
  have hsuf_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
      1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
    have h1 : " ".toUTF8.size = 1 := rfl
    have h2 : "=".toUTF8.size = 1 := rfl
    have h3 : "\n".toUTF8.size = 1 := rfl
    simp only [toUTF8_size_append, h1, h2, h3, Nat.add_assoc]
  have hpow_ge : ∀ d : Nat, 4 ≤ d → d + 100 < 10 ^ (d - 1) := by
    intro d hd
    induction d with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k 4 with hk | hk
      · have : k = 3 := by omega
        subst this
        decide
      · have ihk := ih hk
        have : 10 ^ (k + 1 - 1) = 10 ^ (k - 1) * 10 := by
          rw [show k + 1 - 1 = (k - 1) + 1 from by omega, Nat.pow_succ]
        omega
  have hdr_lt4 : decDigitsLen r < 4 := by
    rcases Nat.lt_or_ge (decDigitsLen r) 4 with hlt | hge4
    · exact hlt
    · exfalso
      rcases decDigitsLen_eq_digits_length r with ⟨ds, _, hbounds, _, _, hdec, _⟩
      rcases hbounds (by omega) with ⟨_, _, _, _, hlo, _⟩
      rw [← hdec] at hlo
      have hlt := hpow_ge (decDigitsLen r) hge4
      rw [hr_sz] at hr_eq
      omega
  rw [hr_sz] at hr_eq
  rw [hsz]
  omega

/-- Reflexivity of `TarEquiv` on singleton lists. -/
theorem tarEquiv_singleton_self (e : TarEntry) : TarEquiv [e] [e] := by
  refine ⟨?_, trivial⟩
  unfold entryEquivBool
  have hk : (e.kind == e.kind) = true := by cases e.kind <;> rfl
  simp only [beq_self_eq_true, hk, Bool.and_self]

/-- `(mkRegularFrame p d).size = 512 + pad512 d.size`. -/
theorem mkRegularFrame_size (p : String) (d : ByteArray) :
    (mkRegularFrame p d).size = 512 + pad512 d.size := by
  unfold mkRegularFrame
  rw [ByteArray.size_append, mkUstarHeader_size, padBlock512_size]

/-- `(mkPaxFrame pax).size = 512 + pad512 pax.size`. -/
theorem mkPaxFrame_size (pax : ByteArray) :
    (mkPaxFrame pax).size = 512 + pad512 pax.size := by
  unfold mkPaxFrame
  rw [ByteArray.size_append, mkUstarHeader_size, padBlock512_size]

private theorem padBlock512_getElem_prefix {bs : ByteArray} {k : Nat} (hk : k < bs.size) :
    (padBlock512 bs)[k]'(by
        rw [padBlock512_size]
        exact Nat.lt_of_lt_of_le hk (le_pad512 bs.size)) = bs[k]'hk := by
  have h1 : (padBlock512 bs).extract 0 bs.size = bs := padBlock512_extract_prefix bs
  have h2 : k < ((padBlock512 bs).extract 0 bs.size).size := by rw [h1]; exact hk
  have h3 := ByteArray.getElem_extract h2
  simp only [Nat.zero_add] at h3
  rw [← h3]
  exact byteArray_getElem_of_eq h1 _ _

private theorem unpackWith_alignment_err (opts : UnpackOptions) (bytes : ByteArray)
    (h : bytes.size = 0 ∨ bytes.size % 512 ≠ 0) :
    ∃ e, Impl.unpackWith opts bytes = .error e ∧ e.kind = .truncatedArchive ∧ (!e.message.isEmpty) = true := by
  unfold Impl.unpackWith
  have hcond : (bytes.size == 0 || bytes.size % 512 != 0) = true := by
    rcases h with hz | hmod
    · simp [hz]
    · simp [bne, hmod]
  rw [ite_eq_left hcond]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem isZeroRange_zeroBlock {a b : ByteArray} {off : Nat}
    (ha : a.size = off) (hb : 512 ≤ b.size)
    (hz : ∀ i (hi : i < 512), b[i]'(by omega) = 0) :
    isZeroRange (a ++ b) off 512 = true := by
  refine (isZeroRange_eq_true_iff (a ++ b) off 512 (by decide)).mpr ⟨by rw [ByteArray.size_append, ha]; omega, ?_⟩
  intro i hi hbd
  have hge : a.size ≤ off + i := by omega
  rw [getElem_append_right hge]
  have hi_b : i < b.size := by omega
  have hb' : b[off + i - a.size]'(by rw [ByteArray.size_append, ha] at hbd; omega) = b[i]'hi_b := by
    congr 1; omega
  rw [hb']
  exact hz i hi

private theorem isZeroRange_twoZeroBlocks_fst (pre suf : ByteArray) :
    isZeroRange (pre ++ twoZeroBlocks ++ suf) pre.size 512 = true := by
  rw [ByteArray.append_assoc]
  refine isZeroRange_zeroBlock rfl (by rw [ByteArray.size_append, twoZeroBlocks_size]; omega) ?_
  intro i hi
  have hlt_tz : i < twoZeroBlocks.size := by rw [twoZeroBlocks_size]; omega
  rw [getElem_append_left hlt_tz]
  have hlt_zb : i < zeroBlock.size := by rw [zeroBlock_size]; omega
  change (zeroBlock ++ zeroBlock)[i]'(by rw [ByteArray.size_append, zeroBlock_size]; omega) = 0
  rw [getElem_append_left hlt_zb]
  exact zeroBlock_getElem _

private theorem isZeroRange_twoZeroBlocks_snd (pre suf : ByteArray) :
    isZeroRange (pre ++ twoZeroBlocks ++ suf) (pre.size + 512) 512 = true := by
  have heq : pre ++ twoZeroBlocks ++ suf = (pre ++ zeroBlock) ++ (zeroBlock ++ suf) := by
    unfold twoZeroBlocks
    simp only [ByteArray.append_assoc]
  rw [heq]
  refine isZeroRange_zeroBlock (by rw [ByteArray.size_append, zeroBlock_size])
    (by rw [ByteArray.size_append, zeroBlock_size]; omega) ?_
  intro i hi
  have hlt_zb : i < zeroBlock.size := by rw [zeroBlock_size]; omega
  rw [getElem_append_left hlt_zb]
  exact zeroBlock_getElem _

/-- `unpackLoop` at `pre ++ (zeroBlock ++ zeroBlock)` immediately returns `.ok acc.reverse`. -/
theorem unpackLoop_at_twoZeroBlocks (opts : UnpackOptions) (pre : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat) :
    unpackLoop opts (pre ++ (zeroBlock ++ zeroBlock)) pre.size none seen acc totalBytes =
      .ok acc.reverse := by
  let bytes := pre ++ (zeroBlock ++ zeroBlock)
  have hbytes_eq : bytes = pre ++ twoZeroBlocks ++ ByteArray.empty := by
    simp only [bytes, twoZeroBlocks, ByteArray.append_empty]
  have hsz : bytes.size = pre.size + 1024 := by
    rw [ByteArray.size_append, ByteArray.size_append, zeroBlock_size]
  have hz1 : isZeroRange bytes pre.size 512 = true := by
    rw [hbytes_eq]
    exact isZeroRange_twoZeroBlocks_fst pre ByteArray.empty
  have hz2 : isZeroRange bytes (pre.size + 512) 512 = true := by
    rw [hbytes_eq]
    exact isZeroRange_twoZeroBlocks_snd pre ByteArray.empty
  have htr : allZeroTrailer bytes (pre.size + 1024) = true := by
    refine allZeroTrailer_of_zeros (bytes := bytes) (offset := pre.size + 1024) (by simp [hsz]) ?_
    intro k hk hle
    exact False.elim (by omega)
  refine unpackLoop_step_done opts bytes pre.size none seen acc totalBytes acc.reverse (by rw [hsz]; omega) ?_
  unfold unpackStep
  have hnotge : ¬(pre.size ≥ bytes.size) := by rw [hsz]; omega
  have hnotge2 : ¬(pre.size + 512 ≥ bytes.size) := by rw [hsz]; omega
  simp only [hnotge, hnotge2, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true, hz2,
    Bool.not_true, htr]

private theorem unpackLoop_at_padded_twoZeroBlocks (opts : UnpackOptions) (pre pad : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hpad_mod : pad.size % 512 = 0)
    (hpad_zero : ∀ k (hk : k < pad.size), pad[k]'hk = 0) :
    unpackLoop opts (pre ++ twoZeroBlocks ++ pad) pre.size none seen acc totalBytes =
      .ok acc.reverse := by
  let bytes := pre ++ twoZeroBlocks ++ pad
  have hsz : bytes.size = pre.size + 1024 + pad.size := by
    simp only [bytes, ByteArray.size_append, twoZeroBlocks_size, Nat.add_assoc]
  have hz1 : isZeroRange bytes pre.size 512 = true := isZeroRange_twoZeroBlocks_fst pre pad
  have hz2 : isZeroRange bytes (pre.size + 512) 512 = true := isZeroRange_twoZeroBlocks_snd pre pad
  have htr : allZeroTrailer bytes (pre.size + 1024) = true := by
    refine allZeroTrailer_of_zeros (bytes := bytes) (offset := pre.size + 1024) (by rw [hsz]; omega) ?_
    intro k hk hle hi
    have hpre2_sz : (pre ++ twoZeroBlocks).size = pre.size + 1024 := by
      rw [ByteArray.size_append, twoZeroBlocks_size]
    have hge : (pre ++ twoZeroBlocks).size ≤ k := by omega
    change (pre ++ twoZeroBlocks ++ pad)[k]'hi = 0
    rw [getElem_append_right hge]
    have hsub_lt : k - (pre ++ twoZeroBlocks).size < pad.size := by omega
    exact hpad_zero _ hsub_lt
  refine unpackLoop_step_done opts bytes pre.size none seen acc totalBytes acc.reverse (by rw [hsz]; omega) ?_
  unfold unpackStep
  have hnotge : ¬(pre.size ≥ bytes.size) := by rw [hsz]; omega
  have hnotge2 : ¬(pre.size + 512 ≥ bytes.size) := by rw [hsz]; omega
  simp only [hnotge, hnotge2, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true, hz2,
    Bool.not_true, htr]

/-- Decode strings from a `mkUstarHeader` block with zeroed USTAR string fields (`linkname = uname = gname = pfx = ""`). -/
theorem mkUstarHeader_zero_decode_strings {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid size mtime typeflag "" "" "" "")
    (hnm_sz : name.toUTF8.size ≤ 100) (hnm_nul : !hasNulString name = true) :
    decodeCStringUtf8 bytes offset (offset + 100) offset "name" = .ok name ∧
    decodeCStringUtf8 bytes (offset + 157) (offset + 257) offset "linkname" = .ok "" ∧
    decodeCStringUtf8 bytes (offset + 265) (offset + 297) offset "uname" = .ok "" ∧
    decodeCStringUtf8 bytes (offset + 297) (offset + 329) offset "gname" = .ok "" ∧
    decodeCStringUtf8 bytes (offset + 345) (offset + 500) offset "prefix" = .ok "" := by
  have hemp_sz : ("" : String).toUTF8.size = 0 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hemp_nul : !hasNulString "" = true := by decide
  have hstrs := mkUstarHeader_extract_strings hext
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact decodeCStringUtf8_padRightBytes hnm_nul hnm_sz (by omega) hstrs.1
  · have hext_lk : bytes.extract (offset + 157) (offset + 157 + 100) = padRightBytes 100 "".toUTF8 := by
      rw [show offset + 157 + 100 = offset + 257 from by omega]; exact hstrs.2.1
    rw [show offset + 257 = (offset + 157) + 100 from by omega]
    exact decodeCStringUtf8_padRightBytes hemp_nul (by omega) (by omega) hext_lk
  · have hext_u : bytes.extract (offset + 265) (offset + 265 + 32) = padRightBytes 32 "".toUTF8 := by
      rw [show offset + 265 + 32 = offset + 297 from by omega]; exact hstrs.2.2.1
    rw [show offset + 297 = (offset + 265) + 32 from by omega]
    exact decodeCStringUtf8_padRightBytes hemp_nul (by omega) (by omega) hext_u
  · have hext_g : bytes.extract (offset + 297) (offset + 297 + 32) = padRightBytes 32 "".toUTF8 := by
      rw [show offset + 297 + 32 = offset + 329 from by omega]; exact hstrs.2.2.2.1
    rw [show offset + 329 = (offset + 297) + 32 from by omega]
    exact decodeCStringUtf8_padRightBytes hemp_nul (by omega) (by omega) hext_g
  · have hext_p : bytes.extract (offset + 345) (offset + 345 + 155) = padRightBytes 155 "".toUTF8 := by
      rw [show offset + 345 + 155 = offset + 500 from by omega]; exact hstrs.2.2.2.2
    rw [show offset + 500 = (offset + 345) + 155 from by omega]
    exact decodeCStringUtf8_padRightBytes hemp_nul (by omega) (by omega) hext_p

/-- General `decodeTarEntry` step lemma for a `mkUstarHeader` regular-file header at `offset`. -/
theorem decodeTarEntry_mkUstarHeader_regular
    (opts : UnpackOptions) (bytes hdr : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (accLen totalBytes : Nat)
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = hdr)
    {name : String} {mode : UInt32} {uid gid hdrSize mtime : Nat}
    (hhdr : hdr = mkUstarHeader name mode uid gid hdrSize mtime 0x30 "" "" "" "")
    (hnm_sz : name.toUTF8.size ≤ 100) (hnm_nul : !hasNulString name = true)
    (_huid : uid < ustarOctal7Limit) (_hgid : gid < ustarOctal7Limit)
    (_hsz : hdrSize < ustarOctal11Limit) (_hmtime : mtime < ustarOctal11Limit)
    {normPath : String}
    (hval_path : validateEntryPath opts.allowAbsolute opts.allowParentTraversal .regular
      (pendingPax.bind (·.path?) |>.getD name) = .ok normPath)
    (hseen : seen.contains normPath = false)
    (hnul_u : hasNulString (pendingPax.bind (·.uname?) |>.getD "") = false)
    (hnul_g : hasNulString (pendingPax.bind (·.gname?) |>.getD "") = false)
    (hentries : accLen + 1 ≤ opts.maxEntries)
    (heff_sz_bound : totalBytes + (pendingPax.bind (·.size?) |>.getD hdrSize) ≤ opts.maxTotalBytes)
    (hdata_bound : offset + 512 + pad512 (pendingPax.bind (·.size?) |>.getD hdrSize) ≤ bytes.size) :
    let effSize := pendingPax.bind (·.size?) |>.getD hdrSize
    let payload := if effSize == 0 then ByteArray.empty else bytes.extract (offset + 512) (offset + 512 + effSize)
    let entry : TarEntry :=
      { path := normPath
      , kind := .regular
      , mode := (mode &&& 0o7777).toNat.toUInt32
      , uid := pendingPax.bind (·.uid?) |>.getD uid
      , gid := pendingPax.bind (·.gid?) |>.getD gid
      , mtime := pendingPax.bind (·.mtime?) |>.getD mtime
      , uname := pendingPax.bind (·.uname?) |>.getD ""
      , gname := pendingPax.bind (·.gname?) |>.getD ""
      , data := payload
      , linkTarget := "" }
    decodeTarEntry opts bytes offset
      { mode := (mode &&& 0o7777).toNat, uid := uid, gid := gid,
        size := hdrSize, mtime := mtime, typeflag := 0x30 }
      pendingPax seen accLen totalBytes = .ok (entry, pad512 effSize) := by
  have hext' : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid hdrSize mtime 0x30 "" "" "" "" := hext.trans hhdr
  have hdec_strs := mkUstarHeader_zero_decode_strings hbd hext' hnm_sz hnm_nul
  rw [decodeTarEntry.eq_1]
  have htf : ((0x30 : UInt8) == 0x30 || (0x30 : UInt8) == 0x00) = true := rfl
  have hne_reg : ((EntryKind.regular != EntryKind.regular) && (pendingPax.bind (·.size?) |>.getD hdrSize) != 0) = false := rfl
  have hnot_maxe : ¬(accLen + 1 > opts.maxEntries) := by omega
  have hnot_maxb : ¬(totalBytes + (pendingPax.bind (·.size?) |>.getD hdrSize) > opts.maxTotalBytes) := by omega
  have hnot_trunc : ¬(offset + 512 + pad512 (pendingPax.bind (·.size?) |>.getD hdrSize) > bytes.size) := by omega
  have hps : (pendingPax.getD {}).size? = pendingPax.bind (·.size?) := by cases pendingPax <;> rfl
  have hpu : (pendingPax.getD {}).uid? = pendingPax.bind (·.uid?) := by cases pendingPax <;> rfl
  have hpg : (pendingPax.getD {}).gid? = pendingPax.bind (·.gid?) := by cases pendingPax <;> rfl
  have hpm : (pendingPax.getD {}).mtime? = pendingPax.bind (·.mtime?) := by cases pendingPax <;> rfl
  have hpp : (pendingPax.getD {}).path? = pendingPax.bind (·.path?) := by cases pendingPax <;> rfl
  have hpun : (pendingPax.getD {}).uname? = pendingPax.bind (·.uname?) := by cases pendingPax <;> rfl
  have hpgn : (pendingPax.getD {}).gname? = pendingPax.bind (·.gname?) := by cases pendingPax <;> rfl
  have hmode_idem : ((mode &&& 0o7777).toNat &&& 0o7777) = (mode &&& 0o7777).toNat := by
    have hlt : mode.toNat &&& 0o7777 < 2 ^ 12 := Nat.and_lt_two_pow (n := 12) mode.toNat (by decide)
    change (mode.toNat &&& 0o7777) &&& 0o7777 = mode.toNat &&& 0o7777
    rw [Nat.and_assoc]
    rfl
  dsimp only
  rw [ite_eq_left htf]
  dsimp only
  rw [hps, ite_eq_right (fun h => by rw [hne_reg] at h; cases h),
    ite_eq_right hnot_maxe, ite_eq_right hnot_maxb, ite_eq_right hnot_trunc]
  rw [hpp, hpun, hpgn, hdec_strs.1, hdec_strs.2.2.1, hdec_strs.2.2.2.1, hdec_strs.2.2.2.2]
  dsimp only [Bind.bind, Except.bind]
  rw [ite_eq_left (by decide : ("" : String).isEmpty = true)]
  rcases h1 : pendingPax.bind (·.path?) with _ | p1 <;>
    rcases h2 : pendingPax.bind (·.uname?) with _ | p2 <;>
    rcases h3 : pendingPax.bind (·.gname?) with _ | p3 <;>
    (simp only [h1, h2, h3, Option.getD_none, Option.getD_some] at hval_path hnul_u hnul_g ⊢;
     rw [hval_path]; dsimp only [Bind.bind, Except.bind];
     have hs' : ¬(seen.contains normPath = true) := by rw [hseen]; simp;
     rw [ite_eq_right hs', hpu, hpg, hpm, hmode_idem])

/-- Single-record `parsePaxPayload` certificate for well-formed `"key=value"` records. -/
theorem parsePaxPayload_kv_single {key value : String} {offset : Nat} {nextOv : PaxOverrides}
    (hmin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hmax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes)
    (hkey_ne : key.isEmpty = false)
    (hkey_nul : hasNulString key = false)
    (hkey_nl : key.toList.contains '\n' = false)
    (hkey_eq : (0x3d : UInt8) ∉ key.toUTF8.toList)
    (hnot_gnu : startsWithStr key "GNU.sparse." = false)
    (happly : applyPaxKey {} key value offset = .ok nextOv) :
    parsePaxPayload (encodePaxRecord key value) offset = .ok nextOv := by
  let pax := encodePaxRecord key value
  rcases encodePaxRecord_parts hmin hmax with ⟨_, _, _, _, hsz_pax⟩
  have hp : 0 < pax.size := by dsimp only [pax]; omega
  have hstep := parsePaxPayload_go_step (bs := pax) (rest := ByteArray.empty) (offset := offset)
    (fuel := pax.size + 1) (pos := 0) (seenKeys := []) (ov := {}) (nextOv := nextOv)
    (key := key) (value := value) (by omega) hmin hmax (by simp [hkey_ne]) (by simp [hkey_nul])
    (by rw [hkey_nl]; rfl) hkey_eq (by simp) (by simp [hnot_gnu]) happly
    (by rw [ByteArray.extract_zero_size, ByteArray.append_empty])
  unfold parsePaxPayload
  rw [hstep]
  have hsz : 0 + pax.size = pax.size := Nat.zero_add _
  have hfuel : pax.size + 1 - 1 = (pax.size - 1) + 1 := by omega
  have hge : pax.size ≥ pax.size := Nat.le_refl _
  rw [hsz, hfuel, parsePaxPayload.go.eq_2, ite_eq_left hge]

/-- `parsePaxPayload` for `path="a.txt"`. -/
theorem parsePax_path_a (off : Nat) :
    parsePaxPayload (encodePaxRecord "path" "a.txt") off = .ok { path? := some "a.txt" } := by
  have hmin : 4 ≤ (" " ++ "path" ++ "=" ++ "a.txt" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hmax : (" " ++ "path" ++ "=" ++ "a.txt" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : (" " ++ "path" ++ "=" ++ "a.txt" ++ "\n").toUTF8.size ≤ 100 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have : maxPaxHeaderBytes = 1048576 := rfl
    omega
  exact parsePaxPayload_kv_single hmin hmax rfl (by decide) (by decide)
    (by rw [toUTF8_toList]; decide) (by decide) rfl

private theorem parsePax_path_safe (off : Nat) :
    parsePaxPayload (encodePaxRecord "path" "safe.txt") off = .ok { path? := some "safe.txt" } := by
  have hmin : 4 ≤ (" " ++ "path" ++ "=" ++ "safe.txt" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hmax : (" " ++ "path" ++ "=" ++ "safe.txt" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : (" " ++ "path" ++ "=" ++ "safe.txt" ++ "\n").toUTF8.size ≤ 100 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have : maxPaxHeaderBytes = 1048576 := rfl
    omega
  exact parsePaxPayload_kv_single hmin hmax rfl (by decide) (by decide)
    (by rw [toUTF8_toList]; decide) (by decide) rfl

private theorem parsePax_size_8g (off : Nat) :
    parsePaxPayload (encodePaxRecord "size" "8589934592") off = .ok { size? := some 8589934592 } := by
  have hmin : 4 ≤ (" " ++ "size" ++ "=" ++ "8589934592" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hmax : (" " ++ "size" ++ "=" ++ "8589934592" ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes := by
    have : (" " ++ "size" ++ "=" ++ "8589934592" ++ "\n").toUTF8.size ≤ 100 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have : maxPaxHeaderBytes = 1048576 := rfl
    omega
  exact parsePaxPayload_kv_single hmin hmax rfl (by decide) (by decide)
    (by rw [toUTF8_toList]; decide) (by decide) rfl

/-- Step `unpackLoop` across one well-formed `mkPaxFrame` block at `pre.size`. -/
theorem unpackLoop_mkPaxFrame_step (opts : UnpackOptions) (pre post pax : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hpax_sz : pax.size ≤ maxPaxHeaderBytes) (ov : PaxOverrides)
    (hparse : parsePaxPayload pax pre.size = .ok ov) :
    unpackLoop opts (pre ++ mkPaxFrame pax ++ post) pre.size none seen acc totalBytes =
      unpackLoop opts (pre ++ mkPaxFrame pax ++ post)
        (pre.size + 512 + pad512 pax.size) (some ov) seen acc totalBytes := by
  let bytes := pre ++ mkPaxFrame pax ++ post
  let off := pre.size
  have hle_pad := le_pad512 pax.size
  have hmax_lt : maxPaxHeaderBytes < ustarOctal11Limit := by
    have h1 : maxPaxHeaderBytes = 1048576 := rfl
    have h2 : ustarOctal11Limit = 8 ^ 11 := rfl
    omega
  have hsz_lt : pax.size < ustarOctal11Limit := Nat.lt_of_le_of_lt hpax_sz hmax_lt
  have hframe_sz : (mkPaxFrame pax).size = 512 + pad512 pax.size := mkPaxFrame_size pax
  have hbytes_sz : bytes.size = off + 512 + pad512 pax.size + post.size := by
    simp only [bytes, off, ByteArray.size_append, hframe_sz]
    omega
  have hh_eq : mkPaxFrame pax =
      mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "" ++ padBlock512 pax := rfl
  have hext_hdr : bytes.extract off (off + 512) =
      mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "" := by
    have hassoc : bytes = pre ++ mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "" ++
        (padBlock512 pax ++ post) := by
      simp only [bytes, hh_eq, ByteArray.append_assoc]
    rw [hassoc]
    have h := extract_append_mid pre (mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "")
      (padBlock512 pax ++ post)
    rw [mkUstarHeader_size] at h
    exact h
  have hnz : isZeroRange bytes off 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_hdr
  have hparse_hdr : parseUstarHeader bytes off =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := pax.size, mtime := 0, typeflag := 0x78 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) hsz_lt (by decide)
      (by rw [hbytes_sz]; omega) hext_hdr
  have hext_pax : bytes.extract (off + 512) (off + 512 + pax.size) = pax := by
    have hext_pad : bytes.extract (off + 512) (off + 512 + pad512 pax.size) = padBlock512 pax := by
      have hassoc : bytes = (pre ++ mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "") ++
          padBlock512 pax ++ post := by
        simp only [bytes, hh_eq, ByteArray.append_assoc]
      have hpre_sz : (pre ++ mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "").size =
          off + 512 := by
        rw [ByteArray.size_append, mkUstarHeader_size]
      rw [hassoc, ← hpre_sz]
      have h := extract_append_mid
        (pre ++ mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "")
        (padBlock512 pax) post
      rw [padBlock512_size] at h
      exact h
    have hsub_ext : (bytes.extract (off + 512) (off + 512 + pad512 pax.size)).extract 0 pax.size =
        bytes.extract (off + 512) (off + 512 + pax.size) := by
      rw [ByteArray.extract_extract, Nat.add_zero]
      apply congrArg (bytes.extract (off + 512))
      omega
    rw [← hsub_ext, hext_pad, padBlock512_extract_prefix]
  have hparse' : parsePaxPayload pax off = .ok ov := hparse
  have hnotge : ¬(off ≥ bytes.size) := by rw [hbytes_sz]; omega
  have hnotgt512 : ¬(off + 512 > bytes.size) := by rw [hbytes_sz]; omega
  have hnotgt_pax : ¬(pax.size > maxPaxHeaderBytes) := by omega
  have hnotgt_end : ¬(off + 512 + pad512 pax.size > bytes.size) := by rw [hbytes_sz]; omega
  have hadv : off + 512 + pad512 pax.size > off := by omega
  refine unpackLoop_step_continue opts bytes off none seen acc totalBytes
    (off + 512 + pad512 pax.size) (some ov) seen acc totalBytes (by rw [hbytes_sz]; omega) ?_ hadv
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt512, hparse_hdr, beq_self_eq_true,
    Option.isSome_none, hnotgt_pax, hnotgt_end, hext_pax, hparse']

/-- Step `unpackLoop` across one valid `mkRegularFrame` block at `pre.size`. -/
theorem unpackLoop_mkRegularFrame_step (opts : UnpackOptions) (pre post : ByteArray)
    (path : String) (data : ByteArray) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hnm_sz : path.toUTF8.size ≤ 100) (hnm_nul : !hasNulString path = true)
    (hdata_sz : data.size < ustarOctal11Limit)
    {normPath : String}
    (hval_path : validateEntryPath opts.allowAbsolute opts.allowParentTraversal .regular path = .ok normPath)
    (hseen : seen.contains normPath = false)
    (hentries : acc.length + 1 ≤ opts.maxEntries)
    (hbytes : totalBytes + data.size ≤ opts.maxTotalBytes) :
    let entry : TarEntry :=
      { path := normPath, kind := .regular, mode := 0o644, uid := 0, gid := 0, mtime := 0,
        uname := "", gname := "", data := data, linkTarget := "" }
    unpackLoop opts (pre ++ mkRegularFrame path data ++ post) pre.size none seen acc totalBytes =
      unpackLoop opts (pre ++ mkRegularFrame path data ++ post)
        (pre.size + 512 + pad512 data.size) none (normPath :: seen) (entry :: acc) (totalBytes + data.size) := by
  let bytes := pre ++ mkRegularFrame path data ++ post
  let off := pre.size
  have hle_pad := le_pad512 data.size
  have hframe_sz : (mkRegularFrame path data).size = 512 + pad512 data.size := mkRegularFrame_size path data
  have hbytes_sz : bytes.size = off + 512 + pad512 data.size + post.size := by
    simp only [bytes, off, ByteArray.size_append, hframe_sz]
    omega
  have hh_eq : mkRegularFrame path data =
      mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "" ++ padBlock512 data := rfl
  have hext_hdr : bytes.extract off (off + 512) =
      mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "" := by
    have hassoc : bytes = pre ++ mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "" ++
        (padBlock512 data ++ post) := by
      simp only [bytes, hh_eq, ByteArray.append_assoc]
    rw [hassoc]
    have h := extract_append_mid pre (mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "")
      (padBlock512 data ++ post)
    rw [mkUstarHeader_size] at h
    exact h
  have hnz : isZeroRange bytes off 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_hdr
  have hparse_hdr : parseUstarHeader bytes off =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := data.size, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) hdata_sz (by decide)
      (by rw [hbytes_sz]; omega) hext_hdr
  have hext_data : bytes.extract (off + 512) (off + 512 + data.size) = data := by
    have hext_pad : bytes.extract (off + 512) (off + 512 + pad512 data.size) = padBlock512 data := by
      have hassoc : bytes = (pre ++ mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "") ++
          padBlock512 data ++ post := by
        simp only [bytes, hh_eq, ByteArray.append_assoc]
      have hpre_sz : (pre ++ mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "").size =
          off + 512 := by
        rw [ByteArray.size_append, mkUstarHeader_size]
      rw [hassoc, ← hpre_sz]
      have h := extract_append_mid
        (pre ++ mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "")
        (padBlock512 data) post
      rw [padBlock512_size] at h
      exact h
    have hsub_ext : (bytes.extract (off + 512) (off + 512 + pad512 data.size)).extract 0 data.size =
        bytes.extract (off + 512) (off + 512 + data.size) := by
      rw [ByteArray.extract_extract, Nat.add_zero]
      apply congrArg (bytes.extract (off + 512))
      omega
    rw [← hsub_ext, hext_pad, padBlock512_extract_prefix]
  have hpay_eq : (if data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + data.size)) = data := by
    rw [hext_data]
    by_cases hdz : data.size = 0
    · simp only [hdz, beq_self_eq_true, ↓reduceIte]
      symm
      apply ByteArray.ext
      apply Array.ext
      · simp [hdz]
      · intro i hi
        simp [hdz] at hi
    · simp [hdz]
  have hdec := decodeTarEntry_mkUstarHeader_regular opts bytes
    (mkUstarHeader path 0o644 0 0 data.size 0 0x30 "" "" "" "") off none seen acc.length totalBytes
    (by rw [hbytes_sz]; omega) hext_hdr rfl hnm_sz hnm_nul (by decide) (by decide) hdata_sz (by decide)
    hval_path hseen (by decide) (by decide) hentries hbytes
    (by simp only [Option.bind, Option.getD]; rw [hbytes_sz]; omega)
  dsimp only [Option.bind, Option.getD] at hdec
  rw [hpay_eq] at hdec
  have hmode_val : (((0o644 : UInt32) &&& 0o7777).toNat.toUInt32) = 0o644 := by decide
  rw [hmode_val] at hdec
  have hnotge : ¬(off ≥ bytes.size) := by rw [hbytes_sz]; omega
  have hnotgt512 : ¬(off + 512 > bytes.size) := by rw [hbytes_sz]; omega
  have hadv : off + 512 + pad512 data.size > off := by omega
  refine unpackLoop_step_continue opts bytes off none seen acc totalBytes
    (off + 512 + pad512 data.size) none (normPath :: seen)
    ({ path := normPath, kind := .regular, mode := 0o644, uid := 0, gid := 0, mtime := 0,
       uname := "", gname := "", data := data, linkTarget := "" } :: acc)
    (totalBytes + data.size) (by rw [hbytes_sz]; omega) ?_ hadv
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt512, hparse_hdr,
    show ((0x30 : UInt8) == 0x78) = false from rfl, hdec]

private theorem regFrame_a_txt_step (opts : UnpackOptions) (post : ByteArray)
    (hentries : 1 ≤ opts.maxEntries) (hbytes : 2 ≤ opts.maxTotalBytes) :
    unpackLoop opts (mkRegularFrame "a.txt" "hi".toUTF8 ++ post) 0 none [] [] 0 =
      unpackLoop opts (mkRegularFrame "a.txt" "hi".toUTF8 ++ post) 1024 none ["a.txt"]
        [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2 := by
  have hnm_sz : ("a.txt" : String).toUTF8.size ≤ 100 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hnm_nul : !hasNulString "a.txt" = true := by decide
  have hdat_sz : ("hi".toUTF8).size = 2 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hdat_lt : ("hi".toUTF8).size < ustarOctal11Limit := by
    have : ustarOctal11Limit = 8 ^ 11 := rfl
    omega
  have hstep := unpackLoop_mkRegularFrame_step opts ByteArray.empty post "a.txt" "hi".toUTF8 [] [] 0
    hnm_sz hnm_nul hdat_lt rfl rfl hentries (by omega)
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add, hdat_sz] at hstep
  exact hstep

private theorem test4_h4 :
    ∃ e, Impl.unpackWith {} (mkRegularFrame "a.txt" "hi".toUTF8) = .error e ∧
      e.kind = .truncatedArchive ∧ (!e.message.isEmpty) = true := by
  let frame := mkRegularFrame "a.txt" "hi".toUTF8
  have hdat_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hframe_sz : frame.size = 1024 := by rw [mkRegularFrame_size, hdat_sz]; decide
  have hnz : (frame.size == 0 || frame.size % 512 != 0) = false := by rw [hframe_sz]; rfl
  have hstep := regFrame_a_txt_step {} ByteArray.empty (by decide) (by decide)
  rw [ByteArray.append_empty] at hstep
  have hdone : unpackLoop {} frame 1024 none ["a.txt"]
      [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2 =
      .error { kind := .truncatedArchive, message := "tar archive missing end-of-archive zero blocks",
               offset := some 1024 } :=
    unpackLoop_at_ge {} frame 1024 none _ _ _ (by rw [hframe_sz]; exact Nat.le_refl _)
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep, hdone]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem test4_h5 :
    ∃ e, Impl.unpackWith {} (mkRegularFrame "a.txt" "hi".toUTF8 ++ zeroBlock) = .error e ∧
      e.kind = .truncatedArchive ∧ (!e.message.isEmpty) = true := by
  let frame := mkRegularFrame "a.txt" "hi".toUTF8
  let bytes := frame ++ zeroBlock
  have hdat_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hframe_sz : frame.size = 1024 := by rw [mkRegularFrame_size, hdat_sz]; decide
  have hbytes_sz : bytes.size = 1536 := by simp only [bytes, ByteArray.size_append, hframe_sz, zeroBlock_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hstep := regFrame_a_txt_step {} zeroBlock (by decide) (by decide)
  have hz1 : isZeroRange bytes 1024 512 = true := by
    refine isZeroRange_zeroBlock hframe_sz (by rw [zeroBlock_size]; exact Nat.le_refl _)
      (fun _ _ => zeroBlock_getElem _)
  have herr : unpackLoop {} bytes 1024 none ["a.txt"]
      [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2 =
      .error { kind := .truncatedArchive,
               message := "tar archive has only one trailing zero block",
               offset := some 1024 } := by
    refine unpackLoop_step_err {} bytes 1024 none _ _ _ _ (by rw [hbytes_sz]; omega) ?_
    unfold unpackStep
    have hnotge : ¬(1024 ≥ bytes.size) := by rw [hbytes_sz]; omega
    have hge2 : 1024 + 512 ≥ bytes.size := by rw [hbytes_sz]; omega
    simp only [hnotge, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true, hge2]
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep, herr]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem test4_h6 :
    ∃ e, Impl.unpackWith {} (mkRegularFrame "a.txt" "hi".toUTF8 ++ zeroBlock ++ mkRegularFrame "a.txt" "hi".toUTF8) = .error e ∧
      e.kind = .invalidHeader ∧ (!e.message.isEmpty) = true := by
  let frame := mkRegularFrame "a.txt" "hi".toUTF8
  let bytes := frame ++ zeroBlock ++ frame
  have hdat_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hframe_sz : frame.size = 1024 := by rw [mkRegularFrame_size, hdat_sz]; decide
  have hbytes_sz : bytes.size = 2560 := by
    simp only [bytes, ByteArray.size_append, hframe_sz, zeroBlock_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hstep : unpackLoop {} bytes 0 none [] [] 0 =
      unpackLoop {} bytes 1024 none ["a.txt"]
        [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2 := by
    dsimp only [bytes]
    rw [ByteArray.append_assoc]
    exact regFrame_a_txt_step {} (zeroBlock ++ frame) (by decide) (by decide)
  have hz1 : isZeroRange bytes 1024 512 = true := by
    dsimp only [bytes]
    rw [ByteArray.append_assoc]
    refine isZeroRange_zeroBlock hframe_sz (by rw [ByteArray.size_append, zeroBlock_size, hframe_sz]; omega) ?_
    intro i hi
    rw [getElem_append_left (by rw [zeroBlock_size]; omega)]
    exact zeroBlock_getElem _
  have hext_hdr2 : bytes.extract 1536 (1536 + 512) =
      mkUstarHeader "a.txt" 0o644 0 0 ("hi".toUTF8).size 0 0x30 "" "" "" "" := by
    have hpre_sz : (frame ++ zeroBlock).size = 1536 := by
      rw [ByteArray.size_append, hframe_sz, zeroBlock_size]
    have hassoc : bytes = (frame ++ zeroBlock) ++
        mkUstarHeader "a.txt" 0o644 0 0 ("hi".toUTF8).size 0 0x30 "" "" "" "" ++ padBlock512 "hi".toUTF8 := by
      simp only [bytes, frame, mkRegularFrame, ByteArray.append_assoc]
    rw [hassoc, ← hpre_sz]
    have h := extract_append_mid (frame ++ zeroBlock)
      (mkUstarHeader "a.txt" 0o644 0 0 ("hi".toUTF8).size 0 0x30 "" "" "" "") (padBlock512 "hi".toUTF8)
    rw [mkUstarHeader_size] at h
    exact h
  have hnz2 : isZeroRange bytes 1536 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_hdr2
  have herr : unpackLoop {} bytes 1024 none ["a.txt"]
      [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2 =
      .error { kind := .invalidHeader,
               message := "non-zero block after single zero block",
               offset := some (1024 + 512) } := by
    refine unpackLoop_step_err {} bytes 1024 none _ _ _ _ (by rw [hbytes_sz]; omega) ?_
    unfold unpackStep
    have hnotge : ¬(1024 ≥ bytes.size) := by rw [hbytes_sz]; omega
    have hnotge2 : ¬(1024 + 512 ≥ bytes.size) := by rw [hbytes_sz]; omega
    simp only [hnotge, hnotge2, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true,
      Bool.not_false, show 1024 + 512 = 1536 from rfl, hnz2]
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep, herr]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem pax_a_txt_sz : (encodePaxRecord "path" "a.txt").size ≤ maxPaxHeaderBytes := by
  have hmin : 4 ≤ (" " ++ "path" ++ "=" ++ "a.txt" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hmax : (" " ++ "path" ++ "=" ++ "a.txt" ++ "\n").toUTF8.size ≤ 100 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have ⟨_, hlt⟩ := encodePaxRecord_size_lt_512 hmin hmax
  have : maxPaxHeaderBytes = 1048576 := rfl
  omega

private theorem pax_a_txt_pad_sz :
    512 + pad512 (encodePaxRecord "path" "a.txt").size = 1024 := by
  have hmin : 4 ≤ (" " ++ "path" ++ "=" ++ "a.txt" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hmax : (" " ++ "path" ++ "=" ++ "a.txt" ++ "\n").toUTF8.size ≤ 100 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have ⟨hpos, hlt⟩ := encodePaxRecord_size_lt_512 hmin hmax
  have hpad : pad512 (encodePaxRecord "path" "a.txt").size = 512 := by
    unfold pad512
    have hq : ((encodePaxRecord "path" "a.txt").size + 511) / 512 = 1 := by omega
    rw [hq]
  rw [hpad]

private theorem test4_h7_h8_h9 :
    (∃ e, Impl.unpackWith {} (mkPaxFrame (encodePaxRecord "path" "a.txt")) = .error e ∧
      e.kind = .truncatedArchive ∧ (!e.message.isEmpty) = true) ∧
    (∃ e, Impl.unpackWith {} (mkPaxFrame (encodePaxRecord "path" "a.txt") ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ (!e.message.isEmpty) = true) ∧
    (∃ e, Impl.unpackWith {} (mkPaxFrame (encodePaxRecord "path" "a.txt") ++
        mkPaxFrame (encodePaxRecord "path" "a.txt") ++
        mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks) = .error e ∧
      e.kind = .invalidHeader ∧ (!e.message.isEmpty) = true) := by
  let pax := encodePaxRecord "path" "a.txt"
  let paxHdr := mkPaxFrame pax
  have hframe_sz : paxHdr.size = 1024 := by
    dsimp only [paxHdr, pax]
    rw [mkPaxFrame_size]
    exact pax_a_txt_pad_sz
  have hpax_step : ∀ (post : ByteArray),
      unpackLoop {} (paxHdr ++ post) 0 none [] [] 0 =
        unpackLoop {} (paxHdr ++ post) 1024 (some { path? := some "a.txt" }) [] [] 0 := by
    intro post
    have h := unpackLoop_mkPaxFrame_step {} ByteArray.empty post pax [] [] 0
      pax_a_txt_sz { path? := some "a.txt" } (parsePax_path_a 0)
    rw [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at h
    have hpax_pad : 512 + pad512 pax.size = 1024 := pax_a_txt_pad_sz
    rw [hpax_pad] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · have hnz : (paxHdr.size == 0 || paxHdr.size % 512 != 0) = false := by rw [hframe_sz]; rfl
    have hs := hpax_step ByteArray.empty
    rw [ByteArray.append_empty] at hs
    have hdone : unpackLoop {} paxHdr 1024 (some { path? := some "a.txt" }) [] [] 0 =
        .error { kind := .truncatedArchive, message := "tar archive missing end-of-archive zero blocks",
                 offset := some 1024 } :=
      unpackLoop_at_ge {} paxHdr 1024 _ [] [] 0 (by rw [hframe_sz]; exact Nat.le_refl _)
    unfold Impl.unpackWith
    rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hs, hdone]
    exact ⟨_, rfl, rfl, by decide⟩
  · let bytes := paxHdr ++ twoZeroBlocks
    have hbytes_sz : bytes.size = 2048 := by rw [ByteArray.size_append, hframe_sz, twoZeroBlocks_size]
    have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
    have hz1 : isZeroRange bytes 1024 512 = true := by
      have h1 := isZeroRange_twoZeroBlocks_fst paxHdr ByteArray.empty
      rw [ByteArray.append_empty, hframe_sz] at h1
      exact h1
    have herr : unpackLoop {} bytes 1024 (some { path? := some "a.txt" }) [] [] 0 =
        .error { kind := .invalidHeader,
                 message := "dangling PAX header before zero block",
                 offset := some 1024 } := by
      refine unpackLoop_step_err {} bytes 1024 _ _ _ _ _ (by rw [hbytes_sz]; omega) ?_
      unfold unpackStep
      have hnotge : ¬(1024 ≥ bytes.size) := by rw [hbytes_sz]; omega
      simp only [hnotge, ↓reduceIte, hz1, Option.isSome_some]
    unfold Impl.unpackWith
    rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hpax_step twoZeroBlocks, herr]
    exact ⟨_, rfl, rfl, by decide⟩
  · let reg := mkRegularFrame "a.txt" "hi".toUTF8
    let post := paxHdr ++ reg ++ twoZeroBlocks
    let bytes := paxHdr ++ paxHdr ++ reg ++ twoZeroBlocks
    have hdat_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hreg_sz : reg.size = 1024 := by rw [mkRegularFrame_size, hdat_sz]; decide
    have hbytes_sz : bytes.size = 4096 := by
      simp only [bytes, ByteArray.size_append, hframe_sz, hreg_sz, twoZeroBlocks_size]
    have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
    have hassoc : bytes = paxHdr ++ post := by simp only [bytes, post, ByteArray.append_assoc]
    have hext2 : bytes.extract 1024 (1024 + 512) =
        mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "" := by
      have hassoc2 : bytes = paxHdr ++
          mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "" ++
          (padBlock512 pax ++ reg ++ twoZeroBlocks) := by
        simp only [bytes, paxHdr, mkPaxFrame, ByteArray.append_assoc]
      rw [hassoc2, ← hframe_sz]
      have h := extract_append_mid paxHdr
        (mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "")
        (padBlock512 pax ++ reg ++ twoZeroBlocks)
      rw [mkUstarHeader_size] at h
      exact h
    have hnz2 : isZeroRange bytes 1024 512 = false :=
      isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext2
    have hsz_lt : pax.size < ustarOctal11Limit := by
      have hle : pax.size ≤ maxPaxHeaderBytes := pax_a_txt_sz
      have : maxPaxHeaderBytes = 1048576 := rfl
      have : ustarOctal11Limit = 8 ^ 11 := rfl
      omega
    have hparse2 : parseUstarHeader bytes 1024 =
        .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
              size := pax.size, mtime := 0, typeflag := 0x78 } :=
      parseUstarHeader_mkUstarHeader (by decide) (by decide) hsz_lt (by decide)
        (by rw [hbytes_sz]; omega) hext2
    have herr : unpackLoop {} bytes 1024 (some { path? := some "a.txt" }) [] [] 0 =
        .error { kind := .invalidHeader,
                 message := "consecutive PAX 'x' headers are not allowed",
                 offset := some 1024 } := by
      refine unpackLoop_step_err {} bytes 1024 _ _ _ _ _ (by rw [hbytes_sz]; omega) ?_
      unfold unpackStep
      have hnotge : ¬(1024 ≥ bytes.size) := by rw [hbytes_sz]; omega
      have hnotgt : ¬(1024 + 512 > bytes.size) := by rw [hbytes_sz]; omega
      simp only [hnotge, ↓reduceIte, hnz2, Bool.false_eq_true, hnotgt, hparse2, beq_self_eq_true,
        Option.isSome_some]
    unfold Impl.unpackWith
    have hgoal_eq : mkPaxFrame (encodePaxRecord "path" "a.txt") ++ mkPaxFrame (encodePaxRecord "path" "a.txt") ++
        mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks = paxHdr ++ post := hassoc
    rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hgoal_eq, hpax_step post, ← hassoc, herr]
    exact ⟨_, rfl, rfl, by decide⟩

private theorem test4_h10 :
    ∃ e, Impl.unpackWith {} (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ mkRegularFrame "a.txt" "hi".toUTF8) = .error e ∧
      e.kind = .invalidHeader ∧ (!e.message.isEmpty) = true := by
  let frame := mkRegularFrame "a.txt" "hi".toUTF8
  let bytes := frame ++ twoZeroBlocks ++ frame
  have hdat_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hframe_sz : frame.size = 1024 := by rw [mkRegularFrame_size, hdat_sz]; decide
  have hbytes_sz : bytes.size = 3072 := by
    simp only [bytes, ByteArray.size_append, hframe_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hstep : unpackLoop {} bytes 0 none [] [] 0 =
      unpackLoop {} bytes 1024 none ["a.txt"]
        [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2 := by
    dsimp only [bytes]
    rw [ByteArray.append_assoc]
    exact regFrame_a_txt_step {} (twoZeroBlocks ++ frame) (by decide) (by decide)
  have hz1 : isZeroRange bytes 1024 512 = true := by
    have h1 := isZeroRange_twoZeroBlocks_fst frame frame
    rw [hframe_sz] at h1
    exact h1
  have hz2 : isZeroRange bytes 1536 512 = true := by
    have h1 := isZeroRange_twoZeroBlocks_snd frame frame
    rw [hframe_sz] at h1
    exact h1
  have hext_trail : bytes.extract 2048 (2048 + 512) =
      mkUstarHeader "a.txt" 0o644 0 0 ("hi".toUTF8).size 0 0x30 "" "" "" "" := by
    have hpre_sz : (frame ++ twoZeroBlocks).size = 2048 := by
      rw [ByteArray.size_append, hframe_sz, twoZeroBlocks_size]
    have hassoc : bytes = (frame ++ twoZeroBlocks) ++
        mkUstarHeader "a.txt" 0o644 0 0 ("hi".toUTF8).size 0 0x30 "" "" "" "" ++ padBlock512 "hi".toUTF8 := by
      simp only [bytes, frame, mkRegularFrame, ByteArray.append_assoc]
    rw [hassoc, ← hpre_sz]
    have h := extract_append_mid (frame ++ twoZeroBlocks)
      (mkUstarHeader "a.txt" 0o644 0 0 ("hi".toUTF8).size 0 0x30 "" "" "" "") (padBlock512 "hi".toUTF8)
    rw [mkUstarHeader_size] at h
    exact h
  have hnz_trail : isZeroRange bytes 2048 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_trail
  have htr : allZeroTrailer bytes 2048 = false := by
    unfold allZeroTrailer
    rw [hbytes_sz]
    rw [allZeroTrailer.go.eq_2, ite_eq_right (by omega), hnz_trail]
    rfl
  have herr : unpackLoop {} bytes 1024 none ["a.txt"]
      [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2 =
      .error { kind := .invalidHeader,
               message := "non-zero garbage after tar end-of-archive marker",
               offset := some (1024 + 1024) } := by
    refine unpackLoop_step_err {} bytes 1024 none _ _ _ _ (by rw [hbytes_sz]; omega) ?_
    unfold unpackStep
    have hnotge : ¬(1024 ≥ bytes.size) := by rw [hbytes_sz]; omega
    have hnotge2 : ¬(1024 + 512 ≥ bytes.size) := by rw [hbytes_sz]; omega
    simp only [hnotge, hnotge2, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true,
      show 1024 + 512 = 1536 from rfl, hz2,
      show 1024 + 1024 = 2048 from rfl, htr, Bool.not_true, Bool.not_false]
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep, herr]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem test4_paddedArchive_ok :
    ∃ res, Impl.unpackWith {}
        (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock) =
        .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular, data := "hi".toUTF8 }] res := by
  let frame := mkRegularFrame "a.txt" "hi".toUTF8
  let pad := zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock
  let bytes := frame ++ twoZeroBlocks ++ pad
  have hdat_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hframe_sz : frame.size = 1024 := by rw [mkRegularFrame_size, hdat_sz]; decide
  have hpad_sz : pad.size = 2048 := by
    simp only [pad, ByteArray.size_append, zeroBlock_size]
  have hbytes_sz : bytes.size = 4096 := by
    simp only [bytes, ByteArray.size_append, hframe_sz, twoZeroBlocks_size, hpad_sz]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hassoc : bytes = frame ++ (twoZeroBlocks ++ pad) := ByteArray.append_assoc
  have hstep := regFrame_a_txt_step {} (twoZeroBlocks ++ pad) (by decide) (by decide)
  rw [← hassoc] at hstep
  have hpad_zero : ∀ k (hk : k < pad.size), pad[k]'hk = 0 := by
    intro k hk
    have hlt_split : ∀ (x y : ByteArray) (i : Nat) (hi : i < (x ++ y).size),
        (∀ a (ha : a < x.size), x[a]'ha = 0) →
        (∀ b (hb : b < y.size), y[b]'hb = 0) → (x ++ y)[i]'hi = 0 := by
      intro x y i hi hx hy
      by_cases hix : i < x.size
      · rw [getElem_append_left hix]; exact hx i hix
      · have hge : x.size ≤ i := by omega
        rw [getElem_append_right hge]; exact hy (i - x.size) (by rw [ByteArray.size_append] at hi; omega)
    have hzb : ∀ i (hi : i < zeroBlock.size), zeroBlock[i]'hi = 0 := fun i hi => zeroBlock_getElem hi
    have hzb2 : ∀ i (hi : i < (zeroBlock ++ zeroBlock).size), (zeroBlock ++ zeroBlock)[i]'hi = 0 :=
      fun i hi => hlt_split _ _ i hi hzb hzb
    have hzb3 : ∀ i (hi : i < ((zeroBlock ++ zeroBlock) ++ zeroBlock).size),
        ((zeroBlock ++ zeroBlock) ++ zeroBlock)[i]'hi = 0 :=
      fun i hi => hlt_split _ _ i hi hzb2 hzb
    exact hlt_split _ _ k hk hzb3 hzb
  have hdone := unpackLoop_at_padded_twoZeroBlocks {} frame pad ["a.txt"]
    [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] 2
    (by rw [hpad_sz]) hpad_zero
  rw [hframe_sz] at hdone
  have hunpack : Impl.unpackWith {}
      (frame ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock) =
      .ok [{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }] := by
    have heq : frame ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock = bytes := by
      simp only [bytes, pad, ByteArray.append_assoc]
    rw [heq]
    unfold Impl.unpackWith
    rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep, hdone]
    rfl
  exact ⟨[{ path := "a.txt", kind := .regular, mode := 0o644, data := "hi".toUTF8 }], hunpack,
    tarEquiv_singleton_self _⟩

private theorem ab_utf8_eq : "AB".toUTF8 = ByteArray.mk #[0x41, 0x42] := by
  apply ByteArray.ext
  apply Array.ext
  · change ("AB".toUTF8).size = 2
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]
    decide
  · intro i hi1 hi2
    have h1 := byteArray_toList_eq "AB".toUTF8
    have h2 : "AB".toUTF8.toList = [0x41, 0x42] := by rw [toUTF8_toList]; decide
    have hmem := congrArg (fun l => l[i]?) (h1.symm.trans h2)
    have hl1 : i < "AB".toUTF8.data.toList.length := hi1
    have hl2 : i < ([0x41, 0x42] : List UInt8).length := hi2
    have hi2_lt : i < 2 := hi2
    simp only [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2, Array.getElem_toList,
      Option.some.injEq] at hmem
    rw [hmem]
    rcases i with _ | _ | k
    · rfl
    · rfl
    · omega

private theorem mk_ab_tail_extract_2 (tail : Array UInt8) :
    (ByteArray.mk (#[0x41, 0x42] ++ tail)).extract 0 2 = ByteArray.mk #[0x41, 0x42] := by
  apply ByteArray.ext
  apply Array.ext
  · change ((ByteArray.mk (#[0x41, 0x42] ++ tail)).extract 0 2).size = 2
    rw [ByteArray.size_extract,
      show (ByteArray.mk (#[0x41, 0x42] ++ tail)).size = (#[0x41, 0x42] ++ tail).size from rfl,
      Array.size_append, show (#[0x41, 0x42] : Array UInt8).size = 2 from rfl]
    omega
  · intro i hi1 hi2
    have hi2' : i < (#[0x41, 0x42] : Array UInt8).size := hi2
    have hi2_lt : i < 2 := hi2'
    have hi_dirty : i < (ByteArray.mk (#[0x41, 0x42] ++ tail)).size := by
      rw [show (ByteArray.mk (#[0x41, 0x42] ++ tail)).size = (#[0x41, 0x42] ++ tail).size from rfl,
        Array.size_append, show (#[0x41, 0x42] : Array UInt8).size = 2 from rfl]
      omega
    have h2a : ((ByteArray.mk (#[0x41, 0x42] ++ tail)).extract 0 2).data[i]'hi1 =
        (ByteArray.mk (#[0x41, 0x42] ++ tail))[i]'hi_dirty := by
      rw [← ByteArray.getElem_eq_getElem_data (h := hi1)]
      simp only [ByteArray.getElem_extract, Nat.zero_add]
    have h2b : (ByteArray.mk (#[0x41, 0x42] ++ tail))[i]'hi_dirty = (#[0x41, 0x42] : Array UInt8)[i]'hi2' := by
      rw [ByteArray.getElem_eq_getElem_data (h := hi_dirty)]
      exact Array.getElem_append_left (xs := #[0x41, 0x42]) (ys := tail) hi2'
    exact h2a.trans (h2b.trans (ByteArray.getElem_eq_getElem_data (h := hi2_lt)).symm)

private theorem unpackStep_nonPax_of_decode_ok
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

private theorem unpackStep_nonPax_of_decode_err
    (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hbd : offset + 512 ≤ bytes.size)
    (hnz : isZeroRange bytes offset 512 = false)
    {hdr : UstarHeaderFields} (htf_not78 : (hdr.typeflag == 0x78) = false)
    (hparse : parseUstarHeader bytes offset = .ok hdr)
    {err : TarError}
    (hdec : decodeTarEntry opts bytes offset hdr pendingPax seen acc.length totalBytes = .error err) :
    unpackStep opts bytes offset pendingPax seen acc totalBytes = .error err := by
  have hnotge : ¬(offset ≥ bytes.size) := by omega
  have hnotgt512 : ¬(offset + 512 > bytes.size) := by omega
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt512, hparse, htf_not78, hdec]

private theorem unpackStep_regular_precheck_err
    (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hbd : offset + 512 ≤ bytes.size)
    (hnz : isZeroRange bytes offset 512 = false)
    {mode : UInt32} {uid gid hdrSize mtime : Nat}
    (hparse : parseUstarHeader bytes offset = .ok { mode := (mode &&& 0o7777).toNat, uid := uid, gid := gid, size := hdrSize, mtime := mtime, typeflag := 0x30 })
    (expectedKind : TarErrorKind)
    (herr_case :
      (acc.length + 1 > opts.maxEntries ∧ expectedKind = .resourceLimitExceeded) ∨
      (¬(acc.length + 1 > opts.maxEntries) ∧
        totalBytes + (pendingPax.bind (·.size?) |>.getD hdrSize) > opts.maxTotalBytes ∧
        expectedKind = .resourceLimitExceeded) ∨
      (¬(acc.length + 1 > opts.maxEntries) ∧
        ¬(totalBytes + (pendingPax.bind (·.size?) |>.getD hdrSize) > opts.maxTotalBytes) ∧
        offset + 512 + pad512 (pendingPax.bind (·.size?) |>.getD hdrSize) > bytes.size ∧
        expectedKind = .truncatedArchive)) :
    ∃ e, unpackStep opts bytes offset pendingPax seen acc totalBytes = .error e ∧
      e.kind = expectedKind ∧ (!e.message.isEmpty) = true := by
  have hnotge : ¬(offset ≥ bytes.size) := by omega
  have hnotgt512 : ¬(offset + 512 > bytes.size) := by omega
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt512, hparse,
    show ((0x30 : UInt8) == 0x78) = false from rfl]
  rw [decodeTarEntry.eq_1]
  have htf : ((0x30 : UInt8) == 0x30 || (0x30 : UInt8) == 0x00) = true := rfl
  dsimp only
  rw [ite_eq_left htf]
  cases pendingPax with
  | none =>
    simp only [Option.bind, Option.getD] at herr_case ⊢
    rw [show (EntryKind.regular != EntryKind.regular) = false from rfl, Bool.false_and,
      ite_eq_right Bool.false_ne_true]
    rcases herr_case with ⟨h1, hk⟩ | ⟨h1, h2, hk⟩ | ⟨h1, h2, h3, hk⟩
    · rw [ite_eq_left h1, hk]; exact ⟨_, rfl, rfl, by dsimp only; decide⟩
    · rw [ite_eq_right h1, ite_eq_left h2, hk]; exact ⟨_, rfl, rfl, by dsimp only; decide⟩
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, hk]; exact ⟨_, rfl, rfl, by dsimp only; decide⟩
  | some p =>
    simp only [Option.bind, Option.getD] at herr_case ⊢
    rw [show (EntryKind.regular != EntryKind.regular) = false from rfl, Bool.false_and,
      ite_eq_right Bool.false_ne_true]
    rcases herr_case with ⟨h1, hk⟩ | ⟨h1, h2, hk⟩ | ⟨h1, h2, h3, hk⟩
    · rw [ite_eq_left h1, hk]; exact ⟨_, rfl, rfl, by dsimp only; decide⟩
    · rw [ite_eq_right h1, ite_eq_left h2, hk]; exact ⟨_, rfl, rfl, by dsimp only; decide⟩
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, hk]; exact ⟨_, rfl, rfl, by dsimp only; decide⟩

private theorem test4_dirtyData_ok :
    let hdr := mkUstarHeader "p.txt" 0o644 0 0 2 0 0x30 "" "" "" ""
    let dirtyData := ByteArray.mk (#[0x41, 0x42] ++ Array.replicate 510 0xff)
    ∃ res, Impl.unpackWith {} (hdr ++ dirtyData ++ twoZeroBlocks) = .ok res ∧
      TarEquiv [{ path := "p.txt", kind := .regular, data := "AB".toUTF8 }] res := by
  intro hdr dirtyData
  let bytes := hdr ++ dirtyData ++ twoZeroBlocks
  have hhdr_sz : hdr.size = 512 := mkUstarHeader_size ..
  have hdirty_sz : dirtyData.size = 512 := by
    simp [dirtyData, ByteArray.size, Array.size_append, Array.size_replicate]
  have hbytes_sz : bytes.size = 2048 := by
    simp only [bytes, ByteArray.size_append, hhdr_sz, hdirty_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hext_hdr : bytes.extract 0 512 = hdr := by
    have h := extract_append_mid ByteArray.empty hdr (dirtyData ++ twoZeroBlocks)
    simp only [ByteArray.size_empty, Nat.zero_add, ByteArray.empty_append, hhdr_sz] at h
    simpa only [bytes, ByteArray.append_assoc] using h
  have hnz_hdr : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_hdr
  have hparse_hdr : parseUstarHeader bytes 0 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 2, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_hdr
  have hext_data : bytes.extract 512 514 = "AB".toUTF8 := by
    have h1 : bytes.extract 512 1024 = dirtyData := by
      have h := extract_append_mid hdr dirtyData twoZeroBlocks
      rw [hhdr_sz, hdirty_sz] at h
      exact h
    have h2 : dirtyData.extract 0 2 = ByteArray.mk #[0x41, 0x42] :=
      mk_ab_tail_extract_2 (Array.replicate 510 0xff)
    have h3 : (bytes.extract 512 1024).extract 0 2 = bytes.extract 512 514 := by
      rw [ByteArray.extract_extract, Nat.add_zero]
      apply congrArg (bytes.extract 512)
      omega
    rw [← h3, h1, h2, ab_utf8_eq]
  have hnm_sz : ("p.txt" : String).toUTF8.size ≤ 100 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hnm_nul : !hasNulString "p.txt" = true := by decide
  have hdec := decodeTarEntry_mkUstarHeader_regular {} bytes hdr 0 none [] 0 0
    (by rw [hbytes_sz]; omega) hext_hdr rfl hnm_sz hnm_nul
    (by decide) (by decide) (by decide) (by decide)
    (normPath := "p.txt") rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by dsimp only [Option.bind, Option.getD, pad512]; rw [hbytes_sz]; omega)
  dsimp only [Option.bind, Option.getD, Nat.zero_add, pad512] at hdec
  rw [hext_data] at hdec
  have hmode_val : (((0o644 : UInt32) &&& 0o7777).toNat.toUInt32) = 0o644 := by decide
  rw [hmode_val, show (if (2 == 0) = true then ByteArray.empty else "AB".toUTF8) = "AB".toUTF8 from rfl] at hdec
  have hstep : unpackLoop {} bytes 0 none [] [] 0 =
      unpackLoop {} bytes 1024 none ["p.txt"]
        [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }] 2 := by
    refine unpackLoop_step_continue {} bytes 0 none [] [] 0 1024 none ["p.txt"]
      [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }] 2
      (by rw [hbytes_sz]; omega) ?_ (by omega)
    have hs := unpackStep_nonPax_of_decode_ok {} bytes 0 none [] [] 0
      (by rw [hbytes_sz]; omega) hnz_hdr (show ((0x30 : UInt8) == 0x78) = false from rfl)
      hparse_hdr (by simpa only [List.length_nil] using hdec)
    rw [hs, show (0 : Nat) + 512 + 512 = 1024 from rfl,
      show (0 : Nat) + ("AB".toUTF8).size = 2 from rfl]
  have hdone : unpackLoop {} bytes 1024 none ["p.txt"]
      [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }] 2 =
      .ok [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }] := by
    have hpre_sz : (hdr ++ dirtyData).size = 1024 := by rw [ByteArray.size_append, hhdr_sz, hdirty_sz]
    have hassoc : bytes = (hdr ++ dirtyData) ++ (zeroBlock ++ zeroBlock) := by
      simp only [bytes, twoZeroBlocks]
    have h := unpackLoop_at_twoZeroBlocks {} (hdr ++ dirtyData) ["p.txt"]
      [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }] 2
    rw [hpre_sz, ← hassoc] at h
    exact h
  have hunpack : Impl.unpackWith {} bytes =
      .ok [{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }] := by
    unfold Impl.unpackWith
    rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep, hdone]
  exact ⟨[{ path := "p.txt", kind := .regular, mode := 0o644, data := "AB".toUTF8 }], hunpack,
    tarEquiv_singleton_self _⟩

private theorem allPass_checkUnpackError_impl_bind {api : TarApi}
    (hu : ∀ opts bytes, api.unpackWith opts bytes = Impl.unpackWith opts bytes)
    {opts : UnpackOptions} {bytes : ByteArray} {expectedKind : TarErrorKind}
    (h : ∃ e, Impl.unpackWith opts bytes = .error e ∧ e.kind = expectedKind ∧ (!e.message.isEmpty) = true)
    (k : Unit → AllPassRun Unit) (hkRest : AllPass (k ())) :
    AllPass (checkUnpackError api opts bytes expectedKind >>= k) := by
  rcases h with ⟨e, he, hk, hm⟩
  rw [← hu opts bytes] at he
  exact allPass_checkUnpackError_bind he hk hm hkRest

private theorem allPass_unpackWith_framing_for (api : TarApi)
    (hu : ∀ opts bytes, api.unpackWith opts bytes = Impl.unpackWith opts bytes)
    (hup : ∀ bytes, api.unpack bytes = Impl.unpackWith {} bytes) :
    AllPass (test_tar_unpackWith_framingAndTrailer_validated api) := by
  unfold test_tar_unpackWith_framingAndTrailer_validated
  rw [allPass_have]
  intro jp1 hjp1
  rw [allPass_have]
  intro jp2 hjp2
  refine allPass_checkUnpackError_impl_bind hu
    (unpackWith_alignment_err {} ByteArray.empty (Or.inl rfl)) _ ?_
  rw [hjp2, hjp1]
  refine allPass_checkUnpackError_impl_bind hu
    (unpackWith_alignment_err {} (ByteArray.mk #[0]) (Or.inr (by decide))) _ ?_
  refine allPass_checkUnpackError_impl_bind hu
    (unpackWith_alignment_err {} (twoZeroBlocks ++ ByteArray.mk #[1])
      (Or.inr (by rw [ByteArray.size_append, twoZeroBlocks_size]; decide))) _ ?_
  refine allPass_checkUnpackError_impl_bind hu test4_h4 _ ?_
  refine allPass_checkUnpackError_impl_bind hu test4_h5 _ ?_
  refine allPass_checkUnpackError_impl_bind hu test4_h6 _ ?_
  refine allPass_checkUnpackError_impl_bind hu test4_h7_h8_h9.1 _ ?_
  refine allPass_checkUnpackError_impl_bind hu test4_h7_h8_h9.2.1 _ ?_
  refine allPass_checkUnpackError_impl_bind hu test4_h7_h8_h9.2.2 _ ?_
  refine allPass_checkUnpackError_impl_bind hu test4_h10 _ ?_
  dsimp only
  have ⟨res1, hun1, hte1⟩ := test4_paddedArchive_ok
  have hun1' : api.unpack
      (mkRegularFrame "a.txt" "hi".toUTF8 ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock) =
      .ok res1 := by
    rw [hup _]; exact hun1
  rw [hun1']
  rw [allPass_assert_bind]
  refine ⟨hte1, ?_⟩
  have ⟨res2, hun2, hte2⟩ := test4_dirtyData_ok
  have hun2' : api.unpack
      (mkUstarHeader "p.txt" 0o644 0 0 2 0 0x30 "" "" "" "" ++
        ByteArray.mk (#[0x41, 0x42] ++ Array.replicate 510 0xff) ++ twoZeroBlocks) =
      .ok res2 := by
    rw [hup _]; exact hun2
  rw [hun2']
  exact ⟨hte2, trivial⟩

/-- Prove `test_tar_unpackWith_framingAndTrailer_validated` for `defaultApi`. -/
theorem allPass_unpackWith_framingAndTrailer_validated :
    AllPass (test_tar_unpackWith_framingAndTrailer_validated defaultApi) :=
  allPass_unpackWith_framing_for defaultApi defaultApi_unpackWith_eq
    (fun b => by rw [defaultApi_unpack_eq])

private theorem regFrame_hello_decode_err (opts : UnpackOptions)
    (hfail : opts.maxEntries = 0 ∨ opts.maxTotalBytes = 4) :
    ∃ e, Impl.unpackWith opts (mkRegularFrame "a.txt" "hello".toUTF8 ++ twoZeroBlocks) = .error e ∧
      e.kind = .resourceLimitExceeded ∧ (!e.message.isEmpty) = true := by
  let frame := mkRegularFrame "a.txt" "hello".toUTF8
  let bytes := frame ++ twoZeroBlocks
  have hdat_sz : ("hello".toUTF8).size = 5 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hframe_sz : frame.size = 1024 := by rw [mkRegularFrame_size, hdat_sz]; decide
  have hbytes_sz : bytes.size = 2048 := by rw [ByteArray.size_append, hframe_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hext_hdr : bytes.extract 0 512 =
      mkUstarHeader "a.txt" 0o644 0 0 5 0 0x30 "" "" "" "" := by
    have hassoc : bytes = mkUstarHeader "a.txt" 0o644 0 0 5 0 0x30 "" "" "" "" ++
        (padBlock512 "hello".toUTF8 ++ twoZeroBlocks) := by
      simp only [bytes, frame, mkRegularFrame, hdat_sz, ByteArray.append_assoc]
    have h := extract_append_mid ByteArray.empty
      (mkUstarHeader "a.txt" 0o644 0 0 5 0 0x30 "" "" "" "") (padBlock512 "hello".toUTF8 ++ twoZeroBlocks)
    simp only [ByteArray.size_empty, Nat.zero_add, ByteArray.empty_append, mkUstarHeader_size] at h
    rw [hassoc]
    exact h
  have hnz_hdr : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_hdr
  have hparse_hdr : parseUstarHeader bytes 0 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 5, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_hdr
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz)]
  have herr_step : ∃ e, unpackStep opts bytes 0 none [] [] 0 = .error e ∧
      e.kind = .resourceLimitExceeded ∧ (!e.message.isEmpty) = true := by
    refine unpackStep_regular_precheck_err opts bytes 0 none [] [] 0
      (by rw [hbytes_sz]; omega) hnz_hdr hparse_hdr .resourceLimitExceeded ?_
    rcases hfail with hme | hmb
    · exact Or.inl ⟨by rw [hme]; simp, rfl⟩
    · by_cases hme : ([] : List TarEntry).length + 1 > opts.maxEntries
      · exact Or.inl ⟨hme, rfl⟩
      · exact Or.inr (Or.inl ⟨hme, by dsimp only [Option.bind, Option.getD]; rw [hmb]; omega, rfl⟩)
  rcases herr_step with ⟨e, he, hk, hm⟩
  rw [unpackLoop_step_err opts bytes 0 none [] [] 0 e (by rw [hbytes_sz]; omega) he]
  exact ⟨e, rfl, hk, hm⟩

private theorem pax_size_8g_pad_sz :
    512 + pad512 (encodePaxRecord "size" "8589934592").size = 1024 := by
  have hmin : 4 ≤ (" " ++ "size" ++ "=" ++ "8589934592" ++ "\n").toUTF8.size := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hmax : (" " ++ "size" ++ "=" ++ "8589934592" ++ "\n").toUTF8.size ≤ 100 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have ⟨hpos, hlt⟩ := encodePaxRecord_size_lt_512 hmin hmax
  have hpad : pad512 (encodePaxRecord "size" "8589934592").size = 512 := by
    unfold pad512
    have hq : ((encodePaxRecord "size" "8589934592").size + 511) / 512 = 1 := by omega
    rw [hq]
  rw [hpad]

private theorem test6_paxZeroFile_ok :
    ∃ res, Impl.unpackWith { maxTotalBytes := 0 }
        (mkPaxFrame (encodePaxRecord "path" "a.txt") ++ mkRegularFrame "a.txt" ByteArray.empty ++ twoZeroBlocks) =
        .ok res ∧
      TarEquiv [{ path := "a.txt", kind := .regular }] res := by
  let pax := encodePaxRecord "path" "a.txt"
  let paxF := mkPaxFrame pax
  let regF := mkRegularFrame "a.txt" ByteArray.empty
  let bytes := paxF ++ regF ++ twoZeroBlocks
  have hpax_sz : paxF.size = 1024 := by
    dsimp only [paxF, pax]
    rw [mkPaxFrame_size]
    exact pax_a_txt_pad_sz
  have hreg_sz : regF.size = 512 := by simp only [regF, mkRegularFrame_size, ByteArray.size_empty]; decide
  have hbytes_sz : bytes.size = 2560 := by
    simp only [bytes, ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hstep1 : unpackLoop { maxTotalBytes := 0 } bytes 0 none [] [] 0 =
      unpackLoop { maxTotalBytes := 0 } bytes 1024 (some { path? := some "a.txt" }) [] [] 0 := by
    have hassoc : bytes = ByteArray.empty ++ paxF ++ (regF ++ twoZeroBlocks) := by
      simp only [bytes, ByteArray.empty_append, ByteArray.append_assoc]
    have h := unpackLoop_mkPaxFrame_step { maxTotalBytes := 0 } ByteArray.empty (regF ++ twoZeroBlocks)
      pax [] [] 0 pax_a_txt_sz { path? := some "a.txt" } (parsePax_path_a 0)
    rw [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at h
    have hp : 512 + pad512 pax.size = 1024 := pax_a_txt_pad_sz
    rw [hp] at h
    exact hassoc ▸ h
  have hext_reg : bytes.extract 1024 (1024 + 512) =
      mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" := by
    have hreg_eq : regF = mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" := by
      have hpad_emp : padBlock512 ByteArray.empty = ByteArray.empty := rfl
      simp only [regF, mkRegularFrame, hpad_emp, ByteArray.append_empty, ByteArray.size_empty]
    have hassoc : bytes = paxF ++ mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks := by
      simp only [bytes, hreg_eq]
    rw [hassoc, ← hpax_sz]
    have h := extract_append_mid paxF (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") twoZeroBlocks
    rw [mkUstarHeader_size] at h
    exact h
  have hnz_reg : isZeroRange bytes 1024 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_reg
  have hparse_reg : parseUstarHeader bytes 1024 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 0, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_reg
  have hdec := decodeTarEntry_mkUstarHeader_regular { maxTotalBytes := 0 } bytes
    (mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 1024 (some { path? := some "a.txt" }) [] 0 0
    (normPath := "a.txt") (by rw [hbytes_sz]; omega) hext_reg rfl
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by dsimp only [Option.bind, Option.getD, pad512]; rw [hbytes_sz]; omega)
  dsimp only [Option.bind, Option.getD, pad512] at hdec
  have hmode_val : (((0o644 : UInt32) &&& 0o7777).toNat.toUInt32) = 0o644 := by decide
  rw [hmode_val, ite_eq_left (by decide : ((0 == 0) = true))] at hdec
  have hstep2 : unpackLoop { maxTotalBytes := 0 } bytes 1024 (some { path? := some "a.txt" }) [] [] 0 =
      unpackLoop { maxTotalBytes := 0 } bytes 1536 none ["a.txt"]
        [{ path := "a.txt", kind := .regular, mode := 0o644 }] 0 := by
    refine unpackLoop_step_continue { maxTotalBytes := 0 } bytes 1024
      (some { path? := some "a.txt" }) [] [] 0 1536 none ["a.txt"]
      [{ path := "a.txt", kind := .regular, mode := 0o644 }] 0 (by rw [hbytes_sz]; omega) ?_ (by omega)
    have hs := unpackStep_nonPax_of_decode_ok { maxTotalBytes := 0 } bytes 1024
      (some { path? := some "a.txt" }) [] [] 0 (by rw [hbytes_sz]; omega) hnz_reg
      (show ((0x30 : UInt8) == 0x78) = false from rfl) hparse_reg
      (by simpa only [List.length_nil] using hdec)
    rw [hs, show (1024 : Nat) + 512 + 0 = 1536 from rfl,
      show (0 : Nat) + (ByteArray.empty).size = 0 from rfl]
  have hdone : unpackLoop { maxTotalBytes := 0 } bytes 1536 none ["a.txt"]
      [{ path := "a.txt", kind := .regular, mode := 0o644 }] 0 =
      .ok [{ path := "a.txt", kind := .regular, mode := 0o644 }] := by
    have hpre_sz : (paxF ++ regF).size = 1536 := by rw [ByteArray.size_append, hpax_sz, hreg_sz]
    have hassoc : bytes = (paxF ++ regF) ++ (zeroBlock ++ zeroBlock) := by
      simp only [bytes, twoZeroBlocks]
    rw [hassoc, ← hpre_sz]
    exact unpackLoop_at_twoZeroBlocks { maxTotalBytes := 0 } (paxF ++ regF) ["a.txt"]
      [{ path := "a.txt", kind := .regular, mode := 0o644 }] 0
  have hunpack : Impl.unpackWith { maxTotalBytes := 0 } bytes =
      .ok [{ path := "a.txt", kind := .regular, mode := 0o644 }] := by
    unfold Impl.unpackWith
    rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep1, hstep2, hdone]
  exact ⟨_, hunpack, tarEquiv_singleton_self _⟩

private theorem test6_bigSizePax_err (opts : UnpackOptions) (expectedKind : TarErrorKind)
    (hmax_e : 1 ≤ opts.maxEntries)
    (hopts : (opts.maxTotalBytes = 1024 ∧ expectedKind = .resourceLimitExceeded) ∨
             (opts.maxTotalBytes = 10737418240 ∧ expectedKind = .truncatedArchive)) :
    ∃ e, Impl.unpackWith opts
        (mkPaxFrame (encodePaxRecord "size" "8589934592") ++ mkRegularFrame "big.bin" ByteArray.empty ++ twoZeroBlocks) =
        .error e ∧ e.kind = expectedKind ∧ (!e.message.isEmpty) = true := by
  let pax := encodePaxRecord "size" "8589934592"
  let paxF := mkPaxFrame pax
  let regF := mkRegularFrame "big.bin" ByteArray.empty
  let bytes := paxF ++ regF ++ twoZeroBlocks
  have hpax_le : pax.size ≤ maxPaxHeaderBytes := by
    have hmin : 4 ≤ (" " ++ "size" ++ "=" ++ "8589934592" ++ "\n").toUTF8.size := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hmax : (" " ++ "size" ++ "=" ++ "8589934592" ++ "\n").toUTF8.size ≤ 100 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hp : 0 < pax.size ∧ pax.size < 512 := encodePaxRecord_size_lt_512 hmin hmax
    have : maxPaxHeaderBytes = 1048576 := rfl
    omega
  have hpax_sz : paxF.size = 1024 := by
    dsimp only [paxF, pax]
    rw [mkPaxFrame_size]
    exact pax_size_8g_pad_sz
  have hreg_sz : regF.size = 512 := by simp only [regF, mkRegularFrame_size, ByteArray.size_empty]; decide
  have hbytes_sz : bytes.size = 2560 := by
    simp only [bytes, ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hstep1 : unpackLoop opts bytes 0 none [] [] 0 =
      unpackLoop opts bytes 1024 (some { size? := some 8589934592 }) [] [] 0 := by
    have hassoc : bytes = ByteArray.empty ++ paxF ++ (regF ++ twoZeroBlocks) := by
      simp only [bytes, ByteArray.empty_append, ByteArray.append_assoc]
    have h := unpackLoop_mkPaxFrame_step opts ByteArray.empty (regF ++ twoZeroBlocks)
      pax [] [] 0 hpax_le { size? := some 8589934592 } (parsePax_size_8g 0)
    rw [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at h
    have hp : 512 + pad512 pax.size = 1024 := pax_size_8g_pad_sz
    rw [hp] at h
    exact hassoc ▸ h
  have hext_reg : bytes.extract 1024 (1024 + 512) =
      mkUstarHeader "big.bin" 0o644 0 0 0 0 0x30 "" "" "" "" := by
    have hreg_eq : regF = mkUstarHeader "big.bin" 0o644 0 0 0 0 0x30 "" "" "" "" := by
      have hpad_emp : padBlock512 ByteArray.empty = ByteArray.empty := rfl
      simp only [regF, mkRegularFrame, hpad_emp, ByteArray.append_empty, ByteArray.size_empty]
    have hassoc : bytes = paxF ++ mkUstarHeader "big.bin" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks := by
      simp only [bytes, hreg_eq]
    rw [hassoc, ← hpax_sz]
    have h := extract_append_mid paxF (mkUstarHeader "big.bin" 0o644 0 0 0 0 0x30 "" "" "" "") twoZeroBlocks
    rw [mkUstarHeader_size] at h
    exact h
  have hnz_reg : isZeroRange bytes 1024 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_reg
  have hparse_reg : parseUstarHeader bytes 1024 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 0, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_reg
  have herr2 : ∃ e, unpackStep opts bytes 1024 (some { size? := some 8589934592 }) [] [] 0 = .error e ∧
      e.kind = expectedKind ∧ (!e.message.isEmpty) = true := by
    refine unpackStep_regular_precheck_err opts bytes 1024 (some { size? := some 8589934592 }) [] [] 0
      (by rw [hbytes_sz]; omega) hnz_reg hparse_reg expectedKind ?_
    have hnot_maxe : ¬(([] : List TarEntry).length + 1 > opts.maxEntries) := by simp; omega
    dsimp only [Option.bind, Option.getD]
    rcases hopts with ⟨hmb, hk⟩ | ⟨hmb, hk⟩
    · exact Or.inr (Or.inl ⟨hnot_maxe, by omega, hk⟩)
    · have htrunc : 1024 + 512 + pad512 8589934592 > bytes.size := by
        have hle := le_pad512 8589934592
        rw [hbytes_sz]; omega
      exact Or.inr (Or.inr ⟨hnot_maxe, by omega, htrunc, hk⟩)
  rcases herr2 with ⟨e, he, hk, hm⟩
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep1,
    unpackLoop_step_err opts bytes 1024 _ _ _ _ e (by rw [hbytes_sz]; omega) he]
  exact ⟨e, rfl, hk, hm⟩

private theorem test6_hugePax_err :
    let hugePaxHdr := mkUstarHeader "././@PaxHeader" 0o644 0 0 (maxPaxHeaderBytes + 1) 0 0x78 "" "" "" ""
    ∃ e, Impl.unpackWith {} (hugePaxHdr ++ twoZeroBlocks) = .error e ∧
      e.kind = .resourceLimitExceeded ∧ (!e.message.isEmpty) = true := by
  intro hugePaxHdr
  let bytes := hugePaxHdr ++ twoZeroBlocks
  have hhdr_sz : hugePaxHdr.size = 512 := mkUstarHeader_size ..
  have hbytes_sz : bytes.size = 1536 := by rw [ByteArray.size_append, hhdr_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hext_hdr : bytes.extract 0 512 = hugePaxHdr := by
    have h := extract_append_mid ByteArray.empty hugePaxHdr twoZeroBlocks
    simp only [ByteArray.size_empty, Nat.zero_add, ByteArray.empty_append, hhdr_sz] at h
    exact h
  have hnz_hdr : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_hdr
  have hsz_lt : maxPaxHeaderBytes + 1 < ustarOctal11Limit := by
    have : maxPaxHeaderBytes = 1048576 := rfl
    have : ustarOctal11Limit = 8 ^ 11 := rfl
    omega
  have hparse_hdr : parseUstarHeader bytes 0 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := maxPaxHeaderBytes + 1, mtime := 0, typeflag := 0x78 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) hsz_lt (by decide)
      (by rw [hbytes_sz]; omega) hext_hdr
  have hnotge : ¬(0 ≥ bytes.size) := by rw [hbytes_sz]; omega
  have hnotgt512 : ¬(0 + 512 > bytes.size) := by rw [hbytes_sz]; omega
  have herr : unpackStep {} bytes 0 none [] [] 0 =
      .error { kind := .resourceLimitExceeded, message := "PAX header exceeds maxPaxHeaderBytes", offset := some 0 } := by
    unfold unpackStep
    simp only [hnotge, ↓reduceIte, hnz_hdr, Bool.false_eq_true, hnotgt512, hparse_hdr,
      beq_self_eq_true, Option.isSome_none, show maxPaxHeaderBytes + 1 > maxPaxHeaderBytes by omega]
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz),
    unpackLoop_step_err {} bytes 0 none [] [] 0 _ (by rw [hbytes_sz]; omega) herr]
  exact ⟨_, rfl, rfl, by decide⟩

/-- Prove `test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced` for `defaultApi`. -/
theorem allPass_unpackWith_resourceLimitsAndLargePaxSize_enforced :
    AllPass (test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced defaultApi) := by
  unfold test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced
  rw [allPass_have]
  intro regFrame hrf
  rw [hrf]
  refine allPass_checkUnpackError_exists_bind
    (regFrame_hello_decode_err { maxEntries := 0 } (Or.inl rfl)) _ ?_
  refine allPass_checkUnpackError_exists_bind
    (regFrame_hello_decode_err { maxTotalBytes := 4 } (Or.inr rfl)) _ ?_
  rw [allPass_have]
  intro jp_ok hjp_ok
  have ⟨res, hun, hte⟩ := test6_paxZeroFile_ok
  have hun' : defaultApi.unpackWith { maxTotalBytes := 0 }
      (mkPaxFrame (encodePaxRecord "path" "a.txt") ++ mkRegularFrame "a.txt" ByteArray.empty ++ twoZeroBlocks) = .ok res := by
    rw [defaultApi_unpackWith_eq]; exact hun
  rw [hun']
  rw [hjp_ok]
  dsimp (config := { zeta := false }) only
  rw [allPass_assert_bind]
  refine ⟨hte, ?_⟩
  rw [allPass_have]
  intro bigSizePax hbsp
  rw [hbsp]
  refine allPass_checkUnpackError_exists_bind
    (test6_bigSizePax_err { maxTotalBytes := 1024 } .resourceLimitExceeded (by decide)
      (Or.inl ⟨rfl, rfl⟩)) _ ?_
  refine allPass_checkUnpackError_exists_bind
    (test6_bigSizePax_err { maxTotalBytes := 10737418240 } .truncatedArchive (by decide)
      (Or.inr ⟨rfl, rfl⟩)) _ ?_
  rw [allPass_have]
  intro hugePaxHdr hhp
  rw [hhp]
  exact allPass_checkUnpackError_of_err {} _ _ test6_hugePax_err

private theorem unpackWith_single_raw_path_err
    {path linkname : String} {mode : UInt32} {typeflag : UInt8}
    (hnm_sz : path.toUTF8.size ≤ 100) (hnm_nul : !hasNulString path = true)
    (hlk_sz : linkname.toUTF8.size ≤ 100) (hlk_nul : !hasNulString linkname = true)
    (htf_ok : (typeflag == 0x30 || typeflag == 0x00 || typeflag == 0x35 || typeflag == 0x32) = true)
    (htf_not78 : (typeflag == 0x78) = false)
    (_hkind_ok : let kind := if typeflag == 0x35 then EntryKind.directory
        else if typeflag == 0x32 then EntryKind.symlink else EntryKind.regular
      (kind != EntryKind.regular && 0 != 0) = false)
    {expectedKind : TarErrorKind} {e : TarError}
    (hpath_or_sym_err :
      let kind := if typeflag == 0x35 then EntryKind.directory
        else if typeflag == 0x32 then EntryKind.symlink else EntryKind.regular
      (do
        let normPath ← validateEntryPath false false kind path
        if kind == EntryKind.symlink then validateSymlinkTarget false false normPath linkname else pure ()) = .error e)
    (hk : e.kind = expectedKind) (hm : (!e.message.isEmpty) = true) :
    ∃ err, Impl.unpackWith {} (mkUstarHeader path mode 0 0 0 0 typeflag linkname "" "" "" ++ twoZeroBlocks) =
      .error err ∧ err.kind = expectedKind ∧ (!err.message.isEmpty) = true := by
  let hdr := mkUstarHeader path mode 0 0 0 0 typeflag linkname "" "" ""
  let bytes := hdr ++ twoZeroBlocks
  have hhdr_sz : hdr.size = 512 := mkUstarHeader_size ..
  have hbytes_sz : bytes.size = 1536 := by rw [ByteArray.size_append, hhdr_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hext_hdr : bytes.extract 0 512 = hdr := by
    have h := extract_append_mid ByteArray.empty hdr twoZeroBlocks
    simp only [ByteArray.size_empty, Nat.zero_add, ByteArray.empty_append, hhdr_sz] at h
    exact h
  have hnz_hdr : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_hdr
  have hparse_hdr : parseUstarHeader bytes 0 =
      .ok { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 0, mtime := 0, typeflag := typeflag } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_hdr
  have hemp_sz : ("" : String).toUTF8.size = 0 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hemp_nul : !hasNulString "" = true := by decide
  have hstrs := mkUstarHeader_extract_strings hext_hdr
  have hdec_nm : decodeCStringUtf8 bytes 0 100 0 "name" = .ok path := by
    rw [show (100 : Nat) = 0 + 100 from rfl]
    exact decodeCStringUtf8_padRightBytes hnm_nul hnm_sz (by rw [hbytes_sz]; omega) hstrs.1
  have hdec_lk : decodeCStringUtf8 bytes 157 257 0 "linkname" = .ok linkname := by
    rw [show (257 : Nat) = 157 + 100 from rfl]
    exact decodeCStringUtf8_padRightBytes hlk_nul hlk_sz (by rw [hbytes_sz]; omega) hstrs.2.1
  have hdec_u : decodeCStringUtf8 bytes 265 297 0 "uname" = .ok "" := by
    rw [show (297 : Nat) = 265 + 32 from rfl]
    exact decodeCStringUtf8_padRightBytes hemp_nul (by omega) (by rw [hbytes_sz]; omega) hstrs.2.2.1
  have hdec_g : decodeCStringUtf8 bytes 297 329 0 "gname" = .ok "" := by
    rw [show (329 : Nat) = 297 + 32 from rfl]
    exact decodeCStringUtf8_padRightBytes hemp_nul (by omega) (by rw [hbytes_sz]; omega) hstrs.2.2.2.1
  have hdec_p : decodeCStringUtf8 bytes 345 500 0 "prefix" = .ok "" := by
    rw [show (500 : Nat) = 345 + 155 from rfl]
    exact decodeCStringUtf8_padRightBytes hemp_nul (by omega) (by rw [hbytes_sz]; omega) hstrs.2.2.2.2
  let kind := if typeflag == 0x35 then EntryKind.directory
    else if typeflag == 0x32 then EntryKind.symlink else EntryKind.regular
  have herr_dec : decodeTarEntry {} bytes 0
      { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := typeflag }
      none [] 0 0 = .error { e with offset := some 0 } := by
    rw [decodeTarEntry.eq_1]
    have hnot_maxe : ¬(0 + 1 > ({} : UnpackOptions).maxEntries) := by decide
    have hnot_maxb : ¬(0 + 0 > ({} : UnpackOptions).maxTotalBytes) := by decide
    have hpad0 : pad512 0 = 0 := rfl
    have hnot_trunc : ¬(0 + 512 + 0 > bytes.size) := by rw [hbytes_sz]; omega
    have htf1 : (typeflag == 0x30 || typeflag == 0x00 || typeflag == 0x35 || typeflag == 0x32) = true := htf_ok
    have hpa : (if ("" : String).isEmpty = true then path else "" ++ "/" ++ path) = path := rfl
    dsimp only
    rcases h30 : (typeflag == 0x30 || typeflag == 0x00) with _ | _
    · rw [ite_eq_right Bool.false_ne_true]
      rcases h35 : (typeflag == 0x35) with _ | _
      · rw [ite_eq_right Bool.false_ne_true]
        have h32 : (typeflag == 0x32) = true := by
          simp only [h30, h35, Bool.false_or] at htf1; exact htf1
        rw [ite_eq_left h32]
        dsimp only
        simp only [Nat.zero_add, Option.getD_none, hpad0]
        rw [ite_eq_right (by simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true]),
          ite_eq_right hnot_maxe, ite_eq_right hnot_maxb, ite_eq_right hnot_trunc]
        rw [hdec_nm, hdec_lk, hdec_u, hdec_g, hdec_p]
        dsimp only [Bind.bind, Except.bind]
        rw [hpa]
        have hk_def : (if (typeflag == 0x35 : Bool) then EntryKind.directory
            else if (typeflag == 0x32 : Bool) then EntryKind.symlink else EntryKind.regular) = .symlink := by
          simp [h35, h32]
        rw [hk_def] at hpath_or_sym_err
        cases hve : validateEntryPath false false .symlink path with
        | error err =>
          simp only [hve, Bind.bind, Except.bind] at hpath_or_sym_err
          cases hpath_or_sym_err; rfl
        | ok np =>
          simp only [hve, Bind.bind, Except.bind, show ((EntryKind.symlink == EntryKind.symlink) = true) from rfl,
            ↓reduceIte] at hpath_or_sym_err
          dsimp only
          rw [hpath_or_sym_err]
      · rw [ite_eq_left rfl]
        dsimp only
        simp only [Nat.zero_add, Option.getD_none, hpad0]
        rw [ite_eq_right (by simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true]),
          ite_eq_right hnot_maxe, ite_eq_right hnot_maxb, ite_eq_right hnot_trunc]
        rw [hdec_nm, hdec_u, hdec_g, hdec_p]
        dsimp only [Bind.bind, Except.bind]
        rw [hpa]
        have hk_def : (if (typeflag == 0x35 : Bool) then EntryKind.directory
            else if (typeflag == 0x32 : Bool) then EntryKind.symlink else EntryKind.regular) = .directory := by
          simp [h35]
        rw [hk_def] at hpath_or_sym_err
        cases hve : validateEntryPath false false .directory path with
        | error err =>
          simp only [hve, Bind.bind, Except.bind] at hpath_or_sym_err
          cases hpath_or_sym_err; rfl
        | ok np =>
          simp only [hve, Bind.bind, Except.bind, show ((EntryKind.directory == EntryKind.symlink) = false) from rfl,
            Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure] at hpath_or_sym_err
          cases hpath_or_sym_err
    · rw [ite_eq_left rfl]
      dsimp only
      simp only [Nat.zero_add, Option.getD_none, hpad0]
      rw [ite_eq_right (by simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true]),
        ite_eq_right hnot_maxe, ite_eq_right hnot_maxb, ite_eq_right hnot_trunc]
      rw [hdec_nm, hdec_u, hdec_g, hdec_p]
      dsimp only [Bind.bind, Except.bind]
      rw [hpa]
      have hk_def : (if (typeflag == 0x35 : Bool) then EntryKind.directory
          else if (typeflag == 0x32 : Bool) then EntryKind.symlink else EntryKind.regular) = .regular := by
        cases h35 : typeflag == 0x35
        · cases h32 : typeflag == 0x32
          · simp
          · exfalso; have : typeflag = 0x32 := eq_of_beq h32; subst this; cases h30
        · exfalso; have : typeflag = 0x35 := eq_of_beq h35; subst this; cases h30
      rw [hk_def] at hpath_or_sym_err
      cases hve : validateEntryPath false false .regular path with
      | error err =>
        simp only [hve, Bind.bind, Except.bind] at hpath_or_sym_err
        cases hpath_or_sym_err; rfl
      | ok np =>
        simp only [hve, Bind.bind, Except.bind, show ((EntryKind.regular == EntryKind.symlink) = false) from rfl,
          Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure] at hpath_or_sym_err
        cases hpath_or_sym_err
  have herr_step : unpackStep {} bytes 0 none [] [] 0 = .error { e with offset := some 0 } :=
    unpackStep_nonPax_of_decode_err {} bytes 0 none [] [] 0 (by rw [hbytes_sz]; omega)
      hnz_hdr htf_not78 hparse_hdr (by simpa only [List.length_nil] using herr_dec)
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz),
    unpackLoop_step_err {} bytes 0 none [] [] 0 _ (by rw [hbytes_sz]; omega) herr_step]
  exact ⟨_, rfl, hk, hm⟩

private theorem test7_dup_err :
    let dupA := mkUstarHeader "sub/" 0o755 0 0 0 0 0x35 "" "" "" ""
    let dupB := mkUstarHeader "sub" 0o644 0 0 0 0 0x30 "" "" "" ""
    ∃ e, Impl.unpackWith {} (dupA ++ dupB ++ twoZeroBlocks) = .error e ∧
      e.kind = .duplicatePath ∧ (!e.message.isEmpty) = true := by
  intro dupA dupB
  let bytes := dupA ++ dupB ++ twoZeroBlocks
  have ha_sz : dupA.size = 512 := mkUstarHeader_size ..
  have hb_sz : dupB.size = 512 := mkUstarHeader_size ..
  have hbytes_sz : bytes.size = 2048 := by rw [ByteArray.size_append, ByteArray.size_append, ha_sz, hb_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hext_a : bytes.extract 0 512 = dupA := by
    have h := extract_append_mid ByteArray.empty dupA (dupB ++ twoZeroBlocks)
    simp only [ByteArray.size_empty, Nat.zero_add, ByteArray.empty_append, ha_sz] at h
    simpa only [bytes, ByteArray.append_assoc] using h
  have hnz_a : isZeroRange bytes 0 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_a
  have hparse_a : parseUstarHeader bytes 0 =
      .ok { mode := ((0o755 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 0, mtime := 0, typeflag := 0x35 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_a
  have hstrs_a := mkUstarHeader_zero_decode_strings (by rw [hbytes_sz]; omega) hext_a
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide : !hasNulString "sub/" = true)
  let entryA : TarEntry :=
    { path := "sub", kind := .directory, mode := ((0o755 : UInt32) &&& 0o7777).toNat.toUInt32,
      uid := 0, gid := 0, mtime := 0, uname := "", gname := "", data := ByteArray.empty, linkTarget := "" }
  have hdec_a : decodeTarEntry {} bytes 0
      { mode := ((0o755 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x35 }
      none [] 0 0 = .ok (entryA, 0) := by
    rw [decodeTarEntry.eq_1]
    rw [ite_eq_right (by decide), ite_eq_left (by decide)]
    dsimp only
    simp only [Nat.zero_add, Option.getD_none, show pad512 0 = 0 from rfl]
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by rw [hbytes_sz]; omega)]
    rw [hstrs_a.1, hstrs_a.2.2.1, hstrs_a.2.2.2.1, hstrs_a.2.2.2.2]
    dsimp only [Bind.bind, Except.bind]
    rw [ite_eq_left (by decide : ("" : String).isEmpty = true)]
    have hvalA : validateEntryPath false false .directory "sub/" = .ok "sub" := rfl
    rw [hvalA]
    dsimp only [Bind.bind, Except.bind]
    rw [ite_eq_right (by decide)]
    rfl
  have hstep1 : unpackLoop {} bytes 0 none [] [] 0 =
      unpackLoop {} bytes 512 none ["sub"] [entryA] 0 := by
    refine unpackLoop_step_continue {} bytes 0 none [] [] 0 512 none ["sub"] [entryA] 0
      (by rw [hbytes_sz]; omega) ?_ (by omega)
    have hs := unpackStep_nonPax_of_decode_ok {} bytes 0 none [] [] 0
      (by rw [hbytes_sz]; omega) hnz_a (show ((0x35 : UInt8) == 0x78) = false from rfl)
      hparse_a (by simpa only [List.length_nil] using hdec_a)
    rw [hs, show (0 : Nat) + 512 + 0 = 512 from rfl, show (0 : Nat) + entryA.data.size = 0 from rfl]
  have hext_b : bytes.extract 512 (512 + 512) = dupB := by
    have h := extract_append_mid dupA dupB twoZeroBlocks
    rw [ha_sz, hb_sz] at h
    exact h
  have hnz_b : isZeroRange bytes 512 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_b
  have hparse_b : parseUstarHeader bytes 512 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 0, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_b
  have hstrs_b := mkUstarHeader_zero_decode_strings (by rw [hbytes_sz]; omega) hext_b
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide : !hasNulString "sub" = true)
  have hdec_b : decodeTarEntry {} bytes 512
      { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x30 }
      none ["sub"] 1 0 =
      .error { kind := .duplicatePath, message := "duplicate tar entry path: sub",
               entryPath := some "sub", offset := some 512 } := by
    rw [decodeTarEntry.eq_1]
    rw [ite_eq_left (by decide)]
    dsimp only
    simp only [Nat.add_zero, Option.getD_none, show pad512 0 = 0 from rfl]
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by rw [hbytes_sz]; omega)]
    rw [hstrs_b.1, hstrs_b.2.2.1, hstrs_b.2.2.2.1, hstrs_b.2.2.2.2]
    dsimp only [Bind.bind, Except.bind]
    rw [ite_eq_left (by decide : ("" : String).isEmpty = true)]
    have hvalB : validateEntryPath false false .regular "sub" = .ok "sub" := rfl
    rw [hvalB]
    dsimp only [Bind.bind, Except.bind]
    rw [ite_eq_left (by decide)]
    rfl
  have herr2 : unpackStep {} bytes 512 none ["sub"] [entryA] 0 =
      .error { kind := .duplicatePath, message := "duplicate tar entry path: sub",
               entryPath := some "sub", offset := some 512 } :=
    unpackStep_nonPax_of_decode_err {} bytes 512 none ["sub"] [entryA] 0
      (by rw [hbytes_sz]; omega) hnz_b (show ((0x30 : UInt8) == 0x78) = false from rfl)
      hparse_b (by simpa only [show [entryA].length = 1 from rfl] using hdec_b)
  unfold Impl.unpackWith
  rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep1,
    unpackLoop_step_err {} bytes 512 none ["sub"] [entryA] 0 _ (by rw [hbytes_sz]; omega) herr2]
  exact ⟨_, rfl, rfl, by decide⟩

private theorem test7_safe_ok :
    ∃ res, Impl.unpackWith {}
        (mkPaxFrame (encodePaxRecord "path" "safe.txt") ++ mkRegularFrame "safe.txt" ByteArray.empty ++ twoZeroBlocks) =
        .ok res ∧
      TarEquiv [{ path := "safe.txt", kind := .regular }] res := by
  let pax := encodePaxRecord "path" "safe.txt"
  let paxF := mkPaxFrame pax
  let regF := mkRegularFrame "safe.txt" ByteArray.empty
  let bytes := paxF ++ regF ++ twoZeroBlocks
  have hpax_le : pax.size ≤ maxPaxHeaderBytes := by
    have hmin : 4 ≤ (" " ++ "path" ++ "=" ++ "safe.txt" ++ "\n").toUTF8.size := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hmax : (" " ++ "path" ++ "=" ++ "safe.txt" ++ "\n").toUTF8.size ≤ 100 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hp : 0 < pax.size ∧ pax.size < 512 := encodePaxRecord_size_lt_512 hmin hmax
    have : maxPaxHeaderBytes = 1048576 := rfl
    omega
  have hpax_pad : 512 + pad512 pax.size = 1024 := by
    have hmin : 4 ≤ (" " ++ "path" ++ "=" ++ "safe.txt" ++ "\n").toUTF8.size := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hmax : (" " ++ "path" ++ "=" ++ "safe.txt" ++ "\n").toUTF8.size ≤ 100 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hp : 0 < pax.size ∧ pax.size < 512 := encodePaxRecord_size_lt_512 hmin hmax
    have hpad : pad512 pax.size = 512 := by
      unfold pad512
      have hq : (pax.size + 511) / 512 = 1 := by omega
      rw [hq]
    rw [hpad]
  have hpax_sz : paxF.size = 1024 := by
    dsimp only [paxF, pax]
    rw [mkPaxFrame_size]
    exact hpax_pad
  have hreg_sz : regF.size = 512 := by simp only [regF, mkRegularFrame_size, ByteArray.size_empty]; decide
  have hbytes_sz : bytes.size = 2560 := by
    simp only [bytes, ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by rw [hbytes_sz]; rfl
  have hstep1 : unpackLoop {} bytes 0 none [] [] 0 =
      unpackLoop {} bytes 1024 (some { path? := some "safe.txt" }) [] [] 0 := by
    have hassoc : bytes = ByteArray.empty ++ paxF ++ (regF ++ twoZeroBlocks) := by
      simp only [bytes, ByteArray.empty_append, ByteArray.append_assoc]
    have h := unpackLoop_mkPaxFrame_step {} ByteArray.empty (regF ++ twoZeroBlocks)
      pax [] [] 0 hpax_le { path? := some "safe.txt" } (parsePax_path_safe 0)
    rw [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at h
    rw [hpax_pad] at h
    exact hassoc ▸ h
  have hext_reg : bytes.extract 1024 (1024 + 512) =
      mkUstarHeader "safe.txt" 0o644 0 0 0 0 0x30 "" "" "" "" := by
    have hreg_eq : regF = mkUstarHeader "safe.txt" 0o644 0 0 0 0 0x30 "" "" "" "" := by
      have hpad_emp : padBlock512 ByteArray.empty = ByteArray.empty := rfl
      simp only [regF, mkRegularFrame, hpad_emp, ByteArray.append_empty, ByteArray.size_empty]
    have hassoc : bytes = paxF ++ mkUstarHeader "safe.txt" 0o644 0 0 0 0 0x30 "" "" "" "" ++ twoZeroBlocks := by
      simp only [bytes, hreg_eq]
    rw [hassoc, ← hpax_sz]
    have h := extract_append_mid paxF (mkUstarHeader "safe.txt" 0o644 0 0 0 0 0x30 "" "" "" "") twoZeroBlocks
    rw [mkUstarHeader_size] at h
    exact h
  have hnz_reg : isZeroRange bytes 1024 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hbytes_sz]; omega) hext_reg
  have hparse_reg : parseUstarHeader bytes 1024 =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0,
            size := 0, mtime := 0, typeflag := 0x30 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by decide) (by decide)
      (by rw [hbytes_sz]; omega) hext_reg
  have hdec := decodeTarEntry_mkUstarHeader_regular {} bytes
    (mkUstarHeader "safe.txt" 0o644 0 0 0 0 0x30 "" "" "" "") 1024 (some { path? := some "safe.txt" }) [] 0 0
    (normPath := "safe.txt") (by rw [hbytes_sz]; omega) hext_reg rfl
    (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by dsimp only [Option.bind, Option.getD, pad512]; rw [hbytes_sz]; omega)
  dsimp only [Option.bind, Option.getD, pad512] at hdec
  have hmode_val : (((0o644 : UInt32) &&& 0o7777).toNat.toUInt32) = 0o644 := by decide
  rw [hmode_val, ite_eq_left (by decide : ((0 == 0) = true))] at hdec
  have hstep2 : unpackLoop {} bytes 1024 (some { path? := some "safe.txt" }) [] [] 0 =
      unpackLoop {} bytes 1536 none ["safe.txt"]
        [{ path := "safe.txt", kind := .regular, mode := 0o644 }] 0 := by
    refine unpackLoop_step_continue {} bytes 1024
      (some { path? := some "safe.txt" }) [] [] 0 1536 none ["safe.txt"]
      [{ path := "safe.txt", kind := .regular, mode := 0o644 }] 0 (by rw [hbytes_sz]; omega) ?_ (by omega)
    have hs := unpackStep_nonPax_of_decode_ok {} bytes 1024
      (some { path? := some "safe.txt" }) [] [] 0 (by rw [hbytes_sz]; omega) hnz_reg
      (show ((0x30 : UInt8) == 0x78) = false from rfl) hparse_reg
      (by simpa only [List.length_nil] using hdec)
    rw [hs, show (1024 : Nat) + 512 + 0 = 1536 from rfl,
      show (0 : Nat) + (ByteArray.empty).size = 0 from rfl]
  have hdone : unpackLoop {} bytes 1536 none ["safe.txt"]
      [{ path := "safe.txt", kind := .regular, mode := 0o644 }] 0 =
      .ok [{ path := "safe.txt", kind := .regular, mode := 0o644 }] := by
    have hpre_sz : (paxF ++ regF).size = 1536 := by rw [ByteArray.size_append, hpax_sz, hreg_sz]
    have hassoc : bytes = (paxF ++ regF) ++ (zeroBlock ++ zeroBlock) := by
      simp only [bytes, twoZeroBlocks]
    rw [hassoc, ← hpre_sz]
    exact unpackLoop_at_twoZeroBlocks {} (paxF ++ regF) ["safe.txt"]
      [{ path := "safe.txt", kind := .regular, mode := 0o644 }] 0
  have hunpack : Impl.unpackWith {} bytes =
      .ok [{ path := "safe.txt", kind := .regular, mode := 0o644 }] := by
    unfold Impl.unpackWith
    rw [ite_eq_right (fun hc => by rw [hc] at hnz; cases hnz), hstep1, hstep2, hdone]
  exact ⟨_, hunpack, tarEquiv_singleton_self _⟩

/-- Prove `test_tar_unpackWith_securityOnWire_enforced` for `defaultApi`. -/
theorem allPass_unpackWith_securityOnWire_enforced :
    AllPass (test_tar_unpackWith_securityOnWire_enforced defaultApi) := by
  unfold test_tar_unpackWith_securityOnWire_enforced
  rw [allPass_have]
  intro travHdr htrav
  rw [htrav]
  refine allPass_checkUnpackError_exists_bind
    (unpackWith_single_raw_path_err (path := "../evil") (linkname := "") (mode := 0o644) (typeflag := 0x30)
      (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by decide)
      (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by decide) rfl rfl rfl rfl rfl (by decide)) _ ?_
  rw [allPass_have]
  intro absHdr habs
  rw [habs]
  refine allPass_checkUnpackError_exists_bind
    (unpackWith_single_raw_path_err (path := "/etc/passwd") (linkname := "") (mode := 0o644) (typeflag := 0x30)
      (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by decide)
      (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by decide) rfl rfl rfl rfl rfl (by decide)) _ ?_
  rw [allPass_have]
  intro escSym hesc
  rw [hesc]
  refine allPass_checkUnpackError_exists_bind
    (unpackWith_single_raw_path_err (path := "escape") (linkname := "../etc/passwd") (mode := 0o777) (typeflag := 0x32)
      (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by decide)
      (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
      (by decide)
      rfl rfl rfl rfl rfl (by decide)) _ ?_
  rw [allPass_have]
  intro dupA hda
  rw [allPass_have]
  intro dupB hdb
  refine allPass_checkUnpackError_exists_bind test7_dup_err _ ?_
  rw [hdb, hda, allPass_have]
  intro jp_ok hjp_ok
  have ⟨res, hun, hte⟩ := test7_safe_ok
  have hun' : defaultApi.unpack
      (mkPaxFrame (encodePaxRecord "path" "safe.txt") ++ mkRegularFrame "safe.txt" ByteArray.empty ++ twoZeroBlocks) =
      .ok res := by
    rw [defaultApi_unpack_eq]; exact hun
  rw [hun', hjp_ok]
  dsimp only
  exact ⟨hte, trivial⟩

end LeanSwe.Tar.Proofs
