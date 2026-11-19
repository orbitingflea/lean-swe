import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout

namespace LeanSwe.Tar.Proofs

open Core Core.NondetTest LeanSwe.Tar LeanSwe.Tar.Model LeanSwe.Tar.Impl

/-- Discharge a mid-sequence `checkUnpackError` assertion on `api`. -/
theorem allPass_err_for {api : TarApi} (hu : api.unpackWith = Impl.unpackWith)
    {opts : UnpackOptions} {bytes : ByteArray} {kind : TarErrorKind} {e : TarError}
    (h : Impl.unpackWith opts bytes = .error e) (hk : e.kind = kind) (hm : (!e.message.isEmpty) = true)
    {k : Unit → AllPassRun Unit} (hrest : AllPass (k ())) : AllPass (Bind.bind (checkUnpackError api opts bytes kind) k) :=
  allPass_checkUnpackError_bind (by rw [hu]; exact h) hk hm hrest
/-- Discharge a mid-sequence `match f bytes` `.ok` assertion in a `do` block. -/
theorem allPass_ok_bind_fn {f : ByteArray → Except TarError (List TarEntry)} {opts : UnpackOptions}
    (hf : f = Impl.unpackWith opts) {bytes : ByteArray} {expected decoded : List TarEntry}
    (h : Impl.unpackWith opts bytes = .ok decoded) (heq : TarEquiv expected decoded)
    {kErr : TarError → AllPassRun Unit} {k : Unit → AllPassRun Unit} (hrest : AllPass (k ())) :
    AllPass (match f bytes with | .error e => kErr e | .ok r => Bind.bind (NondetTest.assert (TarEquiv expected r)) k) := by
  rw [hf, h]; exact ⟨heq, hrest⟩
/-- Discharge a terminal `match Impl.unpackWith ...` `.ok` assertion. -/
theorem allPass_ok_last_impl {opts : UnpackOptions} {bytes : ByteArray} {expected decoded : List TarEntry}
    (h : Impl.unpackWith opts bytes = .ok decoded) (heq : TarEquiv expected decoded) {kErr : TarError → AllPassRun Unit} :
    AllPass (match Impl.unpackWith opts bytes with | .error e => kErr e | .ok r => NondetTest.assert (TarEquiv expected r)) := by
  rw [h]; exact ⟨heq, trivial⟩
/-- Reflexivity of `TarEquiv` on singleton lists. -/
theorem tarEquiv_singleton_self (e : TarEntry) : TarEquiv [e] [e] := by
  refine ⟨?_, trivial⟩; unfold entryEquivBool
  have hk : (e.kind == e.kind) = true := by cases e.kind <;> rfl
  simp only [beq_self_eq_true, hk, Bool.and_self]
/-- Unfold `Impl.unpackWith` to `unpackLoop` when `bytes` is non-empty and 512-byte aligned. -/
theorem unpackWith_eq_unpackLoop {opts : UnpackOptions} {bytes : ByteArray} (hpos : 0 < bytes.size) (hmod : bytes.size % 512 = 0) :
    Impl.unpackWith opts bytes = unpackLoop opts bytes 0 none [] [] 0 := by
  unfold Impl.unpackWith
  have hne0 : (bytes.size == 0) = false := beq_false_of_ne (by omega)
  have hrem : (bytes.size % 512 != 0) = false := Bool.eq_false_iff.mpr fun h => (bne_iff_ne.mp h) hmod
  simp only [hne0, hrem, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

private theorem unpackWith_alignment_err (opts : UnpackOptions) (bytes : ByteArray) (h : bytes.size = 0 ∨ bytes.size % 512 ≠ 0) :
    Impl.unpackWith opts bytes = .error { kind := .truncatedArchive, message := "tar archive is empty or not 512-byte aligned" } := by
  unfold Impl.unpackWith; rw [ite_eq_left (by rcases h with hz | hm <;> simp [*, bne])]
private theorem mkRegularFrame_size (p : String) (d : ByteArray) : (mkRegularFrame p d).size = 512 + pad512 d.size := by
  rw [mkRegularFrame, ByteArray.size_append, mkUstarHeader_size, padBlock512_size]
private theorem mkRegularFrame_empty (p : String) : mkRegularFrame p ByteArray.empty = mkUstarHeader p 0o644 0 0 0 0 0x30 "" "" "" "" := by
  rw [mkRegularFrame, show padBlock512 ByteArray.empty = ByteArray.empty from rfl, ByteArray.append_empty]; rfl
private theorem mkPaxFrame_size (pax : ByteArray) : (mkPaxFrame pax).size = 512 + pad512 pax.size := by
  rw [mkPaxFrame, ByteArray.size_append, mkUstarHeader_size, padBlock512_size]
private theorem isZeroRange_zeroBlock_mid (a b : ByteArray) : isZeroRange (a ++ (zeroBlock ++ b)) a.size 512 = true := by
  refine (isZeroRange_eq_true_iff _ a.size 512 (by decide)).mpr ⟨by simp [ByteArray.size_append], fun i hi _ => ?_⟩
  rw [getElem_append_right (by omega), ByteArray.getElem_append_left (by simp [hi])]; exact zeroBlock_getElem _

private theorem unpackLoop_at_zeroBlock_mid (opts : UnpackOptions) (pre rest : ByteArray)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat) :
    unpackLoop opts (pre ++ (zeroBlock ++ rest)) pre.size pendingPax seen acc totalBytes =
      if pendingPax.isSome then .error { kind := .invalidHeader, message := "dangling PAX header before zero block", offset := some pre.size }
      else if pre.size + 512 ≥ (pre ++ (zeroBlock ++ rest)).size then .error { kind := .truncatedArchive, message := "tar archive has only one trailing zero block", offset := some pre.size }
      else if !isZeroRange (pre ++ (zeroBlock ++ rest)) (pre.size + 512) 512 then .error { kind := .invalidHeader, message := "non-zero block after single zero block", offset := some (pre.size + 512) }
      else if !allZeroTrailer (pre ++ (zeroBlock ++ rest)) (pre.size + 1024) then .error { kind := .invalidHeader, message := "non-zero garbage after tar end-of-archive marker", offset := some (pre.size + 1024) }
      else .ok acc.reverse := by
  obtain ⟨bytes, hbytes⟩ : ∃ b, b = pre ++ (zeroBlock ++ rest) := ⟨_, rfl⟩; rw [← hbytes]
  have hng : ¬(pre.size ≥ bytes.size) := by simp only [hbytes, ByteArray.size_append, zeroBlock_size]; omega
  have hz1 : isZeroRange bytes pre.size 512 = true := by rw [hbytes]; exact isZeroRange_zeroBlock_mid pre rest
  rw [unpackLoop, unpackLoopFuel.eq_2, ite_eq_right hng]; unfold unpackStep; simp only [hng, ↓reduceIte, hz1]
  by_cases h1 : pendingPax.isSome = true; · simp only [h1, ↓reduceIte]
  by_cases h2 : pre.size + 512 ≥ bytes.size; · simp only [h1, Bool.false_eq_true, ↓reduceIte, h2]
  by_cases h3 : (!isZeroRange bytes (pre.size + 512) 512) = true; · simp only [h1, Bool.false_eq_true, ↓reduceIte, h2, h3]
  by_cases h4 : (!allZeroTrailer bytes (pre.size + 1024)) = true <;> simp only [h1, Bool.false_eq_true, ↓reduceIte, h2, h3, h4]

private theorem unpackLoop_at_padded_twoZeroBlocks (opts : UnpackOptions) (pre pad : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat) (hpad_mod : pad.size % 512 = 0) (hpad_zero : ∀ k (hk : k < pad.size), pad[k]'hk = 0) :
    unpackLoop opts (pre ++ twoZeroBlocks ++ pad) pre.size none seen acc totalBytes = .ok acc.reverse := by
  have ha : pre ++ twoZeroBlocks ++ pad = pre ++ (zeroBlock ++ (zeroBlock ++ pad)) := by simp [twoZeroBlocks, ByteArray.append_assoc]
  have hsz : (pre ++ (zeroBlock ++ (zeroBlock ++ pad))).size = pre.size + 1024 + pad.size := by simp [ByteArray.size_append, zeroBlock_size]; omega
  have hz2 : isZeroRange (pre ++ (zeroBlock ++ (zeroBlock ++ pad))) (pre.size + 512) 512 = true := by
    simpa only [ByteArray.append_assoc, ByteArray.size_append, zeroBlock_size] using isZeroRange_zeroBlock_mid (pre ++ zeroBlock) pad
  have htr : allZeroTrailer (pre ++ (zeroBlock ++ (zeroBlock ++ pad))) (pre.size + 1024) = true := by
    refine allZeroTrailer_of_zeros (by rw [hsz]; omega) fun k hk _ _ => ?_
    have hk' : (pre ++ twoZeroBlocks).size ≤ k := by rw [ByteArray.size_append, twoZeroBlocks_size]; exact hk
    simpa only [ha] using (getElem_append_right (a := pre ++ twoZeroBlocks) (b := pad) hk' (by rw [ha, hsz] at *; omega)).trans (hpad_zero _ _)
  have hng2 : ¬(pre.size + 512 ≥ (pre ++ (zeroBlock ++ (zeroBlock ++ pad))).size) := by rw [hsz]; omega
  rw [ha, unpackLoop_at_zeroBlock_mid]; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hng2, hz2, htr, Bool.not_true]

/-- `unpackLoop` at `pre ++ (zeroBlock ++ zeroBlock)` immediately returns `.ok acc.reverse`. -/
theorem unpackLoop_at_twoZeroBlocks (opts : UnpackOptions) (pre : ByteArray) (seen : List String) (acc : List TarEntry) (totalBytes : Nat) :
    unpackLoop opts (pre ++ (zeroBlock ++ zeroBlock)) pre.size none seen acc totalBytes = .ok acc.reverse := by
  simpa only [twoZeroBlocks, ByteArray.append_empty] using
    unpackLoop_at_padded_twoZeroBlocks opts pre ByteArray.empty seen acc totalBytes rfl (fun _ hk => False.elim (Nat.not_lt_zero _ hk))

private theorem extract_padBlock512_mid (a bs c : ByteArray) : (a ++ (padBlock512 bs ++ c)).extract a.size (a.size + bs.size) = bs := by
  rw [extract_append_right]; have hle : bs.size ≤ (padBlock512 bs).size := by rw [padBlock512_size]; exact le_pad512 _
  have hs : (padBlock512 bs ++ c).extract 0 bs.size = ((padBlock512 bs ++ c).extract 0 (padBlock512 bs).size).extract 0 bs.size := by
    simp only [ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left hle]
  rw [hs, extract_append_exact_left, padBlock512_extract_prefix]

private def evalEntry (opts : UnpackOptions) (offset : Nat) (trunc : Bool) (hdr : UstarHeaderFields)
    (pendingPax : Option PaxOverrides) (name linkname : String) (seen : List String) (accLen totalBytes : Nat) (payload : ByteArray) :
    Except TarError (TarEntry × Nat) :=
  let kind? := if hdr.typeflag == 0x30 || hdr.typeflag == 0x00 then some EntryKind.regular
    else if hdr.typeflag == 0x35 then some .directory else if hdr.typeflag == 0x32 then some .symlink else none
  match kind? with
  | none => .error { kind := .unsupportedEntry, message := s!"unsupported tar entry typeflag: {hdr.typeflag.toNat}", offset := some offset }
  | some kind =>
    let pax := pendingPax.getD {}; let effSize := pax.size?.getD hdr.size
    if kind != .regular && effSize != 0 then .error { kind := .invalidHeader, message := "non-regular tar entry has non-zero size", offset := some offset }
    else if accLen + 1 > opts.maxEntries then .error { kind := .resourceLimitExceeded, message := "tar archive exceeds maxEntries limit", offset := some offset }
    else if totalBytes + effSize > opts.maxTotalBytes then .error { kind := .resourceLimitExceeded, message := "tar archive exceeds maxTotalBytes limit", offset := some offset }
    else if trunc then .error { kind := .truncatedArchive, message := "truncated tar entry payload", offset := some offset }
    else
      let rawLink := match kind with | .symlink => pax.linkpath?.getD linkname | .regular | .directory => ""
      match validateEntryPath opts.allowAbsolute opts.allowParentTraversal kind (pax.path?.getD name) with
      | .error err => .error { err with offset := some offset }
      | .ok normPath =>
        match (match kind with | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath rawLink | .regular | .directory => .ok ()) with
        | .error err => .error { err with offset := some offset }
        | .ok () =>
          if seen.contains normPath then
            .error { kind := .duplicatePath, message := s!"duplicate tar entry path: {normPath}", entryPath := some normPath, offset := some offset }
          else .ok ({ path := normPath, kind := kind, mode := (hdr.mode &&& 0o7777).toUInt32, uid := pax.uid?.getD hdr.uid,
                      gid := pax.gid?.getD hdr.gid, mtime := pax.mtime?.getD hdr.mtime, uname := pax.uname?.getD "",
                      gname := pax.gname?.getD "", data := payload, linkTarget := rawLink }, pad512 effSize)

private theorem decodeTarEntry_mkUstarHeader (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    {name linkname : String} {mode : UInt32} {hdrSize : Nat} {typeflag : UInt8}
    (pendingPax : Option PaxOverrides) (seen : List String) (accLen totalBytes : Nat) (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = mkUstarHeader name mode 0 0 hdrSize 0 typeflag linkname "" "" "")
    (hnm_sz : name.toUTF8.size ≤ 100) (hnm_nul : !hasNulString name = true)
    (hlk_sz : linkname.toUTF8.size ≤ 100) (hlk_nul : !hasNulString linkname = true) :
    let effSize := (pendingPax.getD {}).size?.getD hdrSize
    decodeTarEntry opts bytes offset { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := hdrSize, mtime := 0, typeflag := typeflag }
      pendingPax seen accLen totalBytes =
    evalEntry opts offset (decide (offset + 512 + pad512 effSize > bytes.size))
      { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := hdrSize, mtime := 0, typeflag := typeflag }
      pendingPax name linkname seen accLen totalBytes
      (if effSize == 0 then ByteArray.empty else bytes.extract (offset + 512) (offset + 512 + effSize)) := by
  have ⟨hs_nm, hs_lk, hs_un, hs_gn, hs_pf⟩ := buildUstarHeader_extract_strings (hext.trans (mkUstarHeader_eq_buildUstarHeader ..))
  have hd_at : ∀ {s w : Nat} {str lbl : String}, !hasNulString str = true → str.toUTF8.size ≤ w →
      offset + (s + w) ≤ bytes.size → bytes.extract (offset + s) (offset + (s + w)) = padRightBytes w str.toUTF8 →
      decodeCStringUtf8 bytes (offset + s) (offset + (s + w)) offset lbl = .ok str := by
    intro s w str lbl hn hsz hb hx; rw [← Nat.add_assoc]; exact decodeCStringUtf8_padRightBytes hn hsz (by omega) (by simpa only [Nat.add_assoc] using hx)
  have hd_nm : decodeCStringUtf8 bytes offset (offset + 100) offset "name" = .ok name := decodeCStringUtf8_padRightBytes hnm_nul hnm_sz (by omega) hs_nm
  have hd_lk := hd_at (s := 157) (w := 100) (lbl := "linkname") hlk_nul hlk_sz (by omega) hs_lk
  have hd_un := hd_at (s := 265) (w := 32) (lbl := "uname") rfl (by decide) (by omega) hs_un
  have hd_gn := hd_at (s := 297) (w := 32) (lbl := "gname") rfl (by decide) (by omega) hs_gn
  have hd_pf := hd_at (s := 345) (w := 155) (lbl := "prefix") rfl (by decide) (by omega) hs_pf
  unfold decodeTarEntry evalEntry; dsimp only
  cases (if typeflag == 0x30 || typeflag == 0x00 then some EntryKind.regular
         else if typeflag == 0x35 then some EntryKind.directory else if typeflag == 0x32 then some EntryKind.symlink else none) with
  | none => rfl
  | some kind =>
    dsimp only; iterate 3 (split; · rfl)
    by_cases ht : offset + 512 + pad512 ((pendingPax.getD {}).size?.getD hdrSize) > bytes.size
    · simp only [ht, decide_eq_true_eq, ↓reduceIte]
    · simp only [ht, decide_eq_true_eq, ↓reduceIte, hd_nm, hd_pf, hd_lk, hd_un, hd_gn]
      cases (pendingPax.getD {}).path? <;> cases (pendingPax.getD {}).linkpath? <;>
        cases (pendingPax.getD {}).uname? <;> cases (pendingPax.getD {}).gname? <;> cases kind <;> rfl

private theorem unpackStep_mkUstarHeader (opts : UnpackOptions) (pre hdr post : ByteArray)
    {name linkname : String} {mode : UInt32} {hdrSize : Nat} {typeflag : UInt8}
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hhdr : hdr = mkUstarHeader name mode 0 0 hdrSize 0 typeflag linkname "" "" "") (hsz_lt : hdrSize < ustarOctal11Limit) :
    unpackStep opts (pre ++ hdr ++ post) pre.size pendingPax seen acc totalBytes =
      if typeflag == 0x78 then
        if pendingPax.isSome then .error { kind := .invalidHeader, message := "consecutive PAX 'x' headers are not allowed", offset := some pre.size }
        else if hdrSize > maxPaxHeaderBytes then .error { kind := .resourceLimitExceeded, message := "PAX header exceeds maxPaxHeaderBytes", offset := some pre.size }
        else if pre.size + 512 + pad512 hdrSize > (pre ++ hdr ++ post).size then .error { kind := .truncatedArchive, message := "truncated PAX extended header payload", offset := some pre.size }
        else match parsePaxPayload ((pre ++ hdr ++ post).extract (pre.size + 512) (pre.size + 512 + hdrSize)) pre.size with
          | .error err => .error err | .ok paxOv => .ok (.cont (pre.size + 512 + pad512 hdrSize) (some paxOv) seen acc totalBytes)
      else match decodeTarEntry opts (pre ++ hdr ++ post) pre.size
          { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := hdrSize, mtime := 0, typeflag := typeflag } pendingPax seen acc.length totalBytes with
        | .error err => .error err
        | .ok (entry, padded) => .ok (.cont (pre.size + 512 + padded) none (entry.path :: seen) (entry :: acc) (totalBytes + entry.data.size)) := by
  have hhdr_sz : hdr.size = 512 := by rw [hhdr, mkUstarHeader_size]
  have hbd : pre.size + 512 ≤ (pre ++ hdr ++ post).size := by simp only [ByteArray.size_append, hhdr_sz]; omega
  have hext : (pre ++ hdr ++ post).extract pre.size (pre.size + 512) = mkUstarHeader name mode 0 0 hdrSize 0 typeflag linkname "" "" "" := by
    have h := extract_append_mid pre hdr post; rw [hhdr_sz] at h; exact h.trans hhdr
  have hnz := isZeroRange_buildUstarHeader_false hbd (hext.trans (mkUstarHeader_eq_buildUstarHeader ..))
  have hparse := parseUstarHeader_mkUstarHeader (by simp [ustarOctal7Limit]) (by simp [ustarOctal7Limit]) hsz_lt (by simp [ustarOctal11Limit]) hbd hext
  have hng : ¬(pre.size ≥ (pre ++ hdr ++ post).size) := by omega
  have hng512 : ¬(pre.size + 512 > (pre ++ hdr ++ post).size) := by omega
  unfold unpackStep; simp only [hng, ↓reduceIte, hnz, Bool.false_eq_true, hng512, hparse]
  by_cases htf : (typeflag == 0x78) = true
  · simp only [htf, ↓reduceIte]; iterate 3 (split; · rfl)
    cases parsePaxPayload ((pre ++ hdr ++ post).extract (pre.size + 512) (pre.size + 512 + hdrSize)) pre.size <;> rfl
  · simp only [htf, Bool.false_eq_true, ↓reduceIte]
    cases decodeTarEntry opts (pre ++ hdr ++ post) pre.size
      { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := hdrSize, mtime := 0, typeflag := typeflag } pendingPax seen acc.length totalBytes <;> rfl

private theorem unpackStep_mkPaxFrame (opts : UnpackOptions) (pre post pax : ByteArray)
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat) (hpax_sz : pax.size ≤ maxPaxHeaderBytes) :
    unpackStep opts (pre ++ mkPaxFrame pax ++ post) pre.size pendingPax seen acc totalBytes =
      if pendingPax.isSome then .error { kind := .invalidHeader, message := "consecutive PAX 'x' headers are not allowed", offset := some pre.size }
      else match parsePaxPayload pax pre.size with
        | .error err => .error err | .ok ov => .ok (.cont (pre.size + 512 + pad512 pax.size) (some ov) seen acc totalBytes) := by
  obtain ⟨hdr, hhdr⟩ : ∃ b, b = mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" "" := ⟨_, rfl⟩
  have hhdr_sz : hdr.size = 512 := by rw [hhdr, mkUstarHeader_size]
  have hassoc : pre ++ mkPaxFrame pax ++ post = pre ++ hdr ++ (padBlock512 pax ++ post) := by simp [mkPaxFrame, ← hhdr, ByteArray.append_assoc]
  have hlt : pax.size < ustarOctal11Limit := by simp only [maxPaxHeaderBytes, ustarOctal11Limit] at hpax_sz ⊢; omega
  have hsz : (pre ++ hdr ++ (padBlock512 pax ++ post)).size = pre.size + 512 + pad512 pax.size + post.size := by simp [ByteArray.size_append, hhdr_sz, padBlock512_size]; omega
  have hext : (pre ++ hdr ++ (padBlock512 pax ++ post)).extract (pre.size + 512) (pre.size + 512 + pax.size) = pax := by
    simpa only [ByteArray.append_assoc, ByteArray.size_append, hhdr_sz] using extract_padBlock512_mid (pre ++ hdr) pax post
  rw [hassoc, unpackStep_mkUstarHeader opts pre hdr (padBlock512 pax ++ post) pendingPax seen acc totalBytes hhdr hlt]
  have hng1 : ¬(pax.size > maxPaxHeaderBytes) := by omega
  have hng2 : ¬(pre.size + 512 + pad512 pax.size > (pre ++ hdr ++ (padBlock512 pax ++ post)).size) := by rw [hsz]; omega
  by_cases hp : pendingPax.isSome = true <;> simp only [beq_self_eq_true, ↓reduceIte, hp, Bool.false_eq_true, hng1, hng2, hext]

private theorem unpackLoop_mkPaxFrame_step (opts : UnpackOptions) (pre post pax : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat) (hpax_sz : pax.size ≤ maxPaxHeaderBytes)
    (ov : PaxOverrides) (hparse : parsePaxPayload pax pre.size = .ok ov) :
    unpackLoop opts (pre ++ mkPaxFrame pax ++ post) pre.size none seen acc totalBytes =
      unpackLoop opts (pre ++ mkPaxFrame pax ++ post) (pre.size + 512 + pad512 pax.size) (some ov) seen acc totalBytes := by
  have hsz : (pre ++ mkPaxFrame pax ++ post).size = pre.size + (512 + pad512 pax.size) + post.size := by simp [ByteArray.size_append, mkPaxFrame_size]
  refine unpackLoop_step_continue opts _ pre.size none seen acc totalBytes (pre.size + 512 + pad512 pax.size) (some ov) seen acc totalBytes (by rw [hsz]; omega) ?_ (by omega)
  rw [unpackStep_mkPaxFrame opts pre post pax none seen acc totalBytes hpax_sz, Option.isSome_none, ite_eq_right Bool.false_ne_true, hparse]

/-- Error certificate for `Impl.unpackWith` when `parsePaxPayload` fails on a leading `mkPaxFrame`. -/
theorem unpackWith_mkPaxFrame_err (opts : UnpackOptions) (pax post : ByteArray) {err : TarError}
    (hpax_sz : pax.size ≤ maxPaxHeaderBytes) (hpost : post.size % 512 = 0) (hparse : parsePaxPayload pax 0 = .error err) :
    Impl.unpackWith opts (mkPaxFrame pax ++ post) = .error err := by
  have hsz : (mkPaxFrame pax ++ post).size = 512 + pad512 pax.size + post.size := by rw [ByteArray.size_append, mkPaxFrame_size]
  rw [unpackWith_eq_unpackLoop (by rw [hsz]; omega) (by have := pad512_mod pax.size; rw [hsz]; omega)]
  refine unpackLoop_step_err opts _ 0 none [] [] 0 err (by rw [hsz]; omega) ?_
  simpa only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hparse] using
    unpackStep_mkPaxFrame opts ByteArray.empty post pax none [] [] 0 hpax_sz

private theorem unpackLoop_hdr_ok (opts : UnpackOptions) (pre hdr blk post : ByteArray)
    {name : String} {mode : UInt32} {hdrSize : Nat} {typeflag : UInt8}
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) (totalBytes : Nat) (entry : TarEntry) (padded : Nat) (data : ByteArray)
    (hhdr : hdr = mkUstarHeader name mode 0 0 hdrSize 0 typeflag "" "" "" "") (hblk : blk.size = pad512 hdrSize)
    (hdata : (if hdrSize == 0 then ByteArray.empty else blk.extract 0 hdrSize) = data) (hosz : (pendingPax.getD {}).size? = none := by rfl)
    (hnm_sz : name.toUTF8.size ≤ 100 := by decide) (hnm_nul : !hasNulString name = true := by rfl)
    (hsz_lt : hdrSize < ustarOctal11Limit := by simp [ustarOctal11Limit]) (htf78 : (typeflag == 0x78) = false := by rfl)
    (heval : evalEntry opts pre.size false { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := hdrSize, mtime := 0, typeflag := typeflag }
      pendingPax name "" seen acc.length totalBytes data = .ok (entry, padded) := by rfl) :
    unpackLoop opts (pre ++ hdr ++ (blk ++ post)) pre.size pendingPax seen acc totalBytes =
      unpackLoop opts (pre ++ hdr ++ (blk ++ post)) (pre.size + 512 + padded) none (entry.path :: seen) (entry :: acc) (totalBytes + entry.data.size) := by
  have hhdr_sz : hdr.size = 512 := by rw [hhdr, mkUstarHeader_size]
  have htot : (pre ++ hdr ++ (blk ++ post)).size = pre.size + 512 + pad512 hdrSize + post.size := by simp [ByteArray.size_append, hhdr_sz, hblk]; omega
  have hext_hdr : (pre ++ hdr ++ (blk ++ post)).extract pre.size (pre.size + 512) = mkUstarHeader name mode 0 0 hdrSize 0 typeflag "" "" "" "" := by
    have h := extract_append_mid pre hdr (blk ++ post); rw [hhdr_sz] at h; exact h.trans hhdr
  have hext_pay : (if hdrSize == 0 then ByteArray.empty else (pre ++ hdr ++ (blk ++ post)).extract (pre.size + 512) (pre.size + 512 + hdrSize)) = data := by
    by_cases hz : hdrSize = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte] at hdata ⊢; exact hdata
    · simp only [hz, beq_iff_eq, ↓reduceIte] at hdata ⊢
      have hp : (pre ++ hdr).size = pre.size + 512 := by rw [ByteArray.size_append, hhdr_sz]
      have hle : hdrSize ≤ blk.size := by rw [hblk]; exact le_pad512 _
      have hs : (blk ++ post).extract 0 hdrSize = ((blk ++ post).extract 0 blk.size).extract 0 hdrSize := by simp [ByteArray.extract_extract, hle]
      rw [← hp, extract_append_right, hs, extract_append_exact_left, hdata]
  refine unpackLoop_step_continue opts _ pre.size pendingPax seen acc totalBytes
    (pre.size + 512 + padded) none (entry.path :: seen) (entry :: acc) (totalBytes + entry.data.size) (by rw [htot]; omega) ?_ (by omega)
  rw [unpackStep_mkUstarHeader opts pre hdr (blk ++ post) pendingPax seen acc totalBytes hhdr hsz_lt, htf78, ite_eq_right Bool.false_ne_true,
    decodeTarEntry_mkUstarHeader opts _ pre.size pendingPax seen acc.length totalBytes (by rw [htot]; omega) hext_hdr hnm_sz hnm_nul (by decide) rfl]
  rw [hosz, Option.getD_none, decide_eq_false (by rw [htot]; omega), hext_pay, heval]

private theorem unpackLoop_hdr_err (opts : UnpackOptions) (pre hdr post : ByteArray)
    {name linkname : String} {mode : UInt32} {hdrSize off totSz : Nat} {typeflag : UInt8}
    (pendingPax : Option PaxOverrides) (seen : List String) (acc : List TarEntry) {e : TarError}
    (hhdr : hdr = mkUstarHeader name mode 0 0 hdrSize 0 typeflag linkname "" "" "") (hoff : pre.size = off) (htot : off + 512 + post.size = totSz)
    (hsz_lt : hdrSize < ustarOctal11Limit := by simp [ustarOctal11Limit])
    (hnm_sz : name.toUTF8.size ≤ 100 := by decide) (hnm_nul : !hasNulString name = true := by rfl)
    (hlk_sz : linkname.toUTF8.size ≤ 100 := by decide) (hlk_nul : !hasNulString linkname = true := by rfl) (htf78 : (typeflag == 0x78) = false := by rfl)
    (herr : ∀ p, evalEntry opts off (decide (off + 512 + pad512 ((pendingPax.getD {}).size?.getD hdrSize) > totSz))
      { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := hdrSize, mtime := 0, typeflag := typeflag }
      pendingPax name linkname seen acc.length 0 p = .error e := by intro _; rfl) :
    unpackLoop opts (pre ++ hdr ++ post) off pendingPax seen acc 0 = .error e := by
  have hhdr_sz : hdr.size = 512 := by rw [hhdr, mkUstarHeader_size]
  have hsz : (pre ++ hdr ++ post).size = totSz := by simp only [ByteArray.size_append, hoff, hhdr_sz, htot]
  refine unpackLoop_step_err opts _ off pendingPax seen acc 0 e (by rw [hsz]; omega) ?_
  have hs := unpackStep_mkUstarHeader opts pre hdr post pendingPax seen acc 0 hhdr hsz_lt
  rw [hoff, htf78, ite_eq_right Bool.false_ne_true] at hs; rw [hs]
  have hext : (pre ++ hdr ++ post).extract off (off + 512) = mkUstarHeader name mode 0 0 hdrSize 0 typeflag linkname "" "" "" := by
    have h := extract_append_mid pre hdr post; rw [hoff, hhdr_sz] at h; exact h.trans hhdr
  have hd := decodeTarEntry_mkUstarHeader opts (pre ++ hdr ++ post) off pendingPax seen acc.length 0 (by rw [hsz]; omega) hext hnm_sz hnm_nul hlk_sz hlk_nul
  dsimp only at hd; rw [hsz, herr] at hd; rw [hd]

/-- Unpack `bytes` equal to `mkPaxFrame pax ++ hdr ++ twoZeroBlocks` into a single `TarEntry`. -/
theorem unpackWith_pax_emptyRegular_ok (opts : UnpackOptions) (bytes pax hdr : ByteArray) (name normPath : String) (ov : PaxOverrides)
    (hbytes : bytes = mkPaxFrame pax ++ hdr ++ twoZeroBlocks) (hhdr : hdr = mkUstarHeader name 0o644 0 0 0 0 0x30 "" "" "" "")
    (hpax_sz : pax.size ≤ maxPaxHeaderBytes := by decide) (hparse : parsePaxPayload pax 0 = .ok ov := by rfl)
    (hosz : ov.size? = none := by rfl) (hou : ov.uname? = none := by rfl) (hog : ov.gname? = none := by rfl)
    (hnm_sz : name.toUTF8.size ≤ 100 := by decide) (hnm_nul : !hasNulString name = true := by rfl)
    (hval : validateEntryPath opts.allowAbsolute opts.allowParentTraversal .regular (ov.path?.getD name) = .ok normPath := by rfl)
    (hentries : 1 ≤ opts.maxEntries := by decide) :
    Impl.unpackWith opts bytes =
      .ok [{ path := normPath, kind := .regular, mode := 0o644, uid := ov.uid?.getD 0, gid := ov.gid?.getD 0, mtime := ov.mtime?.getD 0 }] := by
  obtain ⟨pf, hpf⟩ : ∃ b, b = mkPaxFrame pax := ⟨_, rfl⟩
  have hpf_sz : pf.size = 512 + pad512 pax.size := by rw [hpf, mkPaxFrame_size]
  have hhdr_sz : hdr.size = 512 := by rw [hhdr, mkUstarHeader_size]
  have htot : (pf ++ hdr ++ twoZeroBlocks).size = 512 + pad512 pax.size + 512 + 1024 := by simp [ByteArray.size_append, hpf_sz, hhdr_sz, twoZeroBlocks_size]
  rw [show bytes = pf ++ hdr ++ twoZeroBlocks by rw [hbytes, ← hpf],
    unpackWith_eq_unpackLoop (by rw [htot]; omega) (by have := pad512_mod pax.size; rw [htot]; omega)]
  have hs1 := unpackLoop_mkPaxFrame_step opts ByteArray.empty (hdr ++ twoZeroBlocks) pax [] [] 0 hpax_sz ov hparse
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add, ← hpf, ← ByteArray.append_assoc] at hs1; rw [hs1, ← hpf_sz]
  let entry : TarEntry := { path := normPath, kind := .regular, mode := 0o644, uid := ov.uid?.getD 0, gid := ov.gid?.getD 0, mtime := ov.mtime?.getD 0 }
  have hev : evalEntry opts pf.size false { mode := 0o644, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x30 }
      (some ov) name "" [] 0 0 ByteArray.empty = .ok (entry, 0) := by
    have he1 : ¬(opts.maxEntries < 1) := by omega
    simp [evalEntry, hosz, hval, hou, hog, he1, entry]
  have hs2 := unpackLoop_hdr_ok opts pf hdr ByteArray.empty twoZeroBlocks (some ov) [] [] 0 entry 0 ByteArray.empty
    hhdr rfl rfl hosz hnm_sz hnm_nul (by simp [ustarOctal11Limit]) rfl hev
  simp only [ByteArray.empty_append, Nat.add_zero] at hs2
  rw [hs2, ← (by rw [ByteArray.size_append, hhdr_sz] : (pf ++ hdr).size = pf.size + 512)]
  exact unpackLoop_at_twoZeroBlocks opts (pf ++ hdr) _ _ 0

private theorem unpackWith_single_raw_err (opts : UnpackOptions) (bytes hdr post : ByteArray)
    {name linkname : String} {mode : UInt32} {hdrSize postSz : Nat} {typeflag : UInt8} {e : TarError}
    (hbytes : bytes = hdr ++ post) (hhdr : hdr = mkUstarHeader name mode 0 0 hdrSize 0 typeflag linkname "" "" "")
    (hpost : post.size = postSz) (hmod : postSz % 512 = 0 := by rfl) (hsz_lt : hdrSize < ustarOctal11Limit := by simp [ustarOctal11Limit])
    (hnm_sz : name.toUTF8.size ≤ 100 := by decide) (hnm_nul : !hasNulString name = true := by rfl)
    (hlk_sz : linkname.toUTF8.size ≤ 100 := by decide) (hlk_nul : !hasNulString linkname = true := by rfl) (htf78 : (typeflag == 0x78) = false := by rfl)
    (herr : ∀ p, evalEntry opts 0 (decide (512 + pad512 hdrSize > 512 + postSz))
      { mode := (mode &&& 0o7777).toNat, uid := 0, gid := 0, size := hdrSize, mtime := 0, typeflag := typeflag }
      none name linkname [] 0 0 p = .error e := by intro _; rfl) : Impl.unpackWith opts bytes = .error e := by
  have htot : (hdr ++ post).size = 512 + postSz := by rw [ByteArray.size_append, hhdr, mkUstarHeader_size, hpost]
  rw [hbytes, unpackWith_eq_unpackLoop (by rw [htot]; omega) (by rw [htot]; omega)]
  simpa only [ByteArray.empty_append] using unpackLoop_hdr_err opts ByteArray.empty hdr post none [] []
    hhdr ByteArray.size_empty (by simp [hpost]) hsz_lt hnm_sz hnm_nul hlk_sz hlk_nul htf78 herr

private theorem test4_for (api : TarApi) (hu : api.unpackWith = Impl.unpackWith) (hup : api.unpack = Impl.unpackWith {}) :
    AllPass (test_tar_unpackWith_framingAndTrailer_validated api) := by
  obtain ⟨reg, hreg⟩ : ∃ b, b = mkRegularFrame "a.txt" "hi".toUTF8 := ⟨_, rfl⟩
  obtain ⟨pax, hpax⟩ : ∃ b, b = mkPaxFrame (encodePaxRecord "path" "a.txt") := ⟨_, rfl⟩
  obtain ⟨hdr, hhdr⟩ : ∃ b, b = mkUstarHeader "p.txt" 0o644 0 0 2 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  obtain ⟨dirty, hdirty⟩ : ∃ b, b = ByteArray.mk (#[0x41, 0x42] ++ Array.replicate 510 0xff) := ⟨_, rfl⟩
  obtain ⟨rh, hrh⟩ : ∃ b, b = mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  have hreg_sz : reg.size = 1024 := by rw [hreg, mkRegularFrame_size]; rfl
  have hpax_sz : pax.size = 1024 := by rw [hpax, mkPaxFrame_size]; rfl
  have hrh_sz : rh.size = 512 := by rw [hrh, mkUstarHeader_size]
  let entryA : TarEntry := { path := "a.txt", kind := .regular, data := "hi".toUTF8 }
  have hstep1024 : ∀ {pre : ByteArray} {p s a t}, pre.size = 1024 →
      (∀ post, unpackLoop {} (pre ++ post) 0 none [] [] 0 = unpackLoop {} (pre ++ post) 1024 p s a t) →
      ∀ {post : ByteArray}, post.size % 512 = 0 → Impl.unpackWith {} (pre ++ post) = unpackLoop {} (pre ++ post) 1024 p s a t := by
    intro pre p s a t hsz hst post hm; have htot : (pre ++ post).size = 1024 + post.size := by rw [ByteArray.size_append, hsz]
    rw [unpackWith_eq_unpackLoop (by rw [htot]; omega) (by rw [htot]; omega), hst]
  have hreg_step : ∀ post, unpackLoop {} (reg ++ post) 0 none [] [] 0 = unpackLoop {} (reg ++ post) 1024 none ["a.txt"] [entryA] 2 := by
    intro post; have ha : reg ++ post = ByteArray.empty ++ rh ++ (padBlock512 "hi".toUTF8 ++ post) := by
      rw [hreg, mkRegularFrame, show ("hi".toUTF8).size = 2 from rfl, ← hrh, ByteArray.empty_append, ByteArray.append_assoc]
    have hd : (if (2 : Nat) == 0 then ByteArray.empty else (padBlock512 "hi".toUTF8).extract 0 2) = "hi".toUTF8 := by
      rw [show ((2 : Nat) == 0) = false from rfl, ite_eq_right Bool.false_ne_true]; exact padBlock512_extract_prefix _
    simpa only [← ha, ByteArray.size_empty, Nat.zero_add, entryA, show 512 + 512 = 1024 from rfl, show ("hi".toUTF8).size = 2 from rfl] using
      unpackLoop_hdr_ok {} ByteArray.empty rh (padBlock512 "hi".toUTF8) post none [] [] 0 entryA 512 "hi".toUTF8 hrh (by rw [padBlock512_size]; rfl) hd
  have hpax_step : ∀ post, unpackLoop {} (pax ++ post) 0 none [] [] 0 = unpackLoop {} (pax ++ post) 1024 (some { path? := some "a.txt" }) [] [] 0 := by
    intro post; simpa only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add, ← hpax, show 512 + pad512 (encodePaxRecord "path" "a.txt").size = 1024 from rfl] using
      unpackLoop_mkPaxFrame_step {} ByteArray.empty post (encodePaxRecord "path" "a.txt") [] [] 0 (by decide) { path? := some "a.txt" } rfl
  have hreg_nz : ∀ pre : ByteArray, isZeroRange (pre ++ reg) pre.size 512 = false := by
    intro pre; have ha : pre ++ reg = pre ++ rh ++ padBlock512 "hi".toUTF8 := by rw [hreg, mkRegularFrame, show ("hi".toUTF8).size = 2 from rfl, ← hrh, ByteArray.append_assoc]
    rw [ha]; have hext : (pre ++ rh ++ padBlock512 "hi".toUTF8).extract pre.size (pre.size + 512) = mkUstarHeader "a.txt" 0o644 0 0 2 0 0x30 "" "" "" "" := by
      have h := extract_append_mid pre rh (padBlock512 "hi".toUTF8); rw [hrh_sz] at h; exact h.trans hrh
    exact isZeroRange_buildUstarHeader_false (by simp only [ByteArray.size_append, hrh_sz]; omega) (hext.trans (mkUstarHeader_eq_buildUstarHeader ..))
  have heof : ∀ (x : ByteArray) {p s a t}, x.size = 1024 → (∀ post, unpackLoop {} (x ++ post) 0 none [] [] 0 = unpackLoop {} (x ++ post) 1024 p s a t) →
      Impl.unpackWith {} x = .error { kind := .truncatedArchive, message := "tar archive missing end-of-archive zero blocks", offset := some 1024 } := by
    intro x p s a t hx hst; have h1 := hstep1024 hx hst (post := ByteArray.empty) rfl
    rw [ByteArray.append_empty] at h1; exact h1.trans (unpackLoop_at_ge {} x 1024 _ _ _ _ (by omega))
  have hreg_zb : ∀ rest : ByteArray, rest.size % 512 = 0 → Impl.unpackWith {} (reg ++ (zeroBlock ++ rest)) =
      if 1536 ≥ (reg ++ (zeroBlock ++ rest)).size then .error { kind := .truncatedArchive, message := "tar archive has only one trailing zero block", offset := some 1024 }
      else if !isZeroRange (reg ++ (zeroBlock ++ rest)) 1536 512 then .error { kind := .invalidHeader, message := "non-zero block after single zero block", offset := some 1536 }
      else if !allZeroTrailer (reg ++ (zeroBlock ++ rest)) 2048 then .error { kind := .invalidHeader, message := "non-zero garbage after tar end-of-archive marker", offset := some 2048 }
      else .ok [entryA] := by
    intro rest hm; rw [hstep1024 hreg_sz hreg_step (by simp [ByteArray.size_append, zeroBlock_size, hm]), ← hreg_sz, unpackLoop_at_zeroBlock_mid, hreg_sz]; rfl
  have h5 : Impl.unpackWith {} (reg ++ zeroBlock) = .error { kind := .truncatedArchive, message := "tar archive has only one trailing zero block", offset := some 1024 } := by
    simpa [ByteArray.append_empty, ByteArray.size_append, hreg_sz, zeroBlock_size] using hreg_zb ByteArray.empty rfl
  have h6 : Impl.unpackWith {} (reg ++ zeroBlock ++ reg) = .error { kind := .invalidHeader, message := "non-zero block after single zero block", offset := some 1536 } := by
    have hz2 : isZeroRange (reg ++ (zeroBlock ++ reg)) 1536 512 = false := by simpa [ByteArray.append_assoc, ByteArray.size_append, hreg_sz, zeroBlock_size] using hreg_nz (reg ++ zeroBlock)
    rw [ByteArray.append_assoc, hreg_zb reg (by rw [hreg_sz])]; simp [ByteArray.size_append, hreg_sz, zeroBlock_size, hz2]
  have h8 : Impl.unpackWith {} (pax ++ twoZeroBlocks) = .error { kind := .invalidHeader, message := "dangling PAX header before zero block", offset := some 1024 } := by
    rw [hstep1024 hpax_sz hpax_step (by rw [twoZeroBlocks_size]), ← hpax_sz, show twoZeroBlocks = zeroBlock ++ zeroBlock from rfl, unpackLoop_at_zeroBlock_mid, hpax_sz]; rfl
  have h9 : Impl.unpackWith {} (pax ++ pax ++ reg ++ twoZeroBlocks) = .error { kind := .invalidHeader, message := "consecutive PAX 'x' headers are not allowed", offset := some 1024 } := by
    have ha1 : pax ++ pax ++ reg ++ twoZeroBlocks = pax ++ (pax ++ (reg ++ twoZeroBlocks)) := by simp [ByteArray.append_assoc]
    rw [ha1, hstep1024 hpax_sz hpax_step (by simp [ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size])]
    refine unpackLoop_step_err {} _ 1024 _ [] [] 0 _ (by simp [ByteArray.size_append, hpax_sz, hreg_sz, twoZeroBlocks_size]) ?_
    have hs := unpackStep_mkPaxFrame {} pax (reg ++ twoZeroBlocks) (encodePaxRecord "path" "a.txt") (some { path? := some "a.txt" }) [] [] 0 (by decide)
    rw [← hpax, ByteArray.append_assoc, hpax_sz] at hs; exact hs
  have h10 : Impl.unpackWith {} (reg ++ twoZeroBlocks ++ reg) = .error { kind := .invalidHeader, message := "non-zero garbage after tar end-of-archive marker", offset := some 2048 } := by
    have ha : reg ++ twoZeroBlocks ++ reg = reg ++ (zeroBlock ++ (zeroBlock ++ reg)) := by simp [twoZeroBlocks, ByteArray.append_assoc]
    have hz2 : isZeroRange (reg ++ (zeroBlock ++ (zeroBlock ++ reg))) 1536 512 = true := by simpa [ByteArray.append_assoc, ByteArray.size_append, hreg_sz, zeroBlock_size] using isZeroRange_zeroBlock_mid (reg ++ zeroBlock) reg
    have hnz3 : isZeroRange (reg ++ (zeroBlock ++ (zeroBlock ++ reg))) 2048 512 = false := by simpa [← ha, ByteArray.size_append, hreg_sz, twoZeroBlocks_size] using hreg_nz (reg ++ twoZeroBlocks)
    have htr : allZeroTrailer (reg ++ (zeroBlock ++ (zeroBlock ++ reg))) 2048 = false := by
      have hsz3 : (reg ++ (zeroBlock ++ (zeroBlock ++ reg))).size = 3072 := by simp [ByteArray.size_append, hreg_sz, zeroBlock_size]
      unfold allZeroTrailer; rw [hsz3, allZeroTrailer.go.eq_2, ite_eq_right (by omega), hnz3]; rfl
    rw [ha, hreg_zb _ (by simp [ByteArray.size_append, zeroBlock_size, hreg_sz])]; simp [ByteArray.size_append, hreg_sz, zeroBlock_size, hz2, htr]
  have h11 : Impl.unpackWith {} (reg ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock) = .ok [entryA] := by
    obtain ⟨pad, hpad⟩ : ∃ b, b = zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock := ⟨_, rfl⟩
    have hpad_sz : pad.size = 2048 := by simp only [hpad, ByteArray.size_append, zeroBlock_size]
    have hza : ∀ {x y : ByteArray}, (∀ i (hi : i < x.size), x[i]'hi = 0) → (∀ j (hj : j < y.size), y[j]'hj = 0) → ∀ k (hk : k < (x ++ y).size), (x ++ y)[k]'hk = 0 := by
      intro x y hx hy k hk; rw [byteArray_getElem_append]; split <;> first | exact hx _ _ | exact hy _ _
    have hz0 : ∀ i (hi : i < zeroBlock.size), zeroBlock[i]'hi = 0 := fun _ hi => zeroBlock_getElem hi
    have hpad_z : ∀ k (hk : k < pad.size), pad[k]'hk = 0 := by subst hpad; exact hza (hza (hza hz0 hz0) hz0) hz0
    have ha : reg ++ twoZeroBlocks ++ zeroBlock ++ zeroBlock ++ zeroBlock ++ zeroBlock = reg ++ (twoZeroBlocks ++ pad) := by simp [hpad, ByteArray.append_assoc]
    rw [ha, hstep1024 hreg_sz hreg_step (by rw [ByteArray.size_append, twoZeroBlocks_size, hpad_sz]), ← ByteArray.append_assoc]
    simpa only [hreg_sz, List.reverse_singleton] using unpackLoop_at_padded_twoZeroBlocks {} reg pad ["a.txt"] [entryA] 2 (by rw [hpad_sz]) hpad_z
  have h12 : Impl.unpackWith {} (hdr ++ dirty ++ twoZeroBlocks) = .ok [{ path := "p.txt", kind := .regular, data := "AB".toUTF8 }] := by
    obtain ⟨tail, htail, hdirty_eq⟩ : ∃ t : Array UInt8, t.size = 510 ∧ dirty = ByteArray.mk (#[0x41, 0x42] ++ t) := ⟨_, Array.size_replicate, hdirty⟩
    have hhdr_sz : hdr.size = 512 := by rw [hhdr, mkUstarHeader_size]
    have hdirty_sz : dirty.size = 512 := by rw [hdirty_eq]; change (#[0x41, 0x42] ++ tail).size = 512; simp [htail]
    have hsz : (hdr ++ dirty ++ twoZeroBlocks).size = 2048 := by simp [ByteArray.size_append, hhdr_sz, hdirty_sz, twoZeroBlocks_size]
    have hab : (if (2 : Nat) == 0 then ByteArray.empty else dirty.extract 0 2) = "AB".toUTF8 := by
      rw [show ((2 : Nat) == 0) = false from rfl, ite_eq_right Bool.false_ne_true]
      apply ByteArray.ext_getElem (by rw [ByteArray.size_extract, hdirty_sz]; rfl); intro i hi1 hi2
      rw [ByteArray.getElem_extract hi1]; subst hdirty_eq; change (#[0x41, 0x42] ++ tail)[0 + i]'_ = _
      simp only [Nat.zero_add]; rw [Array.getElem_append_left (by change i < 2; exact hi2)]; clear hi1; revert i hi2; decide
    rw [unpackWith_eq_unpackLoop (by rw [hsz]; omega) (by rw [hsz])]
    have hs := unpackLoop_hdr_ok {} ByteArray.empty hdr dirty twoZeroBlocks none [] [] 0 { path := "p.txt", kind := .regular, data := "AB".toUTF8 } 512 "AB".toUTF8 hhdr hdirty_sz hab
    simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add, ← ByteArray.append_assoc, show 512 + 512 = 1024 from rfl, show ("AB".toUTF8).size = 2 from rfl] at hs
    rw [hs]; have hp : (hdr ++ dirty).size = 1024 := by rw [ByteArray.size_append, hhdr_sz, hdirty_sz]
    simpa only [twoZeroBlocks, hp, List.reverse_singleton] using unpackLoop_at_twoZeroBlocks {} (hdr ++ dirty) ["p.txt"] [{ path := "p.txt", kind := .regular, data := "AB".toUTF8 }] 2
  unfold test_tar_unpackWith_framingAndTrailer_validated; dsimp only; rw [← hreg, ← hpax, ← hhdr, ← hdirty, hup]
  refine allPass_err_for hu (unpackWith_alignment_err {} ByteArray.empty (Or.inl rfl)) rfl rfl ?_
  refine allPass_err_for hu (unpackWith_alignment_err {} (ByteArray.mk #[0]) (Or.inr (by decide))) rfl rfl ?_
  refine allPass_err_for hu (unpackWith_alignment_err {} (twoZeroBlocks ++ ByteArray.mk #[1]) (Or.inr (by rw [ByteArray.size_append, twoZeroBlocks_size]; decide))) rfl rfl ?_
  refine allPass_err_for hu (heof reg hreg_sz hreg_step) rfl rfl ?_
  refine allPass_err_for hu h5 rfl rfl ?_
  refine allPass_err_for hu h6 rfl rfl ?_
  refine allPass_err_for hu (heof pax hpax_sz hpax_step) rfl rfl ?_
  refine allPass_err_for hu h8 rfl rfl ?_
  refine allPass_err_for hu h9 rfl rfl ?_
  refine allPass_err_for hu h10 rfl rfl ?_
  refine allPass_ok_bind_fn rfl h11 (tarEquiv_singleton_self _) ?_
  exact allPass_ok_last_impl h12 (tarEquiv_singleton_self _)

/-- Prove `test_tar_unpackWith_framingAndTrailer_validated` for `defaultApi`. -/
theorem allPass_unpackWith_framingAndTrailer_validated :
    AllPass (test_tar_unpackWith_framingAndTrailer_validated defaultApi) := test4_for defaultApi rfl rfl

private theorem test6_for (api : TarApi) (hu : api.unpackWith = Impl.unpackWith) :
    AllPass (test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced api) := by
  obtain ⟨rf, hrf⟩ : ∃ b, b = mkRegularFrame "a.txt" "hello".toUTF8 := ⟨_, rfl⟩
  obtain ⟨hdr5, hhdr5⟩ : ∃ b, b = mkUstarHeader "a.txt" 0o644 0 0 5 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  obtain ⟨post5, hpost5⟩ : ∃ b, b = padBlock512 "hello".toUTF8 ++ twoZeroBlocks := ⟨_, rfl⟩
  have hpost5_sz : post5.size = 1536 := by rw [hpost5, ByteArray.size_append, padBlock512_size, twoZeroBlocks_size]; rfl
  have hrf_eq : rf ++ twoZeroBlocks = hdr5 ++ post5 := by rw [hrf, mkRegularFrame, show ("hello".toUTF8).size = 5 from rfl, ← hhdr5, ByteArray.append_assoc, ← hpost5]
  obtain ⟨pzf, hpzf⟩ : ∃ b, b = mkPaxFrame (encodePaxRecord "path" "a.txt") ++ mkRegularFrame "a.txt" ByteArray.empty ++ twoZeroBlocks := ⟨_, rfl⟩
  obtain ⟨hdr0, hhdr0⟩ : ∃ b, b = mkUstarHeader "a.txt" 0o644 0 0 0 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  obtain ⟨bsp, hbsp⟩ : ∃ b, b = mkPaxFrame (encodePaxRecord "size" "8589934592") ++ mkRegularFrame "big.bin" ByteArray.empty ++ twoZeroBlocks := ⟨_, rfl⟩
  obtain ⟨hpHdr, hhp⟩ : ∃ b, b = mkUstarHeader "././@PaxHeader" 0o644 0 0 (maxPaxHeaderBytes + 1) 0 0x78 "" "" "" "" := ⟨_, rfl⟩
  have hbig : ∀ (opts : UnpackOptions) {e : TarError},
      (∀ p, evalEntry opts 1024 (decide (1024 + 512 + pad512 8589934592 > 2560)) { mode := 0o644, uid := 0, gid := 0, size := 0, mtime := 0, typeflag := 0x30 }
        (some { size? := some 8589934592 }) "big.bin" "" [] 0 0 p = .error e) → Impl.unpackWith opts bsp = .error e := by
    intro opts e hderr; obtain ⟨pf, hpf⟩ : ∃ b, b = mkPaxFrame (encodePaxRecord "size" "8589934592") := ⟨_, rfl⟩
    obtain ⟨hdr, hhdr⟩ : ∃ b, b = mkUstarHeader "big.bin" 0o644 0 0 0 0 0x30 "" "" "" "" := ⟨_, rfl⟩
    have hpf_sz : pf.size = 1024 := by rw [hpf, mkPaxFrame_size]; rfl
    have hsz : (pf ++ hdr ++ twoZeroBlocks).size = 2560 := by simp [ByteArray.size_append, hpf_sz, hhdr, mkUstarHeader_size, twoZeroBlocks_size]
    rw [show bsp = pf ++ hdr ++ twoZeroBlocks by rw [hbsp, ← hpf, mkRegularFrame_empty, ← hhdr], unpackWith_eq_unpackLoop (by rw [hsz]; omega) (by rw [hsz])]
    have hs1 := unpackLoop_mkPaxFrame_step opts ByteArray.empty (hdr ++ twoZeroBlocks) (encodePaxRecord "size" "8589934592") [] [] 0 (by decide) { size? := some 8589934592 } rfl
    simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add, ← hpf, ← ByteArray.append_assoc, show 512 + pad512 (encodePaxRecord "size" "8589934592").size = 1024 from rfl] at hs1
    rw [hs1]; exact unpackLoop_hdr_err opts pf hdr twoZeroBlocks (some { size? := some 8589934592 }) [] [] hhdr hpf_sz (by rw [twoZeroBlocks_size]) (herr := hderr)
  have hhp_err : Impl.unpackWith {} (hpHdr ++ twoZeroBlocks) = .error { kind := .resourceLimitExceeded, message := "PAX header exceeds maxPaxHeaderBytes", offset := some 0 } := by
    have hsz : (hpHdr ++ twoZeroBlocks).size = 1536 := by rw [ByteArray.size_append, hhp, mkUstarHeader_size, twoZeroBlocks_size]
    rw [unpackWith_eq_unpackLoop (by rw [hsz]; omega) (by rw [hsz])]; refine unpackLoop_step_err {} _ 0 none [] [] 0 _ (by rw [hsz]; omega) ?_
    have hs := unpackStep_mkUstarHeader {} ByteArray.empty hpHdr twoZeroBlocks none [] [] 0 hhp (by simp [maxPaxHeaderBytes, ustarOctal11Limit])
    rw [ByteArray.empty_append, ByteArray.size_empty] at hs; rw [hs]; rfl
  unfold test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced; dsimp only; rw [← hrf, ← hpzf, ← hbsp, ← hhp]
  refine allPass_err_for hu (unpackWith_single_raw_err { maxEntries := 0 } _ hdr5 post5 hrf_eq hhdr5 hpost5_sz) rfl rfl ?_
  refine allPass_err_for hu (unpackWith_single_raw_err { maxTotalBytes := 4 } _ hdr5 post5 hrf_eq hhdr5 hpost5_sz) rfl rfl ?_
  refine allPass_ok_bind_fn (congrFun hu _) (unpackWith_pax_emptyRegular_ok { maxTotalBytes := 0 } pzf _ hdr0 "a.txt" "a.txt"
    { path? := some "a.txt" } (by rw [hpzf, mkRegularFrame_empty, ← hhdr0]) hhdr0) (tarEquiv_singleton_self _) ?_
  refine allPass_err_for hu (hbig { maxTotalBytes := 1024 } fun _ => rfl) rfl rfl ?_
  refine allPass_err_for hu (hbig { maxTotalBytes := 10737418240 } fun _ => rfl) rfl rfl ?_
  dsimp only [checkUnpackError]; rw [hu, hhp_err]; exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Prove `test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced` for `defaultApi`. -/
theorem allPass_unpackWith_resourceLimitsAndLargePaxSize_enforced :
    AllPass (test_tar_unpackWith_resourceLimitsAndLargePaxSize_enforced defaultApi) := test6_for defaultApi rfl

private theorem test7_for (api : TarApi) (hu : api.unpackWith = Impl.unpackWith) (hup : api.unpack = Impl.unpackWith {}) :
    AllPass (test_tar_unpackWith_securityOnWire_enforced api) := by
  obtain ⟨h1, hh1⟩ : ∃ b, b = mkUstarHeader "../evil" 0o644 0 0 0 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  obtain ⟨h2, hh2⟩ : ∃ b, b = mkUstarHeader "/etc/passwd" 0o644 0 0 0 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  obtain ⟨h3, hh3⟩ : ∃ b, b = mkUstarHeader "escape" 0o777 0 0 0 0 0x32 "../etc/passwd" "" "" "" := ⟨_, rfl⟩
  obtain ⟨da, hda⟩ : ∃ b, b = mkUstarHeader "sub/" 0o755 0 0 0 0 0x35 "" "" "" "" := ⟨_, rfl⟩
  obtain ⟨db, hdb⟩ : ∃ b, b = mkUstarHeader "sub" 0o644 0 0 0 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ b, b = mkPaxFrame (encodePaxRecord "path" "safe.txt") ++ mkRegularFrame "safe.txt" ByteArray.empty ++ twoZeroBlocks := ⟨_, rfl⟩
  obtain ⟨hdrS, hhdrS⟩ : ∃ b, b = mkUstarHeader "safe.txt" 0o644 0 0 0 0 0x30 "" "" "" "" := ⟨_, rfl⟩
  have hdup : Impl.unpackWith {} (da ++ db ++ twoZeroBlocks) =
      .error { kind := .duplicatePath, message := "duplicate tar entry path: sub", entryPath := some "sub", offset := some 512 } := by
    have ha_sz : da.size = 512 := by rw [hda, mkUstarHeader_size]
    have hsz : (da ++ db ++ twoZeroBlocks).size = 2048 := by simp [ByteArray.size_append, ha_sz, hdb, mkUstarHeader_size, twoZeroBlocks_size]
    rw [unpackWith_eq_unpackLoop (by rw [hsz]; omega) (by rw [hsz])]
    have hs1 := unpackLoop_hdr_ok {} ByteArray.empty da ByteArray.empty (db ++ twoZeroBlocks) none [] [] 0 { path := "sub", kind := .directory, mode := 0o755 } 0 ByteArray.empty hda rfl rfl
    simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.add_zero, ← ByteArray.append_assoc] at hs1
    rw [hs1]; exact unpackLoop_hdr_err {} da db twoZeroBlocks none ["sub"] [{ path := "sub", kind := .directory, mode := 0o755 }] hdb ha_sz (by rw [twoZeroBlocks_size])
  unfold test_tar_unpackWith_securityOnWire_enforced; dsimp only; rw [← hh1, ← hh2, ← hh3, ← hda, ← hdb, ← hsp, hup]
  refine allPass_err_for hu (unpackWith_single_raw_err {} _ h1 twoZeroBlocks rfl hh1 twoZeroBlocks_size) rfl rfl ?_
  refine allPass_err_for hu (unpackWith_single_raw_err {} _ h2 twoZeroBlocks rfl hh2 twoZeroBlocks_size) rfl rfl ?_
  refine allPass_err_for hu (unpackWith_single_raw_err {} _ h3 twoZeroBlocks rfl hh3 twoZeroBlocks_size) rfl rfl ?_
  refine allPass_err_for hu hdup rfl rfl ?_
  exact allPass_ok_last_impl (unpackWith_pax_emptyRegular_ok {} sp _ hdrS "safe.txt" "safe.txt"
    { path? := some "safe.txt" } (by rw [hsp, mkRegularFrame_empty, ← hhdrS]) hhdrS) (tarEquiv_singleton_self _)

/-- Prove `test_tar_unpackWith_securityOnWire_enforced` for `defaultApi`. -/
theorem allPass_unpackWith_securityOnWire_enforced :
    AllPass (test_tar_unpackWith_securityOnWire_enforced defaultApi) := test7_for defaultApi rfl rfl

end LeanSwe.Tar.Proofs
