import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.Headers
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.PaxRoundTrip

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem mode_mask_idemp (m : UInt32) :
    (((m &&& 0o7777).toNat &&& 0o7777).toUInt32 &&& 0o7777) = (m &&& 0o7777) := by
  have h1 : (m &&& 0o7777).toNat = m.toNat &&& 4095 := rfl
  have hlt : m.toNat &&& 4095 < 2 ^ 12 := Nat.and_lt_two_pow m.toNat (by decide)
  have hlt32 : m.toNat &&& 4095 < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  have h2 : (((m &&& 0o7777).toNat &&& 0o7777).toUInt32 &&& 0o7777).toNat =
      (((m.toNat &&& 4095) &&& 4095) % 2 ^ 32) &&& 4095 := rfl
  rw [h2, ← h1, h1, Nat.and_assoc, Nat.and_self, Nat.mod_eq_of_lt hlt32, Nat.and_assoc, Nat.and_self]

private theorem ustarPathSplit_ok (wp : String) (hfit : pathFitsUstar wp = true) (hnul : !hasNulString wp = true) :
    let pair := if wp.toUTF8.size ≤ 100 then ("", wp) else match findUstarSplit wp with | some p => p | none => ("", wp)
    pair.2.toUTF8.size ≤ 100 ∧
    pair.1.toUTF8.size ≤ 155 ∧
    !hasNulString pair.2 = true ∧
    !hasNulString pair.1 = true ∧
    (if pair.1.isEmpty then pair.2 else pair.1 ++ "/" ++ pair.2) = wp := by
  by_cases h100 : wp.toUTF8.size ≤ 100
  · simp only [h100, ↓reduceIte]
    have hemp : "".isEmpty = true := rfl
    have hnul_e : !hasNulString "" = true := by decide
    have hsz_e : "".toUTF8.size ≤ 155 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]
      decide
    exact ⟨trivial, hsz_e, hnul, hnul_e, by simp [hemp]⟩
  · simp only [h100, ↓reduceIte]
    unfold pathFitsUstar at hfit
    rw [Bool.and_eq_true] at hfit
    have hsome : (findUstarSplit wp).isSome = true := by
      rcases Bool.or_eq_true_iff.mp hfit.2 with hle | hsome
      · exact absurd (decide_eq_true_eq.mp hle) h100
      · exact hsome
    cases hf : findUstarSplit wp with
    | none => rw [hf] at hsome; cases hsome
    | some pair =>
      rcases pair with ⟨pfx, nm⟩
      have ⟨hjoin, hpfx_ne, hnm_ne, hpfx_sz, hnm_sz⟩ := findUstarSplit_spec hf
      have hjoin_nul := not_hasNulString_append (a := pfx) (b := "/" ++ nm)
      have hnul_wp' : (!hasNulString wp) = true := by cases hc : hasNulString wp <;> simp_all
      have hnul_all : (!hasNulString (pfx ++ ("/" ++ nm))) = true := by
        rw [← String.append_assoc, hjoin]
        exact hnul_wp'
      rw [hjoin_nul, Bool.and_eq_true] at hnul_all
      have hnul_s := not_hasNulString_append (a := "/") (b := nm)
      rw [hnul_s, Bool.and_eq_true] at hnul_all
      have hnul_nm : !hasNulString nm = true := by
        have h2 := hnul_all.2.2
        cases hc : hasNulString nm <;> simp [hc] at h2 ⊢
      have hnul_pfx : !hasNulString pfx = true := by
        have h1 := hnul_all.1
        cases hc : hasNulString pfx <;> simp [hc] at h1 ⊢
      have hpfx_e : pfx.isEmpty = false := by cases hc : pfx.isEmpty <;> simp_all
      exact ⟨hnm_sz, hpfx_sz, hnul_nm, hnul_pfx, by simp [hpfx_e, hjoin]⟩

/-- Single-entry round-trip step for `unpackLoop` over `encodeEntryBlocks`. -/
theorem unpackLoop_encodeEntryBlocks_step (opts : UnpackOptions)
    (pre post : ByteArray) (e : TarEntry) (normPath : String)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hve : validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true)
    (hnorm : normPath = normalizeTarPath e.kind e.path)
    (hpax_lim : fitsPaxLimit e = true)
    (hnot_seen : !seen.contains normPath = true)
    (hle_e : acc.length + 1 ≤ opts.maxEntries)
    (hle_b : totalBytes + e.data.size ≤ opts.maxTotalBytes)
    (hpost_sz : post.size ≥ 512) :
    ∃ entry' : TarEntry,
      entryEquivBool e entry' = true ∧
      entry'.path = normPath ∧
      entry'.data.size = e.data.size ∧
      let bytes := pre ++ (encodeEntryBlocks e normPath ++ post)
      unpackLoop opts bytes pre.size none seen acc totalBytes =
        unpackLoop opts bytes (pre.size + (encodeEntryBlocks e normPath).size)
          none (normPath :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
  unfold validEntryBool at hve
  cases hv : validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path with
  | error _ => rw [hv] at hve; cases hve
  | ok np =>
    rw [hv] at hve
    dsimp only at hve
    have hnp_eq : np = normalizeTarPath e.kind e.path := validateEntryPath_normPath hv
    have hnp : np = normPath := hnp_eq.trans hnorm.symm
    subst hnp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hve
    rcases hve with ⟨⟨hsym_ok, hdata_ok⟩, ⟨⟨⟨⟨⟨hnul_u, hnul_g⟩, huid⟩, hgid⟩, hmtime⟩, hsz⟩⟩
    have ⟨hv_wp, hnul_wp⟩ := validateEntryPath_wirePathOf hv
    have hnot_nul_e : !hasNulString e.linkTarget = true := by
      cases hk : e.kind <;> simp only [hk] at hsym_ok
      · rw [beq_iff_eq.mp hsym_ok]; decide
      · rw [beq_iff_eq.mp hsym_ok]; decide
      · cases hvs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal np e.linkTarget with
        | error _ => rw [hvs] at hsym_ok; cases hsym_ok
        | ok _ =>
          unfold validateSymlinkTarget at hvs
          dsimp only at hvs
          split at hvs
          · cases hvs
          · split at hvs
            · cases hvs
            · rename_i _ hnn
              cases hc : hasNulString e.linkTarget
              · rfl
              · exfalso; exact hnn hc
    let wp := wirePathOf e.kind np
    let typeByte : UInt8 := match e.kind with | .regular => 0x30 | .directory => 0x35 | .symlink => 0x32
    have htype_ne : typeByte ≠ 0x78 := by dsimp only [typeByte]; cases e.kind <;> decide
    have htype_beq : (typeByte == 0x78) = false := Bool.eq_false_iff.mpr (by simpa [beq_iff_eq] using htype_ne)
    have hlink_empty_of_non_sym : e.kind ≠ .symlink → e.linkTarget = "" := by
      intro hne
      cases hk : e.kind <;> simp only [hk] at hsym_ok hne
      · exact beq_iff_eq.mp hsym_ok
      · exact beq_iff_eq.mp hsym_ok
      · exact absurd rfl hne
    have decode_ustar_entry :
        ∀ (bytes hdrBlock : ByteArray) (off : Nat) (pendingPax : Option PaxOverrides)
          (fbName fbPrefix fbLink fbUname fbGname : String)
          (fbUid fbGid fbSize fbMtime : Nat)
          (hbytes : bytes.extract off (off + 512 + pad512 e.data.size) = hdrBlock ++ padBlock512 e.data)
          (hhdr : hdrBlock = buildUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix)
          (hbd_off : off + 512 + pad512 e.data.size ≤ bytes.size)
          (hfuid : fbUid < ustarOctal7Limit) (hfgid : fbGid < ustarOctal7Limit)
          (hfsize : fbSize < ustarOctal11Limit) (hfmtime : fbMtime < ustarOctal11Limit)
          (heff_size : (pendingPax.getD {}).size?.getD fbSize = e.data.size)
          (heff_uid : (pendingPax.getD {}).uid?.getD fbUid = e.uid)
          (heff_gid : (pendingPax.getD {}).gid?.getD fbGid = e.gid)
          (heff_mtime : (pendingPax.getD {}).mtime?.getD fbMtime = e.mtime)
          (heff_path : (pendingPax.getD {}).path? = some wp ∨
            ((pendingPax.getD {}).path? = none ∧ fbName.toUTF8.size ≤ 100 ∧ fbPrefix.toUTF8.size ≤ 155 ∧
              !hasNulString fbName = true ∧ !hasNulString fbPrefix = true ∧
              (if fbPrefix.isEmpty then fbName else fbPrefix ++ "/" ++ fbName) = wp))
          (heff_link : e.kind = .symlink → (pendingPax.getD {}).linkpath? = some e.linkTarget ∨
            ((pendingPax.getD {}).linkpath? = none ∧ fbLink = e.linkTarget ∧ e.linkTarget.toUTF8.size ≤ 100))
          (heff_uname : (pendingPax.getD {}).uname? = some e.uname ∨
            ((pendingPax.getD {}).uname? = none ∧ fbUname = e.uname ∧ e.uname.toUTF8.size ≤ 32))
          (heff_gname : (pendingPax.getD {}).gname? = some e.gname ∨
            ((pendingPax.getD {}).gname? = none ∧ fbGname = e.gname ∧ e.gname.toUTF8.size ≤ 32)),
          let entry' : TarEntry :=
            { path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
            , uid := e.uid, gid := e.gid, mtime := e.mtime
            , uname := e.uname, gname := e.gname
            , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
            , linkTarget := if e.kind == .symlink then e.linkTarget else "" }
          entryEquivBool e entry' = true ∧
          entry'.data.size = e.data.size ∧
          unpackLoop opts bytes off pendingPax seen acc totalBytes =
            unpackLoop opts bytes (off + 512 + pad512 e.data.size) none (np :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
      intro bytes hdrBlock off pendingPax fbName fbPrefix fbLink fbUname fbGname
        fbUid fbGid fbSize fbMtime hbytes hhdr hbd_off hfuid hfgid hfsize hfmtime
        heff_size heff_uid heff_gid heff_mtime heff_path heff_link heff_uname heff_gname
      have hhdr_sz : hdrBlock.size = 512 := by rw [hhdr]; exact buildUstarHeader_size ..
      have hext_hdr : bytes.extract off (off + 512) =
          buildUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix := by
        have hsub : bytes.extract off (off + 512) =
            (bytes.extract off (off + 512 + pad512 e.data.size)).extract 0 512 := by
          rw [ByteArray.extract_extract]; congr 1; omega
        rw [hsub, hbytes, ← hhdr_sz]
        exact (extract_append_exact_left hdrBlock (padBlock512 e.data)).trans hhdr
      have hnot_ge : ¬(off ≥ bytes.size) := by omega
      have hnz : isZeroRange bytes off 512 = false := isZeroRange_buildUstarHeader_false (by omega) hext_hdr
      have hnot_gt : ¬(off + 512 > bytes.size) := by omega
      have hparse : parseUstarHeader bytes off = .ok
          { mode := (e.mode &&& 0o7777).toNat, uid := fbUid, gid := fbGid, size := fbSize, mtime := fbMtime, typeflag := typeByte } :=
        parseUstarHeader_buildUstarHeader hfuid hfgid hfsize hfmtime (by omega) hext_hdr
      have ⟨hext_nm, hext_lk, hext_un, hext_gn, hext_pfx⟩ := buildUstarHeader_extract_strings hext_hdr
      have hkind_eq : (if typeByte == 0x30 || typeByte == 0x00 then some EntryKind.regular
          else if typeByte == 0x35 then some .directory
          else if typeByte == 0x32 then some .symlink
          else none) = some e.kind := by
        have hk_fn : ∀ k : EntryKind, (let tb : UInt8 := match k with | .regular => 0x30 | .directory => 0x35 | .symlink => 0x32
            if tb == 0x30 || tb == 0x00 then some EntryKind.regular
            else if tb == 0x35 then some .directory
            else if tb == 0x32 then some .symlink
            else none) = some k := fun k => by cases k <;> rfl
        exact hk_fn e.kind
      have hnonreg_f : (e.kind != .regular && e.data.size != 0) = false := by
        cases hk : e.kind with
        | regular => rfl
        | directory => simp only [hk] at hdata_ok ⊢; simp [bne, hdata_ok]
        | symlink => simp only [hk] at hdata_ok ⊢; simp [bne, hdata_ok]
      have hnot_maxe : ¬(acc.length + 1 > opts.maxEntries) := by omega
      have hnot_maxb : ¬(totalBytes + e.data.size > opts.maxTotalBytes) := by omega
      have hnot_trunc : ¬(off + 512 + pad512 e.data.size > bytes.size) := by omega
      have hseen_f : seen.contains np = false := by
        cases hc : seen.contains np <;> simp_all
      have huname_ok : (match (pendingPax.getD {}).uname? with
          | some u => Except.ok u
          | none => decodeCStringUtf8 bytes (off + 265) (off + 297) off "uname") = .ok e.uname := by
        rcases heff_uname with hu | ⟨hu, hfb_u, hsz_u⟩
        · rw [hu]
        · have hnul_fb : !hasNulString fbUname = true := by rw [hfb_u]; exact hnul_u
          have hsz_fb : fbUname.toUTF8.size ≤ 32 := by rw [hfb_u]; exact hsz_u
          have hdec_un : decodeCStringUtf8 bytes (off + 265) (off + 297) off "uname" = .ok e.uname := by
            rw [(by omega : off + 297 = (off + 265) + 32)]
            have h0 : decodeCStringUtf8 bytes (off + 265) ((off + 265) + 32) off "uname" = .ok fbUname :=
              decodeCStringUtf8_padRightBytes hnul_fb hsz_fb (by omega) hext_un
            rwa [hfb_u] at h0
          rw [hu, hdec_un]
      have hgname_ok : (match (pendingPax.getD {}).gname? with
          | some g => Except.ok g
          | none => decodeCStringUtf8 bytes (off + 297) (off + 329) off "gname") = .ok e.gname := by
        rcases heff_gname with hg | ⟨hg, hfb_g, hsz_g⟩
        · rw [hg]
        · have hnul_fb : !hasNulString fbGname = true := by rw [hfb_g]; exact hnul_g
          have hsz_fb : fbGname.toUTF8.size ≤ 32 := by rw [hfb_g]; exact hsz_g
          have hdec_gn : decodeCStringUtf8 bytes (off + 297) (off + 329) off "gname" = .ok e.gname := by
            rw [(by omega : off + 329 = (off + 297) + 32)]
            have h0 : decodeCStringUtf8 bytes (off + 297) ((off + 297) + 32) off "gname" = .ok fbGname :=
              decodeCStringUtf8_padRightBytes hnul_fb hsz_fb (by omega) hext_gn
            rwa [hfb_g] at h0
          rw [hg, hdec_gn]
      have hlink_ok : (match e.kind with
          | .symlink =>
            match (pendingPax.getD {}).linkpath? with
            | some p => Except.ok p
            | none => decodeCStringUtf8 bytes (off + 157) (off + 257) off "linkname"
          | .regular => Except.ok ""
          | .directory => Except.ok "") = .ok (if e.kind == .symlink then e.linkTarget else "") := by
        cases hk : e.kind
        · rfl
        · rfl
        · rcases heff_link hk with hl | ⟨hl, hfb_l, hsz_l⟩
          · rw [hl]; rfl
          · have hnul_fb : !hasNulString fbLink = true := by rw [hfb_l]; exact hnot_nul_e
            have hsz_fb : fbLink.toUTF8.size ≤ 100 := by rw [hfb_l]; exact hsz_l
            have hdec_lk : decodeCStringUtf8 bytes (off + 157) (off + 257) off "linkname" = .ok e.linkTarget := by
              rw [(by omega : off + 257 = (off + 157) + 100)]
              have h0 : decodeCStringUtf8 bytes (off + 157) ((off + 157) + 100) off "linkname" = .ok fbLink :=
                decodeCStringUtf8_padRightBytes hnul_fb hsz_fb (by omega) hext_lk
              rwa [hfb_l] at h0
            rw [hl, hdec_lk]; rfl
      have hdec_step : decodeTarEntry opts bytes off
          { mode := (e.mode &&& 0o7777).toNat, uid := fbUid, gid := fbGid, size := fbSize, mtime := fbMtime, typeflag := typeByte }
          pendingPax seen acc.length totalBytes =
          .ok ({ path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
               , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
               , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
               , linkTarget := if e.kind == .symlink then e.linkTarget else "" }, pad512 e.data.size) := by
        unfold decodeTarEntry
        dsimp only
        rw [hkind_eq]
        dsimp only
        simp only [heff_size, hnonreg_f, Bool.false_eq_true, ↓reduceIte, hnot_maxe, hnot_maxb, hnot_trunc]
        have hdec_tail : ∀ (unameRes gnameRes : Except TarError String) (linkRes : Except TarError String),
            unameRes = .ok e.uname → gnameRes = .ok e.gname →
            linkRes = .ok (if e.kind == .symlink then e.linkTarget else "") →
            ((match (@Except.ok TarError String wp), linkRes, unameRes, gnameRes with
            | Except.error e, _, _, _ | _, Except.error e, _, _ | _, _, Except.error e, _ | _, _, _, Except.error e =>
              Except.error e
            | Except.ok rawPath, Except.ok rawLink, Except.ok uname, Except.ok gname =>
              match validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind rawPath with
              | Except.error err => Except.error { err with offset := some off }
              | Except.ok normPath =>
                match (match e.kind with
                  | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath rawLink
                  | .regular | .directory => (@Except.ok TarError Unit ())) with
                | Except.error err => Except.error { err with offset := some off }
                | Except.ok () =>
                  if seen.contains normPath then
                    Except.error ({ kind := TarErrorKind.duplicatePath
                                  , message := s!"duplicate tar entry path: {normPath}"
                                  , entryPath := some normPath, offset := some off } : TarError)
                  else
                    Except.ok ({ path := normPath, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
                               , uid := (pendingPax.getD {}).uid?.getD fbUid, gid := (pendingPax.getD {}).gid?.getD fbGid
                               , mtime := (pendingPax.getD {}).mtime?.getD fbMtime, uname := uname, gname := gname
                               , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
                               , linkTarget := rawLink }, pad512 e.data.size)) : Except TarError (TarEntry × Nat)) =
            .ok ({ path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
                 , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
                 , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
                 , linkTarget := if e.kind == .symlink then e.linkTarget else "" }, pad512 e.data.size) := by
          intro unameRes gnameRes linkRes hu hg hl
          rw [hu, hg, hl]
          dsimp only
          rw [hv_wp]
          dsimp only
          cases hk : e.kind <;> simp only [hk] at hsym_ok ⊢
          · simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]
          · simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]
          · have h_sym_beq : (EntryKind.symlink == EntryKind.symlink) = true := rfl
            rw [h_sym_beq]; simp only [↓reduceIte]
            cases hvs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal np e.linkTarget with
            | error err => simp [hvs] at hsym_ok
            | ok _ => simp only [hseen_f, Bool.false_eq_true, ↓reduceIte, heff_uid, heff_gid, heff_mtime]
        rcases heff_path with hp | ⟨hp, hnm_sz, hpfx_sz, hnm_nul, hpfx_nul, hjoin⟩
        · rw [hp]; dsimp only
          exact hdec_tail _ _ _ huname_ok hgname_ok hlink_ok
        · have hdec_nm : decodeCStringUtf8 bytes off (off + 100) off "name" = .ok fbName :=
            decodeCStringUtf8_padRightBytes hnm_nul hnm_sz (by omega) hext_nm
          have hdec_pfx : decodeCStringUtf8 bytes (off + 345) (off + 500) off "prefix" = .ok fbPrefix := by
            have heq500 : off + 500 = (off + 345) + 155 := by omega
            rw [heq500]
            exact decodeCStringUtf8_padRightBytes hpfx_nul hpfx_sz (by omega) hext_pfx
          rw [hp, hdec_nm, hdec_pfx]; dsimp only; rw [hjoin]
          exact hdec_tail _ _ _ huname_ok hgname_ok hlink_ok
      have hdata_extract : (if e.data.size == 0 then ByteArray.empty
          else bytes.extract (off + 512) (off + 512 + e.data.size)) = e.data := by
        by_cases hz : e.data.size = 0
        · simp only [hz, beq_self_eq_true, ↓reduceIte]
          have : e.data.data = #[] := Array.eq_empty_of_size_eq_zero hz
          exact ByteArray.ext this.symm
        · have hbeq : (e.data.size == 0) = false := Bool.eq_false_iff.mpr (by simpa using hz)
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
          have hpad_le := le_pad512 e.data.size
          have hsub : bytes.extract (off + 512) (off + 512 + e.data.size) =
              (bytes.extract off (off + 512 + pad512 e.data.size)).extract 512 (512 + e.data.size) := by
            rw [ByteArray.extract_extract]; congr 1; omega
          rw [hsub, hbytes, ← hhdr_sz, extract_append_right hdrBlock (padBlock512 e.data) e.data.size,
            padBlock512_extract_prefix e.data]
      have ⟨_, hnorm_id, _⟩ := validateEntryPath_idemp hv
      have heqv : entryEquivBool e
          { path := np, kind := e.kind, mode := ((e.mode &&& 0o7777).toNat &&& 0o7777).toUInt32
          , uid := e.uid, gid := e.gid, mtime := e.mtime, uname := e.uname, gname := e.gname
          , data := if e.data.size == 0 then ByteArray.empty else bytes.extract (off + 512) (off + 512 + e.data.size)
          , linkTarget := if e.kind == .symlink then e.linkTarget else "" } = true := by
        unfold entryEquivBool
        dsimp only
        rw [hnorm_id, ← hnp_eq, hdata_extract, mode_mask_idemp]
        have hl : ((if e.kind == .symlink then e.linkTarget else "") ==
            (if e.kind == .symlink then (if e.kind == .symlink then e.linkTarget else "") else "")) = true := by
          cases e.kind
          · rfl
          · rfl
          · change (e.linkTarget == e.linkTarget) = true; exact beq_self_eq_true _
        have hkeq : (e.kind == e.kind) = true := by cases e.kind <;> rfl
        simp [hl, hkeq]
      have hdata_sz' : (if e.data.size == 0 then ByteArray.empty
          else bytes.extract (off + 512) (off + 512 + e.data.size)).size = e.data.size := by
        rw [hdata_extract]
      refine ⟨heqv, hdata_sz', ?_⟩
      rw [unpackLoop.eq_1]
      simp only [hnot_ge, ↓reduceIte]
      unfold unpackStep
      simp only [hnot_ge, ↓reduceIte, hnz, Bool.false_eq_true, hnot_gt, hparse, htype_beq, hdec_step,
        hdata_sz']
      have hgt : off + 512 + pad512 e.data.size > off := by omega
      simp [hgt]
    by_cases hneed : needsPax e wp
    · have hpax_lim' : (buildPaxPayload e wp).size ≤ maxPaxHeaderBytes := by
        unfold fitsPaxLimit at hpax_lim
        dsimp only at hpax_lim
        rw [← hnp_eq] at hpax_lim
        simp [wp, hneed] at hpax_lim
        exact hpax_lim
      let fbPair := if !pathFitsUstar wp then ("", asciiFallback wp 100)
        else if wp.toUTF8.size ≤ 100 then ("", wp)
        else match findUstarSplit wp with | some pair => pair | none => ("", asciiFallback wp 100)
      let fbLink := if e.kind == .symlink then asciiFallback e.linkTarget 100 else ""
      let fbUname := asciiFallback e.uname 32
      let fbGname := asciiFallback e.gname 32
      let fbUid := if e.uid < ustarOctal7Limit then e.uid else 0
      let fbGid := if e.gid < ustarOctal7Limit then e.gid else 0
      let fbSize := if e.data.size < ustarOctal11Limit then e.data.size else 0
      let fbMtime := if e.mtime < ustarOctal11Limit then e.mtime else 0
      have hpax_step : ∀ (paxPayload paxHdr hdr : ByteArray),
          paxPayload = buildPaxPayload e wp →
          paxHdr = buildUstarHeader "././@PaxHeader" (0o644 : UInt32) 0 0 paxPayload.size 0 0x78 "" "" "" "" →
          hdr = buildUstarHeader fbPair.2 e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPair.1 →
          ∃ entry' : TarEntry,
            entryEquivBool e entry' = true ∧
            entry'.path = np ∧
            entry'.data.size = e.data.size ∧
            let bytes := pre ++ (encodeEntryBlocks e np ++ post)
            unpackLoop opts bytes pre.size none seen acc totalBytes =
              unpackLoop opts bytes (pre.size + (encodeEntryBlocks e np).size)
                none (np :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
        intro paxPayload paxHdr hdr hpaxPayload_eq hpaxHdr_eq hhdr_eq
        have henc : encodeEntryBlocks e np = paxHdr ++ padBlock512 paxPayload ++ hdr ++ padBlock512 e.data := by
          have hneed' : needsPax e (wirePathOf e.kind np) = true := hneed
          unfold encodeEntryBlocks
          dsimp only
          simp only [hneed', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          dsimp only [wp] at hpaxPayload_eq hpaxHdr_eq hhdr_eq
          rw [← hpaxPayload_eq, ← hpaxHdr_eq]
          exact congrArg (fun x => paxHdr ++ padBlock512 paxPayload ++ x ++ padBlock512 e.data) hhdr_eq.symm
        have hpaxHdr_sz : paxHdr.size = 512 := by rw [hpaxHdr_eq]; exact buildUstarHeader_size ..
        have hhdr_sz : hdr.size = 512 := by rw [hhdr_eq]; exact buildUstarHeader_size ..
        have hpadPax_sz : (padBlock512 paxPayload).size = pad512 paxPayload.size := padBlock512_size _
        have hpadData_sz : (padBlock512 e.data).size = pad512 e.data.size := padBlock512_size _
        have henc_sz : (encodeEntryBlocks e np).size = (512 + pad512 paxPayload.size) + (512 + pad512 e.data.size) := by
          rw [henc]
          simp only [ByteArray.size_append, hpaxHdr_sz, hpadPax_sz, hhdr_sz, hpadData_sz]
          omega
        let bytes := pre ++ (encodeEntryBlocks e np ++ post)
        have hbytes_sz : bytes.size = pre.size + (encodeEntryBlocks e np).size + post.size := by
          simp only [bytes, ByteArray.size_append, Nat.add_assoc]
        have hext_paxHdr : bytes.extract pre.size (pre.size + 512) = paxHdr := by
          have hsplit : encodeEntryBlocks e np ++ post =
              paxHdr ++ (padBlock512 paxPayload ++ hdr ++ padBlock512 e.data ++ post) := by
            rw [henc]; simp only [ByteArray.append_assoc]
          dsimp only [bytes]
          rw [hsplit, ← ByteArray.append_assoc, ← hpaxHdr_sz]
          exact extract_append_mid pre paxHdr _
        have hnot_ge0 : ¬(pre.size ≥ bytes.size) := by omega
        have hnz0 : isZeroRange bytes pre.size 512 = false :=
          isZeroRange_buildUstarHeader_false (by omega) (hext_paxHdr.trans hpaxHdr_eq)
        have hnot_gt0 : ¬(pre.size + 512 > bytes.size) := by omega
        have hpax_lim'' : paxPayload.size ≤ maxPaxHeaderBytes := by rw [hpaxPayload_eq]; exact hpax_lim'
        have hpax_o11 : paxPayload.size < ustarOctal11Limit := by
          have h : maxPaxHeaderBytes < ustarOctal11Limit := by decide
          omega
        have h0_o7 : 0 < ustarOctal7Limit := by decide
        have h0_o11 : 0 < ustarOctal11Limit := by decide
        have hparse0 : parseUstarHeader bytes pre.size = .ok
            { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := paxPayload.size, mtime := 0, typeflag := 0x78 } :=
          parseUstarHeader_buildUstarHeader h0_o7 h0_o7 hpax_o11 h0_o11 (by omega) (hext_paxHdr.trans hpaxHdr_eq)
        have hnot_maxPax : ¬(paxPayload.size > maxPaxHeaderBytes) := by omega
        have hnot_truncPax : ¬(pre.size + 512 + pad512 paxPayload.size > bytes.size) := by omega
        have hext_paxPayload : bytes.extract (pre.size + 512) (pre.size + 512 + paxPayload.size) = paxPayload := by
          have hsplit : encodeEntryBlocks e np ++ post =
              (paxHdr ++ padBlock512 paxPayload) ++ (hdr ++ padBlock512 e.data ++ post) := by
            rw [henc]; simp only [ByteArray.append_assoc]
          have hsub : bytes.extract (pre.size + 512) (pre.size + 512 + paxPayload.size) =
              (bytes.extract (pre.size + 512) (pre.size + 512 + (padBlock512 paxPayload).size)).extract 0 paxPayload.size := by
            rw [ByteArray.extract_extract, hpadPax_sz]
            have hle := le_pad512 paxPayload.size
            congr 1; omega
          have hpre_hdr_sz : (pre ++ paxHdr).size = pre.size + 512 := by
            rw [ByteArray.size_append, hpaxHdr_sz]
          have hbytes_eq : bytes = pre ++ paxHdr ++ padBlock512 paxPayload ++ (hdr ++ padBlock512 e.data ++ post) := by
            dsimp only [bytes]; rw [hsplit]; simp only [ByteArray.append_assoc]
          rw [hsub, hbytes_eq, ← hpre_hdr_sz]
          rw [extract_append_mid (pre ++ paxHdr) (padBlock512 paxPayload) (hdr ++ padBlock512 e.data ++ post),
            padBlock512_extract_prefix paxPayload]
        have hparsePax : parsePaxPayload paxPayload pre.size = .ok
            { path? := if !pathFitsUstar wp then some wp else none
            , linkpath? := if e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) then some e.linkTarget else none
            , uname? := if !isAsciiString e.uname || e.uname.toUTF8.size > 32 then some e.uname else none
            , gname? := if !isAsciiString e.gname || e.gname.toUTF8.size > 32 then some e.gname else none
            , size? := if e.data.size ≥ ustarOctal11Limit then some e.data.size else none
            , mtime? := if e.mtime ≥ ustarOctal11Limit then some e.mtime else none
            , uid? := if e.uid ≥ ustarOctal7Limit then some e.uid else none
            , gid? := if e.gid ≥ ustarOctal7Limit then some e.gid else none } := by
          rw [hpaxPayload_eq]
          exact buildPaxPayload_parse e wp pre.size hnul_u hnul_g huid hgid hsz hmtime hpax_lim'
        let paxOv : PaxOverrides :=
          { path? := if !pathFitsUstar wp then some wp else none
          , linkpath? := if e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) then some e.linkTarget else none
          , uname? := if !isAsciiString e.uname || e.uname.toUTF8.size > 32 then some e.uname else none
          , gname? := if !isAsciiString e.gname || e.gname.toUTF8.size > 32 then some e.gname else none
          , size? := if e.data.size ≥ ustarOctal11Limit then some e.data.size else none
          , mtime? := if e.mtime ≥ ustarOctal11Limit then some e.mtime else none
          , uid? := if e.uid ≥ ustarOctal7Limit then some e.uid else none
          , gid? := if e.gid ≥ ustarOctal7Limit then some e.gid else none }
        have hstep0 : unpackLoop opts bytes pre.size none seen acc totalBytes =
            unpackLoop opts bytes (pre.size + 512 + pad512 paxPayload.size) (some paxOv) seen acc totalBytes := by
          rw [unpackLoop.eq_1]
          simp only [hnot_ge0, ↓reduceIte]
          unfold unpackStep
          simp only [hnot_ge0, ↓reduceIte, hnz0, Bool.false_eq_true, hnot_gt0, hparse0, beq_self_eq_true,
            Option.isSome_none, hnot_maxPax, hnot_truncPax, hext_paxPayload, hparsePax]
          have hgt0 : pre.size + 512 + pad512 paxPayload.size > pre.size := by omega
          simp only [hgt0, ↓reduceIte]
          rfl
        let off1 := pre.size + 512 + pad512 paxPayload.size
        have hext1 : bytes.extract off1 (off1 + 512 + pad512 e.data.size) = hdr ++ padBlock512 e.data := by
          have hpre1 : (pre ++ (paxHdr ++ padBlock512 paxPayload)).size = off1 := by
            simp only [off1, ByteArray.size_append, hpaxHdr_sz, hpadPax_sz, Nat.add_assoc]
          have hmid_sz : (hdr ++ padBlock512 e.data).size = 512 + pad512 e.data.size := by
            rw [ByteArray.size_append, hhdr_sz, hpadData_sz]
          have hbytes_eq : bytes = (pre ++ (paxHdr ++ padBlock512 paxPayload)) ++ (hdr ++ padBlock512 e.data) ++ post := by
            dsimp only [bytes]; rw [henc]; simp only [ByteArray.append_assoc]
          rw [hbytes_eq, Nat.add_assoc off1 512 (pad512 e.data.size), ← hpre1, ← hmid_sz]
          exact extract_append_mid (pre ++ (paxHdr ++ padBlock512 paxPayload)) (hdr ++ padBlock512 e.data) post
        have hfuid : fbUid < ustarOctal7Limit := by dsimp [fbUid]; split <;> first | assumption | exact h0_o7
        have hfgid : fbGid < ustarOctal7Limit := by dsimp [fbGid]; split <;> first | assumption | exact h0_o7
        have hfsize : fbSize < ustarOctal11Limit := by dsimp [fbSize]; split <;> first | assumption | exact h0_o11
        have hfmtime : fbMtime < ustarOctal11Limit := by dsimp [fbMtime]; split <;> first | assumption | exact h0_o11
        have heff_size : (some paxOv |>.getD {}).size?.getD fbSize = e.data.size := by
          dsimp [paxOv, fbSize]; by_cases h : e.data.size ≥ ustarOctal11Limit <;> simp [h]
        have heff_uid : (some paxOv |>.getD {}).uid?.getD fbUid = e.uid := by
          dsimp [paxOv, fbUid]; by_cases h : e.uid ≥ ustarOctal7Limit <;> simp [h]
        have heff_gid : (some paxOv |>.getD {}).gid?.getD fbGid = e.gid := by
          dsimp [paxOv, fbGid]; by_cases h : e.gid ≥ ustarOctal7Limit <;> simp [h]
        have heff_mtime : (some paxOv |>.getD {}).mtime?.getD fbMtime = e.mtime := by
          dsimp [paxOv, fbMtime]; by_cases h : e.mtime ≥ ustarOctal11Limit <;> simp [h]
        have heff_path : (some paxOv |>.getD {}).path? = some wp ∨
            ((some paxOv |>.getD {}).path? = none ∧ fbPair.2.toUTF8.size ≤ 100 ∧ fbPair.1.toUTF8.size ≤ 155 ∧
              !hasNulString fbPair.2 = true ∧ !hasNulString fbPair.1 = true ∧
              (if fbPair.1.isEmpty then fbPair.2 else fbPair.1 ++ "/" ++ fbPair.2) = wp) := by
          cases hp : !pathFitsUstar wp with
          | true =>
            left
            dsimp [paxOv]
            simp [hp]
          | false =>
            right
            have hfit : pathFitsUstar wp = true := by simpa using hp
            have hsplit := ustarPathSplit_ok wp hfit hnul_wp
            have hpair : fbPair = (if wp.toUTF8.size ≤ 100 then ("", wp)
                else match findUstarSplit wp with | some p => p | none => ("", asciiFallback wp 100)) := by
              dsimp only [fbPair]
              simp only [hp, Bool.false_eq_true, ↓reduceIte]
            refine ⟨by dsimp [paxOv]; simp [hp], ?_⟩
            by_cases h100 : wp.toUTF8.size ≤ 100
            · dsimp only at hsplit
              simp only [h100, ↓reduceIte] at hsplit
              rw [hpair]
              simp only [h100, ↓reduceIte]
              exact hsplit
            · have hsome : (findUstarSplit wp).isSome = true := by
                have hfit' := hfit
                unfold pathFitsUstar at hfit'
                rw [Bool.and_eq_true] at hfit'
                rcases Bool.or_eq_true_iff.mp hfit'.2 with hle | hs
                · exact absurd (decide_eq_true_eq.mp hle) h100
                · exact hs
              cases hf : findUstarSplit wp with
              | none => rw [hf] at hsome; cases hsome
              | some p =>
                dsimp only at hsplit
                simp only [h100, ↓reduceIte, hf] at hsplit
                rw [hpair]
                simp only [h100, ↓reduceIte, hf]
                exact hsplit
        have heff_link : e.kind = .symlink → (some paxOv |>.getD {}).linkpath? = some e.linkTarget ∨
            ((some paxOv |>.getD {}).linkpath? = none ∧ fbLink = e.linkTarget ∧ e.linkTarget.toUTF8.size ≤ 100) := by
          intro hk
          cases hl : (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) with
          | true =>
            left
            dsimp only [paxOv]
            rw [hk, hl]
            rfl
          | false =>
            right
            have hl' := hl
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt] at hl'
            refine ⟨by dsimp only [paxOv]; rw [hk, hl]; rfl, ?_, hl'.2⟩
            dsimp only [fbLink]
            rw [hk]
            change asciiFallback e.linkTarget 100 = e.linkTarget
            exact isAsciiString_asciiFallback_eq hl'.1 hl'.2
        have heff_uname : (some paxOv |>.getD {}).uname? = some e.uname ∨
            ((some paxOv |>.getD {}).uname? = none ∧ fbUname = e.uname ∧ e.uname.toUTF8.size ≤ 32) := by
          cases hu : (!isAsciiString e.uname || e.uname.toUTF8.size > 32) with
          | true =>
            left
            dsimp only [paxOv]
            rw [hu]
            rfl
          | false =>
            right
            have hu' := hu
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt] at hu'
            refine ⟨by dsimp only [paxOv]; rw [hu]; rfl, ?_, hu'.2⟩
            exact isAsciiString_asciiFallback_eq hu'.1 hu'.2
        have heff_gname : (some paxOv |>.getD {}).gname? = some e.gname ∨
            ((some paxOv |>.getD {}).gname? = none ∧ fbGname = e.gname ∧ e.gname.toUTF8.size ≤ 32) := by
          cases hg : (!isAsciiString e.gname || e.gname.toUTF8.size > 32) with
          | true =>
            left
            dsimp only [paxOv]
            rw [hg]
            rfl
          | false =>
            right
            have hg' := hg
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt] at hg'
            refine ⟨by dsimp only [paxOv]; rw [hg]; rfl, ?_, hg'.2⟩
            exact isAsciiString_asciiFallback_eq hg'.1 hg'.2
        have ⟨heqv1, hsz1, hloop1⟩ := decode_ustar_entry bytes hdr off1 (some paxOv)
          fbPair.2 fbPair.1 fbLink fbUname fbGname fbUid fbGid fbSize fbMtime
          hext1 hhdr_eq (by omega) hfuid hfgid hfsize hfmtime heff_size heff_uid heff_gid heff_mtime
          heff_path heff_link heff_uname heff_gname
        refine ⟨_, heqv1, rfl, hsz1, ?_⟩
        dsimp only
        dsimp only [bytes] at hstep0 hloop1
        rw [hstep0, hloop1]
        have hoff_eq : off1 + 512 + pad512 e.data.size = pre.size + (encodeEntryBlocks e np).size := by
          simp only [off1, henc_sz, Nat.add_assoc]
        rw [hoff_eq]
      exact hpax_step _ _ _ rfl rfl rfl
    · have hneed_false : needsPax e (wirePathOf e.kind np) = false := Bool.eq_false_iff.mpr hneed
      have hnot_need := hneed_false
      unfold needsPax at hnot_need
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt, Nat.not_le] at hnot_need
      rcases hnot_need with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfit_wp, hasc_lk⟩, hsz_lk⟩, hasc_un⟩, hsz_un⟩, hasc_gn⟩, hsz_gn⟩, huid7⟩, hgid7⟩, hsz11⟩, hmtime11⟩
      let pair := if wp.toUTF8.size ≤ 100 then ("", wp)
        else match findUstarSplit wp with | some p => p | none => ("", wp)
      have hustar_step : ∀ (hdr : ByteArray),
          hdr = buildUstarHeader pair.2 e.mode e.uid e.gid e.data.size e.mtime typeByte e.linkTarget e.uname e.gname pair.1 →
          ∃ entry' : TarEntry,
            entryEquivBool e entry' = true ∧
            entry'.path = np ∧
            entry'.data.size = e.data.size ∧
            let bytes := pre ++ (encodeEntryBlocks e np ++ post)
            unpackLoop opts bytes pre.size none seen acc totalBytes =
              unpackLoop opts bytes (pre.size + (encodeEntryBlocks e np).size)
                none (np :: seen) (entry' :: acc) (totalBytes + e.data.size) := by
        intro hdr hhdr_eq
        have henc : encodeEntryBlocks e np = hdr ++ padBlock512 e.data := by
          unfold encodeEntryBlocks
          dsimp only
          simp only [hneed_false, Bool.not_false, ↓reduceIte]
          exact congrArg (· ++ padBlock512 e.data) hhdr_eq.symm
        have hhdr_sz : hdr.size = 512 := by rw [hhdr_eq]; exact buildUstarHeader_size ..
        have hpad_sz : (padBlock512 e.data).size = pad512 e.data.size := padBlock512_size _
        have henc_sz : (encodeEntryBlocks e np).size = 512 + pad512 e.data.size := by
          rw [henc, ByteArray.size_append, hhdr_sz, hpad_sz]
        let bytes := pre ++ (encodeEntryBlocks e np ++ post)
        have hbytes_sz : bytes.size = pre.size + (encodeEntryBlocks e np).size + post.size := by
          simp only [bytes, ByteArray.size_append, Nat.add_assoc]
        have hext1 : bytes.extract pre.size (pre.size + 512 + pad512 e.data.size) = hdr ++ padBlock512 e.data := by
          have hmid_sz : (hdr ++ padBlock512 e.data).size = 512 + pad512 e.data.size := by
            rw [ByteArray.size_append, hhdr_sz, hpad_sz]
          dsimp only [bytes]
          rw [henc, Nat.add_assoc pre.size 512 (pad512 e.data.size), ← hmid_sz, ← ByteArray.append_assoc]
          exact extract_append_mid pre (hdr ++ padBlock512 e.data) post
        have hsplit_wp := ustarPathSplit_ok wp hfit_wp hnul_wp
        have ⟨heqv1, hsz1, hloop1⟩ := decode_ustar_entry bytes hdr pre.size none
          pair.2 pair.1 e.linkTarget e.uname e.gname e.uid e.gid e.data.size e.mtime
          hext1 hhdr_eq (by omega) huid7 hgid7 hsz11 hmtime11 rfl rfl rfl rfl
          (Or.inr ⟨rfl, hsplit_wp⟩)
          (fun _ => Or.inr ⟨rfl, rfl, hsz_lk⟩)
          (Or.inr ⟨rfl, rfl, hsz_un⟩)
          (Or.inr ⟨rfl, rfl, hsz_gn⟩)
        refine ⟨_, heqv1, rfl, hsz1, ?_⟩
        dsimp only [bytes]
        rw [hloop1, Nat.add_assoc pre.size 512 (pad512 e.data.size), ← henc_sz]
      exact hustar_step _ rfl

end LeanSwe.Tar.Proofs
