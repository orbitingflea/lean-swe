import LeanSwe.Tar.Model.WireSpec
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.RefinesUnpackCodec
import LeanSwe.Tar.Proofs.RefinesPax

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem optionPaxOvRel_getD {a : Option PaxOverrides} {b : Option PaxModelOverrides}
    (h : match a, b with | none, none => True | some x, some y => paxOvRel x y | _, _ => False) :
    paxOvRel (a.getD {}) (b.getD {}) := by
  cases a <;> cases b <;> simp only [Option.getD] at h ⊢
  · exact paxOvRel_empty
  · exact h

private theorem optionPaxOvRel_isSome {a : Option PaxOverrides} {b : Option PaxModelOverrides}
    (h : match a, b with | none, none => True | some x, some y => paxOvRel x y | _, _ => False) :
    a.isSome = b.isSome := by
  cases a <;> cases b <;> first | rfl | exact False.elim h

private theorem decodeTarEntry_ok_tail (bytes : ByteArray) (offset : Nat)
    (seen : List String) (normPath rawLink uname gname : String)
    (kind : EntryKind) (mode uid gid mtime effSize : Nat) :
    tarExceptRel (fun (a b : TarEntry × Nat) => a = b ∧ a.2 % 512 = 0)
      (if seen.contains normPath then
         Except.error
           ({ kind := TarErrorKind.duplicatePath
            , message := s!"duplicate tar entry path: {normPath}"
            , entryPath := some normPath
            , offset := some offset } : TarError)
       else
         let payload := if effSize == 0 then ByteArray.empty
           else bytes.extract (offset + 512) (offset + 512 + effSize)
         let entry : TarEntry := {
           path := normPath, kind := kind, mode := (mode &&& 0o7777).toUInt32
           uid := uid, gid := gid, mtime := mtime
           uname := uname, gname := gname, data := payload, linkTarget := rawLink
         }
         Except.ok (entry, pad512 effSize))
      (if seen.contains normPath then
         Except.error (TarErrorKind.duplicatePath, some normPath, some offset)
       else
         let payload := bytes.extract (offset + 512) (offset + 512 + effSize)
         let entry : TarEntry := {
           path := normPath, kind := kind, mode := (mode &&& 0o7777).toUInt32
           uid := uid, gid := gid, mtime := mtime
           uname := uname, gname := gname, data := payload, linkTarget := rawLink
         }
         Except.ok (entry, pad512 effSize)) := by
  by_cases hdup : seen.contains normPath = true
  · simp only [hdup, ↓reduceIte]
    exact .error rfl (nonEmpty_append_left (by decide))
  · simp only [Bool.eq_false_iff.mpr hdup, Bool.false_eq_true, ↓reduceIte]
    apply tarExceptRel.ok
    refine ⟨?_, pad512_mod _⟩
    by_cases hz : effSize = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte, Nat.add_zero]
      have hemp : bytes.extract (offset + 512) (offset + 512) = ByteArray.empty :=
        ByteArray.extract_eq_empty_iff.mpr (by omega)
      rw [hemp]
    · simp [beq_false_of_ne hz]

local macro "close_decode_val" : tactic =>
  `(tactic| (
    split
    · rename_i hv
      simp only [hv]
      exact .error rfl (validateEntryPath_err_props _ _ _ _ hv).1
    · rename_i hv
      simp only [hv]
      first
      | exact decodeTarEntry_ok_tail _ _ _ _ _ _ _ _ _ _ _ _ _
      | (split
         · rename_i hs
           simp only [hs]
           exact .error rfl (validateSymlinkTarget_err_props _ _ _ _ hs).1
         · rename_i hs
           simp only [hs]
           exact decodeTarEntry_ok_tail _ _ _ _ _ _ _ _ _ _ _ _ _)))

private theorem decodeTarEntry_refines (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    {hdr : UstarHeaderFields} {mhdr : HeaderFieldsModel} (hh : headerFieldsRel hdr mhdr)
    {pendingPax : Option PaxOverrides} {mpendingPax : Option PaxModelOverrides}
    (hpax : match pendingPax, mpendingPax with
      | none, none => True | some x, some y => paxOvRel x y | _, _ => False)
    (seen : List String) (accLen totalBytes : Nat) :
    tarExceptRel (fun a b => a = b ∧ a.2 % 512 = 0)
      (decodeTarEntry opts bytes offset hdr pendingPax seen accLen totalBytes)
      (decodeTarEntryModel opts bytes (bytes.extract offset (offset + 512)) offset
        mhdr mpendingPax seen accLen totalBytes) := by
  rcases hh with ⟨hmode, huid, hgid, hsize, hmtime, htype⟩
  rcases optionPaxOvRel_getD hpax with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  unfold decodeTarEntry decodeTarEntryModel
  simp only [pad512Impl_eq, validateEntryPathImpl_eq, validateSymlinkTargetImpl_eq]
  rw [htype]
  generalize
    (if mhdr.typeflag == 0x30 || mhdr.typeflag == 0x00 then some EntryKind.regular
     else if mhdr.typeflag == 0x35 then some .directory
     else if mhdr.typeflag == 0x32 then some .symlink else none) = kind?
  cases kind? with
  | none =>
    exact .error rfl (nonEmpty_append_left (by decide))
  | some kind =>
    dsimp only
    have heff : (pendingPax.getD {}).size?.getD hdr.size =
        (mpendingPax.getD {}).size?.getD mhdr.size := by rw [h5, hsize]
    rw [heff]
    by_cases hnr : (kind != .regular && (mpendingPax.getD {}).size?.getD mhdr.size != 0) = true
    · simp only [hnr, ↓reduceIte]; exact .error rfl rfl
    simp only [Bool.eq_false_iff.mpr hnr, Bool.false_eq_true, ↓reduceIte]
    by_cases hme : accLen + 1 > opts.maxEntries
    · simp only [hme, ↓reduceIte]; exact .error rfl rfl
    simp only [hme, ↓reduceIte]
    by_cases hmb : totalBytes + (mpendingPax.getD {}).size?.getD mhdr.size > opts.maxTotalBytes
    · simp only [hmb, ↓reduceIte]; exact .error rfl rfl
    simp only [hmb, ↓reduceIte]
    by_cases htr : offset + 512 + pad512 ((mpendingPax.getD {}).size?.getD mhdr.size) > bytes.size
    · simp only [htr, ↓reduceIte]; exact .error rfl rfl
    simp only [htr, ↓reduceIte]
    rw [sliceList_hdr_sub bytes offset 0 100 (by decide),
      sliceList_hdr_sub bytes offset 345 500 (by decide),
      sliceList_hdr_sub bytes offset 157 257 (by decide),
      sliceList_hdr_sub bytes offset 265 297 (by decide),
      sliceList_hdr_sub bytes offset 297 329 (by decide),
      h1, h2, h3, h4, h6, h7, h8, hmode, huid, hgid, hmtime]
    have h0 : offset + 0 = offset := Nat.add_zero offset
    rw [h0]
    have hnm := decodeCStringUtf8_refines bytes offset (offset + 100) offset "name"
    have hpf := decodeCStringUtf8_refines bytes (offset + 345) (offset + 500) offset "prefix"
    have hln := decodeCStringUtf8_refines bytes (offset + 157) (offset + 257) offset "linkname"
    have hu := decodeCStringUtf8_refines bytes (offset + 265) (offset + 297) offset "uname"
    have hg := decodeCStringUtf8_refines bytes (offset + 297) (offset + 329) offset "gname"
    generalize decodeCStringUtf8 bytes offset (offset + 100) offset "name" = nm1 at hnm ⊢
    generalize decodeCStringList (sliceList bytes offset (offset + 100)) offset = nm2 at hnm ⊢
    generalize decodeCStringUtf8 bytes (offset + 345) (offset + 500) offset "prefix" = pf1 at hpf ⊢
    generalize decodeCStringList (sliceList bytes (offset + 345) (offset + 500)) offset = pf2 at hpf ⊢
    generalize decodeCStringUtf8 bytes (offset + 157) (offset + 257) offset "linkname" = ln1 at hln ⊢
    generalize decodeCStringList (sliceList bytes (offset + 157) (offset + 257)) offset = ln2 at hln ⊢
    generalize decodeCStringUtf8 bytes (offset + 265) (offset + 297) offset "uname" = un1 at hu ⊢
    generalize decodeCStringList (sliceList bytes (offset + 265) (offset + 297)) offset = un2 at hu ⊢
    generalize decodeCStringUtf8 bytes (offset + 297) (offset + 329) offset "gname" = gn1 at hg ⊢
    generalize decodeCStringList (sliceList bytes (offset + 297) (offset + 329)) offset = gn2 at hg ⊢
    generalize (mpendingPax.getD {}).path? = pOpt
    generalize (mpendingPax.getD {}).linkpath? = lOpt
    generalize (mpendingPax.getD {}).uname? = uOpt
    generalize (mpendingPax.getD {}).gname? = gOpt
    cases pOpt
    cases hnm
    rotate_left 1
    · rename_i hk' hm; dsimp only; exact .error hk' hm
    rotate_right 1
    rename_i hne; subst hne
    cases hpf
    rotate_left 1
    · rename_i hk' hm; dsimp only; exact .error hk' hm
    rotate_right 1
    rename_i hpe; subst hpe
    all_goals
      cases kind
      rotate_left 2
      cases lOpt
      cases hln
      rotate_left 1
      · rename_i hk' hm; dsimp only; exact .error hk' hm
      rotate_right 1
      rename_i hle; subst hle
    all_goals
      cases uOpt
      cases hu
      rotate_left 1
      · rename_i hk' hm; dsimp only; exact .error hk' hm
      rotate_right 1
      rename_i hue; subst hue
    all_goals
      cases gOpt with
      | some _ => dsimp only; close_decode_val
      | none =>
        cases hg with
        | error hk' hm => dsimp only; exact .error hk' hm
        | ok hge => subst hge; dsimp only; close_decode_val

private inductive UnpackStepRel (offset : Nat) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) :
    UnpackStep → UnpackStepModel → Prop
  | done : UnpackStepRel offset seen acc totalBytes (.done acc.reverse) .done
  | pax {nextOff : Nat} {ov : PaxOverrides} {mov : PaxModelOverrides}
      (hlt : offset < nextOff) (hmod : nextOff % 512 = 0) (hrel : paxOvRel ov mov) :
      UnpackStepRel offset seen acc totalBytes
        (.cont nextOff (some ov) seen acc totalBytes) (.pax nextOff mov)
  | entry {nextOff : Nat} {e : TarEntry}
      (hlt : offset < nextOff) (hmod : nextOff % 512 = 0) :
      UnpackStepRel offset seen acc totalBytes
        (.cont nextOff none (e.path :: seen) (e :: acc) (totalBytes + e.data.size))
        (.entry nextOff e)

private theorem unpackStep_refines (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (hbm : bytes.size % 512 = 0) (hom : offset % 512 = 0)
    (pendingPax : Option PaxOverrides) (mpendingPax : Option PaxModelOverrides)
    (hpax : match pendingPax, mpendingPax with
      | none, none => True | some x, some y => paxOvRel x y | _, _ => False)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat) :
    tarExceptRel (UnpackStepRel offset seen acc totalBytes)
      (unpackStep opts bytes offset pendingPax seen acc totalBytes)
      (unpackStepModel opts bytes offset mpendingPax seen acc.length totalBytes) := by
  unfold unpackStep unpackStepModel
  by_cases hge : offset ≥ bytes.size
  · simp only [hge, ↓reduceIte]; exact .error rfl rfl
  simp only [hge, ↓reduceIte]
  rw [isZeroRange_eq_isZeroBlockAt bytes offset]
  by_cases hzb : isZeroBlockAt bytes offset = true
  · simp only [hzb, ↓reduceIte, optionPaxOvRel_isSome hpax]
    by_cases hp1 : mpendingPax.isSome = true
    · simp only [hp1, ↓reduceIte]; exact .error rfl rfl
    simp only [Bool.eq_false_iff.mpr hp1, Bool.false_eq_true, ↓reduceIte]
    by_cases hp2 : offset + 512 ≥ bytes.size
    · simp only [hp2, ↓reduceIte]; exact .error rfl rfl
    simp only [hp2, ↓reduceIte, isZeroRange_eq_isZeroBlockAt bytes (offset + 512)]
    by_cases hp3 : (!isZeroBlockAt bytes (offset + 512)) = true
    · simp only [hp3, ↓reduceIte]; exact .error rfl rfl
    simp only [Bool.eq_false_iff.mpr hp3, Bool.false_eq_true, ↓reduceIte,
      allZeroTrailer_eq_isZeroSuffix bytes (offset + 1024) hbm (by omega)]
    by_cases hp4 : (!isZeroSuffix bytes (offset + 1024)) = true
    · simp only [hp4, ↓reduceIte]; exact .error rfl rfl
    simp only [Bool.eq_false_iff.mpr hp4, Bool.false_eq_true, ↓reduceIte]
    exact .ok .done
  simp only [Bool.eq_false_iff.mpr hzb, Bool.false_eq_true, ↓reduceIte]
  by_cases hfit : offset + 512 > bytes.size
  · simp only [hfit, ↓reduceIte]; exact .error rfl rfl
  simp only [hfit, ↓reduceIte]
  have hhdr := parseUstarHeader_refines bytes offset
  generalize parseUstarHeader bytes offset = rh1 at hhdr ⊢
  generalize parseUstarHeaderModel (bytes.extract offset (offset + 512)) offset = rh2 at hhdr ⊢
  cases hhdr with
  | error hk hm => dsimp only; exact .error hk hm
  | ok hhdr' =>
    rename_i hdr mhdr
    dsimp only
    have htf : hdr.typeflag = mhdr.typeflag := hhdr'.2.2.2.2.2
    have hsz : hdr.size = mhdr.size := hhdr'.2.2.2.1
    rw [htf]
    by_cases hpaxT : (mhdr.typeflag == 0x78) = true
    · simp only [hpaxT, ↓reduceIte, optionPaxOvRel_isSome hpax, hsz]
      by_cases hp1 : mpendingPax.isSome = true
      · simp only [hp1, ↓reduceIte]; exact .error rfl rfl
      simp only [Bool.eq_false_iff.mpr hp1, Bool.false_eq_true, ↓reduceIte]
      by_cases hlim : mhdr.size > maxPaxHeaderBytes
      · simp only [hlim, ↓reduceIte]; exact .error rfl rfl
      simp only [hlim, ↓reduceIte, pad512Impl_eq]
      by_cases htr : offset + 512 + pad512 mhdr.size > bytes.size
      · simp only [htr, ↓reduceIte]; exact .error rfl rfl
      simp only [htr, ↓reduceIte]
      have hpSlice : sliceList (bytes.extract (offset + 512) (offset + 512 + mhdr.size)) 0
          (bytes.extract (offset + 512) (offset + 512 + mhdr.size)).size =
          sliceList bytes (offset + 512) (offset + 512 + mhdr.size) := by
        unfold sliceList; rw [ByteArray.extract_zero_size]
      have hpx := parsePaxPayload_refines (bytes.extract (offset + 512) (offset + 512 + mhdr.size)) offset
      rw [hpSlice] at hpx
      generalize parsePaxPayload (bytes.extract (offset + 512) (offset + 512 + mhdr.size)) offset = px1 at hpx ⊢
      generalize parsePaxRecordsModel (sliceList bytes (offset + 512) (offset + 512 + mhdr.size)) offset [] {} = px2 at hpx ⊢
      cases hpx with
      | error hk hm => dsimp only; exact .error hk hm
      | ok hrel => dsimp only; exact .ok (.pax (by omega) (by have := pad512_mod mhdr.size; omega) hrel)
    · simp only [Bool.eq_false_iff.mpr hpaxT, Bool.false_eq_true, ↓reduceIte]
      have hdec := decodeTarEntry_refines opts bytes offset hhdr' hpax seen acc.length totalBytes
      generalize decodeTarEntry opts bytes offset hdr pendingPax seen acc.length totalBytes = d1 at hdec ⊢
      generalize decodeTarEntryModel opts bytes (bytes.extract offset (offset + 512)) offset mhdr mpendingPax seen acc.length totalBytes = d2 at hdec ⊢
      cases hdec with
      | error hk hm => dsimp only; exact .error hk hm
      | ok hpe =>
        rename_i p1 p2
        rcases p1 with ⟨e1, n1⟩
        rcases p2 with ⟨e2, n2⟩
        rcases hpe with ⟨heq, hpmod⟩
        injection heq with he hn
        subst he hn
        dsimp only
        exact .ok (.entry (by omega) (by omega))

private theorem unpackLoop_refines (opts : UnpackOptions) (bytes : ByteArray)
    (hbm : bytes.size % 512 = 0) :
    ∀ (rem offset : Nat) (pendingPax : Option PaxOverrides) (mpendingPax : Option PaxModelOverrides)
      (seen : List String) (acc : List TarEntry) (totalBytes : Nat),
      bytes.size - offset ≤ rem →
      offset % 512 = 0 →
      (match pendingPax, mpendingPax with
       | none, none => True | some x, some y => paxOvRel x y | _, _ => False) →
      tarExceptRel (fun out rest => out = acc.reverse ++ rest)
        (unpackLoop opts bytes offset pendingPax seen acc totalBytes)
        (unpackStreamModel opts bytes offset mpendingPax seen acc.length totalBytes) := by
  intro rem; induction rem with
  | zero =>
    intro offset pendingPax mpendingPax seen acc totalBytes hrem _ _
    have hge : offset ≥ bytes.size := by omega
    rw [unpackLoop_at_ge _ _ _ _ _ _ _ hge, unpackStreamModel.eq_1]
    simp only [hge, ↓reduceIte]; exact .error rfl rfl
  | succ rem ih =>
    intro offset pendingPax mpendingPax seen acc totalBytes hrem hom hpax
    rw [unpackStreamModel.eq_1]
    by_cases hge : offset ≥ bytes.size
    · rw [unpackLoop_at_ge _ _ _ _ _ _ _ hge]
      simp only [hge, ↓reduceIte]; exact .error rfl rfl
    · have hoff : offset < bytes.size := by omega
      simp only [hge, ↓reduceIte]
      have hs := unpackStep_refines opts bytes offset hbm hom pendingPax mpendingPax hpax seen acc totalBytes
      generalize hs1 : unpackStep opts bytes offset pendingPax seen acc totalBytes = st1 at hs
      generalize hs2 : unpackStepModel opts bytes offset mpendingPax seen acc.length totalBytes = st2 at hs ⊢
      cases hs with
      | error hk hm =>
        rw [unpackLoop_step_err _ _ _ _ _ _ _ _ hoff hs1]
        exact .error hk hm
      | ok hrel =>
        cases hrel with
        | done =>
          rw [unpackLoop_step_done _ _ _ _ _ _ _ _ hoff hs1]
          exact .ok (by simp)
        | pax hlt hmod hpx =>
          rw [unpackLoop_step_continue _ _ _ _ _ _ _ _ _ _ _ _ hoff hs1 hlt]
          simp only [hlt, ↓reduceIte]
          exact ih _ (some _) (some _) seen acc totalBytes (by omega) hmod hpx
        | entry hlt hmod =>
          rename_i nextOff e
          rw [unpackLoop_step_continue _ _ _ _ _ _ _ _ _ _ _ _ hoff hs1 hlt]
          simp only [hlt, ↓reduceIte]
          have hrec := ih nextOff none none (e.path :: seen) (e :: acc) (totalBytes + e.data.size)
            (by omega) hmod trivial
          simp only [List.length_cons] at hrec
          generalize unpackLoop opts bytes nextOff none (e.path :: seen) (e :: acc) (totalBytes + e.data.size) = r1 at hrec ⊢
          generalize unpackStreamModel opts bytes nextOff none (e.path :: seen) (acc.length + 1) (totalBytes + e.data.size) = r2 at hrec ⊢
          cases hrec with
          | error hk hm => exact .error hk hm
          | ok heq => exact .ok (by rw [heq, List.reverse_cons, List.append_assoc, List.singleton_append])

/-- `LeanSwe.Tar.unpackWith` refines `Model.allowedUnpackWith` on all options and byte arrays. -/
theorem unpackWith_refines_model (opts : UnpackOptions) (bytes : ByteArray) :
    allowedUnpackWith opts bytes (LeanSwe.Tar.unpackWith opts bytes) := by
  unfold allowedUnpackWith unpackWithModel LeanSwe.Tar.unpackWith Impl.unpackWith
  by_cases hbad : (bytes.size == 0 || bytes.size % 512 != 0) = true
  · simp only [hbad, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · have hbadF : (bytes.size == 0 || bytes.size % 512 != 0) = false := Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte]
    have hmod : bytes.size % 512 = 0 := by
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hbadF
      exact hbadF.2
    have hloop := unpackLoop_refines opts bytes hmod bytes.size 0 none none [] [] 0 (by omega) rfl trivial
    generalize unpackLoop opts bytes 0 none [] [] 0 = r1 at hloop ⊢
    generalize unpackStreamModel opts bytes 0 none [] 0 0 = r2 at hloop ⊢
    cases hloop with
    | error hk hm => exact ⟨hk, hm⟩
    | ok heq => simpa using heq

/-- `LeanSwe.Tar.unpack` refines `Model.allowedUnpack` on all byte arrays. -/
theorem unpack_refines_model (bytes : ByteArray) :
    allowedUnpack bytes (LeanSwe.Tar.unpack bytes) :=
  unpackWith_refines_model {} bytes

end LeanSwe.Tar.Proofs
