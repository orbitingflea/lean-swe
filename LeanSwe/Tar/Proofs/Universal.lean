import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.Headers
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.UnpackValid
import LeanSwe.Tar.Proofs.EncodeStep

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Concatenate encoded tar entry blocks sequentially across an entry list. -/
def encodeEntriesList : List TarEntry → ByteArray
  | [] => ByteArray.empty
  | e :: rest => encodeEntryBlocks e (normalizeTarPath e.kind e.path) ++ encodeEntriesList rest

/-- Prove that `packWith.go` on valid entries equals `encodeEntriesList` plus two zero trailer blocks. -/
theorem packWith_go_eq_encodeEntriesList (opts : PackOptions) (es : List TarEntry)
    (seen : List String) (acc : ByteArray)
    (hvalid : (es.all (validEntryBool opts.allowAbsolute opts.allowParentTraversal) &&
      noDupNormalizedPathsBool.go seen es) = true) :
    ∃ out, packWith.go opts es seen acc = .ok out ∧
      out = acc ++ encodeEntriesList (if opts.deterministic then es.map zeroDeterministicMeta else es) ++
        (zeroBlock ++ zeroBlock) := by
  have ⟨out, hout⟩ := (packWith_go_spec opts es seen acc).2 hvalid
  have ⟨_, hout_eq⟩ := (packWith_go_spec opts es seen acc).1 out hout
  refine ⟨out, hout, ?_⟩
  have hfold_entries : ∀ (xs : List TarEntry) (d : Bool),
      xs.foldl (fun b x => b ++ encodeEntryBlocks (if d then zeroDeterministicMeta x else x)
        (normalizeTarPath x.kind x.path)) ByteArray.empty =
      encodeEntriesList (if d then xs.map zeroDeterministicMeta else xs) := by
    intro xs d
    have hfold : ∀ (init : ByteArray) (ys : List TarEntry),
        ys.foldl (fun b x => b ++ encodeEntryBlocks (if d then zeroDeterministicMeta x else x)
          (normalizeTarPath x.kind x.path)) init =
        init ++ ys.foldl (fun b x => b ++ encodeEntryBlocks (if d then zeroDeterministicMeta x else x)
          (normalizeTarPath x.kind x.path)) ByteArray.empty := by
      intro init ys
      induction ys generalizing init with
      | nil => simp [ByteArray.append_empty]
      | cons x ys ihy =>
        simp only [List.foldl_cons, ByteArray.empty_append]
        rw [ihy, ihy (encodeEntryBlocks _ _), ByteArray.append_assoc]
    cases d with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hfold
      induction xs with
      | nil => rfl
      | cons e rest ih =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_cons, ByteArray.empty_append,
          encodeEntriesList] at ih ⊢
        rw [hfold, ih]
    | true =>
      simp only [↓reduceIte] at hfold
      induction xs with
      | nil => rfl
      | cons e rest ih =>
        simp only [↓reduceIte, List.map_cons, List.foldl_cons, ByteArray.empty_append,
          encodeEntriesList] at ih ⊢
        have hnp : normalizeTarPath (zeroDeterministicMeta e).kind (zeroDeterministicMeta e).path =
            normalizeTarPath e.kind e.path := rfl
        rw [hnp, hfold, ih]
  rw [hout_eq, hfold_entries]

/-- Prove that `unpackLoop` decodes `encodeEntriesList es ++ twoZeroBlocks` to a `TarEquiv` list. -/
theorem unpackLoop_encodeEntriesList (opts : UnpackOptions) (pre : ByteArray)
    (es : List TarEntry) (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hvalid : ∀ e ∈ es, validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true)
    (hnodup : noDupNormalizedPathsBool.go seen es = true)
    (hpax : es.all fitsPaxLimit = true)
    (hle_e : acc.length + es.length ≤ opts.maxEntries)
    (hle_b : totalBytes + totalDataBytes es ≤ opts.maxTotalBytes) :
    ∃ decoded : List TarEntry,
      TarEquiv es decoded ∧
      unpackLoop opts (pre ++ (encodeEntriesList es ++ (zeroBlock ++ zeroBlock)))
        pre.size none seen acc totalBytes = .ok (acc.reverse ++ decoded) := by
  induction es generalizing pre seen acc totalBytes with
  | nil =>
    refine ⟨[], trivial, ?_⟩
    simp only [encodeEntriesList, ByteArray.empty_append, List.append_nil]
    let bytes := pre ++ (zeroBlock ++ zeroBlock)
    have hz2_sz : (zeroBlock ++ zeroBlock).size = 1024 := by
      rw [ByteArray.size_append, zeroBlock_size]
    have hbytes_sz : bytes.size = pre.size + 1024 := by
      rw [ByteArray.size_append, hz2_sz]
    have hnot_ge : ¬(pre.size ≥ bytes.size) := by omega
    have hnot_ge2 : ¬(pre.size + 512 ≥ bytes.size) := by omega
    have hz_fn : ∀ off k, (off = pre.size ∨ off = pre.size + 512) → k < 512 →
        ∀ hk : off + k < bytes.size, bytes[off + k]'hk = 0 := by
      intro off k hoff hk hk_bd
      rcases hoff with rfl | rfl
      · rw [getElem_append_right (Nat.le_add_right _ _)]
        have hsub : pre.size + k - pre.size = k := Nat.add_sub_cancel_left _ _
        simp only [hsub]
        rw [getElem_append_left (by rw [zeroBlock_size]; exact hk) (by rw [ByteArray.size_append, zeroBlock_size]; omega)]
        exact zeroBlock_getElem _
      · rw [getElem_append_right (by omega)]
        have hsub : pre.size + 512 + k - pre.size = 512 + k := by omega
        simp only [hsub]
        rw [getElem_append_right (by rw [zeroBlock_size]; omega)]
        exact zeroBlock_getElem _
    have hzr1 : isZeroRange bytes pre.size 512 = true :=
      (isZeroRange_eq_true_iff bytes pre.size 512 (by omega)).mpr ⟨by omega, fun k hk hbd => hz_fn _ k (Or.inl rfl) hk hbd⟩
    have hzr2 : isZeroRange bytes (pre.size + 512) 512 = true :=
      (isZeroRange_eq_true_iff bytes (pre.size + 512) 512 (by omega)).mpr ⟨by omega, fun k hk hbd => hz_fn _ k (Or.inr rfl) hk hbd⟩
    have htrail : allZeroTrailer bytes (pre.size + 1024) = true := by
      rw [allZeroTrailer.eq_1]
      have hge : pre.size + 1024 ≥ bytes.size := by omega
      simp only [hge, ↓reduceIte]
    dsimp only [bytes] at hnot_ge hnot_ge2 hzr1 hzr2 htrail
    rw [unpackLoop.eq_1]
    simp only [hnot_ge, ↓reduceIte]
    unfold unpackStep
    simp only [hnot_ge, ↓reduceIte, hzr1, Option.isSome_none, Bool.false_eq_true,
      hnot_ge2, hzr2, Bool.not_true, htrail]
  | cons e rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hpax
    rw [noDupNormalizedPathsBool.go.eq_2, Bool.and_eq_true] at hnodup
    have hve_e : validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true := hvalid e (by simp)
    have hcons_bytes : totalDataBytes (e :: rest) = e.data.size + totalDataBytes rest := by
      have h := totalDataBytes_append [e] rest
      have h1 : totalDataBytes [e] = e.data.size := by unfold totalDataBytes; simp
      simpa [h1] using h
    let post := encodeEntriesList rest ++ (zeroBlock ++ zeroBlock)
    have hpost_sz : post.size ≥ 512 := by
      have hz2_sz : (zeroBlock ++ zeroBlock).size = 1024 := by rw [ByteArray.size_append, zeroBlock_size]
      dsimp only [post]
      rw [ByteArray.size_append, hz2_sz]
      omega
    have ⟨entry', heqv, hpath', _, hstep⟩ := unpackLoop_encodeEntryBlocks_step opts pre post e
      (normalizeTarPath e.kind e.path) seen acc totalBytes hve_e rfl hpax.1 hnodup.1
      (by simp at hle_e; omega) (by omega) hpost_sz
    have hpre_eq : pre ++ (encodeEntriesList (e :: rest) ++ (zeroBlock ++ zeroBlock)) =
        pre ++ (encodeEntryBlocks e (normalizeTarPath e.kind e.path) ++ post) := by
      simp [encodeEntriesList, post, ByteArray.append_assoc]
    have hih_eq : (pre ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path)) ++ (encodeEntriesList rest ++ (zeroBlock ++ zeroBlock)) =
        pre ++ (encodeEntryBlocks e (normalizeTarPath e.kind e.path) ++ post) := by
      simp [post, ByteArray.append_assoc]
    have ⟨decodedTail, hteq, htail⟩ := ih (pre ++ encodeEntryBlocks e (normalizeTarPath e.kind e.path))
      (normalizeTarPath e.kind e.path :: seen) (entry' :: acc) (totalBytes + e.data.size)
      (fun x hx => hvalid x (by simp [hx])) hnodup.2 hpax.2 (by simp at hle_e ⊢; omega) (by omega)
    refine ⟨entry' :: decodedTail, ⟨heqv, hteq⟩, ?_⟩
    rw [hpre_eq, hstep]
    rw [← ByteArray.size_append, ← hih_eq]
    rw [htail]
    simp [List.reverse_cons, List.append_assoc]

private theorem packUnpack_roundTrip_witness
    (entries : List TarEntry) (packOpts : PackOptions) (unpackOpts : UnpackOptions)
    (hvalid : ValidArchive packOpts.allowAbsolute packOpts.allowParentTraversal entries)
    (habs : (!packOpts.allowAbsolute || unpackOpts.allowAbsolute) = true)
    (hpar : (!packOpts.allowParentTraversal || unpackOpts.allowParentTraversal) = true)
    (hlen : entries.length ≤ unpackOpts.maxEntries)
    (hbytes : totalDataBytes entries ≤ unpackOpts.maxTotalBytes)
    (hpax : entries.all fitsPaxLimit = true) :
    ∃ bytes decoded,
      Impl.packWith packOpts entries = .ok bytes ∧
      Impl.unpackWith unpackOpts bytes = .ok decoded ∧
      TarEquiv (if packOpts.deterministic then entries.map zeroDeterministicMeta else entries) decoded := by
  let effEntries := if packOpts.deterministic then entries.map zeroDeterministicMeta else entries
  have hvalid_pack : (entries.all (validEntryBool packOpts.allowAbsolute packOpts.allowParentTraversal) &&
      noDupNormalizedPathsBool.go [] entries) = true := hvalid
  have ⟨bytes, hpack_ok, hbytes_eq⟩ := packWith_go_eq_encodeEntriesList packOpts entries [] ByteArray.empty hvalid_pack
  have hvalid_eff : validArchiveBool packOpts.allowAbsolute packOpts.allowParentTraversal effEntries = true := by
    cases hd : packOpts.deterministic <;> simp only [effEntries, hd, Bool.false_eq_true, ↓reduceIte]
    · exact hvalid
    · exact validArchiveBool_map_zeroDeterministicMeta hvalid
  have hvalid_unpack : validArchiveBool unpackOpts.allowAbsolute unpackOpts.allowParentTraversal effEntries = true :=
    validArchiveBool_mono habs hpar effEntries hvalid_eff
  have hpax_eff : effEntries.all fitsPaxLimit = true := by
    cases hd : packOpts.deterministic <;> simp only [effEntries, hd, Bool.false_eq_true, ↓reduceIte]
    · exact hpax
    · rw [List.all_eq_true] at hpax ⊢
      intro e he
      rw [List.mem_map] at he
      rcases he with ⟨e0, he0, rfl⟩
      exact fitsPaxLimit_zeroDeterministicMeta (hpax e0 he0)
  have hlen_eff : effEntries.length ≤ unpackOpts.maxEntries := by
    cases hd : packOpts.deterministic <;> simp [effEntries, hd, hlen]
  have hbytes_eff : totalDataBytes effEntries ≤ unpackOpts.maxTotalBytes := by
    cases hd : packOpts.deterministic <;> simp only [effEntries, hd, Bool.false_eq_true, ↓reduceIte]
    · exact hbytes
    · have htot_map : totalDataBytes (entries.map zeroDeterministicMeta) = totalDataBytes entries := by
        unfold totalDataBytes
        have hfold : ∀ (init : Nat) (xs : List TarEntry),
            (xs.map zeroDeterministicMeta).foldl (fun a e => a + e.data.size) init =
            xs.foldl (fun a e => a + e.data.size) init := by
          intro init xs
          induction xs generalizing init with
          | nil => rfl
          | cons x xs ih => simp [List.map_cons, zeroDeterministicMeta, ih]
        exact hfold 0 entries
      rw [htot_map]; exact hbytes
  unfold validArchiveBool at hvalid_unpack
  rw [Bool.and_eq_true, List.all_eq_true] at hvalid_unpack
  have ⟨decoded, hteq, hloop_ok⟩ := unpackLoop_encodeEntriesList unpackOpts ByteArray.empty effEntries [] [] 0
    hvalid_unpack.1 hvalid_unpack.2 hpax_eff (by simpa using hlen_eff) (by simpa using hbytes_eff)
  have hbytes_nz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by
    have hbytes_form : bytes = encodeEntriesList effEntries ++ (zeroBlock ++ zeroBlock) := by
      simpa [ByteArray.empty_append] using hbytes_eq
    have hsz_mod : ∀ es : List TarEntry, (encodeEntriesList es).size % 512 = 0 := by
      intro es
      induction es with
      | nil => simp [encodeEntriesList]
      | cons e rest ih =>
        simp only [encodeEntriesList, ByteArray.size_append]
        have he_mod : (encodeEntryBlocks e (normalizeTarPath e.kind e.path)).size % 512 = 0 := by
          unfold encodeEntryBlocks
          dsimp only
          split
          · have hmd := padBlock512_size_mod e.data
            simp only [ByteArray.size_append, buildUstarHeader_size]
            omega
          · have hmp := padBlock512_size_mod (buildPaxPayload e (wirePathOf e.kind (normalizeTarPath e.kind e.path)))
            have hmd := padBlock512_size_mod e.data
            simp only [ByteArray.size_append, buildUstarHeader_size]
            omega
        omega
    have hz2_sz : (zeroBlock ++ zeroBlock).size = 1024 := by rw [ByteArray.size_append, zeroBlock_size]
    have hsz_full : bytes.size = (encodeEntriesList effEntries).size + 1024 := by
      rw [hbytes_form, ByteArray.size_append, hz2_sz]
    have hmod : bytes.size % 512 = 0 := by have := hsz_mod effEntries; omega
    have hpos : bytes.size ≠ 0 := by omega
    simp [hpos, hmod]
  have hunpack_ok : Impl.unpackWith unpackOpts bytes = .ok decoded := by
    unfold Impl.unpackWith
    simp only [hbytes_nz, Bool.false_eq_true, ↓reduceIte]
    have hbytes_form : ByteArray.empty ++ (encodeEntriesList effEntries ++ (zeroBlock ++ zeroBlock)) = bytes := by
      simpa [ByteArray.empty_append] using hbytes_eq.symm
    simpa [hbytes_form] using hloop_ok
  exact ⟨bytes, decoded, hpack_ok, hunpack_ok, hteq⟩

/-- Prove `test_tar_packUnpack_roundTrip` for `defaultApi`. -/
theorem allPass_packUnpack_roundTrip :
    AllPass (test_tar_packUnpack_roundTrip defaultApi) := by
  intro entries packOpts unpackOpts hvalid habs hpar hlen hbytes hpax
  have ⟨bytes, decoded, hpack_ok, hunpack_ok, hteq⟩ :=
    packUnpack_roundTrip_witness entries packOpts unpackOpts hvalid habs hpar hlen hbytes hpax
  have hpack_def : defaultApi.packWith packOpts entries = .ok bytes := hpack_ok
  have hunpack_def : defaultApi.unpackWith unpackOpts bytes = .ok decoded := hunpack_ok
  dsimp only [test_tar_packUnpack_roundTrip, Bind.bind, Pure.pure, NondetTest.assert]
  rw [hpack_def]
  dsimp only
  rw [hunpack_def]
  exact ⟨hteq, trivial⟩

/-- Witness `CanReach (test_tar_packUnpack_roundTrip defaultApi)` using an empty archive. -/
theorem canReach_packUnpack_roundTrip :
    CanReach (test_tar_packUnpack_roundTrip defaultApi) := by
  have hv : ValidArchive ({} : PackOptions).allowAbsolute ({} : PackOptions).allowParentTraversal [] := by
    unfold ValidArchive validArchiveBool; rfl
  have hlen : ([] : List TarEntry).length ≤ ({} : UnpackOptions).maxEntries := Nat.zero_le _
  have htot : totalDataBytes [] ≤ ({} : UnpackOptions).maxTotalBytes := by simp [totalDataBytes]
  have hpax : ([] : List TarEntry).all fitsPaxLimit = true := rfl
  have ⟨bytes, decoded, hpack_ok, hunpack_ok, hteq⟩ :=
    packUnpack_roundTrip_witness [] {} {} hv rfl rfl hlen htot hpax
  have hpack_def : defaultApi.packWith {} [] = .ok bytes := hpack_ok
  have hunpack_def : defaultApi.unpackWith {} bytes = .ok decoded := hunpack_ok
  unfold CanReach CanReachRun test_tar_packUnpack_roundTrip
  simp only [Bind.bind, NondetTest.nondet, NondetTest.assume, NondetTest.assert]
  refine ⟨[], {}, {}, hv, rfl, rfl, hlen, htot, hpax, ?_⟩
  rw [hpack_def]
  dsimp only
  rw [hunpack_def]
  exact ⟨hteq, trivial⟩

/-- Decidable `Bool` form of `TarEquiv` for concrete certificate proofs. -/
def tarEquivBool : List TarEntry → List TarEntry → Bool
  | [], [] => true
  | a :: xs, b :: ys => entryEquivBool a b && tarEquivBool xs ys
  | _, _ => false

/-- `tarEquivBool xs ys = true` implies `TarEquiv xs ys`. -/
theorem tarEquiv_of_tarEquivBool {xs ys : List TarEntry} (h : tarEquivBool xs ys = true) :
    TarEquiv xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => trivial
    | cons _ _ => cases h
  | cons a xs ih =>
    cases ys with
    | nil => cases h
    | cons b ys =>
      simp only [tarEquivBool, Bool.and_eq_true] at h
      exact ⟨h.1, ih h.2⟩

/-- Concrete helper certifying `checkRoundTripCase defaultApi` when concrete evaluation succeeds. -/
theorem checkRoundTripCase_of_eval {packOpts : PackOptions} {unpackOpts : UnpackOptions}
    {entries : List TarEntry}
    (h : (match defaultApi.packWith packOpts entries with
      | .error _ => false
      | .ok bytes =>
        match defaultApi.unpackWith unpackOpts bytes with
        | .error _ => false
        | .ok decoded =>
          let expected := if packOpts.deterministic then entries.map zeroDeterministicMeta else entries
          tarEquivBool expected decoded) = true) :
    AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries) := by
  cases hp : defaultApi.packWith packOpts entries with
  | error _ => simp [hp] at h
  | ok bytes =>
    cases hu : defaultApi.unpackWith unpackOpts bytes with
    | error _ => simp [hp, hu] at h
    | ok decoded =>
      simp only [hp, hu] at h
      dsimp [AllPass, checkRoundTripCase]
      rw [hp]
      dsimp only
      rw [hu]
      dsimp only [Bind.bind, Pure.pure, NondetTest.assert]
      exact ⟨tarEquiv_of_tarEquivBool h, trivial⟩

/-- Certify `checkRoundTripCase defaultApi` directly from `allPass_packUnpack_roundTrip`. -/
theorem checkRoundTripCase_of_valid {entries : List TarEntry} {packOpts : PackOptions}
    {unpackOpts : UnpackOptions}
    (hv : ValidArchive packOpts.allowAbsolute packOpts.allowParentTraversal entries)
    (ha : (!packOpts.allowAbsolute || unpackOpts.allowAbsolute) = true)
    (hp : (!packOpts.allowParentTraversal || unpackOpts.allowParentTraversal) = true)
    (hl : entries.length ≤ unpackOpts.maxEntries)
    (hb : totalDataBytes entries ≤ unpackOpts.maxTotalBytes)
    (hx : entries.all fitsPaxLimit = true) :
    AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries) :=
  allPass_packUnpack_roundTrip entries packOpts unpackOpts hv ha hp hl hb hx

end LeanSwe.Tar.Proofs
