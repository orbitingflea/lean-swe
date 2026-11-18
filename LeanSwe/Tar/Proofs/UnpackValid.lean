import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Distributivity of `totalDataBytes` over list append. -/
theorem totalDataBytes_append (a b : List TarEntry) :
    totalDataBytes (a ++ b) = totalDataBytes a + totalDataBytes b := by
  unfold totalDataBytes
  have hfold : ∀ (init : Nat) (xs : List TarEntry),
      xs.foldl (fun acc e => acc + e.data.size) init =
      init + xs.foldl (fun acc e => acc + e.data.size) 0 := by
    intro init xs
    induction xs generalizing init with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ih (init + x.data.size), ih x.data.size, Nat.add_assoc]
  rw [List.foldl_append, hfold _ b]

private theorem totalDataBytes_reverse (es : List TarEntry) :
    totalDataBytes es.reverse = totalDataBytes es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.reverse_cons, totalDataBytes_append, ih]
    have hcons : totalDataBytes (e :: rest) = e.data.size + totalDataBytes rest := by
      unfold totalDataBytes
      simp only [List.foldl_cons, Nat.zero_add]
      have hfold : ∀ (init : Nat) (xs : List TarEntry),
          xs.foldl (fun acc x => acc + x.data.size) init =
          init + xs.foldl (fun acc x => acc + x.data.size) 0 := by
        intro init xs
        induction xs generalizing init with
        | nil => simp
        | cons x xs ihx =>
          simp only [List.foldl_cons, Nat.zero_add]
          rw [ihx (init + x.data.size), ihx x.data.size, Nat.add_assoc]
      exact hfold e.data.size rest
    have hsingle : totalDataBytes [e] = e.data.size := by
      unfold totalDataBytes; simp
    rw [hcons, hsingle, Nat.add_comm]

private theorem noDupNormalizedPathsBool_go_iff_pairwise (seen : List String) (es : List TarEntry) :
    noDupNormalizedPathsBool.go seen es = true ↔
      (es.map (fun e => normalizeTarPath e.kind e.path)).Pairwise (· ≠ ·) ∧
      ∀ e ∈ es, normalizeTarPath e.kind e.path ∉ seen := by
  induction es generalizing seen with
  | nil =>
    simp [noDupNormalizedPathsBool.go.eq_1]
  | cons e rest ih =>
    rw [noDupNormalizedPathsBool.go.eq_2]
    let np := normalizeTarPath e.kind e.path
    cases hmem : seen.contains np with
    | true =>
      have hin : np ∈ seen := List.contains_iff_mem.mp hmem
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, false_iff]
      intro h
      exact h.2 e (by simp) hin
    | false =>
      have hnin : np ∉ seen := fun hin => by
        rw [List.contains_iff_mem.mpr hin] at hmem
        cases hmem
      have hnp_eq : np = normalizeTarPath e.kind e.path := rfl
      rw [Bool.not_false, Bool.true_and, ih (np :: seen)]
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · rintro ⟨hpw, hall⟩
        refine ⟨⟨?_, hpw⟩, ?_⟩
        · intro x hx
          rw [List.mem_map] at hx
          rcases hx with ⟨e', he', rfl⟩
          intro heq
          exact hall e' he' (by simp [← heq, hnp_eq])
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact hnin
          · exact fun hin => hall x hx_rest (by simp [hin])
      · rintro ⟨⟨hne, hpw⟩, hall⟩
        refine ⟨hpw, ?_⟩
        intro e' he' hmem'
        rcases List.mem_cons.mp hmem' with heq | hin_seen
        · exact hne _ (List.mem_map.mpr ⟨e', he', rfl⟩) heq.symm
        · exact hall e' (by simp [he']) hin_seen

private theorem fromUTF8?_eq_some_toUTF8 {bs : ByteArray} {s : String}
    (h : String.fromUTF8? bs = some s) : s.toUTF8 = bs := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

private theorem extractCStringBytes_no_zero (bytes : ByteArray) (start stop : Nat)
    {j : Nat} (hj : j < (extractCStringBytes bytes start stop).size) :
    (extractCStringBytes bytes start stop)[j]'hj ≠ 0 := by
  have hfind : ∀ rem i, rem + i = stop → start ≤ i →
      (∀ k, start ≤ k → k < i → ∀ hk : k < bytes.size, bytes[k]'hk ≠ 0) →
      extractCStringBytes.findNul bytes stop rem i ≤ stop ∧
      (∀ k, start ≤ k → k < extractCStringBytes.findNul bytes stop rem i → ∀ hk : k < bytes.size, bytes[k]'hk ≠ 0) := by
    intro rem
    induction rem with
    | zero =>
      intro i hsum hsi hk
      rw [extractCStringBytes.findNul.eq_1]
      exact ⟨by omega, fun k hk1 hk2 hkbd => hk k hk1 (by omega) hkbd⟩
    | succ d ih =>
      intro i hsum hsi hk
      rw [extractCStringBytes.findNul.eq_2]
      split
      · rename_i hbd
        split
        · exact ⟨by omega, fun k hk1 hk2 hkbd => hk k hk1 (by omega) hkbd⟩
        · rename_i hnz
          refine ih (i + 1) (by omega) (by omega) ?_
          intro k hk1 hk2 hkbd
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hlt | rfl
          · exact hk k hk1 hlt hkbd
          · exact fun heq => hnz (beq_iff_eq.mpr heq)
      · exact ⟨by omega, fun k hk1 hk2 hkbd => hk k hk1 (by omega) hkbd⟩
  have hss : start ≤ stop := by
    by_cases hle : start ≤ stop
    · exact hle
    · exfalso
      have h0 : stop - start = 0 := by omega
      have hj' := hj
      unfold extractCStringBytes at hj'
      rw [h0, extractCStringBytes.findNul.eq_1, ByteArray.size_extract] at hj'
      omega
  have hprop := hfind (stop - start) start (by omega) (Nat.le_refl _) (fun k hk1 hk2 _ => absurd hk2 (Nat.not_lt_of_ge hk1))
  unfold extractCStringBytes at hj ⊢
  rw [ByteArray.getElem_extract]
  have hbd : start + j < bytes.size := by
    rw [ByteArray.size_extract] at hj
    omega
  have hlt : start + j < extractCStringBytes.findNul bytes stop (stop - start) start := by
    rw [ByteArray.size_extract] at hj
    omega
  exact hprop.2 (start + j) (Nat.le_add_right _ _) hlt hbd

private theorem decodeCStringUtf8_not_hasNul {bytes : ByteArray} {start stop offset : Nat}
    {fieldName s : String} (h : decodeCStringUtf8 bytes start stop offset fieldName = .ok s) :
    !hasNulString s = true := by
  unfold decodeCStringUtf8 at h
  dsimp only at h
  cases hf : String.fromUTF8? (extractCStringBytes bytes start stop) with
  | none => rw [hf] at h; cases h
  | some s' =>
    rw [hf] at h; cases h
    have hs_utf8 : s.toUTF8 = extractCStringBytes bytes start stop := fromUTF8?_eq_some_toUTF8 hf
    cases hnul : hasNulString s
    · simp
    · exfalso
      have h0_mem : (0 : UInt8) ∈ s.toUTF8.toList := by
        have hmem_chars : Char.ofNat 0 ∈ s.toList := by
          unfold hasNulString at hnul
          revert hnul
          generalize s.toList = cs
          intro hnul
          induction cs with
          | nil => cases hnul
          | cons c cs ih =>
            rw [hasNulChars.eq_2] at hnul
            rcases Bool.or_eq_true_iff.mp hnul with hbeq | hrest
            · exact List.mem_cons.mpr (Or.inl (beq_iff_eq.mp hbeq).symm)
            · exact List.mem_cons_of_mem c (ih hrest)
        rw [toUTF8_toList, List.mem_flatMap]
        refine ⟨Char.ofNat 0, hmem_chars, ?_⟩
        decide
      rw [hs_utf8, byteArray_toList_eq] at h0_mem
      have ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp h0_mem
      have hj' : j < (extractCStringBytes bytes start stop).size := hj
      have hget' : (extractCStringBytes bytes start stop)[j]'hj' = 0 := by
        simpa [ByteArray.getElem_eq_getElem_data] using hget
      exact extractCStringBytes_no_zero bytes start stop hj' hget'

private theorem decodeTarEntry_valid (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (hdr : UstarHeaderFields) (pendingPax : Option PaxOverrides)
    (seen : List String) (accLen totalBytes : Nat) (entry : TarEntry) (padded : Nat)
    (hpax_ok : ∀ ov, pendingPax = some ov →
      (!hasNulString (ov.uname?.getD "") = true) ∧
      (!hasNulString (ov.gname?.getD "") = true) ∧
      (∀ n, ov.uid? = some n → n < u64Limit) ∧
      (∀ n, ov.gid? = some n → n < u64Limit) ∧
      (∀ n, ov.size? = some n → n < u64Limit) ∧
      (∀ n, ov.mtime? = some n → n < u64Limit))
    (hhdr_ok : hdr.uid < u64Limit ∧ hdr.gid < u64Limit ∧ hdr.size < u64Limit ∧ hdr.mtime < u64Limit)
    (hdec : decodeTarEntry opts bytes offset hdr pendingPax seen accLen totalBytes = .ok (entry, padded)) :
    validEntryBool opts.allowAbsolute opts.allowParentTraversal entry = true ∧
    normalizeTarPath entry.kind entry.path = entry.path ∧
    !seen.contains entry.path = true ∧
    accLen + 1 ≤ opts.maxEntries ∧
    totalBytes + entry.data.size ≤ opts.maxTotalBytes ∧
    entry.data.size ≤ padded := by
  unfold decodeTarEntry at hdec
  dsimp only at hdec
  split at hdec
  · cases hdec
  · rename_i kind hkind?
    split at hdec
    · cases hdec
    · split at hdec
      · cases hdec
      · split at hdec
        · cases hdec
        · split at hdec
          · cases hdec
          · rename_i hne_nonreg hmax_e hmax_b hno_trunc
            split at hdec
            · cases hdec
            · cases hdec
            · cases hdec
            · cases hdec
            · rename_i rawPath rawLink uname gname hpath_res hlink_res huname hgname
              cases hval : validateEntryPath opts.allowAbsolute opts.allowParentTraversal kind rawPath with
              | error _ => rw [hval] at hdec; cases hdec
              | ok normPath =>
                rw [hval] at hdec
                dsimp only at hdec
                have hsym : (match kind with
                    | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath rawLink
                    | .regular | .directory => Except.ok ()) = .ok () := by
                  cases hk : kind <;> simp only [hk] at hdec ⊢
                  cases hs : validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath rawLink with
                  | error _ => rw [hs] at hdec; cases hdec
                  | ok _ => rfl
                have hseen_f : seen.contains normPath = false := by
                  cases hk : kind <;> simp only [hk] at hdec
                  · split at hdec
                    · cases hdec
                    · exact Bool.eq_false_iff.mpr (by assumption)
                  · split at hdec
                    · cases hdec
                    · exact Bool.eq_false_iff.mpr (by assumption)
                  · simp only [hk] at hsym
                    simp only [hsym] at hdec
                    split at hdec
                    · cases hdec
                    · exact Bool.eq_false_iff.mpr (by assumption)
                have hdec_body : entry = {
                    path := normPath,
                    kind := kind,
                    mode := (hdr.mode &&& 0o7777).toUInt32,
                    uid := (pendingPax.getD {}).uid?.getD hdr.uid,
                    gid := (pendingPax.getD {}).gid?.getD hdr.gid,
                    mtime := (pendingPax.getD {}).mtime?.getD hdr.mtime,
                    uname := uname,
                    gname := gname,
                    data := if (pendingPax.getD {}).size?.getD hdr.size == 0 then ByteArray.empty
                            else bytes.extract (offset + 512) (offset + 512 + (pendingPax.getD {}).size?.getD hdr.size),
                    linkTarget := rawLink } ∧
                    padded = pad512 ((pendingPax.getD {}).size?.getD hdr.size) := by
                  cases hk : kind <;> simp only [hk] at hdec hsym
                  · simp only [hseen_f, Bool.false_eq_true, ↓reduceIte] at hdec; cases hdec; exact ⟨rfl, rfl⟩
                  · simp only [hseen_f, Bool.false_eq_true, ↓reduceIte] at hdec; cases hdec; exact ⟨rfl, rfl⟩
                  · simp only [hsym, hseen_f, Bool.false_eq_true, ↓reduceIte] at hdec; cases hdec; exact ⟨rfl, rfl⟩
                rcases hdec_body with ⟨rfl, rfl⟩
                dsimp only
                let pax := pendingPax.getD {}
                let effSize := pax.size?.getD hdr.size
                have hpax_uid : pax.uid?.getD hdr.uid < u64Limit := by
                  cases pendingPax with
                  | none => simp [pax]; exact hhdr_ok.1
                  | some ov =>
                    have hov := hpax_ok ov rfl
                    cases h : ov.uid? with
                    | none => simp [pax, h]; exact hhdr_ok.1
                    | some n => simp [pax, h]; exact hov.2.2.1 n h
                have hpax_gid : pax.gid?.getD hdr.gid < u64Limit := by
                  cases pendingPax with
                  | none => simp [pax]; exact hhdr_ok.2.1
                  | some ov =>
                    have hov := hpax_ok ov rfl
                    cases h : ov.gid? with
                    | none => simp [pax, h]; exact hhdr_ok.2.1
                    | some n => simp [pax, h]; exact hov.2.2.2.1 n h
                have hpax_size : effSize < u64Limit := by
                  cases pendingPax with
                  | none => simp [effSize, pax]; exact hhdr_ok.2.2.1
                  | some ov =>
                    have hov := hpax_ok ov rfl
                    cases h : ov.size? with
                    | none => simp [effSize, pax, h]; exact hhdr_ok.2.2.1
                    | some n => simp [effSize, pax, h]; exact hov.2.2.2.2.1 n h
                have hpax_mtime : pax.mtime?.getD hdr.mtime < u64Limit := by
                  cases pendingPax with
                  | none => simp [pax]; exact hhdr_ok.2.2.2
                  | some ov =>
                    have hov := hpax_ok ov rfl
                    cases h : ov.mtime? with
                    | none => simp [pax, h]; exact hhdr_ok.2.2.2
                    | some n => simp [pax, h]; exact hov.2.2.2.2.2 n h
                have hnul_u : (!hasNulString uname) = true := by
                  cases hu : pax.uname? with
                  | none =>
                    have hdec : decodeCStringUtf8 bytes (offset + 265) (offset + 297) offset "uname" = .ok uname := by
                      dsimp only [pax] at hu
                      simpa [hu] using huname
                    simpa using decodeCStringUtf8_not_hasNul hdec
                  | some u =>
                    have hu_eq : u = uname := by
                      dsimp only [pax] at hu
                      simpa [hu] using huname
                    subst hu_eq
                    cases hpp : pendingPax with
                    | none => simp [pax, hpp] at hu
                    | some ov =>
                      have hov := hpax_ok ov hpp
                      dsimp only [pax] at hu
                      simp only [hpp, Option.getD_some] at hu
                      simpa [hu] using hov.1
                have hnul_g : (!hasNulString gname) = true := by
                  cases hg : pax.gname? with
                  | none =>
                    have hdec : decodeCStringUtf8 bytes (offset + 297) (offset + 329) offset "gname" = .ok gname := by
                      dsimp only [pax] at hg
                      simpa [hg] using hgname
                    simpa using decodeCStringUtf8_not_hasNul hdec
                  | some g =>
                    have hg_eq : g = gname := by
                      dsimp only [pax] at hg
                      simpa [hg] using hgname
                    subst hg_eq
                    cases hpp : pendingPax with
                    | none => simp [pax, hpp] at hg
                    | some ov =>
                      have hov := hpax_ok ov hpp
                      dsimp only [pax] at hg
                      simp only [hpp, Option.getD_some] at hg
                      simpa [hg] using hov.2.1
                have hle_pad : effSize ≤ pad512 effSize := le_pad512 effSize
                have hpay_sz : (if effSize == 0 then ByteArray.empty
                    else bytes.extract (offset + 512) (offset + 512 + effSize)).size = effSize := by
                  have hle_pad' : (pendingPax.getD {}).size?.getD hdr.size ≤
                      pad512 ((pendingPax.getD {}).size?.getD hdr.size) := le_pad512 _
                  dsimp only [effSize, pax]
                  by_cases hz : (pendingPax.getD {}).size?.getD hdr.size = 0
                  · simp [hz]
                  · have hbeq : ((pendingPax.getD {}).size?.getD hdr.size == 0) = false :=
                      Bool.eq_false_iff.mpr (by simpa using hz)
                    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, ByteArray.size_extract]
                    omega
                have hle_e : accLen + 1 ≤ opts.maxEntries := by omega
                have hle_b : totalBytes + effSize ≤ opts.maxTotalBytes := by
                  dsimp only [effSize, pax]; omega
                have hnot_seen' : (!seen.contains normPath) = true := by
                  rw [hseen_f]; rfl
                have ⟨hid, hnorm_id, _⟩ := validateEntryPath_idemp hval
                have hve : validEntryBool opts.allowAbsolute opts.allowParentTraversal
                    { path := normPath, kind := kind, mode := (hdr.mode &&& 0o7777).toUInt32
                    , uid := pax.uid?.getD hdr.uid, gid := pax.gid?.getD hdr.gid
                    , mtime := pax.mtime?.getD hdr.mtime, uname := uname, gname := gname
                    , data := if effSize == 0 then ByteArray.empty else bytes.extract (offset + 512) (offset + 512 + effSize)
                    , linkTarget := rawLink } = true := by
                  unfold validEntryBool
                  rw [hid]
                  dsimp only
                  simp only [Bool.and_eq_true]
                  refine ⟨⟨?_, ?_⟩, ?_⟩
                  · cases hk : kind <;> simp only [hk] at hsym hlink_res ⊢
                    · cases hlink_res; rfl
                    · cases hlink_res; rfl
                    · rw [hsym]
                  · cases hk : kind <;> simp only [hk] at hne_nonreg ⊢
                    · have heff0 : effSize = 0 := by
                        dsimp only [effSize, pax]
                        cases hz : ((pendingPax.getD {}).size?.getD hdr.size == 0)
                        · exfalso; apply hne_nonreg
                          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
                          exact ⟨by decide, fun h0 => by simp [h0] at hz⟩
                        · exact beq_iff_eq.mp hz
                      rw [hpay_sz, heff0]; rfl
                    · have heff0 : effSize = 0 := by
                        dsimp only [effSize, pax]
                        cases hz : ((pendingPax.getD {}).size?.getD hdr.size == 0)
                        · exfalso; apply hne_nonreg
                          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
                          exact ⟨by decide, fun h0 => by simp [h0] at hz⟩
                        · exact beq_iff_eq.mp hz
                      rw [hpay_sz, heff0]; rfl
                  · simp only [hnul_u, hnul_g, hpay_sz, decide_eq_true_eq,
                      hpax_uid, hpax_gid, hpax_mtime, hpax_size, and_self]
                refine ⟨hve, hnorm_id, ?_, hle_e, ?_, ?_⟩
                · simpa using hnot_seen'
                · rw [hpay_sz]; exact hle_b
                · rw [hpay_sz]; exact hle_pad

private theorem applyPaxKey_invariants (ov nextOv : PaxOverrides) (key val : String) (offset : Nat)
    (hov : (!hasNulString (ov.uname?.getD "") = true) ∧
      (!hasNulString (ov.gname?.getD "") = true) ∧
      (∀ n, ov.uid? = some n → n < u64Limit) ∧
      (∀ n, ov.gid? = some n → n < u64Limit) ∧
      (∀ n, ov.size? = some n → n < u64Limit) ∧
      (∀ n, ov.mtime? = some n → n < u64Limit))
    (happly : applyPaxKey ov key val offset = .ok nextOv) :
    (!hasNulString (nextOv.uname?.getD "") = true) ∧
    (!hasNulString (nextOv.gname?.getD "") = true) ∧
    (∀ n, nextOv.uid? = some n → n < u64Limit) ∧
    (∀ n, nextOv.gid? = some n → n < u64Limit) ∧
    (∀ n, nextOv.size? = some n → n < u64Limit) ∧
    (∀ n, nextOv.mtime? = some n → n < u64Limit) := by
  have hparseNat : ∀ key' n, parsePaxNat val offset key' = .ok n → n < u64Limit := by
    intro key' n hp
    unfold parsePaxNat at hp
    dsimp only at hp
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · split at hp
        · cases hp
        · split at hp
          · cases hp
          · cases hp; omega
  have hparseMtime : ∀ n, parsePaxMtime val offset = .ok n → n < u64Limit := by
    intro n hp
    unfold parsePaxMtime at hp
    dsimp only at hp
    split at hp; · cases hp
    split at hp; · cases hp
    split at hp; · cases hp
    split at hp
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
      split at hp <;> cases hp; omega
    · split at hp
      · cases hp
      · split at hp <;> cases hp; omega
    · simp at hp
  unfold applyPaxKey at happly
  split at happly
  · cases happly; exact hov
  · split at happly
    · cases happly; exact hov
    · split at happly
      · split at happly
        · cases happly
        · cases happly
          rename_i hnn
          exact ⟨by simp [hnn], hov.2⟩
      · split at happly
        · split at happly
          · cases happly
          · cases happly
            rename_i hnn
            exact ⟨hov.1, by simp [hnn], hov.2.2⟩
        · split at happly
          · simp only [Except.map] at happly
            split at happly
            · cases happly
            · cases happly
              rename_i n hn
              exact ⟨hov.1, hov.2.1, hov.2.2.1, hov.2.2.2.1,
                fun m hm => by cases hm; exact hparseNat "size" n hn, hov.2.2.2.2.2⟩
          · split at happly
            · simp only [Except.map] at happly
              split at happly
              · cases happly
              · cases happly
                rename_i n hn
                exact ⟨hov.1, hov.2.1, fun m hm => by cases hm; exact hparseNat "uid" n hn,
                  hov.2.2.2⟩
            · split at happly
              · simp only [Except.map] at happly
                split at happly
                · cases happly
                · cases happly
                  rename_i n hn
                  exact ⟨hov.1, hov.2.1, hov.2.2.1,
                    fun m hm => by cases hm; exact hparseNat "gid" n hn, hov.2.2.2.2⟩
              · split at happly
                · simp only [Except.map] at happly
                  split at happly
                  · cases happly
                  · cases happly
                    rename_i n hn
                    exact ⟨hov.1, hov.2.1, hov.2.2.1, hov.2.2.2.1, hov.2.2.2.2.1,
                      fun m hm => by cases hm; exact hparseMtime n hn⟩
                · cases happly; exact hov

/-- Validity invariant on parsed PAX overrides: NUL-free `uname`/`gname` and numeric bounds `< u64Limit`. -/
def PaxOverrides.Valid (ov : PaxOverrides) : Prop :=
  (!hasNulString (ov.uname?.getD "") = true) ∧
  (!hasNulString (ov.gname?.getD "") = true) ∧
  (∀ n, ov.uid? = some n → n < u64Limit) ∧
  (∀ n, ov.gid? = some n → n < u64Limit) ∧
  (∀ n, ov.size? = some n → n < u64Limit) ∧
  (∀ n, ov.mtime? = some n → n < u64Limit)

private theorem parsePaxPayload_go_invariants (pax : ByteArray) (offset rem pos : Nat)
    (seenKeys : List String) (ov resOv : PaxOverrides)
    (hov : PaxOverrides.Valid ov)
    (hpax : parsePaxPayload.go pax offset rem pos seenKeys ov = .ok resOv) :
    PaxOverrides.Valid resOv := by
  fun_induction parsePaxPayload.go pax offset rem pos seenKeys ov with
  | case1 => cases hpax; exact hov
  | case2 => cases hpax; exact hov
  | _ =>
    first
    | cases hpax
    | (rename_i happly ih; exact ih (applyPaxKey_invariants _ _ _ _ _ hov happly) hpax)

private theorem parseUstarNumeric_lt (bytes : ByteArray) (start stop offset : Nat)
    (allowAllEmpty : Bool) (limit : Nat) (fieldName : String) (val : Nat)
    (hlim : 0 < limit) (h : parseUstarNumeric bytes start stop offset allowAllEmpty limit fieldName = .ok val) :
    val < limit := by
  unfold parseUstarNumeric at h
  dsimp only at h
  cases hraw : (bytes.extract start stop).data.toList with
  | nil => rw [hraw] at h; cases h
  | cons b0 rest =>
    rw [hraw] at h
    dsimp only at h
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; omega
    · split at h
      · split at h
        · cases h; exact hlim
        · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · cases h; omega

private theorem parseUstarHeader_u64 (bytes : ByteArray) (offset : Nat) (hdr : UstarHeaderFields)
    (h : parseUstarHeader bytes offset = .ok hdr) :
    hdr.uid < u64Limit ∧ hdr.gid < u64Limit ∧ hdr.size < u64Limit ∧ hdr.mtime < u64Limit := by
  unfold parseUstarHeader at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, MonadExcept.throw] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hmode
          split at h
          · cases h
          · rename_i huid
            split at h
            · cases h
            · rename_i hgid
              split at h
              · cases h
              · rename_i hsize
                split at h
                · cases h
                · rename_i hmtime
                  cases h
                  have hpos : 0 < u64Limit := by decide
                  exact ⟨parseUstarNumeric_lt _ _ _ _ _ _ _ _ hpos huid,
                    parseUstarNumeric_lt _ _ _ _ _ _ _ _ hpos hgid,
                    parseUstarNumeric_lt _ _ _ _ _ _ _ _ hpos hsize,
                    parseUstarNumeric_lt _ _ _ _ _ _ _ _ hpos hmtime⟩

private theorem unpackLoopFuel_valid (fuel : Nat) (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) (res : List TarEntry)
    (hpax_ok : ∀ ov, pendingPax = some ov → PaxOverrides.Valid ov)
    (hacc_valid : ∀ e ∈ acc, validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true)
    (hseen_eq : seen = acc.map (fun e => normalizeTarPath e.kind e.path))
    (hacc_pw : (acc.map (fun e => normalizeTarPath e.kind e.path)).Pairwise (· ≠ ·))
    (hacc_len : acc.length ≤ opts.maxEntries)
    (htot_eq : totalDataBytes acc = totalBytes)
    (htot_le : totalBytes ≤ opts.maxTotalBytes)
    (hrun : unpackLoopFuel fuel opts bytes offset pendingPax seen acc totalBytes = .ok res) :
    ValidArchive opts.allowAbsolute opts.allowParentTraversal res ∧
    res.length ≤ opts.maxEntries ∧
    totalDataBytes res ≤ opts.maxTotalBytes := by
  induction fuel generalizing offset pendingPax seen acc totalBytes with
  | zero => rw [unpackLoopFuel.eq_1] at hrun; cases hrun
  | succ fuel' ih =>
    rw [unpackLoopFuel.eq_2] at hrun
    split at hrun
    · cases hrun
    · cases hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes with
      | error _ => rw [hstep] at hrun; cases hrun
      | ok step =>
        cases step with
        | done resDone =>
          simp only [hstep] at hrun
          unfold unpackStep at hstep
          split at hstep
          · cases hstep
          · split at hstep
            · split at hstep
              · cases hstep
              · split at hstep
                · cases hstep
                · split at hstep
                  · cases hstep
                  · split at hstep
                    · cases hstep
                    · cases hstep
                      cases hrun
                      refine ⟨?_, ?_, ?_⟩
                      · unfold ValidArchive validArchiveBool
                        rw [Bool.and_eq_true, List.all_eq_true, noDupNormalizedPathsBool,
                          noDupNormalizedPathsBool_go_iff_pairwise]
                        refine ⟨fun e he => hacc_valid e (List.mem_reverse.mp he), ?_, fun _ h _ => by contradiction⟩
                        rw [List.map_reverse, List.pairwise_reverse]
                        refine List.Pairwise.imp (fun {a b} hne => hne.symm) hacc_pw
                      · simpa using hacc_len
                      · rw [totalDataBytes_reverse, htot_eq]; exact htot_le
            · split at hstep
              · cases hstep
              · split at hstep
                · cases hstep
                · split at hstep
                  · by_cases hps : pendingPax.isSome = true
                    · simp [hps] at hstep
                    · simp only [hps, Bool.false_eq_true, ↓reduceIte] at hstep
                      split at hstep
                      · cases hstep
                      · split at hstep
                        · cases hstep
                        · split at hstep <;> cases hstep
                  · split at hstep
                    · cases hstep
                    · cases hstep
        | cont nextOffset nextPax nextSeen nextAcc nextTotal =>
          simp only [hstep] at hrun
          split at hrun
          · unfold unpackStep at hstep
            split at hstep
            · cases hstep
            · split at hstep
              · split at hstep
                · cases hstep
                · split at hstep
                  · cases hstep
                  · split at hstep
                    · cases hstep
                    · split at hstep
                      · cases hstep
                      · cases hstep
              · split at hstep
                · cases hstep
                · split at hstep
                  · cases hstep
                  · rename_i hparse_hdr
                    split at hstep
                    · split at hstep
                      · cases hstep
                      · split at hstep
                        · cases hstep
                        · dsimp only at hstep
                          split at hstep
                          · cases hstep
                          · split at hstep
                            · cases hstep
                            · rename_i hpax_parse
                              cases hstep
                              have hpax_empty : PaxOverrides.Valid {} := by
                                simp [PaxOverrides.Valid, hasNulString, hasNulChars]
                              have hpax_res := parsePaxPayload_go_invariants _ _ _ _ _ _ _ hpax_empty hpax_parse
                              exact ih _ _ _ _ _ (fun ov hov => by cases hov; exact hpax_res)
                                hacc_valid hseen_eq hacc_pw hacc_len htot_eq htot_le hrun
                    · split at hstep
                      · cases hstep
                      · rename_i entry padded hdec
                        cases hstep
                        have hhdr_ok := parseUstarHeader_u64 _ _ _ hparse_hdr
                        have ⟨hve, hnorm_id, hnot_seen, hle_e, hle_b, _⟩ :=
                          decodeTarEntry_valid opts bytes offset _ pendingPax seen acc.length totalBytes
                            entry padded hpax_ok hhdr_ok hdec
                        have hacc_valid' : ∀ e ∈ entry :: acc, validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true := by
                          intro e he
                          rcases List.mem_cons.mp he with rfl | he_acc
                          · exact hve
                          · exact hacc_valid e he_acc
                        have hseen_eq' : (entry.path :: seen) =
                            (entry :: acc).map (fun e => normalizeTarPath e.kind e.path) := by
                          simp [hnorm_id, hseen_eq]
                        have hacc_pw' : ((entry :: acc).map (fun e => normalizeTarPath e.kind e.path)).Pairwise (· ≠ ·) := by
                          simp only [List.map_cons, List.pairwise_cons, hnorm_id]
                          refine ⟨?_, hacc_pw⟩
                          intro x hx heq
                          rw [← hseen_eq] at hx
                          have hc := List.contains_iff_mem.mpr (heq ▸ hx)
                          rw [hc] at hnot_seen
                          cases hnot_seen
                        have htot_eq' : totalDataBytes (entry :: acc) = totalBytes + entry.data.size := by
                          unfold totalDataBytes
                          simp only [List.foldl_cons, Nat.zero_add]
                          have hfold : ∀ (init : Nat) (xs : List TarEntry),
                              xs.foldl (fun a x => a + x.data.size) init =
                              init + xs.foldl (fun a x => a + x.data.size) 0 := by
                            intro init xs
                            induction xs generalizing init with
                            | nil => simp
                            | cons x xs ihx =>
                              simp only [List.foldl_cons, Nat.zero_add]
                              rw [ihx (init + x.data.size), ihx x.data.size, Nat.add_assoc]
                          rw [hfold entry.data.size acc]
                          have hacc_tot : acc.foldl (fun a x => a + x.data.size) 0 = totalBytes := htot_eq
                          omega
                        exact ih _ _ _ _ _ (fun ov hov => by cases hov) hacc_valid' hseen_eq' hacc_pw' hle_e htot_eq' hle_b hrun
          · cases hrun

/-- Prove `test_tar_unpackWith_returnsValidArchiveWithinLimits` for `defaultApi`. -/
theorem allPass_unpackWith_returnsValidArchiveWithinLimits :
    AllPass (test_tar_unpackWith_returnsValidArchiveWithinLimits defaultApi) := by
  dsimp [AllPass, test_tar_unpackWith_returnsValidArchiveWithinLimits, Bind.bind, Pure.pure,
    NondetTest.nondet, NondetTest.assert, defaultApi, makeTarApi]
  intro opts bytes
  cases h : Impl.unpackWith opts bytes with
  | error _ => trivial
  | ok entries =>
    unfold Impl.unpackWith at h
    split at h
    · cases h
    · unfold unpackLoop at h
      have ⟨hv, hl, ht⟩ := unpackLoopFuel_valid (bytes.size - 0 + 1) opts bytes 0 none [] [] 0 entries
        (fun _ hov => by cases hov) (fun _ hmem => by contradiction) rfl
        List.Pairwise.nil (Nat.zero_le _) rfl (Nat.zero_le _) h
      exact ⟨hv, hl, ht, trivial⟩


end LeanSwe.Tar.Proofs
