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

private theorem totalDataBytes_foldl (init : Nat) (xs : List TarEntry) :
    xs.foldl (fun acc e => acc + e.data.size) init = init + totalDataBytes xs := by
  induction xs generalizing init with
  | nil => simp [totalDataBytes]
  | cons x xs ih =>
    simp only [totalDataBytes, List.foldl_cons, Nat.zero_add] at ih ⊢
    rw [ih (init + x.data.size), ih x.data.size, Nat.add_assoc]

private theorem totalDataBytes_cons (e : TarEntry) (xs : List TarEntry) :
    totalDataBytes (e :: xs) = e.data.size + totalDataBytes xs := by
  unfold totalDataBytes; rw [List.foldl_cons, Nat.zero_add]; exact totalDataBytes_foldl _ _

/-- Distributivity of `totalDataBytes` over list append. -/
theorem totalDataBytes_append (a b : List TarEntry) :
    totalDataBytes (a ++ b) = totalDataBytes a + totalDataBytes b := by
  unfold totalDataBytes; rw [List.foldl_append]; exact totalDataBytes_foldl _ b

private theorem totalDataBytes_reverse (es : List TarEntry) :
    totalDataBytes es.reverse = totalDataBytes es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have h0 : totalDataBytes [] = 0 := rfl
    rw [List.reverse_cons, totalDataBytes_append, ih, totalDataBytes_cons, totalDataBytes_cons, h0]
    omega

private theorem noDup_go_snoc (seen : List String) (xs : List TarEntry) (e : TarEntry) :
    noDupNormalizedPathsBool.go seen (xs ++ [e]) =
      (noDupNormalizedPathsBool.go seen xs &&
        !(xs.reverse.map (fun x => normalizeTarPath x.kind x.path) ++ seen).contains
          (normalizeTarPath e.kind e.path)) := by
  induction xs generalizing seen with
  | nil => simp [noDupNormalizedPathsBool.go]
  | cons x xs ih =>
    simp only [List.cons_append, noDupNormalizedPathsBool.go, ih, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.nil_append,
      Bool.and_assoc]

private theorem extractCStringBytes_no_zero (bytes : ByteArray) (start stop : Nat)
    {j : Nat} (hj : j < (extractCStringBytes bytes start stop).size) :
    (extractCStringBytes bytes start stop)[j]'hj ≠ 0 := by
  have hfind : ∀ rem i, rem + i = stop → start ≤ i →
      (∀ k, start ≤ k → k < i → ∀ hk : k < bytes.size, bytes[k]'hk ≠ 0) →
      extractCStringBytes.findNul bytes stop rem i ≤ stop ∧
      (∀ k, start ≤ k → k < extractCStringBytes.findNul bytes stop rem i →
        ∀ hk : k < bytes.size, bytes[k]'hk ≠ 0) := by
    intro rem; induction rem with
    | zero =>
      intro i _ _ hk; rw [extractCStringBytes.findNul.eq_1]
      exact ⟨by omega, fun k hk1 hk2 hkbd => hk k hk1 (by omega) hkbd⟩
    | succ d ih =>
      intro i _ _ hk; rw [extractCStringBytes.findNul.eq_2]
      split
      · split
        · exact ⟨by omega, fun k hk1 hk2 hkbd => hk k hk1 (by omega) hkbd⟩
        · rename_i hnz
          refine ih (i + 1) (by omega) (by omega) fun k hk1 hk2 hkbd => ?_
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk2) with hlt | rfl
          · exact hk k hk1 hlt hkbd
          · exact fun heq => hnz (beq_iff_eq.mpr heq)
      · exact ⟨by omega, fun k hk1 hk2 hkbd => hk k hk1 (by omega) hkbd⟩
  have hss : start ≤ stop := by
    by_cases hle : start ≤ stop; · exact hle
    exfalso; have h0 : stop - start = 0 := by omega
    unfold extractCStringBytes at hj
    rw [h0, extractCStringBytes.findNul.eq_1, ByteArray.size_extract] at hj; omega
  have hprop := hfind (stop - start) start (by omega) (Nat.le_refl _)
    (fun _ hk1 hk2 _ => absurd hk2 (Nat.not_lt_of_ge hk1))
  unfold extractCStringBytes at hj ⊢
  rw [ByteArray.getElem_extract]
  rw [ByteArray.size_extract] at hj
  exact hprop.2 (start + j) (Nat.le_add_right _ _) (by omega) (by omega)

private theorem decodeCStringUtf8_not_hasNul {bytes : ByteArray} {start stop offset : Nat}
    {fieldName s : String} (h : decodeCStringUtf8 bytes start stop offset fieldName = .ok s) :
    (!hasNulString s) = true := by
  unfold decodeCStringUtf8 at h; dsimp only at h
  cases hf : String.fromUTF8? (extractCStringBytes bytes start stop) with
  | none => rw [hf] at h; cases h
  | some s' =>
    rw [hf] at h; cases h
    have hs_utf8 : s.toUTF8 = extractCStringBytes bytes start stop := by
      unfold String.fromUTF8? at hf; split at hf <;> cases hf; rfl
    cases hnul : hasNulString s
    · rfl
    · exfalso
      have hmem_chars : Char.ofNat 0 ∈ s.toList :=
        Classical.not_not.mp (mt (hasNulChars_false_iff s.toList).mpr (by simp [hasNulString] at hnul; simp [hnul]))
      have h0_mem : (0 : UInt8) ∈ s.toUTF8.toList := by
        rw [toUTF8_toList, List.mem_flatMap]; exact ⟨Char.ofNat 0, hmem_chars, by decide⟩
      rw [hs_utf8, byteArray_toList_eq] at h0_mem
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp h0_mem
      exact extractCStringBytes_no_zero bytes start stop hj
        (by simpa [ByteArray.getElem_eq_getElem_data] using hget)

/-- Validity invariant on parsed PAX overrides: NUL-free `uname`/`gname` and numeric bounds `< u64Limit`. -/
structure PaxOverrides.Valid (ov : PaxOverrides) : Prop where
  /-- Overridden `uname` contains no NUL characters. -/
  uname_ok : (!hasNulString (ov.uname?.getD "")) = true
  /-- Overridden `gname` contains no NUL characters. -/
  gname_ok : (!hasNulString (ov.gname?.getD "")) = true
  /-- Overridden `uid` is `< 2^64`. -/
  uid_ok : ∀ n, ov.uid? = some n → n < u64Limit
  /-- Overridden `gid` is `< 2^64`. -/
  gid_ok : ∀ n, ov.gid? = some n → n < u64Limit
  /-- Overridden `size` is `< 2^64`. -/
  size_ok : ∀ n, ov.size? = some n → n < u64Limit
  /-- Overridden `mtime` is `< 2^64`. -/
  mtime_ok : ∀ n, ov.mtime? = some n → n < u64Limit

private theorem paxValid_empty : PaxOverrides.Valid {} :=
  ⟨by decide, by decide, by simp, by simp, by simp, by simp⟩

private theorem applyPaxKey_valid {ov nextOv : PaxOverrides} {key val : String} {offset : Nat}
    (hov : PaxOverrides.Valid ov) (h : applyPaxKey ov key val offset = .ok nextOv) :
    PaxOverrides.Valid nextOv := by
  have hNat : ∀ k n, parsePaxNat val offset k = .ok n → n < u64Limit := by
    intro k n hp; unfold parsePaxNat at hp; dsimp only at hp
    iterate 4 (split at hp; · cases hp)
    cases hp; omega
  have hMtime : ∀ n, parsePaxMtime val offset = .ok n → n < u64Limit := by
    intro n hp; unfold parsePaxMtime at hp; dsimp only at hp
    iterate 3 (split at hp; · cases hp)
    have htail : ∀ (fok : Bool) (m : Nat),
        (if !fok then Except.error ({ kind := .invalidHeader, message := "malformed PAX mtime fraction", offset := some offset } : TarError)
         else if m ≥ u64Limit then Except.error ({ kind := .sizeOverflow, message := "PAX mtime overflows 2^64", offset := some offset } : TarError)
         else Except.ok m) = .ok n → n < u64Limit := by
      intro fok m hm; cases fok
      · cases hm
      · by_cases hm_ge : m ≥ u64Limit <;> simp [hm_ge] at hm; omega
    exact htail _ _ hp
  unfold applyPaxKey at h
  split at h; · (cases h; exact ⟨hov.1, hov.2, hov.3, hov.4, hov.5, hov.6⟩)
  split at h; · (cases h; exact ⟨hov.1, hov.2, hov.3, hov.4, hov.5, hov.6⟩)
  split at h
  · split at h; · cases h
    cases h; exact ⟨by simp [Bool.eq_false_iff.mpr ‹_›], hov.2, hov.3, hov.4, hov.5, hov.6⟩
  split at h
  · split at h; · cases h
    cases h; exact ⟨hov.1, by simp [Bool.eq_false_iff.mpr ‹_›], hov.3, hov.4, hov.5, hov.6⟩
  split at h
  · simp only [Except.map] at h; split at h; · cases h
    cases h; exact ⟨hov.1, hov.2, hov.3, hov.4, fun _ hm => by cases hm; exact hNat _ _ ‹_›, hov.6⟩
  split at h
  · simp only [Except.map] at h; split at h; · cases h
    cases h; exact ⟨hov.1, hov.2, fun _ hm => by cases hm; exact hNat _ _ ‹_›, hov.4, hov.5, hov.6⟩
  split at h
  · simp only [Except.map] at h; split at h; · cases h
    cases h; exact ⟨hov.1, hov.2, hov.3, fun _ hm => by cases hm; exact hNat _ _ ‹_›, hov.5, hov.6⟩
  split at h
  · simp only [Except.map] at h; split at h; · cases h
    cases h; exact ⟨hov.1, hov.2, hov.3, hov.4, hov.5, fun _ hm => by cases hm; exact hMtime _ ‹_›⟩
  · cases h; exact hov

private theorem parsePaxPayload_go_valid {pax : ByteArray} {offset rem pos : Nat}
    {seenKeys : List String} {ov resOv : PaxOverrides}
    (hov : PaxOverrides.Valid ov)
    (hpax : parsePaxPayload.go pax offset rem pos seenKeys ov = .ok resOv) :
    PaxOverrides.Valid resOv := by
  fun_induction parsePaxPayload.go pax offset rem pos seenKeys ov with
  | case1 => cases hpax; exact hov
  | case2 => cases hpax; exact hov
  | _ =>
    first
    | cases hpax
    | (rename_i happly ih; exact ih (applyPaxKey_valid hov happly) hpax)

private theorem parseUstarNumeric_lt {bytes : ByteArray} {start stop offset : Nat}
    {allowAllEmpty : Bool} {limit : Nat} {fieldName : String} {val : Nat}
    (hlim : 0 < limit) (h : parseUstarNumeric bytes start stop offset allowAllEmpty limit fieldName = .ok val) :
    val < limit := by
  unfold parseUstarNumeric at h; dsimp only at h
  cases hraw : (bytes.extract start stop).data.toList with
  | nil => rw [hraw] at h; cases h
  | cons b0 rest =>
    rw [hraw] at h; dsimp only at h
    split at h
    · split at h; · cases h
      split at h <;> cases h; omega
    · split at h
      · split at h <;> cases h; exact hlim
      · iterate 3 (split at h; · cases h)
        cases h; omega

private theorem error_bind_eq {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

private theorem ite_err_eq_ok {ε α} {p : Prop} [Decidable p] {err : ε} {rest : Except ε α} {v : α} :
    (if p then Except.error err else rest) = .ok v ↔ ¬p ∧ rest = .ok v := by
  split <;> simp_all

private theorem parseUstarHeader_u64 {bytes : ByteArray} {offset : Nat} {hdr : UstarHeaderFields}
    (h : parseUstarHeader bytes offset = .ok hdr) :
    hdr.uid < u64Limit ∧ hdr.gid < u64Limit ∧ hdr.size < u64Limit ∧ hdr.mtime < u64Limit := by
  unfold parseUstarHeader at h
  simp only [throw, throwThe, MonadExceptOf.throw, error_bind_eq, except_bind_eq_ok,
    ite_err_eq_ok, pure, Except.pure, Except.ok.injEq] at h
  rcases h with ⟨_, _, _, _, _, _, uUid, huid, uGid, hgid, uSize, hsize, uMtime, hmtime, rfl⟩
  have hpos : 0 < u64Limit := by decide
  exact ⟨parseUstarNumeric_lt hpos huid, parseUstarNumeric_lt hpos hgid,
    parseUstarNumeric_lt hpos hsize, parseUstarNumeric_lt hpos hmtime⟩

private theorem decodeTarEntry_valid (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (hdr : UstarHeaderFields) (pendingPax : Option PaxOverrides)
    (seen : List String) (accLen totalBytes : Nat) (entry : TarEntry) (padded : Nat)
    (hpax_ok : PaxOverrides.Valid (pendingPax.getD {}))
    (hhdr_ok : hdr.uid < u64Limit ∧ hdr.gid < u64Limit ∧ hdr.size < u64Limit ∧ hdr.mtime < u64Limit)
    (hdec : decodeTarEntry opts bytes offset hdr pendingPax seen accLen totalBytes = .ok (entry, padded)) :
    validEntryBool opts.allowAbsolute opts.allowParentTraversal entry = true ∧
    normalizeTarPath entry.kind entry.path = entry.path ∧
    (!seen.contains entry.path) = true ∧
    accLen + 1 ≤ opts.maxEntries ∧
    totalBytes + entry.data.size ≤ opts.maxTotalBytes ∧
    entry.data.size ≤ padded := by
  unfold decodeTarEntry at hdec; dsimp only at hdec
  split at hdec; · cases hdec
  rename_i kind _
  iterate 4 (split at hdec; · cases hdec)
  rename_i hne_nonreg hmax_e hmax_b hno_trunc
  split at hdec <;> try cases hdec
  rename_i rawPath rawLink uname gname _ hlink_res huname hgname
  cases hval : validateEntryPath opts.allowAbsolute opts.allowParentTraversal kind rawPath with
  | error _ => rw [hval] at hdec; cases hdec
  | ok normPath =>
    rw [hval] at hdec; dsimp only at hdec
    split at hdec; · cases hdec
    rename_i hsym
    split at hdec; · cases hdec
    rename_i hnot_seen
    cases hdec
    let pax := pendingPax.getD {}
    let effSize := pax.size?.getD hdr.size
    have hopt_lt : ∀ (o : Option Nat) (d : Nat), (∀ n, o = some n → n < u64Limit) → d < u64Limit →
        o.getD d < u64Limit := fun o _ ho hd => by cases o with | none => exact hd | some n => exact ho n rfl
    have hopt_nul : ∀ (o : Option String) (fn : String) (st sp : Nat) (s : String),
        (!hasNulString (o.getD "")) = true →
        (match o with | some u => Except.ok u | none => decodeCStringUtf8 bytes st sp offset fn) = .ok s →
        (!hasNulString s) = true := by
      intro o fn st sp s ho hm; cases o with
      | none => exact decodeCStringUtf8_not_hasNul hm
      | some u => cases hm; exact ho
    have hpax_uid : pax.uid?.getD hdr.uid < u64Limit := hopt_lt _ _ hpax_ok.uid_ok hhdr_ok.1
    have hpax_gid : pax.gid?.getD hdr.gid < u64Limit := hopt_lt _ _ hpax_ok.gid_ok hhdr_ok.2.1
    have hpax_size : effSize < u64Limit := hopt_lt _ _ hpax_ok.size_ok hhdr_ok.2.2.1
    have hpax_mtime : pax.mtime?.getD hdr.mtime < u64Limit := hopt_lt _ _ hpax_ok.mtime_ok hhdr_ok.2.2.2
    have hnul_u : (!hasNulString uname) = true := hopt_nul pax.uname? "uname" _ _ _ hpax_ok.uname_ok huname
    have hnul_g : (!hasNulString gname) = true := hopt_nul pax.gname? "gname" _ _ _ hpax_ok.gname_ok hgname
    have hle_pad : effSize ≤ pad512 effSize := le_pad512 effSize
    have hpay_sz : (if effSize == 0 then ByteArray.empty
        else bytes.extract (offset + 512) (offset + 512 + effSize)).size = effSize := by
      have hpad' := le_pad512 ((pendingPax.getD {}).size?.getD hdr.size)
      dsimp only [effSize, pax]
      by_cases hz : (pendingPax.getD {}).size?.getD hdr.size = 0
      · simp [hz]
      · simp only [beq_false_of_ne hz, Bool.false_eq_true, ↓reduceIte, ByteArray.size_extract]; omega
    have ⟨hid, hnorm_id, _⟩ := validateEntryPath_idemp hval
    refine ⟨?_, hnorm_id, by dsimp only; rw [Bool.eq_false_iff.mpr hnot_seen]; rfl, by omega,
      by dsimp only [effSize, pax] at hpay_sz ⊢; omega,
      by dsimp only [effSize, pax] at hpay_sz hle_pad ⊢; omega⟩
    unfold validEntryBool
    dsimp only; rw [hid]; dsimp only
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · cases hk : kind <;> simp only [hk] at hsym hlink_res ⊢
      · cases hlink_res; rfl
      · cases hlink_res; rfl
      · rw [hsym]
    · cases hk : kind <;> simp only [hk] at hne_nonreg ⊢
      · have he0 : effSize = 0 := by
          dsimp only [effSize, pax]
          cases hz : ((pendingPax.getD {}).size?.getD hdr.size == 0)
          · exfalso; apply hne_nonreg; rw [Bool.and_eq_true]; refine ⟨by decide, by rw [bne, hz]; rfl⟩
          · exact beq_iff_eq.mp hz
        dsimp only [effSize, pax] at hpay_sz he0; rw [hpay_sz, he0]; rfl
      · have he0 : effSize = 0 := by
          dsimp only [effSize, pax]
          cases hz : ((pendingPax.getD {}).size?.getD hdr.size == 0)
          · exfalso; apply hne_nonreg; rw [Bool.and_eq_true]; refine ⟨by decide, by rw [bne, hz]; rfl⟩
          · exact beq_iff_eq.mp hz
        dsimp only [effSize, pax] at hpay_sz he0; rw [hpay_sz, he0]; rfl
    · dsimp only [effSize, pax] at hpay_sz hpax_uid hpax_gid hpax_size hpax_mtime
      simp only [hnul_u, hnul_g, hpay_sz, decide_eq_true_eq,
        hpax_uid, hpax_gid, hpax_mtime, hpax_size, and_self]

private theorem unpackStep_ok_cases {opts bytes offset pendingPax seen acc totalBytes step}
    (h : unpackStep opts bytes offset pendingPax seen acc totalBytes = .ok step) :
    step = .done acc.reverse ∨
    (∃ nextOff paxOv, step = .cont nextOff (some paxOv) seen acc totalBytes ∧ PaxOverrides.Valid paxOv) ∨
    (∃ hdr entry padded,
      parseUstarHeader bytes offset = .ok hdr ∧
      decodeTarEntry opts bytes offset hdr pendingPax seen acc.length totalBytes = .ok (entry, padded) ∧
      step = .cont (offset + 512 + padded) none (entry.path :: seen) (entry :: acc)
        (totalBytes + entry.data.size)) := by
  unfold unpackStep at h
  split at h; · cases h
  split at h
  · iterate 4 (split at h; · cases h)
    cases h; exact Or.inl rfl
  · split at h; · cases h
    split at h; · cases h
    rename_i hdr hhdr
    split at h
    · iterate 2 (split at h; · cases h)
      dsimp only at h
      split at h; · cases h
      split at h; · cases h
      rename_i paxOv hpax
      cases h
      exact Or.inr (Or.inl ⟨_, paxOv, rfl, parsePaxPayload_go_valid paxValid_empty hpax⟩)
    · split at h; · cases h
      rename_i entry padded hdec
      cases h
      exact Or.inr (Or.inr ⟨hdr, entry, padded, hhdr, hdec, rfl⟩)

private theorem unpackLoopFuel_valid (fuel : Nat) (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) (res : List TarEntry)
    (hpax_ok : PaxOverrides.Valid (pendingPax.getD {}))
    (hacc_valid : ∀ e ∈ acc, validEntryBool opts.allowAbsolute opts.allowParentTraversal e = true)
    (hseen_eq : seen = acc.map (fun e => normalizeTarPath e.kind e.path))
    (hnodup : noDupNormalizedPathsBool acc.reverse = true)
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
    split at hrun; · cases hrun
    cases hstep : unpackStep opts bytes offset pendingPax seen acc totalBytes with
    | error _ => rw [hstep] at hrun; cases hrun
    | ok step =>
      rw [hstep] at hrun
      rcases unpackStep_ok_cases hstep with rfl | ⟨nextOff, paxOv, rfl, hpax'⟩ | ⟨hdr, entry, padded, hhdr, hdec, rfl⟩
      · cases hrun
        refine ⟨?_, by simpa using hacc_len, by rw [totalDataBytes_reverse, htot_eq]; exact htot_le⟩
        unfold ValidArchive validArchiveBool
        rw [Bool.and_eq_true, List.all_eq_true]
        exact ⟨fun e he => hacc_valid e (List.mem_reverse.mp he), hnodup⟩
      · dsimp only at hrun
        split at hrun
        · exact ih nextOff (some paxOv) seen acc totalBytes hpax' hacc_valid hseen_eq hnodup hacc_len htot_eq htot_le hrun
        · cases hrun
      · dsimp only at hrun
        split at hrun
        · have ⟨hve, hnorm_id, hnot_seen, hle_e, hle_b, _⟩ :=
            decodeTarEntry_valid opts bytes offset hdr pendingPax seen acc.length totalBytes
              entry padded hpax_ok (parseUstarHeader_u64 hhdr) hdec
          have hnodup' : noDupNormalizedPathsBool (entry :: acc).reverse = true := by
            unfold noDupNormalizedPathsBool at hnodup ⊢
            rw [List.reverse_cons, noDup_go_snoc, hnodup, Bool.true_and, List.reverse_reverse,
              List.append_nil, ← hseen_eq, hnorm_id]
            exact hnot_seen
          exact ih (offset + 512 + padded) none (entry.path :: seen) (entry :: acc) (totalBytes + entry.data.size)
            paxValid_empty
            (fun e he => by rcases List.mem_cons.mp he with rfl | ha; exact hve; exact hacc_valid e ha)
            (by simp [hnorm_id, hseen_eq]) hnodup' hle_e
            (by rw [totalDataBytes_cons, htot_eq, Nat.add_comm]) hle_b hrun
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
    split at h; · cases h
    have ⟨hv, hl, ht⟩ := unpackLoopFuel_valid _ opts bytes 0 none [] [] 0 entries
      paxValid_empty (fun _ hm => by cases hm) rfl rfl (Nat.zero_le _) rfl (Nat.zero_le _) h
    exact ⟨hv, hl, ht, trivial⟩

end LeanSwe.Tar.Proofs
