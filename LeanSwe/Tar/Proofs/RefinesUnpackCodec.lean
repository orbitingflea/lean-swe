import LeanSwe.Tar.Model.WireSpec
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.HeaderLayout

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Unpack `sliceList bytes start stop` into `(bytes.extract start stop).data.toList`. -/
theorem sliceList_eq_data_toList (bytes : ByteArray) (start stop : Nat) :
    sliceList bytes start stop = (bytes.extract start stop).data.toList := by
  unfold sliceList; exact byteArray_toList_eq _

/-- Length of `sliceList bytes start stop`. -/
theorem sliceList_length (bytes : ByteArray) (start stop : Nat) :
    (sliceList bytes start stop).length = min stop bytes.size - start := by
  rw [sliceList_eq_data_toList, Array.length_toList]
  exact ByteArray.size_extract

/-- Indexing helper for `sliceList bytes start stop`. -/
theorem sliceList_getElem {bytes : ByteArray} {start stop i : Nat}
    (hi : i < (sliceList bytes start stop).length) :
    (sliceList bytes start stop)[i]'hi =
      bytes[start + i]'(by rw [sliceList_length] at hi; omega) := by
  have hi_s : i < (bytes.extract start stop).size := by
    rw [ByteArray.size_extract]; rw [sliceList_length] at hi; exact hi
  have h1 : (sliceList bytes start stop)[i]'hi = (bytes.extract start stop).data.toList[i]'(by
      rw [Array.length_toList]; exact hi_s) := by
    congr 1; exact sliceList_eq_data_toList bytes start stop
  rw [h1, Array.getElem_toList]
  exact ByteArray.getElem_extract hi_s

/-- Sub-slice equivalence for a nested `bytes.extract offset (offset + 512)`. -/
theorem sliceList_hdr_sub (bytes : ByteArray) (offset a b : Nat) (hb : b ≤ 512) :
    sliceList (bytes.extract offset (offset + 512)) a b =
      sliceList bytes (offset + a) (offset + b) := by
  unfold sliceList
  rw [ByteArray.extract_extract]
  congr 1
  rw [show min (offset + b) (offset + 512) = offset + b by omega]

/-- Empty `sliceList` when `stop ≤ start` or `bytes.size ≤ start`. -/
theorem sliceList_eq_nil {bytes : ByteArray} {start stop : Nat}
    (h : stop ≤ start ∨ bytes.size ≤ start) :
    sliceList bytes start stop = [] := by
  rw [← List.length_eq_zero_iff, sliceList_length]; omega

/-- Cons decomposition of `sliceList` at its first index `i < min stop bytes.size`. -/
theorem sliceList_cons {bytes : ByteArray} {i stop : Nat}
    (hi : i < bytes.size) (histop : i < stop) :
    sliceList bytes i stop = bytes[i]'hi :: sliceList bytes (i + 1) stop := by
  refine List.ext_getElem (by simp [sliceList_length]; omega) fun k hk1 hk2 => ?_
  rw [sliceList_getElem hk1]
  cases k with
  | zero => rfl
  | succ k' =>
    have hk' : k' < (sliceList bytes (i + 1) stop).length := by
      rw [sliceList_length]; rw [sliceList_length] at hk1; omega
    rw [List.getElem_cons_succ, sliceList_getElem hk']
    congr 1; omega

/-- Drop `k` bytes from `sliceList bytes start stop`. -/
theorem sliceList_drop (bytes : ByteArray) (start stop k : Nat) :
    (sliceList bytes start stop).drop k = sliceList bytes (start + k) stop := by
  induction k generalizing start with
  | zero => simp
  | succ k ih =>
    by_cases hlt : start < bytes.size ∧ start < stop
    · rw [sliceList_cons hlt.1 hlt.2, List.drop_succ_cons, ih]
      congr 1; omega
    · have hnil : sliceList bytes start stop = [] := sliceList_eq_nil (by omega)
      have hnil' : sliceList bytes (start + (k + 1)) stop = [] := sliceList_eq_nil (by omega)
      rw [hnil, List.drop_nil, hnil']

/-- Take `k` bytes from `sliceList bytes start stop`. -/
theorem sliceList_take (bytes : ByteArray) (start stop k : Nat) :
    (sliceList bytes start stop).take k = sliceList bytes start (min stop (start + k)) := by
  induction k generalizing start with
  | zero =>
    rw [List.take_zero, sliceList_eq_nil (Or.inl (by omega))]
  | succ k ih =>
    by_cases hlt : start < bytes.size ∧ start < stop
    · rw [sliceList_cons hlt.1 hlt.2, List.take_succ_cons, ih,
        sliceList_cons hlt.1 (by omega)]
      congr 2; omega
    · have hnil : sliceList bytes start stop = [] := sliceList_eq_nil (by omega)
      have hnil' : sliceList bytes start (min stop (start + (k + 1))) = [] :=
        sliceList_eq_nil (by omega)
      rw [hnil, List.take_nil, hnil']

/-- `Impl.isZeroRange bytes offset 512` equals `Model.isZeroBlockAt bytes offset`. -/
theorem isZeroRange_eq_isZeroBlockAt (bytes : ByteArray) (offset : Nat) :
    isZeroRange bytes offset 512 = isZeroBlockAt bytes offset := by
  apply Bool.eq_iff_iff.mpr
  rw [isZeroRange_eq_true_iff bytes offset 512 (by decide)]
  unfold isZeroBlockAt
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨hbd, hall⟩
    refine ⟨hbd, fun b hb => ?_⟩
    rw [beq_iff_eq]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    rw [sliceList_getElem hi]
    have hi512 : i < 512 := by rw [sliceList_length] at hi; omega
    exact hall i hi512 (by omega)
  · rintro ⟨hbd, hall⟩
    refine ⟨hbd, fun i hi hbi => ?_⟩
    have hi_l : i < (sliceList bytes offset (offset + 512)).length := by
      rw [sliceList_length]; omega
    have hz := beq_iff_eq.mp (hall _ (List.getElem_mem hi_l))
    rwa [sliceList_getElem hi_l] at hz

private theorem allZeroTrailer_go_iff (bytes : ByteArray) (hmod : bytes.size % 512 = 0) :
    ∀ (rem pos : Nat), pos % 512 = 0 →
      (allZeroTrailer.go bytes rem pos = true ↔
        ∀ i, pos ≤ i → i < bytes.size → i < pos + 512 * rem →
          ∀ hi : i < bytes.size, bytes[i]'hi = 0) := by
  intro rem; induction rem with
  | zero =>
    intro pos _
    simp only [allZeroTrailer.go.eq_1, true_iff]
    intro i h1 _ h3; omega
  | succ rem ih =>
    intro pos hpm
    rw [allZeroTrailer.go.eq_2]
    by_cases hge : pos ≥ bytes.size
    · simp only [hge, ↓reduceIte, true_iff]
      intro i h1 h2; omega
    · simp only [hge, ↓reduceIte, Bool.and_eq_true]
      have hbd : pos + 512 ≤ bytes.size := by omega
      rw [isZeroRange_eq_true_iff bytes pos 512 (by decide), ih (pos + 512) (by omega)]
      constructor
      · rintro ⟨⟨_, hblk⟩, hrest⟩ i h1 h2 h3 hi
        by_cases hlt : i < pos + 512
        · simpa [show pos + (i - pos) = i by omega] using hblk (i - pos) (by omega) (by omega)
        · exact hrest i (by omega) h2 (by omega) hi
      · intro hall
        refine ⟨⟨hbd, fun k hk hki => hall (pos + k) (by omega) hki (by omega) hki⟩,
          fun i h1 h2 h3 hi => hall i (by omega) h2 (by omega) hi⟩

/-- `Impl.allZeroTrailer` agrees with `Model.isZeroSuffix` on 512-byte-aligned positions and archives. -/
theorem allZeroTrailer_eq_isZeroSuffix (bytes : ByteArray) (offset : Nat)
    (hbm : bytes.size % 512 = 0) (hom : offset % 512 = 0) :
    allZeroTrailer bytes offset = isZeroSuffix bytes offset := by
  apply Bool.eq_iff_iff.mpr
  unfold allZeroTrailer isZeroSuffix
  rw [allZeroTrailer_go_iff bytes hbm _ offset hom, List.all_eq_true]
  have hcov : bytes.size ≤ offset + 512 * ((bytes.size - offset + 511) / 512) := by omega
  constructor
  · intro hall b hb
    rw [beq_iff_eq]
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
    rw [sliceList_getElem hk]
    have hki : offset + k < bytes.size := by rw [sliceList_length] at hk; omega
    exact hall (offset + k) (by omega) hki (by omega) hki
  · intro hall i h1 h2 _ hi
    have hk_l : i - offset < (sliceList bytes offset bytes.size).length := by
      rw [sliceList_length]; omega
    have hz := beq_iff_eq.mp (hall _ (List.getElem_mem hk_l))
    rw [sliceList_getElem hk_l] at hz
    simpa [show offset + (i - offset) = i by omega] using hz

private theorem findNul_ge (bytes : ByteArray) (stop : Nat) :
    ∀ rem i, rem + i = stop → i ≤ extractCStringBytes.findNul bytes stop rem i := by
  intro rem; induction rem with
  | zero => intro i h; rw [extractCStringBytes.findNul.eq_1]; omega
  | succ rem ih =>
    intro i h; rw [extractCStringBytes.findNul.eq_2]
    split
    · split
      · exact Nat.le_refl _
      · have := ih (i + 1) (by omega); omega
    · omega

private theorem sliceList_extractCString_go (bytes : ByteArray) (stop : Nat) :
    ∀ rem i, rem + i = stop →
      sliceList bytes i (extractCStringBytes.findNul bytes stop rem i) =
        (sliceList bytes i stop).takeWhile (· != 0) := by
  intro rem; induction rem with
  | zero =>
    intro i h
    rw [extractCStringBytes.findNul.eq_1]
    have hs1 : sliceList bytes i stop = [] := sliceList_eq_nil (Or.inl (by omega))
    rw [hs1, List.takeWhile_nil]
  | succ rem ih =>
    intro i h
    rw [extractCStringBytes.findNul.eq_2]
    by_cases hi : i < bytes.size
    · simp only [hi, ↓reduceDIte]
      have hcons := sliceList_cons hi (show i < stop by omega)
      by_cases hz : (bytes[i]'hi == 0) = true
      · simp only [hz, ↓reduceIte, hcons]
        have hnz : (bytes[i]'hi != 0) = false := by
          simp only [bne, hz, Bool.not_true]
        rw [sliceList_eq_nil (Or.inl (Nat.le_refl _)), List.takeWhile_cons, hnz]
        rfl
      · have hzF : (bytes[i]'hi == 0) = false := Bool.eq_false_iff.mpr hz
        have hnz : (bytes[i]'hi != 0) = true := by
          simp only [bne, hzF, Bool.not_false]
        have hge : i + 1 ≤ extractCStringBytes.findNul bytes stop rem (i + 1) :=
          findNul_ge bytes stop rem (i + 1) (by omega)
        simp only [hzF, Bool.false_eq_true, ↓reduceIte, hcons, List.takeWhile_cons, hnz]
        rw [sliceList_cons hi (by omega), ih (i + 1) (by omega)]
    · simp only [hi, ↓reduceDIte]
      have hs1 : sliceList bytes i stop = [] := sliceList_eq_nil (Or.inr (by omega))
      rw [hs1, List.takeWhile_nil]

/-- `Impl.extractCStringBytes` coincides with taking bytes up to the first `0x00` in `sliceList`. -/
theorem extractCStringBytes_eq_model (bytes : ByteArray) (start stop : Nat) :
    extractCStringBytes bytes start stop =
      ByteArray.mk ((sliceList bytes start stop).takeWhile (· != 0)).toArray := by
  have hlist : (extractCStringBytes bytes start stop).data.toList =
      (sliceList bytes start stop).takeWhile (· != 0) := by
    unfold extractCStringBytes
    rw [← sliceList_eq_data_toList]
    by_cases hle : start ≤ stop
    · exact sliceList_extractCString_go bytes stop (stop - start) start (by omega)
    · rw [show stop - start = 0 by omega, extractCStringBytes.findNul.eq_1]
      have hs1 : sliceList bytes start stop = [] := sliceList_eq_nil (Or.inl (by omega))
      rw [hs1, List.takeWhile_nil]
  cases hb : extractCStringBytes bytes start stop with
  | mk arr =>
    congr 1
    apply Array.toList_inj.mp
    simpa [hb] using hlist

/-- Refinement relation between `Except TarError α` and `Except TarErrKey β` modulo message prose. -/
inductive tarExceptRel {α β : Type} (R : α → β → Prop) :
    Except TarError α → Except TarErrKey β → Prop where
  /-- Both sides succeeded with `R`-related values. -/
  | ok {a : α} {b : β} : R a b → tarExceptRel R (.ok a) (.ok b)
  /-- Both sides failed with matching `TarErrKey` and a non-empty error message. -/
  | error {err : TarError} {key : TarErrKey} :
      tarErrKeyOf err = key → !err.message.isEmpty = true →
      tarExceptRel R (.error err) (.error key)

/-- Extract the underlying `R` relation or error obligation from `tarExceptRel`. -/
theorem tarExceptRel_elim {α β : Type} {R : α → β → Prop}
    {a : Except TarError α} {b : Except TarErrKey β} (h : tarExceptRel R a b) :
    match a, b with
    | .ok x, .ok y => R x y
    | .error err, .error key => tarErrKeyOf err = key ∧ !err.message.isEmpty = true
    | _, _ => False := by
  cases h with
  | ok hr => exact hr
  | error hk hm => exact ⟨hk, hm⟩

/-- Monadic bind congruence for `tarExceptRel`. -/
theorem tarExceptRel_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {m1 : Except TarError α} {m2 : Except TarErrKey β}
    {f1 : α → Except TarError γ} {f2 : β → Except TarErrKey δ}
    (hm : tarExceptRel R m1 m2) (hf : ∀ a b, R a b → tarExceptRel S (f1 a) (f2 b)) :
    tarExceptRel S (m1 >>= f1) (m2 >>= f2) := by
  cases hm with
  | error hk hm => exact .error hk hm
  | ok hr => exact hf _ _ hr

/-- `Impl.decodeCStringUtf8` agrees with `Model.decodeCStringList` modulo error message text. -/
theorem decodeCStringUtf8_refines (bytes : ByteArray) (start stop offset : Nat) (fieldName : String) :
    tarExceptRel (· = ·)
      (decodeCStringUtf8 bytes start stop offset fieldName)
      (decodeCStringList (sliceList bytes start stop) offset) := by
  unfold decodeCStringUtf8 decodeCStringList
  dsimp only
  rw [extractCStringBytes_eq_model]
  cases String.fromUTF8? (ByteArray.mk ((sliceList bytes start stop).takeWhile (· != 0)).toArray) with
  | none =>
    exact .error rfl (by dsimp only [ToString.toString]; exact nonEmpty_append_left (by decide))
  | some _ => exact .ok rfl

/-- `Impl.ustarChecksumAt bytes offset` equals `Model.ustarChecksum (bytes.extract offset (offset + 512))`. -/
theorem ustarChecksumAt_eq_extract (bytes : ByteArray) (offset : Nat) :
    ustarChecksumAt bytes offset = ustarChecksum (bytes.extract offset (offset + 512)) := by
  rw [ustarChecksum_eq_ustarChecksumAt]
  unfold ustarChecksumAt
  have hgo : ∀ rem idx acc : Nat, rem + idx = 512 →
      ustarChecksumAt.go bytes offset rem idx acc =
        ustarChecksumAt.go (bytes.extract offset (offset + 512)) 0 rem idx acc := by
    intro rem; induction rem with
    | zero => intros; rfl
    | succ d ih =>
      intro idx acc hsum
      rw [ustarChecksumAt.go.eq_2, ustarChecksumAt.go.eq_2]
      by_cases hchk : (decide (148 ≤ idx) && decide (idx < 156)) = true
      · simp only [hchk, ↓reduceIte]
        exact ih (idx + 1) _ (by omega)
      · have hchkF : (decide (148 ≤ idx) && decide (idx < 156)) = false := Bool.eq_false_iff.mpr hchk
        simp only [hchkF, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        by_cases hi : offset + idx < bytes.size
        · have hi_e : idx < (bytes.extract offset (offset + 512)).size := by
            rw [ByteArray.size_extract]; omega
          simp only [hi, hi_e, ↓reduceDIte, ByteArray.getElem_extract hi_e]
          exact ih (idx + 1) _ (by omega)
        · have hi_e : ¬(idx < (bytes.extract offset (offset + 512)).size) := by
            rw [ByteArray.size_extract]; omega
          simp only [hi, hi_e, ↓reduceDIte]
          exact ih (idx + 1) _ (by omega)
  exact hgo 512 0 0 rfl

/-- `Impl.hasValidMagic` equals `Model.hasValidMagicModel` on the extracted 512-byte header. -/
theorem hasValidMagic_eq_model (bytes : ByteArray) (offset : Nat) :
    hasValidMagic bytes offset = hasValidMagicModel (bytes.extract offset (offset + 512)) := by
  unfold hasValidMagic hasValidMagicModel
  rw [sliceList_hdr_sub bytes offset 257 263 (by decide),
    sliceList_hdr_sub bytes offset 263 265 (by decide),
    sliceList_eq_data_toList, sliceList_eq_data_toList]

/-- `Impl.parseChecksumOctal` agrees with `Model.parseChecksumOctalModel` modulo error message text. -/
theorem parseChecksumOctal_refines (bytes : ByteArray) (start stop offset : Nat) :
    tarExceptRel (· = ·)
      (parseChecksumOctal bytes start stop offset)
      (parseChecksumOctalModel (sliceList bytes start stop) offset) := by
  unfold parseChecksumOctal parseChecksumOctalModel
  rw [sliceList_eq_data_toList]
  generalize (bytes.extract start stop).data.toList = raw
  dsimp only
  let afterLead := raw.dropWhile (· == 0x20)
  let digits := afterLead.takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37)
  let tail := afterLead.drop digits.length
  by_cases h1 : digits.isEmpty = true
  · simp only [digits, afterLead] at h1
    simp only [h1, ↓reduceIte]; exact .error rfl rfl
  simp only [digits, afterLead] at h1
  simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (!tail.all (fun b => b == 0x20 || b == 0x00)) = true
  · simp only [tail, digits, afterLead] at h2
    simp only [h2, ↓reduceIte]; exact .error rfl rfl
  simp only [tail, digits, afterLead] at h2
  simp only [Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte]
  exact .ok rfl

/-- `Impl.parseUstarNumeric` agrees with `Model.parseUstarNumericModel` modulo error message text. -/
theorem parseUstarNumeric_refines (bytes : ByteArray) (start stop offset : Nat)
    (allowAllEmpty : Bool) (limit : Nat) (fieldName : String) :
    tarExceptRel (· = ·)
      (parseUstarNumeric bytes start stop offset allowAllEmpty limit fieldName)
      (parseUstarNumericModel (sliceList bytes start stop) offset allowAllEmpty limit) := by
  unfold parseUstarNumeric parseUstarNumericModel
  rw [sliceList_eq_data_toList]
  generalize (bytes.extract start stop).data.toList = raw
  cases raw with
  | nil =>
    exact .error rfl (nonEmpty_append_left (nonEmpty_append_left (by decide)))
  | cons b0 rest =>
    dsimp only
    by_cases hb1 : ((b0 &&& 0x80) != 0) = true
    · simp only [hb1, ↓reduceIte]
      by_cases hb2 : ((b0 &&& 0x40) != 0) = true
      · simp only [hb2, ↓reduceIte]
        exact .error rfl (nonEmpty_append_left (by decide))
      simp only [Bool.eq_false_iff.mpr hb2, Bool.false_eq_true, ↓reduceIte]
      by_cases hov : rest.foldl (fun acc b => acc * 256 + b.toNat) (b0 &&& 0x7f).toNat ≥ limit
      · simp only [hov, ↓reduceIte]
        exact .error rfl (nonEmpty_append_left (nonEmpty_append_left (by decide)))
      simp only [hov, ↓reduceIte]; exact .ok rfl
    simp only [Bool.eq_false_iff.mpr hb1, Bool.false_eq_true, ↓reduceIte]
    by_cases hemp : (b0 :: rest).all (fun b => b == 0x00 || b == 0x20) = true
    · simp only [hemp, ↓reduceIte]
      cases allowAllEmpty
      · exact .error rfl (nonEmpty_append_left (by decide))
      · exact .ok rfl
    simp only [Bool.eq_false_iff.mpr hemp, Bool.false_eq_true, ↓reduceIte]
    by_cases hd0 : (((b0 :: rest).dropWhile (· == 0x20)).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37)).isEmpty = true
    · simp only [hd0, ↓reduceIte]
      exact .error rfl (nonEmpty_append_left (by decide))
    simp only [Bool.eq_false_iff.mpr hd0, Bool.false_eq_true, ↓reduceIte]
    by_cases htl : (!(((b0 :: rest).dropWhile (· == 0x20)).drop
        (((b0 :: rest).dropWhile (· == 0x20)).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37)).length).all
        (fun b => b == 0x20 || b == 0x00)) = true
    · simp only [htl, ↓reduceIte]
      exact .error rfl (nonEmpty_append_left (by decide))
    simp only [Bool.eq_false_iff.mpr htl, Bool.false_eq_true, ↓reduceIte]
    by_cases hov2 : (((b0 :: rest).dropWhile (· == 0x20)).takeWhile
        (fun b => 0x30 ≤ b && b ≤ 0x37)).foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0 ≥ limit
    · simp only [hov2, ↓reduceIte]
      exact .error rfl (nonEmpty_append_left (nonEmpty_append_left (by decide)))
    simp only [hov2, ↓reduceIte]; exact .ok rfl

/-- Exact equality relation between `Impl.UstarHeaderFields` and `Model.HeaderFieldsModel`. -/
def headerFieldsRel (a : UstarHeaderFields) (b : HeaderFieldsModel) : Prop :=
  a.mode = b.mode ∧ a.uid = b.uid ∧ a.gid = b.gid ∧ a.size = b.size ∧ a.mtime = b.mtime ∧ a.typeflag = b.typeflag

private theorem tarExceptRel_congr_right {α β : Type} {R : α → β → Prop}
    {m1 : Except TarError α} {m2 m2' : Except TarErrKey β}
    (h : m2 = m2') (hm : tarExceptRel R m1 m2) : tarExceptRel R m1 m2' :=
  h ▸ hm

private theorem parseChecksumOctal_hdr_refines (bytes : ByteArray) (offset a b : Nat) (hb : b ≤ 512) :
    tarExceptRel (· = ·)
      (parseChecksumOctal bytes (offset + a) (offset + b) offset)
      (parseChecksumOctalModel (sliceList (bytes.extract offset (offset + 512)) a b) offset) :=
  tarExceptRel_congr_right
    (congrArg (fun xs => parseChecksumOctalModel xs offset) (sliceList_hdr_sub bytes offset a b hb).symm)
    (parseChecksumOctal_refines bytes (offset + a) (offset + b) offset)

private theorem parseUstarNumeric_hdr_refines (bytes : ByteArray) (offset a b : Nat) (hb : b ≤ 512)
    (allowAllEmpty : Bool) (limit : Nat) (fieldName : String) :
    tarExceptRel (· = ·)
      (parseUstarNumeric bytes (offset + a) (offset + b) offset allowAllEmpty limit fieldName)
      (parseUstarNumericModel (sliceList (bytes.extract offset (offset + 512)) a b) offset allowAllEmpty limit) :=
  tarExceptRel_congr_right
    (congrArg (fun xs => parseUstarNumericModel xs offset allowAllEmpty limit)
      (sliceList_hdr_sub bytes offset a b hb).symm)
    (parseUstarNumeric_refines bytes (offset + a) (offset + b) offset allowAllEmpty limit fieldName)

private theorem parseUstarHeader_core
    (offset : Nat)
    (chkA chkB : Nat) (hchkEq : chkA = chkB)
    (mgA mgB : Bool) (hmgEq : mgA = mgB)
    (typeA typeB : UInt8) (htypeEq : typeA = typeB)
    (mChk mMode mUid mGid mSize mMtime : Except TarError Nat)
    (sChk sMode sUid sGid sSize sMtime : Except TarErrKey Nat)
    (hc : tarExceptRel (· = ·) mChk sChk)
    (hm : tarExceptRel (· = ·) mMode sMode)
    (hu : tarExceptRel (· = ·) mUid sUid)
    (hg : tarExceptRel (· = ·) mGid sGid)
    (hs : tarExceptRel (· = ·) mSize sSize)
    (hmt : tarExceptRel (· = ·) mMtime sMtime) :
    tarExceptRel headerFieldsRel
      (do
        let storedChk ← mChk
        if storedChk != chkA then
          throw { kind := .checksumMismatch, message := "USTAR header checksum mismatch", offset := some offset }
        if !mgA then
          throw { kind := .invalidHeader, message := "invalid USTAR magic or version", offset := some offset }
        let uMode ← mMode
        let uUid ← mUid
        let uGid ← mGid
        let uSize ← mSize
        let uMtime ← mMtime
        pure { mode := uMode, uid := uUid, gid := uGid, size := uSize, mtime := uMtime, typeflag := typeA })
      (do
        let storedChk ← sChk
        if storedChk != chkB then
          .error (.checksumMismatch, none, some offset)
        else if !mgB then
          .error (.invalidHeader, none, some offset)
        else
          let uMode ← sMode
          let uUid ← sUid
          let uGid ← sGid
          let uSize ← sSize
          let uMtime ← sMtime
          .ok { mode := uMode, uid := uUid, gid := uGid, size := uSize, mtime := uMtime, typeflag := typeB }) := by
  subst hchkEq hmgEq htypeEq
  cases hc with
  | error hk hmsg => exact .error hk hmsg
  | ok hce =>
    rename_i c1 c2
    subst hce
    by_cases hck : (c1 != chkA) = true
    · simp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hck, ↓reduceIte]
      exact .error rfl rfl
    · have hckF : (c1 != chkA) = false := Bool.eq_false_iff.mpr hck
      cases mgA with
      | false =>
        simp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hckF,
          Bool.false_eq_true, ↓reduceIte, Bool.not_false]
        exact .error rfl rfl
      | true =>
        simp only [Bind.bind, Except.bind, pure, Except.pure,
          hckF, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        cases hm with
        | error hk hmsg => exact .error hk hmsg
        | ok he =>
          subst he
          cases hu with
          | error hk hmsg => exact .error hk hmsg
          | ok he =>
            subst he
            cases hg with
            | error hk hmsg => exact .error hk hmsg
            | ok he =>
              subst he
              cases hs with
              | error hk hmsg => exact .error hk hmsg
              | ok he =>
                subst he
                cases hmt with
                | error hk hmsg => exact .error hk hmsg
                | ok he =>
                  subst he
                  exact .ok ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Impl.parseUstarHeader` refines `Model.parseUstarHeaderModel`. -/
theorem parseUstarHeader_refines (bytes : ByteArray) (offset : Nat) :
    tarExceptRel headerFieldsRel (parseUstarHeader bytes offset)
      (parseUstarHeaderModel (bytes.extract offset (offset + 512)) offset) := by
  have hchk := ustarChecksumAt_eq_extract bytes offset
  have hmg := hasValidMagic_eq_model bytes offset
  have htypeEq :
      (if h : offset + 156 < bytes.size then bytes[offset + 156]'h else (0 : UInt8)) =
      (if h : 156 < (bytes.extract offset (offset + 512)).size then
        (bytes.extract offset (offset + 512))[156]'h else 0) := by
    by_cases ht : offset + 156 < bytes.size
    · have hte : 156 < (bytes.extract offset (offset + 512)).size := by
        rw [ByteArray.size_extract]; omega
      simp only [ht, hte, ↓reduceDIte]
      exact (ByteArray.getElem_extract hte).symm
    · have hte : ¬(156 < (bytes.extract offset (offset + 512)).size) := by
        rw [ByteArray.size_extract]; omega
      simp only [ht, hte, ↓reduceDIte]
  have hle156 : 156 ≤ 512 := Nat.le_of_ble_eq_true rfl
  have hle108 : 108 ≤ 512 := Nat.le_of_ble_eq_true rfl
  have hle116 : 116 ≤ 512 := Nat.le_of_ble_eq_true rfl
  have hle124 : 124 ≤ 512 := Nat.le_of_ble_eq_true rfl
  have hle136 : 136 ≤ 512 := Nat.le_of_ble_eq_true rfl
  have hle148 : 148 ≤ 512 := Nat.le_of_ble_eq_true rfl
  have h0 := parseChecksumOctal_hdr_refines bytes offset 148 156 hle156
  have h1 := parseUstarNumeric_hdr_refines bytes offset 100 108 hle108 false u32Limit "mode"
  have h2 := parseUstarNumeric_hdr_refines bytes offset 108 116 hle116 true u64Limit "uid"
  have h3 := parseUstarNumeric_hdr_refines bytes offset 116 124 hle124 true u64Limit "gid"
  have h4 := parseUstarNumeric_hdr_refines bytes offset 124 136 hle136 false u64Limit "size"
  have h5 := parseUstarNumeric_hdr_refines bytes offset 136 148 hle148 true u64Limit "mtime"
  generalize bytes.extract offset (offset + 512) = hdr at *
  unfold parseUstarHeader parseUstarHeaderModel
  exact parseUstarHeader_core offset
    (ustarChecksumAt bytes offset) (ustarChecksum hdr) hchk
    (hasValidMagic bytes offset) (hasValidMagicModel hdr) hmg
    (if h : offset + 156 < bytes.size then bytes[offset + 156]'h else 0)
    (if h : 156 < hdr.size then hdr[156]'h else 0) htypeEq
    (parseChecksumOctal bytes (offset + 148) (offset + 156) offset)
    (parseUstarNumeric bytes (offset + 100) (offset + 108) offset false u32Limit "mode")
    (parseUstarNumeric bytes (offset + 108) (offset + 116) offset true u64Limit "uid")
    (parseUstarNumeric bytes (offset + 116) (offset + 124) offset true u64Limit "gid")
    (parseUstarNumeric bytes (offset + 124) (offset + 136) offset false u64Limit "size")
    (parseUstarNumeric bytes (offset + 136) (offset + 148) offset true u64Limit "mtime")
    (parseChecksumOctalModel (sliceList hdr 148 156) offset)
    (parseUstarNumericModel (sliceList hdr 100 108) offset false u32Limit)
    (parseUstarNumericModel (sliceList hdr 108 116) offset true u64Limit)
    (parseUstarNumericModel (sliceList hdr 116 124) offset true u64Limit)
    (parseUstarNumericModel (sliceList hdr 124 136) offset false u64Limit)
    (parseUstarNumericModel (sliceList hdr 136 148) offset true u64Limit)
    h0 h1 h2 h3 h4 h5

end LeanSwe.Tar.Proofs
