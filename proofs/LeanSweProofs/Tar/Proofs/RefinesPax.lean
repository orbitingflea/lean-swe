import LeanSweProofs.Tar.Model.WireSpec
import LeanSweProofs.Tar.Proofs.ByteModel
import LeanSweProofs.Tar.Proofs.HeaderLayout
import LeanSweProofs.Tar.Proofs.RefinesUnpackCodec

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Field-wise correspondence between `Impl.PaxOverrides` and `Model.PaxModelOverrides`. -/
def paxOvRel (a : PaxOverrides) (b : PaxModelOverrides) : Prop :=
  a.path? = b.path? ∧ a.linkpath? = b.linkpath? ∧ a.uname? = b.uname? ∧ a.gname? = b.gname? ∧
  a.size? = b.size? ∧ a.mtime? = b.mtime? ∧ a.uid? = b.uid? ∧ a.gid? = b.gid?

/-- Empty PAX override records match. -/
theorem paxOvRel_empty : paxOvRel {} {} :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem list_take_takeWhile_length {α : Type} (p : α → Bool) (xs : List α) :
    xs.take (xs.takeWhile p).length = xs.takeWhile p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : p x
    · simp [h]
    · simp [h, ih]

private theorem findByteIn_go_spec (bs : ByteArray) (target : UInt8) (stop : Nat) :
    ∀ rem i, rem + i = stop →
      let xs := sliceList bs i stop
      let pre := xs.takeWhile (· != target)
      match findByteIn.go bs target rem i with
      | none => xs.drop pre.length = []
      | some k => i ≤ k ∧ k < stop ∧ k < bs.size ∧ pre.length = k - i ∧
          xs.drop pre.length = target :: sliceList bs (k + 1) stop := by
  intro rem; induction rem with
  | zero =>
    intro i h
    rw [findByteIn.go.eq_1, sliceList_eq_nil (Or.inl (by omega))]
    simp
  | succ rem ih =>
    intro i h
    rw [findByteIn.go.eq_2]
    by_cases hi : i < bs.size
    · simp only [hi, ↓reduceDIte]
      have hcons := sliceList_cons hi (show i < stop by omega)
      by_cases hhit : (bs[i]'hi == target) = true
      · simp only [hhit, ↓reduceIte]
        simp only [hcons, beq_iff_eq.mp hhit, List.takeWhile_cons, bne_self_eq_false,
          Bool.false_eq_true, ↓reduceIte, List.length_nil, List.drop_zero]
        exact ⟨Nat.le_refl _, by omega, hi, by omega, trivial⟩
      · have hhitF : (bs[i]'hi == target) = false := Bool.eq_false_iff.mpr hhit
        have hneT : (bs[i]'hi != target) = true := by
          simp only [bne, Bool.not_eq_true']; exact hhitF
        simp only [hhitF, Bool.false_eq_true, ↓reduceIte]
        have hsub := ih (i + 1) (by omega)
        dsimp only at hsub ⊢
        simp only [hcons, List.takeWhile_cons, hneT, ↓reduceIte, List.length_cons,
          List.drop_succ_cons]
        cases hfind : findByteIn.go bs target rem (i + 1) with
        | none => simpa [hfind] using hsub
        | some k =>
          simp only [hfind] at hsub
          exact ⟨by omega, hsub.2.1, hsub.2.2.1, by omega, hsub.2.2.2.2⟩
    · simp only [hi, ↓reduceDIte]
      rw [sliceList_eq_nil (Or.inr (by omega))]
      simp

private theorem findByteIn_spec (bs : ByteArray) (target : UInt8) (idx stop : Nat) :
    let xs := sliceList bs idx stop
    let pre := xs.takeWhile (· != target)
    match findByteIn bs target idx stop with
    | none => xs.drop pre.length = []
    | some k => idx ≤ k ∧ k < stop ∧ k < bs.size ∧ pre.length = k - idx ∧
        xs.drop pre.length = target :: sliceList bs (k + 1) stop := by
  by_cases hle : idx ≤ stop
  · exact findByteIn_go_spec bs target stop (stop - idx) idx (by omega)
  · unfold findByteIn
    rw [show stop - idx = 0 by omega, findByteIn.go.eq_1, sliceList_eq_nil (Or.inl (by omega))]
    simp

private theorem parsePaxNat_refines (val : String) (offset : Nat) (key : String) :
    match parsePaxNat val offset key, parsePaxNatModel val offset with
    | .ok a, .ok b => a = b
    | .error err, .error k => tarErrKeyOf err = k ∧ !err.message.isEmpty = true
    | _, _ => False := by
  unfold parsePaxNat parsePaxNatModel
  rw [u64LimitImpl_eq]
  dsimp only
  generalize val.toList = cs
  by_cases h1 : cs.isEmpty = true
  · simp only [h1, ↓reduceIte]; exact ⟨rfl, nonEmpty_append_left (by decide)⟩
  simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (cs.head? == some '-') = true
  · simp only [h2, ↓reduceIte]; exact ⟨rfl, nonEmpty_append_left (by decide)⟩
  simp only [Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte]
  by_cases h3 : (!cs.all (fun c => '0' ≤ c && c ≤ '9')) = true
  · simp only [h3, ↓reduceIte]; exact ⟨rfl, nonEmpty_append_left (nonEmpty_append_left (by decide))⟩
  simp only [Bool.eq_false_iff.mpr h3, Bool.false_eq_true, ↓reduceIte]
  by_cases h4 : cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 ≥ u64Limit
  · simp only [h4, ↓reduceIte]; exact ⟨rfl, nonEmpty_append_left (nonEmpty_append_left (by decide))⟩
  simp only [h4, ↓reduceIte]

private theorem parsePaxMtime_refines (val : String) (offset : Nat) :
    match parsePaxMtime val offset, parsePaxMtimeModel val offset with
    | .ok a, .ok b => a = b
    | .error err, .error k => tarErrKeyOf err = k ∧ !err.message.isEmpty = true
    | _, _ => False := by
  unfold parsePaxMtime parsePaxMtimeModel
  rw [u64LimitImpl_eq]
  dsimp only
  generalize val.toList = cs
  by_cases h1 : cs.isEmpty = true
  · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
  simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (cs.head? == some '-') = true
  · simp only [h2, ↓reduceIte]; exact ⟨rfl, rfl⟩
  simp only [Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte]
  by_cases h3 : (cs.takeWhile (fun c => '0' ≤ c && c ≤ '9')).isEmpty = true
  · simp only [h3, ↓reduceIte]; exact ⟨rfl, rfl⟩
  simp only [Bool.eq_false_iff.mpr h3, Bool.false_eq_true, ↓reduceIte]
  generalize cs.drop (cs.takeWhile (fun c => '0' ≤ c && c ≤ '9')).length = rest
  cases rest with
  | nil =>
    by_cases h4 : (cs.takeWhile (fun c => '0' ≤ c && c ≤ '9')).foldl
        (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 ≥ u64Limit
    · simp only [h4, ↓reduceIte, Bool.not_true, Bool.false_eq_true]; exact ⟨rfl, rfl⟩
    · simp only [h4, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
  | cons c frac =>
    by_cases hdot : c = '.'
    · subst hdot
      by_cases hfk : (!frac.isEmpty && frac.all (fun c => '0' ≤ c && c ≤ '9')) = true
      · simp only [hfk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : (cs.takeWhile (fun c => '0' ≤ c && c ≤ '9')).foldl
            (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 ≥ u64Limit
        · simp only [h4, ↓reduceIte]; exact ⟨rfl, rfl⟩
        · simp only [h4, ↓reduceIte]
      · simp only [Bool.eq_false_iff.mpr hfk, Bool.not_false, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp [hdot, tarErrKeyOf]

private theorem applyPaxKey_refines {ov : PaxOverrides} {mov : PaxModelOverrides}
    (hrel : paxOvRel ov mov) (key val : String) (offset : Nat) :
    match applyPaxKey ov key val offset, applyPaxKeyModel mov key val offset with
    | .ok a, .ok b => paxOvRel a b
    | .error err, .error k => tarErrKeyOf err = k ∧ !err.message.isEmpty = true
    | _, _ => False := by
  rcases hrel with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  unfold applyPaxKey applyPaxKeyModel
  simp only [hasNulStringImpl_eq]
  by_cases kp : (key == "path") = true
  · simp only [kp, ↓reduceIte]; exact ⟨rfl, h2, h3, h4, h5, h6, h7, h8⟩
  simp only [Bool.eq_false_iff.mpr kp, Bool.false_eq_true, ↓reduceIte]
  by_cases kl : (key == "linkpath") = true
  · simp only [kl, ↓reduceIte]; exact ⟨h1, rfl, h3, h4, h5, h6, h7, h8⟩
  simp only [Bool.eq_false_iff.mpr kl, Bool.false_eq_true, ↓reduceIte]
  by_cases ku : (key == "uname") = true
  · simp only [ku, ↓reduceIte]
    by_cases hn : hasNulString val = true
    · simp only [hn, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [Bool.eq_false_iff.mpr hn, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h1, h2, rfl, h4, h5, h6, h7, h8⟩
  simp only [Bool.eq_false_iff.mpr ku, Bool.false_eq_true, ↓reduceIte]
  by_cases kg : (key == "gname") = true
  · simp only [kg, ↓reduceIte]
    by_cases hn : hasNulString val = true
    · simp only [hn, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · simp only [Bool.eq_false_iff.mpr hn, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h1, h2, h3, rfl, h5, h6, h7, h8⟩
  simp only [Bool.eq_false_iff.mpr kg, Bool.false_eq_true, ↓reduceIte]
  by_cases ks : (key == "size") = true
  · simp only [ks, ↓reduceIte, Except.map]
    have hn := parsePaxNat_refines val offset "size"
    cases hp1 : parsePaxNat val offset "size" <;> cases hp2 : parsePaxNatModel val offset <;>
      simp only [hp1, hp2] at hn ⊢
    · exact hn
    · subst hn; exact ⟨h1, h2, h3, h4, rfl, h6, h7, h8⟩
  simp only [Bool.eq_false_iff.mpr ks, Bool.false_eq_true, ↓reduceIte]
  by_cases kuid : (key == "uid") = true
  · simp only [kuid, ↓reduceIte, Except.map]
    have hn := parsePaxNat_refines val offset "uid"
    cases hp1 : parsePaxNat val offset "uid" <;> cases hp2 : parsePaxNatModel val offset <;>
      simp only [hp1, hp2] at hn ⊢
    · exact hn
    · subst hn; exact ⟨h1, h2, h3, h4, h5, h6, rfl, h8⟩
  simp only [Bool.eq_false_iff.mpr kuid, Bool.false_eq_true, ↓reduceIte]
  by_cases kgid : (key == "gid") = true
  · simp only [kgid, ↓reduceIte, Except.map]
    have hn := parsePaxNat_refines val offset "gid"
    cases hp1 : parsePaxNat val offset "gid" <;> cases hp2 : parsePaxNatModel val offset <;>
      simp only [hp1, hp2] at hn ⊢
    · exact hn
    · subst hn; exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl⟩
  simp only [Bool.eq_false_iff.mpr kgid, Bool.false_eq_true, ↓reduceIte]
  by_cases km : (key == "mtime") = true
  · simp only [km, ↓reduceIte, Except.map]
    have hn := parsePaxMtime_refines val offset
    cases hp1 : parsePaxMtime val offset <;> cases hp2 : parsePaxMtimeModel val offset <;>
      simp only [hp1, hp2] at hn ⊢
    · exact hn
    · subst hn; exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8⟩
  simp only [Bool.eq_false_iff.mpr km, Bool.false_eq_true, ↓reduceIte]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

private theorem parsePaxLen_eq_model (pax : ByteArray) (start stop : Nat) :
    parsePaxLen pax start stop = parsePaxLenList (sliceList pax start stop) := by
  unfold parsePaxLen parsePaxLenList
  by_cases hge : start ≥ stop
  · simp only [hge, ↓reduceIte, sliceList_eq_nil (Or.inl hge)]
  · simp only [hge, ↓reduceIte, sliceList_eq_data_toList]
    rfl

private theorem parsePaxPayload_go_refines (pax : ByteArray) (offset : Nat) :
    ∀ (fuel pos : Nat) (seenKeys : List String) (ov : PaxOverrides) (mov : PaxModelOverrides),
      pax.size - pos + 1 ≤ fuel →
      paxOvRel ov mov →
      match parsePaxPayload.go pax offset fuel pos seenKeys ov,
            parsePaxRecordsModel (sliceList pax pos pax.size) offset seenKeys mov with
      | .ok a, .ok b => paxOvRel a b
      | .error err, .error key => tarErrKeyOf err = key ∧ !err.message.isEmpty = true
      | _, _ => False := by
  intro fuel; induction fuel with
  | zero => intro pos _ _ _ hf; omega
  | succ fuel ih =>
    intro pos seenKeys ov mov hf hrel
    rw [parsePaxPayload.go.eq_2]
    by_cases hge : pos ≥ pax.size
    · simp only [hge, ↓reduceIte, sliceList_eq_nil (Or.inl hge), parsePaxRecordsModel.eq_1]
      exact hrel
    · simp only [hge, ↓reduceIte]
      have hpos : pos < pax.size := by omega
      have hcons : sliceList pax pos pax.size = pax[pos]'hpos :: sliceList pax (pos + 1) pax.size :=
        sliceList_cons hpos hpos
      have hraw_len : (sliceList pax pos pax.size).length = pax.size - pos := by
        rw [sliceList_length]; omega
      rw [hcons, parsePaxRecordsModel.eq_2, ← hcons]
      unfold parsePaxRecordStep
      have hsp := findByteIn_spec pax 0x20 pos pax.size
      dsimp only at hsp
      cases hfs : findByteIn pax 0x20 pos pax.size with
      | none =>
        simp only [hfs] at hsp
        simp only [hsp]; exact ⟨rfl, rfl⟩
      | some spIdx =>
        simp only [hfs] at hsp
        rcases hsp with ⟨hsp1, hsp2, _, hspLen, hspDrop⟩
        simp only [hspDrop]
        have hdigEq : (sliceList pax pos pax.size).takeWhile (· != 0x20) =
            sliceList pax pos spIdx := by
          have htk := sliceList_take pax pos pax.size ((sliceList pax pos pax.size).takeWhile (· != 0x20)).length
          have hpre := list_take_takeWhile_length (· != (0x20 : UInt8)) (sliceList pax pos pax.size)
          rw [← hpre, htk, hspLen, show min pax.size (pos + (spIdx - pos)) = spIdx by omega]
        rw [hdigEq, ← parsePaxLen_eq_model pax pos spIdx]
        cases hpl : parsePaxLen pax pos spIdx with
        | none => exact ⟨rfl, rfl⟩
        | some recLen =>
          by_cases hlt5 : recLen < 5
          · simp only [hlt5, ↓reduceIte]; exact ⟨rfl, rfl⟩
          · by_cases hgt : pos + recLen > pax.size
            · have hgtL : recLen > (sliceList pax pos pax.size).length := by rw [hraw_len]; omega
              simp only [hlt5, hgt, hgtL, ↓reduceIte]; exact ⟨rfl, rfl⟩
            · have hgtL : ¬(recLen > (sliceList pax pos pax.size).length) := by rw [hraw_len]; omega
              simp only [hlt5, hgt, hgtL, ↓reduceIte]
              have hnlbd : pos + recLen - 1 < pax.size := by omega
              have hlastEq : ((sliceList pax pos pax.size).take recLen).getLast? =
                  some (pax[pos + recLen - 1]'hnlbd) := by
                have ht := sliceList_take pax pos pax.size recLen
                rw [ht, show min pax.size (pos + recLen) = pos + recLen by omega]
                have hlen : (sliceList pax pos (pos + recLen)).length = recLen := by
                  rw [sliceList_length]; omega
                have hne : sliceList pax pos (pos + recLen) ≠ [] := by
                  intro he; rw [he] at hlen; simp at hlen; omega
                rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem]
                congr 1
                rw [sliceList_getElem]
                congr 1; omega
              simp only [hnlbd, ↓reduceDIte, hlastEq]
              by_cases hnl : pax[pos + recLen - 1]'hnlbd == 0x0a
              · have hneF : (some (pax[pos + recLen - 1]'hnlbd) != some (0x0a : UInt8)) = false := by
                  simp [bne, beq_iff_eq.mp hnl]
                simp only [hnl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hneF]
                have hkvEq : ((sliceList pax pos pax.size).drop (spIdx - pos + 1)).take
                    (recLen - 1 - (spIdx - pos + 1)) = sliceList pax (spIdx + 1) (pos + recLen - 1) := by
                  rw [sliceList_drop, sliceList_take,
                    show pos + (spIdx - pos + 1) = spIdx + 1 by omega,
                    show min pax.size (spIdx + 1 + (recLen - 1 - (spIdx - pos + 1))) =
                      max (spIdx + 1) (pos + recLen - 1) by omega]
                  by_cases hle : spIdx + 1 ≤ pos + recLen - 1
                  · rw [show max (spIdx + 1) (pos + recLen - 1) = pos + recLen - 1 by omega]
                  · rw [sliceList_eq_nil (Or.inl (by omega)), sliceList_eq_nil (Or.inl (by omega))]
                have hdLen : (sliceList pax pos spIdx).length = spIdx - pos := by
                  rw [sliceList_length]; omega
                rw [hdLen, hkvEq]
                have heq := findByteIn_spec pax 0x3d (spIdx + 1) (pos + recLen - 1)
                dsimp only at heq
                cases hfe : findByteIn pax 0x3d (spIdx + 1) (pos + recLen - 1) with
                | none =>
                  simp only [hfe] at heq
                  simp only [heq]; exact ⟨rfl, rfl⟩
                | some eqIdx =>
                  simp only [hfe] at heq
                  rcases heq with ⟨heq1, heq2, _, heqLen, heqDrop⟩
                  simp only [heqDrop]
                  have hkeyEq : ByteArray.mk (((sliceList pax (spIdx + 1) (pos + recLen - 1)).takeWhile (· != 0x3d))).toArray =
                      pax.extract (spIdx + 1) eqIdx := by
                    have hpre := sliceList_take pax (spIdx + 1) (pos + recLen - 1)
                      ((sliceList pax (spIdx + 1) (pos + recLen - 1)).takeWhile (· != 0x3d)).length
                    have ht := list_take_takeWhile_length (· != (0x3d : UInt8))
                      (sliceList pax (spIdx + 1) (pos + recLen - 1))
                    have hslice : (sliceList pax (spIdx + 1) (pos + recLen - 1)).takeWhile (· != 0x3d) =
                        sliceList pax (spIdx + 1) eqIdx := by
                      rw [← ht, hpre, heqLen,
                        show min (pos + recLen - 1) (spIdx + 1 + (eqIdx - (spIdx + 1))) = eqIdx by omega]
                    rw [hslice, sliceList_eq_data_toList]
                  have hvalEq : ByteArray.mk (sliceList pax (eqIdx + 1) (pos + recLen - 1)).toArray =
                      pax.extract (eqIdx + 1) (pos + recLen - 1) := by
                    rw [sliceList_eq_data_toList]
                  rw [hkeyEq, hvalEq]
                  cases String.fromUTF8? (pax.extract (spIdx + 1) eqIdx) with
                  | none => exact ⟨rfl, rfl⟩
                  | some key =>
                    cases String.fromUTF8? (pax.extract (eqIdx + 1) (pos + recLen - 1)) with
                    | none => exact ⟨rfl, rfl⟩
                    | some val =>
                      dsimp only
                      rw [hasNulStringImpl_eq]
                      by_cases hkbad : (key.isEmpty || hasNulString key || key.toList.contains '\n') = true
                      · simp only [hkbad, ↓reduceIte]; exact ⟨rfl, rfl⟩
                      · simp only [Bool.eq_false_iff.mpr hkbad, Bool.false_eq_true, ↓reduceIte]
                        by_cases hkdup : seenKeys.contains key = true
                        · simp only [hkdup, ↓reduceIte]; exact ⟨rfl, nonEmpty_append_left (by decide)⟩
                        · simp only [Bool.eq_false_iff.mpr hkdup, Bool.false_eq_true, ↓reduceIte]
                          have hsw : startsWithStr key "GNU.sparse." =
                              (key.toList.take 11 == "GNU.sparse.".toList) := rfl
                          rw [hsw]
                          by_cases hspfx : (key.toList.take 11 == "GNU.sparse.".toList) = true
                          · simp only [hspfx, ↓reduceIte]; exact ⟨rfl, rfl⟩
                          · simp only [Bool.eq_false_iff.mpr hspfx, Bool.false_eq_true, ↓reduceIte]
                            have hap := applyPaxKey_refines hrel key val offset
                            cases ha1 : applyPaxKey ov key val offset <;>
                              cases ha2 : applyPaxKeyModel mov key val offset <;>
                              simp only [ha1, ha2] at hap ⊢
                            · exact hap
                            · simp only [show 0 < recLen by omega, ↓reduceIte, sliceList_drop]
                              exact ih (pos + recLen) (key :: seenKeys) _ _ (by omega) hap
              · have hnlF : (pax[pos + recLen - 1]'hnlbd == 0x0a) = false := Bool.eq_false_iff.mpr hnl
                have hneT : (some (pax[pos + recLen - 1]'hnlbd) != some (0x0a : UInt8)) = true := by
                  simp [bne, hnlF]
                simp only [hnlF, Bool.not_false, ↓reduceIte, hneT]
                exact ⟨rfl, rfl⟩

/-- `Impl.parsePaxPayload` refines `Model.parsePaxRecordsModel` on all payloads and offsets. -/
theorem parsePaxPayload_refines (pax : ByteArray) (offset : Nat) :
    tarExceptRel paxOvRel (parsePaxPayload pax offset)
      (parsePaxRecordsModel (sliceList pax 0 pax.size) offset [] {}) := by
  have h := parsePaxPayload_go_refines pax offset (pax.size + 1) 0 [] {} {} (by omega) paxOvRel_empty
  unfold parsePaxPayload
  cases h1 : parsePaxPayload.go pax offset (pax.size + 1) 0 [] {} <;>
    cases h2 : parsePaxRecordsModel (sliceList pax 0 pax.size) offset [] {} <;>
    simp only [h1, h2] at h ⊢
  · exact .error h.1 h.2
  · exact .ok h

end LeanSwe.Tar.Proofs
