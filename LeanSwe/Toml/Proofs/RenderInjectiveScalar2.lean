import LeanSwe.Toml.Proofs.RenderInjectiveNum

/-!
# Datetime & Unquoted Scalar Disjointness and Prefix Injectivity

Proves `renderTime_inj`, `renderOffset_inj`, `scalarKindOf` 7-way disjointness, and
full `Impl`-independent prefix-injectivity (`TomlEquiv v1 v2 ∧ rem1 = rem2`) for all
unquoted TOML scalars.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

theorem renderTime_info {t : Std.Time.PlainTime} {fl : Option String} {ts : String}
    (hr : renderTime t fl = some ts) :
    (∃ h1 h2 m1 m2 s1 s2 fracCs, ts.toList = [h1, h2, ':', m1, m2, ':', s1, s2] ++ fracCs ∧
      [h1, h2, m1, m2, s1, s2].all isAsciiDigitModel = true ∧
      (fracCs.all fun c => isAsciiDigitModel c || c == '.') = true) ∧
    (ts.toList.all fun c => !isModelDelim c) = true ∧ NoCrStr ts := by
  unfold renderTime at hr
  split at hr
  · cases hr
  · rename_i hvt
    have hh_p := t.hour.property; have hm_p := t.minute.property; have hs_p := t.second.property
    dsimp at hs_p
    obtain ⟨hdh, _, hlh⟩ := padNatZero_props 2 t.hour.val.toNat
    obtain ⟨hdm, _, hlm⟩ := padNatZero_props 2 t.minute.val.toNat
    obtain ⟨hds, _, hls⟩ := padNatZero_props 2 t.second.val.toNat
    have hlh' := hlh (by decide) (by change t.hour.val.toNat < 100; omega)
    have hlm' := hlm (by decide) (by change t.minute.val.toNat < 100; omega)
    have hls' := hls (by decide) (by change t.second.val.toNat < 100; omega)
    rcases hhl : (padNatZero 2 t.hour.val.toNat).toList with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩ <;> rw [hhl] at hlh' <;> try (simp at hlh')
    rcases hml : (padNatZero 2 t.minute.val.toNat).toList with _ | ⟨m1, _ | ⟨m2, _ | _⟩⟩ <;> rw [hml] at hlm' <;> try (simp at hlm')
    rcases hsl : (padNatZero 2 t.second.val.toNat).toList with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩ <;> rw [hsl] at hls' <;> try (simp at hls')
    rw [hhl] at hdh; rw [hml] at hdm; rw [hsl] at hds
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hdh hdm hds
    have hbase : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat).toList =
        [h1, h2, ':', m1, m2, ':', s1, s2] := by
      simp only [String.toList_append, hhl, hml, hsl, show (":" : String).toList = [':'] from rfl]; rfl
    have cl (c) (hc : isAsciiDigitModel c = true) : (!isModelDelim c) = true ∧ c ≠ '\r' := by
      have h1 := isAsciiDigitModel_clean hc; simp only [Bool.and_eq_true, bne_iff_ne] at h1
      exact ⟨h1.1.1.1.1.1, h1.1.1.1.1.2⟩
    have hbase_nd : ([h1, h2, ':', m1, m2, ':', s1, s2].all fun c => !isModelDelim c) = true := by
      simp [(cl _ hdh.1).1, (cl _ hdh.2).1, (cl _ hdm.1).1, (cl _ hdm.2).1, (cl _ hds.1).1, (cl _ hds.2).1,
        show (!isModelDelim ':') = true by decide]
    have hbase_cr : '\r' ∉ [h1, h2, ':', m1, m2, ':', s1, s2] := by
      simp [(cl _ hdh.1).2.symm, (cl _ hdh.2).2.symm, (cl _ hdm.1).2.symm, (cl _ hdm.2).2.symm,
        (cl _ hds.1).2.symm, (cl _ hds.2).2.symm]
    cases fl with
    | none =>
      dsimp only at hr; split at hr
      · injection hr with hts; subst hts
        refine ⟨⟨h1, h2, m1, m2, s1, s2, [], by simpa using hbase, by simp [hdh, hdm, hds], rfl⟩,
          by rw [hbase]; exact hbase_nd, by unfold NoCrStr; rw [hbase]; exact hbase_cr⟩
      · cases hr
    | some ds =>
      dsimp only at hr; split at hr
      · rename_i hds_ok; injection hr with hts; subst hts
        simp only [Bool.and_eq_true] at hds_ok
        have hfull : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
            padNatZero 2 t.second.val.toNat ++ "." ++ ds).toList =
            [h1, h2, ':', m1, m2, ':', s1, s2] ++ ('.' :: ds.toList) := by
          simp only [String.toList_append, hbase, show ("." : String).toList = ['.'] from rfl, List.append_assoc, List.singleton_append]
        have hf_all : (('.' :: ds.toList).all fun c => isAsciiDigitModel c || c == '.') = true := by
          simp only [List.all_cons, beq_self_eq_true, Bool.or_true, Bool.true_and]
          exact List.all_eq_true.mpr fun c hc => Bool.or_eq_true_iff.mpr (Or.inl (List.all_eq_true.mp hds_ok.1.2 c hc))
        have hf_nd : (('.' :: ds.toList).all fun c => !isModelDelim c) = true := by
          simp only [List.all_cons, show (!isModelDelim '.') = true by decide, Bool.true_and]
          exact List.all_eq_true.mpr fun c hc => (cl c (List.all_eq_true.mp hds_ok.1.2 c hc)).1
        have hf_cr : '\r' ∉ ('.' :: ds.toList) := by
          intro hm; rcases List.mem_cons.mp hm with heq | htl
          · cases heq
          · exact (cl '\r' (List.all_eq_true.mp hds_ok.1.2 '\r' htl)).2 rfl
        refine ⟨⟨h1, h2, m1, m2, s1, s2, '.' :: ds.toList, hfull, by simp [hdh, hdm, hds], hf_all⟩,
          by rw [hfull, List.all_append, hbase_nd, hf_nd]; rfl,
          by unfold NoCrStr; rw [hfull, List.mem_append, not_or]; exact ⟨hbase_cr, hf_cr⟩⟩
      · cases hr

theorem renderTime_inj {t1 t2 : Std.Time.PlainTime} {fl1 fl2 : Option String} {ts : String}
    (h1 : renderTime t1 fl1 = some ts) (h2 : renderTime t2 fl2 = some ts) : t1 = t2 := by
  unfold renderTime at h1 h2
  cases hv1 : validTomlTime t1 <;> simp only [hv1, Bool.not_true, Bool.not_false, ↓reduceIte, reduceCtorEq] at h1
  cases hv2 : validTomlTime t2 <;> simp only [hv2, Bool.not_true, Bool.not_false, ↓reduceIte, reduceCtorEq] at h2
  have hs1_p := t1.second.property; dsimp at hs1_p
  have hs2_p := t2.second.property; dsimp at hs2_p
  have hh1 := (padNatZero_props 2 t1.hour.val.toNat).2.2 (by decide) (by have := t1.hour.property; change t1.hour.val.toNat < 100; omega)
  have hh2 := (padNatZero_props 2 t2.hour.val.toNat).2.2 (by decide) (by have := t2.hour.property; change t2.hour.val.toNat < 100; omega)
  have hm1 := (padNatZero_props 2 t1.minute.val.toNat).2.2 (by decide) (by have := t1.minute.property; change t1.minute.val.toNat < 100; omega)
  have hm2 := (padNatZero_props 2 t2.minute.val.toNat).2.2 (by decide) (by have := t2.minute.property; change t2.minute.val.toNat < 100; omega)
  have hs1 := (padNatZero_props 2 t1.second.val.toNat).2.2 (by decide) (by change t1.second.val.toNat < 100; omega)
  have hs2 := (padNatZero_props 2 t2.second.val.toNat).2.2 (by decide) (by change t2.second.val.toNat < 100; omega)
  have extractFrac (t : Std.Time.PlainTime) (fl : Option String)
      (hr : (match fl with
        | none => if t.nanosecond.val == 0 then some (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat) else none
        | some ds => if !ds.isEmpty && ds.toList.all isAsciiDigitModel && fracDigitsToNanosModel ds.toList == t.nanosecond.val.toNat then
            some (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat ++ "." ++ ds) else none) = some ts) :
      ∃ fcs : List Char,
        ts.toList = (padNatZero 2 t.hour.val.toNat).toList ++ ':' :: (padNatZero 2 t.minute.val.toNat).toList ++
          ':' :: (padNatZero 2 t.second.val.toNat).toList ++ fcs ∧
        ((fcs = [] ∧ t.nanosecond.val = 0) ∨ (∃ ds, fcs = '.' :: ds ∧ fracDigitsToNanosModel ds = t.nanosecond.val.toNat)) := by
    cases fl with
    | none =>
      dsimp only at hr; split at hr
      · rename_i hn0; injection hr with hts; subst hts
        refine ⟨[], ?_, Or.inl ⟨rfl, eq_of_beq hn0⟩⟩
        simp [String.toList_append, show (":" : String).toList = [':'] from rfl, List.append_assoc]
      · cases hr
    | some ds =>
      dsimp only at hr; split at hr
      · rename_i hd_ok; injection hr with hts; subst hts
        simp only [Bool.and_eq_true, beq_iff_eq] at hd_ok
        refine ⟨'.' :: ds.toList, ?_, Or.inr ⟨ds.toList, rfl, hd_ok.2⟩⟩
        simp [String.toList_append, show (":" : String).toList = [':'] from rfl, show ("." : String).toList = ['.'] from rfl, List.append_assoc]
      · cases hr
  obtain ⟨fcs1, hts1, hns1⟩ := extractFrac t1 fl1 h1
  obtain ⟨fcs2, hts2, hns2⟩ := extractFrac t2 fl2 h2
  have heq := hts1.symm.trans hts2
  simp only [List.append_assoc, List.cons_append] at heq
  obtain ⟨ehl, r1⟩ := List.append_inj heq (hh1.trans hh2.symm)
  have r2 := (List.cons.inj r1).2
  obtain ⟨eml, r3⟩ := List.append_inj r2 (hm1.trans hm2.symm)
  have r4 := (List.cons.inj r3).2
  obtain ⟨esl, efcs⟩ := List.append_inj r4 (hs1.trans hs2.symm)
  subst efcs
  have ehr : t1.hour = t2.hour := Subtype.ext (by
    have := padNatZero_inj (String.ext_iff.mpr ehl)
    have := t1.hour.property; have := t2.hour.property
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ t1.hour.val by omega)
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ t2.hour.val by omega); omega)
  have emin : t1.minute = t2.minute := Subtype.ext (by
    have := padNatZero_inj (String.ext_iff.mpr eml)
    have := t1.minute.property; have := t2.minute.property
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ t1.minute.val by omega)
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ t2.minute.val by omega); omega)
  have esec : t1.second = t2.second := Subtype.ext (by
    have := padNatZero_inj (String.ext_iff.mpr esl)
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ t1.second.val from hs1_p.1)
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ t2.second.val from hs2_p.1); omega)
  have enano : t1.nanosecond = t2.nanosecond := Subtype.ext (by
    have hn1_0 : (0 : Int) ≤ t1.nanosecond.val := t1.nanosecond.property.1
    have hn2_0 : (0 : Int) ≤ t2.nanosecond.val := t2.nanosecond.property.1
    rcases hns1 with ⟨hf1, z1⟩ | ⟨ds1, hf1, fn1⟩ <;> rcases hns2 with ⟨hf2, z2⟩ | ⟨ds2, hf2, fn2⟩
    · exact z1.trans z2.symm
    · rw [hf1] at hf2; cases hf2
    · rw [hf1] at hf2; cases hf2
    · rw [hf1] at hf2
      obtain ⟨_, rfl⟩ := List.cons.inj hf2
      exact (Int.toNat_of_nonneg hn1_0).symm.trans
        ((congrArg Int.ofNat (fn1.symm.trans fn2)).trans (Int.toNat_of_nonneg hn2_0)))
  exact Std.Time.PlainTime.ext ehr emin esec enano

theorem renderOffset_info {o : Std.Time.TimeZone.Offset} {st : OffsetStyle} {os : String}
    (hr : renderOffset o st = some os) :
    (∃ o0 osRest, os.toList = o0 :: osRest ∧ (o0 = 'Z' ∨ o0 = 'z' ∨ o0 = '+' ∨ o0 = '-')) ∧
    (os.toList.all fun c => !isModelDelim c) = true ∧ NoCrStr os := by
  unfold renderOffset at hr
  split at hr
  · cases hr
  · rename_i hvo
    split at hr
    · cases st <;> simp only [Option.some.injEq] at hr <;> subst hr
      · exact ⟨⟨'Z', [], rfl, Or.inl rfl⟩, by decide, by decide⟩
      · exact ⟨⟨'z', [], rfl, Or.inr (Or.inl rfl)⟩, by decide, by decide⟩
      · exact ⟨⟨'+', ['0', '0', ':', '0', '0'], rfl, Or.inr (Or.inr (Or.inl rfl))⟩, by decide, by decide⟩
      · exact ⟨⟨'-', ['0', '0', ':', '0', '0'], rfl, Or.inr (Or.inr (Or.inr rfl))⟩, by decide, by decide⟩
    · simp only [Option.some.injEq] at hr; subst hr
      obtain ⟨hdh, _⟩ := padNatZero_props 2 (o.second.val.natAbs / 60 / 60)
      obtain ⟨hdm, _⟩ := padNatZero_props 2 ((o.second.val.natAbs / 60) % 60)
      have cl (c) (hc : isAsciiDigitModel c = true) : (!isModelDelim c) = true ∧ c ≠ '\r' := by
        have h1 := isAsciiDigitModel_clean hc; simp only [Bool.and_eq_true, bne_iff_ne] at h1
        exact ⟨h1.1.1.1.1.1, h1.1.1.1.1.2⟩
      have hdh_nd : ((padNatZero 2 (o.second.val.natAbs / 60 / 60)).toList.all fun c => !isModelDelim c) = true :=
        List.all_eq_true.mpr fun c hc => (cl c (List.all_eq_true.mp hdh c hc)).1
      have hdm_nd : ((padNatZero 2 ((o.second.val.natAbs / 60) % 60)).toList.all fun c => !isModelDelim c) = true :=
        List.all_eq_true.mpr fun c hc => (cl c (List.all_eq_true.mp hdm c hc)).1
      have hdh_cr : NoCrStr (padNatZero 2 (o.second.val.natAbs / 60 / 60)) :=
        fun hm => (cl '\r' (List.all_eq_true.mp hdh '\r' hm)).2 rfl
      have hdm_cr : NoCrStr (padNatZero 2 ((o.second.val.natAbs / 60) % 60)) :=
        fun hm => (cl '\r' (List.all_eq_true.mp hdm '\r' hm)).2 rfl
      by_cases hneg : o.second.val < 0
      · simp only [hneg, ↓reduceIte]
        refine ⟨⟨'-', (padNatZero 2 (o.second.val.natAbs / 60 / 60) ++ ":" ++ padNatZero 2 ((o.second.val.natAbs / 60) % 60)).toList,
          by simp [String.toList_append, show ("-" : String).toList = ['-'] from rfl, List.append_assoc],
          Or.inr (Or.inr (Or.inr rfl))⟩, ?_,
          noCrStr_append (noCrStr_append (noCrStr_append (by decide) hdh_cr) (by decide)) hdm_cr⟩
        simp only [String.toList_append, List.all_append, hdh_nd, hdm_nd]
        decide
      · simp only [hneg, ↓reduceIte]
        refine ⟨⟨'+', (padNatZero 2 (o.second.val.natAbs / 60 / 60) ++ ":" ++ padNatZero 2 ((o.second.val.natAbs / 60) % 60)).toList,
          by simp [String.toList_append, show ("+" : String).toList = ['+'] from rfl, List.append_assoc],
          Or.inr (Or.inr (Or.inl rfl))⟩, ?_,
          noCrStr_append (noCrStr_append (noCrStr_append (by decide) hdh_cr) (by decide)) hdm_cr⟩
        simp only [String.toList_append, List.all_append, hdh_nd, hdm_nd]
        decide

theorem renderOffset_inj {o1 o2 : Std.Time.TimeZone.Offset} {st1 st2 : OffsetStyle} {os : String}
    (h1 : renderOffset o1 st1 = some os) (h2 : renderOffset o2 st2 = some os) : o1 = o2 := by
  have nonzero_not_zero_str (o : Std.Time.TimeZone.Offset) (hvo : validTomlOffset o = true)
      (hnz : o.second.val ≠ 0) :
      let s := (if o.second.val < 0 then "-" else "+") ++
        padNatZero 2 (o.second.val.natAbs / 60 / 60) ++ ":" ++ padNatZero 2 ((o.second.val.natAbs / 60) % 60)
      s ≠ "Z" ∧ s ≠ "z" ∧ s ≠ "+00:00" ∧ s ≠ "-00:00" := by
    have hv : o.second.val % 60 = 0 ∧ -86340 ≤ o.second.val ∧ o.second.val ≤ 86340 := by
      simpa [validTomlOffset] using hvo
    dsimp only
    have ham_pos : 0 < o.second.val.natAbs / 60 := by omega
    have hlen_h := (padNatZero_props 2 (o.second.val.natAbs / 60 / 60)).2.2
      (by decide) (by change o.second.val.natAbs / 60 / 60 < 100; omega)
    have hlen_m := (padNatZero_props 2 ((o.second.val.natAbs / 60) % 60)).2.2
      (by decide) (by change (o.second.val.natAbs / 60) % 60 < 100; omega)
    have hnot00 : ¬(padNatZero 2 (o.second.val.natAbs / 60 / 60) = "00" ∧
        padNatZero 2 ((o.second.val.natAbs / 60) % 60) = "00") := by
      rintro ⟨eh, em⟩
      have zh := padNatZero_inj (eh.trans (show "00" = padNatZero 2 0 from rfl))
      have zm := padNatZero_inj (em.trans (show "00" = padNatZero 2 0 from rfl))
      omega
    have hsgn_len : (if o.second.val < 0 then "-" else "+").toList.length = 1 := by split <;> rfl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> have hl := congrArg String.toList heq
    · have hlen := congrArg List.length hl
      simp only [String.toList_append, List.length_append, hsgn_len, hlen_h, hlen_m,
        show (":" : String).toList.length = 1 from rfl, show ("Z" : String).toList.length = 1 from rfl] at hlen
      omega
    · have hlen := congrArg List.length hl
      simp only [String.toList_append, List.length_append, hsgn_len, hlen_h, hlen_m,
        show (":" : String).toList.length = 1 from rfl, show ("z" : String).toList.length = 1 from rfl] at hlen
      omega
    · by_cases hneg : o.second.val < 0
      · simp [hneg, String.toList_append] at hl
      · simp only [hneg, ↓reduceIte, String.toList_append, show ("+" : String).toList = ['+'] from rfl,
          show (":" : String).toList = [':'] from rfl,
          show ("+00:00" : String).toList = '+' :: (['0', '0'] ++ ':' :: ['0', '0']) from rfl,
          List.singleton_append, List.append_assoc] at hl
        obtain ⟨eh, r1⟩ := List.append_inj (List.cons.inj hl).2
          (hlen_h.trans (show (['0', '0'] : List Char).length = 2 from rfl))
        have em := (List.cons.inj r1).2
        exact hnot00 ⟨String.ext_iff.mpr eh, String.ext_iff.mpr em⟩
    · by_cases hneg : o.second.val < 0
      · simp only [hneg, ↓reduceIte, String.toList_append, show ("-" : String).toList = ['-'] from rfl,
          show (":" : String).toList = [':'] from rfl,
          show ("-00:00" : String).toList = '-' :: (['0', '0'] ++ ':' :: ['0', '0']) from rfl,
          List.singleton_append, List.append_assoc] at hl
        obtain ⟨eh, r1⟩ := List.append_inj (List.cons.inj hl).2
          (hlen_h.trans (show (['0', '0'] : List Char).length = 2 from rfl))
        have em := (List.cons.inj r1).2
        exact hnot00 ⟨String.ext_iff.mpr eh, String.ext_iff.mpr em⟩
      · simp [hneg, String.toList_append] at hl
  unfold renderOffset at h1 h2
  cases hvo1 : validTomlOffset o1 <;> simp [hvo1] at h1
  cases hvo2 : validTomlOffset o2 <;> simp [hvo2] at h2
  by_cases hz1 : o1.second.val = 0
  · by_cases hz2 : o2.second.val = 0
    · exact Std.Time.TimeZone.Offset.ext (Std.Time.Internal.UnitVal.ext (hz1.trans hz2.symm))
    · exfalso
      simp only [hz1, hz2, ↓reduceIte, Option.some.injEq] at h1 h2
      have hne := nonzero_not_zero_str o2 hvo2 hz2
      subst h2
      cases st1 <;> simp only [Option.some.injEq] at h1
      · exact hne.1 h1.symm
      · exact hne.2.1 h1.symm
      · exact hne.2.2.1 h1.symm
      · exact hne.2.2.2 h1.symm
  · by_cases hz2 : o2.second.val = 0
    · exfalso
      simp only [hz1, hz2, ↓reduceIte, Option.some.injEq] at h1 h2
      have hne := nonzero_not_zero_str o1 hvo1 hz1
      subst h1
      cases st2 <;> simp only [Option.some.injEq] at h2
      · exact hne.1 h2.symm
      · exact hne.2.1 h2.symm
      · exact hne.2.2.1 h2.symm
      · exact hne.2.2.2 h2.symm
    · simp only [hz1, hz2, ↓reduceIte, Option.some.injEq] at h1 h2
      have hv1 : o1.second.val % 60 = 0 ∧ -86340 ≤ o1.second.val ∧ o1.second.val ≤ 86340 := by simpa [validTomlOffset] using hvo1
      have hv2 : o2.second.val % 60 = 0 ∧ -86340 ≤ o2.second.val ∧ o2.second.val ≤ 86340 := by simpa [validTomlOffset] using hvo2
      have hlh1 := (padNatZero_props 2 (o1.second.val.natAbs / 60 / 60)).2.2
        (by decide) (by change o1.second.val.natAbs / 60 / 60 < 100; omega)
      have hlh2 := (padNatZero_props 2 (o2.second.val.natAbs / 60 / 60)).2.2
        (by decide) (by change o2.second.val.natAbs / 60 / 60 < 100; omega)
      have heq := congrArg String.toList (h1.trans h2.symm)
      simp only [String.toList_append, show (":" : String).toList = [':'] from rfl, List.append_assoc, List.singleton_append] at heq
      have h1s : (if o1.second.val < 0 then "-" else "+").toList = [if decide (o1.second.val < 0) then '-' else '+'] := by split <;> simp_all
      have h2s : (if o2.second.val < 0 then "-" else "+").toList = [if decide (o2.second.val < 0) then '-' else '+'] := by split <;> simp_all
      rw [h1s, h2s, List.singleton_append, List.singleton_append] at heq
      obtain ⟨esgn, erest⟩ := List.cons.inj heq
      obtain ⟨ehl, erest2⟩ := List.append_inj erest (hlh1.trans hlh2.symm)
      have eml := (List.cons.inj erest2).2
      have ehh := padNatZero_inj (String.ext_iff.mpr ehl)
      have emm := padNatZero_inj (String.ext_iff.mpr eml)
      have enat : o1.second.val.natAbs = o2.second.val.natAbs := by omega
      have eval_eq : o1.second.val = o2.second.val := by
        by_cases hn1 : o1.second.val < 0 <;> by_cases hn2 : o2.second.val < 0
        · omega
        · simp [hn1, hn2] at esgn
        · simp [hn1, hn2] at esgn
        · omega
      exact Std.Time.TimeZone.Offset.ext (Std.Time.Internal.UnitVal.ext eval_eq)

/-- Drop time body characters (`'0'..'9'`, `':'`, `'.'`) up to timezone offset start. -/
def dropTimeBodyChars : List Char → List Char
  | c :: cs => if isAsciiDigitModel c || c == ':' || c == '.' then dropTimeBodyChars cs else c :: cs
  | [] => []

theorem dropTimeBodyChars_append {ts os : String}
    {t : Std.Time.PlainTime} {fl : Option String} {o : Std.Time.TimeZone.Offset} {st : OffsetStyle}
    (ht : renderTime t fl = some ts) (ho : renderOffset o st = some os) :
    dropTimeBodyChars (ts.toList ++ os.toList) = os.toList := by
  obtain ⟨⟨h1, h2, m1, m2, s1, s2, fracCs, hts, hdig, hfrac⟩, _, _⟩ := renderTime_info ht
  obtain ⟨⟨o0, orest, hos, ho0⟩, _, _⟩ := renderOffset_info ho
  have hts_all : (ts.toList.all fun c => isAsciiDigitModel c || c == ':' || c == '.') = true := by
    rw [hts, List.all_append]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hdig ⊢
    refine ⟨⟨by simp [hdig.1], by simp [hdig.2.1], by decide, by simp [hdig.2.2.1],
      by simp [hdig.2.2.2.1], by decide, by simp [hdig.2.2.2.2.1], by simp [hdig.2.2.2.2.2]⟩, ?_⟩
    exact List.all_eq_true.mpr fun c hc => by
      rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hfrac c hc) with hd | hp
      · simp [hd]
      · simp [hp]
  have ho0_not : (isAsciiDigitModel o0 || o0 == ':' || o0 == '.') = false := by
    rcases ho0 with rfl | rfl | rfl | rfl <;> decide
  have haux : ∀ l : List Char, (l.all fun c => isAsciiDigitModel c || c == ':' || c == '.') = true →
      dropTimeBodyChars (l ++ o0 :: orest) = o0 :: orest := by
    intro l hl; induction l with
    | nil => simp [dropTimeBodyChars, ho0_not]
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hl
      simp [dropTimeBodyChars, hl.1, ih hl.2]
  rw [hos]; exact haux ts.toList hts_all

theorem splitModelUnquoted_spaceDateTime {d : Std.Time.PlainDate} {t : Std.Time.PlainTime}
    {fl : Option String} {ds ts suf : String} {rem : List Char}
    (hd : renderDate d = some ds) (ht : renderTime t fl = some ts)
    (hsuf : (suf.toList.all fun c => !isModelDelim c) = true) (hrem : ModelDelimTail rem) :
    splitModelUnquoted ((ds ++ " " ++ ts ++ suf).toList ++ rem) =
      ((ds ++ " " ++ ts ++ suf).toList, rem) := by
  obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, hdd⟩, _, _⟩ := renderDate_info hd
  obtain ⟨⟨h1, h2, min1, min2, s1, s2, fracCs, hts, htd, _⟩, ht_nd, _⟩ := renderTime_info ht
  have hfrac_nd : (fracCs.all fun c => !isModelDelim c) = true := by
    rw [hts, List.all_append] at ht_nd; exact (Bool.and_eq_true_iff.mp ht_nd).2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hdd htd
  have hfull : (ds ++ " " ++ ts ++ suf).toList =
      [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, ' ', h1, h2, ':', min1, min2, ':', s1, s2] ++
        (fracCs ++ suf.toList) := by
    simp [String.toList_append, hds, hts, show (" " : String).toList = [' '] from rfl]
  rw [hfull, List.append_assoc]
  simp only [List.cons_append, List.nil_append, splitModelUnquoted, List.all_cons, List.all_nil,
    hdd.1, hdd.2.1, hdd.2.2.1, hdd.2.2.2.1, hdd.2.2.2.2.1, hdd.2.2.2.2.2.1,
    hdd.2.2.2.2.2.2.1, hdd.2.2.2.2.2.2.2, htd.1, htd.2.1, htd.2.2.1, htd.2.2.2.1, htd.2.2.2.2.1,
    htd.2.2.2.2.2, Bool.and_self, ↓reduceIte]
  rw [takeModelNonDelim_append (fracCs ++ suf.toList) rem
    (by simp [List.all_append, hfrac_nd, hsuf]) (fun c r h => (hrem c r h).1)]

/-- Check whether `vt` is one of the 7 unquoted scalar `ValueTape` constructors. -/
def isUnquotedTape : ValueTape → Bool
  | .string _ | .array _ _ | .inlineTable _ _ => false
  | _ => true

/-- Classify a rendered unquoted scalar character list into 7 disjoint TOML scalar categories (`0..6`). -/
def scalarKindOf (cs : List Char) : Nat :=
  let isSpec :=
    cs == ['i', 'n', 'f'] || cs == ['+', 'i', 'n', 'f'] || cs == ['-', 'i', 'n', 'f'] ||
    cs == ['n', 'a', 'n'] || cs == ['+', 'n', 'a', 'n'] || cs == ['-', 'n', 'a', 'n']
  if cs == ['t', 'r', 'u', 'e'] || cs == ['f', 'a', 'l', 's', 'e'] then 0
  else if decide (cs.length ≥ 10) && cs[4]? == some '-' && cs[7]? == some '-' then
    if cs.length == 10 then 1
    else if (cs.drop 11).any (fun c => c == 'Z' || c == 'z' || c == '+' || c == '-') then 2
    else 3
  else if cs.contains ':' then 4
  else if !(cs.take 2 == ['0', 'x']) &&
      (cs.contains '.' || cs.contains 'e' || cs.contains 'E' || isSpec) then 5
  else 6

theorem float_not_date_dashes (cs : List Char) (f : Float)
    (h : NumParse.Model.parseFloatModelChars cs = .ok f) :
    ¬(cs[4]? = some '-' ∧ cs[7]? = some '-') := by
  have no_dash_digits : ∀ a c l m c' r,
      NumParse.Model.consumeDecFloatDigits a c l = .ok (m, c', r) →
      ∃ p, l = p ++ r ∧ '-' ∉ p := by
    intro a c l m c' r hc
    fun_induction NumParse.Model.consumeDecFloatDigits a c l with
    | case1 => simp only [Except.ok.injEq, Prod.mk.injEq] at hc; exact ⟨[], by simp [← hc.2.2], by simp⟩
    | case2 _ _ ch cs hd ih =>
      obtain ⟨p, hcs, hp⟩ := ih hc
      have hne : ch ≠ '-' := fun e => by subst e; revert hd; decide
      exact ⟨'_' :: ch :: p, by simp [hcs], by simp [hne.symm, hp]⟩
    | case3 | case4 => simp at hc
    | case5 _ _ ch cs _ _ hd ih =>
      obtain ⟨p, hcs, hp⟩ := ih hc
      have hne : ch ≠ '-' := fun e => by subst e; revert hd; decide
      exact ⟨ch :: p, by simp [hcs], by simp [hne.symm, hp]⟩
    | case6 => simp only [Except.ok.injEq, Prod.mk.injEq] at hc; exact ⟨[], by simp [← hc.2.2], by simp⟩
  have count_le_exp : ∀ afterE (g : Int → Float),
      ((match NumParse.Model.parseFloatExpPart afterE with
       | .error k => .error k
       | .ok (ev, ae) => if ae.isEmpty then .ok (g ev) else .error .trailingChars) :
         Except NumParseErrorKind Float) = .ok f →
      afterE.count '-' ≤ 1 := by
    intro afterE g hexp
    cases he : NumParse.Model.parseFloatExpPart afterE with
    | error => simp [he] at hexp
    | ok res =>
      rcases res with ⟨ev, ae⟩; rw [he] at hexp; dsimp only at hexp
      cases ae with | cons _ _ => simp at hexp | nil =>
      simp only [NumParse.Model.parseFloatExpPart.eq_def] at he
      split at he <;> try cases he
      rename_i c0 r0 _ hlet; split at he <;> try cases he
      rename_i hd0; split at he <;> try cases he
      rename_i _ _ _ hc
      obtain ⟨p, hr0, hp⟩ := no_dash_digits _ _ _ _ _ _ hc; rw [List.append_nil] at hr0; subst p
      have hc0 : c0 ≠ '-' := fun e => by subst e; revert hd0; decide
      have hcnt0 : (c0 :: r0).count '-' = 0 := List.count_eq_zero.mpr (by simp [hc0.symm, hp])
      split at hlet
      · dsimp at hlet; rw [hlet, List.count_cons]; simp [hcnt0]
      · dsimp at hlet; rw [hlet, List.count_cons]; simp [hcnt0]
      · dsimp at hlet; rw [hlet, hcnt0]; decide
  have body_count : ∀ body (neg : Bool),
      ((match body with
       | 'i' :: 'n' :: 'f' :: r =>
         match r with | [] => .ok (if neg then -Float.inf else Float.inf) | _ :: _ => .error .trailingChars
       | 'n' :: 'a' :: 'n' :: r =>
         match r with | [] => .ok Float.nan | _ :: _ => .error .trailingChars
       | _ =>
         match NumParse.Model.parseFloatIntPart body with
         | .error k => .error k
         | .ok (iv, ai) =>
           match ai with
           | '.' :: ad =>
             match ad with
             | '_' :: _ => .error .invalidUnderscore
             | c :: r =>
               if NumParse.Model.isDecDigit c then
                 match NumParse.Model.consumeDecFloatDigits (iv * 10 + (c.toNat - '0'.toNat)) 1 r with
                 | .error k => .error k
                 | .ok (man, fc, af) =>
                   match af with
                   | 'e' :: ae =>
                     match NumParse.Model.parseFloatExpPart ae with
                     | .error k => .error k
                     | .ok (ev, ax) =>
                       if ax.isEmpty then .ok (evalFloat neg man (ev - Int.ofNat fc))
                       else .error .trailingChars
                   | 'E' :: ae =>
                     match NumParse.Model.parseFloatExpPart ae with
                     | .error k => .error k
                     | .ok (ev, ax) =>
                       if ax.isEmpty then .ok (evalFloat neg man (ev - Int.ofNat fc))
                       else .error .trailingChars
                   | [] => .ok (evalFloat neg man (-Int.ofNat fc))
                   | _ :: _ => .error .trailingChars
               else .error .invalidSyntax
             | [] => .error .invalidSyntax
           | 'e' :: ae =>
             match NumParse.Model.parseFloatExpPart ae with
             | .error k => .error k
             | .ok (ev, ax) =>
               if ax.isEmpty then .ok (evalFloat neg iv ev) else .error .trailingChars
           | 'E' :: ae =>
             match NumParse.Model.parseFloatExpPart ae with
             | .error k => .error k
             | .ok (ev, ax) =>
               if ax.isEmpty then .ok (evalFloat neg iv ev) else .error .trailingChars
           | _ => .error .invalidSyntax) :
         Except NumParseErrorKind Float) = .ok f → body.count '-' ≤ 1 := by
    intro body neg hb
    split at hb
    · split at hb <;> first | decide | cases hb
    · split at hb <;> first | decide | cases hb
    · split at hb <;> try cases hb
      rename_i iv ai hip
      have hip_nodash : ∃ p, body = p ++ ai ∧ p.count '-' = 0 := by
        unfold NumParse.Model.parseFloatIntPart at hip; split at hip <;> try cases hip
        · split at hip
          · split at hip <;> try cases hip
            split at hip
            · repeat (split at hip; all_goals try cases hip)
            · cases hip; exact ⟨['0'], rfl, rfl⟩
          · cases hip; exact ⟨['0'], rfl, rfl⟩
        · rename_i c r _ _ _ _; split at hip <;> try cases hip
          rename_i hd; split at hip <;> try cases hip
          rename_i _ _ rem hc
          obtain ⟨p, hr, hp⟩ := no_dash_digits _ _ _ _ _ _ hc
          have hc_ne : c ≠ '-' := fun e => by subst e; revert hd; decide
          exact ⟨c :: p, by simp [hr], List.count_eq_zero.mpr (by simp [hc_ne.symm, hp])⟩
      obtain ⟨ip, hbody, hip0⟩ := hip_nodash
      split at hb <;> try cases hb
      · rename_i ad; split at hb <;> try cases hb
        rename_i c r _; split at hb <;> try cases hb
        rename_i hd; split at hb <;> try cases hb
        rename_i man fc af hcf
        obtain ⟨fp, hr, hfp⟩ := no_dash_digits _ _ _ _ _ _ hcf
        have hc_ne : c ≠ '-' := fun e => by subst e; revert hd; decide
        have hfp0 : ('.' :: c :: fp).count '-' = 0 := List.count_eq_zero.mpr (by simp [hc_ne.symm, hfp])
        rw [hbody, hr]
        have haf_le : af.count '-' ≤ 1 := by
          split at hb
          · simp only [List.count_cons, show ('e' == '-') = false from rfl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact count_le_exp _ _ hb
          · simp only [List.count_cons, show ('E' == '-') = false from rfl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact count_le_exp _ _ hb
          · cases hb; decide
          · cases hb
        have : ip ++ ('.' :: c :: (fp ++ af)) = ip ++ ('.' :: c :: fp) ++ af := by simp [List.append_assoc]
        rw [this, List.count_append, List.count_append, hip0, hfp0]; omega
      · rename_i ae; rw [hbody, List.count_append, hip0, Nat.zero_add, List.count_cons]
        simp only [show ('e' == '-') = false from rfl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact count_le_exp ae _ hb
      · rename_i ae; rw [hbody, List.count_append, hip0, Nat.zero_add, List.count_cons]
        simp only [show ('E' == '-') = false from rfl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact count_le_exp ae _ hb
  have hdrop1 : (cs.drop 1).count '-' ≤ 1 := by
    unfold NumParse.Model.parseFloatModelChars at h; split at h
    · cases h
    · split at h; rename_i _ _ _ neg body hsign
      have hbc := body_count body neg h
      split at hsign
      · injection hsign with _ hb; subst hb; simpa using hbc
      · injection hsign with _ hb; subst hb; simpa using hbc
      · injection hsign with _ hb; subst hb
        cases cs with
        | nil => decide
        | cons c0 cs' => simp only [List.drop_succ_cons, List.drop_zero]; rw [List.count_cons] at hbc; omega
  rintro ⟨h4, h7⟩
  rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, _ | ⟨c7, tl⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h4 h7
  subst h4 h7
  simp only [List.drop_succ_cons, List.drop_zero, List.count_cons, beq_self_eq_true, ↓reduceIte] at hdrop1
  omega

end LeanSwe.Toml.Proofs
