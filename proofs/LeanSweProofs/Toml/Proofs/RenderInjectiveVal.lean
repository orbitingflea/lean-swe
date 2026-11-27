import LeanSweProofs.Toml.Proofs.RenderInjectiveString
import LeanSweProofs.Toml.Proofs.RenderInjectiveScalar2
import LeanSweProofs.Toml.Proofs.RenderInjectiveSkel2

/-!
# Unquoted Scalar Injectivity & Value Head Classification

Proves `unquotedScalar_injective` and `renderValueInline_head` across all `TomlValue`
and `ValueTape` constructors without importing `Toml.Impl`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem dateTimeSep_info (sep : DateTimeSep) :
    ∃ ch, (renderDateTimeSep sep).toList = [ch] ∧ (ch = 'T' ∨ ch = 't' ∨ ch = ' ') ∧ NoCrStr (renderDateTimeSep sep) := by
  cases sep
  · exact ⟨'T', rfl, Or.inl rfl, by decide⟩
  · exact ⟨'t', rfl, Or.inr (Or.inl rfl), by decide⟩
  · exact ⟨' ', rfl, Or.inr (Or.inr rfl), by decide⟩

private theorem int_isValid_of_render {n : Int64} {lex? : Option String} {rs : String}
    (hr : renderValueInline (.int n) (.int lex?) = some rs) : isValidIntLex rs n = true := by
  cases lex? with
  | none =>
    simp only [renderValueInline, Option.some.injEq] at hr; subst hr
    exact formatInt64Canonical_isValidIntLex n
  | some lex =>
    simp only [renderValueInline] at hr; split at hr
    · rename_i hv; injection hr with hrs; subst hrs; exact hv
    · cases hr

private theorem float_isValid_of_render {f : Float} {lex? : Option String} {rs : String}
    (hr : renderValueInline (.float f) (.float lex?) = some rs) : isValidFloatLex rs f = true := by
  cases lex? with
  | none =>
    simp only [renderValueInline] at hr
    have hc := canonicalFloat_isValidFloatLex f
    if h1 : f.isNaN = true then simp [h1] at hr; subst hr; exact hc.1 h1 else
    if h2 : (f == Float.inf) = true then simp [h1, h2] at hr; subst hr; exact hc.2.1 h2 else
    if h3 : (f == -Float.inf) = true then simp [h1, h2, h3] at hr; subst hr; exact hc.2.2.1 h3 else
    if h4 : (f.toBits == (0.0 : Float).toBits) = true then
      simp [h1, h2, h3, h4] at hr; subst hr; exact hc.2.2.2.1 (eq_of_beq h4)
    else if h5 : (f.toBits == (-0.0 : Float).toBits) = true then
      simp [h1, h2, h3, h4, h5] at hr; subst hr; exact hc.2.2.2.2 (eq_of_beq h5)
    else simp [h1, h2, h3, h4, h5] at hr
  | some lex =>
    simp only [renderValueInline] at hr; split at hr
    · rename_i hv; injection hr with hrs; subst hrs; exact hv
    · cases hr

/-- Every rendered unquoted scalar has clean non-delimiter characters, safe non-quote/bracket head, and exact `splitModelUnquoted` recovery. -/
theorem unquotedScalar_info {v : TomlValue} {vt : ValueTape} {rs : String}
    (hunq : isUnquotedTape vt = true) (hr : renderValueInline v vt = some rs) :
    NoCrStr rs ∧
    (∃ c0 r0, rs.toList = c0 :: r0 ∧ isModelDelim c0 = false ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{') ∧
    (∀ rem, ModelDelimTail rem → splitModelUnquoted (rs.toList ++ rem) = (rs.toList, rem)) := by
  cases vt with
  | string _ | array _ _ | inlineTable _ _ => simp [isUnquotedTape] at hunq
  | bool =>
    cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
    rename_i b; injection hr with hrs; subst hrs
    cases b
    · exact ⟨by decide, ⟨'f', ['a', 'l', 's', 'e'], rfl, by decide⟩,
        fun rem hrem => splitModelUnquoted_noSpace (by decide) hrem⟩
    · exact ⟨by decide, ⟨'t', ['r', 'u', 'e'], rfl, by decide⟩,
        fun rem hrem => splitModelUnquoted_noSpace (by decide) hrem⟩
  | localDate =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, hdd⟩, hnd, hnocr⟩ := renderDate_info hr
    simp only [List.all_cons, Bool.and_eq_true] at hdd
    have hc := isAsciiDigitModel_clean hdd.1; simp only [Bool.and_eq_true, bne_iff_ne] at hc
    exact ⟨hnocr, ⟨y1, _, hds, Bool.eq_false_iff.mpr (by simpa using hc.1.1.1.1.1),
      hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩, fun rem hrem => splitModelUnquoted_noSpace hnd hrem⟩
  | localTime fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    obtain ⟨⟨h1, h2, m1, m2, s1, s2, fcs, hts, htd, _⟩, hnd, hnocr⟩ := renderTime_info hr
    simp only [List.all_cons, Bool.and_eq_true] at htd
    have hc := isAsciiDigitModel_clean htd.1; simp only [Bool.and_eq_true, bne_iff_ne] at hc
    exact ⟨hnocr, ⟨h1, _, hts, Bool.eq_false_iff.mpr (by simpa using hc.1.1.1.1.1),
      hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩, fun rem hrem => splitModelUnquoted_noSpace hnd hrem⟩
  | localDateTime sep fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    rcases hr with ⟨ds, hds_r, ts, hts_r, rfl⟩
    obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, hdd⟩, hd_nd, hd_cr⟩ := renderDate_info hds_r
    obtain ⟨_, ht_nd, ht_cr⟩ := renderTime_info hts_r
    obtain ⟨sch, _, _, hs_cr⟩ := dateTimeSep_info sep
    simp only [List.all_cons, Bool.and_eq_true] at hdd
    have hc := isAsciiDigitModel_clean hdd.1; simp only [Bool.and_eq_true, bne_iff_ne] at hc
    refine ⟨noCrStr_append (noCrStr_append hd_cr hs_cr) ht_cr,
      ⟨y1, _, by simp only [String.toList_append, hds, List.cons_append, List.nil_append]; rfl,
        Bool.eq_false_iff.mpr (by simpa using hc.1.1.1.1.1),
        hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩, fun rem hrem => ?_⟩
    cases sep with
    | space =>
      simpa [renderDateTimeSep, String.append_empty] using
        splitModelUnquoted_spaceDateTime (suf := "") hds_r hts_r rfl hrem
    | upperT =>
      refine splitModelUnquoted_noSpace ?_ hrem
      simp [renderDateTimeSep, String.toList_append, List.all_append, hd_nd, ht_nd, show (!isModelDelim 'T') = true by decide]
    | lowerT =>
      refine splitModelUnquoted_noSpace ?_ hrem
      simp [renderDateTimeSep, String.toList_append, List.all_append, hd_nd, ht_nd, show (!isModelDelim 't') = true by decide]
  | offsetDateTime sep oStyle fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    rcases hr with ⟨ds, hds_r, ts, hts_r, os, hos_r, rfl⟩
    obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, hdd⟩, hd_nd, hd_cr⟩ := renderDate_info hds_r
    obtain ⟨_, ht_nd, ht_cr⟩ := renderTime_info hts_r
    obtain ⟨_, ho_nd, ho_cr⟩ := renderOffset_info hos_r
    obtain ⟨_, _, _, hs_cr⟩ := dateTimeSep_info sep
    simp only [List.all_cons, Bool.and_eq_true] at hdd
    have hc := isAsciiDigitModel_clean hdd.1; simp only [Bool.and_eq_true, bne_iff_ne] at hc
    refine ⟨noCrStr_append (noCrStr_append (noCrStr_append hd_cr hs_cr) ht_cr) ho_cr,
      ⟨y1, _, by simp only [String.toList_append, hds, List.cons_append, List.nil_append, List.append_assoc]; rfl,
        Bool.eq_false_iff.mpr (by simpa using hc.1.1.1.1.1),
        hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩, fun rem hrem => ?_⟩
    cases sep with
    | space =>
      simpa [renderDateTimeSep] using splitModelUnquoted_spaceDateTime hds_r hts_r ho_nd hrem
    | upperT =>
      refine splitModelUnquoted_noSpace ?_ hrem
      simp [renderDateTimeSep, String.toList_append, List.all_append, hd_nd, ht_nd, ho_nd, show (!isModelDelim 'T') = true by decide]
    | lowerT =>
      refine splitModelUnquoted_noSpace ?_ hrem
      simp [renderDateTimeSep, String.toList_append, List.all_append, hd_nd, ht_nd, ho_nd, show (!isModelDelim 't') = true by decide]
  | int lex? =>
    cases v <;> try (cases lex? <;> simp [renderValueInline] at hr <;> done)
    rename_i n
    have hv := int_isValid_of_render hr
    simp only [isValidIntLex, Bool.and_eq_true] at hv
    rcases hv with ⟨⟨⟨_, hnoTerm⟩, _⟩, hpm⟩
    cases hp : parseInt64Model rs with
    | error => rw [hp] at hpm; cases hpm
    | ok m =>
      have hm_int : ∃ mi, parseIntModelChars rs.toList = .ok mi := by
        unfold parseInt64Model parseIntModel at hp
        cases hc : parseIntModelChars rs.toList with
        | error => rw [hc] at hp; cases hp
        | ok mi => exact ⟨mi, rfl⟩
      rcases hm_int with ⟨mi, hmi⟩
      obtain ⟨⟨c0, r0, hlist, hc0, _⟩, _, _⟩ := parseIntModelChars_propsM rs.toList mi hmi
      have hnd : (rs.toList.all fun c => !isModelDelim c) = true := List.all_eq_true.mpr fun c hc => by
        have ht := List.all_eq_true.mp hnoTerm c hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at ht
        have hnw (w : Char) (hw : w.isWhitespace = true) : c ≠ w := fun e => by subst e; simp [hw] at ht
        simp [isModelDelim, isModelHorizWs, hnw ' ' (by decide), hnw '\t' (by decide), hnw '\n' (by decide),
          ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2]
      have hnocr : NoCrStr rs := fun hm => by
        have ht := List.all_eq_true.mp hnoTerm '\r' hm
        simp [show ('\r' : Char).isWhitespace = true by decide] at ht
      have hc0_nd : isModelDelim c0 = false := by
        simpa using List.all_eq_true.mp hnd c0 (by rw [hlist]; simp)
      have hc0_safe : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
        rcases hc0 with rfl | rfl | hdig
        · decide
        · decide
        · have hcl := isAsciiDigitModel_clean hdig; simp only [Bool.and_eq_true, bne_iff_ne] at hcl
          exact ⟨hcl.1.1.1.2, hcl.1.1.2, hcl.1.2, hcl.2⟩
      exact ⟨hnocr, ⟨c0, r0, hlist, hc0_nd, hc0_safe⟩, fun rem hrem => splitModelUnquoted_noSpace hnd hrem⟩
  | float lex? =>
    cases v <;> try (cases lex? <;> simp [renderValueInline] at hr <;> done)
    rename_i f
    have hv := float_isValid_of_render hr
    simp only [isValidFloatLex, Bool.and_eq_true] at hv
    rcases hv with ⟨_, hpm⟩
    cases hp : parseFloatModel rs with
    | error => rw [hp] at hpm; cases hpm
    | ok g =>
      obtain ⟨⟨c0, r0, hlist, hc0⟩, hfmc⟩ := parseFloatModelChars_propsM rs.toList g (by simpa [parseFloatModel] using hp)
      have hnd : (rs.toList.all fun c => !isModelDelim c) = true := List.all_eq_true.mpr fun c hc =>
        ((Bool.and_eq_true _ _).mp (isFloatModelCharM_props c (hfmc c hc)).2.2.2.2).1
      have hnocr : NoCrStr rs := fun hm =>
        bne_iff_ne.mp ((Bool.and_eq_true _ _).mp (isFloatModelCharM_props '\r' (hfmc '\r' hm)).2.2.2.2).2 rfl
      have hc0_nd : isModelDelim c0 = false := by
        simpa using List.all_eq_true.mp hnd c0 (by rw [hlist]; simp)
      have hc0_safe : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
        rcases hc0 with rfl | rfl | rfl | rfl | hdig <;>
          first | decide | (have hcl := isAsciiDigitModel_clean hdig; simp only [Bool.and_eq_true, bne_iff_ne] at hcl
                            exact ⟨hcl.1.1.1.2, hcl.1.1.2, hcl.1.2, hcl.2⟩)
      exact ⟨hnocr, ⟨c0, r0, hlist, hc0_nd, hc0_safe⟩, fun rem hrem => splitModelUnquoted_noSpace hnd hrem⟩

private def expectedScalarKind : ValueTape → Nat
  | .bool => 0
  | .localDate => 1
  | .offsetDateTime _ _ _ => 2
  | .localDateTime _ _ => 3
  | .localTime _ => 4
  | .float _ => 5
  | .int _ => 6
  | _ => 99

private theorem scalarKind_of_render {v : TomlValue} {vt : ValueTape} {tok : String}
    (hunq : isUnquotedTape vt = true) (hr : renderValueInline v vt = some tok) :
    scalarKindOf tok.toList = expectedScalarKind vt := by
  cases vt with
  | string _ | array _ _ | inlineTable _ _ => simp [isUnquotedTape] at hunq
  | bool =>
    cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
    rename_i b; obtain rfl := (Option.some.inj hr).symm; cases b <;> decide
  | localDate =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, _⟩, _, _⟩ := renderDate_info hr
    rw [hds]; unfold scalarKindOf; dsimp only [expectedScalarKind]
    have hnb : ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] == ['t', 'r', 'u', 'e'] ||
        [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] == ['f', 'a', 'l', 's', 'e']) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; constructor <;> intro h <;> have := congrArg List.length h <;> simp at this
    rw [hnb]; simp
  | offsetDateTime sep oStyle fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    rcases hr with ⟨ds, hds_r, ts, hts_r, os, hos_r, rfl⟩
    obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, _⟩, _, _⟩ := renderDate_info hds_r
    obtain ⟨⟨h1, h2, min1, min2, s1, s2, fcs, hts, _, _⟩, _, _⟩ := renderTime_info hts_r
    obtain ⟨⟨o0, orest, hos, ho0⟩, _, _⟩ := renderOffset_info hos_r
    obtain ⟨sch, hsep, _, _⟩ := dateTimeSep_info sep
    have hfull : (ds ++ renderDateTimeSep sep ++ ts ++ os).toList =
        [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ (ts.toList ++ o0 :: orest) := by
      simp [String.toList_append, hds, hsep, hos]
    rw [hfull]; unfold scalarKindOf; dsimp only [expectedScalarKind]
    have hlen : ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ (ts.toList ++ o0 :: orest)).length ≥ 12 := by
      simp [List.length_append]; omega
    have hnb : (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ (ts.toList ++ o0 :: orest)) == ['t', 'r', 'u', 'e'] ||
        ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ (ts.toList ++ o0 :: orest)) == ['f', 'a', 'l', 's', 'e']) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; constructor <;> intro h <;> have := congrArg List.length h <;> simp at this <;> omega
    have hany : ((ts.toList ++ o0 :: orest).any fun c => c == 'Z' || c == 'z' || c == '+' || c == '-') = true := by
      refine List.any_eq_true.mpr ⟨o0, by simp, ?_⟩
      rcases ho0 with rfl | rfl | rfl | rfl <;> decide
    have hge10 : decide (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ (ts.toList ++ o0 :: orest)).length ≥ 10) = true :=
      decide_eq_true (by omega)
    have hne10 : (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ (ts.toList ++ o0 :: orest)).length == 10) = false :=
      beq_false_of_ne (by omega)
    rw [hnb, hge10, hne10]; simp [hany]
  | localDateTime sep fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    rcases hr with ⟨ds, hds_r, ts, hts_r, rfl⟩
    obtain ⟨⟨y1, y2, y3, y4, m1, m2, d1, d2, hds, _⟩, _, _⟩ := renderDate_info hds_r
    obtain ⟨⟨h1, h2, min1, min2, s1, s2, fcs, hts, htd, htf⟩, _, _⟩ := renderTime_info hts_r
    obtain ⟨sch, hsep, _, _⟩ := dateTimeSep_info sep
    have hfull : (ds ++ renderDateTimeSep sep ++ ts).toList =
        [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ ts.toList := by
      simp [String.toList_append, hds, hsep]
    rw [hfull]; unfold scalarKindOf; dsimp only [expectedScalarKind]
    have hlen : ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ ts.toList).length ≥ 19 := by
      rw [hts]; simp
    have hnb : (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ ts.toList) == ['t', 'r', 'u', 'e'] ||
        ([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ ts.toList) == ['f', 'a', 'l', 's', 'e']) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; constructor <;> intro h <;> have := congrArg List.length h <;> simp at this <;> omega
    have hno_off : (ts.toList.any fun c => c == 'Z' || c == 'z' || c == '+' || c == '-') = false := by
      rw [List.any_eq_false]; intro c hc
      rw [hts, List.mem_append] at hc
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htd
      have not_off_d (x) (hx : isAsciiDigitModel x = true) : ¬((x == 'Z' || x == 'z' || x == '+' || x == '-') = true) := by
        rw [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff]
        simp only [beq_eq_false_iff_ne]; refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> rintro rfl <;> revert hx <;> decide
      rcases hc with hb | hf
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact not_off_d _ htd.1
        · exact not_off_d _ htd.2.1
        · decide
        · exact not_off_d _ htd.2.2.1
        · exact not_off_d _ htd.2.2.2.1
        · decide
        · exact not_off_d _ htd.2.2.2.2.1
        · exact not_off_d _ htd.2.2.2.2.2
      · rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp htf c hf) with hd | hp
        · exact not_off_d _ hd
        · rw [eq_of_beq hp]; decide
    have hge10 : decide (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ ts.toList).length ≥ 10) = true :=
      decide_eq_true (by omega)
    have hne10 : (([y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, sch] ++ ts.toList).length == 10) = false :=
      beq_false_of_ne (by omega)
    rw [hnb, hge10, hne10]; simp [hno_off]
  | localTime fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try cases hr
    obtain ⟨⟨h1, h2, m1, m2, s1, s2, fcs, hts, htd, _⟩, _, _⟩ := renderTime_info hr
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htd
    have hm2_d := htd.2.2.2.1
    have hm2_ne : m2 ≠ '-' := by intro heq; subst heq; revert hm2_d; decide
    have hnb : (tok.toList == ['t', 'r', 'u', 'e'] || tok.toList == ['f', 'a', 'l', 's', 'e']) = false := by
      rw [hts]; simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; constructor <;> intro h <;> have := congrArg List.length h <;> simp at this
    unfold scalarKindOf; dsimp only [expectedScalarKind]; rw [hnb]
    have h4 : tok.toList[4]? = some m2 := by rw [hts]; rfl
    have hcol : ':' ∈ tok.toList := by rw [hts]; simp
    simp [h4, beq_false_of_ne hm2_ne, hcol]
  | float lex? =>
    cases v <;> try (cases lex? <;> simp [renderValueInline] at hr <;> done)
    rename_i f
    have hv := float_isValid_of_render hr
    simp only [isValidFloatLex, Bool.and_eq_true] at hv
    rcases hv with ⟨⟨hmark, _⟩, hpm⟩
    cases hp : parseFloatModel tok with
    | error => rw [hp] at hpm; cases hpm
    | ok g =>
      have hp_cs : parseFloatModelChars tok.toList = .ok g := by simpa [parseFloatModel] using hp
      obtain ⟨_, hfmc⟩ := parseFloatModelChars_propsM tok.toList g hp_cs
      have hnb : (tok.toList == ['t', 'r', 'u', 'e'] || tok.toList == ['f', 'a', 'l', 's', 'e']) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        refine ⟨fun heq => ?_, fun heq => ?_⟩
        · have hm := hfmc 't' (by rw [heq]; simp); revert hm; decide
        · have hm := hfmc 'l' (by rw [heq]; simp); revert hm; decide
      have hnod : (decide (tok.toList.length ≥ 10) && tok.toList[4]? == some '-' && tok.toList[7]? == some '-') = false := by
        cases hd : (decide (tok.toList.length ≥ 10) && tok.toList[4]? == some '-' && tok.toList[7]? == some '-')
        · rfl
        · simp only [Bool.and_eq_true, beq_iff_eq] at hd
          exact absurd ⟨hd.1.2, hd.2⟩ (float_not_date_dashes tok.toList g hp_cs)
      have hnoc : tok.toList.contains ':' = false :=
        Bool.eq_false_iff.mpr fun hm => (isFloatModelCharM_props ':' (hfmc ':' (List.contains_iff_mem.mp hm))).1 rfl
      have hno0x : (tok.toList.take 2 == ['0', 'x']) = false := by
        rw [beq_eq_false_iff_ne]; intro hx
        have hmem : 'x' ∈ tok.toList := List.mem_of_mem_take (by rw [hx]; simp)
        exact (isFloatModelCharM_props 'x' (hfmc 'x' hmem)).2.1 rfl
      have hmark_cs : (tok.toList.contains '.' || tok.toList.contains 'e' || tok.toList.contains 'E' ||
          (tok.toList == ['i', 'n', 'f'] || tok.toList == ['+', 'i', 'n', 'f'] || tok.toList == ['-', 'i', 'n', 'f'] ||
           tok.toList == ['n', 'a', 'n'] || tok.toList == ['+', 'n', 'a', 'n'] || tok.toList == ['-', 'n', 'a', 'n'])) = true := by
        simp only [String.contains_char_eq, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, String.ext_iff] at hmark
        simp only [List.contains_iff_mem, Bool.or_eq_true, beq_iff_eq]
        rcases hmark with (((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
        · exact Or.inl (Or.inl (Or.inl h1))
        · exact Or.inl (Or.inl (Or.inr h1))
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1)))))
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1)))))
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h1))))
        · exact Or.inr (Or.inl (Or.inl (Or.inr h1)))
        · exact Or.inr (Or.inl (Or.inr h1))
        · exact Or.inr (Or.inr h1)
      unfold scalarKindOf; dsimp only [expectedScalarKind]
      rw [hnb, hnod, hnoc, hno0x, hmark_cs]; rfl
  | int lex? =>
    cases v <;> try (cases lex? <;> simp [renderValueInline] at hr <;> done)
    rename_i n
    have hv := int_isValid_of_render hr
    simp only [isValidIntLex, Bool.and_eq_true] at hv
    rcases hv with ⟨⟨⟨_, _⟩, hnoExp⟩, hpm⟩
    cases hp : parseInt64Model tok with
    | error => rw [hp] at hpm; cases hpm
    | ok m =>
      have hm_int : ∃ mi, parseIntModelChars tok.toList = .ok mi := by
        unfold parseInt64Model parseIntModel at hp
        cases hc : parseIntModelChars tok.toList with
        | error => rw [hc] at hp; cases hp
        | ok mi => exact ⟨mi, rfl⟩
      rcases hm_int with ⟨mi, hmi⟩
      obtain ⟨⟨c0, r0, hlist, hc0, hc1⟩, hno_cd, hno_dash⟩ := parseIntModelChars_propsM tok.toList mi hmi
      have hnb : (tok.toList == ['t', 'r', 'u', 'e'] || tok.toList == ['f', 'a', 'l', 's', 'e']) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        refine ⟨fun heq => ?_, fun heq => ?_⟩ <;> (rw [heq] at hlist; obtain ⟨rfl, _⟩ := List.cons.inj hlist; revert hc0; decide)
      have hnod4 : (tok.toList[4]? == some '-') = false := by
        rw [beq_eq_false_iff_ne]; intro h4
        rw [hlist] at h4
        have hm_r0 : '-' ∈ r0 := List.mem_of_getElem? (i := 3) h4
        exact hno_dash c0 r0 hlist '-' hm_r0 rfl
      have hnod : (decide (tok.toList.length ≥ 10) && tok.toList[4]? == some '-' && tok.toList[7]? == some '-') = false := by
        rw [hnod4]; simp
      have hnoc : tok.toList.contains ':' = false :=
        Bool.eq_false_iff.mpr fun hm => (hno_cd ':' (List.contains_iff_mem.mp hm)).1 rfl
      have hnodot : tok.toList.contains '.' = false :=
        Bool.eq_false_iff.mpr fun hm => (hno_cd '.' (List.contains_iff_mem.mp hm)).2 rfl
      have hnospec : (tok.toList == ['i', 'n', 'f'] || tok.toList == ['+', 'i', 'n', 'f'] || tok.toList == ['-', 'i', 'n', 'f'] ||
          tok.toList == ['n', 'a', 'n'] || tok.toList == ['+', 'n', 'a', 'n'] || tok.toList == ['-', 'n', 'a', 'n']) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
        · intro heq; rw [heq] at hlist; obtain ⟨rfl, _⟩ := List.cons.inj hlist; revert hc0; decide
        · intro heq; rw [heq] at hlist; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist
          have hd := hc1 'i' ['n', 'f'] (Or.inl rfl) rfl; revert hd; decide
        · intro heq; rw [heq] at hlist; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist
          have hd := hc1 'i' ['n', 'f'] (Or.inr rfl) rfl; revert hd; decide
        · intro heq; rw [heq] at hlist; obtain ⟨rfl, _⟩ := List.cons.inj hlist; revert hc0; decide
        · intro heq; rw [heq] at hlist; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist
          have hd := hc1 'n' ['a', 'n'] (Or.inl rfl) rfl; revert hd; decide
        · intro heq; rw [heq] at hlist; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist
          have hd := hc1 'n' ['a', 'n'] (Or.inr rfl) rfl; revert hd; decide
      have hflt_branch : (!(tok.toList.take 2 == ['0', 'x']) &&
          (tok.toList.contains '.' || tok.toList.contains 'e' || tok.toList.contains 'E' ||
           (tok.toList == ['i', 'n', 'f'] || tok.toList == ['+', 'i', 'n', 'f'] || tok.toList == ['-', 'i', 'n', 'f'] ||
            tok.toList == ['n', 'a', 'n'] || tok.toList == ['+', 'n', 'a', 'n'] || tok.toList == ['-', 'n', 'a', 'n']))) = false := by
        cases h0x : tok.toList.take 2 == ['0', 'x']
        · have hnsw : tok.startsWith "0x" = false := by
            rw [Bool.eq_false_iff]; intro hsw
            rcases String.startsWith_string_iff.mp hsw with ⟨t, ht⟩
            have htk : (tok.toList.take 2 == ['0', 'x']) = true := by rw [beq_iff_eq, ← ht]; rfl
            rw [h0x] at htk; cases htk
          rw [hnsw] at hnoExp; simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
            Bool.or_eq_false_iff, String.contains_char_eq, decide_eq_false_iff_not] at hnoExp
          have hne_e : tok.toList.contains 'e' = false := Bool.eq_false_iff.mpr (hnoExp.1 ∘ List.contains_iff_mem.mp)
          have hne_E : tok.toList.contains 'E' = false := Bool.eq_false_iff.mpr (hnoExp.2 ∘ List.contains_iff_mem.mp)
          rw [hnodot, hne_e, hne_E, hnospec]; rfl
        · rfl
      unfold scalarKindOf; dsimp only [expectedScalarKind]
      rw [hnb, hnod, hnoc, hflt_branch]; rfl

/-- Full prefix-injectivity and `TomlEquiv` for all unquoted scalar `ValueTape` forms. -/
theorem unquotedScalar_injective {v1 v2 : TomlValue} {vt1 vt2 : ValueTape}
    {rs1 rs2 : String} {rem1 rem2 : List Char}
    (hu1 : isUnquotedTape vt1 = true) (hu2 : isUnquotedTape vt2 = true)
    (hr1 : renderValueInline v1 vt1 = some rs1) (hr2 : renderValueInline v2 vt2 = some rs2)
    (hd1 : ModelDelimTail rem1) (hd2 : ModelDelimTail rem2)
    (heq : rs1.toList ++ rem1 = rs2.toList ++ rem2) :
    TomlEquiv v1 v2 ∧ rem1 = rem2 := by
  obtain ⟨_, _, hsp1⟩ := unquotedScalar_info hu1 hr1
  obtain ⟨_, _, hsp2⟩ := unquotedScalar_info hu2 hr2
  have hsp_eq := (hsp1 rem1 hd1).symm.trans ((congrArg splitModelUnquoted heq).trans (hsp2 rem2 hd2))
  injection hsp_eq with hrs_l hrem_eq
  have hrs : rs1 = rs2 := String.ext_iff.mpr hrs_l
  subst hrs hrem_eq
  refine ⟨?_, rfl⟩
  have hkind : expectedScalarKind vt1 = expectedScalarKind vt2 :=
    (scalarKind_of_render hu1 hr1).symm.trans (scalarKind_of_render hu2 hr2)
  cases vt1 with
  | string _ | array _ _ | inlineTable _ _ => simp [isUnquotedTape] at hu1
  | int l1 =>
    cases vt2 with
    | int l2 =>
      cases v1 <;> try (cases l1 <;> simp [renderValueInline] at hr1 <;> done)
      cases v2 <;> try (cases l2 <;> simp [renderValueInline] at hr2 <;> done)
      have hv1 := int_isValid_of_render hr1
      have hv2 := int_isValid_of_render hr2
      simp only [isValidIntLex, Bool.and_eq_true] at hv1 hv2
      cases hp : parseInt64Model rs1 with
      | error => rw [hp] at hv1; cases hv1.2
      | ok m =>
        rw [hp] at hv1 hv2; simp only [beq_iff_eq] at hv1 hv2
        simp [TomlEquiv, hv1.2.symm.trans hv2.2]
    | _ => first | (simp [isUnquotedTape] at hu2; done) | (simp [expectedScalarKind] at hkind; done)
  | float l1 =>
    cases vt2 with
    | float l2 =>
      cases v1 <;> try (cases l1 <;> simp [renderValueInline] at hr1 <;> done)
      cases v2 <;> try (cases l2 <;> simp [renderValueInline] at hr2 <;> done)
      rename_i f1 f2
      have hv1 := float_isValid_of_render hr1
      have hv2 := float_isValid_of_render hr2
      simp only [isValidFloatLex, Bool.and_eq_true] at hv1 hv2
      cases hp : parseFloatModel rs1 with
      | error => rw [hp] at hv1; cases hv1.2
      | ok g =>
        rw [hp] at hv1 hv2
        have toEqv (f : Float) (hm : ((g.isNaN && f.isNaN) || g == f) = true) : FloatEquiv g f := by
          rcases Bool.or_eq_true_iff.mp hm with hnan | hbeq
          · exact Or.inl (Bool.and_eq_true_iff.mp hnan)
          · exact Or.inr hbeq
        simp only [TomlEquiv]
        exact floatEquiv_trans (floatEquiv_symm (toEqv f1 hv1.2)) (toEqv f2 hv2.2)
    | _ => first | (simp [isUnquotedTape] at hu2; done) | (simp [expectedScalarKind] at hkind; done)
  | bool =>
    cases vt2 with
    | bool =>
      cases v1 <;> simp only [renderValueInline] at hr1 <;> try (simp at hr1; done)
      cases v2 <;> simp only [renderValueInline] at hr2 <;> try (simp at hr2; done)
      rename_i b1 b2
      obtain rfl := Option.some.inj hr1
      have h12 := Option.some.inj hr2
      cases b1 <;> cases b2 <;> simp [TomlEquiv] at h12 ⊢
    | _ => first | (simp [isUnquotedTape] at hu2; done) | (simp [expectedScalarKind] at hkind; done)
  | offsetDateTime sep1 _ _ =>
    cases vt2 with
    | offsetDateTime sep2 _ _ =>
      cases v1 <;> simp only [renderValueInline] at hr1 <;> try cases hr1
      cases v2 <;> simp only [renderValueInline] at hr2 <;> try cases hr2
      rename_i dt1 dt2
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr1 hr2
      rcases hr1 with ⟨ds1, hd1_r, ts1, ht1_r, os1, ho1_r, htok1⟩
      rcases hr2 with ⟨ds2, hd2_r, ts2, ht2_r, os2, ho2_r, htok2⟩
      obtain ⟨⟨_, _, _, _, _, _, _, _, hds1_l, _⟩, _, _⟩ := renderDate_info hd1_r
      obtain ⟨⟨_, _, _, _, _, _, _, _, hds2_l, _⟩, _, _⟩ := renderDate_info hd2_r
      obtain ⟨sch1, hs1_l, _, _⟩ := dateTimeSep_info sep1
      obtain ⟨sch2, hs2_l, _, _⟩ := dateTimeSep_info sep2
      have heq_l := congrArg String.toList (htok1.trans htok2.symm)
      simp only [String.toList_append, hs1_l, hs2_l, List.append_assoc, List.singleton_append] at heq_l
      have hlen_d : ds1.toList.length = ds2.toList.length := by simp [hds1_l, hds2_l]
      obtain ⟨eds_l, erest⟩ := List.append_inj heq_l hlen_d
      have etsos := (List.cons.inj erest).2
      simp only [List.append_eq] at etsos
      have eos_l : os1.toList = os2.toList := by
        have h := congrArg dropTimeBodyChars etsos
        rwa [dropTimeBodyChars_append ht1_r ho1_r, dropTimeBodyChars_append ht2_r ho2_r] at h
      have ets_l : ts1.toList = ts2.toList := List.append_cancel_right (etsos.trans (by rw [eos_l]))
      have ed := renderDate_inj hd1_r (String.ext_iff.mpr eds_l ▸ hd2_r)
      have et := renderTime_inj ht1_r (String.ext_iff.mpr ets_l ▸ ht2_r)
      have eo := renderOffset_inj ho1_r (String.ext_iff.mpr eos_l ▸ ho2_r)
      rcases dt1 with ⟨⟨_, _⟩, _⟩; rcases dt2 with ⟨⟨_, _⟩, _⟩
      dsimp only at ed et eo; subst ed et eo; simp [TomlEquiv]
    | _ => first | (simp [isUnquotedTape] at hu2; done) | (simp [expectedScalarKind] at hkind; done)
  | localDateTime sep1 _ =>
    cases vt2 with
    | localDateTime sep2 _ =>
      cases v1 <;> simp only [renderValueInline] at hr1 <;> try cases hr1
      cases v2 <;> simp only [renderValueInline] at hr2 <;> try cases hr2
      rename_i dt1 dt2
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr1 hr2
      rcases hr1 with ⟨ds1, hd1_r, ts1, ht1_r, htok1⟩
      rcases hr2 with ⟨ds2, hd2_r, ts2, ht2_r, htok2⟩
      obtain ⟨⟨_, _, _, _, _, _, _, _, hds1_l, _⟩, _, _⟩ := renderDate_info hd1_r
      obtain ⟨⟨_, _, _, _, _, _, _, _, hds2_l, _⟩, _, _⟩ := renderDate_info hd2_r
      obtain ⟨sch1, hs1_l, _, _⟩ := dateTimeSep_info sep1
      obtain ⟨sch2, hs2_l, _, _⟩ := dateTimeSep_info sep2
      have heq_l := congrArg String.toList (htok1.trans htok2.symm)
      simp only [String.toList_append, hs1_l, hs2_l, List.append_assoc, List.singleton_append] at heq_l
      obtain ⟨eds_l, erest⟩ := List.append_inj heq_l (by simp [hds1_l, hds2_l])
      have ets_l := (List.cons.inj erest).2
      have ed := renderDate_inj hd1_r (String.ext_iff.mpr eds_l ▸ hd2_r)
      have et := renderTime_inj ht1_r (String.ext_iff.mpr ets_l ▸ ht2_r)
      cases dt1; cases dt2
      dsimp only at ed et; subst ed et; simp [TomlEquiv]
    | _ => first | (simp [isUnquotedTape] at hu2; done) | (simp [expectedScalarKind] at hkind; done)
  | localDate =>
    cases vt2 with
    | localDate =>
      cases v1 <;> simp only [renderValueInline] at hr1 <;> try cases hr1
      cases v2 <;> simp only [renderValueInline] at hr2 <;> try cases hr2
      obtain rfl := renderDate_inj hr1 hr2; simp [TomlEquiv]
    | _ => first | (simp [isUnquotedTape] at hu2; done) | (simp [expectedScalarKind] at hkind; done)
  | localTime _ =>
    cases vt2 with
    | localTime _ =>
      cases v1 <;> simp only [renderValueInline] at hr1 <;> try cases hr1
      cases v2 <;> simp only [renderValueInline] at hr2 <;> try cases hr2
      obtain rfl := renderTime_inj hr1 hr2; simp [TomlEquiv]
    | _ => first | (simp [isUnquotedTape] at hu2; done) | (simp [expectedScalarKind] at hkind; done)

end LeanSwe.Toml.Proofs
