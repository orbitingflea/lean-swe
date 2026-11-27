import LeanSweProofs.Toml.Proofs.RoundTripKeyDt

/-!
# Unquoted Scalar Render-to-Parse Soundness (`RoundTripScalar`)

Proves `unquotedScalar_parseValueFuel`, showing that every unquoted TOML 1.0 scalar (`bool`,
`int`, `float`, `localDate`, `localTime`, `localDateTime`, `offsetDateTime`) emitted by
`Model.renderValueInline` parses cleanly under `Impl.parseValueFuel`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

/-- Every unquoted scalar rendered by `Model.renderValueInline` parses cleanly via `Impl.parseValueFuel`. -/
theorem unquotedScalar_parseValueFuel {numApi : NumParseApi} (hnum : ValidNumApi numApi)
    {v : TomlValue} {vt : ValueTape} {rs : String}
    (hunq : isUnquotedTape vt = true) (hr : renderValueInline v vt = some rs) :
    CleanNorm rs.toList ∧ rs.toList ≠ [] ∧
    ∀ rem, ModelDelimTail rem → ∀ fuel, 1 ≤ fuel →
      ∃ v', parseValueFuel (toCharNumApi numApi) fuel (rs.toList ++ rem) = .ok (v', rem) ∧
        isTableVal v' = false := by
  obtain ⟨_, ⟨c0, r0, hrs_l, _, hc0_safe⟩, hsplit_m⟩ := unquotedScalar_info hunq hr
  have step_unq (rem : List Char) (hrem : ModelDelimTail rem) (f : Nat) :
      parseValueFuel (toCharNumApi numApi) (f + 1) (rs.toList ++ rem) =
        (classifyScalarChars (toCharNumApi numApi) rs.toList >>= fun v' => .ok (v', rem)) := by
    have hsp : takeUnquotedTokenChars (rs.toList ++ rem) = (rs.toList, rem) := by
      rw [takeUnquotedTokenChars_eq_splitModelUnquoted]; exact hsplit_m rem hrem
    have hst : parseValueFuel (toCharNumApi numApi) (f + 1) (c0 :: (r0 ++ rem)) =
        (let (tok, af) := takeUnquotedTokenChars (c0 :: (r0 ++ rem))
         classifyScalarChars (toCharNumApi numApi) tok >>= fun v' => .ok (v', af)) := by
      rcases hc0_safe with ⟨hq1, hq2, hb1, hb2⟩
      conv => lhs; unfold parseValueFuel
      split <;> simp_all
    rw [hrs_l, List.cons_append, hst, ← List.cons_append, ← hrs_l, hsp]
  have cls_dt (w : TomlValue) (hdt : parseDateTimeChars rs.toList = some (.ok w)) (hw_nt : isTableVal w = false)
      (hdig0 : isAsciiDigit c0 = true) :
      ∀ rem, ModelDelimTail rem → ∀ fuel, 1 ≤ fuel →
        ∃ v', parseValueFuel (toCharNumApi numApi) fuel (rs.toList ++ rem) = .ok (v', rem) ∧ isTableVal v' = false := by
    intro rem hrem fuel hf
    cases fuel with | zero => omega | succ f =>
    have hne_nil : rs.toList ≠ [] := by simp [hrs_l]
    have hne_t : rs.toList ≠ ['t', 'r', 'u', 'e'] := fun e => by rw [hrs_l] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; revert hdig0; decide
    have hne_f : rs.toList ≠ ['f', 'a', 'l', 's', 'e'] := fun e => by rw [hrs_l] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; revert hdig0; decide
    have hcls : classifyScalarChars (toCharNumApi numApi) rs.toList = .ok w := by
      unfold classifyScalarChars; split
      · rename_i heq; exact absurd heq hne_nil
      · rename_i heq; exact absurd heq hne_t
      · rename_i heq; exact absurd heq hne_f
      · simp [hdt]
    exact ⟨w, by rw [step_unq rem hrem f, hcls]; rfl, hw_nt⟩
  cases vt with
  | string _ | array _ _ | inlineTable _ _ => simp [isUnquotedTape] at hunq
  | bool =>
    cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
    rename_i b; injection hr with hrs; subst hrs
    refine ⟨by cases b <;> decide, by cases b <;> decide, fun rem hrem fuel hf => ?_⟩
    cases fuel with | zero => omega | succ f =>
    exact ⟨.bool b, by rw [step_unq rem hrem f]; cases b <;> rfl, rfl⟩
  | localDate =>
    cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
    rename_i d
    obtain ⟨hcl, hdp⟩ := renderDate_parseDatePart hr
    obtain ⟨hp0, hpref0⟩ := hdp []; simp only [List.append_nil] at hp0 hpref0
    have hc0_d : isAsciiDigit c0 = true := by
      rw [hrs_l] at hpref0; unfold hasDatePrefix at hpref0
      split at hpref0 <;> try (simp at hpref0; done)
      rename_i heq; obtain ⟨rfl, _⟩ := List.cons.inj heq
      simp only [Bool.and_eq_true] at hpref0; exact hpref0.1.1.1.1.1.1.1
    exact ⟨hcl, by simp [hrs_l], cls_dt (.localDate d) (by simp [parseDateTimeChars, hpref0, hp0]) rfl hc0_d⟩
  | localTime fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
    rename_i t
    obtain ⟨hcl, htp⟩ := renderTime_parseTimePart hr
    obtain ⟨hp0, hpref0⟩ := htp [] (fun _ _ e => nomatch e); simp only [List.append_nil] at hp0 hpref0
    obtain ⟨⟨h1, h2, m1, m2, s1, s2, fcs, hts, htd, _⟩, _, _⟩ := renderTime_info hr
    have hno_dp : hasDatePrefix rs.toList = false := by
      rw [hts]; unfold hasDatePrefix
      split
      · rename_i y1 y2 y3 _ _ _ _ _ _ heq
        have hcol : ':' = y3 := (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).1
        subst hcol; simp [show isAsciiDigit ':' = false from rfl]
      · rfl
    have hc0_d : isAsciiDigit c0 = true := by
      rw [hrs_l] at hpref0; unfold hasTimePrefix at hpref0
      split at hpref0 <;> try (simp at hpref0; done)
      rename_i heq; obtain ⟨rfl, _⟩ := List.cons.inj heq
      simp only [Bool.and_eq_true] at hpref0; exact hpref0.1.1.1.1.1
    exact ⟨hcl, by simp [hrs_l], cls_dt (.localTime t) (by simp [parseDateTimeChars, hno_dp, hpref0, hp0]) rfl hc0_d⟩
  | localDateTime sep fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
    rename_i dt
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    rcases hr with ⟨ds, hds_r, ts, hts_r, rfl⟩
    obtain ⟨hcl_d, hdp⟩ := renderDate_parseDatePart hds_r
    obtain ⟨hcl_t, htp⟩ := renderTime_parseTimePart hts_r
    obtain ⟨htp0, _⟩ := htp [] (fun _ _ e => nomatch e); simp only [List.append_nil] at htp0
    have hsep_p : ∃ ch, (renderDateTimeSep sep).toList = [ch] ∧ (ch == 'T' || ch == 't' || ch == ' ') = true ∧ CleanNorm [ch] := by
      cases sep <;> exact ⟨_, rfl, rfl, by decide⟩
    obtain ⟨sch, hsep_l, hsep_ok, hcl_s⟩ := hsep_p
    obtain ⟨hdp_s, hpref_s⟩ := hdp (sch :: ts.toList)
    have hfull : (ds ++ renderDateTimeSep sep ++ ts).toList = ds.toList ++ sch :: ts.toList := by
      simp [String.toList_append, hsep_l]
    have hc0_d : isAsciiDigit c0 = true := by
      rw [← hfull, hrs_l] at hpref_s; unfold hasDatePrefix at hpref_s
      split at hpref_s <;> try (simp at hpref_s; done)
      rename_i heq; obtain ⟨rfl, _⟩ := List.cons.inj heq
      simp only [Bool.and_eq_true] at hpref_s; exact hpref_s.1.1.1.1.1.1.1
    have hdt_ok : parseDateTimeChars (ds ++ renderDateTimeSep sep ++ ts).toList = some (.ok (.localDateTime dt)) := by
      rw [hfull]; simp [parseDateTimeChars, hpref_s, hdp_s, hsep_ok, htp0,
        show Std.Time.PlainDateTime.mk dt.date dt.time = dt by cases dt; rfl]
    refine ⟨by simp only [String.toList_append, hsep_l]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨hcl_d, hcl_s⟩, hcl_t⟩,
      by simp [hrs_l], cls_dt (.localDateTime dt) hdt_ok rfl hc0_d⟩
  | offsetDateTime sep oStyle fl =>
    cases v <;> simp only [renderValueInline] at hr <;> try (simp at hr; done)
    rename_i odt
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
    rcases hr with ⟨ds, hds_r, ts, hts_r, os, hos_r, rfl⟩
    obtain ⟨hcl_d, hdp⟩ := renderDate_parseDatePart hds_r
    obtain ⟨hcl_t, htp⟩ := renderTime_parseTimePart hts_r
    obtain ⟨hcl_o, hos_ne, hop, ho_hd⟩ := renderOffset_parseOffsetPartR hos_r
    obtain ⟨htp_o, _⟩ := htp os.toList ho_hd
    have hsep_p : ∃ ch, (renderDateTimeSep sep).toList = [ch] ∧ (ch == 'T' || ch == 't' || ch == ' ') = true ∧ CleanNorm [ch] := by
      cases sep <;> exact ⟨_, rfl, rfl, by decide⟩
    obtain ⟨sch, hsep_l, hsep_ok, hcl_s⟩ := hsep_p
    obtain ⟨hdp_s, hpref_s⟩ := hdp (sch :: (ts.toList ++ os.toList))
    cases hos_l : os.toList with
    | nil => exact absurd hos_l hos_ne
    | cons o0 os' =>
      have hfull : (ds ++ renderDateTimeSep sep ++ ts ++ os).toList = ds.toList ++ sch :: (ts.toList ++ o0 :: os') := by
        simp [String.toList_append, hsep_l, hos_l, List.append_assoc]
      have hc0_d : isAsciiDigit c0 = true := by
        rw [hos_l, ← hfull, hrs_l] at hpref_s; unfold hasDatePrefix at hpref_s
        split at hpref_s <;> try (simp at hpref_s; done)
        rename_i heq; obtain ⟨rfl, _⟩ := List.cons.inj heq
        simp only [Bool.and_eq_true] at hpref_s; exact hpref_s.1.1.1.1.1.1.1
      have hdt_ok : parseDateTimeChars (ds ++ renderDateTimeSep sep ++ ts ++ os).toList = some (.ok (.offsetDateTime odt)) := by
        rw [hfull]; rw [hos_l] at htp_o hop hdp_s hpref_s
        simp [parseDateTimeChars, hpref_s, hdp_s, hsep_ok, htp_o, hop,
          show TomlOffsetDateTime.mk (Std.Time.PlainDateTime.mk odt.dateTime.date odt.dateTime.time) odt.offset = odt by
            rcases odt with ⟨⟨_, _⟩, _⟩; rfl]
      refine ⟨by simp only [String.toList_append, hsep_l]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨hcl_d, hcl_s⟩, hcl_t⟩, hcl_o⟩,
        by simp [hrs_l], cls_dt (.offsetDateTime odt) hdt_ok rfl hc0_d⟩
  | int lex? =>
    cases v <;> try (cases lex? <;> simp [renderValueInline] at hr; done)
    rename_i n
    have hv : isValidIntLex rs n = true := by
      cases lex? with
      | none => simp only [renderValueInline, Option.some.injEq] at hr; subst hr; exact formatInt64Canonical_isValidIntLex n
      | some l =>
        simp only [renderValueInline] at hr
        if hv0 : isValidIntLex l n = true then simp [hv0] at hr; subst hr; exact hv0
        else simp [hv0] at hr
    simp only [isValidIntLex, Bool.and_eq_true] at hv
    rcases hv with ⟨⟨⟨hnoBad, hnoTerm⟩, hnoExp⟩, hpm_b⟩
    have hp64 : parseInt64Model rs = .ok n := by
      cases hp : parseInt64Model rs with
      | error _ => rw [hp] at hpm_b; cases hpm_b
      | ok m => rw [hp] at hpm_b; rw [eq_of_beq hpm_b]
    have hcl_rs : CleanNorm rs.toList := List.all_eq_true.mpr fun c hc => by
      have ht := List.all_eq_true.mp hnoTerm c hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at ht ⊢
      exact ⟨ht.2, fun h0 => by subst h0; simp [show ('\r' : Char).isWhitespace = true by decide] at ht⟩
    have hm_int : ∃ mi, parseIntModelChars rs.toList = .ok mi := by
      unfold parseInt64Model parseIntModel at hp64
      cases hc : parseIntModelChars rs.toList with
      | error _ => rw [hc] at hp64; nomatch hp64
      | ok mi => exact ⟨mi, rfl⟩
    rcases hm_int with ⟨mi, hmi⟩
    obtain ⟨⟨d0, r0', hlist_i, hd0, hd1⟩, hno_cd, hno_dash⟩ := parseIntModelChars_propsM rs.toList mi hmi
    have hnd_p : hasDatePrefix rs.toList = false := by
      cases hd : hasDatePrefix rs.toList; · rfl
      unfold hasDatePrefix at hd; split at hd <;> try (simp at hd; done)
      rename_i heq; rw [hlist_i] at heq; obtain ⟨_, hr_eq⟩ := List.cons.inj heq
      exact absurd rfl (hno_dash d0 r0' hlist_i '-' (by rw [hr_eq]; simp))
    have hnt_p : hasTimePrefix rs.toList = false := by
      unfold hasTimePrefix; split
      · rename_i _ _ _ _ _ _ _ heq
        exact absurd rfl (hno_cd ':' (by rw [heq]; simp)).1
      · rfl
    have hnot_dt : parseDateTimeChars rs.toList = none := by
      simp [parseDateTimeChars, hnd_p, hnt_p, show ¬(':' ∈ rs.toList) from fun hm => (hno_cd ':' hm).1 rfl]
    have hnot_spec : (rs.toList == ['i', 'n', 'f'] || rs.toList == ['+', 'i', 'n', 'f'] || rs.toList == ['-', 'i', 'n', 'f'] ||
        rs.toList == ['n', 'a', 'n'] || rs.toList == ['+', 'n', 'a', 'n'] || rs.toList == ['-', 'n', 'a', 'n']) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · intro heq; rw [heq] at hlist_i; obtain ⟨rfl, _⟩ := List.cons.inj hlist_i; revert hd0; decide
      · intro heq; rw [heq] at hlist_i; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist_i
        have hd := hd1 'i' ['n', 'f'] (Or.inl rfl) rfl; revert hd; decide
      · intro heq; rw [heq] at hlist_i; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist_i
        have hd := hd1 'i' ['n', 'f'] (Or.inr rfl) rfl; revert hd; decide
      · intro heq; rw [heq] at hlist_i; obtain ⟨rfl, _⟩ := List.cons.inj hlist_i; revert hd0; decide
      · intro heq; rw [heq] at hlist_i; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist_i
        have hd := hd1 'n' ['a', 'n'] (Or.inl rfl) rfl; revert hd; decide
      · intro heq; rw [heq] at hlist_i; obtain ⟨rfl, rfl⟩ := List.cons.inj hlist_i
        have hd := hd1 'n' ['a', 'n'] (Or.inr rfl) rfl; revert hd; decide
    have hnot_flt : isFloatTokenCandidateChars rs.toList = false := by
      unfold isFloatTokenCandidateChars; rw [hnot_spec, Bool.false_or]
      by_cases h0x : rs.startsWith "0x" = true
      · rcases String.startsWith_string_iff.mp h0x with ⟨t, ht⟩
        rw [show ("0x" : String).toList = ['0', 'x'] from rfl] at ht; simp [← ht]
      · simp only [h0x, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true', Bool.or_eq_false_iff, String.contains_char_eq, decide_eq_false_iff_not] at hnoExp
        simp [show ¬('.' ∈ rs.toList) from fun hm => (hno_cd '.' hm).2 rfl, hnoExp.1, hnoExp.2]
    have hno_up : hasUppercaseBasePrefixChars rs.toList = false := by
      have hsw (p : String) (hp : rs.startsWith p = false) (t : List Char) (ht : rs.toList = p.toList ++ t) : False := by
        rw [String.startsWith_string_iff.mpr ⟨t, ht.symm⟩] at hp; nomatch hp
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hnoBad
      rcases hnoBad with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
      unfold hasUppercaseBasePrefixChars; split
      all_goals try rfl
      all_goals rename_i _ tail heq; exfalso
      all_goals first | exact hsw "0X" h1 tail heq | exact hsw "0O" h2 tail heq | exact hsw "0B" h3 tail heq
                      | exact hsw "+0X" h4 tail heq | exact hsw "+0O" h5 tail heq | exact hsw "+0B" h6 tail heq
                      | exact hsw "-0X" h7 tail heq | exact hsw "-0O" h8 tail heq | exact hsw "-0B" h9 tail heq
    have hpi_ok : (toCharNumApi numApi).parseInt64Chars rs.toList = .ok n := by
      change numApi.parseInt64 (String.ofList rs.toList) = .ok n
      rw [String.ofList_toList]
      have hspec := (hnum.parseInt64 rs).1
      cases ha : numApi.parseInt64 rs with
      | error _ => simp [Except.mapError, ha, hp64] at hspec
      | ok m => simp [Except.mapError, ha, hp64] at hspec; exact congrArg Except.ok hspec
    have hne_nil : rs.toList ≠ [] := by simp [hrs_l]
    have hne_t : rs.toList ≠ ['t', 'r', 'u', 'e'] := fun e => by
      rw [e] at hlist_i; obtain ⟨rfl, _⟩ := List.cons.inj hlist_i; revert hd0; decide
    have hne_f : rs.toList ≠ ['f', 'a', 'l', 's', 'e'] := fun e => by
      rw [e] at hlist_i; obtain ⟨rfl, _⟩ := List.cons.inj hlist_i; revert hd0; decide
    have hcls : classifyScalarChars (toCharNumApi numApi) rs.toList = .ok (.int n) := by
      unfold classifyScalarChars; split
      · rename_i heq; exact absurd heq hne_nil
      · rename_i heq; exact absurd heq hne_t
      · rename_i heq; exact absurd heq hne_f
      · simp [hnot_dt, hnot_flt, hno_up, hpi_ok]
    refine ⟨hcl_rs, hne_nil, fun rem hrem fuel hf => ?_⟩
    cases fuel with | zero => omega | succ f =>
    exact ⟨.int n, by rw [step_unq rem hrem f, hcls]; rfl, rfl⟩
  | float lex? =>
    cases v <;> try (cases lex? <;> simp [renderValueInline] at hr; done)
    rename_i fv
    have hv : isValidFloatLex rs fv = true := by
      cases lex? with
      | none =>
        simp only [renderValueInline] at hr
        have hc := canonicalFloat_isValidFloatLex fv
        if h1 : fv.isNaN = true then simp [h1] at hr; subst hr; exact hc.1 h1 else
        if h2 : (fv == Float.inf) = true then simp [h1, h2] at hr; subst hr; exact hc.2.1 h2 else
        if h3 : (fv == -Float.inf) = true then simp [h1, h2, h3] at hr; subst hr; exact hc.2.2.1 h3 else
        if h4 : (fv.toBits == (0.0 : Float).toBits) = true then simp [h1, h2, h3, h4] at hr; subst hr; exact hc.2.2.2.1 (eq_of_beq h4) else
        if h5 : (fv.toBits == (-0.0 : Float).toBits) = true then simp [h1, h2, h3, h4, h5] at hr; subst hr; exact hc.2.2.2.2 (eq_of_beq h5) else
        simp [h1, h2, h3, h4, h5] at hr
      | some l =>
        simp only [renderValueInline] at hr
        if hv0 : isValidFloatLex l fv = true then simp [hv0] at hr; subst hr; exact hv0
        else simp [hv0] at hr
    simp only [isValidFloatLex, Bool.and_eq_true] at hv
    rcases hv with ⟨⟨hmark, hnoTerm⟩, hpm_b⟩
    cases hpm : parseFloatModel rs with
    | error _ => rw [hpm] at hpm_b; cases hpm_b
    | ok g =>
      have hp_cs : parseFloatModelChars rs.toList = .ok g := by simpa [parseFloatModel] using hpm
      obtain ⟨_, hfmc⟩ := parseFloatModelChars_propsM rs.toList g hp_cs
      have hcl_rs : CleanNorm rs.toList := List.all_eq_true.mpr fun c hc => by
        have hp := (isFloatModelCharM_props c (hfmc c hc)).2.2.2
        simp only [Bool.and_eq_true] at hp ⊢
        exact ⟨hp.1.2, hp.2.2⟩
      have hnd_p : hasDatePrefix rs.toList = false := by
        cases hd : hasDatePrefix rs.toList; · rfl
        exfalso; apply float_not_date_dashes rs.toList g hp_cs
        unfold hasDatePrefix at hd; split at hd
        · rename_i _ _ _ _ _ _ _ _ _ heq
          rw [heq]; exact ⟨rfl, rfl⟩
        · nomatch hd
      have hnt_p : hasTimePrefix rs.toList = false := by
        unfold hasTimePrefix; split
        · rename_i _ _ _ _ _ _ _ heq
          exact absurd rfl (isFloatModelCharM_props ':' (hfmc ':' (by rw [heq]; simp))).1
        · rfl
      have hnot_dt : parseDateTimeChars rs.toList = none := by
        simp [parseDateTimeChars, hnd_p, hnt_p,
          show ¬(':' ∈ rs.toList) from fun hm => (isFloatModelCharM_props ':' (hfmc ':' hm)).1 rfl]
      have hcand : isFloatTokenCandidateChars rs.toList = true := by
        have hmark_or : (rs.toList == ['i', 'n', 'f'] || rs.toList == ['+', 'i', 'n', 'f'] ||
            rs.toList == ['-', 'i', 'n', 'f'] || rs.toList == ['n', 'a', 'n'] ||
            rs.toList == ['+', 'n', 'a', 'n'] || rs.toList == ['-', 'n', 'a', 'n']) = true ∨
            (rs.toList.contains '.' || rs.toList.contains 'e' || rs.toList.contains 'E') = true := by
          simp only [String.contains_char_eq, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, String.ext_iff] at hmark
          simp only [List.contains_iff_mem, Bool.or_eq_true, beq_iff_eq]
          rcases hmark with (((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
          · exact Or.inr (Or.inl (Or.inl h1))
          · exact Or.inr (Or.inl (Or.inr h1))
          · exact Or.inr (Or.inr h1)
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (by simpa using h1))))))
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simpa using h1))))))
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simpa using h1)))))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (by simpa using h1))))
          · exact Or.inl (Or.inl (Or.inr (by simpa using h1)))
          · exact Or.inl (Or.inr (by simpa using h1))
        unfold isFloatTokenCandidateChars; dsimp only
        rcases hmark_or with hsp | hde
        · rw [hsp, Bool.true_or]
        · rw [hde, Bool.and_true, Bool.or_eq_true]; right
          rw [Bool.not_eq_true']
          split
          all_goals try rfl
          all_goals
            rename_i _ heq
            have hx : 'x' ∈ rs.toList ∨ 'X' ∈ rs.toList := by rw [heq]; simp
            rcases hx with hm | hm
            · exact absurd rfl (isFloatModelCharM_props 'x' (hfmc 'x' hm)).2.1
            · exact absurd rfl (isFloatModelCharM_props 'X' (hfmc 'X' hm)).2.2.1
      have hpf_ok : ∃ g', (toCharNumApi numApi).parseFloatChars rs.toList = .ok g' := by
        change ∃ g', numApi.parseFloat (String.ofList rs.toList) = .ok g'
        rw [String.ofList_toList]
        have hspec := hnum.parseFloat rs; rw [hpm] at hspec
        cases ha : numApi.parseFloat rs with
        | error _ => rw [ha] at hspec; exact False.elim hspec
        | ok g' => exact ⟨g', rfl⟩
      rcases hpf_ok with ⟨g', hg'⟩
      have hne_nil : rs.toList ≠ [] := by simp [hrs_l]
      have hne_t : rs.toList ≠ ['t', 'r', 'u', 'e'] := fun e => by
        have hm := hfmc 't' (by rw [e]; simp); revert hm; decide
      have hne_f : rs.toList ≠ ['f', 'a', 'l', 's', 'e'] := fun e => by
        have hm := hfmc 'l' (by rw [e]; simp); revert hm; decide
      have hcls : classifyScalarChars (toCharNumApi numApi) rs.toList = .ok (.float g') := by
        unfold classifyScalarChars; split
        · rename_i heq; exact absurd heq hne_nil
        · rename_i heq; exact absurd heq hne_t
        · rename_i heq; exact absurd heq hne_f
        · simp [hnot_dt, hcand, hg']
      refine ⟨hcl_rs, hne_nil, fun rem hrem fuel hf => ?_⟩
      cases fuel with | zero => omega | succ f =>
      exact ⟨.float g', by rw [step_unq rem hrem f, hcls]; rfl, rfl⟩

end LeanSwe.Toml.Proofs
