import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.Proofs.RoundTripScalar
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse
open LeanSwe.NumParse.Model

private theorem parseValueFuel_unquoted (numApi : NumParseApi) (fuel : Nat) (c0 : Char) (cs : List Char)
    (hq1 : c0 ≠ '"') (hq2 : c0 ≠ '\'') (hb : c0 ≠ '[') (hbr : c0 ≠ '{') :
    parseValueFuel numApi (fuel + 1) (c0 :: cs) =
      (let (tok, rest) := takeUnquotedToken (c0 :: cs)
       classifyScalarToken numApi tok >>= fun v => .ok (v, rest)) := by
  conv => lhs; unfold parseValueFuel
  split <;>
    first
    | exact absurd rfl hq1
    | exact absurd rfl hq2
    | exact absurd rfl hb
    | exact absurd rfl hbr
    | (rename_i heq; injection heq with h1 _; first
      | exact absurd h1 hq1
      | exact absurd h1 hq2
      | exact absurd h1 hb
      | exact absurd h1 hbr)
    | rfl

private theorem clean_no_nl_of_full (cs : List Char)
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true) :
    (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have h1 := h c hc
  simp only [Bool.and_eq_true] at h1 ⊢
  exact h1.1

private theorem clean_cr_of_no_nl (cs : List Char)
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) :
    (cs.all fun c => !isDisallowedControl c && c != '\r') = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have h1 := h c hc
  simp only [Bool.and_eq_true] at h1 ⊢
  exact h1.1

private theorem renderValueInline_scalar_parseValueFuel (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (v : TomlValue) (tape : ValueTape)
    (rs : String) (hr : renderValueInline v tape = some rs)
    (rest : List Char) (fuel : Nat) (hf : fuel ≥ 1)
    (hscalar : match v with | .array _ => False | .table _ => False | _ => True)
    (hrest : ∀ c r, rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) :
    ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
      TomlEquiv v v' ∧
      (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
      ((∀ s st, v = .string s → tape = .string st → st = .basic ∨ st = .literal) →
        (rs.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) := by
  cases fuel with
  | zero => omega
  | succ f =>
    have hrest_q : ∀ c r, rest = c :: r → c ≠ '"' ∧ c ≠ '\'' := by
      intro c r h
      have hd := (hrest c r h).1
      exact ⟨fun hc => (by subst hc; cases hd), fun hc => (by subst hc; cases hd)⟩
    have hrest_delim : ∀ c r, rest = c :: r → isUnquotedDelim c = true :=
      fun c r h => (hrest c r h).1
    cases v with
    | array _ => cases hscalar
    | table _ => cases hscalar
    | string s =>
      cases tape with
      | string st =>
        simp only [renderValueInline] at hr
        obtain ⟨hp, hcl, hsl⟩ := renderStringLiteral_parseValueFuel numApi s st rs hr rest (f + 1) (by omega) hrest_q
        refine ⟨.string s, hp, tomlEquiv_refl _, hcl, fun h => ?_⟩
        exact hsl (h s st rfl rfl)
      | _ => simp [renderValueInline] at hr
    | int n =>
      cases tape with
      | int olex =>
        have hlex : isValidIntLex rs n = true := by
          cases olex with
          | none =>
            simp only [renderValueInline] at hr
            injection hr with hrs; subst hrs
            exact formatInt64Canonical_isValidIntLex n
          | some lex =>
            simp only [renderValueInline] at hr
            split at hr
            · rename_i hv
              injection hr with hrs; subst hrs; exact hv
            · cases hr
        obtain ⟨hcls, hcl, c0, cs0, hrs_list, hq1, hq2, hb, hbr⟩ :=
          isValidIntLex_classifyScalarToken numApi hInt rs n hlex
        have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
        rw [String.ofList_toList] at htok
        have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.int n, rest) := by
          rw [hrs_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hq1 hq2 hb hbr]
          rw [← List.cons_append, ← hrs_list, htok]
          simp [hcls, bind, Except.bind]
        have hnl := clean_no_nl_of_full _ hcl
        exact ⟨.int n, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | float fl =>
      cases tape with
      | float olex =>
        have hlex : isValidFloatLex rs fl = true := by
          cases olex with
          | none =>
            simp only [renderValueInline] at hr
            split at hr
            · rename_i h1; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).1 h1
            · split at hr
              · rename_i h2; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.1 h2
              · split at hr
                · rename_i h3; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.1 h3
                · split at hr
                  · rename_i h4; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.1 (by simpa using h4)
                  · split at hr
                    · rename_i h5; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.2 (by simpa using h5)
                    · cases hr
          | some lex =>
            simp only [renderValueInline] at hr
            split at hr
            · rename_i hv; injection hr with hrs; subst hrs; exact hv
            · cases hr
        obtain ⟨g, hcls, heq_f, hcl, c0, cs0, hrs_list, hq1, hq2, hb, hbr⟩ :=
          isValidFloatLex_classifyScalarToken numApi hFloat rs fl hlex
        have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
        rw [String.ofList_toList] at htok
        have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.float g, rest) := by
          rw [hrs_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hq1 hq2 hb hbr]
          rw [← List.cons_append, ← hrs_list, htok]
          simp [hcls, bind, Except.bind]
        have hnl := clean_no_nl_of_full _ hcl
        exact ⟨.float g, hpv, heq_f, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | bool b =>
      cases tape with
      | bool =>
        cases b
        · simp [renderValueInline] at hr
          subst hr
          have htok := takeUnquotedToken_noSpace ("false" : String).toList rest (by decide) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi "false" = .ok (.bool false) := rfl
          refine ⟨.bool false, ?_, tomlEquiv_refl _, by decide, fun _ => by decide⟩
          have hf_list : ("false" : String).toList = ['f', 'a', 'l', 's', 'e'] := rfl
          rw [hf_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f 'f' (['a', 'l', 's', 'e'] ++ rest) (by decide) (by decide) (by decide) (by decide)]
          rw [← List.cons_append, ← hf_list, htok]
          simp [hcls, bind, Except.bind]
        · simp [renderValueInline] at hr
          subst hr
          have htok := takeUnquotedToken_noSpace ("true" : String).toList rest (by decide) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi "true" = .ok (.bool true) := rfl
          refine ⟨.bool true, ?_, tomlEquiv_refl _, by decide, fun _ => by decide⟩
          have ht_list : ("true" : String).toList = ['t', 'r', 'u', 'e'] := rfl
          rw [ht_list, List.cons_append]
          rw [parseValueFuel_unquoted numApi f 't' (['r', 'u', 'e'] ++ rest) (by decide) (by decide) (by decide) (by decide)]
          rw [← List.cons_append, ← ht_list, htok]
          simp [hcls, bind, Except.bind]
      | _ => simp [renderValueInline] at hr
    | localDate d =>
      cases tape with
      | localDate =>
        simp only [renderValueInline] at hr
        obtain ⟨hdt, hcl, hhd⟩ := renderDate_localDate d rs hr
        cases hrs_list : rs.toList with
        | nil =>
          have hrs : rs = "" := by rw [← String.ofList_toList (s := rs), hrs_list]
          subst hrs; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
        | cons c0 cs0 =>
          have hdig := hhd c0 cs0 hrs_list
          have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
            refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
          have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi rs = .ok (.localDate d) := by
            have hne : rs.isEmpty = false := by
              rw [Bool.eq_false_iff]; intro he
              have : rs = "" := by simpa using he
              subst this; cases hrs_list
            have hnt : rs ≠ "true" := fun he => by subst he; cases hrs_list; revert hdig; decide
            have hnf : rs ≠ "false" := fun he => by subst he; cases hrs_list; revert hdig; decide
            simp [classifyScalarToken, hne, hnt, hnf, hdt]
          have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.localDate d, rest) := by
            rw [hrs_list, List.cons_append]
            rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
            rw [← List.cons_append, ← hrs_list, htok]
            simp [hcls, bind, Except.bind]
          have hnl := clean_no_nl_of_full _ hcl
          rw [← hrs_list]
          exact ⟨.localDate d, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | localTime t =>
      cases tape with
      | localTime fd =>
        simp only [renderValueInline] at hr
        obtain ⟨hdt, hcl, hhd⟩ := renderTime_localTime t fd rs hr
        cases hrs_list : rs.toList with
        | nil =>
          have hrs : rs = "" := by rw [← String.ofList_toList (s := rs), hrs_list]
          subst hrs; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
        | cons c0 cs0 =>
          have hdig := hhd c0 cs0 hrs_list
          have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
            refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
          have htok := takeUnquotedToken_noSpace rs.toList rest (clean_all_not_unquotedDelim _ hcl) hrest
          rw [String.ofList_toList] at htok
          have hcls : classifyScalarToken numApi rs = .ok (.localTime t) := by
            have hne : rs.isEmpty = false := by
              rw [Bool.eq_false_iff]; intro he
              have : rs = "" := by simpa using he
              subst this; cases hrs_list
            have hnt : rs ≠ "true" := fun he => by subst he; cases hrs_list; revert hdig; decide
            have hnf : rs ≠ "false" := fun he => by subst he; cases hrs_list; revert hdig; decide
            simp [classifyScalarToken, hne, hnt, hnf, hdt]
          have hpv : parseValueFuel numApi (f + 1) (rs.toList ++ rest) = .ok (.localTime t, rest) := by
            rw [hrs_list, List.cons_append]
            rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
            rw [← List.cons_append, ← hrs_list, htok]
            simp [hcls, bind, Except.bind]
          have hnl := clean_no_nl_of_full _ hcl
          rw [← hrs_list]
          exact ⟨.localTime t, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hnl, fun _ => hnl⟩
      | _ => simp [renderValueInline] at hr
    | localDateTime dt =>
      cases tape with
      | localDateTime sep fd =>
        simp only [renderValueInline, bind, Option.bind] at hr
        cases hdr : renderDate dt.date with
        | none => simp [hdr] at hr
        | some ds =>
          cases htr : renderTime dt.time fd with
          | none => simp [hdr, htr] at hr
          | some ts =>
            simp only [hdr, htr, Option.some.injEq] at hr
            subst hr
            obtain ⟨_, hds_cl, hds_hd⟩ := renderDate_localDate dt.date ds hdr
            obtain ⟨_, hts_cl, _⟩ := renderTime_localTime dt.time fd ts htr
            have hdt := renderDateTime_localDateTime dt sep fd ds ts hdr htr
            have hds_ne : ds.toList ≠ [] := by
              intro hnil
              have h1 : ds = "" := by rw [← String.ofList_toList (s := ds), hnil]
              subst h1; simp [renderDate] at hdr
            cases hds_list : ds.toList with
            | nil => exact absurd hds_list hds_ne
            | cons c0 cs0 =>
              have hdig := hds_hd c0 cs0 hds_list
              have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
                refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
              have htok : takeUnquotedToken ((ds ++ renderDateTimeSep sep ++ ts).toList ++ rest) =
                  (ds ++ renderDateTimeSep sep ++ ts, rest) := by
                cases sep
                · have hsep_cl : (("T" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                  have hfull_cl : (ds ++ renderDateTimeSep .upperT ++ ts).toList.all (fun c => !isUnquotedDelim c) = true := by
                    simp only [renderDateTimeSep, String.toList_append, List.all_append,
                      clean_all_not_unquotedDelim _ hds_cl, hsep_cl, clean_all_not_unquotedDelim _ hts_cl,
                      Bool.and_self]
                  have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .upperT ++ ts).toList rest hfull_cl hrest
                  simpa [String.ofList_toList, String.append_assoc] using ht
                · have hsep_cl : (("t" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                  have hfull_cl : (ds ++ renderDateTimeSep .lowerT ++ ts).toList.all (fun c => !isUnquotedDelim c) = true := by
                    simp only [renderDateTimeSep, String.toList_append, List.all_append,
                      clean_all_not_unquotedDelim _ hds_cl, hsep_cl, clean_all_not_unquotedDelim _ hts_cl,
                      Bool.and_self]
                  have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .lowerT ++ ts).toList rest hfull_cl hrest
                  simpa [String.ofList_toList, String.append_assoc] using ht
                · have ht := dateTime_space_takeUnquotedToken dt.date dt.time fd ds ts "" hdr htr (by decide) rest hrest_delim
                  simpa [renderDateTimeSep, String.append_empty] using ht
              have hcls : classifyScalarToken numApi (ds ++ renderDateTimeSep sep ++ ts) = .ok (.localDateTime dt) := by
                have hfull_list : (ds ++ renderDateTimeSep sep ++ ts).toList = c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList) := by
                  simp [String.toList_append, hds_list, List.cons_append]
                have hne : (ds ++ renderDateTimeSep sep ++ ts).isEmpty = false := by
                  rw [Bool.eq_false_iff]; intro he
                  have h1 : (ds ++ renderDateTimeSep sep ++ ts) = "" := by simpa using he
                  have h2 := congrArg String.toList h1
                  rw [hfull_list] at h2; cases h2
                have hnt : (ds ++ renderDateTimeSep sep ++ ts) ≠ "true" := by
                  intro he
                  have h2 := congrArg String.toList he
                  rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                have hnf : (ds ++ renderDateTimeSep sep ++ ts) ≠ "false" := by
                  intro he
                  have h2 := congrArg String.toList he
                  rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                simp [classifyScalarToken, hne, hnt, hnf, hdt]
              have hpv : parseValueFuel numApi (f + 1) ((ds ++ renderDateTimeSep sep ++ ts).toList ++ rest) =
                  .ok (.localDateTime dt, rest) := by
                have hfull_list : (ds ++ renderDateTimeSep sep ++ ts).toList = c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList) := by
                  simp [String.toList_append, hds_list, List.cons_append]
                rw [hfull_list, List.cons_append]
                rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ rest)
                  hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
                rw [← List.cons_append, ← hfull_list, htok]
                simp [hcls, bind, Except.bind]
              have hsep_cl : ((renderDateTimeSep sep).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                cases sep <;> decide
              have hcl : ((ds ++ renderDateTimeSep sep ++ ts).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                simp only [String.toList_append, List.all_append, hsep_cl, clean_no_nl_of_full _ hds_cl,
                  clean_no_nl_of_full _ hts_cl, Bool.and_self]
              exact ⟨.localDateTime dt, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hcl, fun _ => hcl⟩
      | _ => simp [renderValueInline] at hr
    | offsetDateTime odt =>
      cases tape with
      | offsetDateTime sep oStyle fd =>
        simp only [renderValueInline, bind, Option.bind] at hr
        cases hdr : renderDate odt.dateTime.date with
        | none => simp [hdr] at hr
        | some ds =>
          cases htr : renderTime odt.dateTime.time fd with
          | none => simp [hdr, htr] at hr
          | some ts =>
            cases hor : renderOffset odt.offset oStyle with
            | none => simp [hdr, htr, hor] at hr
            | some os =>
              simp only [hdr, htr, hor, Option.some.injEq] at hr
              subst hr
              obtain ⟨_, hds_cl, hds_hd⟩ := renderDate_localDate odt.dateTime.date ds hdr
              obtain ⟨_, hts_cl, _⟩ := renderTime_localTime odt.dateTime.time fd ts htr
              obtain ⟨_, hos_cl⟩ := renderOffset_parseOffsetPart odt.offset oStyle os hor
              have hdt := renderOffsetDateTime_offsetDateTime odt sep oStyle fd ds ts os hdr htr hor
              have hds_ne : ds.toList ≠ [] := by
                intro hnil
                have h1 : ds = "" := by rw [← String.ofList_toList (s := ds), hnil]
                subst h1; simp [renderDate] at hdr
              cases hds_list : ds.toList with
              | nil => exact absurd hds_list hds_ne
              | cons c0 cs0 =>
                have hdig := hds_hd c0 cs0 hds_list
                have hhead_ok : c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by
                  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> revert hdig <;> decide
                have htok : takeUnquotedToken ((ds ++ renderDateTimeSep sep ++ ts ++ os).toList ++ rest) =
                    (ds ++ renderDateTimeSep sep ++ ts ++ os, rest) := by
                  cases sep
                  · have hsep_cl : (("T" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                    have hfull_cl : (ds ++ renderDateTimeSep .upperT ++ ts ++ os).toList.all (fun c => !isUnquotedDelim c) = true := by
                      simp only [renderDateTimeSep, String.toList_append, List.all_append,
                        clean_all_not_unquotedDelim _ hds_cl, hsep_cl,
                        clean_all_not_unquotedDelim _ hts_cl, clean_all_not_unquotedDelim _ hos_cl,
                        Bool.and_self]
                    have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .upperT ++ ts ++ os).toList rest hfull_cl hrest
                    simpa [String.ofList_toList, String.append_assoc] using ht
                  · have hsep_cl : (("t" : String).toList.all fun c => !isUnquotedDelim c) = true := by decide
                    have hfull_cl : (ds ++ renderDateTimeSep .lowerT ++ ts ++ os).toList.all (fun c => !isUnquotedDelim c) = true := by
                      simp only [renderDateTimeSep, String.toList_append, List.all_append,
                        clean_all_not_unquotedDelim _ hds_cl, hsep_cl,
                        clean_all_not_unquotedDelim _ hts_cl, clean_all_not_unquotedDelim _ hos_cl,
                        Bool.and_self]
                    have ht := takeUnquotedToken_noSpace (ds ++ renderDateTimeSep .lowerT ++ ts ++ os).toList rest hfull_cl hrest
                    simpa [String.ofList_toList, String.append_assoc] using ht
                  · exact dateTime_space_takeUnquotedToken odt.dateTime.date odt.dateTime.time fd ds ts os hdr htr
                      (clean_all_not_unquotedDelim _ hos_cl) rest hrest_delim
                have hcls : classifyScalarToken numApi (ds ++ renderDateTimeSep sep ++ ts ++ os) = .ok (.offsetDateTime odt) := by
                  have hfull_list : (ds ++ renderDateTimeSep sep ++ ts ++ os).toList =
                      c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ os.toList) := by
                    simp [String.toList_append, hds_list, List.cons_append, List.append_assoc]
                  have hne : (ds ++ renderDateTimeSep sep ++ ts ++ os).isEmpty = false := by
                    rw [Bool.eq_false_iff]; intro he
                    have h1 : (ds ++ renderDateTimeSep sep ++ ts ++ os) = "" := by simpa using he
                    have h2 := congrArg String.toList h1
                    rw [hfull_list] at h2; cases h2
                  have hnt : (ds ++ renderDateTimeSep sep ++ ts ++ os) ≠ "true" := by
                    intro he
                    have h2 := congrArg String.toList he
                    rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                  have hnf : (ds ++ renderDateTimeSep sep ++ ts ++ os) ≠ "false" := by
                    intro he
                    have h2 := congrArg String.toList he
                    rw [hfull_list] at h2; injection h2 with hc; subst hc; revert hdig; decide
                  simp [classifyScalarToken, hne, hnt, hnf, hdt]
                have hpv : parseValueFuel numApi (f + 1) ((ds ++ renderDateTimeSep sep ++ ts ++ os).toList ++ rest) =
                    .ok (.offsetDateTime odt, rest) := by
                  have hfull_list : (ds ++ renderDateTimeSep sep ++ ts ++ os).toList =
                      c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ os.toList) := by
                    simp [String.toList_append, hds_list, List.cons_append, List.append_assoc]
                  rw [hfull_list, List.cons_append]
                  rw [parseValueFuel_unquoted numApi f c0 (cs0 ++ (renderDateTimeSep sep ++ ts).toList ++ os.toList ++ rest)
                    hhead_ok.1 hhead_ok.2.1 hhead_ok.2.2.1 hhead_ok.2.2.2]
                  rw [← List.cons_append, ← hfull_list, htok]
                  simp [hcls, bind, Except.bind]
                have hsep_cl : ((renderDateTimeSep sep).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                  cases sep <;> decide
                have hcl : ((ds ++ renderDateTimeSep sep ++ ts ++ os).toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true := by
                  simp only [String.toList_append, List.all_append, hsep_cl, clean_no_nl_of_full _ hds_cl,
                    clean_no_nl_of_full _ hts_cl, clean_no_nl_of_full _ hos_cl, Bool.and_self]
                exact ⟨.offsetDateTime odt, hpv, tomlEquiv_refl _, clean_cr_of_no_nl _ hcl, fun _ => hcl⟩
      | _ => simp [renderValueInline] at hr

private theorem skipHorizWs_cons_of_false (c : Char) (cs : List Char)
    (h : isHorizWs c = false) : skipHorizWs (c :: cs) = c :: cs := by
  simp [skipHorizWs, h]

private theorem skipHorizWs_space (cs : List Char) : skipHorizWs (' ' :: cs) = skipHorizWs cs := by
  simp [skipHorizWs, isHorizWs]

private theorem skipTriviaNewlines_cons_of_safe (c : Char) (cs : List Char)
    (hws : isHorizWs c = false) (hn : c ≠ '\n') (hc : c ≠ '#') :
    skipTriviaNewlines (c :: cs) = c :: cs := by
  unfold skipTriviaNewlines skipTriviaNewlinesAux
  split
  · rename_i heq; cases heq
  · rename_i heq; injection heq with h1; exact absurd h1 hn
  · rename_i head rest _ heq
    injection heq with h1 h2; subst h1; subst h2
    simp [hws, beq_iff_eq, hc]

private theorem parseArrayFuel_skip_space (numApi : NumParseApi) (fuel : Nat)
    (cs : List Char) (revAcc : List TomlValue) :
    parseArrayFuel numApi fuel (' ' :: cs) revAcc = parseArrayFuel numApi fuel cs revAcc := by
  cases fuel with
  | zero => rfl
  | succ f =>
    have hsp : skipTriviaNewlines (' ' :: cs) = skipTriviaNewlines cs := by
      simp [skipTriviaNewlines, skipTriviaNewlinesAux, isHorizWs]
    simp only [parseArrayFuel, hsp]

private theorem renderKey_headSafe (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) :
    ∃ c0 cs0, rk.toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧
      c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ '[' ∧ c0 ≠ '.' := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hbare
      injection hr with hrk; subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      cases hlist : k.toList with
      | nil =>
        have h0 : k = "" := by rw [← String.ofList_toList (s := k), hlist]
        subst h0; simp at hbare
      | cons c0 cs0 =>
        have hc0 : isBareKeyChar c0 = true :=
          List.all_eq_true.mp hbare.2 c0 (by rw [hlist]; simp)
        have hcl := isBareKeyChar_clean c0 hc0
        simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl
        have hnbr : c0 ≠ '[' := by
          intro heq; subst heq; cases hc0
        exact ⟨c0, cs0, rfl, hcl.1.1.1.1.1.1.1.1.2, hcl.1.1.1.1.1.1.1.1.1.2,
          hcl.1.1.1.1.2, hcl.1.1.2, hcl.1.2, hnbr, hcl.1.1.1.1.1.1.1.2⟩
    · cases hr
  | basic =>
    simp only [renderKey] at hr
    injection hr with hrk; subst hrk
    refine ⟨'"', (escapeBasicBody false k ++ "\"").toList, ?_, by decide⟩
    simp [String.toList_append]
  | literal =>
    simp only [renderKey] at hr
    split at hr
    · injection hr with hrk; subst hrk
      refine ⟨'\'', (k ++ "'").toList, ?_, by decide⟩
      simp [String.toList_append]
    · cases hr

private theorem renderValueInline_headSafe (v : TomlValue) (tape : ValueTape) (rs : String)
    (hr : renderValueInline v tape = some rs) :
    ∃ c0 cs0, rs.toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧
      c0 ≠ '\n' ∧ c0 ≠ '\r' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ ',' := by
  have hdigit_safe : ∀ c0, isAsciiDigit c0 = true →
      isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '\r' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ ',' := by
    intro c0 hd
    have hws : isHorizWs c0 = false := by
      cases hc0_eq : isHorizWs c0 with
      | false => rfl
      | true =>
        simp [isHorizWs] at hc0_eq
        rcases hc0_eq with rfl | rfl <;> cases hd
    refine ⟨hws, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> cases hd
  cases v with
  | string s =>
    cases tape with
    | string st =>
      simp only [renderValueInline] at hr
      cases st
      · simp only [renderStringLiteral] at hr; injection hr with hrs; subst hrs
        refine ⟨'"', (escapeBasicBody false s ++ "\"").toList, ?_, by decide⟩
        simp [String.toList_append]
      · simp only [renderStringLiteral] at hr; injection hr with hrs; subst hrs
        refine ⟨'"', ('"' :: '"' :: '\n' :: (escapeBasicBody true s ++ "\"\"\"").toList), ?_, by decide⟩
        simp [String.toList_append]
      · simp only [renderStringLiteral] at hr
        split at hr
        · injection hr with hrs; subst hrs
          refine ⟨'\'', (s ++ "'").toList, ?_, by decide⟩
          simp [String.toList_append]
        · cases hr
      · simp only [renderStringLiteral] at hr
        split at hr
        · injection hr with hrs; subst hrs
          refine ⟨'\'', ('\'' :: '\'' :: '\n' :: (s ++ "'''").toList), ?_, by decide⟩
          simp [String.toList_append]
        · cases hr
    | _ => simp [renderValueInline] at hr
  | int n =>
    cases tape with
    | int olex =>
      have hlex : isValidIntLex rs n = true := by
        cases olex with
        | none =>
          simp only [renderValueInline] at hr; injection hr with hrs; subst hrs
          exact formatInt64Canonical_isValidIntLex n
        | some lex =>
          simp only [renderValueInline] at hr; split at hr
          · injection hr with hrs; subst hrs; assumption
          · cases hr
      simp only [isValidIntLex, Bool.and_eq_true] at hlex
      have hm : ∃ m : Int, NumParse.Model.parseIntModelChars rs.toList = .ok m := by
        cases hp : NumParse.Model.parseInt64Model rs with
        | error => rw [hp] at hlex; simp at hlex
        | ok parsed =>
          unfold NumParse.Model.parseInt64Model NumParse.Model.parseIntModel at hp
          cases hc : NumParse.Model.parseIntModelChars rs.toList with
          | error => rw [hc] at hp; cases hp
          | ok m => exact ⟨m, rfl⟩
      rcases hm with ⟨m, hm⟩
      obtain ⟨⟨c0, cs0, hlist, hc0, _⟩, _⟩ := parseIntModelChars_props rs.toList m hm
      refine ⟨c0, cs0, hlist, ?_⟩
      rcases hc0 with rfl | rfl | hd
      · decide
      · decide
      · exact hdigit_safe c0 hd
    | _ => simp [renderValueInline] at hr
  | float fl =>
    cases tape with
    | float olex =>
      have hlex : isValidFloatLex rs fl = true := by
        cases olex with
        | none =>
          simp only [renderValueInline] at hr
          split at hr
          · rename_i h1; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).1 h1
          · split at hr
            · rename_i h2; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.1 h2
            · split at hr
              · rename_i h3; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.1 h3
              · split at hr
                · rename_i h4; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.1 (by simpa using h4)
                · split at hr
                  · rename_i h5; injection hr with hrs; subst hrs; exact (canonicalFloat_isValidFloatLex fl).2.2.2.2 (by simpa using h5)
                  · cases hr
        | some lex =>
          simp only [renderValueInline] at hr; split at hr
          · injection hr with hrs; subst hrs; assumption
          · cases hr
      simp only [isValidFloatLex, Bool.and_eq_true] at hlex
      have hm : ∃ g, NumParse.Model.parseFloatModelChars rs.toList = .ok g := by
        cases hp : NumParse.Model.parseFloatModel rs with
        | error => rw [hp] at hlex; simp at hlex
        | ok g => exact ⟨g, by simpa [NumParse.Model.parseFloatModel] using hp⟩
      rcases hm with ⟨g, hg⟩
      obtain ⟨⟨c0, cs0, hlist, hc0⟩, _, _, _, _⟩ := parseFloatModelChars_props rs.toList g hg
      refine ⟨c0, cs0, hlist, ?_⟩
      rcases hc0 with rfl | rfl | rfl | rfl | hd
      · decide
      · decide
      · decide
      · decide
      · exact hdigit_safe c0 hd
    | _ => simp [renderValueInline] at hr
  | bool b =>
    cases tape with
    | bool =>
      cases b <;> simp [renderValueInline] at hr <;> subst hr <;>
        first
        | exact ⟨'f', ['a', 'l', 's', 'e'], rfl, by decide⟩
        | exact ⟨'t', ['r', 'u', 'e'], rfl, by decide⟩
    | _ => simp [renderValueInline] at hr
  | localDate d =>
    cases tape with
    | localDate =>
      simp only [renderValueInline] at hr
      obtain ⟨hdt, _, hhd⟩ := renderDate_localDate d rs hr
      cases hlist : rs.toList with
      | nil =>
        have h0 : rs = "" := by rw [← String.ofList_toList (s := rs), hlist]
        subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
      | cons c0 cs0 =>
        exact ⟨c0, cs0, rfl, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
    | _ => simp [renderValueInline] at hr
  | localTime t =>
    cases tape with
    | localTime fd =>
      simp only [renderValueInline] at hr
      obtain ⟨hdt, _, hhd⟩ := renderTime_localTime t fd rs hr
      cases hlist : rs.toList with
      | nil =>
        have h0 : rs = "" := by rw [← String.ofList_toList (s := rs), hlist]
        subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
      | cons c0 cs0 =>
        exact ⟨c0, cs0, rfl, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
    | _ => simp [renderValueInline] at hr
  | localDateTime dt =>
    cases tape with
    | localDateTime sep fd =>
      simp only [renderValueInline, bind, Option.bind] at hr
      cases hdr : renderDate dt.date with
      | none => simp [hdr] at hr
      | some ds =>
        cases htr : renderTime dt.time fd with
        | none => simp [hdr, htr] at hr
        | some ts =>
          simp only [hdr, htr, Option.some.injEq] at hr; subst hr
          obtain ⟨hdt, _, hhd⟩ := renderDate_localDate dt.date ds hdr
          cases hlist : ds.toList with
          | nil =>
            have h0 : ds = "" := by rw [← String.ofList_toList (s := ds), hlist]
            subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
          | cons c0 cs0 =>
            refine ⟨c0, cs0 ++ (renderDateTimeSep sep ++ ts).toList, ?_, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
            simp [String.toList_append, hlist, List.cons_append]
    | _ => simp [renderValueInline] at hr
  | offsetDateTime odt =>
    cases tape with
    | offsetDateTime sep oStyle fd =>
      simp only [renderValueInline, bind, Option.bind] at hr
      cases hdr : renderDate odt.dateTime.date with
      | none => simp [hdr] at hr
      | some ds =>
        cases htr : renderTime odt.dateTime.time fd with
        | none => simp [hdr, htr] at hr
        | some ts =>
          cases hor : renderOffset odt.offset oStyle with
          | none => simp [hdr, htr, hor] at hr
          | some os =>
            simp only [hdr, htr, hor, Option.some.injEq] at hr; subst hr
            obtain ⟨hdt, _, hhd⟩ := renderDate_localDate odt.dateTime.date ds hdr
            cases hlist : ds.toList with
            | nil =>
              have h0 : ds = "" := by rw [← String.ofList_toList (s := ds), hlist]
              subst h0; simp [parseDateTimeToken, hasDatePrefix, hasTimePrefix] at hdt
            | cons c0 cs0 =>
              refine ⟨c0, cs0 ++ (renderDateTimeSep sep ++ ts ++ os).toList, ?_, hdigit_safe c0 (hhd c0 cs0 hlist)⟩
              simp [String.toList_append, hlist, List.cons_append, List.append_assoc]
    | _ => simp [renderValueInline] at hr
  | array xs =>
    cases tape with
    | array elemTapes =>
      simp only [renderValueInline, bind, Option.bind] at hr
      cases hre : renderValueInline.renderArrayElems xs.toList elemTapes with
      | none => simp [hre] at hr
      | some strs =>
        simp only [hre, Option.some.injEq] at hr; subst hr
        refine ⟨'[', (String.intercalate ", " strs ++ "]").toList, ?_, by decide⟩
        simp [String.toList_append]
    | _ => simp [renderValueInline] at hr
  | table t =>
    cases tape with
    | inlineTable entryTapes =>
      simp only [renderValueInline, bind, Option.bind] at hr
      split at hr
      · simp at hr
      · cases hre : renderValueInline.renderInlineTableEntries t.toList entryTapes with
        | none => simp [hre] at hr
        | some kvs =>
          simp only [hre, Option.some.injEq] at hr; subst hr
          refine ⟨'{', (String.intercalate ", " kvs ++ "}").toList, ?_, by decide⟩
          simp [String.toList_append]
    | _ => simp [renderValueInline] at hr

mutual
  private theorem nodeToTomlValue_valueToInlineNode (v : TomlValue) :
      nodeToTomlValue (valueToInlineNode v) = v := by
    match v with
    | .table ⟨entries⟩ =>
      have hel := entriesToTomlList_inlineListToNodes entries
      simp [valueToInlineNode, nodeToTomlValue, hel]
    | .string _ | .int _ | .float _ | .bool _
    | .offsetDateTime _ | .localDateTime _ | .localDate _ | .localTime _ | .array _ => rfl
  termination_by sizeOf v

  private theorem entriesToTomlList_inlineListToNodes (entries : List (String × TomlValue)) :
      entriesToTomlList (inlineListToNodes entries) = entries := by
    match entries with
    | [] => rfl
    | (k, v) :: rest =>
      simp only [inlineListToNodes, entriesToTomlList]
      rw [nodeToTomlValue_valueToInlineNode v, entriesToTomlList_inlineListToNodes rest]
  termination_by sizeOf entries
end

private theorem lookupKeyList_filter_ne (k q : String) (l : List (String × TomlValue)) :
    lookupKeyList k (l.filter fun p => p.1 != k) = none ∧
    (q ≠ k → lookupKeyList q (l.filter fun p => p.1 != k) = lookupKeyList q l) := by
  induction l with
  | nil => simp [lookupKeyList]
  | cons p ps ih =>
    rcases p with ⟨pk, pv⟩
    refine ⟨?_, ?_⟩
    · by_cases hpk : pk == k
      · have hne : (pk != k) = false := by simp [bne, hpk]
        simp [List.filter, hne, ih.1]
      · have hne : (pk != k) = true := by simp [bne, hpk]
        have hkp : (k == pk) = false := by
          rw [Bool.eq_false_iff]; intro heq
          exact hpk (beq_iff_eq.mpr (beq_iff_eq.mp heq).symm)
        simp [List.filter, hne, lookupKeyList, hkp, ih.1]
    · intro hqk
      by_cases hpk : pk == k
      · have hpk' : pk = k := beq_iff_eq.mp hpk
        have hne : (pk != k) = false := by simp [bne, hpk]
        have hqp : (q == pk) = false := by
          rw [Bool.eq_false_iff]; intro heq
          exact hqk (by rw [beq_iff_eq.mp heq, hpk'])
        simp [List.filter, hne, lookupKeyList, hqp, ih.2 hqk]
      · have hne : (pk != k) = true := by simp [bne, hpk]
        simp only [List.filter, hne, lookupKeyList]
        split
        · rfl
        · exact ih.2 hqk

private theorem assocLookupNode_assocSetNode (k q : String) (n : Node) (acc : List (String × Node)) :
    assocLookupNode q (assocSetNode k n acc) = if q == k then some n else assocLookupNode q acc := by
  induction acc with
  | nil =>
    simp [assocSetNode, assocLookupNode]
  | cons p ps ih =>
    rcases p with ⟨pk, pn⟩
    simp only [assocSetNode]
    by_cases hkp : k == pk
    · have hpk : pk = k := (beq_iff_eq.mp hkp).symm
      subst hpk
      by_cases hqp : (q == pk) = true <;> simp [assocLookupNode, hqp]
    · have hqp : ∀ h : q == pk, (q == k) = false := by
        intro h
        rw [Bool.eq_false_iff]; intro hqk
        exact hkp (beq_iff_eq.mpr ((beq_iff_eq.mp hqk).symm.trans (beq_iff_eq.mp h)))
      simp only [hkp, Bool.false_eq_true, ↓reduceIte, assocLookupNode]
      by_cases hqp_b : q == pk
      · simp [hqp_b, hqp hqp_b]
      · simp [hqp_b, ih]

private theorem lookupKeyList_entriesToTomlList (q : String) (acc : List (String × Node)) :
    lookupKeyList q (entriesToTomlList acc) = (assocLookupNode q acc).map nodeToTomlValue := by
  induction acc with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨pk, pn⟩
    simp only [entriesToTomlList, lookupKeyList, assocLookupNode]
    by_cases h : (q == pk) = true <;> simp [h, ih]

private theorem lookupKeyList_mem {k : String} {v : TomlValue} {l : List (String × TomlValue)}
    (h : lookupKeyList k l = some v) : (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons p ps ih =>
    rcases p with ⟨pk, pv⟩
    simp only [lookupKeyList] at h
    split at h
    · rename_i heq
      have hkp : k = pk := beq_iff_eq.mp heq
      injection h with hv
      subst hkp; subst hv
      exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

private theorem sizeOf_lt_of_mem_array {x : TomlValue} {xs : Array TomlValue}
    (h : x ∈ xs.toList) : sizeOf x < sizeOf (TomlValue.array xs) := by
  cases xs with | mk l =>
  have hx : sizeOf x < sizeOf l := by
    have := List.sizeOf_lt_of_mem h
    omega
  have : sizeOf l < sizeOf (TomlValue.array ⟨l⟩) := by simp +arith
  omega

private theorem sizeOf_lt_of_mem_table {k : String} {v : TomlValue} {t : TomlTable}
    (h : (k, v) ∈ t.toList) : sizeOf v < sizeOf (TomlValue.table t) := by
  cases t with | mk l =>
  have hp : sizeOf (k, v) < sizeOf l := List.sizeOf_lt_of_mem h
  have hv : sizeOf v < sizeOf (k, v) := by simp +arith
  have ht : sizeOf l < sizeOf (TomlValue.table ⟨l⟩) := by simp +arith
  omega

private theorem tomlListEquiv_append_single {l1 l2 : List TomlValue} {x1 x2 : TomlValue}
    (hl : TomlListEquiv l1 l2) (hx : TomlEquiv x1 x2) :
    TomlListEquiv (l1 ++ [x1]) (l2 ++ [x2]) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [TomlListEquiv, hx]
    | cons _ _ => simp [TomlListEquiv] at hl
  | cons a xr ih =>
    cases l2 with
    | nil => simp [TomlListEquiv] at hl
    | cons b yr =>
      simp only [TomlListEquiv] at hl
      simp only [List.cons_append, TomlListEquiv]
      exact ⟨hl.1, ih hl.2⟩

private theorem renderKey_parseDottedKey_single (k : String) (ks : KeyStyle) (rk : String)
    (hr : renderKey k ks = some rk) (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hsw : ∃ c2 t2, skipHorizWs rest = c2 :: t2 ∧ c2 ≠ '.') :
    parseDottedKey (rk.toList ++ rest) = .ok ([k], skipHorizWs rest) := by
  unfold parseDottedKey
  have hlen : ∃ f, (rk.toList ++ rest).length + 1 = f + 1 := ⟨(rk.toList ++ rest).length, rfl⟩
  rcases hlen with ⟨f, hf⟩
  rw [hf]
  unfold parseDottedKeyFuel
  rw [(renderKey_parseKeySegment k ks rk hr rest hrest).1]
  simp only [bind, Except.bind]
  rcases hsw with ⟨c2, t2, hsw_eq, hne_dot⟩
  rw [hsw_eq]
  split
  · rename_i heq; injection heq with h1 _; exact absurd h1 hne_dot
  · rfl

private theorem renderArrayElems_parseArrayFuel (numApi : NumParseApi)
    (xs : List TomlValue) (tps : List ValueTape) (strs : List String)
    (harr : renderValueInline.renderArrayElems xs tps = some strs)
    (hVal : ∀ x ∈ xs, ∀ tp rs, renderValueInline x tp = some rs →
      ∀ rest fuel, fuel ≥ rs.toList.length →
      (∀ c r, rest = c :: r →
        isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
      ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
        TomlEquiv x v' ∧
        (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true)
    (origPrefix revAcc : List TomlValue)
    (hacc : TomlListEquiv origPrefix revAcc.reverse)
    (rest : List Char) (fuel : Nat)
    (hf : fuel ≥ (String.intercalate ", " strs ++ "]").toList.length) :
    ∃ ys, parseArrayFuel numApi fuel ((String.intercalate ", " strs ++ "]").toList ++ rest) revAcc =
        .ok (.array ys, rest) ∧
      TomlListEquiv (origPrefix ++ xs) ys.toList ∧
      ((String.intercalate ", " strs ++ "]").toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction xs generalizing tps strs origPrefix revAcc fuel with
  | nil =>
    cases tps with
    | nil =>
      simp only [renderValueInline.renderArrayElems, Option.some.injEq] at harr
      subst harr
      cases fuel with
      | zero => simp at hf
      | succ f =>
        have hst : skipTriviaNewlines (']' :: rest) = ']' :: rest :=
          skipTriviaNewlines_cons_of_safe ']' rest (by decide) (by decide) (by decide)
        refine ⟨revAcc.reverse.toArray, ?_, ?_, by decide⟩
        · simp [String.intercalate_nil, parseArrayFuel, hst]
        · simpa using hacc
    | cons _ _ => simp [renderValueInline.renderArrayElems] at harr
  | cons x xr ih =>
    cases tps with
    | nil => simp [renderValueInline.renderArrayElems] at harr
    | cons tp tpr =>
      simp only [renderValueInline.renderArrayElems, bind, Option.bind] at harr
      cases hx : renderValueInline x tp with
      | none => simp [hx] at harr
      | some sx =>
        cases hxr : renderValueInline.renderArrayElems xr tpr with
        | none => simp [hx, hxr] at harr
        | some sr =>
          simp only [hx, hxr, Option.some.injEq] at harr
          subst harr
          obtain ⟨c0, cs0, hsx_list, hws0, hn0, _, hc0, hbr0, _, _⟩ := renderValueInline_headSafe x tp sx hx
          let tailStr := match sr with | [] => "]" | _ :: _ => ", " ++ String.intercalate ", " sr ++ "]"
          let tailRest := tailStr.toList ++ rest
          have hinterc : (String.intercalate ", " (sx :: sr) ++ "]").toList = sx.toList ++ tailStr.toList := by
            cases sr with
            | nil => simp [tailStr, String.intercalate_singleton, String.toList_append]
            | cons s2 sr2 =>
              simp [tailStr, String.intercalate_cons_cons, String.toList_append, String.append_assoc]
          have htail_delim : ∀ c r, tailRest = c :: r →
              isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false) := by
            intro c r hc
            cases hsr : sr with
            | nil =>
              have hc' : ']' :: rest = c :: r := by simpa [tailRest, tailStr, hsr] using hc
              injection hc' with hcb _
              subst hcb; exact ⟨by decide, fun h => by cases h⟩
            | cons s2 sr2 =>
              have hc' : ',' :: ' ' :: (String.intercalate ", " (s2 :: sr2) ++ "]").toList ++ rest = c :: r := by
                simpa [tailRest, tailStr, hsr, String.toList_append, List.cons_append, List.append_assoc] using hc
              injection hc' with hcb _
              subst hcb; exact ⟨by decide, fun h => by cases h⟩
          have htail_len : tailStr.toList.length ≥ 1 := by
            cases sr <;> simp [tailStr, String.toList_append] <;> omega
          have hf_pos : ∃ f, fuel = f + 1 ∧ f ≥ sx.toList.length := by
            cases fuel with
            | zero => rw [hinterc, List.length_append] at hf; omega
            | succ f =>
              refine ⟨f, rfl, ?_⟩
              rw [hinterc, List.length_append] at hf
              omega
          rcases hf_pos with ⟨f, rfl, hf_x⟩
          obtain ⟨v', hpv, heqv, hcl_x⟩ := hVal x (by simp) tp sx hx tailRest f hf_x htail_delim
          have hskip1 : skipTriviaNewlines (sx.toList ++ tailRest) = sx.toList ++ tailRest := by
            rw [hsx_list, List.cons_append]
            exact skipTriviaNewlines_cons_of_safe c0 (cs0 ++ tailRest) hws0 hn0 hc0
          have hnot_nil : sx.toList ++ tailRest ≠ [] := by
            rw [hsx_list]; simp
          have hnot_rbr : ∀ r, sx.toList ++ tailRest ≠ ']' :: r := by
            intro r heq; rw [hsx_list, List.cons_append] at heq
            injection heq with h1 _; exact hbr0 h1
          have hstep : parseArrayFuel numApi (f + 1) ((String.intercalate ", " (sx :: sr) ++ "]").toList ++ rest) revAcc =
              (match skipTriviaNewlines tailRest with
               | ',' :: afterComma => parseArrayFuel numApi f afterComma (v' :: revAcc)
               | ']' :: afterClose => .ok (.array (v' :: revAcc).reverse.toArray, afterClose)
               | _ => .error (mkErr .parseError "expected ',' or ']' in TOML array")) := by
            rw [hinterc, List.append_assoc]
            conv => lhs; unfold parseArrayFuel
            rw [hskip1]
            split
            · rename_i heq; exact absurd heq (hnot_rbr _)
            · rename_i heq; exact absurd heq hnot_nil
            · simp only [hpv, bind, Except.bind]; rfl
          cases hsr : sr with
          | nil =>
            have hxr_nil : xr = [] := by
              cases xr with
              | nil => rfl
              | cons y yr =>
                cases tpr with
                | nil => simp [renderValueInline.renderArrayElems] at hxr
                | cons yt ytr =>
                  simp only [renderValueInline.renderArrayElems, bind, Option.bind] at hxr
                  cases hry : renderValueInline y yt with
                  | none => simp [hry] at hxr
                  | some sy =>
                    cases hrrest : renderValueInline.renderArrayElems yr ytr with
                    | none => simp [hry, hrrest] at hxr
                    | some syr => simp [hry, hrrest, hsr] at hxr
            subst hxr_nil
            have htail_eq : tailRest = ']' :: rest := by simp [tailRest, tailStr, hsr]
            have hskip2 : skipTriviaNewlines tailRest = ']' :: rest := by
              rw [htail_eq]
              exact skipTriviaNewlines_cons_of_safe ']' rest (by decide) (by decide) (by decide)
            refine ⟨(v' :: revAcc).reverse.toArray, ?_, ?_, ?_⟩
            · rw [← hsr, hstep, hskip2]; rfl
            · simp only [List.reverse_cons]
              exact tomlListEquiv_append_single hacc heqv
            · rw [← hsr, hinterc, List.all_append]
              exact Bool.and_eq_true_iff.mpr ⟨hcl_x, by simp [tailStr, hsr]; decide⟩
          | cons s2 sr2 =>
            have htail_eq : tailRest = ',' :: ' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest) := by
              simp [tailRest, tailStr, hsr, String.toList_append, List.cons_append, List.append_assoc]
            have hskip2 : skipTriviaNewlines tailRest = ',' :: ' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest) := by
              rw [htail_eq]
              exact skipTriviaNewlines_cons_of_safe ',' _ (by decide) (by decide) (by decide)
            have hf_rec : f ≥ (String.intercalate ", " sr ++ "]").toList.length := by
              have hsx_len : sx.toList.length ≥ 1 := by rw [hsx_list]; simp
              rw [hinterc, List.length_append] at hf
              simp only [tailStr, hsr, String.toList_append, List.length_append] at hf ⊢
              have h2 : (", " : String).toList.length = 2 := rfl
              omega
            have hVal' : ∀ y ∈ xr, ∀ tp' rs', renderValueInline y tp' = some rs' →
                ∀ rest' fuel', fuel' ≥ rs'.toList.length →
                (∀ c r, rest' = c :: r →
                  isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
                ∃ v', parseValueFuel numApi fuel' (rs'.toList ++ rest') = .ok (v', rest') ∧
                  TomlEquiv y v' ∧ (rs'.toList.all fun c => !isDisallowedControl c && c != '\r') = true :=
              fun y hy => hVal y (by simp [hy])
            have hxr_clean : renderValueInline.renderArrayElems xr tpr = some sr := by simpa [hsr] using hxr
            have hacc' : TomlListEquiv (origPrefix ++ [x]) (v' :: revAcc).reverse := by
              simp only [List.reverse_cons]
              exact tomlListEquiv_append_single hacc heqv
            obtain ⟨ys, hys_parse, hys_eqv, hys_cl⟩ :=
              ih tpr sr hxr_clean hVal' (origPrefix ++ [x]) (v' :: revAcc) hacc' f hf_rec
            refine ⟨ys, ?_, ?_, ?_⟩
            · rw [← hsr, hstep, hskip2]
              have hred : (match ',' :: ' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest) with
                  | ',' :: afterComma => parseArrayFuel numApi f afterComma (v' :: revAcc)
                  | ']' :: afterClose => .ok (.array (v' :: revAcc).reverse.toArray, afterClose)
                  | _ => .error (mkErr .parseError "expected ',' or ']' in TOML array")) =
                  parseArrayFuel numApi f (' ' :: ((String.intercalate ", " sr ++ "]").toList ++ rest)) (v' :: revAcc) := rfl
              rw [hred, parseArrayFuel_skip_space]
              exact hys_parse
            · simpa [List.append_assoc] using hys_eqv
            · rw [← hsr, hinterc, List.all_append]
              refine Bool.and_eq_true_iff.mpr ⟨hcl_x, ?_⟩
              simp only [tailStr, hsr]
              rw [String.append_assoc, String.toList_append, List.all_append]
              refine Bool.and_eq_true_iff.mpr ⟨by decide, ?_⟩
              simpa [hsr] using hys_cl

private theorem parseInlineTableFuel_step (numApi : NumParseApi) (f : Nat)
    (cs : List Char) (acc : List (String × Node))
    (k : String) (r1 r3 r5 : List Char) (v : TomlValue) (nextEntries : List (String × Node))
    (hdk : parseDottedKey (skipHorizWs cs) = .ok ([k], r1))
    (hr2 : skipHorizWs r1 = '=' :: r3)
    (hpv : parseValueFuel numApi f (skipHorizWs r3) = .ok (v, r5))
    (hins : insertDottedEntries [k] acc [k] (valueToInlineNode v) = .ok nextEntries) :
    parseInlineTableFuel numApi (f + 1) cs acc =
      (match skipHorizWs r5 with
       | ',' :: afterComma =>
         match skipHorizWs afterComma with
         | '}' :: _ => .error (mkErr .parseError "trailing comma is not allowed in inline table")
         | nextCs => parseInlineTableFuel numApi f nextCs nextEntries
       | '}' :: afterClose => .ok (.table (entriesToTomlList nextEntries).toArray, afterClose)
       | _ => .error (mkErr .parseError "expected ',' or '}' in inline table")) := by
  conv =>
    lhs
    unfold parseInlineTableFuel
    simp only [hdk, bind, Except.bind, hr2, hpv, hins]
  rfl

private theorem renderInlineTableEntries_parseInlineTableFuel (numApi : NumParseApi)
    (origEntries rem : List (String × TomlValue))
    (entryTapes : List (String × KeyStyle × ValueTape)) (kvs : List String)
    (hrem_sub : ∀ q v, lookupKeyList q rem = some v → lookupKeyList q origEntries = some v)
    (htab : renderValueInline.renderInlineTableEntries rem entryTapes = some kvs)
    (hne : entryTapes ≠ [])
    (hVal : ∀ q v, lookupKeyList q origEntries = some v → ∀ tp rs, renderValueInline v tp = some rs →
      ∀ rest fuel, fuel ≥ rs.toList.length →
      (∀ c r, rest = c :: r →
        isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
      ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
        TomlEquiv v v' ∧
        (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true)
    (acc : List (String × Node))
    (h1 : ∀ q, lookupKeyList q origEntries = none → assocLookupNode q acc = none)
    (h2 : ∀ q v, lookupKeyList q rem = some v → assocLookupNode q acc = none)
    (h3 : ∀ q v1, lookupKeyList q origEntries = some v1 → lookupKeyList q rem = none →
      ∃ v2, lookupKeyList q (entriesToTomlList acc) = some v2 ∧ TomlEquiv v1 v2)
    (rest : List Char) (fuel : Nat)
    (hf : fuel ≥ (String.intercalate ", " kvs ++ "}").toList.length) :
    ∃ resT, parseInlineTableFuel numApi fuel ((String.intercalate ", " kvs ++ "}").toList ++ rest) acc =
        .ok (.table resT, rest) ∧
      TomlTableEquivList origEntries resT.toList ∧
      ((String.intercalate ", " kvs ++ "}").toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction entryTapes generalizing rem kvs acc fuel with
  | nil => exact absurd rfl hne
  | cons entry restTapes ih =>
    rcases entry with ⟨k, ks, vt⟩
    simp only [renderValueInline.renderInlineTableEntries] at htab
    cases hlk : lookupKeyList k rem with
    | none => simp [hlk] at htab
    | some v =>
      simp only [hlk, bind, Option.bind] at htab
      cases hrk : renderKey k ks with
      | none => simp [hrk] at htab
      | some rk =>
        cases hrv : renderValueInline v vt with
        | none => simp [hrk, hrv] at htab
        | some rv =>
          cases htail : renderValueInline.renderInlineTableEntries (rem.filter fun p => p.1 != k) restTapes with
          | none => simp [hrk, hrv, htail] at htab
          | some tailKvs =>
            simp only [hrk, hrv, htail, Option.some.injEq] at htab
            subst htab
            let rem' := rem.filter (fun p => p.1 != k)
            change renderValueInline.renderInlineTableEntries rem' restTapes = some tailKvs at htail
            obtain ⟨ck0, csk0, hrk_list, hkws0, _, _, _, _, _, _⟩ := renderKey_headSafe k ks rk hrk
            obtain ⟨cv0, csv0, hrv_list, hvws0, _, _, _, _, _, _⟩ := renderValueInline_headSafe v vt rv hrv
            let tailStr := match tailKvs with | [] => "}" | _ :: _ => ", " ++ String.intercalate ", " tailKvs ++ "}"
            let afterRv := tailStr.toList ++ rest
            have hinterc : (String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList =
                rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ tailStr.toList)) := by
              cases tailKvs with
              | nil => simp [tailStr, String.intercalate_singleton, String.toList_append, List.append_assoc]
              | cons kv2 kvr2 =>
                simp [tailStr, String.intercalate_cons_cons, String.toList_append, List.append_assoc]
            have hinterc_rest : (String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList ++ rest =
                rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv)) := by
              rw [hinterc]
              simp only [afterRv, List.append_assoc, List.cons_append]
            have hafter_delim : ∀ c r, afterRv = c :: r →
                isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false) := by
              intro c r hc
              cases htk : tailKvs with
              | nil =>
                simp only [afterRv, tailStr, htk] at hc
                injection hc with hcb _
                subst hcb; exact ⟨by decide, fun h => by cases h⟩
              | cons kv2 kvr2 =>
                have hc_list : ',' :: ' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest) = c :: r := by
                  simpa [afterRv, tailStr, htk, String.toList_append, List.cons_append, List.append_assoc] using hc
                injection hc_list with hcb _
                subst hcb; exact ⟨by decide, fun h => by cases h⟩
            have hf_pos : ∃ f, fuel = f + 1 ∧ f ≥ rv.toList.length := by
              cases fuel with
              | zero =>
                rw [hinterc] at hf
                simp at hf
              | succ f =>
                refine ⟨f, rfl, ?_⟩
                rw [hinterc, List.length_append] at hf
                simp only [List.length_cons, List.length_append] at hf
                omega
            rcases hf_pos with ⟨f, rfl, hf_v⟩
            have hv_orig : lookupKeyList k origEntries = some v := hrem_sub k v hlk
            obtain ⟨v', hpv, heqv, hcl_v⟩ := hVal k v hv_orig vt rv hrv afterRv f hf_v hafter_delim
            have hcl_k := (renderKey_parseKeySegment k ks rk hrk (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv)) (by
              intro c tail h; injection h with hc _; subst hc; decide)).2
            have hcl_k' : (rk.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
              simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl_k ⊢
              intro c hc
              exact ⟨(hcl_k c hc).1.1, (hcl_k c hc).1.2⟩
            have hcs1 : skipHorizWs ((String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList ++ rest) =
                rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv)) := by
              rw [hinterc_rest, hrk_list, List.cons_append]
              exact skipHorizWs_cons_of_false ck0 _ hkws0
            have hdk : parseDottedKey (rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv))) =
                .ok ([k], '=' :: ' ' :: (rv.toList ++ afterRv)) := by
              have hdk' := renderKey_parseDottedKey_single k ks rk hrk
                (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv))
                (fun c tail h => by injection h with hc _; subst hc; decide)
                ⟨'=', ' ' :: (rv.toList ++ afterRv), by simp [skipHorizWs, isHorizWs], by decide⟩
              simpa [skipHorizWs, isHorizWs] using hdk'
            have hr2 : skipHorizWs ('=' :: ' ' :: (rv.toList ++ afterRv)) = '=' :: ' ' :: (rv.toList ++ afterRv) :=
              skipHorizWs_cons_of_false '=' _ (by decide)
            have hr4 : skipHorizWs (' ' :: (rv.toList ++ afterRv)) = rv.toList ++ afterRv := by
              rw [skipHorizWs_space, hrv_list]
              exact skipHorizWs_cons_of_false cv0 _ hvws0
            have hins : insertDottedEntries [k] acc [k] (valueToInlineNode v') =
                .ok (assocSetNode k (valueToInlineNode v') acc) := by
              simp [insertDottedEntries, h2 k v hlk]
            have hr6 : skipHorizWs afterRv = afterRv := by
              cases htk : tailKvs <;> simp only [afterRv, tailStr, htk, String.toList_append]
              · exact skipHorizWs_cons_of_false '}' _ (by decide)
              · exact skipHorizWs_cons_of_false ',' _ (by decide)
            have h1' : ∀ q, lookupKeyList q origEntries = none →
                assocLookupNode q (assocSetNode k (valueToInlineNode v') acc) = none := by
              intro q hq
              rw [assocLookupNode_assocSetNode]
              by_cases hqk : q == k
              · have : q = k := beq_iff_eq.mp hqk
                subst this; rw [hv_orig] at hq; cases hq
              · simp [hqk, h1 q hq]
            have h2' : ∀ q w, lookupKeyList q rem' = some w →
                assocLookupNode q (assocSetNode k (valueToInlineNode v') acc) = none := by
              intro q w hqw
              have hne_k : q ≠ k := by
                intro heq; subst heq
                rw [(lookupKeyList_filter_ne q q rem).1] at hqw; cases hqw
              have hqw_rem : lookupKeyList q rem = some w := by
                rwa [(lookupKeyList_filter_ne k q rem).2 hne_k] at hqw
              rw [assocLookupNode_assocSetNode]
              have hqb : (q == k) = false := beq_false_of_ne hne_k
              simp [hqb, h2 q w hqw_rem]
            have h3' : ∀ q v1, lookupKeyList q origEntries = some v1 → lookupKeyList q rem' = none →
                ∃ v2, lookupKeyList q (entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)) = some v2 ∧
                  TomlEquiv v1 v2 := by
              intro q v1 hqo hqr
              by_cases hqk : q = k
              · subst hqk
                have hv1_eq : v1 = v := by
                  rw [hv_orig] at hqo
                  injection hqo with hveq
                  exact hveq.symm
                subst hv1_eq
                refine ⟨v', ?_, heqv⟩
                rw [lookupKeyList_entriesToTomlList, assocLookupNode_assocSetNode]
                simp [nodeToTomlValue_valueToInlineNode]
              · have hqr_rem : lookupKeyList q rem = none := by
                  rwa [(lookupKeyList_filter_ne k q rem).2 hqk] at hqr
                obtain ⟨v2, hv2, heqv2⟩ := h3 q v1 hqo hqr_rem
                refine ⟨v2, ?_, heqv2⟩
                rw [lookupKeyList_entriesToTomlList, assocLookupNode_assocSetNode]
                have hqb : (q == k) = false := beq_false_of_ne hqk
                simp only [hqb, Bool.false_eq_true, ↓reduceIte]
                rwa [lookupKeyList_entriesToTomlList] at hv2
            cases hrestT : restTapes with
            | nil =>
              have hrem'_nil : rem' = [] := by
                simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail
                split at htail
                · rename_i hempty; exact List.isEmpty_iff.mp hempty
                · cases htail
              have htailKvs_nil : tailKvs = [] := by
                simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail
                split at htail
                · injection htail with h; exact h.symm
                · cases htail
              have hafter_eq : afterRv = '}' :: rest := by simp [afterRv, tailStr, htailKvs_nil]
              have hteq : TomlTableEquivList origEntries (entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)) := by
                unfold TomlTableEquivList
                refine ⟨?_, ?_⟩
                · intro q hq
                  rw [lookupKeyList_entriesToTomlList, h1' q hq]; rfl
                · intro q v1 hq
                  have hqr : lookupKeyList q rem' = none := by simp [hrem'_nil, lookupKeyList]
                  exact h3' q v1 hq hqr
              refine ⟨(entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)).toArray, ?_, ?_, ?_⟩
              · rw [parseInlineTableFuel_step numApi f _ acc k _ _ _ v' _ (by rw [hcs1]; exact hdk) hr2
                    (by rw [show skipHorizWs (' ' :: (rv.toList ++ afterRv)) = rv.toList ++ afterRv from hr4]; exact hpv) hins,
                  hr6, hafter_eq]
                rfl
              · simpa using hteq
              · rw [hinterc, List.all_append]
                refine Bool.and_eq_true_iff.mpr ⟨hcl_k', ?_⟩
                simp only [List.all_cons, Bool.and_eq_true, List.all_append, tailStr, htailKvs_nil]
                exact ⟨by decide, by decide, by decide, hcl_v, by decide⟩
            | cons e2 er2 =>
              have htailKvs_ne : tailKvs ≠ [] := by
                intro hnil; subst hnil
                rcases e2 with ⟨k2, ks2, vt2⟩
                simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail
                cases hlk2 : lookupKeyList k2 rem' with
                | none => simp [hlk2] at htail
                | some v2 =>
                  simp only [hlk2, bind, Option.bind] at htail
                  cases hrk2 : renderKey k2 ks2 with
                  | none => simp [hrk2] at htail
                  | some rk2 =>
                    cases hrv2 : renderValueInline v2 vt2 with
                    | none => simp [hrk2, hrv2] at htail
                    | some rv2 =>
                      cases htl2 : renderValueInline.renderInlineTableEntries (rem'.filter fun p => p.1 != k2) er2 <;>
                        simp [hrk2, hrv2, htl2] at htail
              cases htk_eq : tailKvs with
              | nil => exact absurd htk_eq htailKvs_ne
              | cons kv2 kvr2 =>
                have htail' : renderValueInline.renderInlineTableEntries rem' restTapes = some (kv2 :: kvr2) := by
                  simpa [htk_eq] using htail
                have hk2_head : ∃ c_hd cs_hd, (String.intercalate ", " (kv2 :: kvr2) ++ "}").toList = c_hd :: cs_hd ∧
                    isHorizWs c_hd = false ∧ c_hd ≠ '}' := by
                  rcases e2 with ⟨k2, ks2, vt2⟩
                  simp only [renderValueInline.renderInlineTableEntries, hrestT] at htail'
                  cases hlk2 : lookupKeyList k2 rem' with
                  | none => simp [hlk2] at htail'
                  | some v2 =>
                    simp only [hlk2, bind, Option.bind] at htail'
                    cases hrk2 : renderKey k2 ks2 with
                    | none => simp [hrk2] at htail'
                    | some rk2 =>
                      cases hrv2 : renderValueInline v2 vt2 with
                      | none => simp [hrk2, hrv2] at htail'
                      | some rv2 =>
                        cases htl2 : renderValueInline.renderInlineTableEntries (rem'.filter fun p => p.1 != k2) er2 with
                        | none => simp [hrk2, hrv2, htl2] at htail'
                        | some tail2 =>
                          simp only [hrk2, hrv2, htl2, Option.some.injEq] at htail'
                          have hkv2 : kv2 = rk2 ++ " = " ++ rv2 := by
                            injection htail' with h1 _
                            exact h1.symm
                          obtain ⟨ck2, csk2, hrk2_list, hkws2, _, _, _, hbr2, _, _⟩ := renderKey_headSafe k2 ks2 rk2 hrk2
                          cases kvr2 with
                          | nil =>
                            refine ⟨ck2, csk2 ++ (" = " ++ rv2 ++ "}").toList, ?_, hkws2, hbr2⟩
                            simp [hkv2, String.intercalate_singleton, String.toList_append, hrk2_list, List.cons_append, List.append_assoc]
                          | cons kv3 kvr3 =>
                            refine ⟨ck2, csk2 ++ (" = " ++ rv2 ++ ", " ++ String.intercalate ", " (kv3 :: kvr3) ++ "}").toList, ?_, hkws2, hbr2⟩
                            simp [hkv2, String.intercalate_cons_cons, String.toList_append, hrk2_list, List.cons_append, List.append_assoc]
                rcases hk2_head with ⟨c_hd, cs_hd, hhd_list, hhd_ws, hhd_br⟩
                have hafter_eq : afterRv = ',' :: ' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest) := by
                  simp [afterRv, tailStr, htk_eq, String.toList_append, List.cons_append, List.append_assoc]
                have hskip_ac : skipHorizWs (' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest)) =
                    (String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest := by
                  rw [skipHorizWs_space, hhd_list, List.cons_append]
                  exact skipHorizWs_cons_of_false c_hd _ hhd_ws
                have hrem'_sub : ∀ q w, lookupKeyList q rem' = some w → lookupKeyList q origEntries = some w := by
                  intro q w hqw
                  have hne_k : q ≠ k := by
                    intro heq; subst heq
                    rw [(lookupKeyList_filter_ne q q rem).1] at hqw; cases hqw
                  exact hrem_sub q w (by rwa [(lookupKeyList_filter_ne k q rem).2 hne_k] at hqw)
                have hf_rec : f ≥ (String.intercalate ", " (kv2 :: kvr2) ++ "}").toList.length := by
                  rw [hinterc, List.length_append] at hf
                  simp only [tailStr, htk_eq, String.toList_append, List.length_cons, List.length_append] at hf ⊢
                  have hrk_len : rk.toList.length ≥ 1 := by rw [hrk_list]; simp
                  have hrv_len : rv.toList.length ≥ 1 := by rw [hrv_list]; simp
                  have h2 : (", " : String).toList.length = 2 := rfl
                  omega
                have hne' : restTapes ≠ [] := by rw [hrestT]; simp
                obtain ⟨resT, hres_parse, hres_eqv, hres_cl⟩ :=
                  ih rem' (kv2 :: kvr2) hrem'_sub htail' hne' (assocSetNode k (valueToInlineNode v') acc)
                    h1' h2' h3' f hf_rec
                refine ⟨resT, ?_, hres_eqv, ?_⟩
                · rw [← htk_eq, parseInlineTableFuel_step numApi f _ acc k _ _ _ v' _ (by rw [hcs1]; exact hdk) hr2
                      (by rw [show skipHorizWs (' ' :: (rv.toList ++ afterRv)) = rv.toList ++ afterRv from hr4]; exact hpv) hins,
                    hr6, hafter_eq]
                  have hred : (match ',' :: ' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest) with
                      | ',' :: afterComma =>
                        match skipHorizWs afterComma with
                        | '}' :: _ => Except.error (mkErr .parseError "trailing comma is not allowed in inline table")
                        | nextCs => parseInlineTableFuel numApi f nextCs (assocSetNode k (valueToInlineNode v') acc)
                      | '}' :: afterClose => Except.ok (.table (entriesToTomlList (assocSetNode k (valueToInlineNode v') acc)).toArray, afterClose)
                      | _ => Except.error (mkErr .parseError "expected ',' or '}' in inline table")) =
                      (match skipHorizWs (' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest)) with
                       | '}' :: _ => Except.error (mkErr .parseError "trailing comma is not allowed in inline table")
                       | nextCs => parseInlineTableFuel numApi f nextCs (assocSetNode k (valueToInlineNode v') acc)) := rfl
                  rw [hred, hskip_ac, hhd_list, List.cons_append]
                  split
                  · rename_i heq; injection heq with h1 _; exact absurd h1 hhd_br
                  · rw [← List.cons_append, ← hhd_list]
                    exact hres_parse
                · rw [← htk_eq, hinterc, List.all_append]
                  refine Bool.and_eq_true_iff.mpr ⟨hcl_k', ?_⟩
                  simp only [List.all_cons, Bool.and_eq_true, List.all_append]
                  refine ⟨by decide, by decide, by decide, hcl_v, ?_⟩
                  simp only [tailStr, htk_eq]
                  rw [String.append_assoc, String.toList_append, List.all_append]
                  refine Bool.and_eq_true_iff.mpr ⟨by decide, ?_⟩
                  exact hres_cl

private theorem renderValueInline_parseValueFuel (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (v : TomlValue) (tape : ValueTape) (rs : String) (hr : renderValueInline v tape = some rs)
    (rest : List Char) (fuel : Nat) (hf : fuel ≥ rs.toList.length)
    (hrest : ∀ c r, rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) :
    ∃ v', parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest) ∧
      TomlEquiv v v' ∧
      (rs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction n0 : sizeOf v using Nat.strongRecOn generalizing v tape rs rest fuel with
  | ind len ih =>
    cases v with
    | array xs =>
      cases tape with
      | array elemTapes =>
        simp only [renderValueInline, bind, Option.bind] at hr
        cases hre : renderValueInline.renderArrayElems xs.toList elemTapes with
        | none => simp [hre] at hr
        | some strs =>
          simp only [hre, Option.some.injEq] at hr; subst hr
          have hrs_list : ("[" ++ String.intercalate ", " strs ++ "]").toList =
              '[' :: ((String.intercalate ", " strs ++ "]").toList) := by
            simp [String.toList_append]
          cases fuel with
          | zero => simp [hrs_list] at hf
          | succ f =>
            have hf_arr : f ≥ (String.intercalate ", " strs ++ "]").toList.length := by
              rw [hrs_list, List.length_cons] at hf; omega
            have hVal : ∀ x ∈ xs.toList, ∀ tp rs', renderValueInline x tp = some rs' →
                ∀ rest' fuel', fuel' ≥ rs'.toList.length →
                (∀ c r, rest' = c :: r →
                  isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
                ∃ v', parseValueFuel numApi fuel' (rs'.toList ++ rest') = .ok (v', rest') ∧
                  TomlEquiv x v' ∧ (rs'.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
              intro x hx tp rs' hrx rest' fuel' hfx hrest'
              have hlt : sizeOf x < len := by
                rw [← n0]; exact sizeOf_lt_of_mem_array hx
              exact ih (sizeOf x) hlt x tp rs' hrx rest' fuel' hfx hrest' rfl
            obtain ⟨ys, hys_parse, hys_eqv, hys_cl⟩ :=
              renderArrayElems_parseArrayFuel numApi xs.toList elemTapes strs hre hVal [] []
                (by simp [TomlListEquiv]) rest f hf_arr
            refine ⟨.array ys, ?_, ?_, ?_⟩
            · rw [hrs_list, List.cons_append]
              conv => lhs; unfold parseValueFuel
              exact hys_parse
            · simpa [TomlEquiv] using hys_eqv
            · rw [hrs_list, List.all_cons]
              exact Bool.and_eq_true_iff.mpr ⟨by decide, hys_cl⟩
      | _ => simp [renderValueInline] at hr
    | table t =>
      cases tape with
      | inlineTable entryTapes =>
        simp only [renderValueInline, bind, Option.bind] at hr
        split at hr
        · simp at hr
        · rename_i hnd
          cases hre : renderValueInline.renderInlineTableEntries t.toList entryTapes with
          | none => simp [hre] at hr
          | some kvs =>
            simp only [hre, Option.some.injEq] at hr; subst hr
            have hrs_list : ("{" ++ String.intercalate ", " kvs ++ "}").toList =
                '{' :: ((String.intercalate ", " kvs ++ "}").toList) := by
              simp [String.toList_append]
            cases fuel with
            | zero => simp [hrs_list] at hf
            | succ f =>
              cases entryTapes with
              | nil =>
                have ht_empty : t.toList = [] := by
                  simp only [renderValueInline.renderInlineTableEntries] at hre
                  split at hre
                  · rename_i hempty; exact List.isEmpty_iff.mp hempty
                  · cases hre
                have hkvs_nil : kvs = [] := by
                  simp only [renderValueInline.renderInlineTableEntries, ht_empty] at hre
                  simpa using hre.symm
                have hparse : parseValueFuel numApi (f + 1) (("{" ++ String.intercalate ", " kvs ++ "}").toList ++ rest) =
                    .ok (.table #[], rest) := by
                  simp [hkvs_nil, String.intercalate_nil, parseValueFuel, skipHorizWs_cons_of_false '}' rest (by decide)]
                have heqv : TomlEquiv (.table t) (.table #[]) := by
                  simp [TomlEquiv, TomlTableEquivList, ht_empty, lookupKeyList]
                refine ⟨.table #[], hparse, heqv, by simp [hkvs_nil, String.intercalate_nil]; decide⟩
              | cons e0 er0 =>
                have hkvs_ne : kvs ≠ [] := by
                  intro hnil; subst hnil
                  rcases e0 with ⟨k0, ks0, vt0⟩
                  simp only [renderValueInline.renderInlineTableEntries] at hre
                  cases hlk0 : lookupKeyList k0 t.toList with
                  | none => simp [hlk0] at hre
                  | some v0 =>
                    simp only [hlk0, bind, Option.bind] at hre
                    cases hrk0 : renderKey k0 ks0 with
                    | none => simp [hrk0] at hre
                    | some rk0 =>
                      cases hrv0 : renderValueInline v0 vt0 with
                      | none => simp [hrk0, hrv0] at hre
                      | some rv0 =>
                        cases htl0 : renderValueInline.renderInlineTableEntries (t.toList.filter fun p => p.1 != k0) er0 <;>
                          simp [hrk0, hrv0, htl0] at hre
                cases hkvs_eq : kvs with
                | nil => exact absurd hkvs_eq hkvs_ne
                | cons kv0 kvr0 =>
                  have hre' : renderValueInline.renderInlineTableEntries t.toList (e0 :: er0) = some (kv0 :: kvr0) := by
                    simpa [hkvs_eq] using hre
                  have hhd : ∃ c_hd cs_hd, (String.intercalate ", " (kv0 :: kvr0) ++ "}").toList = c_hd :: cs_hd ∧
                      isHorizWs c_hd = false ∧ c_hd ≠ '}' := by
                    rcases e0 with ⟨k0, ks0, vt0⟩
                    simp only [renderValueInline.renderInlineTableEntries] at hre'
                    cases hlk0 : lookupKeyList k0 t.toList with
                    | none => simp [hlk0] at hre'
                    | some v0 =>
                      simp only [hlk0, bind, Option.bind] at hre'
                      cases hrk0 : renderKey k0 ks0 with
                      | none => simp [hrk0] at hre'
                      | some rk0 =>
                        cases hrv0 : renderValueInline v0 vt0 with
                        | none => simp [hrk0, hrv0] at hre'
                        | some rv0 =>
                          cases htl0 : renderValueInline.renderInlineTableEntries (t.toList.filter fun p => p.1 != k0) er0 with
                          | none => simp [hrk0, hrv0, htl0] at hre'
                          | some tail0 =>
                            simp only [hrk0, hrv0, htl0, Option.some.injEq] at hre'
                            have hkv0 : kv0 = rk0 ++ " = " ++ rv0 := by
                              injection hre' with h1 _
                              exact h1.symm
                            obtain ⟨ck0, csk0, hrk0_list, hkws0, _, _, _, hbr0, _, _⟩ := renderKey_headSafe k0 ks0 rk0 hrk0
                            cases kvr0 with
                            | nil =>
                              refine ⟨ck0, csk0 ++ (" = " ++ rv0 ++ "}").toList, ?_, hkws0, hbr0⟩
                              simp [hkv0, String.intercalate_singleton, String.toList_append, hrk0_list, List.cons_append, List.append_assoc]
                            | cons kv1 kvr1 =>
                              refine ⟨ck0, csk0 ++ (" = " ++ rv0 ++ ", " ++ String.intercalate ", " (kv1 :: kvr1) ++ "}").toList, ?_, hkws0, hbr0⟩
                              simp [hkv0, String.intercalate_cons_cons, String.toList_append, hrk0_list, List.cons_append, List.append_assoc]
                  rcases hhd with ⟨c_hd, cs_hd, hhd_list, hhd_ws, hhd_br⟩
                  have hf_tab : f ≥ (String.intercalate ", " (kv0 :: kvr0) ++ "}").toList.length := by
                    rw [hrs_list, hkvs_eq, List.length_cons] at hf; omega
                  have hVal : ∀ q v, lookupKeyList q t.toList = some v → ∀ tp rs', renderValueInline v tp = some rs' →
                      ∀ rest' fuel', fuel' ≥ rs'.toList.length →
                      (∀ c r, rest' = c :: r →
                        isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) →
                      ∃ v', parseValueFuel numApi fuel' (rs'.toList ++ rest') = .ok (v', rest') ∧
                        TomlEquiv v v' ∧ (rs'.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
                    intro q v hqv tp rs' hrv' rest' fuel' hfv' hrest'
                    have hlt : sizeOf v < len := by
                      rw [← n0]; exact sizeOf_lt_of_mem_table (lookupKeyList_mem hqv)
                    exact ih (sizeOf v) hlt v tp rs' hrv' rest' fuel' hfv' hrest' rfl
                  obtain ⟨resT, hres_parse, hres_eqv, hres_cl⟩ :=
                    renderInlineTableEntries_parseInlineTableFuel numApi t.toList t.toList (e0 :: er0) (kv0 :: kvr0)
                      (fun _ _ h => h) hre' (by simp) hVal []
                      (fun _ _ => rfl) (fun _ _ _ => rfl)
                      (fun q v1 h1 h2 => by rw [h1] at h2; cases h2)
                      rest f hf_tab
                  refine ⟨.table resT, ?_, ?_, ?_⟩
                  · rw [← hkvs_eq, hrs_list, hkvs_eq, List.cons_append]
                    have hpv_step : parseValueFuel numApi (f + 1) ('{' :: ((String.intercalate ", " (kv0 :: kvr0) ++ "}").toList ++ rest)) =
                        (match skipHorizWs ((String.intercalate ", " (kv0 :: kvr0) ++ "}").toList ++ rest) with
                         | '}' :: afterClose => .ok (.table #[], afterClose)
                         | other => parseInlineTableFuel numApi f other []) := rfl
                    rw [hpv_step, hhd_list, List.cons_append, skipHorizWs_cons_of_false c_hd _ hhd_ws]
                    split
                    · rename_i heq; injection heq with h1 _; exact absurd h1 hhd_br
                    · rw [← List.cons_append, ← hhd_list]
                      exact hres_parse
                  · simpa [TomlEquiv, TomlTableEquiv] using hres_eqv
                  · rw [← hkvs_eq, hrs_list, hkvs_eq, List.all_cons]
                    exact Bool.and_eq_true_iff.mpr ⟨by decide, hres_cl⟩
      | _ => simp [renderValueInline] at hr
    | string _ | int _ | float _ | bool _
    | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
      have hf_ge1 : fuel ≥ 1 := by
        obtain ⟨_, _, hlist, _⟩ := renderValueInline_headSafe _ tape rs hr
        rw [hlist, List.length_cons] at hf
        omega
      obtain ⟨v', hpv, heqv, hcl, _⟩ :=
        renderValueInline_scalar_parseValueFuel numApi hInt hFloat _ tape rs hr rest fuel hf_ge1 (by trivial) hrest
      exact ⟨v', hpv, heqv, hcl⟩

private def joinLines : List String → String
  | [] => ""
  | l :: ls => l ++ "\n" ++ joinLines ls

private theorem joinLines_append (a b : List String) :
    joinLines (a ++ b) = joinLines a ++ joinLines b := by
  induction a with
  | nil => simp [joinLines]
  | cons l ls ih => simp [joinLines, ih, String.append_assoc]

private theorem intercalate_nl_append_nl (lines : List String) (hne : lines ≠ []) :
    String.intercalate "\n" lines ++ "\n" = joinLines lines := by
  induction lines with
  | nil => exact absurd rfl hne
  | cons l ls ih =>
    cases ls with
    | nil => simp [String.intercalate_singleton, joinLines]
    | cons l2 ls2 =>
      rw [String.intercalate_cons_cons, joinLines, String.append_assoc]
      congr 1
      exact ih (by simp)

private theorem joinLines_all_clean (lines : List String)
    (h : ∀ l ∈ lines, (l.toList.all fun c => !isDisallowedControl c && c != '\r') = true) :
    ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
  induction lines with
  | nil => rfl
  | cons l ls ih =>
    simp [joinLines, List.all_append, h l (by simp), ih (fun x hx => h x (by simp [hx])),
      (by decide : isDisallowedControl '\n' = false)]

private theorem joinLines_singleton_clean (s : String)
    (h : (s.toList.all fun c => !isDisallowedControl c && c != '\r') = true) :
    ((joinLines [s]).toList.all fun c => !isDisallowedControl c && c != '\r') = true :=
  joinLines_all_clean [s] (fun _ hl => by simp only [List.mem_singleton] at hl; subst hl; exact h)

private theorem skipCommentBody_clean (cs rest : List Char)
    (h : (cs.all fun c => c != '\n') = true) :
    skipCommentBody (cs ++ '\n' :: rest) = '\n' :: rest := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.cons_append]
    unfold skipCommentBody
    simp [h.1]
    exact ih h.2

private theorem skipTriviaNewlinesAux_true_clean (cs rest : List Char)
    (h : (cs.all fun c => c != '\n') = true) :
    skipTriviaNewlinesAux true (cs ++ '\n' :: rest) = skipTriviaNewlines rest := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.cons_append]
    unfold skipTriviaNewlinesAux
    simp [h.1]
    exact ih h.2

private theorem skipTriviaNewlines_comment_line (c : String) (rest : List Char)
    (hc : isSingleLineClean c = true) :
    skipTriviaNewlines (("#" ++ c ++ "\n").toList ++ rest) = skipTriviaNewlines rest := by
  have hno : (c.toList.all fun ch => ch != '\n') = true := by
    simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc ⊢
    intro ch hch
    exact (hc ch hch).1.2
  have hlist : ("#" ++ c ++ "\n").toList ++ rest = '#' :: (c.toList ++ '\n' :: rest) := by
    simp [String.toList_append, List.cons_append, List.append_assoc]
  rw [hlist]
  exact skipTriviaNewlinesAux_true_clean c.toList rest hno

private theorem renderCommentSuffix_props (comment : Option String) (rc : String)
    (h : renderCommentSuffix comment = some rc) :
    (rc.toList.all fun ch => !isDisallowedControl ch && ch != '\r' && ch != '\n') = true ∧
    (∀ rest : List Char, consumeStatementEnd (rc.toList ++ '\n' :: rest) = .ok rest) ∧
    (∀ rest : List Char, ∀ c r, rc.toList ++ '\n' :: rest = c :: r →
      isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)) := by
  cases comment with
  | none =>
    simp only [renderCommentSuffix, Option.some.injEq] at h
    subst h
    refine ⟨rfl, fun rest => ?_, fun rest c r hc => ?_⟩
    · simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs]
    · injection hc with hc' _; subst hc'; exact ⟨by decide, fun h => by cases h⟩
  | some s =>
    simp only [renderCommentSuffix] at h
    split at h
    · rename_i hclean
      injection h with hrc; subst hrc
      have hcl : (s.toList.all fun ch => !isDisallowedControl ch && ch != '\r' && ch != '\n') = true := by
        simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hclean ⊢
        intro ch hch
        exact ⟨⟨(hclean ch hch).1.1, (hclean ch hch).2⟩, (hclean ch hch).1.2⟩
      have hno_nl : (s.toList.all fun ch => ch != '\n') = true := by
        simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcl ⊢
        intro ch hch; exact (hcl ch hch).2
      refine ⟨?_, fun rest => ?_, fun rest c r hc => ?_⟩
      · simp [String.toList_append, hcl, (by decide : isDisallowedControl ' ' = false),
          (by decide : isDisallowedControl '#' = false)]
      · have hlist : (" #" ++ s).toList ++ '\n' :: rest = ' ' :: '#' :: (s.toList ++ '\n' :: rest) := by
          simp [String.toList_append, List.cons_append]
        rw [hlist]
        simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs, skipCommentBody_clean s.toList rest hno_nl]
      · have hlist : (" #" ++ s).toList ++ '\n' :: rest = ' ' :: '#' :: (s.toList ++ '\n' :: rest) := by
          simp [String.toList_append, List.cons_append]
        rw [hlist] at hc
        injection hc with hc1 hr1
        subst hc1
        refine ⟨by decide, fun _ c2 r2 hr2 => ?_⟩
        rw [← hr1] at hr2
        injection hr2 with hc2 _
        subst hc2; decide
    · cases h

private theorem joinRenderedPath_props (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2) :
    (∃ c0 cs0, (joinRenderedPath (pairs.map Prod.snd)).toList = c0 :: cs0 ∧
      isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ '[' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ '.') ∧
    ((joinRenderedPath (pairs.map Prod.snd)).toList.all fun c =>
      !isDisallowedControl c && c != '\r' && c != '\n') = true ∧
    pairs.length ≤ (joinRenderedPath (pairs.map Prod.snd)).toList.length := by
  induction pairs with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    rcases p with ⟨k, rk⟩
    obtain ⟨ks, hrk⟩ := hkeys (k, rk) (by simp)
    obtain ⟨c0, cs0, hrk_list, hws0, hn0, hc0, hbr0, hrb0, hl0, hdot0⟩ := renderKey_headSafe k ks rk hrk
    have hrk_clean := (renderKey_parseKeySegment k ks rk hrk [' '] (fun c _ h => by
      injection h with h1 _; subst h1; decide)).2
    have hrk_len : rk.toList.length ≥ 1 := by rw [hrk_list]; simp
    cases ps with
    | nil =>
      refine ⟨⟨c0, cs0, ?_, hws0, hn0, hc0, hl0, hbr0, hrb0, hdot0⟩, ?_, ?_⟩
      · simpa [joinRenderedPath] using hrk_list
      · simpa [joinRenderedPath] using hrk_clean
      · simpa [joinRenderedPath] using hrk_len
    | cons p2 ps2 =>
      obtain ⟨_, hclean_ps, hlen_ps⟩ := ih (by simp) (fun q hq => hkeys q (by simp [hq]))
      have hjoin : joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd) =
          rk ++ "." ++ joinRenderedPath ((p2 :: ps2).map Prod.snd) := rfl
      refine ⟨⟨c0, cs0 ++ ('.' :: (joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList), ?_,
          hws0, hn0, hc0, hl0, hbr0, hrb0, hdot0⟩, ?_, ?_⟩
      · rw [hjoin, String.toList_append, String.toList_append, hrk_list]
        simp [List.cons_append, List.append_assoc]
      · rw [hjoin, String.toList_append, String.toList_append, List.all_append, List.all_append]
        simpa [hrk_clean, (by decide : isDisallowedControl '.' = false)] using hclean_ps
      · rw [hjoin, String.toList_append, String.toList_append, List.length_append, List.length_append]
        simp only [List.length_cons] at hlen_ps ⊢
        omega

private theorem parseDottedKeyFuel_joinRenderedPath
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hsw : ∃ c2 t2, skipHorizWs rest = c2 :: t2 ∧ c2 ≠ '.')
    (fuel : Nat) (hf : fuel ≥ pairs.length) :
    parseDottedKeyFuel fuel ((joinRenderedPath (pairs.map Prod.snd)).toList ++ rest) =
      .ok (pairs.map Prod.fst, skipHorizWs rest) := by
  induction pairs generalizing rest fuel with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    rcases p with ⟨k, rk⟩
    obtain ⟨ks, hrk⟩ := hkeys (k, rk) (by simp)
    cases fuel with
    | zero => simp at hf
    | succ f =>
      cases ps with
      | nil =>
        simp only [List.map_cons, List.map_nil, joinRenderedPath]
        unfold parseDottedKeyFuel
        rw [(renderKey_parseKeySegment k ks rk hrk rest hrest).1]
        simp only [bind, Except.bind]
        rcases hsw with ⟨c2, t2, hsw_eq, hne_dot⟩
        rw [hsw_eq]
        split
        · rename_i heq; injection heq with h1 _; exact absurd h1 hne_dot
        · rfl
      | cons p2 ps2 =>
        have hps_ne : p2 :: ps2 ≠ [] := by simp
        have hps_keys : ∀ q ∈ p2 :: ps2, ∃ ks, renderKey q.1 ks = some q.2 :=
          fun q hq => hkeys q (by simp [hq])
        obtain ⟨⟨c2, cs2, hps_list, hws2, _⟩, _, _⟩ := joinRenderedPath_props (p2 :: ps2) hps_ne hps_keys
        have hjoin : joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd) =
            rk ++ "." ++ joinRenderedPath ((p2 :: ps2).map Prod.snd) := rfl
        have hsplit : (joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd)).toList ++ rest =
            rk.toList ++ ('.' :: ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest)) := by
          rw [hjoin, String.toList_append, String.toList_append, List.append_assoc]
          simp
        rw [hsplit]
        unfold parseDottedKeyFuel
        have hdot_rest : ∀ c tail,
            ('.' :: ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest)) = c :: tail →
            !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'' := by
          intro c tail h; injection h with h1 _; subst h1; decide
        rw [(renderKey_parseKeySegment k ks rk hrk _ hdot_rest).1]
        simp only [bind, Except.bind]
        rw [skipHorizWs_cons_of_false '.' _ (by decide)]
        split
        · rename_i r3 hdot_eq
          injection hdot_eq with _ hr3
          rw [← hr3]
          have hskip_ps : skipHorizWs ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest) =
              (joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest := by
            rw [hps_list, List.cons_append]
            exact skipHorizWs_cons_of_false c2 _ hws2
          rw [hskip_ps]
          have hf' : f ≥ (p2 :: ps2).length := by simp at hf; omega
          rw [ih hps_ne hps_keys rest hrest hsw f hf']
          rfl
        · rename_i hnot
          exact absurd rfl (hnot _)

private theorem parseDottedKey_joinRenderedPath
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hsw : ∃ c2 t2, skipHorizWs rest = c2 :: t2 ∧ c2 ≠ '.') :
    parseDottedKey ((joinRenderedPath (pairs.map Prod.snd)).toList ++ rest) =
      .ok (pairs.map Prod.fst, skipHorizWs rest) := by
  unfold parseDottedKey
  have hlen := (joinRenderedPath_props pairs hne hkeys).2.2
  refine parseDottedKeyFuel_joinRenderedPath pairs hne hkeys rest hrest hsw
    (((joinRenderedPath (pairs.map Prod.snd)).toList ++ rest).length + 1) (by simp; omega)

private theorem assocSetNode_idem (k : String) (v1 v2 : Node) (l : List (String × Node)) :
    assocSetNode k v2 (assocSetNode k v1 l) = assocSetNode k v2 l := by
  induction l with
  | nil => simp [assocSetNode]
  | cons p rest ih =>
    rcases p with ⟨k', old⟩
    by_cases h : k == k'
    · simp [assocSetNode, h]
    · simp [assocSetNode, h, ih]

private theorem assocLookupNode_assocSetNode_ne (k q : String) (v : Node)
    (l : List (String × Node)) (hne : q ≠ k) :
    assocLookupNode q (assocSetNode k v l) = assocLookupNode q l := by
  rw [assocLookupNode_assocSetNode, beq_false_of_ne hne]
  rfl

private theorem dropLast_append_singleton {α : Type} (l : List α) (x : α) :
    (l ++ [x]).dropLast = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l2 => simp [List.dropLast]

private theorem getLast?_append_singleton {α : Type} (l : List α) (x : α) :
    (l ++ [x]).getLast? = some x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l2 => simpa [List.getLast?] using ih

private theorem mapLastAot_eq (f : List (String × Node) → Except TomlError (List (String × Node)))
    (elems : List (List (String × Node))) (lastElem newLast : List (String × Node))
    (hne : elems ≠ []) (hlast : elems.getLast? = some lastElem) (hf : f lastElem = .ok newLast) :
    mapLastAot f elems = .ok (elems.dropLast ++ [newLast]) := by
  induction elems with
  | nil => exact absurd rfl hne
  | cons a bs ih =>
    cases bs with
    | nil =>
      have ha : a = lastElem := by simpa [List.getLast?] using hlast
      subst ha
      simp [mapLastAot, hf, bind, Except.bind]
    | cons b bs2 =>
      have hlast' : (b :: bs2).getLast? = some lastElem := by simpa [List.getLast?] using hlast
      have ih' := ih (by simp) hlast'
      simp [mapLastAot, ih', List.dropLast, bind, Except.bind]

private inductive AtLocalPath :
    List (String × Node) → List String → List (String × Node) →
    (List (String × Node) → List (String × Node)) → Prop where
  | nil (entries : List (String × Node)) :
      AtLocalPath entries [] entries id
  | consTable {entries : List (String × Node)} {k : String} {kind : TableKind}
      {sub : List (String × Node)} {ps : List String}
      {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      kind ≠ .inline →
      assocLookupNode k entries = some (.table kind sub) →
      AtLocalPath sub ps loc rb →
      AtLocalPath entries (k :: ps) loc (fun newLoc => assocSetNode k (.table kind (rb newLoc)) entries)
  | consAot {entries : List (String × Node)} {k : String}
      {elems : List (List (String × Node))} {lastElem : List (String × Node)}
      {ps : List String} {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      elems ≠ [] →
      elems.getLast? = some lastElem →
      assocLookupNode k entries = some (.aot elems) →
      AtLocalPath lastElem ps loc rb →
      AtLocalPath entries (k :: ps) loc
        (fun newLoc => assocSetNode k (.aot (elems.dropLast ++ [rb newLoc])) entries)

private theorem atLocalPath_self {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) :
    rb loc = root := by
  induction h with
  | nil _ => rfl
  | @consTable entries k kind sub ps loc rb _ hlk _ ih =>
    dsimp only
    rw [ih]
    clear ih
    induction entries with
    | nil => cases hlk
    | cons p rest ihr =>
      rcases p with ⟨k', n'⟩
      simp only [assocLookupNode] at hlk
      by_cases heq : k == k'
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hlk
        subst hlk
        simp [assocSetNode, heq]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hlk
        simp only [assocSetNode, heq, Bool.false_eq_true, ↓reduceIte, ihr hlk]
  | @consAot entries k elems lastElem ps loc rb hne hlast hlk _ ih =>
    dsimp only
    rw [ih]
    clear ih
    have helems : elems.dropLast ++ [lastElem] = elems := by
      clear hlk
      induction elems with
      | nil => exact absurd rfl hne
      | cons a bs ihe =>
        cases bs with
        | nil =>
          simp only [List.getLast?, Option.some.injEq] at hlast
          subst hlast; rfl
        | cons b bs2 =>
          have hlast' : (b :: bs2).getLast? = some lastElem := by simpa [List.getLast?] using hlast
          simp only [List.dropLast, List.cons_append, ihe (by simp) hlast']
    rw [helems]
    induction entries with
    | nil => cases hlk
    | cons p rest ihr =>
      rcases p with ⟨k', n'⟩
      simp only [assocLookupNode] at hlk
      by_cases heq : k == k'
      · simp only [heq, ↓reduceIte, Option.some.injEq] at hlk
        subst hlk
        simp [assocSetNode, heq]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hlk
        simp only [assocSetNode, heq, Bool.false_eq_true, ↓reduceIte, ihr hlk]

private theorem atLocalPath_rebuild {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (newLoc : List (String × Node)) :
    AtLocalPath (rb newLoc) path newLoc rb := by
  induction h with
  | nil _ => exact AtLocalPath.nil newLoc
  | @consTable entries k kind sub ps loc' rbSub hkind hlk hsub ih =>
    have hlk' : assocLookupNode k (assocSetNode k (.table kind (rbSub newLoc)) entries) =
        some (.table kind (rbSub newLoc)) := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.table kind (rbSub nl))
        (assocSetNode k (.table kind (rbSub newLoc)) entries)) =
        (fun nl => assocSetNode k (.table kind (rbSub nl)) entries) := by
      funext nl; exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using AtLocalPath.consTable hkind hlk' ih
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk hsub ih =>
    let elems' := elems.dropLast ++ [rbSub newLoc]
    have hne' : elems' ≠ [] := by simp [elems']
    have hlast' : elems'.getLast? = some (rbSub newLoc) := getLast?_append_singleton _ _
    have hlk' : assocLookupNode k (assocSetNode k (.aot elems') entries) = some (.aot elems') := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.aot (elems'.dropLast ++ [rbSub nl]))
        (assocSetNode k (.aot elems') entries)) =
        (fun nl => assocSetNode k (.aot (elems.dropLast ++ [rbSub nl])) entries) := by
      funext nl
      rw [dropLast_append_singleton]
      exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using AtLocalPath.consAot hne' hlast' hlk' ih

private theorem atLocalPath_stepTable {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (k : String) (kind : TableKind) (sub : List (String × Node))
    (hkind : kind ≠ .inline) (hlk : assocLookupNode k loc = some (.table kind sub)) :
    AtLocalPath root (path ++ [k]) sub (fun newSub => rb (assocSetNode k (.table kind newSub) loc)) := by
  induction h with
  | nil entries =>
    simp only [List.nil_append, id]
    exact AtLocalPath.consTable hkind hlk (AtLocalPath.nil sub)
  | consTable hkind0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consTable hkind0 hlk0 (ih hlk)
  | consAot hne0 hlast0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consAot hne0 hlast0 hlk0 (ih hlk)

private theorem atLocalPath_stepAot {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (k : String)
    (elems : List (List (String × Node))) (lastElem : List (String × Node))
    (hne : elems ≠ []) (hlast : elems.getLast? = some lastElem)
    (hlk : assocLookupNode k loc = some (.aot elems)) :
    AtLocalPath root (path ++ [k]) lastElem
      (fun newLast => rb (assocSetNode k (.aot (elems.dropLast ++ [newLast])) loc)) := by
  induction h with
  | nil entries =>
    simp only [List.nil_append, id]
    exact AtLocalPath.consAot hne hlast hlk (AtLocalPath.nil lastElem)
  | consTable hkind0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consTable hkind0 hlk0 (ih hlk)
  | consAot hne0 hlast0 hlk0 _ ih =>
    simp only [List.cons_append]
    exact AtLocalPath.consAot hne0 hlast0 hlk0 (ih hlk)

private theorem atLocalPath_insertAtActivePath {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (fullPath relPath : List String) (newNode : Node)
    (newLoc : List (String × Node))
    (hins : insertDottedEntries fullPath loc relPath newNode = .ok newLoc) :
    insertAtActivePath fullPath root path relPath newNode = .ok (rb newLoc) := by
  induction h with
  | nil entries => simpa [insertAtActivePath] using hins
  | @consTable entries k kind sub ps loc' rbSub _ hlk _ ih =>
    simp [insertAtActivePath, hlk, ih hins, bind, Except.bind]
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk _ ih =>
    have hmap := mapLastAot_eq (fun elem => insertAtActivePath fullPath elem ps relPath newNode)
      elems lastElem (rbSub newLoc) hne hlast (ih hins)
    simp [insertAtActivePath, hlk, hmap, bind, Except.bind]

private theorem atLocalPath_applyTableHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyTableHeader fullPath loc suffix = .ok newLoc) :
    applyTableHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h with
  | nil entries => simpa using happ
  | @consTable entries k kind sub ps loc' rbSub hkind hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyTableHeader, hlk]
      rw [← hps]
      cases kind with
      | inline => exact absurd rfl hkind
      | explicit | subtableImplicit | dotted => simp [ih happ, bind, Except.bind]
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyTableHeader, hlk]
      rw [← hps]
      have hmap := mapLastAot_eq (fun elem => applyTableHeader fullPath elem (ps ++ suffix))
        elems lastElem (rbSub newLoc) hne hlast (ih happ)
      simp [hmap, bind, Except.bind]

private theorem atLocalPath_applyAotHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtLocalPath root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyAotHeader fullPath loc suffix = .ok newLoc) :
    applyAotHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h with
  | nil entries => simpa using happ
  | @consTable entries k kind sub ps loc' rbSub hkind hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyAotHeader, hlk]
      rw [← hps]
      cases kind with
      | inline => exact absurd rfl hkind
      | explicit | subtableImplicit | dotted => simp [ih happ, bind, Except.bind]
  | @consAot entries k elems lastElem ps loc' rbSub hne hlast hlk hsub ih =>
    have hps_ne : ps ++ suffix ≠ [] := by
      cases ps with
      | nil => simpa using hsuf
      | cons _ _ => simp
    cases hps : ps ++ suffix with
    | nil => exact absurd hps hps_ne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [applyAotHeader, hlk]
      rw [← hps]
      have hmap := mapLastAot_eq (fun elem => applyAotHeader fullPath elem (ps ++ suffix))
        elems lastElem (rbSub newLoc) hne hlast (ih happ)
      simp [hmap, bind, Except.bind]

private inductive AtHeaderFocus :
    List (String × Node) → List String → List (String × Node) →
    (List (String × Node) → List (String × Node)) → Prop where
  | exact {root : List (String × Node)} {path : List String}
      {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      AtLocalPath root path loc rb → AtHeaderFocus root path loc rb
  | implicitNone {root parentLoc : List (String × Node)} {parentPath : List String}
      {rbParent : List (String × Node) → List (String × Node)} {k : String} :
      AtHeaderFocus root parentPath parentLoc rbParent →
      assocLookupNode k parentLoc = none →
      AtHeaderFocus root (parentPath ++ [k]) []
        (fun newSub => rbParent (assocSetNode k (.table .subtableImplicit newSub) parentLoc))

private theorem atHeaderFocus_applyTableHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtHeaderFocus root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyTableHeader fullPath loc suffix = .ok newLoc) :
    applyTableHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h generalizing suffix newLoc with
  | exact hp => exact atLocalPath_applyTableHeader hp fullPath suffix hsuf newLoc happ
  | @implicitNone parentLoc parentPath rbParent k hParent hnone ih =>
    rw [List.append_assoc]
    apply ih (k :: suffix) (by simp) (assocSetNode k (.table .subtableImplicit newLoc) parentLoc)
    cases suffix with
    | nil => exact absurd rfl hsuf
    | cons s0 ss0 =>
      simp [applyTableHeader, hnone, happ, bind, Except.bind]

private theorem atHeaderFocus_applyAotHeader {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtHeaderFocus root path loc rb) (fullPath suffix : List String) (hsuf : suffix ≠ [])
    (newLoc : List (String × Node))
    (happ : applyAotHeader fullPath loc suffix = .ok newLoc) :
    applyAotHeader fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h generalizing suffix newLoc with
  | exact hp => exact atLocalPath_applyAotHeader hp fullPath suffix hsuf newLoc happ
  | @implicitNone parentLoc parentPath rbParent k hParent hnone ih =>
    rw [List.append_assoc]
    apply ih (k :: suffix) (by simp) (assocSetNode k (.table .subtableImplicit newLoc) parentLoc)
    cases suffix with
    | nil => exact absurd rfl hsuf
    | cons s0 ss0 =>
      simp [applyAotHeader, hnone, happ, bind, Except.bind]

private theorem atHeaderFocus_step {root : List (String × Node)} {path : List String}
    {loc : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : AtHeaderFocus root path loc rb) (newLoc : List (String × Node)) :
    AtLocalPath (rb newLoc) path newLoc rb := by
  induction h generalizing newLoc with
  | exact hp => exact atLocalPath_rebuild hp newLoc
  | @implicitNone parentLoc parentPath rbParent k hParent hnone ih =>
    let newParent := assocSetNode k (.table .subtableImplicit newLoc) parentLoc
    have hp := ih newParent
    have hlk : assocLookupNode k newParent = some (.table .subtableImplicit newLoc) := by
      simp [newParent, assocLookupNode_assocSetNode]
    have hstep := atLocalPath_stepTable hp k .subtableImplicit newLoc (by decide) hlk
    have hrb_eq : (fun nl => rbParent (assocSetNode k (.table .subtableImplicit nl) newParent)) =
        (fun nl => rbParent (assocSetNode k (.table .subtableImplicit nl) parentLoc)) := by
      funext nl
      simp [newParent, assocSetNode_idem]
    rwa [hrb_eq] at hstep

private theorem joinLines_length_ge (lines : List String) :
    (joinLines lines).toList.length ≥ lines.length := by
  induction lines with
  | nil => simp
  | cons l ls ih =>
    simp only [joinLines, String.toList_append, List.length_append, List.length_cons]
    have hnl : ("\n" : String).toList.length = 1 := rfl
    omega

private theorem parseDocumentFuel_assign_step (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (v : TomlValue) (vt : ValueTape) (rv : String) (hrv : renderValueInline v vt = some rv)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root : List (String × Node))
    (restChars : List Char) (fuel : Nat) (hf : fuel ≥ 1) :
    ∃ v', TomlEquiv v v' ∧
      ((joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc).toList.all fun c =>
        !isDisallowedControl c && c != '\r') = true ∧
      (∀ nextRoot, insertAtActivePath (activePath ++ pairs.map Prod.fst) root activePath
        (pairs.map Prod.fst) (valueToInlineNode v') = .ok nextRoot →
       parseDocumentFuel numApi fuel
         ((joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars)
         activePath root =
       parseDocumentFuel numApi (fuel - 1) restChars activePath nextRoot) := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, cs0, hlhs_list, hws0, hn0, hc0, hl0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, hrc_delim⟩ := renderCommentSuffix_props comment rc hrc
  obtain ⟨cv0, csv0, hrv_list, hvws0, _⟩ := renderValueInline_headSafe v vt rv hrv
  let valRest := rc.toList ++ '\n' :: restChars
  let valFuel := (rv.toList ++ valRest).length + 2
  obtain ⟨v', hpv, heqv, hrv_cl⟩ :=
    renderValueInline_parseValueFuel numApi hInt hFloat v vt rv hrv valRest valFuel
      (by dsimp only [valFuel]; rw [List.length_append]; omega) (hrc_delim restChars)
  have hline_cl : ((lhs ++ " = " ++ rv ++ rc).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
    simp only [String.toList_append, List.all_append]
    have hlhs_cl' : (lhs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hlhs_cl ⊢
      intro c hc; exact (hlhs_cl c hc).1
    have hrc_cl' : (rc.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hrc_cl ⊢
      intro c hc; exact (hrc_cl c hc).1
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hlhs_cl', by decide⟩, hrv_cl⟩, hrc_cl'⟩
  refine ⟨v', heqv, hline_cl, fun nextRoot hins' => ?_⟩
  have hf_pos : ∃ f, fuel = f + 1 ∧ fuel - 1 = f := by
    cases fuel with
    | zero => omega
    | succ f => exact ⟨f, rfl, rfl⟩
  rcases hf_pos with ⟨f, hfeq, hsub⟩
  have hline_list : (lhs ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars =
      lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest)) := by
    simp [valRest, String.toList_append, List.cons_append, List.append_assoc]
  have hskip : skipTriviaNewlines ((lhs ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars) =
      lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest)) := by
    rw [hline_list, hlhs_list, List.cons_append]
    exact skipTriviaNewlines_cons_of_safe c0 _ hws0 hn0 hc0
  have hdk : parseDottedKey (lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest))) =
      .ok (pairs.map Prod.fst, '=' :: ' ' :: (rv.toList ++ valRest)) := by
    have h := parseDottedKey_joinRenderedPath pairs hne hkeys (' ' :: '=' :: ' ' :: (rv.toList ++ valRest))
      (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
      ⟨'=', ' ' :: (rv.toList ++ valRest), by simp [skipHorizWs, isHorizWs], by decide⟩
    simpa [lhs, skipHorizWs, isHorizWs] using h
  have hr2 : skipHorizWs ('=' :: ' ' :: (rv.toList ++ valRest)) = '=' :: ' ' :: (rv.toList ++ valRest) :=
    skipHorizWs_cons_of_false '=' _ (by decide)
  have hval_in : skipHorizWs (' ' :: (rv.toList ++ valRest)) = rv.toList ++ valRest := by
    rw [skipHorizWs_space, hrv_list, List.cons_append]
    exact skipHorizWs_cons_of_false cv0 _ hvws0
  have hval_ok : parseValue numApi (rv.toList ++ valRest) = .ok (v', valRest) := by
    unfold parseValue; exact hpv
  rw [hsub, hfeq]
  conv => lhs; unfold parseDocumentFuel
  rw [hskip]
  split
  · rename_i heq; rw [hlhs_list] at heq; cases heq
  · rename_i heq; rw [hlhs_list, List.cons_append] at heq
    injection heq with h1 _; exact absurd h1 hl0
  · rename_i heq; rw [hlhs_list, List.cons_append] at heq
    injection heq with h1 _; exact absurd h1 hl0
  · rw [hdk]
    simp only [bind, Except.bind, hr2]
    rw [hval_in, hval_ok]
    dsimp only [valRest]
    rw [hrc_end restChars]
    dsimp only
    rw [hins']

private theorem parseDocumentFuel_table_step (numApi : NumParseApi)
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root nextRoot : List (String × Node))
    (happ : applyTableHeader (pairs.map Prod.fst) root (pairs.map Prod.fst) = .ok nextRoot)
    (restChars : List Char) (fuel : Nat) (hf : fuel ≥ 1) :
    (("[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]" ++ rc).toList.all fun c =>
      !isDisallowedControl c && c != '\r') = true ∧
    parseDocumentFuel numApi fuel
      (("[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]" ++ rc).toList ++ '\n' :: restChars)
      activePath root =
    parseDocumentFuel numApi (fuel - 1) restChars (pairs.map Prod.fst) nextRoot := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, cs0, hlhs_list, hws0, _, _, hl0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, _⟩ := renderCommentSuffix_props comment rc hrc
  have hline_cl : (("[" ++ lhs ++ "]" ++ rc).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
    simp only [String.toList_append, List.all_append]
    have hlhs_cl' : (lhs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hlhs_cl ⊢
      intro c hc; exact (hlhs_cl c hc).1
    have hrc_cl' : (rc.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hrc_cl ⊢
      intro c hc; exact (hrc_cl c hc).1
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨by decide, hlhs_cl'⟩, by decide⟩, hrc_cl'⟩
  refine ⟨hline_cl, ?_⟩
  have hf_pos : ∃ f, fuel = f + 1 ∧ fuel - 1 = f := by
    cases fuel with
    | zero => omega
    | succ f => exact ⟨f, rfl, rfl⟩
  rcases hf_pos with ⟨f, hfeq, hsub⟩
  have hline_list : ("[" ++ lhs ++ "]" ++ rc).toList ++ '\n' :: restChars =
      '[' :: (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) := by
    simp [String.toList_append, List.cons_append, List.append_assoc]
  have hskip : skipTriviaNewlines (("[" ++ lhs ++ "]" ++ rc).toList ++ '\n' :: restChars) =
      '[' :: (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) := by
    rw [hline_list]
    exact skipTriviaNewlines_cons_of_safe '[' _ (by decide) (by decide) (by decide)
  have hrest_lhs : skipHorizWs (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) =
      lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars)) := by
    rw [hlhs_list, List.cons_append]
    exact skipHorizWs_cons_of_false c0 _ hws0
  have hdk : parseDottedKey (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) =
      .ok (pairs.map Prod.fst, ']' :: (rc.toList ++ '\n' :: restChars)) := by
    have h := parseDottedKey_joinRenderedPath pairs hne hkeys (']' :: (rc.toList ++ '\n' :: restChars))
      (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
      ⟨']', rc.toList ++ '\n' :: restChars, skipHorizWs_cons_of_false ']' _ (by decide), by decide⟩
    simpa [lhs, skipHorizWs_cons_of_false ']' _ (by decide)] using h
  have hr2 : skipHorizWs (']' :: (rc.toList ++ '\n' :: restChars)) = ']' :: (rc.toList ++ '\n' :: restChars) :=
    skipHorizWs_cons_of_false ']' _ (by decide)
  rw [hsub, hfeq]
  conv => lhs; unfold parseDocumentFuel
  rw [hskip]
  split
  · rename_i heq; cases heq
  · rename_i heq
    injection heq with _ h2
    rw [hlhs_list, List.cons_append] at h2
    injection h2 with h2' _
    exact absurd h2' hl0
  · rename_i restHdr _ heq
    injection heq with _ hrest_eq
    rw [← hrest_eq, hrest_lhs, hdk]
    simp only [bind, Except.bind, hr2]
    rw [hrc_end restChars]
    dsimp only
    rw [happ]
  · rename_i hnot
    exact absurd rfl (hnot _)

private theorem parseDocumentFuel_aot_step (numApi : NumParseApi)
    (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root nextRoot : List (String × Node))
    (happ : applyAotHeader (pairs.map Prod.fst) root (pairs.map Prod.fst) = .ok nextRoot)
    (restChars : List Char) (fuel : Nat) (hf : fuel ≥ 1) :
    (("[[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]]" ++ rc).toList.all fun c =>
      !isDisallowedControl c && c != '\r') = true ∧
    parseDocumentFuel numApi fuel
      (("[[" ++ joinRenderedPath (pairs.map Prod.snd) ++ "]]" ++ rc).toList ++ '\n' :: restChars)
      activePath root =
    parseDocumentFuel numApi (fuel - 1) restChars (pairs.map Prod.fst) nextRoot := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, cs0, hlhs_list, hws0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, _⟩ := renderCommentSuffix_props comment rc hrc
  have hline_cl : (("[[" ++ lhs ++ "]]" ++ rc).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
    simp only [String.toList_append, List.all_append]
    have hlhs_cl' : (lhs.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hlhs_cl ⊢
      intro c hc; exact (hlhs_cl c hc).1
    have hrc_cl' : (rc.toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hrc_cl ⊢
      intro c hc; exact (hrc_cl c hc).1
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨by decide, hlhs_cl'⟩, by decide⟩, hrc_cl'⟩
  refine ⟨hline_cl, ?_⟩
  have hf_pos : ∃ f, fuel = f + 1 ∧ fuel - 1 = f := by
    cases fuel with
    | zero => omega
    | succ f => exact ⟨f, rfl, rfl⟩
  rcases hf_pos with ⟨f, hfeq, hsub⟩
  have hline_list : ("[[" ++ lhs ++ "]]" ++ rc).toList ++ '\n' :: restChars =
      '[' :: '[' :: (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) := by
    simp [String.toList_append, List.cons_append, List.append_assoc]
  have hskip : skipTriviaNewlines (("[[" ++ lhs ++ "]]" ++ rc).toList ++ '\n' :: restChars) =
      '[' :: '[' :: (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) := by
    rw [hline_list]
    exact skipTriviaNewlines_cons_of_safe '[' _ (by decide) (by decide) (by decide)
  have hrest_lhs : skipHorizWs (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) =
      lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars)) := by
    rw [hlhs_list, List.cons_append]
    exact skipHorizWs_cons_of_false c0 _ hws0
  have hdk : parseDottedKey (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) =
      .ok (pairs.map Prod.fst, ']' :: ']' :: (rc.toList ++ '\n' :: restChars)) := by
    have h := parseDottedKey_joinRenderedPath pairs hne hkeys (']' :: ']' :: (rc.toList ++ '\n' :: restChars))
      (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
      ⟨']', ']' :: (rc.toList ++ '\n' :: restChars), skipHorizWs_cons_of_false ']' _ (by decide), by decide⟩
    simpa [lhs, skipHorizWs_cons_of_false ']' _ (by decide)] using h
  have hr2 : skipHorizWs (']' :: ']' :: (rc.toList ++ '\n' :: restChars)) =
      ']' :: ']' :: (rc.toList ++ '\n' :: restChars) :=
    skipHorizWs_cons_of_false ']' _ (by decide)
  rw [hsub, hfeq]
  conv => lhs; unfold parseDocumentFuel
  rw [hskip]
  split
  · rename_i heq; cases heq
  · rename_i restHdr _ heq
    injection heq with _ h1
    injection h1 with _ hrest_eq
    rw [← hrest_eq, hrest_lhs, hdk]
    simp only [bind, Except.bind, hr2]
    rw [hrc_end restChars]
    dsimp only
    rw [happ]
  · rename_i hnot heq
    injection heq with _ htail
    exact absurd htail.symm (hnot _)
  · rename_i hnot _
    exact absurd rfl (hnot _)

private inductive DottedWriteFocus :
    List (String × Node) → List String → List (String × Node) →
    (List (String × Node) → List (String × Node)) → Prop where
  | nil (entries : List (String × Node)) :
      DottedWriteFocus entries [] entries id
  | consNone {entries : List (String × Node)} {k : String} {ps : List String}
      {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      assocLookupNode k entries = none →
      DottedWriteFocus [] ps sub rb →
      DottedWriteFocus entries (k :: ps) sub (fun newSub => assocSetNode k (.table .dotted (rb newSub)) entries)
  | consDotted {entries : List (String × Node)} {k : String} {cur : List (String × Node)}
      {ps : List String} {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)} :
      assocLookupNode k entries = some (.table .dotted cur) →
      DottedWriteFocus cur ps sub rb →
      DottedWriteFocus entries (k :: ps) sub (fun newSub => assocSetNode k (.table .dotted (rb newSub)) entries)

private theorem dottedWriteFocus_insert {entries : List (String × Node)} {pref : List String}
    {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : DottedWriteFocus entries pref sub rb) (fullPath rel : List String) (hrel : rel ≠ [])
    (newNode : Node) (newSub : List (String × Node))
    (hins : insertDottedEntries fullPath sub rel newNode = .ok newSub) :
    insertDottedEntries fullPath entries (pref ++ rel) newNode = .ok (rb newSub) := by
  induction h with
  | nil entries => simpa using hins
  | @consNone entries k ps sub' rbSub hnone hsub ih =>
    have hne : ps ++ rel ≠ [] := by
      cases ps with
      | nil => simpa using hrel
      | cons _ _ => simp
    cases hps : ps ++ rel with
    | nil => exact absurd hps hne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [insertDottedEntries, hnone]
      rw [← hps]
      simp [ih hins, bind, Except.bind]
  | @consDotted entries k cur ps sub' rbSub hlk hsub ih =>
    have hne : ps ++ rel ≠ [] := by
      cases ps with
      | nil => simpa using hrel
      | cons _ _ => simp
    cases hps : ps ++ rel with
    | nil => exact absurd hps hne
    | cons s0 ss0 =>
      rw [List.cons_append, hps]
      simp only [insertDottedEntries, hlk]
      rw [← hps]
      simp [ih hins, bind, Except.bind]

private theorem dottedWriteFocus_rebuild {entries : List (String × Node)} {pref : List String}
    {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : DottedWriteFocus entries pref sub rb) (newSub : List (String × Node)) :
    DottedWriteFocus (rb newSub) pref newSub rb := by
  induction h with
  | nil _ => exact DottedWriteFocus.nil newSub
  | @consNone entries k ps sub' rbSub hnone hsub ih =>
    have hlk' : assocLookupNode k (assocSetNode k (.table .dotted (rbSub newSub)) entries) =
        some (.table .dotted (rbSub newSub)) := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.table .dotted (rbSub nl))
        (assocSetNode k (.table .dotted (rbSub newSub)) entries)) =
        (fun nl => assocSetNode k (.table .dotted (rbSub nl)) entries) := by
      funext nl; exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using DottedWriteFocus.consDotted hlk' ih
  | @consDotted entries k cur ps sub' rbSub hlk hsub ih =>
    have hlk' : assocLookupNode k (assocSetNode k (.table .dotted (rbSub newSub)) entries) =
        some (.table .dotted (rbSub newSub)) := by
      rw [assocLookupNode_assocSetNode]; simp
    have hrb_eq : (fun nl => assocSetNode k (.table .dotted (rbSub nl))
        (assocSetNode k (.table .dotted (rbSub newSub)) entries)) =
        (fun nl => assocSetNode k (.table .dotted (rbSub nl)) entries) := by
      funext nl; exact assocSetNode_idem k _ _ entries
    simpa only [hrb_eq] using DottedWriteFocus.consDotted hlk' ih

private theorem dottedWriteFocus_step {entries : List (String × Node)} {pref : List String}
    {sub : List (String × Node)} {rb : List (String × Node) → List (String × Node)}
    (h : DottedWriteFocus entries pref sub rb) (k : String) (hnone : assocLookupNode k sub = none) :
    DottedWriteFocus entries (pref ++ [k]) [] (fun newSub => rb (assocSetNode k (.table .dotted newSub) sub)) := by
  induction h with
  | nil entries =>
    simp only [List.nil_append, id]
    exact DottedWriteFocus.consNone hnone (DottedWriteFocus.nil [])
  | consNone hn0 hsub ih =>
    simp only [List.cons_append]
    exact DottedWriteFocus.consNone hn0 (ih hnone)
  | consDotted hlk0 hsub ih =>
    simp only [List.cons_append]
    exact DottedWriteFocus.consDotted hlk0 (ih hnone)

private theorem noDupStringsBool_iff_nodup (l : List String) :
    noDupStringsBool l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [noDupStringsBool]
  | cons x xs ih =>
    simp only [noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons]
    rw [ih]
    constructor
    · rintro ⟨hx, hxs⟩
      refine ⟨fun hmem => ?_, hxs⟩
      have hc : xs.contains x = true := List.contains_iff_mem.mpr hmem
      rw [hc] at hx; cases hx
    · rintro ⟨hx, hxs⟩
      refine ⟨?_, hxs⟩
      rw [Bool.eq_false_iff]; intro hc
      exact hx (List.contains_iff_mem.mp hc)

private theorem nodup_subset_len_mem {l1 l2 : List String}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hlen : l1.length = l2.length)
    (hsub : ∀ x ∈ l1, x ∈ l2) : ∀ y ∈ l2, y ∈ l1 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => intro y hy; cases hy
    | cons _ _ => simp at hlen
  | cons a as ih =>
    rw [List.nodup_cons] at h1
    have ha2 : a ∈ l2 := hsub a (by simp)
    have h2_erase : (l2.erase a).Nodup := h2.erase a
    have hlen_erase : as.length = (l2.erase a).length := by
      have hl : (l2.erase a).length = l2.length - 1 := List.length_erase_of_mem ha2
      simp only [List.length_cons] at hlen
      have hpos : l2.length ≥ 1 := List.length_pos_of_mem ha2
      omega
    have hsub_erase : ∀ x ∈ as, x ∈ l2.erase a := by
      intro x hx
      have hne : x ≠ a := fun heq => h1.1 (heq ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (by simp [hx]))
    intro y hy
    by_cases hya : y = a
    · simp [hya]
    · have hy_er : y ∈ l2.erase a := (List.mem_erase_of_ne hya).mpr hy
      exact List.mem_cons_of_mem a (ih h1.2 h2_erase hlen_erase hsub_erase y hy_er)

private theorem isPlanPermutation_props {entries : List (String × TomlValue)}
    {plan : List (String × EntryPlacement)} (h : isPlanPermutation entries plan = true) :
    noDupKeysBool entries = true ∧
    noDupStringsBool (plan.map Prod.fst) = true ∧
    (∀ p ∈ plan, ∃ v, lookupKeyList p.1 entries = some v) ∧
    (∀ q v, lookupKeyList q entries = some v → ∃ ep, (q, ep) ∈ plan) := by
  simp only [isPlanPermutation, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  rcases h with ⟨⟨⟨hnd_e, hnd_p⟩, hlen⟩, hall⟩
  have h1 : ∀ p ∈ plan, ∃ v, lookupKeyList p.1 entries = some v := by
    intro p hp
    have hhas : hasKeyList p.1 entries = true := hall p hp
    clear hall hp hnd_e hnd_p hlen
    induction entries with
    | nil => cases hhas
    | cons e es ih =>
      rcases e with ⟨ek, ev⟩
      simp only [lookupKeyList]
      simp only [hasKeyList] at hhas
      by_cases hpk : p.1 == ek
      · simp [hpk]
      · simp only [hpk, Bool.false_eq_true, ↓reduceIte, Bool.false_or] at hhas ⊢
        exact ih hhas
  have hnodup_p : (plan.map Prod.fst).Nodup := (noDupStringsBool_iff_nodup _).mp hnd_p
  have hnodup_e : (entries.map Prod.fst).Nodup := (noDupKeys_iff_nodup entries).mp hnd_e
  have hsub : ∀ x ∈ plan.map Prod.fst, x ∈ entries.map Prod.fst := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨p, hp, rfl⟩
    exact (hasKeyList_eq_true_iff p.1 entries).mp (hall p hp)
  have hlen' : (plan.map Prod.fst).length = (entries.map Prod.fst).length := by
    simpa using hlen
  have hcov : ∀ q v, lookupKeyList q entries = some v → ∃ ep, (q, ep) ∈ plan := by
    intro q v hqv
    have hq_mem_e : q ∈ entries.map Prod.fst := by
      have hp := lookupKeyList_mem hqv
      exact List.mem_map.mpr ⟨(q, v), hp, rfl⟩
    have hq_mem_p : q ∈ plan.map Prod.fst := nodup_subset_len_mem hnodup_p hnodup_e hlen' hsub q hq_mem_e
    rw [List.mem_map] at hq_mem_p
    rcases hq_mem_p with ⟨⟨k, ep⟩, hmem, hkq⟩
    dsimp only at hkq; subst hkq
    exact ⟨ep, hmem⟩
  exact ⟨hnd_e, hnd_p, h1, hcov⟩

private theorem entriesToTomlList_of_plan_match (entries : List (String × TomlValue))
    (plan : List (String × EntryPlacement)) (hperm : isPlanPermutation entries plan = true)
    (nodes : List (String × Node))
    (hmatch : ∀ p ∈ plan, ∃ v nd, lookupKeyList p.1 entries = some v ∧
      assocLookupNode p.1 nodes = some nd ∧ TomlEquiv v (nodeToTomlValue nd))
    (honly : ∀ q, q ∉ plan.map Prod.fst → assocLookupNode q nodes = none) :
    TomlTableEquivList entries (entriesToTomlList nodes) := by
  obtain ⟨_, _, _, hcov⟩ := isPlanPermutation_props hperm
  unfold TomlTableEquivList
  refine ⟨?_, ?_⟩
  · intro q hnone
    rw [lookupKeyList_entriesToTomlList]
    by_cases hmem : q ∈ plan.map Prod.fst
    · rw [List.mem_map] at hmem
      rcases hmem with ⟨p, hp, rfl⟩
      obtain ⟨v, _, hv, _⟩ := hmatch p hp
      rw [hv] at hnone; cases hnone
    · rw [honly q hmem]; rfl
  · intro q v1 hqv1
    obtain ⟨ep, hep⟩ := hcov q v1 hqv1
    obtain ⟨v, nd, hv, hnd, heqv⟩ := hmatch (q, ep) hep
    have hv_eq : v1 = v := by rw [hqv1] at hv; injection hv
    subst hv_eq
    refine ⟨nodeToTomlValue nd, ?_, heqv⟩
    rw [lookupKeyList_entriesToTomlList, hnd]; rfl

private theorem nodup_key_ne_of_scope (plan : List (String × EntryPlacement))
    (hnd : noDupStringsBool (plan.map Prod.fst) = true)
    (p p' : String × EntryPlacement) (hp : p ∈ plan) (hp' : p' ∈ plan)
    (hps : p.2.isInlineScope = true) (hps' : p'.2.isInlineScope = false) :
    p.1 ≠ p'.1 := by
  intro heq
  have hnd' := (noDupStringsBool_iff_nodup _).mp hnd
  clear hnd
  induction plan with
  | nil => cases hp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd'
    rcases List.mem_cons.mp hp with rfl | hpxs <;> rcases List.mem_cons.mp hp' with rfl | hp'xs
    · rw [hps] at hps'; cases hps'
    · exact hnd'.1 (heq ▸ List.mem_map.mpr ⟨p', hp'xs, rfl⟩)
    · exact hnd'.1 (heq.symm ▸ List.mem_map.mpr ⟨p, hpxs, rfl⟩)
    · exact ih hpxs hp'xs hnd'.2

private abbrev RenderPlanP1 (numApi : NumParseApi) (n : Nat) : Prop :=
  ∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
      (revPairs : List (String × String)) (lines : List String),
      sizeOf remPlan ≤ n →
      revPairs ≠ [] →
      (∀ p ∈ revPairs, ∃ ks, renderKey p.1 ks = some p.2) →
      noDupStringsBool (remPlan.map Prod.fst) = true →
      (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
      renderDottedList (revPairs.map Prod.snd) origEntries remPlan = some lines →
      ∀ (startRoot : List (String × Node)) (parentPath : List String)
        (parentLoc : List (String × Node)) (rbParent : List (String × Node) → List (String × Node))
        (subLoc : List (String × Node)) (rbDotted : List (String × Node) → List (String × Node)),
        AtLocalPath startRoot parentPath parentLoc rbParent →
        DottedWriteFocus parentLoc (revPairs.reverse.map Prod.fst) subLoc rbDotted →
        (∀ p ∈ remPlan, assocLookupNode p.1 subLoc = none) →
        ∀ (restChars : List Char) (fuel : Nat),
          fuel ≥ lines.length →
          ∃ finalSubLoc,
            (∀ p ∈ remPlan, ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
              assocLookupNode p.1 finalSubLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
            (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalSubLoc = assocLookupNode q subLoc) ∧
            ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
            (remPlan = [] → lines = [] ∧ finalSubLoc = subLoc ∧
              parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
              parseDocumentFuel numApi (fuel - lines.length) restChars parentPath startRoot) ∧
            (remPlan ≠ [] →
              parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
              parseDocumentFuel numApi (fuel - lines.length) restChars
                parentPath (rbParent (rbDotted finalSubLoc)))

private abbrev RenderPlanP2 (numApi : NumParseApi) (n : Nat) : Prop :=
  ∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
      (revRen : List String) (lines : List String),
      sizeOf remPlan ≤ n →
      noDupStringsBool (remPlan.map Prod.fst) = true →
      (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
      renderInlineEntries revRen origEntries remPlan = some lines →
      ∀ (root : List (String × Node)) (curPath : List String)
        (startLoc : List (String × Node)) (rb : List (String × Node) → List (String × Node)),
        AtLocalPath root curPath startLoc rb →
        (∀ p ∈ remPlan, p.2.isInlineScope = true → assocLookupNode p.1 startLoc = none) →
        ∀ (restChars : List Char) (fuel : Nat),
          fuel ≥ lines.length →
          ∃ finalLoc,
            (∀ p ∈ remPlan, p.2.isInlineScope = true →
              ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
            (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 finalLoc = assocLookupNode p.1 startLoc) ∧
            (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
            ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
            parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) curPath root =
            parseDocumentFuel numApi (fuel - lines.length) restChars curPath (rb finalLoc)

private abbrev RenderPlanP3 (numApi : NumParseApi) (n : Nat) : Prop :=
  ∀ (elemPlans : List (List (String × EntryPlacement))) (xs : List TomlValue)
      (pathPairs : List (String × String)) (k rk : String) (rc : String) (lines : List String),
      sizeOf elemPlans ≤ n →
      (∃ ks, renderKey k ks = some rk) →
      (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
      (∃ comment, renderCommentSuffix comment = some rc) →
      renderAotElems (rk :: pathPairs.reverse.map Prod.snd) rc xs elemPlans = some lines →
      ∀ (root : List (String × Node)) (parentLoc : List (String × Node))
        (rbParent : List (String × Node) → List (String × Node))
        (prevElems : List (List (String × Node))) (startActivePath : List String),
        AtHeaderFocus root (pathPairs.map Prod.fst) parentLoc rbParent →
        ((prevElems = [] ∧ assocLookupNode k parentLoc = none) ∨
         (prevElems ≠ [] ∧ assocLookupNode k parentLoc = some (.aot prevElems))) →
        ∀ (restChars : List Char) (fuel : Nat),
          fuel ≥ lines.length →
          ∃ finalElems endActivePath,
            (xs = [] → finalElems = prevElems ∧ lines = [] ∧ endActivePath = startActivePath) ∧
            (xs ≠ [] → lines ≠ [] ∧
              ∃ tailElems, finalElems = prevElems ++ tailElems ∧ tailElems ≠ [] ∧
                TomlListEquiv xs (aotElemsToToml tailElems) ∧
                AtLocalPath (rbParent (assocSetNode k (.aot finalElems) parentLoc))
                  (pathPairs.map Prod.fst) (assocSetNode k (.aot finalElems) parentLoc) rbParent) ∧
            ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
            (xs ≠ [] →
              parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
              parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath
                (rbParent (assocSetNode k (.aot finalElems) parentLoc)))

private abbrev RenderPlanP4 (numApi : NumParseApi) (n : Nat) : Prop :=
  ∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
      (pathPairs : List (String × String)) (lines : List String),
      sizeOf remPlan ≤ n →
      (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
      noDupStringsBool (remPlan.map Prod.fst) = true →
      (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
      renderSectionEntries (pathPairs.reverse.map Prod.snd) origEntries remPlan = some lines →
      ∀ (root : List (String × Node)) (startLoc : List (String × Node))
        (rb : List (String × Node) → List (String × Node)) (startActivePath : List String),
        AtHeaderFocus root (pathPairs.map Prod.fst) startLoc rb →
        (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 startLoc = none) →
        ∀ (restChars : List Char) (fuel : Nat),
          fuel ≥ lines.length →
          ∃ finalLoc endActivePath,
            (remPlan.any (fun p => !p.2.isInlineScope) = false →
              lines = [] ∧ finalLoc = startLoc ∧ endActivePath = startActivePath ∧
              parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
              parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath root) ∧
            (remPlan.any (fun p => !p.2.isInlineScope) = true →
              lines ≠ [] ∧
              (∀ p ∈ remPlan, p.2.isInlineScope = false →
                ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                  assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
              (∀ q, (∀ p ∈ remPlan, p.2.isInlineScope = false → q ≠ p.1) →
                assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
              AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
              parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
              parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc)) ∧
            ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true

private abbrev RenderPlanP5 (numApi : NumParseApi) (n : Nat) : Prop :=
  ∀ (origEntries : List (String × TomlValue)) (plan : List (String × EntryPlacement))
      (pathPairs : List (String × String)) (lines : List String),
      sizeOf plan + 1 ≤ n →
      (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
      renderTablePlan (pathPairs.reverse.map Prod.snd) origEntries plan = some lines →
      ∀ (root : List (String × Node)) (startLoc : List (String × Node))
        (rb : List (String × Node) → List (String × Node)),
        AtLocalPath root (pathPairs.map Prod.fst) startLoc rb →
        startLoc = [] →
        ∀ (restChars : List Char) (fuel : Nat),
          fuel ≥ lines.length →
          ∃ finalLoc endActivePath,
            TomlTableEquivList origEntries (entriesToTomlList finalLoc) ∧
            AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
            ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
            parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars)
              (pathPairs.map Prod.fst) root =
            parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc)

private abbrev RenderPlanAll (numApi : NumParseApi) (n : Nat) : Prop :=
  RenderPlanP1 numApi n ∧ RenderPlanP2 numApi n ∧
    RenderPlanP3 numApi n ∧ RenderPlanP4 numApi n ∧ RenderPlanP5 numApi n

private theorem renderPlan_dot_step (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) :
    RenderPlanP1 numApi n := by
      intro origEntries remPlan revPairs lines hsz hrev_ne hrev_keys hnd_rem hmem_rem hdl
        startRoot parentPath parentLoc rbParent subLoc rbDotted hAt hDotFocus hfresh restChars fuel hf
      cases remPlan with
      | nil =>
        simp only [renderDottedList, Option.some.injEq] at hdl
        subst hdl
        exact ⟨subLoc, (fun p hp => by cases hp), (fun _ _ => rfl), rfl,
          (fun _ => ⟨rfl, rfl, by simp [joinLines]⟩), (fun hne => absurd rfl hne)⟩
      | cons hd tl =>
        rcases hd with ⟨k, ep⟩
        simp only [renderDottedList] at hdl
        cases hlk : lookupKeyList k origEntries with
        | none => simp [hlk] at hdl
        | some v =>
          simp only [hlk] at hdl
          have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
          have hnd_tl : noDupStringsBool (tl.map Prod.fst) = true := by
            simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true] at hnd_rem
            exact hnd_rem.2
          have hnot_tl : k ∉ tl.map Prod.fst := by
            simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd_rem
            intro hmem; have hc : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr hmem
            rw [hc] at hnd_rem; cases hnd_rem.1
          have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v :=
            fun p hp => hmem_rem p (by simp [hp])
          cases htail_res : renderDottedList (revPairs.map Prod.snd) origEntries tl with
          | none =>
            cases ep <;> simp [htail_res] at hdl
            · cases v <;> cases hdl
          | some tailLines =>
            cases ep with
            | tableSection _ _ _ _ | aotSection _ _ _ => simp at hdl
            | direct ks vt comment =>
              simp only [bind, Option.bind] at hdl
              cases hrk : renderKey k ks with
              | none => simp [hrk] at hdl
              | some rk =>
                cases hrv : renderValueInline v vt with
                | none => simp [hrk, hrv] at hdl
                | some rv =>
                  cases hrc : renderCommentSuffix comment with
                  | none => simp [hrk, hrv, hrc] at hdl
                  | some rc =>
                    simp only [hrk, hrv, hrc, htail_res, Option.some.injEq] at hdl
                    subst hdl
                    let pairs := ((k, rk) :: revPairs).reverse
                    have hpairs_ne : pairs ≠ [] := by simp [pairs]
                    have hpairs_keys : ∀ p ∈ pairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                      intro p hp
                      simp only [pairs, List.reverse_cons, List.mem_append, List.mem_reverse, List.mem_singleton] at hp
                      rcases hp with h | h
                      · exact hrev_keys p h
                      · rw [h]; exact ⟨ks, hrk⟩
                    have hpairs_fst : pairs.map Prod.fst = revPairs.reverse.map Prod.fst ++ [k] := by
                      simp [pairs, List.reverse_cons, List.map_append]
                    have hpairs_snd : pairs.map Prod.snd = (rk :: revPairs.map Prod.snd).reverse := by
                      simp [pairs, List.reverse_cons, List.map_append]
                    have hline_eq : joinRenderedPath (rk :: revPairs.map Prod.snd).reverse ++ " = " ++ rv ++ rc =
                        joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc := by
                      rw [hpairs_snd]
                    let line := joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc
                    have hf1 : fuel ≥ 1 := by simp at hf; omega
                    obtain ⟨v', heqv, hline_cl, hstep⟩ :=
                      parseDocumentFuel_assign_step numApi hInt hFloat pairs hpairs_ne hpairs_keys
                        v vt rv hrv comment rc hrc parentPath startRoot
                        ((joinLines tailLines).toList ++ restChars) fuel hf1
                    let midSubLoc := assocSetNode k (valueToInlineNode v') subLoc
                    have hnone_k : assocLookupNode k subLoc = none := hfresh (k, .direct ks vt comment) (by simp)
                    have hins_sub : insertDottedEntries (parentPath ++ pairs.map Prod.fst) subLoc [k] (valueToInlineNode v') =
                        .ok midSubLoc := by
                      simp [insertDottedEntries, hnone_k, midSubLoc]
                    have hins_parent : insertDottedEntries (parentPath ++ pairs.map Prod.fst) parentLoc
                        (pairs.map Prod.fst) (valueToInlineNode v') = .ok (rbDotted midSubLoc) := by
                      rw [hpairs_fst] at hins_sub ⊢
                      exact dottedWriteFocus_insert hDotFocus _ [k] (by simp) (valueToInlineNode v') midSubLoc hins_sub
                    have hins_root : insertAtActivePath (parentPath ++ pairs.map Prod.fst)
                        startRoot parentPath (pairs.map Prod.fst) (valueToInlineNode v') =
                        .ok (rbParent (rbDotted midSubLoc)) :=
                      atLocalPath_insertAtActivePath hAt _ _ _ _ hins_parent
                    have hAt_mid : AtLocalPath (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent :=
                      atLocalPath_rebuild hAt (rbDotted midSubLoc)
                    have hDot_mid : DottedWriteFocus (rbDotted midSubLoc) (revPairs.reverse.map Prod.fst) midSubLoc rbDotted :=
                      dottedWriteFocus_rebuild hDotFocus midSubLoc
                    have hfresh_tl : ∀ p ∈ tl, assocLookupNode p.1 midSubLoc = none := by
                      intro p hp
                      have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                      rw [assocLookupNode_assocSetNode_ne k p.1 _ subLoc hne]
                      exact hfresh p (by simp [hp])
                    have hih_tl := (ih (sizeOf tl) hsz_tl).1 origEntries tl revPairs tailLines (Nat.le_refl _)
                      hrev_ne hrev_keys hnd_tl hmem_tl htail_res
                      (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent midSubLoc rbDotted
                      hAt_mid hDot_mid hfresh_tl restChars (fuel - 1) (by simp at hf; omega)
                    rcases hih_tl with ⟨finalSubLoc, htl_match, htl_rest, htl_cl, htl_nil, htl_cons⟩
                    have hparse_fin : parseDocumentFuel numApi fuel ((joinLines ([line] ++ tailLines)).toList ++ restChars) parentPath startRoot =
                        parseDocumentFuel numApi (fuel - ([line] ++ tailLines).length) restChars
                          parentPath (rbParent (rbDotted finalSubLoc)) := by
                      have hjoin_eq : (joinLines ([line] ++ tailLines)).toList ++ restChars =
                          line.toList ++ ('\n' :: ((joinLines tailLines).toList ++ restChars)) := by
                        simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                      rw [hjoin_eq, hstep (rbParent (rbDotted midSubLoc)) hins_root]
                      cases tl with
                      | nil =>
                        obtain ⟨_, hfin_eq, hparse0⟩ := htl_nil rfl
                        rw [hfin_eq, hparse0]
                        simp [Nat.sub_sub, Nat.add_comm]
                      | cons _ _ =>
                        rw [htl_cons (by simp)]
                        simp [Nat.sub_sub, Nat.add_comm]
                    refine ⟨finalSubLoc, ?_, ?_, ?_, (fun hnil => by cases hnil), fun _ => ?_⟩
                    · intro p hp
                      simp only [List.mem_cons] at hp
                      rcases hp with rfl | hptl
                      · refine ⟨v, valueToInlineNode v', hlk, ?_, ?_⟩
                        · rw [htl_rest k hnot_tl]
                          simp [midSubLoc, assocLookupNode_assocSetNode]
                        · simpa [nodeToTomlValue_valueToInlineNode] using heqv
                      · exact htl_match p hptl
                    · intro q hq_not
                      have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                      have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                      rw [htl_rest q hnot_tl']
                      exact assocLookupNode_assocSetNode_ne k q _ subLoc hne_k
                    · rw [hline_eq, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append]
                      exact Bool.and_eq_true_iff.mpr ⟨joinLines_singleton_clean _ hline_cl, htl_cl⟩
                    · rw [hline_eq]
                      simpa using hparse_fin
            | dotted ks subPlan =>
              cases v with
              | table sub =>
                by_cases hemp : sub.isEmpty = true
                · simp [hemp] at hdl
                · simp only [hemp, Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at hdl
                  cases hrk : renderKey k ks with
                  | none => simp [hrk] at hdl
                  | some rk =>
                    simp only [hrk] at hdl
                    cases hsub_lines : renderDottedSub (rk :: revPairs.map Prod.snd) sub.toList subPlan with
                    | none => simp [hsub_lines] at hdl
                    | some subLines =>
                      simp [hsub_lines, htail_res] at hdl
                      subst hdl
                      simp only [renderDottedSub] at hsub_lines
                      split at hsub_lines
                      · cases hsub_lines
                      · rename_i hperm_neg
                        have hperm : isPlanPermutation sub.toList subPlan = true := by
                          cases h : isPlanPermutation sub.toList subPlan
                          · exfalso; exact hperm_neg (by simp [h])
                          · rfl
                        obtain ⟨_, hnd_sub, hmem_sub, hcov_sub⟩ := isPlanPermutation_props hperm
                        have hsub_ne_list : sub.toList ≠ [] := by
                          intro heq
                          have hnil : sub = #[] := Array.toList_eq_nil_iff.mp heq
                          subst hnil
                          exact absurd rfl hemp
                        have hsubPlan_ne : subPlan ≠ [] := by
                          intro hnil
                          cases hsub_ne_cons : sub.toList with
                          | nil => exact hsub_ne_list hsub_ne_cons
                          | cons hd_s _ =>
                            obtain ⟨ep0, hep0⟩ := hcov_sub hd_s.1 hd_s.2 (by simp [hsub_ne_cons, lookupKeyList])
                            rw [hnil] at hep0; cases hep0
                        have hsz_sub : sizeOf subPlan < n := by simp +arith at hsz; omega
                        have hrev_sub_ne : (k, rk) :: revPairs ≠ [] := by simp
                        have hrev_sub_keys : ∀ p ∈ (k, rk) :: revPairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                          intro p hp
                          rcases List.mem_cons.mp hp with rfl | h
                          · exact ⟨ks, hrk⟩
                          · exact hrev_keys p h
                        have hnone_k : assocLookupNode k subLoc = none := hfresh (k, .dotted ks subPlan) (by simp)
                        let rbSubDot := fun newSub => rbDotted (assocSetNode k (.table .dotted newSub) subLoc)
                        have hDot_sub : DottedWriteFocus parentLoc (((k, rk) :: revPairs).reverse.map Prod.fst) [] rbSubDot := by
                          simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
                          exact dottedWriteFocus_step hDotFocus k hnone_k
                        have hf_sub : fuel - subLines.length ≥ tailLines.length := by
                          simp only [List.length_append] at hf; omega
                        have hih_sub := (ih (sizeOf subPlan) hsz_sub).1 sub.toList subPlan ((k, rk) :: revPairs) subLines
                          (Nat.le_refl _) hrev_sub_ne hrev_sub_keys hnd_sub hmem_sub hsub_lines
                          startRoot parentPath parentLoc rbParent [] rbSubDot
                          hAt hDot_sub (fun _ _ => rfl) ((joinLines tailLines).toList ++ restChars) fuel
                          (by simp only [List.length_append] at hf; omega)
                        rcases hih_sub with ⟨finalChildSub, hsub_match, hsub_rest, hsub_cl, _, hsub_parse⟩
                        let midSubLoc := assocSetNode k (.table .dotted finalChildSub) subLoc
                        have hAt_mid : AtLocalPath (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent :=
                          atLocalPath_rebuild hAt (rbDotted midSubLoc)
                        have hDot_mid : DottedWriteFocus (rbDotted midSubLoc) (revPairs.reverse.map Prod.fst) midSubLoc rbDotted :=
                          dottedWriteFocus_rebuild hDotFocus midSubLoc
                        have hfresh_tl : ∀ p ∈ tl, assocLookupNode p.1 midSubLoc = none := by
                          intro p hp
                          have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                          rw [assocLookupNode_assocSetNode_ne k p.1 _ subLoc hne]
                          exact hfresh p (by simp [hp])
                        have hih_tl := (ih (sizeOf tl) hsz_tl).1 origEntries tl revPairs tailLines (Nat.le_refl _)
                          hrev_ne hrev_keys hnd_tl hmem_tl htail_res
                          (rbParent (rbDotted midSubLoc)) parentPath (rbDotted midSubLoc) rbParent midSubLoc rbDotted
                          hAt_mid hDot_mid hfresh_tl restChars (fuel - subLines.length) hf_sub
                        rcases hih_tl with ⟨finalSubLoc, htl_match, htl_rest, htl_cl, htl_nil, htl_cons⟩
                        refine ⟨finalSubLoc, ?_, ?_, ?_, (fun hnil => by cases hnil), fun _ => ?_⟩
                        · intro p hp
                          simp only [List.mem_cons] at hp
                          rcases hp with rfl | hptl
                          · refine ⟨.table sub, .table .dotted finalChildSub, hlk, ?_, ?_⟩
                            · rw [htl_rest k hnot_tl]
                              simp [midSubLoc, assocLookupNode_assocSetNode]
                            · have hsub_only : ∀ q, q ∉ subPlan.map Prod.fst → assocLookupNode q finalChildSub = none :=
                                fun q hq => hsub_rest q hq
                              have heqv_sub := entriesToTomlList_of_plan_match sub.toList subPlan hperm finalChildSub hsub_match hsub_only
                              simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                          · exact htl_match p hptl
                        · intro q hq_not
                          have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                          have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                          rw [htl_rest q hnot_tl']
                          exact assocLookupNode_assocSetNode_ne k q _ subLoc hne_k
                        · rw [joinLines_append, String.toList_append, List.all_append]
                          exact Bool.and_eq_true_iff.mpr ⟨hsub_cl, htl_cl⟩
                        · rw [joinLines_append, String.toList_append, List.append_assoc, hsub_parse hsubPlan_ne]
                          change parseDocumentFuel numApi (fuel - subLines.length)
                              ((joinLines tailLines).toList ++ restChars) parentPath (rbParent (rbDotted midSubLoc)) =
                            parseDocumentFuel numApi (fuel - (subLines ++ tailLines).length) restChars
                              parentPath (rbParent (rbDotted finalSubLoc))
                          cases tl with
                          | nil =>
                            obtain ⟨_, hfin_eq, hparse0⟩ := htl_nil rfl
                            rw [hfin_eq, hparse0]
                            simp [List.length_append, Nat.sub_sub]
                          | cons _ _ =>
                            rw [htl_cons (by simp)]
                            simp [List.length_append, Nat.sub_sub]
              | _ => simp at hdl

private theorem renderPlan_inl_step (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) (hDot : RenderPlanP1 numApi n) :
    RenderPlanP2 numApi n := by
      intro origEntries remPlan revRen lines hsz hnd_rem hmem_rem hrie
        root curPath startLoc rb hAt hfresh restChars fuel hf
      cases remPlan with
      | nil =>
        simp only [renderInlineEntries, Option.some.injEq] at hrie
        subst hrie
        refine ⟨startLoc, (fun p hp => by cases hp), (fun p hp => by cases hp), (fun _ _ => rfl), rfl, ?_⟩
        rw [atLocalPath_self hAt]
        simp [joinLines]
      | cons hd tl =>
        rcases hd with ⟨k, ep⟩
        simp only [renderInlineEntries, bind, Option.bind] at hrie
        have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
        have hnd_tl : noDupStringsBool (tl.map Prod.fst) = true := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true] at hnd_rem
          exact hnd_rem.2
        have hnot_tl : k ∉ tl.map Prod.fst := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd_rem
          intro hmem; have hc : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr hmem
          rw [hc] at hnd_rem; cases hnd_rem.1
        have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v :=
          fun p hp => hmem_rem p (by simp [hp])
        by_cases hsc : ep.isInlineScope = true
        · simp only [hsc, Bool.not_true] at hrie
          cases hlk : lookupKeyList k origEntries with
          | none => simp [hlk] at hrie
          | some v =>
            simp only [hlk] at hrie
            cases ep with
            | tableSection _ _ _ _ | aotSection _ _ _ => simp [EntryPlacement.isInlineScope] at hsc
            | direct ks vt comment =>
              cases hrk : renderKey k ks with
              | none => simp [hrk] at hrie
              | some rk =>
                cases hrv : renderValueInline v vt with
                | none => simp [hrk, hrv] at hrie
                | some rv =>
                  cases hrc : renderCommentSuffix comment with
                  | none => simp [hrk, hrv, hrc] at hrie
                  | some rc =>
                    simp only [hrk, hrv, hrc] at hrie
                    cases htail_res : renderInlineEntries revRen origEntries tl with
                    | none => simp [htail_res] at hrie
                    | some tailLines =>
                      simp [htail_res] at hrie
                      subst hrie
                      let pairs := [(k, rk)]
                      have hpairs_ne : pairs ≠ [] := by simp [pairs]
                      have hpairs_keys : ∀ p ∈ pairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                        intro p hp; simp only [pairs, List.mem_singleton] at hp; rw [hp]; exact ⟨ks, hrk⟩
                      have hf1 : fuel ≥ 1 := by simp at hf; omega
                      obtain ⟨v', heqv, hline_cl, hstep⟩ :=
                        parseDocumentFuel_assign_step numApi hInt hFloat pairs hpairs_ne hpairs_keys
                          v vt rv hrv comment rc hrc curPath root
                          ((joinLines tailLines).toList ++ restChars) fuel hf1
                      let midLoc := assocSetNode k (valueToInlineNode v') startLoc
                      have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .direct ks vt comment) (by simp) hsc
                      have hins_loc : insertDottedEntries (curPath ++ [k]) startLoc [k] (valueToInlineNode v') = .ok midLoc := by
                        simp [insertDottedEntries, hnone_k, midLoc]
                      have hins_root : insertAtActivePath (curPath ++ pairs.map Prod.fst) root curPath (pairs.map Prod.fst)
                          (valueToInlineNode v') = .ok (rb midLoc) :=
                        atLocalPath_insertAtActivePath hAt (curPath ++ [k]) [k] (valueToInlineNode v') midLoc hins_loc
                      have hAt_mid : AtLocalPath (rb midLoc) curPath midLoc rb := atLocalPath_rebuild hAt midLoc
                      have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = true → assocLookupNode p.1 midLoc = none := by
                        intro p hp hps
                        have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                        rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                        exact hfresh p (by simp [hp]) hps
                      have hih_tl := (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen tailLines (Nat.le_refl _)
                        hnd_tl hmem_tl htail_res (rb midLoc) curPath midLoc rb hAt_mid hfresh_tl
                        restChars (fuel - 1) (by simp at hf; omega)
                      rcases hih_tl with ⟨finalLoc, htl_inl, htl_sec, htl_rest, htl_cl, htl_parse⟩
                      refine ⟨finalLoc, ?_, ?_, ?_, ?_, ?_⟩
                      · intro p hp hps
                        simp only [List.mem_cons] at hp
                        rcases hp with rfl | hptl
                        · refine ⟨v, valueToInlineNode v', hlk, ?_, ?_⟩
                          · rw [htl_rest k hnot_tl]
                            simp [midLoc, assocLookupNode_assocSetNode]
                          · simpa [nodeToTomlValue_valueToInlineNode] using heqv
                        · exact htl_inl p hptl hps
                      · intro p hp hps
                        simp only [List.mem_cons] at hp
                        rcases hp with rfl | hptl
                        · rw [hsc] at hps; cases hps
                        · have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hptl, rfl⟩)
                          rw [htl_sec p hptl hps]
                          exact assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne
                      · intro q hq_not
                        have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                        have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                        rw [htl_rest q hnot_tl']
                        exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                      · have hline_eq2 : rk ++ " = " ++ rv ++ rc =
                            joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc := rfl
                        rw [hline_eq2, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append]
                        exact Bool.and_eq_true_iff.mpr ⟨joinLines_singleton_clean _ hline_cl, htl_cl⟩
                      · have hjoin_eq : (joinLines ((rk ++ " = " ++ rv ++ rc) :: tailLines)).toList ++ restChars =
                            (joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc).toList ++
                              ('\n' :: ((joinLines tailLines).toList ++ restChars)) := by
                          simp [pairs, joinRenderedPath, joinLines, String.toList_append, List.cons_append, List.append_assoc]
                        rw [hjoin_eq, hstep (rb midLoc) hins_root, htl_parse]
                        simp [Nat.sub_sub, Nat.add_comm]
            | dotted ks subPlan =>
              cases v with
              | table sub =>
                by_cases hemp : sub.isEmpty = true
                · simp [hemp] at hrie
                · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hrie
                  cases hrk : renderKey k ks with
                  | none => simp [hrk] at hrie
                  | some rk =>
                    cases hsub_lines : renderDottedSub [rk] sub.toList subPlan with
                    | none => simp [hrk, hsub_lines] at hrie
                    | some subLines =>
                      simp only [hrk, hsub_lines] at hrie
                      cases htail_res : renderInlineEntries revRen origEntries tl with
                      | none => simp [htail_res] at hrie
                      | some tailLines =>
                        simp [htail_res] at hrie
                        subst hrie
                        simp only [renderDottedSub] at hsub_lines
                        split at hsub_lines
                        · cases hsub_lines
                        · rename_i hperm_neg
                          have hperm : isPlanPermutation sub.toList subPlan = true := by
                            cases h : isPlanPermutation sub.toList subPlan
                            · exfalso; exact hperm_neg (by simp [h])
                            · rfl
                          obtain ⟨_, hnd_sub, hmem_sub, hcov_sub⟩ := isPlanPermutation_props hperm
                          have hsub_ne_list : sub.toList ≠ [] := by
                            intro heq
                            have hnil : sub = #[] := Array.toList_eq_nil_iff.mp heq
                            subst hnil
                            exact absurd rfl hemp
                          have hsubPlan_ne : subPlan ≠ [] := by
                            intro hnil
                            cases hsub_ne_cons : sub.toList with
                            | nil => exact hsub_ne_list hsub_ne_cons
                            | cons hd_s _ =>
                              obtain ⟨ep0, hep0⟩ := hcov_sub hd_s.1 hd_s.2 (by simp [hsub_ne_cons, lookupKeyList])
                              rw [hnil] at hep0; cases hep0
                          have hsz_sub : sizeOf subPlan < n := by simp +arith at hsz; omega
                          have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .dotted ks subPlan) (by simp) hsc
                          let rbSubDot := fun newSub => assocSetNode k (.table .dotted newSub) startLoc
                          have hDot_sub : DottedWriteFocus startLoc ([(k, rk)].reverse.map Prod.fst) [] rbSubDot := by
                            simp only [List.reverse_singleton, List.map_cons, List.map_nil]
                            exact dottedWriteFocus_step (DottedWriteFocus.nil startLoc) k hnone_k
                          have hf_sub : fuel - subLines.length ≥ tailLines.length := by
                            simp only [List.length_append] at hf; omega
                          have hih_sub := hDot sub.toList subPlan [(k, rk)] subLines (by omega) (by simp)
                            (fun p hp => by simp only [List.mem_singleton] at hp; rw [hp]; exact ⟨ks, hrk⟩)
                            hnd_sub hmem_sub hsub_lines
                            root curPath startLoc rb [] rbSubDot hAt hDot_sub (fun _ _ => rfl)
                            ((joinLines tailLines).toList ++ restChars) fuel
                            (by simp only [List.length_append] at hf; omega)
                          rcases hih_sub with ⟨finalChildSub, hsub_match, hsub_rest, hsub_cl, _, hsub_parse⟩
                          let midLoc := assocSetNode k (.table .dotted finalChildSub) startLoc
                          have hAt_mid : AtLocalPath (rb midLoc) curPath midLoc rb := atLocalPath_rebuild hAt midLoc
                          have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = true → assocLookupNode p.1 midLoc = none := by
                            intro p hp hps
                            have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                            rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                            exact hfresh p (by simp [hp]) hps
                          have hih_tl := (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen tailLines (Nat.le_refl _)
                            hnd_tl hmem_tl htail_res (rb midLoc) curPath midLoc rb hAt_mid hfresh_tl
                            restChars (fuel - subLines.length) hf_sub
                          rcases hih_tl with ⟨finalLoc, htl_inl, htl_sec, htl_rest, htl_cl, htl_parse⟩
                          refine ⟨finalLoc, ?_, ?_, ?_, ?_, ?_⟩
                          · intro p hp hps
                            simp only [List.mem_cons] at hp
                            rcases hp with rfl | hptl
                            · refine ⟨.table sub, .table .dotted finalChildSub, hlk, ?_, ?_⟩
                              · rw [htl_rest k hnot_tl]
                                simp [midLoc, assocLookupNode_assocSetNode]
                              · have heqv_sub := entriesToTomlList_of_plan_match sub.toList subPlan hperm finalChildSub hsub_match hsub_rest
                                simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                            · exact htl_inl p hptl hps
                          · intro p hp hps
                            simp only [List.mem_cons] at hp
                            rcases hp with rfl | hptl
                            · rw [hsc] at hps; cases hps
                            · have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hptl, rfl⟩)
                              rw [htl_sec p hptl hps]
                              exact assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne
                          · intro q hq_not
                            have hne_k : q ≠ k := fun heq => hq_not (by simp [heq])
                            have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
                            rw [htl_rest q hnot_tl']
                            exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                          · rw [joinLines_append, String.toList_append, List.all_append]
                            exact Bool.and_eq_true_iff.mpr ⟨hsub_cl, htl_cl⟩
                          · rw [joinLines_append, String.toList_append, List.append_assoc, hsub_parse hsubPlan_ne]
                            change parseDocumentFuel numApi (fuel - subLines.length)
                                ((joinLines tailLines).toList ++ restChars) curPath (rb midLoc) = _
                            rw [htl_parse]
                            simp [List.length_append, Nat.sub_sub]
              | _ => cases hrie
        · have hsc_false : ep.isInlineScope = false := by
            cases h : ep.isInlineScope
            · rfl
            · exact absurd h hsc
          simp only [hsc_false, Bool.not_false, ↓reduceIte] at hrie
          cases htail_res : renderInlineEntries revRen origEntries tl with
          | none => simp [htail_res] at hrie
          | some tailLines =>
            simp only [htail_res, Option.some.injEq, List.nil_append] at hrie
            subst hrie
            have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = true → assocLookupNode p.1 startLoc = none :=
              fun p hp hps => hfresh p (by simp [hp]) hps
            have hih_tl := (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen tailLines (Nat.le_refl _)
              hnd_tl hmem_tl htail_res root curPath startLoc rb hAt hfresh_tl restChars fuel hf
            rcases hih_tl with ⟨finalLoc, htl_inl, htl_sec, htl_rest, htl_cl, htl_parse⟩
            refine ⟨finalLoc, ?_, ?_, ?_, htl_cl, htl_parse⟩
            · intro p hp hps
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hptl
              · rw [hsc_false] at hps; cases hps
              · exact htl_inl p hptl hps
            · intro p hp hps
              simp only [List.mem_cons] at hp
              rcases hp with rfl | hptl
              · exact htl_rest k hnot_tl
              · exact htl_sec p hptl hps
            · intro q hq_not
              have hnot_tl' : q ∉ tl.map Prod.fst := fun hm => hq_not (by simp [hm])
              exact htl_rest q hnot_tl'

private theorem renderPlan_aot_step (numApi : NumParseApi)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) :
    RenderPlanP3 numApi n := by
      intro elemPlans xs pathPairs k rk rc lines hsz hk hpath hrc_ex hrae
        root parentLoc rbParent prevElems startActivePath hFocus hprev restChars fuel hf
      rcases hrc_ex with ⟨comment, hrc⟩
      cases xs with
      | nil =>
        cases elemPlans with
        | cons _ _ => simp [renderAotElems] at hrae
        | nil =>
          simp only [renderAotElems, Option.some.injEq] at hrae
          subst hrae
          refine ⟨prevElems, startActivePath, fun _ => ⟨rfl, rfl, rfl⟩, fun hne => absurd rfl hne, rfl, fun hne => absurd rfl hne⟩
      | cons elemVal xs' =>
        cases elemPlans with
        | nil => simp [renderAotElems] at hrae
        | cons ep eps =>
          cases elemVal with
          | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
            simp [renderAotElems] at hrae
          | table elem =>
            simp only [renderAotElems, bind, Option.bind] at hrae
            cases hbody : renderTablePlan (rk :: (pathPairs.map Prod.snd).reverse) elem.toList ep with
            | none =>
              rw [← List.map_reverse] at hbody
              simp only [List.map_reverse] at hrae
              rw [← List.map_reverse] at hrae
              simp only [hbody] at hrae; cases hrae
            | some bodyLines =>
              cases htail : renderAotElems (rk :: (pathPairs.map Prod.snd).reverse) rc xs' eps with
              | none =>
                rw [← List.map_reverse] at hbody htail
                simp only [List.map_reverse] at hrae
                rw [← List.map_reverse] at hrae
                simp only [hbody, htail] at hrae; cases hrae
              | some tailLines =>
                rw [← List.map_reverse] at hbody htail
                simp only [List.map_reverse] at hrae
                rw [← List.map_reverse] at hrae
                simp only [hbody, htail, Option.some.injEq] at hrae
                subst hrae
                let nextPairs := pathPairs ++ [(k, rk)]
                have hnext_ne : nextPairs ≠ [] := by simp [nextPairs]
                have hnext_keys : ∀ p ∈ nextPairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                  intro p hp
                  simp only [nextPairs, List.mem_append, List.mem_singleton] at hp
                  rcases hp with h | h
                  · exact hpath p h
                  · rw [h]; exact hk
                have hnext_fst : nextPairs.map Prod.fst = pathPairs.map Prod.fst ++ [k] := by
                  simp [nextPairs, List.map_append]
                have hnext_rev : nextPairs.reverse.map Prod.snd = rk :: pathPairs.reverse.map Prod.snd := by
                  simp [nextPairs]
                let elemsMid := prevElems ++ [[]]
                let midParentLoc := assocSetNode k (.aot elemsMid) parentLoc
                have happ_loc : applyAotHeader (nextPairs.map Prod.fst) parentLoc [k] = .ok midParentLoc := by
                  rcases hprev with ⟨rfl, hnone_k⟩ | ⟨_, hsome_k⟩
                  · simp [applyAotHeader, hnone_k, midParentLoc, elemsMid]
                  · simp [applyAotHeader, hsome_k, midParentLoc, elemsMid]
                have happ_root : applyAotHeader (nextPairs.map Prod.fst) root (nextPairs.map Prod.fst) = .ok (rbParent midParentLoc) := by
                  have h := atHeaderFocus_applyAotHeader hFocus (nextPairs.map Prod.fst) [k] (by simp) midParentLoc happ_loc
                  rwa [← hnext_fst] at h
                have hf1 : fuel ≥ 1 := by simp at hf; omega
                obtain ⟨hhdr_cl, hhdr_parse⟩ :=
                  parseDocumentFuel_aot_step numApi nextPairs hnext_ne hnext_keys comment rc hrc
                    startActivePath root (rbParent midParentLoc) happ_root
                    ((joinLines (bodyLines ++ tailLines)).toList ++ restChars) fuel hf1
                have hhdr_eq : "[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc =
                    "[[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]]" ++ rc := by
                  rw [← hnext_rev]; simp
                let rbElem := fun newElem => rbParent (assocSetNode k (.aot (prevElems ++ [newElem])) parentLoc)
                have hAt_midParent : AtLocalPath (rbParent midParentLoc) (pathPairs.map Prod.fst) midParentLoc rbParent :=
                  atHeaderFocus_step hFocus midParentLoc
                have hlk_mid : assocLookupNode k midParentLoc = some (.aot elemsMid) := by
                  simp [midParentLoc, assocLookupNode_assocSetNode]
                have hAt_elem0 : AtLocalPath (rbParent midParentLoc) (nextPairs.map Prod.fst) [] rbElem := by
                  rw [hnext_fst]
                  have hstep := atLocalPath_stepAot hAt_midParent k elemsMid [] (by simp [elemsMid]) (getLast?_append_singleton prevElems []) hlk_mid
                  have hrb_eq : (fun nl => rbParent (assocSetNode k (.aot (elemsMid.dropLast ++ [nl])) midParentLoc)) = rbElem := by
                    funext nl
                    simp only [elemsMid, dropLast_append_singleton, midParentLoc, assocSetNode_idem, rbElem]
                  rwa [hrb_eq] at hstep
                have hsz_ep : sizeOf ep + 1 < n := by
                  cases eps <;> simp +arith at hsz <;> omega
                have hsz_eps : sizeOf eps < n := by simp +arith at hsz; omega
                have hih_ep := (ih (sizeOf ep + 1) hsz_ep).2.2.2.2 elem.toList ep nextPairs bodyLines (Nat.le_refl _) hnext_keys
                  (by rw [hnext_rev]; exact hbody) (rbParent midParentLoc) [] rbElem hAt_elem0 rfl
                  ((joinLines tailLines).toList ++ restChars) (fuel - 1) (by simp only [List.length_cons, List.length_append] at hf; omega)
                rcases hih_ep with ⟨finalElem, midActivePath, heqv_elem, hAt_finalElem, hbody_cl, hbody_parse⟩
                let parentLoc' := assocSetNode k (.aot (prevElems ++ [finalElem])) parentLoc
                have hAt_parent' : AtLocalPath (rbParent parentLoc') (pathPairs.map Prod.fst) parentLoc' rbParent :=
                  atHeaderFocus_step hFocus parentLoc'
                have hlk_parent' : assocLookupNode k parentLoc' = some (.aot (prevElems ++ [finalElem])) := by
                  simp [parentLoc', assocLookupNode_assocSetNode]
                have hih_tail := (ih (sizeOf eps) hsz_eps).2.2.1 eps xs' pathPairs k rk rc tailLines (Nat.le_refl _)
                  hk hpath ⟨comment, hrc⟩ htail (rbParent parentLoc') parentLoc' rbParent (prevElems ++ [finalElem])
                  midActivePath (AtHeaderFocus.exact hAt_parent') (Or.inr ⟨by simp, hlk_parent'⟩)
                  restChars (fuel - 1 - bodyLines.length) (by simp only [List.length_cons, List.length_append] at hf; omega)
                rcases hih_tail with ⟨finalElems, endActivePath, hxs_nil, hxs_cons, htail_cl, htail_parse⟩
                have hcl_all : ((joinLines (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) ::
                    bodyLines ++ tailLines)).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
                  rw [List.cons_append, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append,
                    joinLines_append, String.toList_append, List.all_append]
                  have h1 : ((joinLines ["[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc]).toList.all
                      fun c => !isDisallowedControl c && c != '\r') = true := by
                    rw [hhdr_eq]
                    exact joinLines_singleton_clean _ hhdr_cl
                  exact Bool.and_eq_true_iff.mpr ⟨h1, Bool.and_eq_true_iff.mpr ⟨hbody_cl, htail_cl⟩⟩
                cases xs' with
                | nil =>
                  obtain ⟨rfl, rfl, hact_eq⟩ := hxs_nil rfl
                  refine ⟨prevElems ++ [finalElem], endActivePath, (fun hne => by cases hne), ?_, hcl_all, ?_⟩
                  · intro _
                    refine ⟨by simp, [finalElem], rfl, by simp, ?_, hAt_parent'⟩
                    simpa [aotElemsToToml, TomlListEquiv, TomlEquiv] using heqv_elem
                  · intro _
                    have hjoin_eq : (joinLines (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) ::
                        bodyLines ++ [])).toList ++ restChars =
                        ("[[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]]" ++ rc).toList ++
                          ('\n' :: ((joinLines (bodyLines ++ [])).toList ++ restChars)) := by
                      rw [hhdr_eq]; simp [List.cons_append, joinLines, String.toList_append, List.append_assoc]
                    rw [hjoin_eq, hhdr_parse]
                    simp only [List.append_nil, hact_eq]
                    simpa [joinLines, List.append_nil, rbElem, parentLoc', Nat.sub_sub, Nat.add_comm] using hbody_parse
                | cons _ _ =>
                  obtain ⟨_, tailElems2, hfin_eq, _, heqv_tail, _⟩ := hxs_cons (by simp)
                  have htail_eq2 : finalElems = prevElems ++ (finalElem :: tailElems2) := by
                    rw [hfin_eq, List.append_assoc]; rfl
                  have hAt_final : AtLocalPath (rbParent (assocSetNode k (.aot finalElems) parentLoc))
                      (pathPairs.map Prod.fst) (assocSetNode k (.aot finalElems) parentLoc) rbParent :=
                    atHeaderFocus_step hFocus (assocSetNode k (.aot finalElems) parentLoc)
                  have hrb_idem : rbParent (assocSetNode k (.aot finalElems) parentLoc') =
                      rbParent (assocSetNode k (.aot finalElems) parentLoc) := by
                    simp only [parentLoc', assocSetNode_idem]
                  refine ⟨finalElems, endActivePath, (fun hne => by cases hne), ?_, hcl_all, ?_⟩
                  · intro _
                    refine ⟨by simp, finalElem :: tailElems2, htail_eq2, by simp, ?_, hAt_final⟩
                    simp only [aotElemsToToml, TomlListEquiv, TomlEquiv]
                    exact ⟨heqv_elem, heqv_tail⟩
                  · intro _
                    have hjoin_eq : (joinLines (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) ::
                        bodyLines ++ tailLines)).toList ++ restChars =
                        ("[[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]]" ++ rc).toList ++
                          ('\n' :: ((joinLines (bodyLines ++ tailLines)).toList ++ restChars)) := by
                      rw [hhdr_eq]; simp [List.cons_append, joinLines, String.toList_append, List.append_assoc]
                    rw [hjoin_eq, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hbody_parse]
                    rw [htail_parse (by simp), hrb_idem]
                    rw [show fuel - 1 - bodyLines.length - tailLines.length =
                        fuel - (("[[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]]" ++ rc) :: bodyLines ++ tailLines).length by
                      simp only [List.length_cons, List.length_append]; omega]

private theorem renderPlan_sec_step (numApi : NumParseApi)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) :
    RenderPlanP4 numApi n := by
      intro origEntries remPlan pathPairs lines hsz hpath hnd_rem hmem_rem hrse
        root startLoc rb startActivePath hFocus hfresh restChars fuel hf
      cases remPlan with
      | nil =>
        simp only [renderSectionEntries, Option.some.injEq] at hrse
        subst hrse
        exact ⟨startLoc, startActivePath, fun _ => ⟨rfl, rfl, rfl, by simp [joinLines]⟩, fun h => by simp at h, rfl⟩
      | cons hd tl =>
        rcases hd with ⟨k, ep⟩
        simp only [renderSectionEntries, bind, Option.bind] at hrse
        have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
        have hnd_tl : noDupStringsBool (tl.map Prod.fst) = true := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true] at hnd_rem
          exact hnd_rem.2
        have hnot_tl : k ∉ tl.map Prod.fst := by
          simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd_rem
          intro hmem; have hc : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr hmem
          rw [hc] at hnd_rem; cases hnd_rem.1
        have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v :=
          fun p hp => hmem_rem p (by simp [hp])
        by_cases hsc : ep.isInlineScope = true
        · simp only [hsc, ↓reduceIte] at hrse
          cases htail_res : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
          | none =>
            rw [← List.map_reverse] at htail_res
            simp only [List.map_reverse] at hrse
            rw [← List.map_reverse] at hrse
            simp only [htail_res] at hrse
            cases hrse
          | some tailLines =>
            rw [← List.map_reverse] at htail_res
            simp only [List.map_reverse] at hrse
            rw [← List.map_reverse] at hrse
            simp only [htail_res, Option.some.injEq] at hrse
            subst hrse
            have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 startLoc = none :=
              fun p hp hps => hfresh p (by simp [hp]) hps
            have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
              hpath hnd_tl hmem_tl htail_res root startLoc rb startActivePath hFocus hfresh_tl restChars fuel hf
            rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
            refine ⟨finalLoc, endActivePath, ?_, ?_, htl_cl⟩
            · intro hnone
              have hnone_tl : tl.any (fun p => !p.2.isInlineScope) = false := by
                simpa [hsc] using hnone
              exact htl_false hnone_tl
            · intro hsome
              have hsome_tl : tl.any (fun p => !p.2.isInlineScope) = true := by
                simpa [hsc] using hsome
              obtain ⟨htl_ne, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true hsome_tl
              refine ⟨htl_ne, ?_, ?_, htl_At, htl_parse⟩
              · intro p hp hps
                simp only [List.mem_cons] at hp
                rcases hp with rfl | hptl
                · rw [hsc] at hps; cases hps
                · exact htl_match p hptl hps
              · intro q hq
                exact htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)
        · have hsc_false : ep.isInlineScope = false := by
            cases h : ep.isInlineScope
            · rfl
            · exact absurd h hsc
          simp only [hsc_false, Bool.false_eq_true, ↓reduceIte] at hrse
          cases hlk : lookupKeyList k origEntries with
          | none => simp [hlk] at hrse
          | some v =>
            simp only [hlk] at hrse
            cases ep with
            | direct _ _ _ | dotted _ _ => simp [EntryPlacement.isInlineScope] at hsc_false
            | tableSection ks subtableFirst subPlan comment =>
              cases v with
              | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
                simp at hrse
              | table sub =>
                cases hrk : renderKey k ks with
                | none => simp [hrk] at hrse
                | some rk =>
                  cases hrc : renderCommentSuffix comment with
                  | none => simp [hrk, hrc] at hrse
                  | some rc =>
                    simp only [hrk, hrc] at hrse
                    let nextPairs := pathPairs ++ [(k, rk)]
                    have hnext_ne : nextPairs ≠ [] := by simp [nextPairs]
                    have hnext_keys : ∀ p ∈ nextPairs, ∃ ks', renderKey p.1 ks' = some p.2 := by
                      intro p hp
                      simp only [nextPairs, List.mem_append, List.mem_singleton] at hp
                      rcases hp with h | h
                      · exact hpath p h
                      · rw [h]; exact ⟨ks, hrk⟩
                    have hnext_fst : nextPairs.map Prod.fst = pathPairs.map Prod.fst ++ [k] := by
                      simp [nextPairs, List.map_append]
                    have hnext_rev : nextPairs.reverse.map Prod.snd = rk :: pathPairs.reverse.map Prod.snd := by
                      simp [nextPairs]
                    have hhdr_eq : "[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc =
                        "[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc := by
                      rw [← hnext_rev]; simp
                    have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .tableSection ks subtableFirst subPlan comment) (by simp) hsc_false
                    cases subtableFirst with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte] at hrse
                      cases hbody : renderTablePlan (rk :: (pathPairs.map Prod.snd).reverse) sub.toList subPlan with
                      | none =>
                        rw [← List.map_reverse] at hbody
                        simp only [List.map_reverse] at hrse
                        rw [← List.map_reverse] at hrse
                        simp only [hbody] at hrse
                        cases hrse
                      | some bodyLines =>
                        cases htail : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
                        | none =>
                          rw [← List.map_reverse] at hbody htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hbody, htail] at hrse
                          cases hrse
                        | some tailLines =>
                          rw [← List.map_reverse] at hbody htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hbody, htail, Option.some.injEq] at hrse
                          subst hrse
                          let midParentLoc := assocSetNode k (.table .explicit []) startLoc
                          have happ_loc : applyTableHeader (nextPairs.map Prod.fst) startLoc [k] = .ok midParentLoc := by
                            simp [applyTableHeader, hnone_k, midParentLoc]
                          have happ_root : applyTableHeader (nextPairs.map Prod.fst) root (nextPairs.map Prod.fst) = .ok (rb midParentLoc) := by
                            have h := atHeaderFocus_applyTableHeader hFocus (nextPairs.map Prod.fst) [k] (by simp) midParentLoc happ_loc
                            rwa [← hnext_fst] at h
                          have hf1 : fuel ≥ 1 := by simp at hf; omega
                          obtain ⟨hhdr_cl, hhdr_parse⟩ :=
                            parseDocumentFuel_table_step numApi nextPairs hnext_ne hnext_keys comment rc hrc
                              startActivePath root (rb midParentLoc) happ_root
                              ((joinLines (bodyLines ++ tailLines)).toList ++ restChars) fuel hf1
                          let rbSub := fun newSub => rb (assocSetNode k (.table .explicit newSub) startLoc)
                          have hAt_midParent : AtLocalPath (rb midParentLoc) (pathPairs.map Prod.fst) midParentLoc rb :=
                            atHeaderFocus_step hFocus midParentLoc
                          have hlk_mid : assocLookupNode k midParentLoc = some (.table .explicit []) := by
                            simp [midParentLoc, assocLookupNode_assocSetNode]
                          have hAt_sub0 : AtLocalPath (rb midParentLoc) (nextPairs.map Prod.fst) [] rbSub := by
                            have hrb_eq : (fun newSub => rb (assocSetNode k (.table .explicit newSub) midParentLoc)) = rbSub := by
                              funext newSub; simp [rbSub, midParentLoc, assocSetNode_idem]
                            rw [hnext_fst, ← hrb_eq]
                            exact atLocalPath_stepTable hAt_midParent k .explicit [] (by decide) hlk_mid
                          have hsz_sub : sizeOf subPlan + 1 < n := by simp +arith at hsz; omega
                          have hih_sub := (ih (sizeOf subPlan + 1) hsz_sub).2.2.2.2 sub.toList subPlan nextPairs bodyLines (Nat.le_refl _)
                            hnext_keys (by rw [hnext_rev]; exact hbody) (rb midParentLoc) [] rbSub hAt_sub0 rfl
                            ((joinLines tailLines).toList ++ restChars) (fuel - 1) (by simp only [List.length_cons, List.length_append] at hf; omega)
                          rcases hih_sub with ⟨finalSubLoc, midActivePath, heqv_sub, _, hbody_cl, hbody_parse⟩
                          let midLoc := assocSetNode k (.table .explicit finalSubLoc) startLoc
                          have hAt_midLoc : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb :=
                            atHeaderFocus_step hFocus midLoc
                          have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none := by
                            intro p hp hps
                            have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                            rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                            exact hfresh p (by simp [hp]) hps
                          have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
                            hpath hnd_tl hmem_tl htail (rb midLoc) midLoc rb midActivePath (AtHeaderFocus.exact hAt_midLoc) hfresh_tl
                            restChars (fuel - 1 - bodyLines.length) (by simp only [List.length_cons, List.length_append] at hf; omega)
                          rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
                          have hcl_all : ((joinLines ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ tailLines)).toList.all
                              fun c => !isDisallowedControl c && c != '\r') = true := by
                            rw [List.cons_append, ← List.singleton_append, joinLines_append, String.toList_append, List.all_append,
                              joinLines_append, String.toList_append, List.all_append]
                            have h1 : ((joinLines ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc]).toList.all
                                fun c => !isDisallowedControl c && c != '\r') = true := by
                              rw [hhdr_eq]
                              exact joinLines_singleton_clean _ hhdr_cl
                            exact Bool.and_eq_true_iff.mpr ⟨h1, Bool.and_eq_true_iff.mpr ⟨hbody_cl, htl_cl⟩⟩
                          by_cases htl_any : tl.any (fun p => !p.2.isInlineScope) = true
                          · obtain ⟨_, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true htl_any
                            have htl_pres_k : assocLookupNode k finalLoc = assocLookupNode k midLoc :=
                              htl_pres k (fun p hp _ heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))
                            refine ⟨finalLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp, ?_, ?_, htl_At, ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                · rw [htl_pres_k]; simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                              · exact htl_match p hptl hps
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .tableSection ks false subPlan comment) (by simp) hsc_false
                              rw [htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)]
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · have hjoin_eq : (joinLines ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ tailLines)).toList ++ restChars =
                                  ("[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc).toList ++
                                    ('\n' :: ((joinLines (bodyLines ++ tailLines)).toList ++ restChars)) := by
                                rw [hhdr_eq]; simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                              rw [hjoin_eq, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hbody_parse, htl_parse]
                              rw [show fuel - 1 - bodyLines.length - tailLines.length =
                                  fuel - ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ tailLines).length by
                                simp only [List.length_cons, List.length_append]; omega]
                          · have htl_any_f : tl.any (fun p => !p.2.isInlineScope) = false := by
                              cases h : tl.any (fun p => !p.2.isInlineScope)
                              · rfl
                              · exact absurd h htl_any
                            obtain ⟨rfl, rfl, rfl, htl_parse0⟩ := htl_false htl_any_f
                            refine ⟨midLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp, ?_, ?_, hAt_midLoc, ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                · simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                              · have : (tl.any (fun p => !p.2.isInlineScope)) = true := List.any_eq_true.mpr ⟨p, hptl, by simp [hps]⟩
                                rw [htl_any_f] at this; cases this
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .tableSection ks false subPlan comment) (by simp) hsc_false
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · have hjoin_eq : (joinLines ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ [])).toList ++ restChars =
                                  ("[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc).toList ++
                                    ('\n' :: ((joinLines (bodyLines ++ [])).toList ++ restChars)) := by
                                rw [hhdr_eq]; simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                              rw [hjoin_eq, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hbody_parse, htl_parse0]
                              rw [show fuel - 1 - bodyLines.length - ([] : List String).length =
                                  fuel - ((("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: bodyLines) ++ []).length by
                                simp only [List.length_cons, List.length_append, List.length_nil]; omega]
                    | true =>
                      simp only [↓reduceIte] at hrse
                      split at hrse
                      · cases hrse
                      · split at hrse
                        · cases hrse
                        · rename_i hperm_neg hall_neg
                          have hperm : isPlanPermutation sub.toList subPlan = true := by
                            cases h : isPlanPermutation sub.toList subPlan with
                            | true => rfl
                            | false => exfalso; exact hperm_neg (by simp [h])
                          have hany_sub : subPlan.any (fun p => !p.2.isInlineScope) = true := by
                            cases h : subPlan.any (fun p => !p.2.isInlineScope) with
                            | true => rfl
                            | false =>
                              exfalso; apply hall_neg
                              rw [List.any_eq_false] at h
                              simp only [List.all_eq_true]
                              intro p hp
                              have hnp := h p hp
                              cases hpi : p.2.isInlineScope with
                              | true => rfl
                              | false => exfalso; exact hnp (by simp [hpi])
                          obtain ⟨_, hnd_sub, hmem_sub, _⟩ := isPlanPermutation_props hperm
                          cases hsec_sub : renderSectionEntries (rk :: (pathPairs.map Prod.snd).reverse) sub.toList subPlan with
                          | none =>
                            rw [← List.map_reverse] at hsec_sub
                            simp only [List.map_reverse] at hrse
                            rw [← List.map_reverse] at hrse
                            simp only [hsec_sub] at hrse
                            cases hrse
                          | some secLines =>
                            cases hinl_sub : renderInlineEntries (rk :: (pathPairs.map Prod.snd).reverse) sub.toList subPlan with
                            | none =>
                              rw [← List.map_reverse] at hsec_sub hinl_sub
                              simp only [List.map_reverse] at hrse
                              rw [← List.map_reverse] at hrse
                              simp only [hsec_sub, hinl_sub] at hrse
                              cases hrse
                            | some inlLines =>
                              cases htail : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
                              | none =>
                                rw [← List.map_reverse] at hsec_sub hinl_sub htail
                                simp only [List.map_reverse] at hrse
                                rw [← List.map_reverse] at hrse
                                simp only [hsec_sub, hinl_sub, htail] at hrse
                                cases hrse
                              | some tailLines =>
                                rw [← List.map_reverse] at hsec_sub hinl_sub htail
                                simp only [List.map_reverse] at hrse
                                rw [← List.map_reverse] at hrse
                                simp only [hsec_sub, hinl_sub, htail, Option.some.injEq] at hrse
                                subst hrse
                                let rbImp := fun newSub => rb (assocSetNode k (.table .subtableImplicit newSub) startLoc)
                                have hFocus_sub : AtHeaderFocus root (nextPairs.map Prod.fst) [] rbImp := by
                                  rw [hnext_fst]
                                  exact AtHeaderFocus.implicitNone hFocus hnone_k
                                have hsz_sub : sizeOf subPlan < n := by simp +arith at hsz; omega
                                have hf_sec : fuel ≥ secLines.length := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                have hih_sec := (ih (sizeOf subPlan) hsz_sub).2.2.2.1 sub.toList subPlan nextPairs secLines
                                  (Nat.le_refl _) hnext_keys hnd_sub hmem_sub (by rw [hnext_rev]; exact hsec_sub)
                                  root [] rbImp startActivePath hFocus_sub (fun _ _ _ => rfl)
                                  ((joinLines (["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++
                                    inlLines ++ tailLines)).toList ++ restChars) fuel hf_sec
                                rcases hih_sec with ⟨midSubLoc, midActivePath1, _, hsec_true, hsec_cl⟩
                                obtain ⟨hsec_ne, hsec_match, hsec_pres, hAt_midSub, hsec_parse⟩ := hsec_true hany_sub
                                let midParentImp := assocSetNode k (.table .subtableImplicit midSubLoc) startLoc
                                let midParentExp := assocSetNode k (.table .explicit midSubLoc) startLoc
                                have happ_loc : applyTableHeader (nextPairs.map Prod.fst) midParentImp [k] = .ok midParentExp := by
                                  have hlk_imp : assocLookupNode k midParentImp = some (.table .subtableImplicit midSubLoc) := by
                                    simp [midParentImp, assocLookupNode_assocSetNode]
                                  simp [applyTableHeader, hlk_imp, midParentExp, midParentImp, assocSetNode_idem]
                                have hAt_imp : AtLocalPath (rbImp midSubLoc) (pathPairs.map Prod.fst) midParentImp rb :=
                                  atHeaderFocus_step hFocus midParentImp
                                have happ_root : applyTableHeader (nextPairs.map Prod.fst) (rbImp midSubLoc) (nextPairs.map Prod.fst) = .ok (rb midParentExp) := by
                                  have h := atLocalPath_applyTableHeader hAt_imp (nextPairs.map Prod.fst) [k] (by simp) midParentExp happ_loc
                                  rwa [← hnext_fst] at h
                                have hf_hdr : fuel - secLines.length ≥ 1 := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                obtain ⟨hhdr_cl, hhdr_parse⟩ :=
                                  parseDocumentFuel_table_step numApi nextPairs hnext_ne hnext_keys comment rc hrc
                                    midActivePath1 (rbImp midSubLoc) (rb midParentExp) happ_root
                                    ((joinLines (inlLines ++ tailLines)).toList ++ restChars) (fuel - secLines.length) hf_hdr
                                let rbExp := fun newSub => rb (assocSetNode k (.table .explicit newSub) startLoc)
                                have hAt_exp0 : AtLocalPath (rb midParentExp) (nextPairs.map Prod.fst) midSubLoc rbExp := by
                                  have hAt_exp_p : AtLocalPath (rb midParentExp) (pathPairs.map Prod.fst) midParentExp rb :=
                                    atHeaderFocus_step hFocus midParentExp
                                  have hlk_exp : assocLookupNode k midParentExp = some (.table .explicit midSubLoc) := by
                                    simp [midParentExp, assocLookupNode_assocSetNode]
                                  have hrb_eq : (fun newSub => rb (assocSetNode k (.table .explicit newSub) midParentExp)) = rbExp := by
                                    funext newSub; simp [rbExp, midParentExp, assocSetNode_idem]
                                  rw [hnext_fst, ← hrb_eq]
                                  exact atLocalPath_stepTable hAt_exp_p k .explicit midSubLoc (by decide) hlk_exp
                                have hfresh_inl : ∀ p ∈ subPlan, p.2.isInlineScope = true → assocLookupNode p.1 midSubLoc = none := by
                                  intro p hp hps
                                  have hq : ∀ p' ∈ subPlan, p'.2.isInlineScope = false → p.1 ≠ p'.1 :=
                                    fun p' hp' hps' => nodup_key_ne_of_scope subPlan hnd_sub p p' hp hp' hps hps'
                                  rw [hsec_pres p.1 hq]
                                  rfl
                                have hf_inl : fuel - secLines.length - 1 ≥ inlLines.length := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                have hih_inl := (ih (sizeOf subPlan) hsz_sub).2.1 sub.toList subPlan (rk :: pathPairs.reverse.map Prod.snd) inlLines
                                  (Nat.le_refl _) hnd_sub hmem_sub hinl_sub (rb midParentExp) (nextPairs.map Prod.fst) midSubLoc rbExp
                                  hAt_exp0 hfresh_inl ((joinLines tailLines).toList ++ restChars) (fuel - secLines.length - 1) hf_inl
                                rcases hih_inl with ⟨finalSubLoc, hinl_match, hinl_sec, hinl_rest, hinl_cl, hinl_parse⟩
                                have heqv_sub : TomlTableEquivList sub.toList (entriesToTomlList finalSubLoc) := by
                                  apply entriesToTomlList_of_plan_match sub.toList subPlan hperm finalSubLoc
                                  · intro p hp
                                    by_cases hp_in : p.2.isInlineScope = true
                                    · exact hinl_match p hp hp_in
                                    · have hp_f : p.2.isInlineScope = false := by
                                        cases h : p.2.isInlineScope with
                                        | false => rfl
                                        | true => exact absurd h hp_in
                                      obtain ⟨v_s, nd_s, hv_s, hnd_s, heqv_s⟩ := hsec_match p hp hp_f
                                      refine ⟨v_s, nd_s, hv_s, ?_, heqv_s⟩
                                      rw [hinl_sec p hp hp_f]
                                      exact hnd_s
                                  · intro q hq_not
                                    rw [hinl_rest q hq_not]
                                    rw [hsec_pres q (fun p hp _ => fun heq => hq_not (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]
                                    rfl
                                let midLoc := assocSetNode k (.table .explicit finalSubLoc) startLoc
                                have hAt_midLoc : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb :=
                                  atHeaderFocus_step hFocus midLoc
                                have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none := by
                                  intro p hp hps
                                  have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                                  rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                                  exact hfresh p (by simp [hp]) hps
                                have hf_tail : fuel - secLines.length - 1 - inlLines.length ≥ tailLines.length := by
                                  simp only [List.length_append, List.length_singleton] at hf; omega
                                have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
                                  hpath hnd_tl hmem_tl htail (rb midLoc) midLoc rb (nextPairs.map Prod.fst)
                                  (AtHeaderFocus.exact hAt_midLoc) hfresh_tl restChars (fuel - secLines.length - 1 - inlLines.length) hf_tail
                                rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
                                have hcl_all : ((joinLines ((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++ inlLines) ++ tailLines)).toList.all
                                    fun c => !isDisallowedControl c && c != '\r') = true := by
                                  rw [joinLines_append, joinLines_append, joinLines_append, String.toList_append, String.toList_append, String.toList_append,
                                    List.all_append, List.all_append, List.all_append]
                                  have h1hdr : ((joinLines ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc]).toList.all
                                      fun c => !isDisallowedControl c && c != '\r') = true := by
                                    rw [hhdr_eq]
                                    exact joinLines_singleton_clean _ hhdr_cl
                                  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hsec_cl, h1hdr⟩, hinl_cl⟩, htl_cl⟩
                                have hparse_sub : parseDocumentFuel numApi fuel
                                    ((joinLines (((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc]) ++ inlLines) ++ tailLines)).toList ++ restChars)
                                    startActivePath root =
                                    parseDocumentFuel numApi (fuel - secLines.length - 1 - inlLines.length)
                                      ((joinLines tailLines).toList ++ restChars) (nextPairs.map Prod.fst) (rb midLoc) := by
                                  rw [List.append_assoc secLines ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] inlLines,
                                    List.append_assoc secLines _ tailLines, joinLines_append, String.toList_append, List.append_assoc, hsec_parse]
                                  simp only [List.singleton_append]
                                  rw [List.cons_append]
                                  have hmid2 : (joinLines (("[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc) :: (inlLines ++ tailLines))).toList ++ restChars =
                                      ("[" ++ joinRenderedPath (nextPairs.map Prod.snd) ++ "]" ++ rc).toList ++
                                        ('\n' :: ((joinLines (inlLines ++ tailLines)).toList ++ restChars)) := by
                                    rw [hhdr_eq]; simp [joinLines, String.toList_append, List.cons_append, List.append_assoc]
                                  rw [hmid2, hhdr_parse, joinLines_append, String.toList_append, List.append_assoc, hinl_parse]
                                by_cases htl_any : tl.any (fun p => !p.2.isInlineScope) = true
                                · obtain ⟨_, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true htl_any
                                  have htl_pres_k : assocLookupNode k finalLoc = assocLookupNode k midLoc :=
                                    htl_pres k (fun p hp _ heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))
                                  refine ⟨finalLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                                  intro _
                                  refine ⟨by simp [hsec_ne], ?_, ?_, htl_At, ?_⟩
                                  · intro p hp hps
                                    simp only [List.mem_cons] at hp
                                    rcases hp with rfl | hptl
                                    · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                      · rw [htl_pres_k]; simp [midLoc, assocLookupNode_assocSetNode]
                                      · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                                    · exact htl_match p hptl hps
                                  · intro q hq
                                    have hne_k : q ≠ k := hq (k, .tableSection ks true subPlan comment) (by simp) hsc_false
                                    rw [htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)]
                                    exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                                  · rw [hparse_sub, htl_parse]
                                    rw [show fuel - secLines.length - 1 - inlLines.length - tailLines.length =
                                        fuel - ((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++ inlLines) ++ tailLines).length by
                                      simp only [List.length_append, List.length_singleton]; omega]
                                · have htl_any_f : tl.any (fun p => !p.2.isInlineScope) = false := by
                                    cases h : tl.any (fun p => !p.2.isInlineScope)
                                    · rfl
                                    · exact absurd h htl_any
                                  obtain ⟨rfl, rfl, rfl, htl_parse0⟩ := htl_false htl_any_f
                                  refine ⟨midLoc, nextPairs.map Prod.fst, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                                  intro _
                                  refine ⟨by simp [hsec_ne], ?_, ?_, hAt_midLoc, ?_⟩
                                  · intro p hp hps
                                    simp only [List.mem_cons] at hp
                                    rcases hp with rfl | hptl
                                    · refine ⟨.table sub, .table .explicit finalSubLoc, hlk, ?_, ?_⟩
                                      · simp [midLoc, assocLookupNode_assocSetNode]
                                      · simpa [nodeToTomlValue, TomlEquiv] using heqv_sub
                                    · have : (tl.any (fun p => !p.2.isInlineScope)) = true := List.any_eq_true.mpr ⟨p, hptl, by simp [hps]⟩
                                      rw [htl_any_f] at this; cases this
                                  · intro q hq
                                    have hne_k : q ≠ k := hq (k, .tableSection ks true subPlan comment) (by simp) hsc_false
                                    exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                                  · rw [hparse_sub, htl_parse0]
                                    rw [show fuel - secLines.length - 1 - inlLines.length - ([] : List String).length =
                                        fuel - ((secLines ++ ["[" ++ joinRenderedPath (rk :: pathPairs.reverse.map Prod.snd).reverse ++ "]" ++ rc] ++ inlLines) ++ []).length by
                                      simp only [List.length_append, List.length_singleton, List.length_nil]; omega]
            | aotSection ks elemPlans comment =>
              cases v with
              | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | table _ =>
                simp at hrse
              | array xs =>
                by_cases hemp : xs.isEmpty = true
                · simp [hemp] at hrse
                · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hrse
                  cases hrk : renderKey k ks with
                  | none => simp [hrk] at hrse
                  | some rk =>
                    cases hrc : renderCommentSuffix comment with
                    | none => simp [hrk, hrc] at hrse
                    | some rc =>
                      cases haot : renderAotElems (rk :: (pathPairs.map Prod.snd).reverse) rc xs.toList elemPlans with
                      | none =>
                        rw [← List.map_reverse] at haot
                        simp only [List.map_reverse] at hrse
                        rw [← List.map_reverse] at hrse
                        simp only [hrk, hrc, haot] at hrse
                        cases hrse
                      | some aotLines =>
                        cases htail : renderSectionEntries (pathPairs.map Prod.snd).reverse origEntries tl with
                        | none =>
                          rw [← List.map_reverse] at haot htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hrk, hrc, haot, htail] at hrse
                          cases hrse
                        | some tailLines =>
                          rw [← List.map_reverse] at haot htail
                          simp only [List.map_reverse] at hrse
                          rw [← List.map_reverse] at hrse
                          simp only [hrk, hrc, haot, htail, Option.some.injEq] at hrse
                          subst hrse
                          have hxs_ne : xs.toList ≠ [] := by
                            intro heq
                            have hnil : xs = #[] := Array.toList_eq_nil_iff.mp heq
                            subst hnil
                            exact absurd rfl hemp
                          have hnone_k : assocLookupNode k startLoc = none := hfresh (k, .aotSection ks elemPlans comment) (by simp) hsc_false
                          have hsz_ep : sizeOf elemPlans < n := by simp +arith at hsz; omega
                          have hf_aot : fuel ≥ aotLines.length := by simp only [List.length_append] at hf; omega
                          have hih_aot := (ih (sizeOf elemPlans) hsz_ep).2.2.1 elemPlans xs.toList pathPairs k rk rc aotLines
                            (Nat.le_refl _) ⟨ks, hrk⟩ hpath ⟨comment, hrc⟩ haot root startLoc rb [] startActivePath
                            hFocus (Or.inl ⟨rfl, hnone_k⟩) ((joinLines tailLines).toList ++ restChars) fuel hf_aot
                          rcases hih_aot with ⟨finalElems, midActivePath, _, haot_cons, haot_cl, haot_parse⟩
                          obtain ⟨haot_ne, tailElems, hfin_eq, htail_ne, heqv_aot, hAt_midLoc⟩ := haot_cons hxs_ne
                          rw [List.nil_append] at hfin_eq
                          let midLoc := assocSetNode k (.aot tailElems) startLoc
                          have hAt_midLoc' : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb := by
                            simpa [midLoc, ← hfin_eq] using hAt_midLoc
                          have hfresh_tl : ∀ p ∈ tl, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none := by
                            intro p hp hps
                            have hne : p.1 ≠ k := fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
                            rw [assocLookupNode_assocSetNode_ne k p.1 _ startLoc hne]
                            exact hfresh p (by simp [hp]) hps
                          have hf_tail : fuel - aotLines.length ≥ tailLines.length := by
                            simp only [List.length_append] at hf; omega
                          have hih_tl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl pathPairs tailLines (Nat.le_refl _)
                            hpath hnd_tl hmem_tl htail (rb midLoc) midLoc rb midActivePath (AtHeaderFocus.exact hAt_midLoc')
                            hfresh_tl restChars (fuel - aotLines.length) hf_tail
                          rcases hih_tl with ⟨finalLoc, endActivePath, htl_false, htl_true, htl_cl⟩
                          have hcl_all : ((joinLines (aotLines ++ tailLines)).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
                            rw [joinLines_append, String.toList_append, List.all_append]
                            exact Bool.and_eq_true_iff.mpr ⟨haot_cl, htl_cl⟩
                          by_cases htl_any : tl.any (fun p => !p.2.isInlineScope) = true
                          · obtain ⟨_, htl_match, htl_pres, htl_At, htl_parse⟩ := htl_true htl_any
                            have htl_pres_k : assocLookupNode k finalLoc = assocLookupNode k midLoc :=
                              htl_pres k (fun p hp _ heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))
                            refine ⟨finalLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp [haot_ne], ?_, ?_, htl_At, ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.array xs, .aot tailElems, hlk, ?_, ?_⟩
                                · rw [htl_pres_k]; simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_aot
                              · exact htl_match p hptl hps
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .aotSection ks elemPlans comment) (by simp) hsc_false
                              rw [htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)]
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · rw [joinLines_append, String.toList_append, List.append_assoc, haot_parse hxs_ne]
                              rw [show rb (assocSetNode k (.aot finalElems) startLoc) = rb midLoc by simp [midLoc, hfin_eq]]
                              rw [htl_parse]
                              simp [List.length_append, Nat.sub_sub]
                          · have htl_any_f : tl.any (fun p => !p.2.isInlineScope) = false := by
                              cases h : tl.any (fun p => !p.2.isInlineScope)
                              · rfl
                              · exact absurd h htl_any
                            obtain ⟨rfl, rfl, rfl, htl_parse0⟩ := htl_false htl_any_f
                            refine ⟨midLoc, endActivePath, (fun h => by simp [hsc_false] at h), ?_, hcl_all⟩
                            intro _
                            refine ⟨by simp [haot_ne], ?_, ?_, hAt_midLoc', ?_⟩
                            · intro p hp hps
                              simp only [List.mem_cons] at hp
                              rcases hp with rfl | hptl
                              · refine ⟨.array xs, .aot tailElems, hlk, ?_, ?_⟩
                                · simp [midLoc, assocLookupNode_assocSetNode]
                                · simpa [nodeToTomlValue, TomlEquiv] using heqv_aot
                              · have : (tl.any (fun p => !p.2.isInlineScope)) = true := List.any_eq_true.mpr ⟨p, hptl, by simp [hps]⟩
                                rw [htl_any_f] at this; cases this
                            · intro q hq
                              have hne_k : q ≠ k := hq (k, .aotSection ks elemPlans comment) (by simp) hsc_false
                              exact assocLookupNode_assocSetNode_ne k q _ startLoc hne_k
                            · rw [joinLines_append, String.toList_append, List.append_assoc, haot_parse hxs_ne]
                              rw [show rb (assocSetNode k (.aot finalElems) startLoc) = rb midLoc by simp [midLoc, hfin_eq]]
                              rw [htl_parse0]
                              rw [show fuel - aotLines.length - ([] : List String).length = fuel - (aotLines ++ []).length by
                                simp only [List.length_append, List.length_nil, Nat.add_zero, Nat.sub_zero]]

private theorem renderPlan_plan_step (numApi : NumParseApi)
    (n : Nat) (hInl : RenderPlanP2 numApi n) (hSec : RenderPlanP4 numApi n) :
    RenderPlanP5 numApi n := by
      intro origEntries plan pathPairs lines hsz hpath hrtp root startLoc rb hAt hstart restChars fuel hf
      subst hstart
      simp only [renderTablePlan] at hrtp
      split at hrtp
      · cases hrtp
      · rename_i hperm_neg
        have hperm : isPlanPermutation origEntries plan = true := by
          cases h : isPlanPermutation origEntries plan
          · exfalso; exact hperm_neg (by simp [h])
          · rfl
        obtain ⟨_, hnd_p, hmem_p, _⟩ := isPlanPermutation_props hperm
        simp only [bind, Option.bind] at hrtp
        cases hinl : renderInlineEntries (pathPairs.reverse.map Prod.snd) origEntries plan with
        | none =>
          simp only [hinl] at hrtp
          cases hrtp
        | some inlLines =>
          cases hsec : renderSectionEntries (pathPairs.reverse.map Prod.snd) origEntries plan with
          | none =>
            simp only [hinl, hsec] at hrtp
            cases hrtp
          | some secLines =>
            simp only [hinl, hsec, Option.some.injEq] at hrtp
            subst hrtp
            have hsz_lt : sizeOf plan < n := by omega
            have hf_inl : fuel ≥ inlLines.length := by simp only [List.length_append] at hf; omega
            have hih_inl := hInl origEntries plan (pathPairs.reverse.map Prod.snd) inlLines (Nat.le_of_lt hsz_lt)
              hnd_p hmem_p hinl root (pathPairs.map Prod.fst) [] rb hAt (fun _ _ _ => rfl)
              ((joinLines secLines).toList ++ restChars) fuel hf_inl
            rcases hih_inl with ⟨midLoc, hinl_match, hinl_sec, hinl_rest, hinl_cl, hinl_parse⟩
            have hAt_mid : AtLocalPath (rb midLoc) (pathPairs.map Prod.fst) midLoc rb :=
              atLocalPath_rebuild hAt midLoc
            have hfresh_sec : ∀ p ∈ plan, p.2.isInlineScope = false → assocLookupNode p.1 midLoc = none :=
              fun p hp hps => by rw [hinl_sec p hp hps]; rfl
            have hf_sec : fuel - inlLines.length ≥ secLines.length := by
              simp only [List.length_append] at hf; omega
            have hih_sec := hSec origEntries plan pathPairs secLines (Nat.le_of_lt hsz_lt) hpath hnd_p hmem_p hsec
              (rb midLoc) midLoc rb (pathPairs.map Prod.fst) (AtHeaderFocus.exact hAt_mid) hfresh_sec
              restChars (fuel - inlLines.length) hf_sec
            rcases hih_sec with ⟨finalLoc, endActivePath, hsec_false, hsec_true, hsec_cl⟩
            have hcl_all : ((joinLines (inlLines ++ secLines)).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
              rw [joinLines_append, String.toList_append, List.all_append]
              exact Bool.and_eq_true_iff.mpr ⟨hinl_cl, hsec_cl⟩
            by_cases hany : plan.any (fun p => !p.2.isInlineScope) = true
            · obtain ⟨_, hsec_match, hsec_pres, hAt_fin, hsec_parse⟩ := hsec_true hany
              have heqv : TomlTableEquivList origEntries (entriesToTomlList finalLoc) := by
                apply entriesToTomlList_of_plan_match origEntries plan hperm finalLoc
                · intro p hp
                  by_cases hp_in : p.2.isInlineScope = true
                  · obtain ⟨v, nd, hv, hnd, heqv⟩ := hinl_match p hp hp_in
                    refine ⟨v, nd, hv, ?_, heqv⟩
                    have hq : ∀ p' ∈ plan, p'.2.isInlineScope = false → p.1 ≠ p'.1 :=
                      fun p' hp' hps' => nodup_key_ne_of_scope plan hnd_p p p' hp hp' hp_in hps'
                    rw [hsec_pres p.1 hq]
                    exact hnd
                  · exact hsec_match p hp (by
                      cases h : p.2.isInlineScope
                      · rfl
                      · exact absurd h hp_in)
                · intro q hq_not
                  rw [hsec_pres q (fun p hp _ heq => hq_not (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]
                  exact hinl_rest q hq_not
              refine ⟨finalLoc, endActivePath, heqv, hAt_fin, hcl_all, ?_⟩
              rw [joinLines_append, String.toList_append, List.append_assoc, hinl_parse, hsec_parse]
              simp [List.length_append, Nat.sub_sub]
            · have hany_f : plan.any (fun p => !p.2.isInlineScope) = false := by
                cases h : plan.any (fun p => !p.2.isInlineScope)
                · rfl
                · exact absurd h hany
              obtain ⟨_, rfl, rfl, hsec_parse0⟩ := hsec_false hany_f
              have heqv : TomlTableEquivList origEntries (entriesToTomlList finalLoc) := by
                apply entriesToTomlList_of_plan_match origEntries plan hperm finalLoc
                · intro p hp
                  have hp_in : p.2.isInlineScope = true := by
                    by_cases h : p.2.isInlineScope = true
                    · exact h
                    · have : plan.any (fun p => !p.2.isInlineScope) = true := List.any_eq_true.mpr ⟨p, hp, by simp [h]⟩
                      rw [hany_f] at this; cases this
                  exact hinl_match p hp hp_in
                · exact hinl_rest
              refine ⟨finalLoc, pathPairs.map Prod.fst, heqv, hAt_mid, hcl_all, ?_⟩
              rw [joinLines_append, String.toList_append, List.append_assoc, hinl_parse, hsec_parse0]
              simp [List.length_append, Nat.sub_sub]

private theorem renderPlan_props_strong (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g) :
    ∀ n : Nat,
      (∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
          (revPairs : List (String × String)) (lines : List String),
          sizeOf remPlan ≤ n →
          revPairs ≠ [] →
          (∀ p ∈ revPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          noDupStringsBool (remPlan.map Prod.fst) = true →
          (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
          renderDottedList (revPairs.map Prod.snd) origEntries remPlan = some lines →
          ∀ (startRoot : List (String × Node)) (parentPath : List String)
            (parentLoc : List (String × Node)) (rbParent : List (String × Node) → List (String × Node))
            (subLoc : List (String × Node)) (rbDotted : List (String × Node) → List (String × Node)),
            AtLocalPath startRoot parentPath parentLoc rbParent →
            DottedWriteFocus parentLoc (revPairs.reverse.map Prod.fst) subLoc rbDotted →
            (∀ p ∈ remPlan, assocLookupNode p.1 subLoc = none) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalSubLoc,
                (∀ p ∈ remPlan, ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                  assocLookupNode p.1 finalSubLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
                (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalSubLoc = assocLookupNode q subLoc) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                (remPlan = [] → lines = [] ∧ finalSubLoc = subLoc ∧
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
                  parseDocumentFuel numApi (fuel - lines.length) restChars parentPath startRoot) ∧
                (remPlan ≠ [] →
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) parentPath startRoot =
                  parseDocumentFuel numApi (fuel - lines.length) restChars
                    parentPath (rbParent (rbDotted finalSubLoc)))) ∧
      (∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
          (revRen : List String) (lines : List String),
          sizeOf remPlan ≤ n →
          noDupStringsBool (remPlan.map Prod.fst) = true →
          (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
          renderInlineEntries revRen origEntries remPlan = some lines →
          ∀ (root : List (String × Node)) (curPath : List String)
            (startLoc : List (String × Node)) (rb : List (String × Node) → List (String × Node)),
            AtLocalPath root curPath startLoc rb →
            (∀ p ∈ remPlan, p.2.isInlineScope = true → assocLookupNode p.1 startLoc = none) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalLoc,
                (∀ p ∈ remPlan, p.2.isInlineScope = true →
                  ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                    assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
                (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 finalLoc = assocLookupNode p.1 startLoc) ∧
                (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) curPath root =
                parseDocumentFuel numApi (fuel - lines.length) restChars curPath (rb finalLoc)) ∧
      (∀ (elemPlans : List (List (String × EntryPlacement))) (xs : List TomlValue)
          (pathPairs : List (String × String)) (k rk : String) (rc : String) (lines : List String),
          sizeOf elemPlans ≤ n →
          (∃ ks, renderKey k ks = some rk) →
          (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          (∃ comment, renderCommentSuffix comment = some rc) →
          renderAotElems (rk :: pathPairs.reverse.map Prod.snd) rc xs elemPlans = some lines →
          ∀ (root : List (String × Node)) (parentLoc : List (String × Node))
            (rbParent : List (String × Node) → List (String × Node))
            (prevElems : List (List (String × Node))) (startActivePath : List String),
            AtHeaderFocus root (pathPairs.map Prod.fst) parentLoc rbParent →
            ((prevElems = [] ∧ assocLookupNode k parentLoc = none) ∨
             (prevElems ≠ [] ∧ assocLookupNode k parentLoc = some (.aot prevElems))) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalElems endActivePath,
                (xs = [] → finalElems = prevElems ∧ lines = [] ∧ endActivePath = startActivePath) ∧
                (xs ≠ [] → lines ≠ [] ∧
                  ∃ tailElems, finalElems = prevElems ++ tailElems ∧ tailElems ≠ [] ∧
                    TomlListEquiv xs (aotElemsToToml tailElems) ∧
                    AtLocalPath (rbParent (assocSetNode k (.aot finalElems) parentLoc))
                      (pathPairs.map Prod.fst) (assocSetNode k (.aot finalElems) parentLoc) rbParent) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                (xs ≠ [] →
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                  parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath
                    (rbParent (assocSetNode k (.aot finalElems) parentLoc)))) ∧
      (∀ (origEntries : List (String × TomlValue)) (remPlan : List (String × EntryPlacement))
          (pathPairs : List (String × String)) (lines : List String),
          sizeOf remPlan ≤ n →
          (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          noDupStringsBool (remPlan.map Prod.fst) = true →
          (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
          renderSectionEntries (pathPairs.reverse.map Prod.snd) origEntries remPlan = some lines →
          ∀ (root : List (String × Node)) (startLoc : List (String × Node))
            (rb : List (String × Node) → List (String × Node)) (startActivePath : List String),
            AtHeaderFocus root (pathPairs.map Prod.fst) startLoc rb →
            (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 startLoc = none) →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalLoc endActivePath,
                (remPlan.any (fun p => !p.2.isInlineScope) = false →
                  lines = [] ∧ finalLoc = startLoc ∧ endActivePath = startActivePath ∧
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                  parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath root) ∧
                (remPlan.any (fun p => !p.2.isInlineScope) = true →
                  lines ≠ [] ∧
                  (∀ p ∈ remPlan, p.2.isInlineScope = false →
                    ∃ v nd, lookupKeyList p.1 origEntries = some v ∧
                      assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
                  (∀ q, (∀ p ∈ remPlan, p.2.isInlineScope = false → q ≠ p.1) →
                    assocLookupNode q finalLoc = assocLookupNode q startLoc) ∧
                  AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
                  parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startActivePath root =
                  parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc)) ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true) ∧
      (∀ (origEntries : List (String × TomlValue)) (plan : List (String × EntryPlacement))
          (pathPairs : List (String × String)) (lines : List String),
          sizeOf plan + 1 ≤ n →
          (∀ p ∈ pathPairs, ∃ ks, renderKey p.1 ks = some p.2) →
          renderTablePlan (pathPairs.reverse.map Prod.snd) origEntries plan = some lines →
          ∀ (root : List (String × Node)) (startLoc : List (String × Node))
            (rb : List (String × Node) → List (String × Node)),
            AtLocalPath root (pathPairs.map Prod.fst) startLoc rb →
            startLoc = [] →
            ∀ (restChars : List Char) (fuel : Nat),
              fuel ≥ lines.length →
              ∃ finalLoc endActivePath,
                TomlTableEquivList origEntries (entriesToTomlList finalLoc) ∧
                AtLocalPath (rb finalLoc) (pathPairs.map Prod.fst) finalLoc rb ∧
                ((joinLines lines).toList.all fun c => !isDisallowedControl c && c != '\r') = true ∧
                parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars)
                  (pathPairs.map Prod.fst) root =
                parseDocumentFuel numApi (fuel - lines.length) restChars endActivePath (rb finalLoc)) := by
  change ∀ n : Nat, RenderPlanAll numApi n
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hDot := renderPlan_dot_step numApi hInt hFloat n ih
    have hInl := renderPlan_inl_step numApi hInt hFloat n ih hDot
    have hAot := renderPlan_aot_step numApi n ih
    have hSec := renderPlan_sec_step numApi n ih
    have hPlan := renderPlan_plan_step numApi n hInl hSec
    exact ⟨hDot, hInl, hAot, hSec, hPlan⟩

private theorem parseDocumentFuel_skipTrivia (numApi : NumParseApi) (f : Nat)
    (cs1 cs2 : List Char) (activePath : List String) (root : List (String × Node))
    (h : skipTriviaNewlines cs1 = skipTriviaNewlines cs2) :
    parseDocumentFuel numApi (f + 1) cs1 activePath root =
    parseDocumentFuel numApi (f + 1) cs2 activePath root := by
  unfold parseDocumentFuel
  rw [h]

/-- Any output accepted by `Model.render` parses back under `parseWithNum` to an equivalent `TomlTable` whenever integer and float models match. -/
theorem render_parse_roundTrip_model (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (doc : TomlTable) (tape : RenderTape) (out : String)
    (hrender : render doc tape = some out) :
    ∃ parsed, parseWithNum numApi out = .ok parsed ∧ TomlTableEquiv doc parsed := by
  simp only [render] at hrender
  split at hrender
  · cases hrender
  · rename_i hwf_neg
    simp only [bind, Option.bind] at hrender
    have hhdr_body : ∃ hdrLines bodyLines,
        ((hdrLines = [] ∧ tape.headerComment = none) ∨
         (∃ c, isSingleLineClean c = true ∧ tape.headerComment = some c ∧ hdrLines = ["#" ++ c])) ∧
        renderTablePlan [] doc.toList tape.entries = some bodyLines ∧
        out = String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n" := by
      cases hc : tape.headerComment with
      | none =>
        simp only [hc] at hrender
        cases hbody : renderTablePlan [] doc.toList tape.entries with
        | none => simp [hbody] at hrender
        | some bodyLines =>
          simp only [hbody, Option.some.injEq] at hrender
          exact ⟨[], bodyLines, Or.inl ⟨rfl, rfl⟩, rfl, hrender.symm⟩
      | some c =>
        simp only [hc] at hrender
        split at hrender
        · rename_i hc_clean
          cases hbody : renderTablePlan [] doc.toList tape.entries with
          | none => simp [hbody] at hrender
          | some bodyLines =>
            simp only [hbody, Option.some.injEq] at hrender
            exact ⟨["#" ++ c], bodyLines, Or.inr ⟨c, hc_clean, rfl, rfl⟩, rfl, hrender.symm⟩
        · cases hrender
    rcases hhdr_body with ⟨hdrLines, bodyLines, hhdr_cases, hbody, rfl⟩
    by_cases hall_empty : hdrLines ++ bodyLines = []
    · have hbody_e : bodyLines = [] := (List.append_eq_nil_iff.mp hall_empty).2
      have hplan := (renderPlan_props_strong numApi hInt hFloat (sizeOf tape.entries + 1)).2.2.2.2
        doc.toList tape.entries [] bodyLines (Nat.le_refl _) (fun _ h => by cases h)
        hbody [] [] id (AtLocalPath.nil []) rfl [] 1 (by simp [hbody_e])
      rcases hplan with ⟨finalLoc, _, heqv_list, _, _, hbody_parse⟩
      have hroot_eq : finalLoc = [] := by
        simp [hbody_e, joinLines, parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux] at hbody_parse
        exact hbody_parse
      have hnorm : normalizeChars 1 1 (String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n").toList = .ok ['\n'] := by
        have hstr : (String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n").toList = ['\n'] := by
          simp [hall_empty]
        rw [hstr]
        apply normalizeChars_clean
        decide
      have hp_doc : parseDocumentFuel numApi 2 ['\n'] [] [] = .ok [] := by
        simp [parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux]
      have hlen1 : (['\n'] : List Char).length + 1 = 2 := rfl
      refine ⟨(entriesToTomlList []).toArray, ?_, ?_⟩
      · simp only [parseWithNum, hnorm, bind, Except.bind]
        rw [hlen1, hp_doc]
      · rw [hroot_eq] at heqv_list
        simpa [TomlTableEquiv] using heqv_list
    · have hinter : String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n" = joinLines (hdrLines ++ bodyLines) :=
        intercalate_nl_append_nl (hdrLines ++ bodyLines) hall_empty
      let fullFuel := (joinLines (hdrLines ++ bodyLines)).toList.length + 1
      have hge_len : (joinLines (hdrLines ++ bodyLines)).toList.length ≥ bodyLines.length := by
        have h1 := joinLines_length_ge (hdrLines ++ bodyLines)
        simp only [List.length_append] at h1
        omega
      have hplan := (renderPlan_props_strong numApi hInt hFloat (sizeOf tape.entries + 1)).2.2.2.2
        doc.toList tape.entries [] bodyLines (Nat.le_refl _) (fun _ h => by cases h)
        hbody [] [] id (AtLocalPath.nil []) rfl [] fullFuel (by omega)
      rcases hplan with ⟨finalLoc, _, heqv_list, _, hbody_cl, hbody_parse⟩
      have hnorm_eq : normalizeChars 1 1 (joinLines (hdrLines ++ bodyLines)).toList =
          .ok (joinLines (hdrLines ++ bodyLines)).toList := by
        apply normalizeChars_clean
        rw [joinLines_append, String.toList_append, List.all_append]
        have hhdr_cl : ((joinLines hdrLines).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
          rcases hhdr_cases with ⟨rfl, _⟩ | ⟨c, hc_clean, _, rfl⟩
          · rfl
          · have hc' : (c.toList.all fun ch => !isDisallowedControl ch && ch != '\r') = true := by
              simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc_clean ⊢
              intro ch hch; exact ⟨(hc_clean ch hch).1.1, (hc_clean ch hch).2⟩
            simp [joinLines, List.all_append, hc', (by decide : isDisallowedControl '#' = false),
              (by decide : isDisallowedControl '\n' = false)]
        exact Bool.and_eq_true_iff.mpr ⟨hhdr_cl, hbody_cl⟩
      have hskip : skipTriviaNewlines (joinLines (hdrLines ++ bodyLines)).toList =
          skipTriviaNewlines (joinLines bodyLines).toList := by
        rcases hhdr_cases with ⟨rfl, _⟩ | ⟨c, hc_clean, _, rfl⟩
        · simp
        · simp only [List.cons_append, List.nil_append, joinLines]
          rw [String.toList_append]
          exact skipTriviaNewlines_comment_line c (joinLines bodyLines).toList hc_clean
      have hparse_body : parseDocumentFuel numApi fullFuel (joinLines bodyLines).toList [] [] = .ok finalLoc := by
        simpa [id, List.append_nil] using hbody_parse.trans (by
          have hpos : fullFuel - bodyLines.length ≥ 1 := by omega
          cases hd : fullFuel - bodyLines.length with
          | zero => omega
          | succ _ => simp [parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux])
      have hp_full : parseDocumentFuel numApi fullFuel (joinLines (hdrLines ++ bodyLines)).toList [] [] = .ok finalLoc := by
        rw [parseDocumentFuel_skipTrivia numApi (joinLines (hdrLines ++ bodyLines)).toList.length _ _ [] [] hskip]
        exact hparse_body
      refine ⟨(entriesToTomlList finalLoc).toArray, ?_, ?_⟩
      · simp only [parseWithNum, hinter, hnorm_eq, bind, Except.bind]
        rw [show (joinLines (hdrLines ++ bodyLines)).toList.length + 1 = fullFuel from rfl, hp_full]
      · simpa [TomlTableEquiv] using heqv_list

private theorem joinRenderedPath_eq_intercalate (xs : List String) :
    joinRenderedPath xs = String.intercalate "." xs := by
  match xs with
  | [] => simp [joinRenderedPath, String.intercalate_nil]
  | [k] => simp [joinRenderedPath, String.intercalate_singleton]
  | k :: a :: rest =>
    simp [joinRenderedPath, joinRenderedPath_eq_intercalate (a :: rest), String.intercalate_cons_cons]

private theorem toString_mul_pow10 (q k : Nat) (hq : 0 < q) :
    (toString (q * pow10Nat k)).toList = (toString q).toList ++ List.replicate k '0' := by
  induction k with
  | zero => simp [pow10Nat]
  | succ k' ih =>
    have hmul : q * pow10Nat (k' + 1) = (q * pow10Nat k') * 10 + 0 := by
      change q * (10 * pow10Nat k') = q * pow10Nat k' * 10 + 0
      rw [Nat.add_zero, Nat.mul_left_comm, Nat.mul_comm 10]
    have hq' : 0 < q * pow10Nat k' := Nat.mul_pos hq (pow10Nat_pos k')
    rw [hmul, toString_two_digits_split (q * pow10Nat k') 0 hq' (by decide), ih]
    have hd0 : Nat.digitChar 0 = '0' := by decide
    rw [hd0, List.append_assoc, ← List.replicate_succ']

private theorem digitChar_ne_zero (d : Nat) (hd0 : d ≠ 0) (hd10 : d < 10) :
    Nat.digitChar d ≠ '0' := by
  match d with
  | 0 => exact absurd rfl hd0
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | _ + 10 => omega

private theorem toString_last_ne_zero (q : Nat) (hq : 0 < q) (hmod : q % 10 ≠ 0) :
    ∃ pref c, (toString q).toList = pref ++ [c] ∧ c ≠ '0' := by
  by_cases h10 : q < 10
  · obtain ⟨hch, _, _⟩ := toString_lt10_char q h10
    exact ⟨[], Nat.digitChar q, by rw [hch]; rfl, digitChar_ne_zero q (by omega) h10⟩
  · have hq10 : 0 < q / 10 := by omega
    have heq : q = (q / 10) * 10 + q % 10 := by omega
    have hsp := toString_two_digits_split (q / 10) (q % 10) hq10 (Nat.mod_lt q (by decide))
    rw [← heq] at hsp
    exact ⟨(toString (q / 10)).toList, Nat.digitChar (q % 10), hsp,
      digitChar_ne_zero (q % 10) hmod (Nat.mod_lt q (by decide))⟩

private theorem padNatZero_last_ne_zero (w q : Nat) (hq : 0 < q) (hmod : q % 10 ≠ 0)
    (hw : (toString q).toList.length ≤ w) :
    ∃ pref c, (padNatZero w q).toList = pref ++ [c] ∧ c ≠ '0' := by
  rw [padNatZero_eq_of_toList w q (toString q).toList rfl hw]
  obtain ⟨pref, c, hq_eq, hne⟩ := toString_last_ne_zero q hq hmod
  exact ⟨List.replicate (w - (toString q).toList.length) '0' ++ pref, c,
    by rw [hq_eq, List.append_assoc], hne⟩

private theorem dropWhile_replicate_zero_cons (k : Nat) (c : Char) (tl : List Char) (hc : c ≠ '0') :
    (List.replicate k '0' ++ c :: tl).dropWhile (· == '0') = c :: tl := by
  induction k with
  | zero =>
    have hbeq : (c == '0') = false := beq_false_of_ne hc
    simp [hbeq]
  | succ k' ih =>
    simp [List.replicate_succ, ih]

private def stripTrailingZerosNat (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0)
  else if n % 10 = 0 then
    let p := stripTrailingZerosNat (n / 10)
    (p.1 + 1, p.2)
  else (0, n)
termination_by n

private theorem stripTrailingZerosNat_spec (n : Nat) (hn : 0 < n) :
    let p := stripTrailingZerosNat n
    n = p.2 * pow10Nat p.1 ∧ 0 < p.2 ∧ p.2 % 10 ≠ 0 := by
  unfold stripTrailingZerosNat
  have hne0 : n ≠ 0 := by omega
  simp only [hne0, ↓reduceIte]
  by_cases hmod : n % 10 = 0
  · simp only [hmod, ↓reduceIte]
    have hdiv_pos : 0 < n / 10 := by omega
    have ih := stripTrailingZerosNat_spec (n / 10) hdiv_pos
    rcases ih with ⟨heq, hq_pos, hq_mod⟩
    refine ⟨?_, hq_pos, hq_mod⟩
    calc
      n = (n / 10) * 10 := by omega
      _ = ((stripTrailingZerosNat (n / 10)).2 * pow10Nat (stripTrailingZerosNat (n / 10)).1) * 10 := by rw [← heq]
      _ = (stripTrailingZerosNat (n / 10)).2 * pow10Nat ((stripTrailingZerosNat (n / 10)).1 + 1) := by
        change _ = _ * (10 * pow10Nat (stripTrailingZerosNat (n / 10)).1)
        rw [Nat.mul_assoc, Nat.mul_comm (pow10Nat _) 10]
  · simp only [hmod, ↓reduceIte, pow10Nat, Nat.mul_one]
    exact ⟨trivial, hn, hmod⟩
termination_by n

private theorem pow10Nat_mono {a b : Nat} (hab : a ≤ b) : pow10Nat a ≤ pow10Nat b := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    simp only [pow10Nat]
    omega

private theorem formatNanosTrimmed_exists_exact (nano : Nat) (hn : nano < pow10Nat 9) :
    ∃ fd : Nat, formatNanosExact nano fd = some (formatNanosTrimmed nano) := by
  by_cases hn0 : nano = 0
  · subst hn0
    exact ⟨0, by simp [formatNanosExact, formatNanosTrimmed]⟩
  · have hn_pos : 0 < nano := by omega
    have hsp := stripTrailingZerosNat_spec nano hn_pos
    dsimp only at hsp
    let k := (stripTrailingZerosNat nano).1
    let q := (stripTrailingZerosNat nano).2
    rcases hsp with ⟨heq, hq_pos, hq_mod⟩
    have hk_lt9 : k < 9 := by
      by_cases hk : k < 9
      · exact hk
      · have hge9 : 9 ≤ k := by omega
        have hp9 : pow10Nat 9 ≤ pow10Nat k := pow10Nat_mono hge9
        have h1 : pow10Nat k ≤ q * pow10Nat k := Nat.le_mul_of_pos_left _ hq_pos
        have hle : pow10Nat 9 ≤ nano := by rw [heq]; exact Nat.le_trans hp9 h1
        exact False.elim (by omega)
    let fd := 9 - k
    have hfd_pos : 1 ≤ fd := by omega
    have h9_eq : fd + k = 9 := by omega
    have hq_lt : q < pow10Nat fd := by
      have hmul_pow : pow10Nat fd * pow10Nat k = pow10Nat 9 := by
        rw [← pow10Nat_add, h9_eq]
      by_cases hlt : q < pow10Nat fd
      · exact hlt
      · have h1 : pow10Nat fd ≤ q := by omega
        have h2 := Nat.mul_le_mul_right (pow10Nat k) h1
        rw [hmul_pow] at h2
        have hle : pow10Nat 9 ≤ nano := by rw [heq]; exact h2
        exact False.elim (by omega)
    have hq_len_str : (toString q).length ≤ fd := toString_length_le_pow10 fd q hfd_pos hq_lt
    have hq_len_list : (toString q).toList.length ≤ fd := by
      simpa [String.length] using hq_len_str
    have hn_str_len : (toString nano).length ≤ 9 := toString_length_le_pow10 9 nano (by omega) hn
    have hn_list_len : (toString nano).toList.length ≤ 9 := by
      simpa [String.length] using hn_str_len
    have hpad9 : (padNatZero 9 nano).toList = (padNatZero fd q).toList ++ List.replicate k '0' := by
      have hnano_list : (toString nano).toList = (toString q).toList ++ List.replicate k '0' := by
        rw [heq]; exact toString_mul_pow10 q k hq_pos
      have hlen_sum : (toString nano).toList.length = (toString q).toList.length + k := by
        rw [hnano_list, List.length_append, List.length_replicate]
      rw [padNatZero_eq_of_toList 9 nano _ hnano_list (by rw [← hnano_list]; exact hn_list_len),
        padNatZero_eq_of_toList fd q (toString q).toList rfl hq_len_list]
      have hsub : 9 - ((toString q).toList.length + k) = fd - (toString q).toList.length := by omega
      rw [List.length_append, List.length_replicate, hsub, List.append_assoc]
    obtain ⟨pref, c, hpad_fd, hc_ne⟩ := padNatZero_last_ne_zero fd q hq_pos hq_mod hq_len_list
    have htrim_eq : ((padNatZero 9 nano).toList.reverse.dropWhile (· == '0')).reverse =
        (padNatZero fd q).toList := by
      rw [hpad9, hpad_fd, List.reverse_append, List.reverse_replicate, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      rw [dropWhile_replicate_zero_cons k c pref.reverse hc_ne, List.reverse_cons, List.reverse_reverse]
    have hfmt_trim : formatNanosTrimmed nano = "." ++ padNatZero fd q := by
      have hnb : (nano == 0) = false := beq_false_of_ne hn0
      simp only [formatNanosTrimmed, hnb, Bool.false_eq_true, ↓reduceIte]
      rw [htrim_eq, String.ofList_toList]
    have h9_fd : 9 - fd = k := by omega
    have hmod_div : nano % pow10Nat k = 0 := by
      rw [heq]; exact Nat.mul_mod_left q (pow10Nat k)
    have hdiv_val : nano / pow10Nat k = q := by
      rw [heq]; exact Nat.mul_div_cancel q (pow10Nat_pos k)
    have hfd_gt9 : ¬(fd > 9) := by omega
    have hfd_ne0 : (fd == 0) = false := beq_false_of_ne (by omega)
    refine ⟨fd, ?_⟩
    simp only [formatNanosExact, hfd_gt9, ↓reduceIte, hfd_ne0, Bool.false_eq_true,
      h9_fd, hmod_div, bne_self_eq_false, hdiv_val, hfmt_trim]

private def chooseKeyStyle (k : String) : KeyStyle :=
  if isValidBareKey k then .bare else .basic

private theorem renderKey_chooseKeyStyle (k : String) :
    renderKey k (chooseKeyStyle k) = some (formatKey k) := by
  by_cases hk : isValidBareKey k = true
  · simp [chooseKeyStyle, renderKey, formatKey, hk]
  · simp [chooseKeyStyle, renderKey, formatKey, hk]

private theorem renderDate_formatDate (d : Std.Time.PlainDate) (h : validTomlDate d = true) :
    renderDate d = some (formatDate d) := by
  simp [renderDate, formatDate, h]

private theorem renderTime_formatTime (t : Std.Time.PlainTime) (h : validTomlTime t = true) :
    ∃ fd : Nat, renderTime t fd = some (formatTime t) := by
  have hn_prop := t.nanosecond.property
  have hn_lt : t.nanosecond.val.toNat < pow10Nat 9 := by
    rw [pow10Nat_9]; omega
  obtain ⟨fd, hfd⟩ := formatNanosTrimmed_exists_exact t.nanosecond.val.toNat hn_lt
  exact ⟨fd, by simp [renderTime, formatTime, h, hfd]⟩

private theorem renderOffset_formatOffset (o : Std.Time.TimeZone.Offset)
    (h : validTomlOffset o = true) :
    renderOffset o .upperZ = some (formatOffset o) := by
  simp only [renderOffset, formatOffset, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> rfl

private theorem lookupKeyList_mem_of_noDupKeys (entries : List (String × TomlValue))
    (hnd : noDupKeysBool entries = true) :
    ∀ k v, (k, v) ∈ entries → lookupKeyList k entries = some v := by
  induction entries with
  | nil => intro k v hmem; cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    intro k v hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hhead | htail
    · cases hhead
      simp [lookupKeyList]
    · have hmem_map : k ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(k, v), htail, rfl⟩
      have hhas : hasKeyList k tl = true := (hasKeyList_eq_true_iff k tl).mpr hmem_map
      have hne : k ≠ k' := by
        intro heq
        subst heq
        rw [hnd.1] at hhas
        cases hhas
      have hbeq : (k == k') = false := beq_false_of_ne hne
      simp only [lookupKeyList, hbeq, Bool.false_eq_true, ↓reduceIte]
      exact ih hnd.2 k v htail

private theorem filter_ne_head_of_not_hasKey (k : String) (entries : List (String × TomlValue))
    (hnot : hasKeyList k entries = false) :
    entries.filter (fun p => p.1 != k) = entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [hasKeyList, Bool.or_eq_false_iff] at hnot
    have hne : (k' != k) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact fun h => by subst h; simp at hnot
    simp only [List.filter_cons, hne, ↓reduceIte, ih hnot.2]

private theorem renderValueInline_formatValueInline_aux (numApi : NumParseApi)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (sz : Nat) :
    (∀ v : TomlValue, sizeOf v ≤ sz → WellFormedValue v →
      ∃ vt, renderValueInline v vt = some (formatValueInline numApi v)) ∧
    (∀ xs : List TomlValue, sizeOf xs ≤ sz → wellFormedValueBool.wellFormedListBool xs = true →
      ∃ elemTapes, renderValueInline.renderArrayElems xs elemTapes =
        some (formatArrayElems numApi xs)) ∧
    (∀ entries : List (String × TomlValue), sizeOf entries ≤ sz →
      noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
      ∃ entryTapes, renderValueInline.renderInlineTableEntries entries entryTapes =
        some (formatInlineEntries numApi entries)) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro v hsz _
      cases v <;> simp +arith at hsz
    · intro xs hsz _
      cases xs with
      | nil => exact ⟨[], rfl⟩
      | cons _ _ => simp +arith at hsz
    · intro entries hsz _ _
      cases entries with
      | nil => exact ⟨[], rfl⟩
      | cons _ _ => simp +arith at hsz
  | succ sz' ih =>
    have ihV := ih.1
    have ihA := ih.2.1
    have ihT := ih.2.2
    refine ⟨?_, ?_, ?_⟩
    · intro v hsz hwf
      cases v with
      | string s => exact ⟨.string .basic, rfl⟩
      | int n =>
        exact ⟨.int (some (numApi.formatInt n.toInt)),
          by simp [renderValueInline, hFmtInt n, formatValueInline]⟩
      | float f =>
        exact ⟨.float (some (numApi.formatFloat f)),
          by simp [renderValueInline, hFmtFloat f, formatValueInline]⟩
      | bool b => exact ⟨.bool, rfl⟩
      | offsetDateTime odt =>
        have hvd : validTomlOffsetDateTime odt = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        simp only [validTomlOffsetDateTime, validTomlDateTime, Bool.and_eq_true] at hvd
        have hd := renderDate_formatDate odt.dateTime.date hvd.1.1
        obtain ⟨fd, ht⟩ := renderTime_formatTime odt.dateTime.time hvd.1.2
        have ho := renderOffset_formatOffset odt.offset hvd.2
        exact ⟨.offsetDateTime .upperT .upperZ fd,
          by simp [renderValueInline, formatValueInline, renderDateTimeSep, hd, ht, ho]⟩
      | localDateTime dt =>
        have hvd : validTomlDateTime dt = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        simp only [validTomlDateTime, Bool.and_eq_true] at hvd
        have hd := renderDate_formatDate dt.date hvd.1
        obtain ⟨fd, ht⟩ := renderTime_formatTime dt.time hvd.2
        exact ⟨.localDateTime .upperT fd,
          by simp [renderValueInline, formatValueInline, renderDateTimeSep, hd, ht]⟩
      | localDate d =>
        have hvd : validTomlDate d = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        exact ⟨.localDate, by simp [renderValueInline, formatValueInline, renderDate_formatDate d hvd]⟩
      | localTime t =>
        have hvt : validTomlTime t = true := by simpa [WellFormedValue, wellFormedValueBool] using hwf
        obtain ⟨fd, ht⟩ := renderTime_formatTime t hvt
        exact ⟨.localTime fd, by simp [renderValueInline, formatValueInline, ht]⟩
      | array xs =>
        have hwf_l : wellFormedValueBool.wellFormedListBool xs.toList = true := by
          simpa [WellFormedValue, wellFormedValueBool] using hwf
        have hsz_l : sizeOf xs.toList ≤ sz' := by
          have := sizeOf_toList_lt_array xs
          have : sizeOf xs < sizeOf (TomlValue.array xs) := by simp +arith
          omega
        obtain ⟨elemTapes, he⟩ := ihA xs.toList hsz_l hwf_l
        exact ⟨.array elemTapes,
          by simp [renderValueInline, formatValueInline, he]⟩
      | table t =>
        have hwf_t : noDupKeysBool t.toList = true ∧
            wellFormedValueBool.wellFormedTableListBool t.toList = true := by
          simpa [WellFormedValue, wellFormedValueBool, Bool.and_eq_true] using hwf
        have hsz_t : sizeOf t.toList ≤ sz' := by
          have := sizeOf_toList_lt_array t
          have : sizeOf t < sizeOf (TomlValue.table t) := by simp +arith
          omega
        obtain ⟨entryTapes, he⟩ := ihT t.toList hsz_t hwf_t.1 hwf_t.2
        exact ⟨.inlineTable entryTapes,
          by simp [renderValueInline, formatValueInline, hwf_t.1, he]⟩
    · intro xs hsz hwf
      cases xs with
      | nil => exact ⟨[], rfl⟩
      | cons x rest =>
        simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf
        have hsz_x : sizeOf x ≤ sz' := by simp +arith at hsz ⊢; omega
        have hsz_r : sizeOf rest ≤ sz' := by simp +arith at hsz ⊢; omega
        obtain ⟨vt, hvt⟩ := ihV x hsz_x hwf.1
        obtain ⟨elemTapes, he⟩ := ihA rest hsz_r hwf.2
        exact ⟨vt :: elemTapes,
          by simp [renderValueInline.renderArrayElems, formatArrayElems, hvt, he]⟩
    · intro entries hsz hnd hwf
      cases entries with
      | nil => exact ⟨[], rfl⟩
      | cons hd rest =>
        rcases hd with ⟨k, v⟩
        simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
        simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
        have hsz_v : sizeOf v ≤ sz' := by simp +arith at hsz ⊢; omega
        have hsz_r : sizeOf rest ≤ sz' := by simp +arith at hsz ⊢; omega
        obtain ⟨vt, hvt⟩ := ihV v hsz_v hwf.1
        obtain ⟨restTapes, hr⟩ := ihT rest hsz_r hnd.2 hwf.2
        have hfilt : ((k, v) :: rest).filter (fun p => p.1 != k) = rest := by
          simp only [List.filter_cons, bne_self_eq_false]
          exact filter_ne_head_of_not_hasKey k rest hnd.1
        refine ⟨(k, chooseKeyStyle k, vt) :: restTapes, ?_⟩
        simp only [renderValueInline.renderInlineTableEntries, lookupKeyList, beq_self_eq_true,
          ↓reduceIte, renderKey_chooseKeyStyle k, hvt, hfilt, hr, formatInlineEntries,
          bind, Option.bind]

private theorem renderValueInline_formatValueInline (numApi : NumParseApi)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (v : TomlValue) (hwf : WellFormedValue v) :
    ∃ vt, renderValueInline v vt = some (formatValueInline numApi v) :=
  (renderValueInline_formatValueInline_aux numApi hFmtInt hFmtFloat (sizeOf v)).1 v (Nat.le_refl _) hwf

private def PlacementMatches (numApi : NumParseApi) (k : String) (v : TomlValue)
    (ep : EntryPlacement) : Prop :=
  match v with
  | .table sub =>
    ∃ subPlan, ep = .tableSection (chooseKeyStyle k) false subPlan none ∧
      ∀ revPref, renderTablePlan revPref sub.toList subPlan =
        some (formatTableInlinePart numApi sub.toList ++ formatTableSectionPart numApi revPref sub.toList)
  | .array xs =>
    if isNonEmptyTableArray xs then
      ∃ elemPlans, ep = .aotSection (chooseKeyStyle k) elemPlans none ∧
        ∀ revTarget, renderAotElems revTarget "" xs.toList elemPlans =
          some (formatAotElemList numApi revTarget ("[[" ++ String.intercalate "." revTarget.reverse ++ "]]") xs.toList)
    else
      ∃ vt, ep = .direct (chooseKeyStyle k) vt none ∧
        renderValueInline v vt = some (formatValueInline numApi v)
  | _ =>
    ∃ vt, ep = .direct (chooseKeyStyle k) vt none ∧
      renderValueInline v vt = some (formatValueInline numApi v)

private theorem placementMatches_isInlineScope (numApi : NumParseApi) (k : String) (v : TomlValue)
    (ep : EntryPlacement) (hm : PlacementMatches numApi k v ep) :
    (match v with
     | .table _ => ep.isInlineScope = false
     | .array xs =>
       if isNonEmptyTableArray xs then ep.isInlineScope = false else ep.isInlineScope = true
     | _ => ep.isInlineScope = true) := by
  cases v with
  | table sub =>
    rcases hm with ⟨subPlan, rfl, _⟩; rfl
  | array xs =>
    by_cases haot : isNonEmptyTableArray xs = true
    · simp only [PlacementMatches, haot, ↓reduceIte] at hm ⊢
      rcases hm with ⟨elemPlans, rfl, _⟩; rfl
    · have haf : isNonEmptyTableArray xs = false := Bool.eq_false_iff.mpr haot
      simp only [PlacementMatches, haf, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      rcases hm with ⟨vt, rfl, _⟩; rfl
  | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
    rcases hm with ⟨vt, rfl, _⟩; rfl

private inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

private theorem ListRel.length_eq {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : ListRel R as bs) : bs.length = as.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem renderEntries_of_placementMatches (numApi : NumParseApi)
    (fullEntries : List (String × TomlValue))
    (subEntries : List (String × TomlValue)) (subPlan : List (String × EntryPlacement))
    (hsub : ∀ p ∈ subEntries, lookupKeyList p.1 fullEntries = some p.2)
    (hmatch : ListRel (fun p q => p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) subEntries subPlan)
    (revPref : List String) :
    renderInlineEntries revPref fullEntries subPlan = some (formatTableInlinePart numApi subEntries) ∧
    renderSectionEntries revPref fullEntries subPlan = some (formatTableSectionPart numApi revPref subEntries) := by
  induction hmatch with
  | nil =>
    exact ⟨by simp [renderInlineEntries, formatTableInlinePart],
      by simp [renderSectionEntries, formatTableSectionPart]⟩
  | @cons hd_e hd_p tl_e tl_p hhead htail ih =>
    rcases hd_e with ⟨k, v⟩
    rcases hd_p with ⟨kp, ep⟩
    rcases hhead with ⟨hk_eq, hm⟩
    dsimp only at hk_eq hm
    subst hk_eq
    have hlu : lookupKeyList k fullEntries = some v := hsub (k, v) List.mem_cons_self
    have hsub_tl : ∀ p ∈ tl_e, lookupKeyList p.1 fullEntries = some p.2 :=
      fun p hp => hsub p (List.mem_cons_of_mem _ hp)
    obtain ⟨ih_inl, ih_sec⟩ := ih hsub_tl
    cases v with
    | table sub =>
      rcases sub with ⟨subList⟩
      rcases hm with ⟨subPlan', rfl, htp⟩
      have hinl : renderInlineEntries revPref fullEntries ((k, .tableSection (chooseKeyStyle k) false subPlan' none) :: tl_p) =
          some (formatTableInlinePart numApi ((k, .table ⟨subList⟩) :: tl_e)) := by
        simp [renderInlineEntries, EntryPlacement.isInlineScope, ih_inl, formatTableInlinePart]
      have hsec : renderSectionEntries revPref fullEntries ((k, .tableSection (chooseKeyStyle k) false subPlan' none) :: tl_p) =
          some (formatTableSectionPart numApi revPref ((k, .table ⟨subList⟩) :: tl_e)) := by
        simp only [renderSectionEntries, EntryPlacement.isInlineScope, Bool.false_eq_true, ↓reduceIte,
          hlu, renderKey_chooseKeyStyle k, renderCommentSuffix, htp, ih_sec, formatTableSectionPart,
          bind, Option.bind, joinRenderedPath_eq_intercalate, String.append_empty]
        simp only [List.cons_append, List.append_assoc]
      exact ⟨hinl, hsec⟩
    | array xs =>
      rcases xs with ⟨xsList⟩
      by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
      · simp only [PlacementMatches, haot, ↓reduceIte] at hm
        rcases hm with ⟨elemPlans, rfl, ha⟩
        have hne : (⟨xsList⟩ : Array TomlValue).isEmpty = false := by
          simp only [isNonEmptyTableArray, Bool.and_eq_true, Bool.not_eq_true'] at haot
          exact haot.1
        have hinl : renderInlineEntries revPref fullEntries ((k, .aotSection (chooseKeyStyle k) elemPlans none) :: tl_p) =
            some (formatTableInlinePart numApi ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp [renderInlineEntries, EntryPlacement.isInlineScope, ih_inl, formatTableInlinePart, haot]
        have hsec : renderSectionEntries revPref fullEntries ((k, .aotSection (chooseKeyStyle k) elemPlans none) :: tl_p) =
            some (formatTableSectionPart numApi revPref ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp only [renderSectionEntries, EntryPlacement.isInlineScope, Bool.false_eq_true, ↓reduceIte,
            hlu, hne, renderKey_chooseKeyStyle k, renderCommentSuffix, ha, ih_sec, formatTableSectionPart,
            haot, bind, Option.bind]
        exact ⟨hinl, hsec⟩
      · have haf : isNonEmptyTableArray ⟨xsList⟩ = false := Bool.eq_false_iff.mpr haot
        simp only [PlacementMatches, haf, Bool.false_eq_true, ↓reduceIte] at hm
        rcases hm with ⟨vt, rfl, hrv⟩
        have hinl : renderInlineEntries revPref fullEntries ((k, .direct (chooseKeyStyle k) vt none) :: tl_p) =
            some (formatTableInlinePart numApi ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp only [renderInlineEntries, EntryPlacement.isInlineScope, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hlu, renderKey_chooseKeyStyle k, hrv, renderCommentSuffix, ih_inl,
            formatTableInlinePart, haf, bind, Option.bind, String.append_empty]
          rfl
        have hsec : renderSectionEntries revPref fullEntries ((k, .direct (chooseKeyStyle k) vt none) :: tl_p) =
            some (formatTableSectionPart numApi revPref ((k, .array ⟨xsList⟩) :: tl_e)) := by
          simp [renderSectionEntries, EntryPlacement.isInlineScope, ih_sec, formatTableSectionPart, haf]
        exact ⟨hinl, hsec⟩
    | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
      rcases hm with ⟨vt, rfl, hrv⟩
      refine ⟨?_, ?_⟩
      · simp only [renderInlineEntries, EntryPlacement.isInlineScope, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, hlu, renderKey_chooseKeyStyle k, hrv, renderCommentSuffix, ih_inl,
          formatTableInlinePart, bind, Option.bind, String.append_empty]
        rfl
      · simp [renderSectionEntries, EntryPlacement.isInlineScope, ih_sec, formatTableSectionPart]

private theorem noDupStringsBool_map_fst (entries : List (String × TomlValue)) :
    noDupStringsBool (entries.map Prod.fst) = noDupKeysBool entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, noDupStringsBool, noDupKeysBool, ih]
    have hmem : (tl.map Prod.fst).contains k = hasKeyList k tl := by
      cases hc : (tl.map Prod.fst).contains k
      · symm
        cases hh : hasKeyList k tl
        · rfl
        · have h1 := (hasKeyList_eq_true_iff k tl).mp hh
          have h2 : (tl.map Prod.fst).contains k = true := List.contains_iff_mem.mpr h1
          rw [hc] at h2; cases h2
      · symm
        have h1 : k ∈ tl.map Prod.fst := List.contains_iff_mem.mp hc
        exact (hasKeyList_eq_true_iff k tl).mpr h1
    rw [hmem]

private theorem isPlanPermutation_of_match (numApi : NumParseApi)
    (entries : List (String × TomlValue)) (plan : List (String × EntryPlacement))
    (hnd : noDupKeysBool entries = true)
    (hmatch : ListRel (fun p q => p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) entries plan) :
    isPlanPermutation entries plan = true := by
  have hmap : plan.map Prod.fst = entries.map Prod.fst := by
    clear hnd
    induction hmatch with
    | nil => rfl
    | cons hh _ ih => simp [hh.1, ih]
  have hlen : plan.length = entries.length := hmatch.length_eq
  have hall : plan.all (fun p => hasKeyList p.1 entries) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hmem : p.1 ∈ plan.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hmap] at hmem
    exact (hasKeyList_eq_true_iff p.1 entries).mpr hmem
  simp only [isPlanPermutation, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hnd, ?_⟩, hlen⟩, hall⟩
  rw [hmap, noDupStringsBool_map_fst, hnd]

private theorem choosePlan_exists_aux (numApi : NumParseApi)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (sz : Nat) :
    (∀ entries : List (String × TomlValue), sizeOf entries ≤ sz →
      noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
      ∃ plan, (∀ revPref, renderTablePlan revPref entries plan =
        some (formatTableInlinePart numApi entries ++ formatTableSectionPart numApi revPref entries))) ∧
    (∀ entries : List (String × TomlValue), sizeOf entries ≤ sz →
      noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
      ∃ plan, ListRel (fun (p : String × TomlValue) (q : String × EntryPlacement) =>
        p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) entries plan) ∧
    (∀ xs : List TomlValue, sizeOf xs ≤ sz →
      wellFormedValueBool.wellFormedListBool xs = true →
      (xs.all fun v => match v with | .table _ => true | _ => false) = true →
      ∃ elemPlans, ∀ revTarget, renderAotElems revTarget "" xs elemPlans =
        some (formatAotElemList numApi revTarget ("[[" ++ String.intercalate "." revTarget.reverse ++ "]]") xs)) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro entries hsz _ _
      cases entries with
      | nil =>
        exact ⟨[], fun revPref => by
          simp [renderTablePlan, isPlanPermutation, noDupKeysBool, noDupStringsBool,
            renderInlineEntries, renderSectionEntries, formatTableInlinePart, formatTableSectionPart]⟩
      | cons _ _ => simp +arith at hsz
    · intro entries hsz _ _
      cases entries with
      | nil => exact ⟨[], .nil⟩
      | cons _ _ => simp +arith at hsz
    · intro xs hsz _ _
      cases xs with
      | nil => exact ⟨[], fun _ => by simp [renderAotElems, formatAotElemList]⟩
      | cons _ _ => simp +arith at hsz
  | succ sz' ih =>
    have ihMatch := ih.2.1
    have ihPlan := ih.1
    have ihAot := ih.2.2
    have hMatchStep : ∀ entries : List (String × TomlValue), sizeOf entries ≤ sz' + 1 →
        noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
        ∃ plan, ListRel (fun (p : String × TomlValue) (q : String × EntryPlacement) =>
          p.1 = q.1 ∧ PlacementMatches numApi p.1 p.2 q.2) entries plan := by
      intro entries hsz hnd hwf
      cases entries with
      | nil => exact ⟨[], .nil⟩
      | cons hd tl =>
        rcases hd with ⟨k, v⟩
        simp only [noDupKeysBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
        simp only [wellFormedValueBool.wellFormedTableListBool, Bool.and_eq_true] at hwf
        have hsz_tl : sizeOf tl ≤ sz' := by simp +arith at hsz ⊢; omega
        obtain ⟨tlPlan, htl⟩ := ihMatch tl hsz_tl hnd.2 hwf.2
        cases v with
        | table sub =>
          have hwf_sub : noDupKeysBool sub.toList = true ∧
              wellFormedValueBool.wellFormedTableListBool sub.toList = true := by
            simpa [wellFormedValueBool, Bool.and_eq_true] using hwf.1
          have hsz_sub : sizeOf sub.toList ≤ sz' := by
            have := sizeOf_toList_lt_array sub
            simp +arith at hsz ⊢; omega
          obtain ⟨subPlan, hsub⟩ := ihPlan sub.toList hsz_sub hwf_sub.1 hwf_sub.2
          refine ⟨(k, .tableSection (chooseKeyStyle k) false subPlan none) :: tlPlan,
            .cons ⟨rfl, ⟨subPlan, rfl, hsub⟩⟩ htl⟩
        | array xs =>
          by_cases haot : isNonEmptyTableArray xs = true
          · have hwf_xs : wellFormedValueBool.wellFormedListBool xs.toList = true := by
              simpa [wellFormedValueBool] using hwf.1
            have hall_xs : (xs.toList.all fun v => match v with | .table _ => true | _ => false) = true := by
              simp only [isNonEmptyTableArray, Bool.and_eq_true] at haot
              exact haot.2
            have hsz_xs : sizeOf xs.toList ≤ sz' := by
              have := sizeOf_toList_lt_array xs
              simp +arith at hsz ⊢; omega
            obtain ⟨elemPlans, ha⟩ := ihAot xs.toList hsz_xs hwf_xs hall_xs
            refine ⟨(k, .aotSection (chooseKeyStyle k) elemPlans none) :: tlPlan,
              .cons ⟨rfl, ?_⟩ htl⟩
            simp only [PlacementMatches, haot, ↓reduceIte]
            exact ⟨elemPlans, rfl, ha⟩
          · have haf : isNonEmptyTableArray xs = false := Bool.eq_false_iff.mpr haot
            obtain ⟨vt, hvt⟩ := renderValueInline_formatValueInline numApi hFmtInt hFmtFloat (.array xs) hwf.1
            refine ⟨(k, .direct (chooseKeyStyle k) vt none) :: tlPlan,
              .cons ⟨rfl, ?_⟩ htl⟩
            simp only [PlacementMatches, haf, Bool.false_eq_true, ↓reduceIte]
            exact ⟨vt, rfl, hvt⟩
        | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
          obtain ⟨vt, hvt⟩ := renderValueInline_formatValueInline numApi hFmtInt hFmtFloat _ hwf.1
          exact ⟨(k, .direct (chooseKeyStyle k) vt none) :: tlPlan,
            .cons ⟨rfl, ⟨vt, rfl, hvt⟩⟩ htl⟩
    have hPlanStep : ∀ entries : List (String × TomlValue), sizeOf entries ≤ sz' + 1 →
        noDupKeysBool entries = true → wellFormedValueBool.wellFormedTableListBool entries = true →
        ∃ plan, (∀ revPref, renderTablePlan revPref entries plan =
          some (formatTableInlinePart numApi entries ++ formatTableSectionPart numApi revPref entries)) := by
      intro entries hsz hnd hwf
      obtain ⟨plan, hmatch⟩ := hMatchStep entries hsz hnd hwf
      have hperm : isPlanPermutation entries plan = true :=
        isPlanPermutation_of_match numApi entries plan hnd hmatch
      have hmem : ∀ p ∈ entries, lookupKeyList p.1 entries = some p.2 :=
        fun p hp => lookupKeyList_mem_of_noDupKeys entries hnd p.1 p.2 hp
      refine ⟨plan, fun revPref => ?_⟩
      obtain ⟨hinl, hsec⟩ := renderEntries_of_placementMatches numApi entries entries plan hmem hmatch revPref
      simp only [renderTablePlan, hperm, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hinl, hsec, bind, Option.bind]
    refine ⟨hPlanStep, hMatchStep, ?_⟩
    intro xs hsz hwf hall
    cases xs with
    | nil => exact ⟨[], fun _ => by simp [renderAotElems, formatAotElemList]⟩
    | cons x rest =>
      simp only [wellFormedValueBool.wellFormedListBool, Bool.and_eq_true] at hwf
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hsz_rest : sizeOf rest ≤ sz' := by simp +arith at hsz ⊢; omega
      obtain ⟨tailPlans, htail⟩ := ihAot rest hsz_rest hwf.2 hall.2
      cases x with
      | table elem =>
        have hwf_e : noDupKeysBool elem.toList = true ∧
            wellFormedValueBool.wellFormedTableListBool elem.toList = true := by
          simpa [wellFormedValueBool, Bool.and_eq_true] using hwf.1
        have hsz_e : sizeOf elem.toList ≤ sz' := by
          have := sizeOf_toList_lt_array elem
          simp +arith at hsz ⊢; omega
        obtain ⟨ep, hep⟩ := ihPlan elem.toList hsz_e hwf_e.1 hwf_e.2
        refine ⟨ep :: tailPlans, fun revTarget => ?_⟩
        cases elem with
        | mk elemList =>
          simp only [renderAotElems, joinRenderedPath_eq_intercalate, String.append_empty,
            hep revTarget, htail revTarget, formatAotElemList, bind, Option.bind]
          simp only [List.cons_append, List.append_assoc]
      | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
        cases hall.1

private theorem formatSectionLines_nil_eq_nil (numApi : NumParseApi) (revPref : List String)
    (doc : TomlTable) (h : formatSectionLines numApi revPref doc = []) :
    doc.toList = [] := by
  cases hlist : doc.toList with
  | nil => rfl
  | cons hd tl =>
    rcases hd with ⟨k, v⟩
    simp only [formatSectionLines, hlist, List.append_eq_nil_iff] at h
    rcases h with ⟨hinl, hsec⟩
    cases v with
    | table sub =>
      cases sub
      simp [formatTableSectionPart] at hsec
    | array xs =>
      cases xs with
      | mk xsList =>
        by_cases haot : isNonEmptyTableArray ⟨xsList⟩ = true
        · simp only [formatTableSectionPart, haot, ↓reduceIte] at hsec
          cases xsList with
          | nil =>
            simp [isNonEmptyTableArray] at haot
          | cons x0 rest =>
            simp only [isNonEmptyTableArray, List.all_cons, Bool.and_eq_true] at haot
            cases x0 with
            | table elem =>
              cases elem
              simp [formatAotElemList] at hsec
            | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ | array _ =>
              cases haot.2.1
        · have haf : isNonEmptyTableArray ⟨xsList⟩ = false := Bool.eq_false_iff.mpr haot
          simp [formatTableInlinePart, haf] at hinl
    | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
      simp [formatTableInlinePart] at hinl

/-- Empty input string parses via `parseWithNum` to an empty `TomlTable`. -/
theorem parseWithNum_empty (numApi : NumParseApi) :
    parseWithNum numApi "" = .ok #[] := by
  simp [parseWithNum, normalizeChars, parseDocumentFuel, skipTriviaNewlines,
    skipTriviaNewlinesAux, entriesToTomlList, bind, Except.bind]

/-- Canonical `formatWithNum` output always parses via `parseWithNum` to an equivalent `TomlTable` for any `WellFormedTable`. -/
theorem formatWithNum_roundTrip_model (numApi : NumParseApi)
    (hInt : ∀ tok n, NumParse.Model.parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, NumParse.Model.parseFloatModel tok = .ok f →
      ∃ g, numApi.parseFloat tok = .ok g ∧ NumParse.Model.FloatBitMatch f g)
    (hFmtInt : ∀ n : Int64, isValidIntLex (numApi.formatInt n.toInt) n = true)
    (hFmtFloat : ∀ f : Float, isValidFloatLex (numApi.formatFloat f) f = true)
    (doc : TomlTable) (hwf : WellFormedTable doc) :
    ∃ parsed, parseWithNum numApi (formatWithNum numApi doc) = .ok parsed ∧
      TomlTableEquiv doc parsed := by
  unfold formatWithNum
  cases hlines : formatSectionLines numApi [] doc with
  | nil =>
    have hdoc_nil : doc.toList = [] := formatSectionLines_nil_eq_nil numApi [] doc hlines
    refine ⟨#[], parseWithNum_empty numApi, ?_⟩
    simp [TomlTableEquiv, hdoc_nil, TomlTableEquivList, lookupKeyList]
  | cons hd tl =>
    have hwf_b : wellFormedTableBool doc = true := hwf
    have hwf_parts : noDupKeysBool doc.toList = true ∧
        wellFormedValueBool.wellFormedTableListBool doc.toList = true := by
      simpa [wellFormedTableBool, Bool.and_eq_true] using hwf_b
    obtain ⟨plan, hplan⟩ := (choosePlan_exists_aux numApi hFmtInt hFmtFloat (sizeOf doc.toList)).1
      doc.toList (Nat.le_refl _) hwf_parts.1 hwf_parts.2
    have hrender : render doc ⟨plan, none⟩ = some (String.intercalate "\n" (hd :: tl) ++ "\n") := by
      have hbp : renderTablePlan [] doc.toList plan = some (hd :: tl) := by
        have hp := hplan []
        unfold formatSectionLines at hlines
        rw [hlines] at hp
        exact hp
      simp [render, hwf_b, hbp, bind, Option.bind]
    exact render_parse_roundTrip_model numApi hInt hFloat doc ⟨plan, none⟩
      (String.intercalate "\n" (hd :: tl) ++ "\n") hrender

end LeanSwe.Toml.Proofs
