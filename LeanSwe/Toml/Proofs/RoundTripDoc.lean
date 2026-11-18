import LeanSwe.Toml.Types
import LeanSwe.Toml.Model
import LeanSwe.Toml.Impl
import LeanSwe.Toml.Proofs.RoundTripScalar
import LeanSwe.NumParse.Types
import LeanSwe.NumParse.Model

/-!
# Document-Level TOML Render-Parse Round-Trip Proofs

Proves round-trip correctness for `Model.render` against `Impl.parseWithNum` over nested tables,
arrays of tables, inline tables, dotted keys, and comments via `RenderValSpec`, `DocFocus`, and `DocSteps`.
-/

set_option Elab.async false
namespace LeanSwe.Toml.Proofs
open LeanSwe.Toml LeanSwe.Toml.Model LeanSwe.Toml.Impl LeanSwe.NumParse LeanSwe.NumParse.Model

private theorem none_bind {α β : Type} (f : α → Option β) : (none >>= f) = none := rfl
private theorem bind_const_none {α β : Type} (x : Option α) : (x >>= fun _ => (none : Option β)) = none := by cases x <;> rfl
private theorem some_bind {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl
private theorem bind_some {α β : Type} (x : Option α) (f : α → Option β) (y : β) :
    (x >>= f) = some y ↔ ∃ a, x = some a ∧ f a = some y := by cases x <;> simp [bind, Option.bind]
private theorem ite_true_none_some {α : Type} (b : Bool) (x : Option α) (y : α) :
    (if b then none else x) = some y ↔ b = false ∧ x = some y := by cases b <;> simp
private theorem not_eq_false (b : Bool) : ((!b) = false) ↔ (b = true) := by cases b <;> simp

private abbrev CleanChars (cs : List Char) : Prop := (cs.all fun c => !isDisallowedControl c && c != '\r') = true
private abbrev CleanStr (s : String) : Prop := CleanChars s.toList
private theorem cleanStr_lit (s : String) (h : CleanStr s := by decide) : CleanStr s := h
private theorem cleanChars_append {a b : List Char} (ha : CleanChars a) (hb : CleanChars b) : CleanChars (a ++ b) := by
  simp only [CleanChars, List.all_append, Bool.and_eq_true]; exact ⟨ha, hb⟩
private theorem cleanStr_append {a b : String} (ha : CleanStr a) (hb : CleanStr b) : CleanStr (a ++ b) := by
  simp only [CleanStr, String.toList_append]; exact cleanChars_append ha hb
private theorem cleanChars_of_no_nl {cs : List Char}
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n') = true) : CleanChars cs := by
  simp only [CleanChars, List.all_eq_true, Bool.and_eq_true] at h ⊢; exact fun c hc => (h c hc).1
private theorem cleanChars_of_full {cs : List Char}
    (h : (cs.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true) : CleanChars cs := by
  simp only [CleanChars, List.all_eq_true, Bool.and_eq_true] at h ⊢; exact fun c hc => (h c hc).1.1

private def DelimTail (rest : List Char) : Prop :=
  ∀ c r, rest = c :: r → isUnquotedDelim c = true ∧ (c = ' ' → ∀ c2 r2, r = c2 :: r2 → isAsciiDigit c2 = false)
private def ValidCharNum (numApi : CharNumApi) : Prop :=
  (∀ tok : String, ∀ n, parseInt64Model tok = .ok n → numApi.parseInt64Chars tok.toList = .ok n) ∧
  (∀ tok : String, ∀ f, parseFloatModel tok = .ok f → ∃ g, numApi.parseFloatChars tok.toList = .ok g ∧ FloatBitMatch f g)

private structure RenderValSpec (numApi : CharNumApi) (v : TomlValue) (rs : String) : Prop where
  clean : CleanStr rs
  headSafe : ∃ c0 cs0, rs.toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ',' ∧ c0 ≠ ']' ∧ c0 ≠ '}'
  parses : ∃ v', TomlEquiv v v' ∧ ∀ rest, DelimTail rest →
    ∀ fuel, rs.toList.length ≤ fuel → parseValueFuel numApi fuel (rs.toList ++ rest) = .ok (v', rest)

private theorem headSafe_of_not_delim {c0 : Char} (h : (!isUnquotedDelim c0) = true) :
    isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ',' ∧ c0 ≠ ']' ∧ c0 ≠ '}' := by
  simp only [isUnquotedDelim, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
private theorem headSafe_of_prefix (p rest : String) (c0 : Char) (cs0 : List Char) (hp : p.toList = c0 :: cs0)
    (hs : isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ',' ∧ c0 ≠ ']' ∧ c0 ≠ '}') :
    ∃ c cs, (p ++ rest).toList = c :: cs ∧ isHorizWs c = false ∧ c ≠ '\n' ∧ c ≠ '#' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' :=
  ⟨c0, cs0 ++ rest.toList, by simp [String.toList_append, hp], hs⟩
private theorem digit_not_quote_or_open {c0 : Char} (hd : isAsciiDigit c0 = true) :
    c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{' := by refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; revert hd; decide)

private theorem parseValueFuel_unquoted (numApi : CharNumApi) (fuel : Nat) (c0 : Char) (cs : List Char)
    (hq1 : c0 ≠ '"') (hq2 : c0 ≠ '\'') (hb : c0 ≠ '[') (hbr : c0 ≠ '{') :
    parseValueFuel numApi (fuel + 1) (c0 :: cs) =
      (let (tok, rest) := takeUnquotedTokenChars (c0 :: cs); classifyScalarChars numApi tok >>= fun v => .ok (v, rest)) := by
  conv => lhs; unfold parseValueFuel
  split <;> first
    | exact absurd rfl hq1 | exact absurd rfl hq2 | exact absurd rfl hb | exact absurd rfl hbr
    | (rename_i heq; injection heq with h1 _; first | exact absurd h1 hq1 | exact absurd h1 hq2 | exact absurd h1 hb | exact absurd h1 hbr)
    | rfl

private theorem classifyScalarChars_of_dateTime (numApi : CharNumApi) (c0 : Char) (cs0 : List Char)
    (hdigit : isAsciiDigit c0 = true) {v : TomlValue} (hdt : parseDateTimeChars (c0 :: cs0) = some (.ok v)) :
    classifyScalarChars numApi (c0 :: cs0) = .ok v := by
  unfold classifyScalarChars; split
  · contradiction
  · next h => cases h; exact absurd hdigit (by decide)
  · next h => cases h; exact absurd hdigit (by decide)
  · simp [hdt]

private theorem unquoted_renderValSpec (numApi : CharNumApi) {v v' : TomlValue} {rs : String}
    (heqv : TomlEquiv v v') (hcls : classifyScalarChars numApi rs.toList = .ok v') (hcl : CleanStr rs)
    (hhd : ∃ c0 cs0, rs.toList = c0 :: cs0 ∧ (!isUnquotedDelim c0) = true ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{')
    (htok : ∀ rest, DelimTail rest → takeUnquotedTokenChars (rs.toList ++ rest) = (rs.toList, rest)) :
    RenderValSpec numApi v rs := by
  rcases hhd with ⟨c0, cs0, hlist, hnd, hq1, hq2, hb, hbr⟩
  refine ⟨hcl, ⟨c0, cs0, hlist, headSafe_of_not_delim hnd⟩, v', heqv, fun rest hrest fuel hf => ?_⟩
  cases fuel with
  | zero => rw [hlist] at hf; simp at hf
  | succ f =>
    rw [hlist, List.cons_append, parseValueFuel_unquoted numApi f c0 (cs0 ++ rest) hq1 hq2 hb hbr,
      ← List.cons_append, ← hlist, htok rest hrest]; simp [hcls, bind, Except.bind]

private theorem noSpace_unquoted_renderValSpec (numApi : CharNumApi) {v v' : TomlValue} {rs : String}
    (heqv : TomlEquiv v v') (hcls : classifyScalarChars numApi rs.toList = .ok v')
    (hcl : (rs.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true)
    (hhd : ∃ c0 cs0, rs.toList = c0 :: cs0 ∧ c0 ≠ '"' ∧ c0 ≠ '\'' ∧ c0 ≠ '[' ∧ c0 ≠ '{') :
    RenderValSpec numApi v rs := by
  rcases hhd with ⟨c0, cs0, hlist, hq1, hq2, hb, hbr⟩
  have hnd_all := clean_all_not_unquotedDelim _ hcl
  exact unquoted_renderValSpec numApi heqv hcls (cleanChars_of_full hcl)
    ⟨c0, cs0, hlist, List.all_eq_true.mp hnd_all c0 (by rw [hlist]; simp), hq1, hq2, hb, hbr⟩
    (fun rest hrest => takeUnquotedToken_noSpace rs.toList rest hnd_all hrest)

private theorem dateOrTime_renderValSpec (numApi : CharNumApi) {v : TomlValue} {rs : String}
    (hdt : parseDateTimeChars rs.toList = some (.ok v))
    (hcl : (rs.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true)
    (hhd : ∀ c r, rs.toList = c :: r → isAsciiDigit c = true) : RenderValSpec numApi v rs := by
  cases hlist : rs.toList with
  | nil => simp [hlist, parseDateTimeChars, hasDatePrefix, hasTimePrefix] at hdt
  | cons c0 cs0 =>
    have hdig := hhd c0 cs0 hlist; have hqo := digit_not_quote_or_open hdig
    exact noSpace_unquoted_renderValSpec numApi (tomlEquiv_refl v)
      (by rw [hlist] at hdt ⊢; exact classifyScalarChars_of_dateTime numApi c0 cs0 hdig hdt) hcl
      ⟨c0, cs0, hlist, hqo.1, hqo.2.1, hqo.2.2.1, hqo.2.2.2⟩

private theorem dateTime_compound_renderValSpec (numApi : CharNumApi)
    (d : Std.Time.PlainDate) (t : Std.Time.PlainTime) (sep : DateTimeSep) (fd : Nat)
    (ds ts suf : String) (v : TomlValue) (hdr : renderDate d = some ds) (htr : renderTime t fd = some ts)
    (hsuf : (suf.toList.all fun c => !isDisallowedControl c && c != '\r' && c != '\n' && !isUnquotedDelim c) = true)
    (hdt : parseDateTimeChars (ds ++ renderDateTimeSep sep ++ ts ++ suf).toList = some (.ok v)) :
    RenderValSpec numApi v (ds ++ renderDateTimeSep sep ++ ts ++ suf) := by
  obtain ⟨hdt_d, hds_cl, hds_hd⟩ := renderDate_localDate d ds hdr
  obtain ⟨_, hts_cl, _⟩ := renderTime_localTime t fd ts htr
  cases hds_list : ds.toList with
  | nil => simp [hds_list, parseDateTimeChars, hasDatePrefix, hasTimePrefix] at hdt_d
  | cons c0 cs0 =>
    have hdig := hds_hd c0 cs0 hds_list; have hqo := digit_not_quote_or_open hdig
    have hnd0 := List.all_eq_true.mp (clean_all_not_unquotedDelim _ hds_cl) c0 (by rw [hds_list]; simp)
    have hfull_list : (ds ++ renderDateTimeSep sep ++ ts ++ suf).toList =
        c0 :: (cs0 ++ (renderDateTimeSep sep ++ ts ++ suf).toList) := by
      simp [String.toList_append, hds_list, List.cons_append, List.append_assoc]
    have hcl := cleanStr_append (cleanStr_append (cleanStr_append (cleanChars_of_full hds_cl)
      (show CleanStr (renderDateTimeSep sep) by cases sep <;> decide)) (cleanChars_of_full hts_cl)) (cleanChars_of_full hsuf)
    refine unquoted_renderValSpec numApi (tomlEquiv_refl v)
      (by rw [hfull_list] at hdt ⊢; exact classifyScalarChars_of_dateTime numApi c0 _ hdig hdt) hcl
      ⟨c0, _, hfull_list, hnd0, hqo.1, hqo.2.1, hqo.2.2.1, hqo.2.2.2⟩ (fun rest hrest => ?_)
    by_cases hsp : sep = .space
    · subst hsp; exact dateTime_space_takeUnquotedToken d t fd ds ts suf hdr htr
        (clean_all_not_unquotedDelim _ hsuf) rest (fun c r h => (hrest c r h).1)
    · have hsep_nd : (renderDateTimeSep sep).toList.all (fun c => !isUnquotedDelim c) = true := by
        cases sep <;> first | exact absurd rfl hsp | decide
      exact takeUnquotedToken_noSpace _ rest (by simp only [String.toList_append, List.all_append,
        clean_all_not_unquotedDelim _ hds_cl, hsep_nd, clean_all_not_unquotedDelim _ hts_cl,
        clean_all_not_unquotedDelim _ hsuf, Bool.and_self]) hrest

private def IsScalar : TomlValue → Prop | .array _ | .table _ => False | _ => True

private theorem renderValueInline_scalar_spec (numApi : CharNumApi) (hApi : ValidCharNum numApi)
    (v : TomlValue) (tape : ValueTape) (rs : String) (hr : renderValueInline v tape = some rs)
    (hscalar : IsScalar v) : RenderValSpec numApi v rs := by
  cases v with
  | array _ | table _ => nomatch hscalar
  | string s =>
    cases tape <;> (simp only [renderValueInline] at hr; try contradiction)
    rename_i st
    have hhd : ∃ c0 cs0, rs.toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ',' ∧ c0 ≠ ']' ∧ c0 ≠ '}' := by
      have hhr := hr; cases st <;> simp only [renderStringLiteral] at hhr
      · injection hhr with e; subst e; rw [String.append_assoc]; exact headSafe_of_prefix "\"" _ '"' [] rfl (by decide)
      · injection hhr with e; subst e; rw [String.append_assoc]; exact headSafe_of_prefix "\"\"\"\n" _ '"' ['"', '"', '\n'] rfl (by decide)
      · split at hhr
        · injection hhr with e; subst e; rw [String.append_assoc]; exact headSafe_of_prefix "'" _ '\'' [] rfl (by decide)
        · cases hhr
      · split at hhr
        · injection hhr with e; subst e; rw [String.append_assoc]; exact headSafe_of_prefix "'''\n" _ '\'' ['\'', '\'', '\n'] rfl (by decide)
        · cases hhr
    obtain ⟨_, hcl, _⟩ := renderStringLiteral_parseValueFuel numApi s st rs hr [] 1 (by omega) (fun _ _ h => nomatch h)
    refine ⟨hcl, hhd, .string s, tomlEquiv_refl _, fun rest hrest fuel hf => ?_⟩
    rcases hhd with ⟨_, _, hlist, _⟩
    exact (renderStringLiteral_parseValueFuel numApi s st rs hr rest fuel (by rw [hlist] at hf; simp at hf; omega)
      (fun c r h => by have hd := (hrest c r h).1; constructor <;> (rintro rfl; cases hd))).1
  | int n =>
    cases tape with
    | int olex =>
      have hlex : isValidIntLex rs n = true := by
        cases olex <;> simp only [renderValueInline] at hr
        · injection hr with e; subst e; exact formatInt64Canonical_isValidIntLex n
        · rename_i val; cases hv : isValidIntLex val n <;> simp [hv] at hr; subst hr; exact hv
      obtain ⟨hcls, hcl, hhd⟩ := isValidIntLex_classifyScalarToken numApi hApi.1 rs n hlex
      exact noSpace_unquoted_renderValSpec numApi (tomlEquiv_refl _) hcls hcl hhd
    | _ => simp [renderValueInline] at hr
  | float fl =>
    cases tape with
    | float olex =>
      have hlex : isValidFloatLex rs fl = true := by
        cases olex <;> simp only [renderValueInline] at hr
        · rcases canonicalFloat_isValidFloatLex fl with ⟨c1, c2, c3, c4, c5⟩
          by_cases h1 : fl.isNaN; · simp [h1] at hr; subst hr; exact c1 h1
          by_cases h2 : fl == Float.inf; · simp [h1, h2] at hr; subst hr; exact c2 h2
          by_cases h3 : fl == -Float.inf; · simp [h1, h2, h3] at hr; subst hr; exact c3 h3
          by_cases h4 : fl.toBits == (0.0 : Float).toBits; · simp [h1, h2, h3, h4] at hr; subst hr; exact c4 (by simpa using h4)
          by_cases h5 : fl.toBits == (-0.0 : Float).toBits; · simp [h1, h2, h3, h4, h5] at hr; subst hr; exact c5 (by simpa using h5)
          simp [h1, h2, h3, h4, h5] at hr
        · rename_i val; cases hv : isValidFloatLex val fl <;> simp [hv] at hr; subst hr; exact hv
      obtain ⟨_, hcls, heq_f, hcl, hhd⟩ := isValidFloatLex_classifyScalarToken numApi hApi.2 rs fl hlex
      exact noSpace_unquoted_renderValSpec numApi heq_f hcls hcl hhd
    | _ => simp [renderValueInline] at hr
  | bool b =>
    cases tape <;> (simp only [renderValueInline] at hr; try contradiction)
    cases b <;> simp at hr <;> subst hr
    · exact noSpace_unquoted_renderValSpec numApi (tomlEquiv_refl _) rfl (by decide) ⟨'f', ['a', 'l', 's', 'e'], rfl, by decide⟩
    · exact noSpace_unquoted_renderValSpec numApi (tomlEquiv_refl _) rfl (by decide) ⟨'t', ['r', 'u', 'e'], rfl, by decide⟩
  | localDate d =>
    cases tape <;> (simp only [renderValueInline] at hr; try contradiction)
    obtain ⟨hdt, hcl, hhd⟩ := renderDate_localDate d rs hr; exact dateOrTime_renderValSpec numApi hdt hcl hhd
  | localTime t =>
    cases tape <;> (simp only [renderValueInline] at hr; try contradiction)
    rename_i fd; obtain ⟨hdt, hcl, hhd⟩ := renderTime_localTime t fd rs hr; exact dateOrTime_renderValSpec numApi hdt hcl hhd
  | localDateTime dt =>
    cases tape <;> (simp only [renderValueInline, bind_some, Option.some.injEq] at hr; try contradiction)
    rename_i sep fd; rcases hr with ⟨ds, hdr, ts, htr, rfl⟩
    simpa [String.append_empty] using dateTime_compound_renderValSpec numApi dt.date dt.time sep fd ds ts "" (.localDateTime dt) hdr htr
      (by decide) (by simpa [String.append_empty] using renderDateTime_localDateTime dt sep fd ds ts hdr htr)
  | offsetDateTime odt =>
    cases tape <;> (simp only [renderValueInline, bind_some, Option.some.injEq] at hr; try contradiction)
    rename_i sep oStyle fd; rcases hr with ⟨ds, hdr, ts, htr, os, hor, rfl⟩
    exact dateTime_compound_renderValSpec numApi odt.dateTime.date odt.dateTime.time sep fd ds ts os (.offsetDateTime odt) hdr htr
      (renderOffset_parseOffsetPart odt.offset oStyle os hor).2 (renderOffsetDateTime_offsetDateTime odt sep oStyle fd ds ts os hdr htr hor)

private theorem skipHorizWs_cons_of_false (c : Char) (cs : List Char) (h : isHorizWs c = false) :
    skipHorizWs (c :: cs) = c :: cs := by simp [skipHorizWs, h]
private theorem skipHorizWs_space (cs : List Char) : skipHorizWs (' ' :: cs) = skipHorizWs cs := by simp [skipHorizWs, isHorizWs]
private theorem skipTriviaNewlines_cons_of_safe (c : Char) (cs : List Char)
    (hws : isHorizWs c = false) (hn : c ≠ '\n') (hc : c ≠ '#') : skipTriviaNewlines (c :: cs) = c :: cs := by
  unfold skipTriviaNewlines skipTriviaNewlinesAux; split
  · rename_i heq; cases heq
  · rename_i heq; injection heq with h1; exact absurd h1 hn
  · rename_i _ _ _ heq; injection heq with h1 h2; subst h1; subst h2; simp [hws, beq_iff_eq, hc]
private theorem parseArrayFuel_skip_space (numApi : CharNumApi) (fuel : Nat) (cs : List Char) (revAcc : List TomlValue) :
    parseArrayFuel numApi fuel (' ' :: cs) revAcc = parseArrayFuel numApi fuel cs revAcc := by
  cases fuel with
  | zero => rfl
  | succ _ => simp [parseArrayFuel, show skipTriviaNewlines (' ' :: cs) = skipTriviaNewlines cs by simp [skipTriviaNewlines, skipTriviaNewlinesAux, isHorizWs]]

private theorem renderKey_props (k : String) (ks : KeyStyle) (rk : String) (hr : renderKey k ks = some rk) :
    CleanStr rk ∧ ∃ c0 cs0, rk.toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧
      c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ '[' ∧ c0 ≠ '.' := by
  refine ⟨cleanChars_of_no_nl (renderKey_parseKeySegment k ks rk hr [' '] (fun c _ h => by injection h with h1 _; subst h1; decide)).2, ?_⟩
  cases ks <;> simp only [renderKey] at hr
  · split at hr
    · rename_i hbare; injection hr with hrk; subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      cases hlist : k.toList with
      | nil => have h0 : k = "" := by rw [← String.ofList_toList (s := k), hlist]
               subst h0; simp at hbare
      | cons c0 cs0 =>
        have hc0 := List.all_eq_true.mp hbare.2 c0 (by rw [hlist]; simp)
        have hws0 : isHorizWs c0 = false := Bool.eq_false_iff.mpr fun h => by
          simp [isHorizWs] at h; rcases h with rfl | rfl <;> nomatch hc0
        refine ⟨c0, cs0, rfl, hws0, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; nomatch hc0)
    · cases hr
  · injection hr with hrk; subst hrk; exact ⟨'"', (escapeBasicBody false k ++ "\"").toList, by simp [String.toList_append], by decide⟩
  · split at hr
    · injection hr with hrk; subst hrk; exact ⟨'\'', (k ++ "'").toList, by simp [String.toList_append], by decide⟩
    · cases hr

private theorem joinRenderedPath_props (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2) :
    (∃ c0 cs0, (joinRenderedPath (pairs.map Prod.snd)).toList = c0 :: cs0 ∧
      isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ '[' ∧ c0 ≠ ']' ∧ c0 ≠ '}' ∧ c0 ≠ '.') ∧
    CleanStr (joinRenderedPath (pairs.map Prod.snd)) ∧
    pairs.length ≤ (joinRenderedPath (pairs.map Prod.snd)).toList.length := by
  induction pairs with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    rcases p with ⟨k, rk⟩; obtain ⟨ks, hrk⟩ := hkeys (k, rk) (by simp)
    obtain ⟨hrk_cl, c0, cs0, hrk_list, hws0, hn0, hc0, hbr0, hrb0, hl0, hdot0⟩ := renderKey_props k ks rk hrk
    have hrk_len : 1 ≤ rk.toList.length := by rw [hrk_list]; simp
    cases ps with
    | nil =>
      exact ⟨⟨c0, cs0, by simpa [joinRenderedPath] using hrk_list, hws0, hn0, hc0, hl0, hbr0, hrb0, hdot0⟩,
        by simpa [joinRenderedPath] using hrk_cl, by simpa [joinRenderedPath] using hrk_len⟩
    | cons p2 ps2 =>
      obtain ⟨_, hcl_ps, hlen_ps⟩ := ih (by simp) (fun q hq => hkeys q (by simp [hq]))
      have hjoin : joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd) = rk ++ "." ++ joinRenderedPath ((p2 :: ps2).map Prod.snd) := rfl
      refine ⟨⟨c0, cs0 ++ ('.' :: (joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList), ?_, hws0, hn0, hc0, hl0, hbr0, hrb0, hdot0⟩,
        by rw [hjoin]; exact cleanStr_append (cleanStr_append hrk_cl (cleanStr_lit ".")) hcl_ps, ?_⟩
      · rw [hjoin, String.toList_append, String.toList_append, hrk_list]; simp [List.cons_append, List.append_assoc]
      · rw [hjoin, String.toList_append, String.toList_append, List.length_append, List.length_append]
        simp only [List.length_cons] at hlen_ps ⊢; omega

private theorem parseDottedKey_joinRenderedPath (pairs : List (String × String)) (hne : pairs ≠ [])
    (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2) (rest : List Char)
    (hrest : ∀ c tail, rest = c :: tail → !isBareKeyChar c = true ∧ c ≠ '"' ∧ c ≠ '\'')
    (hsw : ∃ c2 t2, skipHorizWs rest = c2 :: t2 ∧ c2 ≠ '.') :
    parseDottedKey ((joinRenderedPath (pairs.map Prod.snd)).toList ++ rest) = .ok (pairs.map Prod.fst, skipHorizWs rest) := by
  have hfuel : ∀ (ps : List (String × String)), ps ≠ [] →
      (∀ p ∈ ps, ∃ ks, renderKey p.1 ks = some p.2) → ∀ fuel, ps.length ≤ fuel →
      parseDottedKeyFuel fuel ((joinRenderedPath (ps.map Prod.snd)).toList ++ rest) = .ok (ps.map Prod.fst, skipHorizWs rest) := by
    intro ps hps_ne hps_k fuel hf; induction ps generalizing fuel with
    | nil => exact absurd rfl hps_ne
    | cons p tl ih =>
      rcases p with ⟨k, rk⟩; obtain ⟨ks, hrk⟩ := hps_k (k, rk) (by simp)
      cases fuel with
      | zero => simp at hf
      | succ f =>
        cases tl with
        | nil =>
          simp only [List.map_cons, List.map_nil, joinRenderedPath]; unfold parseDottedKeyFuel
          rw [(renderKey_parseKeySegment k ks rk hrk rest hrest).1]; simp only [bind, Except.bind]
          rcases hsw with ⟨c2, t2, hsw_eq, hne_dot⟩; rw [hsw_eq]; split
          · rename_i heq; injection heq with h1 _; exact absurd h1 hne_dot
          · rfl
        | cons p2 ps2 =>
          have htl_k : ∀ q ∈ p2 :: ps2, ∃ ks, renderKey q.1 ks = some q.2 := fun q hq => hps_k q (by simp [hq])
          obtain ⟨⟨c2, _, hps_list, hws2, _⟩, _, _⟩ := joinRenderedPath_props (p2 :: ps2) (by simp) htl_k
          have hsplit : (joinRenderedPath (((k, rk) :: p2 :: ps2).map Prod.snd)).toList ++ rest =
              rk.toList ++ ('.' :: ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest)) := by
            change (rk ++ "." ++ joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest = _
            rw [String.toList_append, String.toList_append, List.append_assoc]; simp
          rw [hsplit]; unfold parseDottedKeyFuel
          rw [(renderKey_parseKeySegment k ks rk hrk _ (fun c _ h => by injection h with h1 _; subst h1; decide)).1]
          simp only [bind, Except.bind, skipHorizWs_cons_of_false '.' _ (by decide)]
          rw [show skipHorizWs ((joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest) =
                (joinRenderedPath ((p2 :: ps2).map Prod.snd)).toList ++ rest by
              rw [hps_list, List.cons_append]; exact skipHorizWs_cons_of_false c2 _ hws2,
            ih (by simp) htl_k f (by simp at hf; omega)]; rfl
  unfold parseDottedKey; have := (joinRenderedPath_props pairs hne hkeys).2.2
  exact hfuel pairs hne hkeys _ (by simp; omega)

mutual
  private theorem nodeToTomlValue_valueToInlineNode : (v : TomlValue) → nodeToTomlValue (valueToInlineNode v) = v
    | .table ⟨entries⟩ => by simp [valueToInlineNode, nodeToTomlValue, entriesToTomlList_inlineListToNodes entries]
    | .string _ | .int _ | .float _ | .bool _ | .offsetDateTime _ | .localDateTime _ | .localDate _ | .localTime _ | .array _ => rfl
  termination_by v => sizeOf v
  private theorem entriesToTomlList_inlineListToNodes : (entries : List (String × TomlValue)) → entriesToTomlList (inlineListToNodes entries) = entries
    | [] => rfl
    | (_, v) :: rest => by simp [inlineListToNodes, entriesToTomlList, nodeToTomlValue_valueToInlineNode v, entriesToTomlList_inlineListToNodes rest]
  termination_by entries => sizeOf entries
end

private theorem lookupKeyList_filter_ne (k q : String) (l : List (String × TomlValue)) :
    lookupKeyList q (l.filter fun p => p.1 != k) = if q == k then none else lookupKeyList q l := by
  induction l with
  | nil => simp [lookupKeyList]
  | cons p ps ih =>
    rcases p with ⟨pk, _⟩; by_cases hpk : pk == k
    · have h := beq_iff_eq.mp hpk; subst h
      by_cases hqk : (q == pk) = true <;> simp [List.filter, lookupKeyList, hqk, ih]
    · simp only [List.filter, (by simp [bne, hpk] : (pk != k) = true), lookupKeyList]
      by_cases hqp : (q == pk) = true
      · rw [beq_iff_eq.mp hqp]; simp [Bool.eq_false_iff.mpr hpk]
      · simp [hqp, ih]

private theorem assocLookupNode_assocSetNode (k q : String) (n : Node) (acc : List (String × Node)) :
    assocLookupNode q (assocSetNode k n acc) = if q == k then some n else assocLookupNode q acc := by
  induction acc with
  | nil => simp [assocSetNode, assocLookupNode]
  | cons p _ ih =>
    rcases p with ⟨pk, _⟩; simp only [assocSetNode]
    by_cases hkp : k == pk
    · have hpk := (beq_iff_eq.mp hkp).symm; subst hpk; by_cases hqp : (q == pk) = true <;> simp [assocLookupNode, hqp]
    · simp only [hkp, Bool.false_eq_true, ↓reduceIte, assocLookupNode]
      by_cases hqp : q == pk
      · simp [hqp, Bool.eq_false_iff.mpr fun h => hkp (beq_iff_eq.mpr ((beq_iff_eq.mp h).symm.trans (beq_iff_eq.mp hqp)))]
      · simp [hqp, ih]
private theorem assocLookupNode_assocSetNode_ne (k q : String) (v : Node) (l : List (String × Node)) (hne : q ≠ k) :
    assocLookupNode q (assocSetNode k v l) = assocLookupNode q l := by rw [assocLookupNode_assocSetNode, beq_false_of_ne hne]; rfl
private theorem assocSetNode_idem (k : String) (v1 v2 : Node) (l : List (String × Node)) :
    assocSetNode k v2 (assocSetNode k v1 l) = assocSetNode k v2 l := by
  induction l with | nil => simp [assocSetNode] | cons p _ ih => rcases p with ⟨k', _⟩; by_cases h : k == k' <;> simp [assocSetNode, h, ih]
private theorem lookupKeyList_entriesToTomlList (q : String) (acc : List (String × Node)) :
    lookupKeyList q (entriesToTomlList acc) = (assocLookupNode q acc).map nodeToTomlValue := by
  induction acc with
  | nil => rfl
  | cons p _ ih => rcases p with ⟨pk, _⟩; simp only [entriesToTomlList, lookupKeyList, assocLookupNode]; by_cases h : (q == pk) = true <;> simp [h, ih]
private theorem tomlListEquiv_append_single {l1 l2 : List TomlValue} {x1 x2 : TomlValue}
    (hl : TomlListEquiv l1 l2) (hx : TomlEquiv x1 x2) : TomlListEquiv (l1 ++ [x1]) (l2 ++ [x2]) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [TomlListEquiv, hx] at hl ⊢
  | cons _ _ ih => cases l2 with | nil => simp [TomlListEquiv] at hl | cons _ _ => simp only [TomlListEquiv, List.cons_append] at hl ⊢; exact ⟨hl.1, ih hl.2⟩

private def commaTail (tl : List String) (close : String) : String :=
  match tl with | [] => close | _ :: _ => ", " ++ String.intercalate ", " tl ++ close
private theorem commaTail_props (hd : String) (tl : List String) (close : String) (hcl : close = "]" ∨ close = "}") :
    (String.intercalate ", " (hd :: tl) ++ close).toList = hd.toList ++ (commaTail tl close).toList ∧
    (∀ rest, DelimTail ((commaTail tl close).toList ++ rest)) ∧
    (∀ rest, skipHorizWs ((commaTail tl close).toList ++ rest) = (commaTail tl close).toList ++ rest) := by
  refine ⟨by cases tl <;> simp [commaTail, String.intercalate_singleton, String.intercalate_cons_cons,
    String.toList_append, String.append_assoc], fun rest c r hc => ?_, fun rest => ?_⟩
  · cases tl with
    | nil => rcases hcl with rfl | rfl <;> (simp [commaTail] at hc; rcases hc with ⟨rfl, _⟩; exact ⟨by decide, fun h => nomatch h⟩)
    | cons s2 sr2 =>
      have hc' : ',' :: ' ' :: ((String.intercalate ", " (s2 :: sr2) ++ close).toList ++ rest) = c :: r := by
        simpa [commaTail, String.toList_append, List.cons_append, List.append_assoc] using hc
      injection hc' with hcb _; subst hcb; exact ⟨by decide, fun h => nomatch h⟩
  · cases tl <;> rcases hcl with rfl | rfl <;> simp [commaTail, String.toList_append, List.cons_append, skipHorizWs, isHorizWs]

private theorem renderArrayElems_parseArrayFuel (numApi : CharNumApi)
    (xs : List TomlValue) (tps : List ValueTape) (strs : List String)
    (harr : renderValueInline.renderArrayElems xs tps = some strs)
    (hVal : ∀ x ∈ xs, ∀ tp rs, renderValueInline x tp = some rs → RenderValSpec numApi x rs)
    (origPrefix revAcc : List TomlValue) (hacc : TomlListEquiv origPrefix revAcc.reverse) :
    ∃ ys : Array TomlValue, TomlListEquiv (origPrefix ++ xs) ys.toList ∧ CleanStr (String.intercalate ", " strs ++ "]") ∧
      ∀ rest fuel, (String.intercalate ", " strs ++ "]").toList.length ≤ fuel →
        parseArrayFuel numApi fuel ((String.intercalate ", " strs ++ "]").toList ++ rest) revAcc = .ok (.array ys, rest) := by
  induction xs generalizing tps strs origPrefix revAcc with
  | nil =>
    cases tps <;> simp [renderValueInline.renderArrayElems] at harr; subst harr
    refine ⟨revAcc.reverse.toArray, by simpa using hacc, by decide, fun rest fuel hf => ?_⟩
    cases fuel with | zero => simp at hf | succ _ => simp [String.intercalate_nil, parseArrayFuel, skipTriviaNewlines_cons_of_safe ']' rest (by decide) (by decide) (by decide)]
  | cons x xr ih =>
    cases tps <;> (simp only [renderValueInline.renderArrayElems, bind_some, Option.some.injEq] at harr; try contradiction)
    rename_i tp tpr; rcases harr with ⟨sx, hx, sr, hxr, rfl⟩
    obtain ⟨hcl_x, ⟨c0, _, hsx_list, hws0, hn0, hc0, _, hbr0, _⟩, v', heqv, hpv_x⟩ := hVal x (by simp) tp sx hx
    obtain ⟨hinterc, htail_delim, _⟩ := commaTail_props sx sr "]" (Or.inl rfl)
    have hacc' : TomlListEquiv (origPrefix ++ [x]) (v' :: revAcc).reverse := by simp only [List.reverse_cons]; exact tomlListEquiv_append_single hacc heqv
    have hstep : ∀ rest f, sx.toList.length ≤ f →
        parseArrayFuel numApi (f + 1) ((String.intercalate ", " (sx :: sr) ++ "]").toList ++ rest) revAcc =
          match skipTriviaNewlines ((commaTail sr "]").toList ++ rest) with
          | ',' :: afterComma => parseArrayFuel numApi f afterComma (v' :: revAcc)
          | ']' :: afterClose => .ok (.array (v' :: revAcc).reverse.toArray, afterClose)
          | _ => .error (mkErr .parseError "expected ',' or ']' in TOML array") := fun rest f hfx => by
      rw [hinterc, List.append_assoc]; conv => lhs; unfold parseArrayFuel
      rw [show skipTriviaNewlines (sx.toList ++ ((commaTail sr "]").toList ++ rest)) = sx.toList ++ ((commaTail sr "]").toList ++ rest) by
        rw [hsx_list, List.cons_append]; exact skipTriviaNewlines_cons_of_safe c0 _ hws0 hn0 hc0]
      split
      · rename_i heq; rw [hsx_list, List.cons_append] at heq; injection heq with h1 _; exact absurd h1 hbr0
      · rename_i heq; rw [hsx_list] at heq; simp at heq
      · simp only [hpv_x _ (htail_delim rest) f hfx, bind, Except.bind]; rfl
    cases xr with
    | nil =>
      cases tpr <;> simp [renderValueInline.renderArrayElems] at hxr; subst hxr
      refine ⟨(v' :: revAcc).reverse.toArray, hacc', by rw [CleanStr, hinterc]; exact cleanChars_append hcl_x (cleanStr_lit "]"), fun rest fuel hf => ?_⟩
      cases fuel with
      | zero => rw [hinterc] at hf; simp [commaTail] at hf
      | succ f =>
        rw [hstep rest f (by rw [hinterc, List.length_append] at hf; simp [commaTail] at hf; omega)]
        simp [commaTail, skipTriviaNewlines_cons_of_safe ']' rest (by decide) (by decide) (by decide)]
    | cons x2 xr2 =>
      cases tpr <;> (simp only [renderValueInline.renderArrayElems] at hxr; try contradiction)
      rename_i tp2 tpr2
      have ⟨s2, sr2, hsr_eq⟩ : ∃ s2 sr2, sr = s2 :: sr2 := by
        have hxr' := hxr; simp only [bind_some, Option.some.injEq] at hxr'
        rcases hxr' with ⟨s2, _, sr2, _, rfl⟩; exact ⟨s2, sr2, rfl⟩
      subst hsr_eq
      obtain ⟨ys, hys_eqv, hys_cl, hys_parse⟩ :=
        ih (tp2 :: tpr2) (s2 :: sr2) hxr (fun y hy => hVal y (by simp [hy])) (origPrefix ++ [x]) (v' :: revAcc) hacc'
      refine ⟨ys, by simpa [List.append_assoc] using hys_eqv,
        by rw [CleanStr, hinterc]; exact cleanChars_append hcl_x (by dsimp only [commaTail]; rw [String.append_assoc]; exact cleanStr_append (cleanStr_lit ", ") hys_cl),
        fun rest fuel hf => ?_⟩
      cases fuel with
      | zero => rw [hinterc, hsx_list] at hf; simp at hf
      | succ f =>
        have : 1 ≤ sx.toList.length := by rw [hsx_list]; simp
        have h2 : (", " : String).toList.length = 2 := rfl
        have hfx : sx.toList.length ≤ f ∧ (String.intercalate ", " (s2 :: sr2) ++ "]").toList.length ≤ f := by
          rw [hinterc, List.length_append] at hf; simp only [commaTail, String.toList_append, List.length_append, h2] at hf ⊢; omega
        rw [hstep rest f hfx.1, show (commaTail (s2 :: sr2) "]").toList ++ rest =
            ',' :: ' ' :: ((String.intercalate ", " (s2 :: sr2) ++ "]").toList ++ rest) by
          simp [commaTail, String.toList_append, List.cons_append, List.append_assoc],
          skipTriviaNewlines_cons_of_safe ',' _ (by decide) (by decide) (by decide)]
        simp only [parseArrayFuel_skip_space]; exact hys_parse rest f hfx.2

private theorem renderInlineTableEntries_nil_inv {rem : List (String × TomlValue)} {kvs : List String}
    (h : renderValueInline.renderInlineTableEntries rem [] = some kvs) : rem = [] ∧ kvs = [] := by
  cases h0 : rem.isEmpty <;> simp [renderValueInline.renderInlineTableEntries, h0] at h
  exact ⟨List.isEmpty_iff.mp h0, h⟩

private theorem renderInlineTableEntries_cons_inv {rem : List (String × TomlValue)}
    {k : String} {ks : KeyStyle} {vt : ValueTape} {restTapes : List (String × KeyStyle × ValueTape)} {kvs : List String}
    (h : renderValueInline.renderInlineTableEntries rem ((k, ks, vt) :: restTapes) = some kvs) :
    ∃ v rk rv tailKvs, lookupKeyList k rem = some v ∧ renderKey k ks = some rk ∧ renderValueInline v vt = some rv ∧
      renderValueInline.renderInlineTableEntries (rem.filter fun p => p.1 != k) restTapes = some tailKvs ∧
      kvs = (rk ++ " = " ++ rv) :: tailKvs := by
  cases hlk : lookupKeyList k rem <;> (simp only [renderValueInline.renderInlineTableEntries, hlk, bind_some, Option.some.injEq] at h; try contradiction)
  rename_i v; rcases h with ⟨rk, hrk, rv, hrv, tailKvs, htail, rfl⟩; exact ⟨v, rk, rv, tailKvs, rfl, hrk, hrv, htail, rfl⟩

private theorem renderInlineTableEntries_nonempty_head {rem : List (String × TomlValue)}
    {e : String × KeyStyle × ValueTape} {er : List (String × KeyStyle × ValueTape)} {kvs : List String}
    (h : renderValueInline.renderInlineTableEntries rem (e :: er) = some kvs) :
    ∃ kv kvr c0 cs0, kvs = kv :: kvr ∧ (String.intercalate ", " (kv :: kvr) ++ "}").toList = c0 :: cs0 ∧ isHorizWs c0 = false ∧ c0 ≠ '}' := by
  rcases e with ⟨k, ks, vt⟩
  obtain ⟨_, rk, rv, tailKvs, _, hrk, _, _, rfl⟩ := renderInlineTableEntries_cons_inv h
  obtain ⟨_, ck0, csk0, hrk_list, hkws0, _, _, _, hbr0, _, _⟩ := renderKey_props k ks rk hrk
  obtain ⟨hinterc, _, _⟩ := commaTail_props (rk ++ " = " ++ rv) tailKvs "}" (Or.inr rfl)
  exact ⟨rk ++ " = " ++ rv, tailKvs, ck0, csk0 ++ (" = " ++ rv).toList ++ (commaTail tailKvs "}").toList, rfl,
    by rw [hinterc]; simp [String.toList_append, hrk_list, List.cons_append, List.append_assoc], hkws0, hbr0⟩

private def InlTabInv (orig rem : List (String × TomlValue)) (acc : List (String × Node)) : Prop :=
  (∀ q v, lookupKeyList q rem = some v → lookupKeyList q orig = some v ∧ assocLookupNode q acc = none) ∧
  (∀ q, lookupKeyList q rem = none →
    (lookupKeyList q orig = none → lookupKeyList q (entriesToTomlList acc) = none) ∧
    (∀ v1, lookupKeyList q orig = some v1 → ∃ v2, lookupKeyList q (entriesToTomlList acc) = some v2 ∧ TomlEquiv v1 v2))

private theorem renderInlineTableEntries_parseInlineTableFuel (numApi : CharNumApi)
    (origEntries rem : List (String × TomlValue)) (entryTapes : List (String × KeyStyle × ValueTape)) (kvs : List String)
    (htab : renderValueInline.renderInlineTableEntries rem entryTapes = some kvs) (hne : entryTapes ≠ [])
    (hVal : ∀ q v, lookupKeyList q origEntries = some v → ∀ tp rs, renderValueInline v tp = some rs → RenderValSpec numApi v rs)
    (acc : List (String × Node)) (hinv : InlTabInv origEntries rem acc) :
    ∃ resT : TomlTable, TomlTableEquivList origEntries resT.toList ∧ CleanStr (String.intercalate ", " kvs ++ "}") ∧
      ∀ rest fuel, (String.intercalate ", " kvs ++ "}").toList.length ≤ fuel →
        parseInlineTableFuel numApi fuel ((String.intercalate ", " kvs ++ "}").toList ++ rest) acc = .ok (.table resT, rest) := by
  induction entryTapes generalizing rem kvs acc with
  | nil => exact absurd rfl hne
  | cons entry restTapes ih =>
    rcases entry with ⟨k, ks, vt⟩
    obtain ⟨v, rk, rv, tailKvs, hlk, hrk, hrv, htail, rfl⟩ := renderInlineTableEntries_cons_inv htab
    let rem' := rem.filter (fun p => p.1 != k)
    change renderValueInline.renderInlineTableEntries rem' restTapes = some tailKvs at htail
    obtain ⟨hcl_k, ck0, _, hrk_list, hkws0, _⟩ := renderKey_props k ks rk hrk
    obtain ⟨hv_orig, hk_acc⟩ := hinv.1 k v hlk
    obtain ⟨hcl_v, ⟨cv0, _, hrv_list, hvws0, _⟩, v', heqv, hpv_v⟩ := hVal k v hv_orig vt rv hrv
    obtain ⟨hinterc0, hafter_delim, hafter_sw⟩ := commaTail_props (rk ++ " = " ++ rv) tailKvs "}" (Or.inr rfl)
    have hinterc : (String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList =
        rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ (commaTail tailKvs "}").toList)) := by
      rw [hinterc0]; simp [String.toList_append, List.append_assoc, List.cons_append]
    let nextAcc := assocSetNode k (valueToInlineNode v') acc
    have hstep_one : ∀ rest f, rv.toList.length ≤ f →
        parseInlineTableFuel numApi (f + 1)
          ((String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList ++ rest) acc =
          match (commaTail tailKvs "}").toList ++ rest with
          | ',' :: afterComma =>
            match skipHorizWs afterComma with
            | '}' :: _ => .error (mkErr .parseError "trailing comma is not allowed in inline table")
            | nextCs => parseInlineTableFuel numApi f nextCs nextAcc
          | '}' :: afterClose => .ok (.table (entriesToTomlList nextAcc).toArray, afterClose)
          | _ => .error (mkErr .parseError "expected ',' or '}' in inline table") := fun rest f hfv => by
      let afterRv := (commaTail tailKvs "}").toList ++ rest
      have hcs1 : skipHorizWs ((String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}").toList ++ rest) =
          rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv)) := by
        rw [hinterc]; simp only [afterRv, List.append_assoc, List.cons_append]
        rw [hrk_list, List.cons_append]; exact skipHorizWs_cons_of_false ck0 _ hkws0
      have hdk : parseDottedKey (rk.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv))) =
          .ok ([k], '=' :: ' ' :: (rv.toList ++ afterRv)) := by
        simpa [joinRenderedPath, skipHorizWs, isHorizWs] using parseDottedKey_joinRenderedPath [(k, rk)] (by simp)
          (fun p hp => by rw [List.mem_singleton.mp hp]; exact ⟨ks, hrk⟩) (' ' :: '=' :: ' ' :: (rv.toList ++ afterRv))
          (fun c _ h => by injection h with hc _; subst hc; decide)
          ⟨'=', ' ' :: (rv.toList ++ afterRv), by simp [skipHorizWs, isHorizWs], by decide⟩
      have hr4 : skipHorizWs (' ' :: (rv.toList ++ afterRv)) = rv.toList ++ afterRv := by
        rw [skipHorizWs_space, hrv_list]; exact skipHorizWs_cons_of_false cv0 _ hvws0
      conv => lhs; unfold parseInlineTableFuel; rw [hcs1]; dsimp only; rw [hdk]
      simp only [bind, Except.bind, skipHorizWs_cons_of_false '=' _ (by decide), hr4,
        hpv_v afterRv (hafter_delim rest) f hfv, show insertDottedEntries [k] acc [k] (valueToInlineNode v') = .ok nextAcc by
          simp [insertDottedEntries, hk_acc, nextAcc], afterRv, hafter_sw rest]; rfl
    have hinv' : InlTabInv origEntries rem' nextAcc := by
      refine ⟨fun q w hqw => ?_, fun q hqn => ?_⟩
      · simp only [rem', lookupKeyList_filter_ne, ite_true_none_some] at hqw
        rcases hqw with ⟨hqk, hqw⟩
        obtain ⟨h1, h2⟩ := hinv.1 q w hqw
        exact ⟨h1, by rw [assocLookupNode_assocSetNode, hqk]; exact h2⟩
      · simp only [rem', lookupKeyList_filter_ne] at hqn
        by_cases hqk : q = k
        · subst hqk
          refine ⟨(fun hqo => by rw [hv_orig] at hqo; cases hqo), fun v1 hqo => ?_⟩
          injection (hv_orig.symm.trans hqo) with hv1; subst hv1
          exact ⟨v', by rw [lookupKeyList_entriesToTomlList, assocLookupNode_assocSetNode]; simp [nodeToTomlValue_valueToInlineNode], heqv⟩
        · simp only [beq_false_of_ne hqk, Bool.false_eq_true, ↓reduceIte] at hqn
          have heq_lu : lookupKeyList q (entriesToTomlList nextAcc) = lookupKeyList q (entriesToTomlList acc) := by
            simp [nextAcc, lookupKeyList_entriesToTomlList, assocLookupNode_assocSetNode, beq_false_of_ne hqk]
          rw [heq_lu]; exact hinv.2 q hqn
    have hcl_kv (h : CleanChars (commaTail tailKvs "}").toList) :
        CleanStr (String.intercalate ", " ((rk ++ " = " ++ rv) :: tailKvs) ++ "}") := by
      rw [CleanStr, hinterc]; refine cleanChars_append hcl_k ?_
      simp only [CleanChars, List.all_cons, Bool.and_eq_true]; exact ⟨by decide, by decide, by decide, cleanChars_append hcl_v h⟩
    cases restTapes with
    | nil =>
      obtain ⟨hrem'_nil, rfl⟩ := renderInlineTableEntries_nil_inv htail
      have hteq : TomlTableEquivList origEntries (entriesToTomlList nextAcc) := by
        unfold TomlTableEquivList
        exact ⟨fun q hq => (hinv'.2 q (by simp [hrem'_nil, lookupKeyList])).1 hq,
          fun q v1 hq => (hinv'.2 q (by simp [hrem'_nil, lookupKeyList])).2 v1 hq⟩
      refine ⟨(entriesToTomlList nextAcc).toArray, hteq, hcl_kv (cleanStr_lit "}"), fun rest fuel hf => ?_⟩
      cases fuel with
      | zero => rw [hinterc] at hf; simp at hf
      | succ f => rw [hstep_one rest f (by rw [hinterc, List.length_append] at hf; simp [commaTail] at hf; omega)]; simp [commaTail]
    | cons e2 er2 =>
      obtain ⟨kv2, kvr2, c_hd, cs_hd, rfl, hhd_list, hhd_ws, hhd_br⟩ := renderInlineTableEntries_nonempty_head htail
      obtain ⟨resT, hres_eqv, hres_cl, hres_parse⟩ := ih rem' (kv2 :: kvr2) htail (by simp) nextAcc hinv'
      refine ⟨resT, hres_eqv, hcl_kv (by dsimp only [commaTail]; rw [String.append_assoc]; exact cleanStr_append (cleanStr_lit ", ") hres_cl),
        fun rest fuel hf => ?_⟩
      cases fuel with
      | zero => rw [hinterc] at hf; simp at hf
      | succ f =>
        have h2 : (", " : String).toList.length = 2 := rfl
        have hfb : rv.toList.length ≤ f ∧ (String.intercalate ", " (kv2 :: kvr2) ++ "}").toList.length ≤ f := by
          have : 1 ≤ rk.toList.length := by rw [hrk_list]; simp
          have : 1 ≤ rv.toList.length := by rw [hrv_list]; simp
          rw [hinterc, List.length_append] at hf
          simp only [commaTail, String.toList_append, List.length_cons, List.length_append, h2] at hf ⊢; omega
        rw [hstep_one rest f hfb.1, show (commaTail (kv2 :: kvr2) "}").toList ++ rest =
            ',' :: ' ' :: ((String.intercalate ", " (kv2 :: kvr2) ++ "}").toList ++ rest) by
          simp [commaTail, String.toList_append, List.cons_append, List.append_assoc]]
        simp only [skipHorizWs_space, hhd_list, List.cons_append, skipHorizWs_cons_of_false c_hd _ hhd_ws]
        split
        · rename_i heq; injection heq with h1 _; exact absurd h1 hhd_br
        · rw [← List.cons_append, ← hhd_list]; exact hres_parse rest f hfb.2

private theorem renderValueInline_spec (numApi : CharNumApi) (hApi : ValidCharNum numApi)
    (v : TomlValue) (tape : ValueTape) (rs : String) (hr : renderValueInline v tape = some rs) :
    RenderValSpec numApi v rs := by
  cases v with
  | array xs =>
    cases tape <;> (simp only [renderValueInline, bind_some, Option.some.injEq] at hr; try contradiction)
    rename_i elemTapes; rcases hr with ⟨strs, hre, rfl⟩
    have hVal : ∀ x ∈ xs.toList, ∀ tp rs', renderValueInline x tp = some rs' → RenderValSpec numApi x rs' :=
      fun x hx tp rs' hrx =>
        have hsz : sizeOf x < sizeOf (TomlValue.array xs) :=
          Nat.lt_trans (List.sizeOf_lt_of_mem hx) (Nat.lt_trans (sizeOf_toList_lt_array xs) (by simp +arith))
        renderValueInline_spec numApi hApi x tp rs' hrx
    obtain ⟨ys, hys_eqv, hys_cl, hys_parse⟩ :=
      renderArrayElems_parseArrayFuel numApi xs.toList elemTapes strs hre hVal [] [] (by simp [TomlListEquiv])
    have hrs_list : ("[" ++ String.intercalate ", " strs ++ "]").toList = '[' :: (String.intercalate ", " strs ++ "]").toList := by simp [String.toList_append]
    refine ⟨by rw [String.append_assoc]; exact cleanStr_append (cleanStr_lit "[") hys_cl,
      by rw [String.append_assoc]; exact headSafe_of_prefix "[" _ '[' [] rfl (by decide),
      .array ys, by simpa [TomlEquiv] using hys_eqv, fun rest _ fuel hf => ?_⟩
    cases fuel with
    | zero => rw [hrs_list] at hf; simp at hf
    | succ f => rw [hrs_list, List.cons_append]; conv => lhs; unfold parseValueFuel
                exact hys_parse rest f (by rw [hrs_list, List.length_cons] at hf; omega)
  | table t =>
    cases tape <;> (simp only [renderValueInline, ite_true_none_some, not_eq_false, bind_some, Option.some.injEq] at hr; try contradiction)
    rename_i entryTapes; rcases hr with ⟨_, kvs, hre, rfl⟩
    have hrs_list : ("{" ++ String.intercalate ", " kvs ++ "}").toList = '{' :: (String.intercalate ", " kvs ++ "}").toList := by simp [String.toList_append]
    have hhd0 : ∃ c0 cs0, ("{" ++ String.intercalate ", " kvs ++ "}").toList = c0 :: cs0 ∧
        isHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ ',' ∧ c0 ≠ ']' ∧ c0 ≠ '}' := by
      rw [String.append_assoc]; exact headSafe_of_prefix "{" _ '{' [] rfl (by decide)
    cases entryTapes with
    | nil =>
      obtain ⟨ht_empty, rfl⟩ := renderInlineTableEntries_nil_inv hre
      refine ⟨by decide, hhd0, .table #[], by simp [TomlEquiv, TomlTableEquivList, ht_empty, lookupKeyList], fun rest _ fuel hf => ?_⟩
      cases fuel with
      | zero => rw [hrs_list] at hf; simp at hf
      | succ _ => simp [String.intercalate_nil, parseValueFuel, skipHorizWs_cons_of_false '}' rest (by decide)]
    | cons e0 er0 =>
      obtain ⟨kv0, kvr0, c_hd, cs_hd, rfl, hhd_list, hhd_ws, hhd_br⟩ := renderInlineTableEntries_nonempty_head hre
      have hVal : ∀ q v0, lookupKeyList q t.toList = some v0 → ∀ tp rs',
          renderValueInline v0 tp = some rs' → RenderValSpec numApi v0 rs' :=
        fun _ v0 hqv tp rs' hrv' =>
          have hsz : sizeOf v0 < sizeOf (TomlValue.table t) :=
            Nat.lt_trans (lookupKeyList_sizeOf hqv) (Nat.lt_trans (sizeOf_toList_lt_array t) (by simp +arith))
          renderValueInline_spec numApi hApi v0 tp rs' hrv'
      obtain ⟨resT, hres_eqv, hres_cl, hres_parse⟩ :=
        renderInlineTableEntries_parseInlineTableFuel numApi t.toList t.toList (e0 :: er0) (kv0 :: kvr0) hre (by simp) hVal []
          ⟨fun _ _ h => ⟨h, rfl⟩, fun _ hn => ⟨fun _ => rfl, fun _ hs => by rw [hn] at hs; cases hs⟩⟩
      refine ⟨by rw [String.append_assoc]; exact cleanStr_append (cleanStr_lit "{") hres_cl, hhd0,
        .table resT, by simpa [TomlEquiv] using hres_eqv, fun rest _ fuel hf => ?_⟩
      cases fuel with
      | zero => rw [hrs_list] at hf; simp at hf
      | succ f =>
        rw [hrs_list, List.cons_append]
        have hpv_step : parseValueFuel numApi (f + 1) ('{' :: ((String.intercalate ", " (kv0 :: kvr0) ++ "}").toList ++ rest)) =
            match skipHorizWs ((String.intercalate ", " (kv0 :: kvr0) ++ "}").toList ++ rest) with
            | '}' :: afterClose => .ok (.table #[], afterClose)
            | other => parseInlineTableFuel numApi f other [] := rfl
        rw [hpv_step, hhd_list, List.cons_append, skipHorizWs_cons_of_false c_hd _ hhd_ws]
        split
        · rename_i heq; injection heq with h1 _; exact absurd h1 hhd_br
        · rw [← List.cons_append, ← hhd_list]; exact hres_parse rest f (by rw [hrs_list, List.length_cons] at hf; omega)
  | string _ | int _ | float _ | bool _ | offsetDateTime _ | localDateTime _ | localDate _ | localTime _ =>
    exact renderValueInline_scalar_spec numApi hApi _ tape rs hr trivial
termination_by sizeOf v
decreasing_by all_goals subst_vars; assumption

private def joinLines : List String → String | [] => "" | l :: ls => l ++ "\n" ++ joinLines ls
private abbrev CleanLines (lines : List String) : Prop := CleanStr (joinLines lines)
private theorem joinLines_append (a b : List String) : joinLines (a ++ b) = joinLines a ++ joinLines b := by
  induction a with | nil => simp [joinLines] | cons _ _ ih => simp [joinLines, ih, String.append_assoc]
private theorem joinLines_length_ge (lines : List String) : lines.length ≤ (joinLines lines).toList.length := by
  induction lines with
  | nil => simp
  | cons _ _ ih => simp only [joinLines, String.toList_append, List.length_append, List.length_cons]; have : ("\n" : String).toList.length = 1 := rfl; omega
private theorem intercalate_nl_append_nl (lines : List String) (hne : lines ≠ []) :
    String.intercalate "\n" lines ++ "\n" = joinLines lines := by
  induction lines with
  | nil => exact absurd rfl hne
  | cons l ls ih => cases ls with
    | nil => simp [String.intercalate_singleton, joinLines]
    | cons _ _ => rw [String.intercalate_cons_cons, joinLines, String.append_assoc]; exact congrArg (l ++ "\n" ++ ·) (ih (by simp))
private theorem cleanLines_nil : CleanLines [] := rfl
private theorem cleanLines_singleton {s : String} (hs : CleanStr s) : CleanLines [s] := cleanStr_append (cleanStr_append hs (cleanStr_lit "\n")) rfl
private theorem cleanLines_append {a b : List String} (ha : CleanLines a) (hb : CleanLines b) : CleanLines (a ++ b) := by
  rw [CleanLines, joinLines_append]; exact cleanStr_append ha hb

private theorem skipCommentBody_clean (cs rest : List Char) (h : (cs.all fun c => c != '\n') = true) :
    skipCommentBody (cs ++ '\n' :: rest) = '\n' :: rest := by
  induction cs with | nil => rfl | cons _ _ ih => simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; simpa [skipCommentBody, h.1] using ih h.2
private theorem skipTriviaNewlines_comment_line (c : String) (rest : List Char) (hc : isSingleLineClean c = true) :
    skipTriviaNewlines (("#" ++ c ++ "\n").toList ++ rest) = skipTriviaNewlines rest := by
  have haux : ∀ cs : List Char, (cs.all fun ch => ch != '\n') = true →
      skipTriviaNewlinesAux true (cs ++ '\n' :: rest) = skipTriviaNewlines rest := fun cs h => by
    induction cs with | nil => rfl | cons _ _ ih => simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; simpa [skipTriviaNewlinesAux, h.1] using ih h.2
  rw [show ("#" ++ c ++ "\n").toList ++ rest = '#' :: (c.toList ++ '\n' :: rest) by simp [String.toList_append, List.cons_append, List.append_assoc]]
  exact haux c.toList (by simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true] at hc ⊢; exact fun ch hch => (hc ch hch).1.2)

private theorem renderCommentSuffix_props (comment : Option String) (rc : String) (h : renderCommentSuffix comment = some rc) :
    CleanStr rc ∧ (∀ rest, consumeStatementEnd (rc.toList ++ '\n' :: rest) = .ok rest) ∧ (∀ rest, DelimTail (rc.toList ++ '\n' :: rest)) := by
  cases comment with
  | none =>
    simp only [renderCommentSuffix, Option.some.injEq] at h; subst h
    refine ⟨rfl, fun _ => by simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs], fun _ _ _ hc => ?_⟩
    injection hc with hc' _; subst hc'; exact ⟨by decide, fun h => nomatch h⟩
  | some s =>
    simp only [renderCommentSuffix] at h; split at h
    · rename_i hclean; injection h with hrc; subst hrc
      have hcl_s : CleanStr s := by
        simp only [isSingleLineClean, CleanStr, CleanChars, List.all_eq_true, Bool.and_eq_true] at hclean ⊢
        exact fun ch hch => ⟨(hclean ch hch).1.1, (hclean ch hch).2⟩
      have hno_nl : (s.toList.all fun ch => ch != '\n') = true := by
        simp only [isSingleLineClean, List.all_eq_true, Bool.and_eq_true] at hclean ⊢; exact fun ch hch => (hclean ch hch).1.2
      have hlist : ∀ rest, (" #" ++ s).toList ++ '\n' :: rest = ' ' :: '#' :: (s.toList ++ '\n' :: rest) :=
        fun _ => by simp [String.toList_append, List.cons_append]
      refine ⟨cleanStr_append (cleanStr_lit " #") hcl_s, fun rest => ?_, fun rest _ _ hc => ?_⟩
      · rw [hlist]; simp [consumeStatementEnd, skipHorizAndComment, skipHorizWs, isHorizWs, skipCommentBody_clean s.toList rest hno_nl]
      · rw [hlist] at hc; injection hc with hc1 hr1; subst hc1
        refine ⟨by decide, fun _ _ _ hr2 => ?_⟩; rw [← hr1] at hr2; injection hr2 with hc2 _; subst hc2; decide
    · cases h

private theorem dropLast_append_singleton {α : Type} (l : List α) (x : α) : (l ++ [x]).dropLast = l := by
  induction l with | nil => rfl | cons _ l ih => cases l <;> simp [List.dropLast]
private theorem getLast?_append_singleton {α : Type} (l : List α) (x : α) : (l ++ [x]).getLast? = some x := by
  induction l with | nil => rfl | cons _ l ih => cases l with | nil => rfl | cons _ _ => simpa [List.getLast?] using ih
private theorem dropLast_append_getLast {α : Type} (l : List α) (x : α) (hne : l ≠ []) (hl : l.getLast? = some x) : l.dropLast ++ [x] = l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons _ bs ih => cases bs with
    | nil => simp only [List.getLast?, Option.some.injEq] at hl; subst hl; rfl
    | cons _ _ => simp [List.dropLast, ih (by simp) (by simpa [List.getLast?] using hl)]
private theorem mapLastAot_eq (f : List (String × Node) → Except TomlError (List (String × Node)))
    (elems : List (List (String × Node))) (lastElem newLast : List (String × Node))
    (hne : elems ≠ []) (hlast : elems.getLast? = some lastElem) (hf : f lastElem = .ok newLast) :
    mapLastAot f elems = .ok (elems.dropLast ++ [newLast]) := by
  induction elems with
  | nil => exact absurd rfl hne
  | cons a bs ih => cases bs with
    | nil => have ha : a = lastElem := by simpa [List.getLast?] using hlast
             subst ha; simp [mapLastAot, hf, bind, Except.bind]
    | cons _ _ => simp [mapLastAot, ih (by simp) (by simpa [List.getLast?] using hlast), List.dropLast, bind, Except.bind]

private inductive AtLocalPath :
    List (String × Node) → List String → List (String × Node) → (List (String × Node) → List (String × Node)) → Prop where
  | nil (entries) : AtLocalPath entries [] entries id
  | consTable {entries k kind sub ps loc rb} :
      kind ≠ .inline → assocLookupNode k entries = some (.table kind sub) → AtLocalPath sub ps loc rb →
      AtLocalPath entries (k :: ps) loc (fun nl => assocSetNode k (.table kind (rb nl)) entries)
  | consAot {entries k elems lastElem ps loc rb} :
      elems ≠ [] → elems.getLast? = some lastElem → assocLookupNode k entries = some (.aot elems) → AtLocalPath lastElem ps loc rb →
      AtLocalPath entries (k :: ps) loc (fun nl => assocSetNode k (.aot (elems.dropLast ++ [rb nl])) entries)

private theorem assocSetNode_self_of_lookup {entries : List (String × Node)} {k : String} {nd : Node}
    (hlk : assocLookupNode k entries = some nd) : assocSetNode k nd entries = entries := by
  induction entries with
  | nil => cases hlk
  | cons p _ ih =>
    rcases p with ⟨k', _⟩; simp only [assocLookupNode] at hlk
    by_cases heq : k == k'
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hlk; subst hlk; simp [assocSetNode, heq]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hlk; simp [assocSetNode, heq, ih hlk]

private theorem atLocalPath_self {root path loc rb} (h : AtLocalPath root path loc rb) : rb loc = root := by
  induction h with
  | nil _ => rfl
  | consTable _ hlk _ ih => dsimp only; rw [ih]; exact assocSetNode_self_of_lookup hlk
  | consAot hne hlast hlk _ ih => dsimp only; rw [ih, dropLast_append_getLast _ _ hne hlast]; exact assocSetNode_self_of_lookup hlk

private theorem atLocalPath_rebuild {root path loc rb} (h : AtLocalPath root path loc rb)
    (newLoc : List (String × Node)) : AtLocalPath (rb newLoc) path newLoc rb := by
  induction h with
  | nil _ => exact .nil newLoc
  | @consTable entries k kind _ _ _ rbSub hkind _ _ ih =>
    have hrb_eq : (fun nl => assocSetNode k (.table kind (rbSub nl)) (assocSetNode k (.table kind (rbSub newLoc)) entries)) =
        (fun nl => assocSetNode k (.table kind (rbSub nl)) entries) := funext fun _ => assocSetNode_idem k _ _ entries
    have h0 := AtLocalPath.consTable hkind
      (show assocLookupNode k (assocSetNode k (.table kind (rbSub newLoc)) entries) = some (.table kind (rbSub newLoc)) by simp [assocLookupNode_assocSetNode]) ih
    rwa [hrb_eq] at h0
  | @consAot entries k elems _ _ _ rbSub _ _ _ _ ih =>
    have hrb_eq : (fun nl => assocSetNode k (.aot ((elems.dropLast ++ [rbSub newLoc]).dropLast ++ [rbSub nl]))
        (assocSetNode k (.aot (elems.dropLast ++ [rbSub newLoc])) entries)) =
        (fun nl => assocSetNode k (.aot (elems.dropLast ++ [rbSub nl])) entries) := by
      funext nl; rw [dropLast_append_singleton]; exact assocSetNode_idem k _ _ entries
    have h0 := AtLocalPath.consAot (by simp) (getLast?_append_singleton elems.dropLast (rbSub newLoc))
      (show assocLookupNode k (assocSetNode k (.aot (elems.dropLast ++ [rbSub newLoc])) entries) = some (.aot (elems.dropLast ++ [rbSub newLoc])) by simp [assocLookupNode_assocSetNode]) ih
    rwa [hrb_eq] at h0

private theorem atLocalPath_stepTable {root path loc rb} (h : AtLocalPath root path loc rb)
    (k : String) (kind : TableKind) (sub : List (String × Node)) (hkind : kind ≠ .inline)
    (hlk : assocLookupNode k loc = some (.table kind sub)) :
    AtLocalPath root (path ++ [k]) sub (fun newSub => rb (assocSetNode k (.table kind newSub) loc)) := by
  induction h with | nil _ => exact .consTable hkind hlk (.nil sub) | consTable hk0 hl0 _ ih => exact .consTable hk0 hl0 (ih hlk) | consAot hn0 hls0 hl0 _ ih => exact .consAot hn0 hls0 hl0 (ih hlk)
private theorem atLocalPath_stepAot {root path loc rb} (h : AtLocalPath root path loc rb) (k : String)
    (elems : List (List (String × Node))) (lastElem : List (String × Node))
    (hne : elems ≠ []) (hlast : elems.getLast? = some lastElem) (hlk : assocLookupNode k loc = some (.aot elems)) :
    AtLocalPath root (path ++ [k]) lastElem (fun newLast => rb (assocSetNode k (.aot (elems.dropLast ++ [newLast])) loc)) := by
  induction h with | nil _ => exact .consAot hne hlast hlk (.nil lastElem) | consTable hk0 hl0 _ ih => exact .consTable hk0 hl0 (ih hlk) | consAot hn0 hls0 hl0 _ ih => exact .consAot hn0 hls0 hl0 (ih hlk)

private theorem atLocalPath_insertAtActivePath {root path loc rb} (h : AtLocalPath root path loc rb)
    (fullPath relPath : List String) (newNode : Node) (newLoc : List (String × Node))
    (hins : insertDottedEntries fullPath loc relPath newNode = .ok newLoc) :
    insertAtActivePath fullPath root path relPath newNode = .ok (rb newLoc) := by
  induction h with
  | nil _ => simpa [insertAtActivePath] using hins
  | consTable _ hlk _ ih => simp [insertAtActivePath, hlk, ih hins, bind, Except.bind]
  | @consAot _ _ elems lastElem ps _ rbSub hne hlast hlk _ ih =>
    simp [insertAtActivePath, hlk, mapLastAot_eq (fun elem => insertAtActivePath fullPath elem ps relPath newNode)
      elems lastElem (rbSub newLoc) hne hlast (ih hins), bind, Except.bind]

private theorem atLocalPath_applyHeader (mode : HeaderMode) {root path loc rb} (h : AtLocalPath root path loc rb)
    (fullPath suffix : List String) (hsuf : suffix ≠ []) (newLoc : List (String × Node))
    (happ : applyHeader mode fullPath loc suffix = .ok newLoc) :
    applyHeader mode fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h with
  | nil _ => simpa using happ
  | @consTable _ _ kind _ ps _ _ hkind hlk _ ih =>
    cases hps : ps ++ suffix with
    | nil => exact absurd hps (by cases ps <;> simp [hsuf])
    | cons _ _ =>
      rw [List.cons_append, hps]; simp only [applyHeader, hlk]; rw [← hps]
      cases kind <;> first | exact absurd rfl hkind | simp [ih happ, bind, Except.bind]
  | @consAot _ _ elems lastElem ps _ rbSub hne hlast hlk _ ih =>
    cases hps : ps ++ suffix with
    | nil => exact absurd hps (by cases ps <;> simp [hsuf])
    | cons _ _ =>
      rw [List.cons_append, hps]; simp only [applyHeader, hlk]; rw [← hps]
      simp [mapLastAot_eq (fun elem => applyHeader mode fullPath elem (ps ++ suffix))
        elems lastElem (rbSub newLoc) hne hlast (ih happ), bind, Except.bind]

private inductive AtHeaderFocus :
    List (String × Node) → List String → List (String × Node) → (List (String × Node) → List (String × Node)) → Prop where
  | exact {root path loc rb} : AtLocalPath root path loc rb → AtHeaderFocus root path loc rb
  | implicitNone {root parentLoc parentPath rbParent k} :
      AtHeaderFocus root parentPath parentLoc rbParent → assocLookupNode k parentLoc = none →
      AtHeaderFocus root (parentPath ++ [k]) [] (fun newSub => rbParent (assocSetNode k (.table .subtableImplicit newSub) parentLoc))

private theorem atHeaderFocus_applyHeader (mode : HeaderMode) {root path loc rb} (h : AtHeaderFocus root path loc rb)
    (fullPath suffix : List String) (hsuf : suffix ≠ []) (newLoc : List (String × Node))
    (happ : applyHeader mode fullPath loc suffix = .ok newLoc) :
    applyHeader mode fullPath root (path ++ suffix) = .ok (rb newLoc) := by
  induction h generalizing suffix newLoc with
  | exact hp => exact atLocalPath_applyHeader mode hp fullPath suffix hsuf newLoc happ
  | @implicitNone parentLoc _ _ k _ hnone ih =>
    rw [List.append_assoc]; apply ih (k :: suffix) (by simp) (assocSetNode k (.table .subtableImplicit newLoc) parentLoc)
    cases suffix with | nil => exact absurd rfl hsuf | cons _ _ => simp [applyHeader, hnone, happ, bind, Except.bind]

private theorem atHeaderFocus_step {root path loc rb} (h : AtHeaderFocus root path loc rb)
    (newLoc : List (String × Node)) : AtLocalPath (rb newLoc) path newLoc rb := by
  induction h generalizing newLoc with
  | exact hp => exact atLocalPath_rebuild hp newLoc
  | @implicitNone parentLoc _ rbParent k _ _ ih =>
    let newParent := assocSetNode k (.table .subtableImplicit newLoc) parentLoc
    have hstep := atLocalPath_stepTable (ih newParent) k .subtableImplicit newLoc (by decide) (by simp [newParent, assocLookupNode_assocSetNode])
    have hrb_eq : (fun nl => rbParent (assocSetNode k (.table .subtableImplicit nl) newParent)) =
        (fun nl => rbParent (assocSetNode k (.table .subtableImplicit nl) parentLoc)) := funext fun _ => by simp [newParent, assocSetNode_idem]
    rwa [hrb_eq] at hstep

private inductive DottedWriteFocus :
    List (String × Node) → List String → List (String × Node) → (List (String × Node) → List (String × Node)) → Prop where
  | nil (entries) : DottedWriteFocus entries [] entries id
  | consNone {entries k ps sub rb} :
      assocLookupNode k entries = none → DottedWriteFocus [] ps sub rb →
      DottedWriteFocus entries (k :: ps) sub (fun newSub => assocSetNode k (.table .dotted (rb newSub)) entries)
  | consDotted {entries k cur ps sub rb} :
      assocLookupNode k entries = some (.table .dotted cur) → DottedWriteFocus cur ps sub rb →
      DottedWriteFocus entries (k :: ps) sub (fun newSub => assocSetNode k (.table .dotted (rb newSub)) entries)

private theorem dottedWriteFocus_insert {entries pref sub rb} (h : DottedWriteFocus entries pref sub rb)
    (fullPath rel : List String) (hrel : rel ≠ []) (newNode : Node) (newSub : List (String × Node))
    (hins : insertDottedEntries fullPath sub rel newNode = .ok newSub) :
    insertDottedEntries fullPath entries (pref ++ rel) newNode = .ok (rb newSub) := by
  induction h with
  | nil _ => simpa using hins
  | @consNone _ _ ps _ _ hlk _ ih | @consDotted _ _ _ ps _ _ hlk _ ih =>
    cases hps : ps ++ rel with
    | nil => exact absurd hps (by cases ps <;> simp [hrel])
    | cons _ _ => rw [List.cons_append, hps]; simp only [insertDottedEntries, hlk]; rw [← hps]; simp [ih hins, bind, Except.bind]

private theorem dottedWriteFocus_rebuild {entries pref sub rb} (h : DottedWriteFocus entries pref sub rb)
    (newSub : List (String × Node)) : DottedWriteFocus (rb newSub) pref newSub rb := by
  induction h with
  | nil _ => exact .nil newSub
  | @consNone entries k _ _ rbSub _ _ ih | @consDotted entries k _ _ _ rbSub _ _ ih =>
    have hrb_eq : (fun nl => assocSetNode k (.table .dotted (rbSub nl)) (assocSetNode k (.table .dotted (rbSub newSub)) entries)) =
        (fun nl => assocSetNode k (.table .dotted (rbSub nl)) entries) := funext fun _ => assocSetNode_idem k _ _ entries
    have h0 := DottedWriteFocus.consDotted
      (show assocLookupNode k (assocSetNode k (.table .dotted (rbSub newSub)) entries) = some (.table .dotted (rbSub newSub)) by simp [assocLookupNode_assocSetNode]) ih
    rwa [hrb_eq] at h0

private theorem dottedWriteFocus_step {entries pref sub rb} (h : DottedWriteFocus entries pref sub rb)
    (k : String) (hnone : assocLookupNode k sub = none) :
    DottedWriteFocus entries (pref ++ [k]) [] (fun newSub => rb (assocSetNode k (.table .dotted newSub) sub)) := by
  induction h with | nil _ => exact .consNone hnone (.nil []) | consNone hn0 _ ih => exact .consNone hn0 (ih hnone) | consDotted hlk0 _ ih => exact .consDotted hlk0 (ih hnone)

private def DocSteps (numApi : CharNumApi) (lines : List String)
    (startAct : List String) (startRoot : List (String × Node)) (endAct : List String) (endRoot : List (String × Node)) : Prop :=
  CleanLines lines ∧ ∀ (restChars : List Char) (fuel : Nat), lines.length ≤ fuel →
    parseDocumentFuel numApi fuel ((joinLines lines).toList ++ restChars) startAct startRoot =
    parseDocumentFuel numApi (fuel - lines.length) restChars endAct endRoot

private theorem docSteps_nil {numApi act root} : DocSteps numApi [] act root act root := ⟨cleanLines_nil, fun _ _ _ => by simp [joinLines]⟩
private theorem docSteps_append {numApi l1 l2 a1 a2 a3 r1 r2 r3}
    (h1 : DocSteps numApi l1 a1 r1 a2 r2) (h2 : DocSteps numApi l2 a2 r2 a3 r3) : DocSteps numApi (l1 ++ l2) a1 r1 a3 r3 := by
  refine ⟨cleanLines_append h1.1 h2.1, fun rest fuel hf => ?_⟩
  simp only [List.length_append] at hf ⊢
  rw [joinLines_append, String.toList_append, List.append_assoc, h1.2 _ fuel (by omega), h2.2 rest (fuel - l1.length) (by omega), Nat.sub_sub]
private theorem docSteps_singleton {numApi line startAct endAct startRoot endRoot} (hcl : CleanStr line)
    (hstep : ∀ restChars f, parseDocumentFuel numApi (f + 1) (line.toList ++ '\n' :: restChars) startAct startRoot = parseDocumentFuel numApi f restChars endAct endRoot) :
    DocSteps numApi [line] startAct startRoot endAct endRoot := by
  refine ⟨cleanLines_singleton hcl, fun restChars fuel hf => ?_⟩
  cases fuel with | zero => simp at hf | succ f => simpa [joinLines, String.toList_append, List.cons_append, List.append_assoc] using hstep restChars f

private theorem docSteps_assign (numApi : CharNumApi) (hApi : ValidCharNum numApi)
    (pairs : List (String × String)) (hne : pairs ≠ []) (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (v : TomlValue) (vt : ValueTape) (rv : String) (hrv : renderValueInline v vt = some rv)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root : List (String × Node)) :
    ∃ v', TomlEquiv v v' ∧ ∀ nextRoot,
      insertAtActivePath (activePath ++ pairs.map Prod.fst) root activePath (pairs.map Prod.fst) (valueToInlineNode v') = .ok nextRoot →
      DocSteps numApi [joinRenderedPath (pairs.map Prod.snd) ++ " = " ++ rv ++ rc] activePath root activePath nextRoot := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, _, hlhs_list, hws0, hn0, hc0, hl0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, hrc_delim⟩ := renderCommentSuffix_props comment rc hrc
  obtain ⟨hrv_cl, ⟨cv0, _, hrv_list, hvws0, _⟩, v', heqv, hpv⟩ := renderValueInline_spec numApi hApi v vt rv hrv
  refine ⟨v', heqv, fun nextRoot hins => docSteps_singleton
    (cleanStr_append (cleanStr_append (cleanStr_append hlhs_cl (cleanStr_lit " = ")) hrv_cl) hrc_cl) fun restChars f => ?_⟩
  let valRest := rc.toList ++ '\n' :: restChars
  have hdk : parseDottedKey (lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest))) =
      .ok (pairs.map Prod.fst, '=' :: ' ' :: (rv.toList ++ valRest)) := by
    simpa [lhs, skipHorizWs, isHorizWs] using parseDottedKey_joinRenderedPath pairs hne hkeys
      (' ' :: '=' :: ' ' :: (rv.toList ++ valRest)) (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
      ⟨'=', ' ' :: (rv.toList ++ valRest), by simp [skipHorizWs, isHorizWs], by decide⟩
  conv => lhs; unfold parseDocumentFuel
  rw [show skipTriviaNewlines ((lhs ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars) = lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest)) by
    rw [show (lhs ++ " = " ++ rv ++ rc).toList ++ '\n' :: restChars = lhs.toList ++ (' ' :: '=' :: ' ' :: (rv.toList ++ valRest)) by
      simp [valRest, String.toList_append, List.cons_append, List.append_assoc], hlhs_list, List.cons_append]
    exact skipTriviaNewlines_cons_of_safe c0 _ hws0 hn0 hc0]
  split
  · rename_i heq; rw [hlhs_list] at heq; cases heq
  · rename_i heq; rw [hlhs_list, List.cons_append] at heq; injection heq with h1 _; exact absurd h1 hl0
  · rename_i heq; rw [hlhs_list, List.cons_append] at heq; injection heq with h1 _; exact absurd h1 hl0
  · rw [hdk]; simp only [bind, Except.bind, skipHorizWs_cons_of_false '=' _ (by decide)]
    rw [show skipHorizWs (' ' :: (rv.toList ++ valRest)) = rv.toList ++ valRest by
          rw [skipHorizWs_space, hrv_list, List.cons_append]; exact skipHorizWs_cons_of_false cv0 _ hvws0,
        show parseValue numApi (rv.toList ++ valRest) = .ok (v', valRest) from
          hpv valRest (hrc_delim restChars) ((rv.toList ++ valRest).length + 2) (by rw [List.length_append]; omega)]
    dsimp only [valRest]; rw [hrc_end restChars]; dsimp only; rw [hins]

private def hdrLine (mode : HeaderMode) (lhs rc : String) : String :=
  match mode with | .table => "[" ++ lhs ++ "]" ++ rc | .aot => "[[" ++ lhs ++ "]]" ++ rc

private theorem docSteps_hdr (numApi : CharNumApi) (mode : HeaderMode)
    (pairs : List (String × String)) (hne : pairs ≠ []) (hkeys : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2)
    (comment : Option String) (rc : String) (hrc : renderCommentSuffix comment = some rc)
    (activePath : List String) (root nextRoot : List (String × Node))
    (happ : applyHeader mode (pairs.map Prod.fst) root (pairs.map Prod.fst) = .ok nextRoot) :
    DocSteps numApi [hdrLine mode (joinRenderedPath (pairs.map Prod.snd)) rc] activePath root (pairs.map Prod.fst) nextRoot := by
  let lhs := joinRenderedPath (pairs.map Prod.snd)
  obtain ⟨⟨c0, _, hlhs_list, hws0, _, _, hl0, _⟩, hlhs_cl, _⟩ := joinRenderedPath_props pairs hne hkeys
  obtain ⟨hrc_cl, hrc_end, _⟩ := renderCommentSuffix_props comment rc hrc
  refine docSteps_singleton (by cases mode <;> exact cleanStr_append (cleanStr_append (cleanStr_append (by decide) hlhs_cl) (by decide)) hrc_cl) fun restChars f => ?_
  have hparse_lhs : ∀ extra,
      skipHorizWs (lhs.toList ++ (']' :: extra)) = lhs.toList ++ (']' :: extra) ∧
      parseDottedKey (lhs.toList ++ (']' :: extra)) = .ok (pairs.map Prod.fst, ']' :: extra) := fun extra =>
    ⟨by rw [hlhs_list, List.cons_append]; exact skipHorizWs_cons_of_false c0 _ hws0,
     by simpa [lhs, skipHorizWs_cons_of_false ']' _ (by decide)] using parseDottedKey_joinRenderedPath pairs hne hkeys
          (']' :: extra) (fun c _ hc => by injection hc with hc1 _; subst hc1; decide)
          ⟨']', extra, skipHorizWs_cons_of_false ']' _ (by decide), by decide⟩⟩
  conv => lhs; unfold parseDocumentFuel
  cases mode
  · obtain ⟨hsw, hdk⟩ := hparse_lhs (rc.toList ++ '\n' :: restChars); dsimp only [hdrLine, lhs]
    rw [show ("[" ++ lhs ++ "]" ++ rc).toList ++ '\n' :: restChars = '[' :: (lhs.toList ++ (']' :: (rc.toList ++ '\n' :: restChars))) by
      simp [String.toList_append, List.cons_append, List.append_assoc], skipTriviaNewlines_cons_of_safe '[' _ (by decide) (by decide) (by decide)]
    split
    · rename_i h; cases h
    · rename_i h; injection h with _ h2; rw [hlhs_list, List.cons_append] at h2; injection h2 with h2' _; exact absurd h2' hl0
    · rename_i _ _ h; injection h with _ hr; rw [← hr, hsw, hdk]
      simp only [bind, Except.bind, skipHorizWs_cons_of_false ']' _ (by decide), hrc_end restChars, happ]
    · rename_i hnot; exact absurd rfl (hnot _)
  · obtain ⟨hsw, hdk⟩ := hparse_lhs (']' :: (rc.toList ++ '\n' :: restChars)); dsimp only [hdrLine, lhs]
    rw [show ("[[" ++ lhs ++ "]]" ++ rc).toList ++ '\n' :: restChars = '[' :: '[' :: (lhs.toList ++ (']' :: ']' :: (rc.toList ++ '\n' :: restChars))) by
      simp [String.toList_append, List.cons_append, List.append_assoc], skipTriviaNewlines_cons_of_safe '[' _ (by decide) (by decide) (by decide)]
    split
    · rename_i h; cases h
    · rename_i _ _ h; injection h with _ h1; injection h1 with _ hr; rw [← hr, hsw, hdk]
      simp only [bind, Except.bind, skipHorizWs_cons_of_false ']' _ (by decide), hrc_end restChars, happ]
    · rename_i hnot h; injection h with _ ht; exact absurd ht.symm (hnot _)
    · rename_i hnot _; exact absurd rfl (hnot _)

private structure DocFocus where
  pairs : List (String × String)
  root : List (String × Node)
  loc : List (String × Node)
  rb : List (String × Node) → List (String × Node)
private abbrev DocFocus.path (f : DocFocus) : List String := f.pairs.map Prod.fst
private abbrev DocFocus.revRen (f : DocFocus) : List String := (f.pairs.map Prod.snd).reverse
private def DocFocus.KeysValid (f : DocFocus) : Prop := ∀ p ∈ f.pairs, ∃ ks, renderKey p.1 ks = some p.2
private def DocFocus.Exact (f : DocFocus) : Prop := f.KeysValid ∧ AtLocalPath f.root f.path f.loc f.rb
private def DocFocus.Header (f : DocFocus) : Prop := f.KeysValid ∧ AtHeaderFocus f.root f.path f.loc f.rb
private abbrev DocFocus.withLoc (f : DocFocus) (newLoc : List (String × Node)) : DocFocus := { f with root := f.rb newLoc, loc := newLoc }
private def DocFocus.pushImplicit (f : DocFocus) (k rk : String) : DocFocus :=
  ⟨f.pairs ++ [(k, rk)], f.root, [], fun nl => f.rb (assocSetNode k (.table .subtableImplicit nl) f.loc)⟩
private def DocFocus.pushExplicit (f : DocFocus) (k rk : String) (sub : List (String × Node)) : DocFocus :=
  ⟨f.pairs ++ [(k, rk)], f.rb (assocSetNode k (.table .explicit sub) f.loc), sub, fun nl => f.rb (assocSetNode k (.table .explicit nl) f.loc)⟩
private def DocFocus.pushAotElem (f : DocFocus) (k rk : String) (prev : List (List (String × Node))) : DocFocus :=
  ⟨f.pairs ++ [(k, rk)], f.rb (assocSetNode k (.aot (prev ++ [[]])) f.loc), [], fun nl => f.rb (assocSetNode k (.aot (prev ++ [nl])) f.loc)⟩

private theorem DocFocus.exact_to_header {f : DocFocus} (h : f.Exact) : f.Header := ⟨h.1, .exact h.2⟩
private theorem DocFocus.exact_withLoc (f : DocFocus) (h : f.Exact) (nl : List (String × Node)) : (f.withLoc nl).Exact := ⟨h.1, atLocalPath_rebuild h.2 nl⟩
private theorem DocFocus.header_withLoc (f : DocFocus) (h : f.Header) (nl : List (String × Node)) : (f.withLoc nl).Exact := ⟨h.1, atHeaderFocus_step h.2 nl⟩
private theorem keysValid_push {pairs : List (String × String)} {k rk : String}
    (hp : ∀ p ∈ pairs, ∃ ks, renderKey p.1 ks = some p.2) (hk : ∃ ks, renderKey k ks = some rk) :
    ∀ p ∈ pairs ++ [(k, rk)], ∃ ks, renderKey p.1 ks = some p.2 :=
  fun p hm => (List.mem_append.mp hm).elim (hp p) (fun h => List.mem_singleton.mp h ▸ hk)
private theorem docFocus_pushImplicit {f : DocFocus} {k rk : String}
    (hf : f.Header) (hk : ∃ ks, renderKey k ks = some rk) (hnone : assocLookupNode k f.loc = none) :
    (f.pushImplicit k rk).Header :=
  ⟨keysValid_push hf.1 hk, by simpa [DocFocus.pushImplicit, DocFocus.path, List.map_append] using .implicitNone hf.2 hnone⟩

private theorem docFocus_emitExplicit (numApi : CharNumApi) {f : DocFocus} {k rk rc : String}
    {comment : Option String} (sub startRoot : List (String × Node)) (act : List String)
    (hf : f.Header) (hk : ∃ ks, renderKey k ks = some rk) (hrc : renderCommentSuffix comment = some rc)
    (happ : applyHeader .table (f.path ++ [k]) startRoot (f.path ++ [k]) = .ok (f.pushExplicit k rk sub).root) :
    (f.pushExplicit k rk sub).Exact ∧
    DocSteps numApi ["[" ++ joinRenderedPath (rk :: f.revRen).reverse ++ "]" ++ rc] act startRoot
      (f.pushExplicit k rk sub).path (f.pushExplicit k rk sub).root := by
  let expParent := assocSetNode k (.table .explicit sub) f.loc
  have hstep := atLocalPath_stepTable (atHeaderFocus_step hf.2 expParent) k .explicit sub (by decide) (by simp [expParent, assocLookupNode_assocSetNode])
  have hrb_eq : (fun nl => f.rb (assocSetNode k (.table .explicit nl) expParent)) =
      (fun nl => f.rb (assocSetNode k (.table .explicit nl) f.loc)) := funext fun _ => by simp [expParent, assocSetNode_idem]
  refine ⟨⟨keysValid_push hf.1 hk, by simpa [DocFocus.pushExplicit, DocFocus.path, List.map_append, hrb_eq] using hstep⟩, ?_⟩
  simpa [hdrLine, DocFocus.revRen, DocFocus.pushExplicit, DocFocus.path] using
    docSteps_hdr numApi .table (f.pairs ++ [(k, rk)]) (by simp) (keysValid_push hf.1 hk) comment rc hrc act startRoot _
      (by simpa [DocFocus.pushExplicit, DocFocus.path, List.map_append] using happ)

private theorem docFocus_openAotElem (numApi : CharNumApi) {f : DocFocus} {k rk rc : String}
    {comment : Option String} (prev : List (List (String × Node))) (act : List String)
    (hf : f.Header) (hk : ∃ ks, renderKey k ks = some rk) (hrc : renderCommentSuffix comment = some rc)
    (hprev : (prev = [] ∧ assocLookupNode k f.loc = none) ∨ (prev ≠ [] ∧ assocLookupNode k f.loc = some (.aot prev))) :
    (f.pushAotElem k rk prev).Exact ∧
    DocSteps numApi ["[[" ++ joinRenderedPath (rk :: f.revRen).reverse ++ "]]" ++ rc] act f.root
      (f.pushAotElem k rk prev).path (f.pushAotElem k rk prev).root := by
  let midElems := prev ++ [[]]; let midParent := assocSetNode k (.aot midElems) f.loc
  have happ_loc : applyHeader .aot (f.path ++ [k]) f.loc [k] = .ok midParent := by
    rcases hprev with ⟨rfl, hnone⟩ | ⟨_, hsome⟩ <;> simp [applyHeader, applyHeaderLeaf, *, midParent, midElems]
  have happ_root : applyHeader .aot ((f.pairs ++ [(k, rk)]).map Prod.fst) f.root
      ((f.pairs ++ [(k, rk)]).map Prod.fst) = .ok (f.rb midParent) := by
    simpa [DocFocus.path, List.map_append] using atHeaderFocus_applyHeader .aot hf.2 (f.path ++ [k]) [k] (by simp) midParent happ_loc
  have hstep := atLocalPath_stepAot (atHeaderFocus_step hf.2 midParent) k midElems []
    (by simp [midElems]) (getLast?_append_singleton prev []) (by simp [midParent, assocLookupNode_assocSetNode])
  have hrb_eq : (fun nl => f.rb (assocSetNode k (.aot (midElems.dropLast ++ [nl])) midParent)) =
      (fun nl => f.rb (assocSetNode k (.aot (prev ++ [nl])) f.loc)) := by
    funext nl; rw [show midElems.dropLast = prev from dropLast_append_singleton prev []]; simp [midParent, assocSetNode_idem]
  refine ⟨⟨keysValid_push hf.1 hk, by simpa [DocFocus.pushAotElem, DocFocus.path, List.map_append, hrb_eq] using hstep⟩, ?_⟩
  simpa [hdrLine, DocFocus.revRen, DocFocus.pushAotElem, DocFocus.path] using
    docSteps_hdr numApi .aot (f.pairs ++ [(k, rk)]) (by simp) (keysValid_push hf.1 hk) comment rc hrc act f.root _ happ_root

private theorem noDupStringsBool_iff_nodup (l : List String) : noDupStringsBool l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [noDupStringsBool]
  | cons x xs ih =>
    simp only [noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, ih]
    exact ⟨fun ⟨hx, hxs⟩ => ⟨fun hm => (by rw [List.contains_iff_mem.mpr hm] at hx; nomatch hx), hxs⟩,
           fun ⟨hx, hxs⟩ => ⟨Bool.eq_false_iff.mpr (hx ∘ List.contains_iff_mem.mp), hxs⟩⟩

private theorem nodup_subset_len_mem {l1 l2 : List String}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hlen : l1.length = l2.length) (hsub : ∀ x ∈ l1, x ∈ l2) : ∀ y ∈ l2, y ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp at hlen ⊢
  | cons a as ih =>
    rw [List.nodup_cons] at h1; have ha2 := hsub a (by simp)
    have hlen_er : as.length = (l2.erase a).length := by
      have := List.length_erase_of_mem ha2; have := List.length_pos_of_mem ha2; simp only [List.length_cons] at hlen; omega
    have hsub_er : ∀ x ∈ as, x ∈ l2.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun heq => h1.1 (by simpa [heq] using hx))).mpr (hsub x (by simp [hx]))
    intro y hy; by_cases hya : y = a; · simp [hya]
    · exact List.mem_cons_of_mem a (ih h1.2 (h2.erase a) hlen_er hsub_er y ((List.mem_erase_of_ne hya).mpr hy))

private theorem hasKeyList_eq_isSome (k : String) (es : List (String × TomlValue)) :
    hasKeyList k es = (lookupKeyList k es).isSome := by
  induction es with | nil => rfl | cons e _ ih => rcases e with ⟨ek, _⟩; by_cases h : k == ek <;> simp [hasKeyList, lookupKeyList, h, ih]

private theorem isPlanPermutation_props {entries : List (String × TomlValue)}
    {plan : List (String × EntryPlacement)} (h : isPlanPermutation entries plan = true) :
    noDupKeysBool entries = true ∧ noDupStringsBool (plan.map Prod.fst) = true ∧
    (∀ p ∈ plan, ∃ v, lookupKeyList p.1 entries = some v) ∧
    (∀ q v, lookupKeyList q entries = some v → ∃ ep, (q, ep) ∈ plan) := by
  simp only [isPlanPermutation, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  rcases h with ⟨⟨⟨hnd_e, hnd_p⟩, hlen⟩, hall⟩
  refine ⟨hnd_e, hnd_p, fun p hp => Option.isSome_iff_exists.mp (by rw [← hasKeyList_eq_isSome]; exact hall p hp), fun q v hqv => ?_⟩
  have hsub : ∀ x ∈ plan.map Prod.fst, x ∈ entries.map Prod.fst := fun x hx => by
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩; exact (hasKeyList_eq_true_iff p.1 entries).mp (hall p hp)
  have hq_e : q ∈ entries.map Prod.fst := (hasKeyList_eq_true_iff q entries).mp (by rw [hasKeyList_eq_isSome, hqv]; rfl)
  have hq_p := nodup_subset_len_mem ((noDupStringsBool_iff_nodup _).mp hnd_p)
    ((noDupKeys_iff_nodup entries).mp hnd_e) (by simpa using hlen) hsub q hq_e
  rcases List.mem_map.mp hq_p with ⟨⟨k, ep⟩, hm, hkq⟩; dsimp only at hkq; subst hkq; exact ⟨ep, hm⟩

private theorem entriesToTomlList_of_plan_match (entries : List (String × TomlValue))
    (plan : List (String × EntryPlacement)) (hperm : isPlanPermutation entries plan = true) (nodes : List (String × Node))
    (hmatch : ∀ p ∈ plan, ∃ v nd, lookupKeyList p.1 entries = some v ∧ assocLookupNode p.1 nodes = some nd ∧ TomlEquiv v (nodeToTomlValue nd))
    (honly : ∀ q, q ∉ plan.map Prod.fst → assocLookupNode q nodes = none) :
    TomlTableEquivList entries (entriesToTomlList nodes) := by
  obtain ⟨_, _, _, hcov⟩ := isPlanPermutation_props hperm; unfold TomlTableEquivList
  refine ⟨fun q hnone => ?_, fun q v1 hqv1 => ?_⟩
  · rw [lookupKeyList_entriesToTomlList]
    by_cases hmem : q ∈ plan.map Prod.fst
    · rcases List.mem_map.mp hmem with ⟨p, hp, rfl⟩; obtain ⟨v, _, hv, _⟩ := hmatch p hp; rw [hv] at hnone; cases hnone
    · rw [honly q hmem]; rfl
  · obtain ⟨ep, hep⟩ := hcov q v1 hqv1; obtain ⟨v, nd, hv, hnd, heqv⟩ := hmatch (q, ep) hep
    injection (hqv1.symm.trans hv) with hv_eq; subst hv_eq
    rw [lookupKeyList_entriesToTomlList, hnd]; exact ⟨nodeToTomlValue nd, rfl, heqv⟩

private theorem tableEquiv_of_split_plan (entries : List (String × TomlValue))
    (plan : List (String × EntryPlacement)) (hperm : isPlanPermutation entries plan = true) (nodes : List (String × Node))
    (hinl : ∀ p ∈ plan, p.2.isInlineScope = true → ∃ v nd, lookupKeyList p.1 entries = some v ∧ assocLookupNode p.1 nodes = some nd ∧ TomlEquiv v (nodeToTomlValue nd))
    (hsec : ∀ p ∈ plan, p.2.isInlineScope = false → ∃ v nd, lookupKeyList p.1 entries = some v ∧ assocLookupNode p.1 nodes = some nd ∧ TomlEquiv v (nodeToTomlValue nd))
    (honly : ∀ q, q ∉ plan.map Prod.fst → assocLookupNode q nodes = none) :
    TomlTableEquivList entries (entriesToTomlList nodes) :=
  entriesToTomlList_of_plan_match entries plan hperm nodes (fun p hp => by
    cases hs : p.2.isInlineScope
    · exact hsec p hp hs
    · exact hinl p hp hs) honly

private theorem nodup_key_ne_of_scope (plan : List (String × EntryPlacement))
    (hnd : noDupStringsBool (plan.map Prod.fst) = true) (p p' : String × EntryPlacement)
    (hp : p ∈ plan) (hp' : p' ∈ plan) (hps : p.2.isInlineScope = true) (hps' : p'.2.isInlineScope = false) :
    p.1 ≠ p'.1 := fun heq => by
  have hnd' := (noDupStringsBool_iff_nodup _).mp hnd; clear hnd
  induction plan with
  | nil => cases hp
  | cons _ _ ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd'
    rcases List.mem_cons.mp hp with rfl | hpxs <;> rcases List.mem_cons.mp hp' with rfl | hp'xs
    · rw [hps] at hps'; cases hps'
    · exact hnd'.1 (heq ▸ List.mem_map.mpr ⟨p', hp'xs, rfl⟩)
    · exact hnd'.1 (heq.symm ▸ List.mem_map.mpr ⟨p, hpxs, rfl⟩)
    · exact ih hpxs hp'xs hnd'.2

private def DotPost (numApi : CharNumApi) (origEntries : List (String × TomlValue))
    (remPlan : List (String × EntryPlacement)) (f : DocFocus)
    (subLoc : List (String × Node)) (rbDotted : List (String × Node) → List (String × Node)) (lines : List String) : Prop :=
  ∃ finalSubLoc,
    (∀ p ∈ remPlan, ∃ v nd, lookupKeyList p.1 origEntries = some v ∧ assocLookupNode p.1 finalSubLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
    (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalSubLoc = assocLookupNode q subLoc) ∧
    (remPlan = [] → lines = [] ∧ finalSubLoc = subLoc) ∧
    (remPlan ≠ [] → DocSteps numApi lines f.path f.root f.path (f.rb (rbDotted finalSubLoc)))

private def InlPost (numApi : CharNumApi) (origEntries : List (String × TomlValue))
    (remPlan : List (String × EntryPlacement)) (f : DocFocus) (lines : List String) : Prop :=
  ∃ finalLoc,
    (∀ p ∈ remPlan, p.2.isInlineScope = true →
      ∃ v nd, lookupKeyList p.1 origEntries = some v ∧ assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
    (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 finalLoc = assocLookupNode p.1 f.loc) ∧
    (∀ q, q ∉ remPlan.map Prod.fst → assocLookupNode q finalLoc = assocLookupNode q f.loc) ∧
    DocSteps numApi lines f.path f.root f.path (f.rb finalLoc)

private def SecPost (numApi : CharNumApi) (origEntries : List (String × TomlValue))
    (remPlan : List (String × EntryPlacement)) (f : DocFocus) (startAct : List String) (lines : List String) : Prop :=
  (remPlan.any (fun p => !p.2.isInlineScope) = false → lines = []) ∧
  (remPlan.any (fun p => !p.2.isInlineScope) = true → ∃ finalLoc endAct,
    (∀ p ∈ remPlan, p.2.isInlineScope = false →
      ∃ v nd, lookupKeyList p.1 origEntries = some v ∧ assocLookupNode p.1 finalLoc = some nd ∧ TomlEquiv v (nodeToTomlValue nd)) ∧
    (∀ q, (∀ p ∈ remPlan, p.2.isInlineScope = false → q ≠ p.1) → assocLookupNode q finalLoc = assocLookupNode q f.loc) ∧
    (f.withLoc finalLoc).Exact ∧ DocSteps numApi lines startAct f.root endAct (f.rb finalLoc))

private theorem dot_cons_compose {numApi origEntries k ep tl f subLoc rbDotted hdLines tailLines v nd}
    (hnot_tl : k ∉ tl.map Prod.fst) (hlk : lookupKeyList k origEntries = some v) (heqv : TomlEquiv v (nodeToTomlValue nd))
    (hSteps1 : DocSteps numApi hdLines f.path f.root f.path (f.rb (rbDotted (assocSetNode k nd subLoc))))
    (htl : DotPost numApi origEntries tl (f.withLoc (rbDotted (assocSetNode k nd subLoc))) (assocSetNode k nd subLoc) rbDotted tailLines) :
    DotPost numApi origEntries ((k, ep) :: tl) f subLoc rbDotted (hdLines ++ tailLines) := by
  rcases htl with ⟨finalSub, htl_match, htl_rest, htl_nil, htl_cons⟩
  refine ⟨finalSub, ?_, ?_, (fun h => nomatch h), fun _ => ?_⟩
  · intro p hp; rcases List.mem_cons.mp hp with rfl | hptl
    · exact ⟨v, nd, hlk, by rw [htl_rest k hnot_tl]; simp [assocLookupNode_assocSetNode], heqv⟩
    · exact htl_match p hptl
  · intro q hq; rw [htl_rest q (fun hm => hq (by simp [hm]))]; exact assocLookupNode_assocSetNode_ne k q nd subLoc (fun heq => hq (by simp [heq]))
  · cases tl with
    | nil => rcases htl_nil rfl with ⟨rfl, rfl⟩; simpa using hSteps1
    | cons _ _ => exact docSteps_append hSteps1 (htl_cons (by simp))

private theorem inl_cons_compose {numApi origEntries k ep tl f hdLines tailLines v nd}
    (hsc : ep.isInlineScope = true) (hnot_tl : k ∉ tl.map Prod.fst)
    (hlk : lookupKeyList k origEntries = some v) (heqv : TomlEquiv v (nodeToTomlValue nd))
    (hSteps1 : DocSteps numApi hdLines f.path f.root f.path (f.rb (assocSetNode k nd f.loc)))
    (htl : InlPost numApi origEntries tl (f.withLoc (assocSetNode k nd f.loc)) tailLines) :
    InlPost numApi origEntries ((k, ep) :: tl) f (hdLines ++ tailLines) := by
  rcases htl with ⟨finalLoc, htl_inl, htl_sec, htl_rest, hSteps2⟩
  refine ⟨finalLoc, ?_, ?_, ?_, docSteps_append hSteps1 hSteps2⟩
  · intro p hp hps; rcases List.mem_cons.mp hp with rfl | hptl
    · exact ⟨v, nd, hlk, by rw [htl_rest k hnot_tl]; simp [assocLookupNode_assocSetNode], heqv⟩
    · exact htl_inl p hptl hps
  · intro p hp hps; rcases List.mem_cons.mp hp with rfl | hptl
    · rw [hsc] at hps; cases hps
    · rw [htl_sec p hptl hps]; exact assocLookupNode_assocSetNode_ne k p.1 nd f.loc (fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hptl, rfl⟩))
  · intro q hq; rw [htl_rest q (fun hm => hq (by simp [hm]))]; exact assocLookupNode_assocSetNode_ne k q nd f.loc (fun heq => hq (by simp [heq]))

private theorem renderSection_compose_tail {numApi origEntries k ep tl f startAct midAct secLines tailLines v nd}
    (hsc : ep.isInlineScope = false) (hnot_tl : k ∉ tl.map Prod.fst)
    (hlk : lookupKeyList k origEntries = some v) (heqv : TomlEquiv v (nodeToTomlValue nd))
    (hMidExact : (f.withLoc (assocSetNode k nd f.loc)).Exact)
    (hSteps1 : DocSteps numApi secLines startAct f.root midAct (f.rb (assocSetNode k nd f.loc)))
    (htl : SecPost numApi origEntries tl (f.withLoc (assocSetNode k nd f.loc)) midAct tailLines) :
    SecPost numApi origEntries ((k, ep) :: tl) f startAct (secLines ++ tailLines) := by
  refine ⟨(fun h => by simp [hsc] at h), fun _ => ?_⟩
  by_cases htl_any : tl.any (fun p => !p.2.isInlineScope) = true
  · obtain ⟨finalLoc, endAct, htl_match, htl_pres, htl_Exact, hSteps2⟩ := htl.2 htl_any
    have hpres_k := htl_pres k (fun p hp _ heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))
    refine ⟨finalLoc, endAct, ?_, ?_, htl_Exact, docSteps_append hSteps1 hSteps2⟩
    · intro p hp hps; rcases List.mem_cons.mp hp with rfl | hptl
      · exact ⟨v, nd, hlk, by rw [hpres_k]; simp [assocLookupNode_assocSetNode], heqv⟩
      · exact htl_match p hptl hps
    · intro q hq; rw [htl_pres q (fun p hp hps => hq p (by simp [hp]) hps)]
      exact assocLookupNode_assocSetNode_ne k q nd f.loc (hq (k, ep) (by simp) hsc)
  · have htl_any_f := Bool.eq_false_iff.mpr htl_any; have htl_nil := htl.1 htl_any_f; subst htl_nil
    refine ⟨assocSetNode k nd f.loc, midAct, ?_, fun q hq => assocLookupNode_assocSetNode_ne k q nd f.loc (hq (k, ep) (by simp) hsc),
      hMidExact, by simpa using hSteps1⟩
    intro p hp hps; rcases List.mem_cons.mp hp with rfl | hptl
    · exact ⟨v, nd, hlk, by simp [assocLookupNode_assocSetNode], heqv⟩
    · have hbad : tl.any (fun p => !p.2.isInlineScope) = true := List.any_eq_true.mpr ⟨p, hptl, by simp [hps]⟩
      rw [htl_any_f] at hbad; cases hbad

private def renderDottedItem (revPref : List String) (k : String) (ep : EntryPlacement) (v : TomlValue) : Option (List String) :=
  match ep with
  | .direct ks vt comment => do
    let rk ← renderKey k ks; let rv ← renderValueInline v vt; let rc ← renderCommentSuffix comment
    some [joinRenderedPath (rk :: revPref).reverse ++ " = " ++ rv ++ rc]
  | .dotted ks subPlan => match v with
    | .table sub => if sub.isEmpty then none else do let rk ← renderKey k ks; renderDottedSub (rk :: revPref) sub.toList subPlan
    | _ => none
  | _ => none

private theorem renderDottedList_cons_inv {revPref origEntries k ep tl lines}
    (h : renderDottedList revPref origEntries ((k, ep) :: tl) = some lines) :
    ∃ v hdLines tailLines, lookupKeyList k origEntries = some v ∧ renderDottedItem revPref k ep v = some hdLines ∧
      renderDottedList revPref origEntries tl = some tailLines ∧ lines = hdLines ++ tailLines := by
  cases hlk : lookupKeyList k origEntries <;> (simp only [renderDottedList, hlk, none_bind] at h; try contradiction)
  rename_i v; cases ep <;> (simp only [bind_some, some_bind, Option.some.injEq] at h; try contradiction)
  · rcases h with ⟨rk, hrk, rv, hrv, rc, hrc, tlL, htl, rfl⟩
    exact ⟨v, _, tlL, rfl, by simp [renderDottedItem, hrk, hrv, hrc], htl, rfl⟩
  · cases v <;> try contradiction
    rename_i sub; cases hemp : sub.isEmpty <;> (simp only [hemp, ↓reduceIte, Bool.false_eq_true, bind_some, Option.some.injEq] at h; try contradiction)
    rcases h with ⟨rk, hrk, hdL, hsub, tlL, htl, rfl⟩
    exact ⟨_, hdL, tlL, rfl, by simp [renderDottedItem, hemp, hrk, hsub], htl, rfl⟩

private theorem renderInlineEntries_cons_inv {revPref origEntries k ep tl lines}
    (h : renderInlineEntries revPref origEntries ((k, ep) :: tl) = some lines) :
    (ep.isInlineScope = false ∧ renderInlineEntries revPref origEntries tl = some lines) ∨
    (ep.isInlineScope = true ∧ ∃ v hdLines tailLines, lookupKeyList k origEntries = some v ∧ renderDottedItem [] k ep v = some hdLines ∧
      renderInlineEntries revPref origEntries tl = some tailLines ∧ lines = hdLines ++ tailLines) := by
  cases ep <;> simp only [renderInlineEntries, EntryPlacement.isInlineScope, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, some_bind, bind_some, Option.some.injEq, List.nil_append] at h
  · cases hlk : lookupKeyList k origEntries <;> (simp only [hlk, none_bind, bind_some, Option.some.injEq] at h; try contradiction)
    rename_i v; rcases h with ⟨rk, hrk, rv, hrv, rc, hrc, tlL, htl, rfl⟩
    exact Or.inr ⟨rfl, v, _, tlL, rfl, by simp [renderDottedItem, joinRenderedPath, hrk, hrv, hrc], htl, rfl⟩
  · cases hlk : lookupKeyList k origEntries <;> (simp only [hlk, none_bind] at h; try contradiction)
    rename_i v; cases v <;> try contradiction
    rename_i sub; cases hemp : sub.isEmpty <;> (simp only [hemp, ↓reduceIte, Bool.false_eq_true, bind_some, Option.some.injEq] at h; try contradiction)
    rcases h with ⟨rk, hrk, hdL, hsub, tlL, htl, rfl⟩
    exact Or.inr ⟨rfl, _, hdL, tlL, rfl, by simp [renderDottedItem, hemp, hrk, hsub], htl, rfl⟩
  · rcases h with ⟨_, htl, rfl⟩; exact Or.inl ⟨rfl, htl⟩
  · rcases h with ⟨_, htl, rfl⟩; exact Or.inl ⟨rfl, htl⟩

private abbrev RenderPlanP1 (numApi : CharNumApi) (n : Nat) : Prop :=
  ∀ origEntries remPlan dotPairs lines, sizeOf remPlan ≤ n → dotPairs ≠ [] →
    (∀ p ∈ dotPairs, ∃ ks, renderKey p.1 ks = some p.2) → noDupStringsBool (remPlan.map Prod.fst) = true →
    (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) →
    renderDottedList (dotPairs.map Prod.snd).reverse origEntries remPlan = some lines →
    ∀ (f : DocFocus) subLoc rbDotted, f.Exact → DottedWriteFocus f.loc (dotPairs.map Prod.fst) subLoc rbDotted →
      (∀ p ∈ remPlan, assocLookupNode p.1 subLoc = none) → DotPost numApi origEntries remPlan f subLoc rbDotted lines
private abbrev RenderPlanP2 (numApi : CharNumApi) (n : Nat) : Prop :=
  ∀ origEntries remPlan revRen lines, sizeOf remPlan ≤ n → noDupStringsBool (remPlan.map Prod.fst) = true →
    (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) → renderInlineEntries revRen origEntries remPlan = some lines →
    ∀ (f : DocFocus), f.Exact → (∀ p ∈ remPlan, p.2.isInlineScope = true → assocLookupNode p.1 f.loc = none) → InlPost numApi origEntries remPlan f lines
private abbrev RenderPlanP3 (numApi : CharNumApi) (n : Nat) : Prop :=
  ∀ elemPlans xs (f : DocFocus) k rk rc lines, sizeOf elemPlans ≤ n →
    (∃ ks, renderKey k ks = some rk) → (∃ comment, renderCommentSuffix comment = some rc) →
    renderAotElems (rk :: f.revRen) rc xs elemPlans = some lines →
    ∀ prevElems startAct, f.Header →
      ((prevElems = [] ∧ assocLookupNode k f.loc = none) ∨ (prevElems ≠ [] ∧ assocLookupNode k f.loc = some (.aot prevElems))) →
      ∃ finalElems endAct, (xs = [] → finalElems = prevElems ∧ lines = [] ∧ endAct = startAct) ∧
        (xs ≠ [] → ∃ tailElems, finalElems = prevElems ++ tailElems ∧ tailElems ≠ [] ∧
          TomlListEquiv xs (aotElemsToToml tailElems) ∧ (f.withLoc (assocSetNode k (.aot finalElems) f.loc)).Exact ∧
          DocSteps numApi lines startAct f.root endAct (f.rb (assocSetNode k (.aot finalElems) f.loc)))
private abbrev RenderPlanP4 (numApi : CharNumApi) (n : Nat) : Prop :=
  ∀ origEntries remPlan (f : DocFocus) lines, sizeOf remPlan ≤ n → noDupStringsBool (remPlan.map Prod.fst) = true →
    (∀ p ∈ remPlan, ∃ v, lookupKeyList p.1 origEntries = some v) → renderSectionEntries f.revRen origEntries remPlan = some lines →
    ∀ startAct, f.Header → (∀ p ∈ remPlan, p.2.isInlineScope = false → assocLookupNode p.1 f.loc = none) → SecPost numApi origEntries remPlan f startAct lines
private abbrev RenderPlanP5 (numApi : CharNumApi) (n : Nat) : Prop :=
  ∀ origEntries plan (f : DocFocus) lines, sizeOf plan + 1 ≤ n → renderTablePlan f.revRen origEntries plan = some lines →
    f.Exact → f.loc = [] → ∃ finalLoc endAct, TomlTableEquivList origEntries (entriesToTomlList finalLoc) ∧
      (f.withLoc finalLoc).Exact ∧ DocSteps numApi lines f.path f.root endAct (f.rb finalLoc)
private abbrev RenderPlanAll (numApi : CharNumApi) (n : Nat) : Prop :=
  RenderPlanP1 numApi n ∧ RenderPlanP2 numApi n ∧ RenderPlanP3 numApi n ∧ RenderPlanP4 numApi n ∧ RenderPlanP5 numApi n

private theorem nodup_cons_split {k : String} {ep : EntryPlacement} {tl : List (String × EntryPlacement)}
    (hnd : noDupStringsBool (((k, ep) :: tl).map Prod.fst) = true) :
    k ∉ tl.map Prod.fst ∧ noDupStringsBool (tl.map Prod.fst) = true := by
  simp only [List.map_cons, noDupStringsBool, Bool.and_eq_true, Bool.not_eq_true'] at hnd
  exact ⟨(fun hm => by rw [List.contains_iff_mem.mpr hm] at hnd; nomatch hnd.1), hnd.2⟩

private theorem renderDottedItem_step {numApi : CharNumApi} (hApi : ValidCharNum numApi)
    {n : Nat} (ih : ∀ m < n, RenderPlanAll numApi m)
    (dotPairs : List (String × String)) (hdot_keys : ∀ p ∈ dotPairs, ∃ ks, renderKey p.1 ks = some p.2)
    {k : String} {ep : EntryPlacement} {tl : List (String × EntryPlacement)} {v : TomlValue}
    (hsz : sizeOf ((k, ep) :: tl) ≤ n) {f : DocFocus} {subLoc : List (String × Node)}
    {rbDotted : List (String × Node) → List (String × Node)}
    (hfExact : f.Exact) (hDotFocus : DottedWriteFocus f.loc (dotPairs.map Prod.fst) subLoc rbDotted)
    (hnone_k : assocLookupNode k subLoc = none) {hdLines : List String}
    (hitem : renderDottedItem (dotPairs.map Prod.snd).reverse k ep v = some hdLines) :
    ∃ nd, TomlEquiv v (nodeToTomlValue nd) ∧
      DocSteps numApi hdLines f.path f.root f.path (f.rb (rbDotted (assocSetNode k nd subLoc))) := by
  cases ep with
  | tableSection _ _ _ _ | aotSection _ _ _ => cases hitem
  | direct ks vt comment =>
    simp only [renderDottedItem, bind_some, Option.some.injEq] at hitem
    rcases hitem with ⟨rk, hrk, rv, hrv, rc, hrc, rfl⟩
    let nextDot := dotPairs ++ [(k, rk)]
    obtain ⟨v', heqv, hstep⟩ := docSteps_assign numApi hApi nextDot (by simp [nextDot])
      (keysValid_push hdot_keys ⟨ks, hrk⟩) v vt rv hrv comment rc hrc f.path f.root
    let midSub := assocSetNode k (valueToInlineNode v') subLoc
    have hins_parent : insertDottedEntries (f.path ++ nextDot.map Prod.fst) f.loc
        (nextDot.map Prod.fst) (valueToInlineNode v') = .ok (rbDotted midSub) := by
      simpa [nextDot, List.map_append] using dottedWriteFocus_insert hDotFocus _ [k] (by simp) _ midSub
        (by simp [insertDottedEntries, hnone_k, midSub])
    exact ⟨valueToInlineNode v', by simpa [nodeToTomlValue_valueToInlineNode] using heqv,
      by rw [show joinRenderedPath (rk :: (dotPairs.map Prod.snd).reverse).reverse ++ " = " ++ rv ++ rc =
           joinRenderedPath (nextDot.map Prod.snd) ++ " = " ++ rv ++ rc by simp [nextDot]]
         exact hstep _ (atLocalPath_insertAtActivePath hfExact.2 _ _ _ _ hins_parent)⟩
  | dotted ks subPlan =>
    cases v <;> (simp only [renderDottedItem] at hitem; try contradiction)
    rename_i sub
    simp only [ite_true_none_some, bind_some, renderDottedSub, not_eq_false] at hitem
    rcases hitem with ⟨hemp, rk, hrk, hperm, hsub_l⟩
    let nextDot := dotPairs ++ [(k, rk)]
    obtain ⟨_, hnd_sub, hmem_sub, hcov⟩ := isPlanPermutation_props hperm
    have hsubPlan_ne : subPlan ≠ [] := fun hnil => by
      cases hcons : sub.toList with
      | nil => rw [Array.toList_eq_nil_iff.mp hcons] at hemp; cases hemp
      | cons hd _ => obtain ⟨_, hep0⟩ := hcov hd.1 hd.2 (by simp [hcons, lookupKeyList]); rw [hnil] at hep0; cases hep0
    obtain ⟨finalChild, hsub_match, hsub_rest, _, hsub_steps⟩ :=
      (ih (sizeOf subPlan) (by simp +arith at hsz; omega)).1 sub.toList subPlan nextDot hdLines
        (Nat.le_refl _) (by simp [nextDot]) (keysValid_push hdot_keys ⟨ks, hrk⟩) hnd_sub hmem_sub
        (by simpa [nextDot] using hsub_l) f [] _ hfExact
        (by simpa [nextDot, List.map_append] using dottedWriteFocus_step hDotFocus k hnone_k) (fun _ _ => rfl)
    exact ⟨.table .dotted finalChild,
      by simpa [nodeToTomlValue, TomlEquiv] using entriesToTomlList_of_plan_match sub.toList subPlan hperm finalChild hsub_match hsub_rest,
      hsub_steps hsubPlan_ne⟩

private theorem renderPlan_dot_step (numApi : CharNumApi) (hApi : ValidCharNum numApi)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) : RenderPlanP1 numApi n := by
  intro origEntries remPlan dotPairs lines hsz hdot_ne hdot_keys hnd_rem hmem_rem hdl f subLoc rbDotted hfExact hDotFocus hfresh
  cases remPlan with
  | nil =>
    simp only [renderDottedList, Option.some.injEq] at hdl; subst hdl
    exact ⟨subLoc, (fun _ hp => nomatch hp), (fun _ _ => rfl), (fun _ => ⟨rfl, rfl⟩), fun hne => absurd rfl hne⟩
  | cons hd tl =>
    rcases hd with ⟨k, ep⟩; obtain ⟨hnot_tl, hnd_tl⟩ := nodup_cons_split hnd_rem
    obtain ⟨v, hdLines, tailLines, hlk, hitem, htail, rfl⟩ := renderDottedList_cons_inv hdl
    obtain ⟨nd, heqv, hSteps1⟩ := renderDottedItem_step hApi ih dotPairs hdot_keys hsz hfExact hDotFocus (hfresh (k, ep) (by simp)) hitem
    refine dot_cons_compose hnot_tl hlk heqv hSteps1 ?_
    exact (ih (sizeOf tl) (by simp +arith at hsz; omega)).1 origEntries tl dotPairs tailLines (Nat.le_refl _) hdot_ne hdot_keys hnd_tl
      (fun p hp => hmem_rem p (by simp [hp])) htail (f.withLoc _) (assocSetNode k nd subLoc) rbDotted
      (f.exact_withLoc hfExact _) (dottedWriteFocus_rebuild hDotFocus _)
      (fun p hp => by rw [assocLookupNode_assocSetNode_ne k p.1 nd subLoc (fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]; exact hfresh p (by simp [hp]))

private theorem renderPlan_inl_step (numApi : CharNumApi) (hApi : ValidCharNum numApi)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) : RenderPlanP2 numApi n := by
  intro origEntries remPlan revRen lines hsz hnd_rem hmem_rem hrie f hfExact hfresh
  cases remPlan with
  | nil =>
    simp only [renderInlineEntries, Option.some.injEq] at hrie; subst hrie
    exact ⟨f.loc, (fun _ hp => nomatch hp), (fun _ hp => nomatch hp), (fun _ _ => rfl), by rw [atLocalPath_self hfExact.2]; exact docSteps_nil⟩
  | cons hd tl =>
    rcases hd with ⟨k, ep⟩; obtain ⟨hnot_tl, hnd_tl⟩ := nodup_cons_split hnd_rem
    have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
    have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v := fun p hp => hmem_rem p (by simp [hp])
    rcases renderInlineEntries_cons_inv hrie with ⟨hsc_false, htail⟩ | ⟨hsc, v, hdLines, tailLines, hlk, hitem, htail, rfl⟩
    · obtain ⟨finalLoc, htl_inl, htl_sec, htl_rest, hSteps⟩ :=
        (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen lines (Nat.le_refl _) hnd_tl hmem_tl htail
          f hfExact (fun p hp hps => hfresh p (by simp [hp]) hps)
      refine ⟨finalLoc, ?_, ?_, fun q hq => htl_rest q (fun hm => hq (by simp [hm])), hSteps⟩
      · intro p hp hps; rcases List.mem_cons.mp hp with rfl | hptl; · rw [hsc_false] at hps; cases hps
        · exact htl_inl p hptl hps
      · intro p hp hps; rcases List.mem_cons.mp hp with rfl | hptl; · exact htl_rest k hnot_tl
        · exact htl_sec p hptl hps
    · obtain ⟨nd, heqv, hSteps1⟩ := renderDottedItem_step hApi ih [] (fun _ h => nomatch h) hsz hfExact (.nil f.loc)
        (hfresh (k, ep) (by simp) hsc) hitem
      refine inl_cons_compose hsc hnot_tl hlk heqv hSteps1 ?_
      exact (ih (sizeOf tl) hsz_tl).2.1 origEntries tl revRen tailLines (Nat.le_refl _) hnd_tl hmem_tl htail
        (f.withLoc _) (f.exact_withLoc hfExact _) (fun p hp hps => by
          rw [assocLookupNode_assocSetNode_ne k p.1 nd f.loc (fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]
          exact hfresh p (by simp [hp]) hps)

private theorem renderPlan_aot_step (numApi : CharNumApi)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) : RenderPlanP3 numApi n := by
  intro elemPlans xs f k rk rc lines hsz hk ⟨comment, hrc⟩ hrae prevElems startAct hfHdr hprev
  cases xs with
  | nil =>
    cases elemPlans <;> simp [renderAotElems] at hrae
    subst hrae; exact ⟨prevElems, startAct, fun _ => ⟨rfl, rfl, rfl⟩, fun hne => absurd rfl hne⟩
  | cons elemVal xs' =>
    cases elemPlans <;> cases elemVal <;> (simp only [renderAotElems, bind_some, Option.some.injEq] at hrae; try contradiction)
    rename_i ep eps elem; rcases hrae with ⟨bodyLines, hbody, tailLines, htail, rfl⟩
    obtain ⟨hElemExact, hHdrSteps⟩ := docFocus_openAotElem numApi prevElems startAct hfHdr hk hrc hprev
    have hsz_ep : sizeOf ep + 1 < n := by cases eps <;> simp +arith at hsz <;> omega
    obtain ⟨finalElem, midAct, heqv_elem, _, hBodySteps⟩ :=
      (ih (sizeOf ep + 1) hsz_ep).2.2.2.2 elem.toList ep (f.pushAotElem k rk prevElems) bodyLines
        (Nat.le_refl _) (by simpa [DocFocus.pushAotElem, DocFocus.revRen] using hbody) hElemExact rfl
    let midParent := assocSetNode k (.aot (prevElems ++ [finalElem])) f.loc
    have hMidExact := f.header_withLoc hfHdr midParent
    obtain ⟨finalElems, endAct, hxs_nil, hxs_cons⟩ :=
      (ih (sizeOf eps) (by simp +arith at hsz; omega)).2.2.1 eps xs' (f.withLoc midParent) k rk rc tailLines
        (Nat.le_refl _) hk ⟨comment, hrc⟩ htail (prevElems ++ [finalElem]) midAct
        (DocFocus.exact_to_header hMidExact) (Or.inr ⟨by simp, by simp [midParent, assocLookupNode_assocSetNode]⟩)
    have hStepsFirst := docSteps_append hHdrSteps hBodySteps
    cases xs' with
    | nil =>
      rcases hxs_nil rfl with ⟨rfl, rfl, rfl⟩
      exact ⟨prevElems ++ [finalElem], endAct, (fun h => nomatch h), fun _ =>
        ⟨[finalElem], rfl, by simp, by simpa [aotElemsToToml, TomlListEquiv, TomlEquiv] using heqv_elem,
         hMidExact, by simpa [List.append_nil, DocFocus.pushAotElem] using hStepsFirst⟩⟩
    | cons _ _ =>
      obtain ⟨tailElems2, hfin_eq, _, heqv_tail, _, hTailSteps⟩ := hxs_cons (by simp)
      have hrb_idem : f.rb (assocSetNode k (.aot finalElems) midParent) =
          f.rb (assocSetNode k (.aot finalElems) f.loc) := by simp [midParent, assocSetNode_idem]
      refine ⟨finalElems, endAct, (fun h => nomatch h), fun _ =>
        ⟨finalElem :: tailElems2, by rw [hfin_eq, List.append_assoc]; rfl, by simp,
         by simpa [aotElemsToToml, TomlListEquiv, TomlEquiv] using And.intro heqv_elem heqv_tail, f.header_withLoc hfHdr _, ?_⟩⟩
      dsimp only [DocFocus.pushAotElem] at hStepsFirst; rw [hrb_idem] at hTailSteps
      exact docSteps_append hStepsFirst hTailSteps

private theorem renderPlan_sec_step (numApi : CharNumApi)
    (n : Nat) (ih : ∀ m < n, RenderPlanAll numApi m) : RenderPlanP4 numApi n := by
  intro origEntries remPlan f lines hsz hnd_rem hmem_rem hrse startAct hfHdr hfresh
  cases remPlan with
  | nil =>
    simp only [renderSectionEntries, Option.some.injEq] at hrse; subst hrse
    exact ⟨fun _ => rfl, fun h => by simp at h⟩
  | cons hd tl =>
    rcases hd with ⟨k, ep⟩; obtain ⟨hnot_tl, hnd_tl⟩ := nodup_cons_split hnd_rem
    have hsz_tl : sizeOf tl < n := by simp +arith at hsz; omega
    have hmem_tl : ∀ p ∈ tl, ∃ v, lookupKeyList p.1 origEntries = some v := fun p hp => hmem_rem p (by simp [hp])
    have hrun_tl : ∀ (nd : Node) (midAct tailLines : List String),
        renderSectionEntries f.revRen origEntries tl = some tailLines →
        SecPost numApi origEntries tl (f.withLoc (assocSetNode k nd f.loc)) midAct tailLines := fun nd midAct tailLines htail =>
      (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl (f.withLoc (assocSetNode k nd f.loc)) tailLines
        (Nat.le_refl _) hnd_tl hmem_tl htail midAct (DocFocus.exact_to_header (f.header_withLoc hfHdr _))
        (fun p hp hps => by
          rw [assocLookupNode_assocSetNode_ne k p.1 nd f.loc (fun heq => hnot_tl (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]
          exact hfresh p (by simp [hp]) hps)
    cases ep with
    | direct _ _ _ | dotted _ _ =>
      simp only [renderSectionEntries, EntryPlacement.isInlineScope, ↓reduceIte, some_bind, bind_some, Option.some.injEq, List.nil_append] at hrse
      rcases hrse with ⟨_, htail, rfl⟩
      have htl := (ih (sizeOf tl) hsz_tl).2.2.2.1 origEntries tl f _ (Nat.le_refl _) hnd_tl hmem_tl htail
        startAct hfHdr (fun p hp hps => hfresh p (by simp [hp]) hps)
      refine ⟨fun hn => htl.1 (by simpa [EntryPlacement.isInlineScope] using hn), fun hs => ?_⟩
      obtain ⟨finalLoc, endAct, hm, hp, hex, hst⟩ := htl.2 (by simpa [EntryPlacement.isInlineScope] using hs)
      refine ⟨finalLoc, endAct, ?_, fun q hq => hp q (fun p hpm hps => hq p (by simp [hpm]) hps), hex, hst⟩
      intro p hpm hps; rcases List.mem_cons.mp hpm with rfl | hptl; · simp [EntryPlacement.isInlineScope] at hps
      · exact hm p hptl hps
    | tableSection ks subtableFirst subPlan comment =>
      have hsc_false : (EntryPlacement.tableSection ks subtableFirst subPlan comment).isInlineScope = false := rfl
      have hnone_k := hfresh (k, _) List.mem_cons_self hsc_false
      cases hlk : lookupKeyList k origEntries <;>
        (simp only [renderSectionEntries, EntryPlacement.isInlineScope, Bool.false_eq_true, ↓reduceIte, hlk, none_bind] at hrse; try contradiction)
      rename_i v; cases v <;> try contradiction
      rename_i sub; cases subtableFirst with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, bind_some, some_bind, Option.some.injEq] at hrse
        rcases hrse with ⟨rk, hrk, rc, hrc, bodyLines, hbody, tailLines, htail, rfl⟩
        obtain ⟨hSubEx, hHdrSteps⟩ := docFocus_emitExplicit numApi [] f.root startAct hfHdr ⟨ks, hrk⟩ hrc
          (atHeaderFocus_applyHeader .table hfHdr.2 (f.path ++ [k]) [k] (by simp) _ (by simp [applyHeader, applyHeaderLeaf, hnone_k]))
        obtain ⟨finalSub, midAct, heqv_sub, _, hBodySteps⟩ :=
          (ih (sizeOf subPlan + 1) (by simp +arith at hsz; omega)).2.2.2.2 sub.toList subPlan (f.pushExplicit k rk [])
            bodyLines (Nat.le_refl _) (by simpa [DocFocus.pushExplicit, DocFocus.revRen] using hbody) hSubEx rfl
        exact renderSection_compose_tail hsc_false hnot_tl hlk
          (by simpa [nodeToTomlValue, TomlEquiv] using heqv_sub) (f.header_withLoc hfHdr _)
          (docSteps_append hHdrSteps hBodySteps) (hrun_tl (.table .explicit finalSub) midAct tailLines htail)
      | true =>
        cases hperm : isPlanPermutation sub.toList subPlan <;>
          (simp only [↓reduceIte, hperm, Bool.not_false, Bool.not_true, Bool.false_eq_true, bind_const_none] at hrse; try contradiction)
        cases hall : subPlan.all (fun p => p.2.isInlineScope)
        · have hall' := hall; simp only [EntryPlacement.isInlineScope] at hall'
          simp only [hall', Bool.false_eq_true, ↓reduceIte, bind_some, some_bind, Option.some.injEq] at hrse
          rcases hrse with ⟨rk, hrk, rc, hrc, secLines, hsec_sub, inlLines, hinl_sub, tailLines, htail, rfl⟩
          have hany_sub : subPlan.any (fun p => !p.2.isInlineScope) = true := by
            cases h : subPlan.any (fun p => !p.2.isInlineScope)
            · have ha : subPlan.all (fun p => p.2.isInlineScope) = true := by
                rw [List.any_eq_false] at h
                exact List.all_eq_true.mpr fun p hp => (not_eq_false _).mp (Bool.eq_false_iff.mpr (h p hp))
              rw [ha] at hall; cases hall
            · rfl
          obtain ⟨_, hnd_sub, hmem_sub, _⟩ := isPlanPermutation_props hperm
          have hsz_sub : sizeOf subPlan < n := by simp +arith at hsz; omega
          have hsec_post := (ih (sizeOf subPlan) hsz_sub).2.2.2.1 sub.toList subPlan (f.pushImplicit k rk) secLines
            (Nat.le_refl _) hnd_sub hmem_sub (by simpa [DocFocus.pushImplicit, DocFocus.revRen] using hsec_sub)
            startAct (docFocus_pushImplicit hfHdr ⟨ks, hrk⟩ hnone_k) (fun _ _ _ => rfl)
          obtain ⟨midSub, midAct1, hsec_match, hsec_pres, _, hSecSteps⟩ := hsec_post.2 hany_sub
          let impParent := assocSetNode k (.table .subtableImplicit midSub) f.loc
          obtain ⟨hExpEx, hHdrSteps⟩ := docFocus_emitExplicit numApi midSub (f.rb impParent) midAct1 hfHdr ⟨ks, hrk⟩ hrc
            (atLocalPath_applyHeader .table (atHeaderFocus_step hfHdr.2 impParent) (f.path ++ [k]) [k] (by simp) _
              (by simp [applyHeader, applyHeaderLeaf, impParent, assocLookupNode_assocSetNode, assocSetNode_idem]))
          obtain ⟨finalSub, hinl_match, hinl_sec, hinl_rest, hInlSteps⟩ :=
            (ih (sizeOf subPlan) hsz_sub).2.1 sub.toList subPlan (rk :: f.revRen) inlLines
              (Nat.le_refl _) hnd_sub hmem_sub hinl_sub (f.pushExplicit k rk midSub) hExpEx
              (fun p hp hps => by
                dsimp only [DocFocus.pushExplicit]
                rw [hsec_pres p.1 (fun p' hp' hps' => nodup_key_ne_of_scope subPlan hnd_sub p p' hp hp' hps hps')]; rfl)
          have heqv_sub := tableEquiv_of_split_plan sub.toList subPlan hperm finalSub hinl_match
            (fun p hp hps => let ⟨v_s, nd_s, hv_s, hnd_s, heqv_s⟩ := hsec_match p hp hps; ⟨v_s, nd_s, hv_s, by rwa [hinl_sec p hp hps], heqv_s⟩)
            (fun q hq_not => by rw [hinl_rest q hq_not]; dsimp only [DocFocus.pushExplicit]; rw [hsec_pres q (fun p hp _ heq => hq_not (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩))]; rfl)
          exact renderSection_compose_tail hsc_false hnot_tl hlk
            (by simpa [nodeToTomlValue, TomlEquiv] using heqv_sub) (f.header_withLoc hfHdr _)
            (docSteps_append (docSteps_append hSecSteps hHdrSteps) hInlSteps)
            (hrun_tl (.table .explicit finalSub) (f.pushExplicit k rk midSub).path tailLines htail)
        · have hall' := hall; simp only [EntryPlacement.isInlineScope] at hall'
          simp only [hall', ↓reduceIte, bind_const_none] at hrse; contradiction
    | aotSection ks elemPlans comment =>
      have hsc_false : (EntryPlacement.aotSection ks elemPlans comment).isInlineScope = false := rfl
      have hnone_k := hfresh (k, _) List.mem_cons_self hsc_false
      cases hlk : lookupKeyList k origEntries <;>
        (simp only [renderSectionEntries, EntryPlacement.isInlineScope, Bool.false_eq_true, ↓reduceIte, hlk, none_bind] at hrse; try contradiction)
      rename_i v; cases v <;> try contradiction
      rename_i xs; cases hemp : xs.isEmpty <;>
        (simp only [hemp, ↓reduceIte, Bool.false_eq_true, bind_some, Option.some.injEq] at hrse; try contradiction)
      rcases hrse with ⟨rk, hrk, rc, hrc, aotLines, haot, tailLines, htail, rfl⟩
      have hxs_ne : xs.toList ≠ [] := fun heq => by rw [Array.toList_eq_nil_iff.mp heq] at hemp; cases hemp
      obtain ⟨finalElems, midAct, _, haot_cons⟩ :=
        (ih (sizeOf elemPlans) (by simp +arith at hsz; omega)).2.2.1 elemPlans xs.toList f k rk rc aotLines
          (Nat.le_refl _) ⟨ks, hrk⟩ ⟨comment, hrc⟩ haot [] startAct hfHdr (Or.inl ⟨rfl, hnone_k⟩)
      obtain ⟨tailElems, hfin_eq, _, heqv_aot, hMidEx, hAotSteps⟩ := haot_cons hxs_ne
      rw [List.nil_append] at hfin_eq; subst finalElems
      exact renderSection_compose_tail hsc_false hnot_tl hlk
        (by simpa [nodeToTomlValue, TomlEquiv] using heqv_aot) hMidEx hAotSteps
        (hrun_tl (.aot tailElems) midAct tailLines htail)

private theorem renderPlan_plan_step (numApi : CharNumApi)
    (n : Nat) (hInl : RenderPlanP2 numApi n) (hSec : RenderPlanP4 numApi n) : RenderPlanP5 numApi n := by
  intro origEntries plan f lines hsz hrtp hfExact hstart
  simp only [renderTablePlan, ite_true_none_some, not_eq_false, bind_some, Option.some.injEq] at hrtp
  rcases hrtp with ⟨hperm, inlLines, hinl, secLines, hsec, rfl⟩
  obtain ⟨_, hnd_p, hmem_p, _⟩ := isPlanPermutation_props hperm
  have hsz_le : sizeOf plan ≤ n := by omega
  obtain ⟨midLoc, hinl_match, hinl_sec, hinl_rest, hInlSteps⟩ :=
    hInl origEntries plan f.revRen inlLines hsz_le hnd_p hmem_p hinl f hfExact (fun _ _ _ => by rw [hstart]; rfl)
  have hMidEx := f.exact_withLoc hfExact midLoc
  have hsec_post := hSec origEntries plan (f.withLoc midLoc) secLines hsz_le hnd_p hmem_p hsec f.path
    (DocFocus.exact_to_header hMidEx) (fun p hp hps => by rw [hinl_sec p hp hps, hstart]; rfl)
  by_cases hany : plan.any (fun p => !p.2.isInlineScope) = true
  · obtain ⟨finalLoc, endAct, hsec_m, hsec_p, hFinEx, hSecSteps⟩ := hsec_post.2 hany
    refine ⟨finalLoc, endAct, ?_, hFinEx, docSteps_append hInlSteps hSecSteps⟩
    exact tableEquiv_of_split_plan origEntries plan hperm finalLoc
      (fun p hp hp_in => let ⟨v, nd, hv, hnd, heqv⟩ := hinl_match p hp hp_in
        ⟨v, nd, hv, by rwa [hsec_p p.1 (fun p' hp' hps' => nodup_key_ne_of_scope plan hnd_p p p' hp hp' hp_in hps')], heqv⟩)
      hsec_m (fun q hq_not => by rw [hsec_p q (fun p hp _ heq => hq_not (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)), hinl_rest q hq_not, hstart]; rfl)
  · have hany_f := Bool.eq_false_iff.mpr hany; have hsec_nil := hsec_post.1 hany_f; subst hsec_nil
    refine ⟨midLoc, f.path, ?_, hMidEx, by simpa using hInlSteps⟩
    exact tableEquiv_of_split_plan origEntries plan hperm midLoc hinl_match
      (fun p hp hps => absurd (List.any_eq_true.mpr ⟨p, hp, by simp [hps]⟩) hany)
      (fun q hq_not => by rw [hinl_rest q hq_not, hstart]; rfl)

private theorem renderPlan_all (numApi : CharNumApi) (hApi : ValidCharNum numApi) (n : Nat) : RenderPlanAll numApi n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hInl := renderPlan_inl_step numApi hApi n ih; have hSec := renderPlan_sec_step numApi n ih
    exact ⟨renderPlan_dot_step numApi hApi n ih, hInl, renderPlan_aot_step numApi n ih, hSec, renderPlan_plan_step numApi n hInl hSec⟩

private theorem render_parse_roundTrip_chars (numApi : CharNumApi) (hApi : ValidCharNum numApi)
    (doc : TomlTable) (tape : RenderTape) (out : String) (hrender : render doc tape = some out) :
    ∃ parsed, parseCharsWithNum numApi out.toList = .ok parsed ∧ TomlTableEquiv doc parsed := by
  unfold render at hrender
  cases hwf : wellFormedTableBool doc <;>
    (simp only [hwf, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrender; try contradiction)
  have ⟨hdrLines, bodyLines, hbody, hout, hhdr_cases⟩ :
      ∃ hdrLines bodyLines, renderTablePlan [] doc.toList tape.entries = some bodyLines ∧
        out = String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n" ∧
        (hdrLines = [] ∨ ∃ c, isSingleLineClean c = true ∧ hdrLines = ["#" ++ c]) := by
    cases hc : tape.headerComment with
    | none =>
      simp only [hc, some_bind, bind_some, Option.some.injEq] at hrender
      rcases hrender with ⟨bodyLines, hbody, rfl⟩; exact ⟨[], bodyLines, hbody, rfl, Or.inl rfl⟩
    | some c =>
      cases hsc : isSingleLineClean c <;>
        (simp only [hc, hsc, Bool.false_eq_true, ↓reduceIte, none_bind, some_bind, bind_some, Option.some.injEq] at hrender; try contradiction)
      rcases hrender with ⟨bodyLines, hbody, rfl⟩; exact ⟨["#" ++ c], bodyLines, hbody, rfl, Or.inr ⟨c, hsc, rfl⟩⟩
  subst hout
  let rootFocus : DocFocus := ⟨[], [], [], id⟩
  obtain ⟨finalLoc, _, heqv_list, _, hBodySteps⟩ :=
    (renderPlan_all numApi hApi (sizeOf tape.entries + 1)).2.2.2.2
      doc.toList tape.entries rootFocus bodyLines (Nat.le_refl _) hbody ⟨(fun _ h => nomatch h), .nil []⟩ rfl
  by_cases hall_empty : hdrLines ++ bodyLines = []
  · have hbody_e := (List.append_eq_nil_iff.mp hall_empty).2
    have hroot_eq : finalLoc = [] := by
      simpa [hbody_e, joinLines, parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux, rootFocus] using hBodySteps.2 [] 1 (by simp [hbody_e])
    refine ⟨#[], ?_, by rw [hroot_eq] at heqv_list; simpa [TomlTableEquiv, entriesToTomlList] using heqv_list⟩
    simp [parseCharsWithNum, show (String.intercalate "\n" (hdrLines ++ bodyLines) ++ "\n").toList = ['\n'] by simp [hall_empty],
      normalizeChars_clean ['\n'] (by decide) 1 1, parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux, entriesToTomlList, bind, Except.bind]
  · rw [intercalate_nl_append_nl (hdrLines ++ bodyLines) hall_empty]
    have hhdr_cl : CleanLines hdrLines := by
      rcases hhdr_cases with rfl | ⟨c, hc_clean, rfl⟩; · exact cleanLines_nil
      · refine cleanLines_singleton (cleanStr_append (cleanStr_lit "#") ?_)
        simp only [isSingleLineClean, CleanStr, CleanChars, List.all_eq_true, Bool.and_eq_true] at hc_clean ⊢
        exact fun ch hch => ⟨(hc_clean ch hch).1.1, (hc_clean ch hch).2⟩
    have hnorm := normalizeChars_clean (joinLines (hdrLines ++ bodyLines)).toList (cleanLines_append hhdr_cl hBodySteps.1) 1 1
    have hge_len : bodyLines.length ≤ (joinLines (hdrLines ++ bodyLines)).toList.length := by
      have h1 := joinLines_length_ge (hdrLines ++ bodyLines); simp only [List.length_append] at h1; omega
    have hskip : skipTriviaNewlines (joinLines (hdrLines ++ bodyLines)).toList = skipTriviaNewlines (joinLines bodyLines).toList := by
      rcases hhdr_cases with rfl | ⟨c, hc_clean, rfl⟩; · simp
      · simpa [joinLines, String.toList_append, List.append_assoc] using skipTriviaNewlines_comment_line c (joinLines bodyLines).toList hc_clean
    have hp_full : parseDocumentFuel numApi ((joinLines (hdrLines ++ bodyLines)).toList.length + 1)
        (joinLines (hdrLines ++ bodyLines)).toList [] [] = .ok finalLoc := by
      rw [show parseDocumentFuel numApi ((joinLines (hdrLines ++ bodyLines)).toList.length + 1) (joinLines (hdrLines ++ bodyLines)).toList [] [] =
          parseDocumentFuel numApi ((joinLines (hdrLines ++ bodyLines)).toList.length + 1) (joinLines bodyLines).toList [] [] by simp only [parseDocumentFuel, hskip]]
      have hp := hBodySteps.2 [] ((joinLines (hdrLines ++ bodyLines)).toList.length + 1) (by omega)
      simp only [rootFocus, DocFocus.path, List.map_nil, List.append_nil, id] at hp; rw [hp]
      cases hd : ((joinLines (hdrLines ++ bodyLines)).toList.length + 1) - bodyLines.length with
      | zero => omega
      | succ _ => simp [parseDocumentFuel, skipTriviaNewlines, skipTriviaNewlinesAux]
    refine ⟨(entriesToTomlList finalLoc).toArray, ?_, by simpa [TomlTableEquiv] using heqv_list⟩
    unfold parseCharsWithNum; rw [hnorm]; dsimp only [bind, Except.bind]; rw [hp_full]

/-- Any rendered `TomlTable` parses back via `parseWithNum` to an equivalent `TomlTable` under valid numeric parsers. -/
theorem render_parse_roundTrip_model (numApi : NumParseApi)
    (hInt : ∀ tok n, parseInt64Model tok = .ok n → numApi.parseInt64 tok = .ok n)
    (hFloat : ∀ tok f, parseFloatModel tok = .ok f → ∃ g, numApi.parseFloat tok = .ok g ∧ FloatBitMatch f g)
    (doc : TomlTable) (tape : RenderTape) (out : String) (hrender : render doc tape = some out) :
    ∃ parsed, parseWithNum numApi out = .ok parsed ∧ TomlTableEquiv doc parsed :=
  render_parse_roundTrip_chars (toCharNumApi numApi)
    ⟨fun tok n h => by simpa [toCharNumApi, String.ofList_toList] using hInt tok n h,
     fun tok f h => by simpa [toCharNumApi, String.ofList_toList] using hFloat tok f h⟩
    doc tape out hrender
end LeanSwe.Toml.Proofs
