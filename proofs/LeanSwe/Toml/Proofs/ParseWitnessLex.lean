import LeanSwe.Toml.Proofs.Core

/-!
# Lexical & Dotted-Key Parse-to-Render Completeness Witnesses

Constructs exact `Model` lexical/key witnesses (`crlfMask`, trivia strings, `LineSuffixTape`,
`KeyStyle`, `DottedKeyTape`) for every character slice accepted by `Toml.Impl` scanners.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml LeanSwe.Toml.Model LeanSwe.Toml.Impl

/-- Post-normalization character invariant: no disallowed control characters and no `'\r'`. -/
def CleanNorm (cs : List Char) : Prop :=
  (cs.all fun c => !isDisallowedControl c && c != '\r') = true

theorem cleanNorm_cons {c : Char} {cs : List Char} :
    CleanNorm (c :: cs) ↔ (isDisallowedControl c = false ∧ c ≠ '\r') ∧ CleanNorm cs := by
  simp [CleanNorm, List.all_cons, Bool.and_eq_true, bne_iff_ne]

theorem cleanNorm_append {a b : List Char} :
    CleanNorm (a ++ b) ↔ CleanNorm a ∧ CleanNorm b := by
  simp [CleanNorm, List.all_append, Bool.and_eq_true]

theorem cleanNorm_of_suffix {p s cs : List Char} (h : CleanNorm cs) (heq : cs = p ++ s) :
    CleanNorm p ∧ CleanNorm s := by
  rw [heq] at h; exact cleanNorm_append.mp h

/-- Extract the exact `crlfMask` (`true` for `\r\n`, `false` for bare `\n`) from raw characters. -/
def extractCrlfMask : List Char → List Bool
  | '\r' :: '\n' :: rest => true :: extractCrlfMask rest
  | '\n' :: rest => false :: extractCrlfMask rest
  | _ :: rest => extractCrlfMask rest
  | [] => []

private theorem expandNewlines_cons_nonNl {mask : List Bool} {c : Char} {cs : List Char} (hnl : c ≠ '\n') :
    expandNewlines mask (c :: cs) = (expandNewlines mask cs >>= fun r => some (c :: r)) := by
  cases mask with
  | nil => (conv => lhs; unfold expandNewlines); split <;> simp_all
  | cons b bs => cases b <;> ((conv => lhs; unfold expandNewlines); split <;> simp_all)

private theorem normalizeCharsAux_witness :
    ∀ (cs : List Char) (line col : Nat) (acc out : List Char),
      normalizeCharsAux line col acc cs = .ok out →
      ∃ tail, out = acc.reverse ++ tail ∧ CleanNorm tail ∧
        expandNewlines (extractCrlfMask cs) tail = some cs
  | [], _, _, acc, out, h => by
    obtain rfl := Except.ok.inj h; exact ⟨[], by simp, rfl, rfl⟩
  | c :: rest, line, col, acc, out, h => by
    by_cases hcr : c = '\r'
    · subst hcr
      cases rest with
      | nil => nomatch h
      | cons c2 r2 =>
        by_cases hnl : c2 = '\n'
        · subst hnl; unfold normalizeCharsAux at h
          obtain ⟨tail', hout, hcl, hexp⟩ := normalizeCharsAux_witness r2 (line + 1) 1 ('\n' :: acc) out h
          exact ⟨'\n' :: tail', by simpa [List.reverse_cons, List.append_assoc] using hout,
            cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩, hcl⟩, by simp [extractCrlfMask, expandNewlines, hexp]⟩
        · have herr : normalizeCharsAux line col acc ('\r' :: c2 :: r2) =
              .error (mkErr .invalidUtf8OrControl "bare carriage return is not allowed in TOML" (some line) (some col)) := by
            (conv => lhs; unfold normalizeCharsAux)
            split
            · contradiction
            · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hnl
            · rfl
            · rename_i _ heq; nomatch (List.cons.inj heq).1
            · rename_i _ hnr _ heq; exact False.elim (hnr (List.cons.inj heq).1.symm)
          rw [herr] at h; nomatch h
    · by_cases hnl : c = '\n'
      · subst hnl
        have hstep : normalizeCharsAux line col acc ('\n' :: rest) =
            normalizeCharsAux (line + 1) 1 ('\n' :: acc) rest := rfl
        rw [hstep] at h
        obtain ⟨tail', hout, hcl, hexp⟩ := normalizeCharsAux_witness rest (line + 1) 1 ('\n' :: acc) out h
        have hm : extractCrlfMask ('\n' :: rest) = false :: extractCrlfMask rest := rfl
        exact ⟨'\n' :: tail', by simpa [List.reverse_cons, List.append_assoc] using hout,
          cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩, hcl⟩, by rw [hm]; simp [expandNewlines, hexp]⟩
      · have hstep : normalizeCharsAux line col acc (c :: rest) =
            (if isDisallowedControl c then
              .error (mkErr .invalidUtf8OrControl "disallowed control character in TOML input" (some line) (some col))
             else normalizeCharsAux line (col + 1) (c :: acc) rest) := by
          (conv => lhs; unfold normalizeCharsAux); split <;> (subst_vars; simp_all)
          rfl
        rw [hstep] at h
        cases hctrl : isDisallowedControl c
        · rw [hctrl] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨tail', hout, hcl, hexp⟩ := normalizeCharsAux_witness rest line (col + 1) (c :: acc) out h
          have hm : extractCrlfMask (c :: rest) = extractCrlfMask rest := by
            (conv => lhs; unfold extractCrlfMask); split <;> (subst_vars; simp_all)
          exact ⟨c :: tail', by simpa [List.reverse_cons, List.append_assoc] using hout,
            cleanNorm_cons.mpr ⟨⟨hctrl, hcr⟩, hcl⟩, by rw [hm, expandNewlines_cons_nonNl hnl]; simp [hexp]⟩
        · rw [hctrl] at h; nomatch h

/-- `normalizeChars` produces `CleanNorm` characters and an exact `expandNewlines` mask witness. -/
theorem normalizeChars_witness {rawCs normCs : List Char}
    (h : normalizeChars 1 1 rawCs = .ok normCs) :
    CleanNorm normCs ∧ expandNewlines (extractCrlfMask rawCs) normCs = some rawCs := by
  obtain ⟨tail, hout, hcl, hexp⟩ := normalizeCharsAux_witness rawCs 1 1 [] normCs h
  simp only [List.reverse_nil, List.nil_append] at hout; subst hout; exact ⟨hcl, hexp⟩

/-- Split leading horizontal whitespace (`' '` and `'\t'`) from `cs`. -/
def takeHorizPrefix : List Char → List Char
  | c :: rest => if isHorizWs c then c :: takeHorizPrefix rest else []
  | [] => []

theorem skipHorizWs_witness (cs : List Char) :
    cs = takeHorizPrefix cs ++ skipHorizWs cs ∧
      isHorizWsStr (String.ofList (takeHorizPrefix cs)) = true := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c rest ih =>
    unfold takeHorizPrefix skipHorizWs
    by_cases hw : isHorizWs c = true
    · have hmw : isModelHorizWs c = true := hw
      simp only [hw, ↓reduceIte, List.cons_append]
      refine ⟨congrArg (c :: ·) ih.1, ?_⟩
      unfold isHorizWsStr at ih ⊢; rw [String.toList_ofList] at ih ⊢; simp [hmw, ih.2]
    · simp [hw, isHorizWsStr]

theorem isHorizWsStr_append {a b : String} (ha : isHorizWsStr a = true) (hb : isHorizWsStr b = true) :
    isHorizWsStr (a ++ b) = true := by
  unfold isHorizWsStr at *; simp [String.toList_append, List.all_append, ha, hb]

/-- Split leading horizontal whitespace and newlines from `cs`. -/
def takeHorizAndNlPrefix : List Char → List Char
  | c :: rest => if isHorizWs c || c == '\n' then c :: takeHorizAndNlPrefix rest else []
  | [] => []

theorem skipHorizAndNl_witness (cs : List Char) :
    cs = takeHorizAndNlPrefix cs ++ skipHorizAndNl cs ∧
      isHorizAndNlStr (String.ofList (takeHorizAndNlPrefix cs)) = true ∧
      (∀ c r, skipHorizAndNl cs = c :: r → isModelHorizWs c = false ∧ c ≠ '\n') := by
  induction cs with
  | nil => exact ⟨rfl, by decide, fun _ _ h => nomatch h⟩
  | cons c rest ih =>
    by_cases hw : (isHorizWs c || c == '\n') = true
    · have hmw : (isModelHorizWs c || c == '\n') = true := hw
      have ht : takeHorizAndNlPrefix (c :: rest) = c :: takeHorizAndNlPrefix rest := by simp [takeHorizAndNlPrefix, hw]
      have hs : skipHorizAndNl (c :: rest) = skipHorizAndNl rest := by simp [skipHorizAndNl, hw]
      rw [ht, hs, List.cons_append]
      refine ⟨congrArg (c :: ·) ih.1, ?_, ih.2.2⟩
      unfold isHorizAndNlStr at ih ⊢; rw [String.toList_ofList] at ih ⊢; simp [hmw, ih.2.1]
    · have ht : takeHorizAndNlPrefix (c :: rest) = [] := by simp [takeHorizAndNlPrefix, hw]
      have hs : skipHorizAndNl (c :: rest) = c :: rest := by simp [skipHorizAndNl, hw]
      rw [ht, hs]
      refine ⟨rfl, by decide, fun c' r' heq => ?_⟩
      obtain ⟨rfl, _⟩ := List.cons.inj heq
      simp only [Bool.or_eq_true, not_or, beq_iff_eq] at hw
      exact ⟨Bool.eq_false_iff.mpr hw.1, hw.2⟩

theorem skipTriviaNewlinesAux_eof_witness :
    ∀ (b : Bool) (cs : List Char),
      CleanNorm cs → skipTriviaNewlinesAux b cs = [] → checkEofTriviaAux b cs = true := by
  intro b cs
  induction cs generalizing b with
  | nil => intro _ _; rfl
  | cons c rest ih =>
    intro hcl hskip
    obtain ⟨⟨hctrl, hcr⟩, hcl_rest⟩ := cleanNorm_cons.mp hcl
    by_cases hnl : c = '\n'
    · subst hnl
      have hs' : skipTriviaNewlinesAux false rest = [] := by simpa [skipTriviaNewlinesAux] using hskip
      simpa [checkEofTriviaAux] using ih false hcl_rest hs'
    · have hs_eq : skipTriviaNewlinesAux b (c :: rest) =
          (if b then skipTriviaNewlinesAux true rest
           else if isHorizWs c then skipTriviaNewlinesAux false rest
           else if c == '#' then skipTriviaNewlinesAux true rest else c :: rest) := by
        (conv => lhs; unfold skipTriviaNewlinesAux); split <;> simp_all
      have hc_eq : checkEofTriviaAux b (c :: rest) =
          (if b then !isDisallowedControl c && c != '\r' && checkEofTriviaAux true rest
           else if isModelHorizWs c then checkEofTriviaAux false rest
           else if c == '#' then checkEofTriviaAux true rest else false) := by
        cases b <;> ((conv => lhs; unfold checkEofTriviaAux); split <;> simp_all)
      rw [hs_eq] at hskip; rw [hc_eq]
      cases b with
      | true =>
        simp only [↓reduceIte] at hskip ⊢
        simp [hctrl, bne_iff_ne.mpr hcr, ih true hcl_rest hskip]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hskip ⊢
        change (if isModelHorizWs c then _ else _) = [] at hskip
        split at hskip
        · rename_i hw; simp [hw, ih false hcl_rest hskip]
        · rename_i hw; simp only [hw, Bool.false_eq_true, ↓reduceIte]
          split at hskip
          · rename_i hh; simp [hh, ih true hcl_rest hskip]
          · nomatch hskip

theorem skipTriviaNewlinesAux_cons_witness :
    ∀ (b : Bool) (cs : List Char) {c0 : Char} {r0 : List Char},
      CleanNorm cs → skipTriviaNewlinesAux b cs = c0 :: r0 →
      ∃ pre, cs = pre ++ (c0 :: r0) ∧ checkClosedTriviaAux b pre = true := by
  intro b cs
  induction cs generalizing b with
  | nil => intro _ _ _ h; simp [skipTriviaNewlinesAux] at h
  | cons c rest ih =>
    intro c0 r0 hcl hskip
    obtain ⟨⟨hctrl, hcr⟩, hcl_rest⟩ := cleanNorm_cons.mp hcl
    by_cases hnl : c = '\n'
    · subst hnl
      have hs' : skipTriviaNewlinesAux false rest = c0 :: r0 := by simpa [skipTriviaNewlinesAux] using hskip
      obtain ⟨pre, hrest, hpre⟩ := ih false hcl_rest hs'
      exact ⟨'\n' :: pre, by simp [hrest], by simpa [checkClosedTriviaAux] using hpre⟩
    · have hs_eq : skipTriviaNewlinesAux b (c :: rest) =
          (if b then skipTriviaNewlinesAux true rest
           else if isHorizWs c then skipTriviaNewlinesAux false rest
           else if c == '#' then skipTriviaNewlinesAux true rest else c :: rest) := by
        (conv => lhs; unfold skipTriviaNewlinesAux); split <;> simp_all
      rw [hs_eq] at hskip
      cases b with
      | true =>
        simp only [↓reduceIte] at hskip
        obtain ⟨pre, hrest, hpre⟩ := ih true hcl_rest hskip
        have hc_eq : checkClosedTriviaAux true (c :: pre) =
            (!isDisallowedControl c && c != '\r' && checkClosedTriviaAux true pre) := by
          (conv => lhs; unfold checkClosedTriviaAux); split <;> simp_all
        exact ⟨c :: pre, by simp [hrest], by rw [hc_eq]; simp [hctrl, bne_iff_ne.mpr hcr, hpre]⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hskip
        change (if isModelHorizWs c then _ else _) = c0 :: r0 at hskip
        by_cases hw : isModelHorizWs c = true
        · simp only [hw, ↓reduceIte] at hskip
          obtain ⟨pre, hrest, hpre⟩ := ih false hcl_rest hskip
          have hc_eq : checkClosedTriviaAux false (c :: pre) = checkClosedTriviaAux false pre := by
            (conv => lhs; unfold checkClosedTriviaAux); split <;> simp_all
          exact ⟨c :: pre, by simp [hrest], by rw [hc_eq]; exact hpre⟩
        · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hskip
          by_cases hh : (c == '#') = true
          · simp only [hh, ↓reduceIte] at hskip
            obtain ⟨pre, hrest, hpre⟩ := ih true hcl_rest hskip
            exact ⟨c :: pre, by simp [hrest], by rw [eq_of_beq hh]; exact hpre⟩
          · simp only [hh, Bool.false_eq_true, ↓reduceIte] at hskip
            obtain ⟨rfl, rfl⟩ := List.cons.inj hskip; exact ⟨[], rfl, rfl⟩

private def takeCommentBody : List Char → List Char
  | [] => []
  | '\n' :: _ => []
  | c :: rest => c :: takeCommentBody rest

private theorem skipCommentBody_witness :
    ∀ cs : List Char, CleanNorm cs →
      cs = takeCommentBody cs ++ skipCommentBody cs ∧
        isSingleLineClean (String.ofList (takeCommentBody cs)) = true ∧
        (skipCommentBody cs = [] ∨ ∃ r, skipCommentBody cs = '\n' :: r)
  | [], _ => ⟨rfl, rfl, Or.inl rfl⟩
  | c :: rest, hcl => by
    obtain ⟨⟨hctrl, hcr⟩, hcl_rest⟩ := cleanNorm_cons.mp hcl
    by_cases hnl : c = '\n'
    · subst hnl; exact ⟨rfl, rfl, Or.inr ⟨rest, rfl⟩⟩
    · have ht_eq : takeCommentBody (c :: rest) = c :: takeCommentBody rest := by
        (conv => lhs; unfold takeCommentBody); split <;> simp_all
      have hs_eq : skipCommentBody (c :: rest) = skipCommentBody rest := by
        (conv => lhs; unfold skipCommentBody); split <;> simp_all
      obtain ⟨heq, hclean, hend⟩ := skipCommentBody_witness rest hcl_rest
      refine ⟨by rw [ht_eq, hs_eq, List.cons_append, ← heq], ?_, by rw [hs_eq]; exact hend⟩
      unfold isSingleLineClean at hclean ⊢; rw [String.toList_ofList] at hclean ⊢
      rw [ht_eq, List.all_cons]; simp [hctrl, bne_iff_ne.mpr hnl, bne_iff_ne.mpr hcr, hclean]

/-- `consumeStatementEnd` produces a `LineSuffixTape` and an explicit `hasNl : Bool` delimiter witness. -/
theorem consumeStatementEnd_witness {cs nextCs : List Char}
    (hcl : CleanNorm cs) (h : consumeStatementEnd cs = .ok nextCs) :
    ∃ (suf : LineSuffixTape) (rsuf : String) (hasNl : Bool),
      renderLineSuffix suf = some rsuf ∧
      (if hasNl then cs = rsuf.toList ++ '\n' :: nextCs else nextCs = [] ∧ cs = rsuf.toList) := by
  unfold consumeStatementEnd at h
  obtain ⟨hws_eq, hws_ok⟩ := skipHorizWs_witness cs
  have hcl_afterWs : CleanNorm (skipHorizWs cs) := (cleanNorm_of_suffix hcl hws_eq).2
  cases hsw : skipHorizWs cs with
  | nil =>
    unfold skipHorizAndComment at h; rw [hsw] at h hws_eq; simp only [Except.ok.injEq] at h; subst h
    refine ⟨{ ws := String.ofList (takeHorizPrefix cs), comment := none },
      String.ofList (takeHorizPrefix cs), false, by simp [renderLineSuffix, hws_ok], rfl, ?_⟩
    exact Eq.trans hws_eq (by simp [String.toList_ofList])
  | cons c0 r0 =>
    rw [hsw] at hws_eq hcl_afterWs
    by_cases hhash : c0 = '#'
    · subst hhash
      have hshc : skipHorizAndComment cs = skipCommentBody r0 := by unfold skipHorizAndComment; rw [hsw]; rfl
      rw [hshc] at h
      have hcl_r0 := (cleanNorm_cons.mp hcl_afterWs).2
      obtain ⟨hcb_eq, hcb_clean, hcb_end⟩ := skipCommentBody_witness r0 hcl_r0
      let suf : LineSuffixTape :=
        { ws := String.ofList (takeHorizPrefix cs), comment := some (String.ofList (takeCommentBody r0)) }
      let rsuf := String.ofList (takeHorizPrefix cs) ++ "#" ++ String.ofList (takeCommentBody r0)
      have hrsuf : renderLineSuffix suf = some rsuf := by simp [renderLineSuffix, suf, rsuf, hws_ok, hcb_clean]
      rcases hcb_end with hnil | ⟨afterNl, hcons⟩
      · rw [hnil] at h hcb_eq; obtain rfl := (Except.ok.inj h).symm
        refine ⟨suf, rsuf, false, hrsuf, rfl, Eq.trans hws_eq ?_⟩
        rw [congrArg ('#' :: ·) hcb_eq]
        simp [rsuf, String.toList_append, String.toList_ofList, show ("#" : String).toList = ['#'] from rfl]
      · rw [hcons] at h hcb_eq; obtain rfl := (Except.ok.inj h).symm
        refine ⟨suf, rsuf, true, hrsuf, Eq.trans hws_eq ?_⟩
        rw [congrArg ('#' :: ·) hcb_eq]
        simp [rsuf, String.toList_append, String.toList_ofList, show ("#" : String).toList = ['#'] from rfl, List.append_assoc]
    · have hshc : skipHorizAndComment cs = c0 :: r0 := by
        unfold skipHorizAndComment; rw [hsw]
        split
        · rename_i rest heq; exact absurd (List.cons.inj heq).1 hhash
        · rfl
      rw [hshc] at h
      by_cases hnl : c0 = '\n'
      · subst hnl; obtain rfl := (Except.ok.inj h).symm
        refine ⟨{ ws := String.ofList (takeHorizPrefix cs), comment := none },
          String.ofList (takeHorizPrefix cs), true, by simp [renderLineSuffix, hws_ok], ?_⟩
        exact Eq.trans hws_eq (by simp [String.toList_ofList])
      · split at h
        · nomatch ‹c0 :: r0 = []›
        · rename_i rest heq; exact absurd (List.cons.inj heq).1 hnl
        · nomatch h

private theorem takeHexDigits_step {k acc : Nat} {cs : List Char} {out : Nat × List Char}
    (h : takeHexDigits (k + 1) acc cs = some out) :
    ∃ x rest d, cs = x :: rest ∧ hexValModel? x = some d ∧ takeHexDigits k (acc * 16 + d) rest = some out := by
  cases cs with
  | nil => nomatch h
  | cons x rest =>
    unfold takeHexDigits at h
    cases hx : hexVal? x <;> rw [hx] at h
    · nomatch h
    · exact ⟨x, rest, _, rfl, hx, h⟩

/-- `parseBasicEscape` produces an exact `BasicEscapeAtom` witness. -/
theorem parseBasicEscape_witness {cs afterEsc : List Char} {ch : Char}
    (h : parseBasicEscape cs = .ok (ch, afterEsc)) :
    ∃ esc : BasicEscapeAtom,
      decodeBasicEscape esc = some ch ∧ '\\' :: cs = renderBasicEscapeChars esc ++ afterEsc := by
  unfold parseBasicEscape at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨.backspace, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨.tab, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨.linefeed, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨.formfeed, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨.carriageReturn, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨.quote, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨.backslash, rfl, rfl⟩
  · rename_i r; unfold parseUnicodeHex at h
    cases htk : takeHexDigits 4 0 r with
    | none => rw [htk] at h; nomatch h
    | some pair =>
      rcases pair with ⟨code, rem⟩; rw [htk] at h; dsimp only at h
      split at h <;> try (simp at h; done)
      rename_i hnotbad
      obtain ⟨x1, r1, d1, rfl, hx1, h1⟩ := takeHexDigits_step htk
      obtain ⟨x2, r2, d2, rfl, hx2, h2⟩ := takeHexDigits_step h1
      obtain ⟨x3, r3, d3, rfl, hx3, h3⟩ := takeHexDigits_step h2
      obtain ⟨x4, r4, d4, rfl, hx4, h4⟩ := takeHexDigits_step h3
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h4)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨.unicode4 x1 x2 x3 x4, ?_, rfl⟩
      have hr_f := Bool.eq_false_iff.mpr hnotbad
      simp only [Nat.zero_mul, Nat.zero_add] at hr_f
      simp [decodeBasicEscape, hx1, hx2, hx3, hx4, hr_f]
  · rename_i r; unfold parseUnicodeHex at h
    cases htk : takeHexDigits 8 0 r with
    | none => rw [htk] at h; nomatch h
    | some pair =>
      rcases pair with ⟨code, rem⟩; rw [htk] at h; dsimp only at h
      split at h <;> try (simp at h; done)
      rename_i hnotbad
      obtain ⟨x1, r1, d1, rfl, hx1, h1⟩ := takeHexDigits_step htk
      obtain ⟨x2, r2, d2, rfl, hx2, h2⟩ := takeHexDigits_step h1
      obtain ⟨x3, r3, d3, rfl, hx3, h3⟩ := takeHexDigits_step h2
      obtain ⟨x4, r4, d4, rfl, hx4, h4⟩ := takeHexDigits_step h3
      obtain ⟨x5, r5, d5, rfl, hx5, h5⟩ := takeHexDigits_step h4
      obtain ⟨x6, r6, d6, rfl, hx6, h6⟩ := takeHexDigits_step h5
      obtain ⟨x7, r7, d7, rfl, hx7, h7⟩ := takeHexDigits_step h6
      obtain ⟨x8, r8, d8, rfl, hx8, h8⟩ := takeHexDigits_step h7
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h8)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨.unicode8 x1 x2 x3 x4 x5 x6 x7 x8, ?_, rfl⟩
      have hr_f := Bool.eq_false_iff.mpr hnotbad
      simp only [Nat.zero_mul, Nat.zero_add] at hr_f
      simp [decodeBasicEscape, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hr_f]
  · nomatch h

private theorem parseBasicStringBodyFuel_witness (fuel : Nat) :
    ∀ (acc cs : List Char) {s : String} {after : List Char},
      CleanNorm cs → parseBasicStringBodyFuel fuel acc cs = .ok (s, after) →
      ∃ csTail atoms enc,
        s = String.ofList (acc.reverse ++ csTail) ∧
        renderBasicAtoms csTail atoms = some enc ∧
        cs = enc ++ '"' :: after := by
  induction fuel with
  | zero => intro _ _ _ _ _ h; nomatch h
  | succ fuel ih =>
    intro acc cs s after hcl h
    cases cs with
    | nil => nomatch h
    | cons c rest =>
      by_cases hnl : c = '\n'
      · subst hnl; nomatch h
      · by_cases hq : c = '"'
        · subst hq
          have hstep : parseBasicStringBodyFuel (fuel + 1) acc ('"' :: rest) =
              .ok (String.ofList acc.reverse, rest) := rfl
          rw [hstep] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
          exact ⟨[], [], [], by simp, rfl, rfl⟩
        · by_cases hbs : c = '\\'
          · subst hbs
            have hstep : parseBasicStringBodyFuel (fuel + 1) acc ('\\' :: rest) =
                (parseBasicEscape rest >>= fun (ch, afterEsc) => parseBasicStringBodyFuel fuel (ch :: acc) afterEsc) := rfl
            rw [hstep] at h; simp only [bind, Except.bind] at h
            cases he : parseBasicEscape rest with
            | error _ => rw [he] at h; nomatch h
            | ok pair =>
              rcases pair with ⟨ch, afterEsc⟩; rw [he] at h; dsimp only at h
              obtain ⟨esc, hdec, hesc_cs⟩ := parseBasicEscape_witness he
              have hcl_after : CleanNorm afterEsc := (cleanNorm_of_suffix hcl hesc_cs).2
              obtain ⟨csTail, atoms, enc, hs, hrend, hafter_eq⟩ := ih (ch :: acc) afterEsc hcl_after h
              refine ⟨ch :: csTail, .escape esc :: atoms, renderBasicEscapeChars esc ++ enc,
                by simpa [List.reverse_cons, List.append_assoc] using hs,
                by simp [renderBasicAtoms, hdec, hrend], ?_⟩
              rw [hafter_eq] at hesc_cs
              have hcons : '\\' :: rest = '\\' :: ((renderBasicEscapeChars esc).tail ++ (enc ++ '"' :: after)) := by
                cases esc <;> simpa [renderBasicEscapeChars, List.cons_append] using hesc_cs
              obtain ⟨_, rfl⟩ := List.cons.inj hcons
              cases esc <;> simp [renderBasicEscapeChars]
          · have hstep : parseBasicStringBodyFuel (fuel + 1) acc (c :: rest) =
                parseBasicStringBodyFuel fuel (c :: acc) rest := by
              (conv => lhs; unfold parseBasicStringBodyFuel); split <;> simp_all
            rw [hstep] at h
            obtain ⟨⟨hctrl, hcr⟩, hcl_rest⟩ := cleanNorm_cons.mp hcl
            obtain ⟨csTail, atoms, enc, hs, hrend, hrest_eq⟩ := ih (c :: acc) rest hcl_rest h
            refine ⟨c :: csTail, .plain :: atoms, c :: enc,
              by simpa [List.reverse_cons, List.append_assoc] using hs, ?_, by simp [hrest_eq]⟩
            simp [renderBasicAtoms, bne_iff_ne.mpr hq, bne_iff_ne.mpr hbs, bne_iff_ne.mpr hnl,
              bne_iff_ne.mpr hcr, hctrl, hrend]

theorem parseBasicStringBody_witness {cs after : List Char} {s : String}
    (hcl : CleanNorm cs) (h : parseBasicStringBody cs = .ok (s, after)) :
    ∃ atoms enc, renderBasicAtoms s.toList atoms = some enc ∧ cs = enc ++ '"' :: after := by
  obtain ⟨csTail, atoms, enc, hs, hrend, hcs⟩ := parseBasicStringBodyFuel_witness (cs.length + 1) [] cs hcl h
  simp only [List.reverse_nil, List.nil_append] at hs
  subst hs; rw [String.toList_ofList]; exact ⟨atoms, enc, hrend, hcs⟩

private theorem parseLiteralStringBody_aux :
    ∀ (cs acc : List Char) {s : String} {after : List Char},
      CleanNorm cs → parseLiteralStringBody acc cs = .ok (s, after) →
      ∃ csTail, s = String.ofList (acc.reverse ++ csTail) ∧
        cs = csTail ++ '\'' :: after ∧
        (csTail.all fun c => (!isDisallowedControl c && c != '\n' && c != '\r') && c != '\'') = true
  | [], _, _, _, _, h => nomatch h
  | c :: rest, acc, s, after, hcl, h => by
    by_cases hnl : c = '\n'
    · subst hnl; nomatch h
    · by_cases hq : c = '\''
      · subst hq
        have hstep : parseLiteralStringBody acc ('\'' :: rest) = .ok (String.ofList acc.reverse, rest) := rfl
        rw [hstep] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨[], by simp, rfl, rfl⟩
      · have hstep : parseLiteralStringBody acc (c :: rest) = parseLiteralStringBody (c :: acc) rest := by
          (conv => lhs; unfold parseLiteralStringBody); split <;> simp_all
        rw [hstep] at h
        obtain ⟨⟨hctrl, hcr⟩, hcl_rest⟩ := cleanNorm_cons.mp hcl
        obtain ⟨csTail, hs, hcs, hall⟩ := parseLiteralStringBody_aux rest (c :: acc) hcl_rest h
        refine ⟨c :: csTail, by simpa [List.reverse_cons, List.append_assoc] using hs, by simp [hcs], ?_⟩
        simp [List.all_cons, hctrl, bne_iff_ne.mpr hnl, bne_iff_ne.mpr hcr, bne_iff_ne.mpr hq, hall]

theorem parseLiteralStringBody_witness {cs after : List Char} {s : String}
    (hcl : CleanNorm cs) (h : parseLiteralStringBody [] cs = .ok (s, after)) :
    isSingleLineClean s = true ∧ s.contains '\'' = false ∧ cs = s.toList ++ '\'' :: after := by
  obtain ⟨csTail, hs, hcs, hall⟩ := parseLiteralStringBody_aux cs [] hcl h
  simp only [List.reverse_nil, List.nil_append] at hs; subst hs
  have hc1 : isSingleLineClean (String.ofList csTail) = true := by
    unfold isSingleLineClean; rw [String.toList_ofList]
    exact List.all_eq_true.mpr fun c hc => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hall c hc)).1
  have hc2 : (String.ofList csTail).contains '\'' = false :=
    Bool.eq_false_iff.mpr fun hm => by
      rw [String.contains_char_eq, decide_eq_true_eq, String.toList_ofList] at hm
      exact bne_iff_ne.mp ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hall '\'' hm)).2 rfl
  exact ⟨hc1, hc2, by simpa [String.toList_ofList] using hcs⟩

private theorem takeBareKeyChars_witness :
    ∀ (cs acc : List Char),
      ∃ ksTail,
        (takeBareKeyChars acc cs).1 = acc.reverse ++ ksTail ∧
        cs = ksTail ++ (takeBareKeyChars acc cs).2 ∧
        ksTail.all isBareKeyChar = true
  | [], acc => ⟨[], by simp [takeBareKeyChars], rfl, rfl⟩
  | c :: rest, acc => by
    unfold takeBareKeyChars
    by_cases hbk : isBareKeyChar c = true
    · simp only [isBareKeyCharImpl_eq, hbk, ↓reduceIte]
      obtain ⟨ksTail, h1, h2, h3⟩ := takeBareKeyChars_witness rest (c :: acc)
      exact ⟨c :: ksTail, by simpa [List.reverse_cons, List.append_assoc] using h1,
        congrArg (c :: ·) h2, by simp [hbk, h3]⟩
    · simp [hbk]

/-- `parseKeySegment` produces a `KeyStyle` rendering to the consumed prefix. -/
theorem parseKeySegment_witness {cs after : List Char} {k : String}
    (hcl : CleanNorm cs) (h : parseKeySegment cs = .ok (k, after)) :
    ∃ style rk, renderKey k style = some rk ∧ cs = rk.toList ++ after := by
  unfold parseKeySegment at h
  split at h
  · nomatch h
  · nomatch h
  · obtain ⟨atoms, enc, hrend, hrest⟩ := parseBasicStringBody_witness (cleanNorm_cons.mp hcl).2 h
    refine ⟨.basic (some atoms), "\"" ++ String.ofList enc ++ "\"", by simp [renderKey, hrend], ?_⟩
    exact Eq.trans (congrArg ('"' :: ·) hrest) (by simp [String.toList_append, String.toList_ofList, List.append_assoc])
  · obtain ⟨hclean, hnq, hrest⟩ := parseLiteralStringBody_witness (cleanNorm_cons.mp hcl).2 h
    refine ⟨.literal, "'" ++ k ++ "'", by simp [renderKey, hclean, hnq], ?_⟩
    exact Eq.trans (congrArg ('\'' :: ·) hrest) (by simp [String.toList_append, List.append_assoc])
  · obtain ⟨ksTail, hks_eq, hcs_eq, hall⟩ := takeBareKeyChars_witness cs []
    rcases htk : takeBareKeyChars [] cs with ⟨ks, rem⟩
    rw [htk] at hks_eq hcs_eq h; dsimp only at hks_eq hcs_eq h
    simp only [List.reverse_nil, List.nil_append] at hks_eq; subst hks_eq
    split at h
    · nomatch h
    · rename_i hne
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have hne_str : (!(String.ofList ks).isEmpty) = true := by
        cases ks with | nil => simp at hne | cons _ _ => simp [String.ext_iff]
      refine ⟨.bare, String.ofList ks, ?_, by simpa [String.toList_ofList] using hcs_eq⟩
      simp [renderKey, isValidBareKey, hne_str, String.toList_ofList, hall]

private theorem parseDottedKeyFuel_witness (fuel : Nat) :
    ∀ {cs after : List Char} {path : List String},
      CleanNorm cs → parseDottedKeyFuel fuel cs = .ok (path, after) →
      ∃ dk rdk wsTrail,
        dk.path = path ∧ renderDottedKey dk = some rdk ∧
        isHorizWsStr wsTrail = true ∧ cs = rdk.toList ++ wsTrail.toList ++ after := by
  induction fuel with
  | zero => intro _ _ _ _ h; nomatch h
  | succ fuel ih =>
    intro cs after path hcl h
    unfold parseDottedKeyFuel at h
    simp only [bind, Except.bind] at h
    cases hk : parseKeySegment cs with
    | error _ => rw [hk] at h; nomatch h
    | ok pair =>
      rcases pair with ⟨k, r1⟩; rw [hk] at h; dsimp only at h
      obtain ⟨st0, rk0, hrk0, hcs_eq⟩ := parseKeySegment_witness hcl hk
      have hcl_r1 : CleanNorm r1 := (cleanNorm_of_suffix hcl hcs_eq).2
      obtain ⟨hr1_eq, hws1_ok⟩ := skipHorizWs_witness r1
      have hcl_r2 : CleanNorm (skipHorizWs r1) := (cleanNorm_of_suffix hcl_r1 hr1_eq).2
      cases hr2 : skipHorizWs r1 with
      | nil =>
        rw [hr2] at h hr1_eq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
        refine ⟨{ firstKey := k, firstStyle := st0, rest := [] }, rk0, String.ofList (takeHorizPrefix r1),
          rfl, by simp [renderDottedKey, renderDottedKeyCont, hrk0], hws1_ok, ?_⟩
        exact Eq.trans hcs_eq (by rw [congrArg (rk0.toList ++ ·) hr1_eq]; simp [String.toList_ofList])
      | cons c2 r3 =>
        rw [hr2] at h hr1_eq hcl_r2
        by_cases hdot : c2 = '.'
        · subst hdot
          split at h
          · rename_i r3' heq_dot
            obtain ⟨_, rfl⟩ := List.cons.inj heq_dot
            have hcl_r3 : CleanNorm r3 := (cleanNorm_cons.mp hcl_r2).2
            obtain ⟨hr3_eq, hws3_ok⟩ := skipHorizWs_witness r3
            have hcl_s3 : CleanNorm (skipHorizWs r3) := (cleanNorm_of_suffix hcl_r3 hr3_eq).2
            cases hrec : parseDottedKeyFuel fuel (skipHorizWs r3) with
            | error _ => rw [hrec] at h; nomatch h
            | ok pair2 =>
              rcases pair2 with ⟨restKeys, r4⟩; rw [hrec] at h; dsimp only at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨dkNext, rdkNext, wsTrail, hdkn_p, hdkn_r, hws_tr, hs3_eq⟩ := ih hcl_s3 hrec
              simp only [renderDottedKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hdkn_r
              rcases hdkn_r with ⟨rkNext0, hrkNext0, contNext, hcontNext, rfl⟩
              let seg0 : DottedSegCont :=
                { wsBeforeDot := String.ofList (takeHorizPrefix r1)
                , wsAfterDot := String.ofList (takeHorizPrefix r3)
                , key := dkNext.firstKey
                , style := dkNext.firstStyle }
              let dkFull : DottedKeyTape :=
                { firstKey := k, firstStyle := st0, rest := seg0 :: dkNext.rest }
              let contFull := seg0.wsBeforeDot ++ "." ++ seg0.wsAfterDot ++ rkNext0 ++ contNext
              refine ⟨dkFull, rk0 ++ contFull, wsTrail, by simp [dkFull, DottedKeyTape.path, seg0, ← hdkn_p],
                ?_, hws_tr, ?_⟩
              · simp [renderDottedKey, dkFull, hrk0, renderDottedKeyCont, seg0, hws1_ok, hws3_ok,
                  hrkNext0, hcontNext, contFull, String.append_assoc]
              · calc cs = rk0.toList ++ r1 := hcs_eq
                  _ = rk0.toList ++ (takeHorizPrefix r1 ++ '.' :: r3) := congrArg (rk0.toList ++ ·) hr1_eq
                  _ = rk0.toList ++ (takeHorizPrefix r1 ++ '.' :: (takeHorizPrefix r3 ++ ((rkNext0 ++ contNext).toList ++ wsTrail.toList ++ r4))) := by
                    congr 3; exact Eq.trans hr3_eq (congrArg (takeHorizPrefix r3 ++ ·) hs3_eq)
                  _ = (rk0 ++ contFull).toList ++ wsTrail.toList ++ r4 := by
                    simp [contFull, seg0, String.toList_append, String.toList_ofList,
                      show ("." : String).toList = ['.'] from rfl, List.append_assoc]
          · rename_i hnotdot; exact False.elim (hnotdot r3 rfl)
        · split at h
          · rename_i r3' heq; exact absurd (List.cons.inj heq).1 hdot
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
            refine ⟨{ firstKey := k, firstStyle := st0, rest := [] }, rk0, String.ofList (takeHorizPrefix r1),
              rfl, by simp [renderDottedKey, renderDottedKeyCont, hrk0], hws1_ok, ?_⟩
            exact Eq.trans hcs_eq (by rw [congrArg (rk0.toList ++ ·) hr1_eq]; simp [String.toList_ofList, List.append_assoc])

/-- `parseDottedKey` produces a `DottedKeyTape` and trailing horizontal whitespace matching `cs`. -/
theorem parseDottedKey_witness {cs after : List Char} {path : List String}
    (hcl : CleanNorm cs) (h : parseDottedKey cs = .ok (path, after)) :
    ∃ dk rdk wsTrail,
      dk.path = path ∧ renderDottedKey dk = some rdk ∧
      isHorizWsStr wsTrail = true ∧ cs = rdk.toList ++ wsTrail.toList ++ after :=
  parseDottedKeyFuel_witness (cs.length + 1) hcl h

end LeanSwe.Toml.Proofs
