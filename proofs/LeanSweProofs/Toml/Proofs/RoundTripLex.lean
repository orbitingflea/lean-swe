import LeanSweProofs.Toml.Proofs.ParseWitnessDoc
import LeanSweProofs.Toml.Proofs.RenderInjective

/-!
# Lexical & Escape Render-to-Parse Soundness (`RoundTripLex`)

Connects `LeanSwe.Toml.Model` whitespace/trivia/CRLF/comment/escape helpers to
`LeanSwe.Toml.Impl` scanners (`skipHorizWs`, `skipTriviaNewlines`, `takeUnquotedTokenChars`,
`normalizeChars`, `consumeStatementEnd`, and `parseBasicEscape`).
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

/-- `CleanNorm cs` is decidable on concrete character lists. -/
instance instDecidableCleanNorm (cs : List Char) : Decidable (CleanNorm cs) :=
  inferInstanceAs (Decidable ((cs.all fun c => !isDisallowedControl c && c != '\r') = true))

/-- Check whether a `TomlValue` is `.table _`. -/
def isTableVal : TomlValue → Bool
  | .table _ => true
  | _ => false

/-- `Impl.skipHorizWs` agrees with `Model.dropHoriz`. -/
theorem skipHorizWs_eq_dropHoriz : ∀ cs : List Char, skipHorizWs cs = dropHoriz cs
  | [] => rfl
  | c :: cs => by
    unfold skipHorizWs dropHoriz
    change (if isModelHorizWs c then skipHorizWs cs else c :: cs) = _
    split <;> simp [skipHorizWs_eq_dropHoriz cs]

/-- `skipHorizWs` is idempotent. -/
theorem skipHorizWs_idem : ∀ cs : List Char, skipHorizWs (skipHorizWs cs) = skipHorizWs cs
  | [] => rfl
  | c :: rest => by
    simp only [skipHorizWs]
    split
    · exact skipHorizWs_idem rest
    · rename_i hw; simp [skipHorizWs, hw]

/-- `Impl.skipHorizAndNl` agrees with `Model.dropHorizAndNl`. -/
theorem skipHorizAndNl_eq_dropHorizAndNl : ∀ cs : List Char, skipHorizAndNl cs = dropHorizAndNl cs
  | [] => rfl
  | c :: cs => by
    unfold skipHorizAndNl dropHorizAndNl
    change (if isModelHorizWs c || c == '\n' then skipHorizAndNl cs else c :: cs) = _
    split <;> simp [skipHorizAndNl_eq_dropHorizAndNl cs]

/-- `Impl.skipTriviaNewlinesAux` agrees with `Model.dropTrivia`. -/
theorem skipTriviaNewlinesAux_eq_dropTrivia :
    ∀ (b : Bool) (cs : List Char), skipTriviaNewlinesAux b cs = dropTrivia b cs := by
  intro b cs
  induction cs generalizing b with
  | nil => rfl
  | cons c rest ih =>
    by_cases hnl : c = '\n'
    · subst hnl
      cases b <;> simpa [skipTriviaNewlinesAux, dropTrivia] using ih false
    · have hs : skipTriviaNewlinesAux b (c :: rest) =
          (if b then skipTriviaNewlinesAux true rest
           else if isModelHorizWs c then skipTriviaNewlinesAux false rest
           else if c == '#' then skipTriviaNewlinesAux true rest else c :: rest) := by
        conv => lhs; unfold skipTriviaNewlinesAux
        split <;> simp_all [isHorizWs, isModelHorizWs]
      have hd : dropTrivia b (c :: rest) =
          (if b then dropTrivia true rest
           else if isModelHorizWs c then dropTrivia false rest
           else if c == '#' then dropTrivia true rest else c :: rest) := by
        cases b
        · conv => lhs; unfold dropTrivia
          split <;> simp_all
        · conv => lhs; unfold dropTrivia
          split <;> simp_all
      rw [hs, hd]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split <;> first | exact ih false | (split <;> first | exact ih true | rfl)
      · exact ih true

/-- `Impl.skipTriviaNewlines` agrees with `Model.dropTrivia false`. -/
theorem skipTriviaNewlines_eq_dropTrivia (cs : List Char) :
    skipTriviaNewlines cs = dropTrivia false cs :=
  skipTriviaNewlinesAux_eq_dropTrivia false cs

private theorem takeNonDelim_eq_takeModelNonDelim :
    ∀ (cs acc : List Char),
      takeNonDelim acc cs = (acc.reverse ++ (takeModelNonDelim cs).1, (takeModelNonDelim cs).2)
  | [], acc => by simp [takeNonDelim, takeModelNonDelim]
  | c :: cs, acc => by
    unfold takeNonDelim takeModelNonDelim
    change (if isModelDelim c then _ else _) = _
    by_cases hd : isModelDelim c = true
    · simp [hd]
    · simp [hd, takeNonDelim_eq_takeModelNonDelim cs (c :: acc), List.reverse_cons, List.append_assoc]

/-- `Impl.takeUnquotedTokenChars` agrees with `splitModelUnquoted`. -/
theorem takeUnquotedTokenChars_eq_splitModelUnquoted (cs : List Char) :
    takeUnquotedTokenChars cs = splitModelUnquoted cs := by
  unfold takeUnquotedTokenChars
  split
  · rename_i y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest
    have hcond :
        (isAsciiDigit y1 && isAsciiDigit y2 && isAsciiDigit y3 && isAsciiDigit y4 &&
         isAsciiDigit m1 && isAsciiDigit m2 && isAsciiDigit d1 && isAsciiDigit d2 &&
         isAsciiDigit h1 && isAsciiDigit h2 && isAsciiDigit min1 && isAsciiDigit min2 &&
         isAsciiDigit s1 && isAsciiDigit s2) =
        ([y1, y2, y3, y4, m1, m2, d1, d2, h1, h2, min1, min2, s1, s2].all isAsciiDigitModel) := by
      change (isAsciiDigitModel y1 && isAsciiDigitModel y2 && isAsciiDigitModel y3 && isAsciiDigitModel y4 &&
              isAsciiDigitModel m1 && isAsciiDigitModel m2 && isAsciiDigitModel d1 && isAsciiDigitModel d2 &&
              isAsciiDigitModel h1 && isAsciiDigitModel h2 && isAsciiDigitModel min1 && isAsciiDigitModel min2 &&
              isAsciiDigitModel s1 && isAsciiDigitModel s2) = _
      simp [List.all_cons, Bool.and_assoc]
    rw [splitModelUnquoted, hcond]
    cases [y1, y2, y3, y4, m1, m2, d1, d2, h1, h2, min1, min2, s1, s2].all isAsciiDigitModel <;>
      simp [takeNonDelim_eq_takeModelNonDelim]
  · rename_i rest_cs hne
    unfold splitModelUnquoted
    split
    · rename_i _ y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest
      exact False.elim (hne y1 y2 y3 y4 m1 m2 d1 d2 h1 h2 min1 min2 s1 s2 rest rfl)
    · simp [takeNonDelim_eq_takeModelNonDelim]

/-- Horizontal whitespace strings satisfy `CleanNorm`. -/
theorem cleanNorm_horizWsStr {s : String} (h : isHorizWsStr s = true) : CleanNorm s.toList := by
  apply List.all_eq_true.mpr
  intro c hc
  have hw := List.all_eq_true.mp h c hc
  simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hw
  rcases hw with rfl | rfl <;> decide

private theorem cleanNorm_closedTriviaAux :
    ∀ (b : Bool) (cs : List Char), checkClosedTriviaAux b cs = true → CleanNorm cs := by
  intro b cs
  induction cs generalizing b with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro h
    by_cases hnl : c = '\n'
    · subst hnl
      have h' : checkClosedTriviaAux false rest = true := by cases b <;> simpa [checkClosedTriviaAux] using h
      exact cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩, ih false h'⟩
    · have hc_eq : checkClosedTriviaAux b (c :: rest) =
          (if b then !isDisallowedControl c && c != '\r' && checkClosedTriviaAux true rest
           else if isModelHorizWs c then checkClosedTriviaAux false rest
           else if c == '#' then checkClosedTriviaAux true rest else false) := by
        cases b
        · conv => lhs; unfold checkClosedTriviaAux
          split <;> simp_all
        · conv => lhs; unfold checkClosedTriviaAux
          split <;> simp_all
      rw [hc_eq] at h
      cases b with
      | true =>
        simp only [↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h
        exact cleanNorm_cons.mpr ⟨⟨h.1.1, h.1.2⟩, ih true h.2⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i hw
          have hcl_c : isDisallowedControl c = false ∧ c ≠ '\r' := by
            simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hw
            rcases hw with rfl | rfl <;> decide
          exact cleanNorm_cons.mpr ⟨hcl_c, ih false h⟩
        · split at h
          · rename_i hh; rw [eq_of_beq hh]
            exact cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩, ih true h⟩
          · cases h

/-- Closed multiline trivia strings satisfy `CleanNorm`. -/
theorem cleanNorm_closedTrivia {s : String} (h : isClosedTrivia s = true) : CleanNorm s.toList :=
  cleanNorm_closedTriviaAux false s.toList h

private theorem cleanNorm_eofTriviaAux :
    ∀ (b : Bool) (cs : List Char), checkEofTriviaAux b cs = true → CleanNorm cs := by
  intro b cs
  induction cs generalizing b with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro h
    by_cases hnl : c = '\n'
    · subst hnl
      have h' : checkEofTriviaAux false rest = true := by cases b <;> simpa [checkEofTriviaAux] using h
      exact cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩, ih false h'⟩
    · have hc_eq : checkEofTriviaAux b (c :: rest) =
          (if b then !isDisallowedControl c && c != '\r' && checkEofTriviaAux true rest
           else if isModelHorizWs c then checkEofTriviaAux false rest
           else if c == '#' then checkEofTriviaAux true rest else false) := by
        cases b
        · conv => lhs; unfold checkEofTriviaAux
          split <;> simp_all
        · conv => lhs; unfold checkEofTriviaAux
          split <;> simp_all
      rw [hc_eq] at h
      cases b with
      | true =>
        simp only [↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at h
        exact cleanNorm_cons.mpr ⟨⟨h.1.1, h.1.2⟩, ih true h.2⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i hw
          have hcl_c : isDisallowedControl c = false ∧ c ≠ '\r' := by
            simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hw
            rcases hw with rfl | rfl <;> decide
          exact cleanNorm_cons.mpr ⟨hcl_c, ih false h⟩
        · split at h
          · rename_i hh; rw [eq_of_beq hh]
            exact cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩, ih true h⟩
          · cases h

/-- End-of-file trivia strings satisfy `CleanNorm`. -/
theorem cleanNorm_eofTrivia {s : String} (h : isEofTrivia s = true) : CleanNorm s.toList :=
  cleanNorm_eofTriviaAux false s.toList h

private theorem normalizeCharsAux_of_expandNewlines :
    ∀ (lfCs : List Char) (line col : Nat) (acc : List Char) (mask : List Bool) (rawCs : List Char),
      CleanNorm lfCs → expandNewlines mask lfCs = some rawCs →
      normalizeCharsAux line col acc rawCs = .ok (acc.reverse ++ lfCs)
  | [], line, col, acc, mask, rawCs, _, hexp => by
    cases mask with
    | nil =>
      simp only [expandNewlines, Option.some.injEq] at hexp; subst hexp
      simp [normalizeCharsAux]
    | cons _ _ => simp [expandNewlines] at hexp
  | c :: cs, line, col, acc, mask, rawCs, hcl, hexp => by
    obtain ⟨⟨hctrl, hcr⟩, hcl_cs⟩ := cleanNorm_cons.mp hcl
    by_cases hnl : c = '\n'
    · subst hnl
      cases mask with
      | nil =>
        simp only [expandNewlines, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hexp
        rcases hexp with ⟨rest, hrest, rfl⟩
        have hstep : normalizeCharsAux line col acc ('\n' :: rest) =
            normalizeCharsAux (line + 1) 1 ('\n' :: acc) rest := rfl
        rw [hstep, normalizeCharsAux_of_expandNewlines cs (line + 1) 1 ('\n' :: acc) [] rest hcl_cs hrest]
        simp [List.reverse_cons, List.append_assoc]
      | cons b bs =>
        cases b
        · simp only [expandNewlines, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hexp
          rcases hexp with ⟨rest, hrest, rfl⟩
          have hstep : normalizeCharsAux line col acc ('\n' :: rest) =
              normalizeCharsAux (line + 1) 1 ('\n' :: acc) rest := rfl
          rw [hstep, normalizeCharsAux_of_expandNewlines cs (line + 1) 1 ('\n' :: acc) bs rest hcl_cs hrest]
          simp [List.reverse_cons, List.append_assoc]
        · simp only [expandNewlines, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hexp
          rcases hexp with ⟨rest, hrest, rfl⟩
          have hstep : normalizeCharsAux line col acc ('\r' :: '\n' :: rest) =
              normalizeCharsAux (line + 1) 1 ('\n' :: acc) rest := rfl
          rw [hstep, normalizeCharsAux_of_expandNewlines cs (line + 1) 1 ('\n' :: acc) bs rest hcl_cs hrest]
          simp [List.reverse_cons, List.append_assoc]
    · have hexp_step : expandNewlines mask (c :: cs) = (expandNewlines mask cs >>= fun r => some (c :: r)) := by
        cases mask with
        | nil => (conv => lhs; unfold expandNewlines); split <;> simp_all
        | cons b bs => cases b <;> ((conv => lhs; unfold expandNewlines); split <;> simp_all)
      rw [hexp_step] at hexp
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hexp
      rcases hexp with ⟨rest, hrest, rfl⟩
      have hstep : normalizeCharsAux line col acc (c :: rest) =
          normalizeCharsAux line (col + 1) (c :: acc) rest := by
        conv => lhs; unfold normalizeCharsAux
        split <;> simp_all
      rw [hstep, normalizeCharsAux_of_expandNewlines cs line (col + 1) (c :: acc) mask rest hcl_cs hrest]
      simp [List.reverse_cons, List.append_assoc]

/-- `Impl.normalizeChars` recovers `lfCs` from any `expandNewlines` output on `CleanNorm lfCs`. -/
theorem normalizeChars_of_expandNewlines {mask : List Bool} {lfCs rawCs : List Char}
    (hcl : CleanNorm lfCs) (hexp : expandNewlines mask lfCs = some rawCs) :
    normalizeChars 1 1 rawCs = .ok lfCs := by
  simpa [normalizeChars] using normalizeCharsAux_of_expandNewlines lfCs 1 1 [] mask rawCs hcl hexp

/-- `Impl.consumeStatementEnd` consumes any rendered `LineSuffixTape` before `'\n'` or EOF. -/
theorem consumeStatementEnd_of_renderLineSuffix {suf : LineSuffixTape} {rsuf : String}
    (hsuf : renderLineSuffix suf = some rsuf) :
    CleanNorm rsuf.toList ∧
    (∀ nextCs, consumeStatementEnd (rsuf.toList ++ '\n' :: nextCs) = .ok nextCs) ∧
    consumeStatementEnd rsuf.toList = .ok [] := by
  unfold renderLineSuffix at hsuf
  split at hsuf <;> try (simp at hsuf; done)
  rename_i hws_not
  have hws : isHorizWsStr suf.ws = true := by cases h : isHorizWsStr suf.ws <;> simp_all
  cases hc : suf.comment with
  | none =>
    rw [hc] at hsuf; injection hsuf with hrsuf; subst hrsuf
    refine ⟨cleanNorm_horizWsStr hws, fun nextCs => ?_, ?_⟩
    · unfold consumeStatementEnd skipHorizAndComment
      rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)]
      simp
    · unfold consumeStatementEnd skipHorizAndComment
      have hd := dropHoriz_append (rem := []) hws (fun _ _ h => nomatch h)
      rw [List.append_nil] at hd
      rw [skipHorizWs_eq_dropHoriz, hd]
  | some comm =>
    rw [hc] at hsuf; dsimp only at hsuf; split at hsuf <;> try (simp at hsuf; done)
    rename_i hclean
    unfold isSingleLineClean at hclean
    injection hsuf with hrsuf; subst hrsuf
    have hcl_comm : CleanNorm comm.toList := by
      apply List.all_eq_true.mpr; intro c hcm
      have h1 := List.all_eq_true.mp hclean c hcm
      simp only [Bool.and_eq_true] at h1 ⊢
      exact ⟨h1.1.1, h1.2⟩
    have hskip_comm : ∀ (l tail : List Char),
        (l.all fun c => !isDisallowedControl c && c != '\n' && c != '\r') = true →
        skipCommentBody (l ++ tail) = skipCommentBody tail := by
      intro l tail hl; induction l with
      | nil => rfl
      | cons ch rest ih =>
        simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hl
        have hst : skipCommentBody (ch :: (rest ++ tail)) = skipCommentBody (rest ++ tail) := by
          conv => lhs; unfold skipCommentBody
          split <;> simp_all
        rw [List.cons_append, hst, ih hl.2]
    refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_horizWsStr hws, by decide⟩, hcl_comm⟩,
      fun nextCs => ?_, ?_⟩
    · unfold consumeStatementEnd skipHorizAndComment
      simp only [String.toList_append, show ("#" : String).toList = ['#'] from rfl, List.append_assoc, List.cons_append, List.nil_append]
      rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)]
      simp only []
      rw [hskip_comm comm.toList _ hclean]; simp [skipCommentBody]
    · unfold consumeStatementEnd skipHorizAndComment
      simp only [String.toList_append, show ("#" : String).toList = ['#'] from rfl, List.append_assoc, List.cons_append, List.nil_append]
      rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)]
      simp only []
      have hs0 := hskip_comm comm.toList [] hclean
      rw [List.append_nil] at hs0; rw [hs0]; simp [skipCommentBody]

/-- `readBasicEscape` soundness for `Impl.parseBasicEscape`. -/
theorem readBasicEscape_imp_parseBasicEscape {cs after : List Char} {ch : Char}
    (h : readBasicEscape cs = some (ch, after)) : parseBasicEscape cs = .ok (ch, after) := by
  unfold readBasicEscape at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · rename_i h1 h2 h3 h4 r
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, decodeBasicEscape] at h
    rcases h with ⟨c', hd, rfl, rfl⟩
    cases hx1 : hexValModel? h1 <;> cases hx2 : hexValModel? h2 <;>
      cases hx3 : hexValModel? h3 <;> cases hx4 : hexValModel? h4 <;>
      try (simp [hx1, hx2, hx3, hx4] at hd; done)
    rename_i d1 d2 d3 d4
    let code := ((d1 * 16 + d2) * 16 + d3) * 16 + d4
    simp only [hx1, hx2, hx3, hx4] at hd
    have hbad : (decide (code > 0x10FFFF) || (decide (0xD800 ≤ code) && decide (code ≤ 0xDFFF))) = false := by
      cases hb : (decide (code > 0x10FFFF) || (decide (0xD800 ≤ code) && decide (code ≤ 0xDFFF)))
      · rfl
      · simp [code, hb] at hd
    have hd_eq : (if (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) then none else some (Char.ofNat code)) = some c' := hd
    rw [show (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) = false from hbad] at hd_eq
    injection hd_eq with hc_eq; subst hc_eq
    change parseUnicodeHex 4 (h1 :: h2 :: h3 :: h4 :: r) = _
    unfold parseUnicodeHex
    simp only [takeHexDigits, show hexVal? = hexValModel? from rfl, hx1, hx2, hx3, hx4, Nat.zero_mul, Nat.zero_add]
    change (if (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) then _ else _) = _
    rw [show (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) = false from hbad]; rfl
  · rename_i h1 h2 h3 h4 h5 h6 h7 h8 r
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, decodeBasicEscape] at h
    rcases h with ⟨c', hd, rfl, rfl⟩
    cases hx1 : hexValModel? h1 <;> cases hx2 : hexValModel? h2 <;>
      cases hx3 : hexValModel? h3 <;> cases hx4 : hexValModel? h4 <;>
      cases hx5 : hexValModel? h5 <;> cases hx6 : hexValModel? h6 <;>
      cases hx7 : hexValModel? h7 <;> cases hx8 : hexValModel? h8 <;>
      try (simp [hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8] at hd; done)
    rename_i d1 d2 d3 d4 d5 d6 d7 d8
    let code := ((((((d1 * 16 + d2) * 16 + d3) * 16 + d4) * 16 + d5) * 16 + d6) * 16 + d7) * 16 + d8
    simp only [hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8] at hd
    have hbad : (decide (code > 0x10FFFF) || (decide (0xD800 ≤ code) && decide (code ≤ 0xDFFF))) = false := by
      cases hb : (decide (code > 0x10FFFF) || (decide (0xD800 ≤ code) && decide (code ≤ 0xDFFF)))
      · rfl
      · simp [code, hb] at hd
    have hd_eq : (if (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) then none else some (Char.ofNat code)) = some c' := hd
    rw [show (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) = false from hbad] at hd_eq
    injection hd_eq with hc_eq; subst hc_eq
    change parseUnicodeHex 8 (h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: r) = _
    unfold parseUnicodeHex
    simp only [takeHexDigits, show hexVal? = hexValModel? from rfl, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, Nat.zero_mul, Nat.zero_add]
    change (if (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) then _ else _) = _
    rw [show (code > 0x10FFFF || (0xD800 ≤ code && code ≤ 0xDFFF)) = false from hbad]; rfl
  · cases h

/-- When `readBasicEscape` returns `none`, `Impl.parseBasicEscape` returns `.error`. -/
theorem readBasicEscape_none_imp_err {cs : List Char} (h : readBasicEscape cs = none) :
    ∃ e, parseBasicEscape cs = .error e := by
  cases hp : parseBasicEscape cs with
  | error e => exact ⟨e, rfl⟩
  | ok pair =>
    rcases pair with ⟨ch, after⟩
    obtain ⟨esc, hdec, hesc_cs⟩ := parseBasicEscape_witness hp
    obtain ⟨escBody, hrend, hread⟩ := readBasicEscape_renderBasicEscapeChars hdec after
    rw [hrend, List.cons_append] at hesc_cs
    obtain ⟨_, rfl⟩ := List.cons.inj hesc_cs
    rw [hread] at h; cases h

/-- Valid `BasicEscapeAtom` renderings satisfy `CleanNorm` and contain no `'\n'`. -/
theorem cleanNorm_renderBasicEscapeChars {esc : BasicEscapeAtom} {c : Char}
    (hd : decodeBasicEscape esc = some c) :
    CleanNorm (renderBasicEscapeChars esc) ∧ '\n' ∉ renderBasicEscapeChars esc := by
  have hex_clean : ∀ {x d}, hexValModel? x = some d →
      (!isDisallowedControl x && x != '\r') = true ∧ '\n' ≠ x := by
    intro x d hx
    have hlt : x.toNat < 128 := by
      unfold hexValModel? at hx
      if h1 : ('0' ≤ x && x ≤ '9') = true then
        have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true (Bool.and_eq_true_iff.mp h1).2)
        have : '9'.val.toNat = 57 := rfl; have : x.toNat = x.val.toNat := rfl; omega
      else if h2 : ('a' ≤ x && x ≤ 'f') = true then
        have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true (Bool.and_eq_true_iff.mp h2).2)
        have : 'f'.val.toNat = 102 := rfl; have : x.toNat = x.val.toNat := rfl; omega
      else if h3 : ('A' ≤ x && x ≤ 'F') = true then
        have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true (Bool.and_eq_true_iff.mp h3).2)
        have : 'F'.val.toNat = 70 := rfl; have : x.toNat = x.val.toNat := rfl; omega
      else simp [h1, h2, h3] at hx
    have hall : (List.range 128).all (fun k =>
        let ch := Char.ofNat k
        (hexValModel? ch).isNone || ((!isDisallowedControl ch && ch != '\r') && ch != '\n')) = true := by decide
    have hm := List.all_eq_true.mp hall x.toNat (List.mem_range.mpr hlt)
    simp only [Char.ofNat_toNat, hx, Option.isNone_some, Bool.false_or, Bool.and_eq_true, bne_iff_ne] at hm
    exact ⟨by simp [hm.1], hm.2.symm⟩
  cases esc with
  | backspace | tab | linefeed | formfeed | carriageReturn | quote | backslash =>
    exact ⟨by decide, by decide⟩
  | unicode4 h1 h2 h3 h4 =>
    simp only [decodeBasicEscape] at hd
    cases hx1 : hexValModel? h1 <;> cases hx2 : hexValModel? h2 <;>
      cases hx3 : hexValModel? h3 <;> cases hx4 : hexValModel? h4 <;>
      simp [hx1, hx2, hx3, hx4] at hd
    obtain ⟨c1, n1⟩ := hex_clean hx1; obtain ⟨c2, n2⟩ := hex_clean hx2
    obtain ⟨c3, n3⟩ := hex_clean hx3; obtain ⟨c4, n4⟩ := hex_clean hx4
    refine ⟨?_, by simp [renderBasicEscapeChars, n1, n2, n3, n4]⟩
    unfold CleanNorm renderBasicEscapeChars
    simp only [List.all_cons, List.all_nil, Bool.and_true, c1, c2, c3, c4]; decide
  | unicode8 h1 h2 h3 h4 h5 h6 h7 h8 =>
    simp only [decodeBasicEscape] at hd
    cases hx1 : hexValModel? h1 <;> cases hx2 : hexValModel? h2 <;>
      cases hx3 : hexValModel? h3 <;> cases hx4 : hexValModel? h4 <;>
      cases hx5 : hexValModel? h5 <;> cases hx6 : hexValModel? h6 <;>
      cases hx7 : hexValModel? h7 <;> cases hx8 : hexValModel? h8 <;>
      simp [hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8] at hd
    obtain ⟨c1, n1⟩ := hex_clean hx1; obtain ⟨c2, n2⟩ := hex_clean hx2
    obtain ⟨c3, n3⟩ := hex_clean hx3; obtain ⟨c4, n4⟩ := hex_clean hx4
    obtain ⟨c5, n5⟩ := hex_clean hx5; obtain ⟨c6, n6⟩ := hex_clean hx6
    obtain ⟨c7, n7⟩ := hex_clean hx7; obtain ⟨c8, n8⟩ := hex_clean hx8
    refine ⟨?_, by simp [renderBasicEscapeChars, n1, n2, n3, n4, n5, n6, n7, n8]⟩
    unfold CleanNorm renderBasicEscapeChars
    simp only [List.all_cons, List.all_nil, Bool.and_true, c1, c2, c3, c4, c5, c6, c7, c8]; decide

/-- Canonical `escapeBasicBody` outputs satisfy `CleanNorm`. -/
theorem cleanNorm_escapeBasicBody (allowNl : Bool) (s : String) :
    CleanNorm (escapeBasicBody allowNl s).toList := by
  have heq : (escapeBasicBody allowNl s).toList = s.toList.flatMap (fun c => (escapeBasicChar allowNl c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  rw [heq]
  induction s.toList with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, cleanNorm_append]
    refine ⟨?_, ih⟩
    rcases escapeBasicChar_atom allowNl c with ⟨hc_l, _, _, hcr, hctrl, _⟩ | ⟨esc, hd, hesc_l⟩
    · rw [hc_l]; exact cleanNorm_cons.mpr ⟨⟨hctrl, hcr⟩, rfl⟩
    · rw [hesc_l]; exact (cleanNorm_renderBasicEscapeChars hd).1

/-- Rendered `MultilineBasicAtom` bodies satisfy `CleanNorm`. -/
theorem cleanNorm_renderMultilineAtoms :
    ∀ (fl at_ : Bool) (qr : Nat) (cs : List Char) (atoms : List MultilineBasicAtom) (enc : List Char),
      renderMultilineAtoms fl at_ qr cs atoms = some enc → CleanNorm enc := by
  intro fl at_ qr cs atoms
  induction atoms generalizing fl at_ qr cs with
  | nil =>
    intro enc h; cases cs <;> simp [renderMultilineAtoms] at h; subst h; rfl
  | cons atom atoms ih =>
    intro enc h
    cases atom with
    | plain =>
      cases cs with
      | nil => simp [renderMultilineAtoms] at h
      | cons c cs' =>
        simp only [renderMultilineAtoms] at h
        if hc : (c == '\\' || c == '\r' || isDisallowedControl c) = true then simp [hc] at h else
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
        have hctrl : isDisallowedControl c = false := by
          cases hd : isDisallowedControl c <;> simp_all
        have hcr : c ≠ '\r' := fun h0 => by subst h0; exact hc (by decide)
        if h1 : (fl && c == '\n') = true then simp [h1] at h else
        if h2 : (at_ && (isModelHorizWs c || c == '\n')) = true then simp [h1, h2] at h else
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hcq : (c == '"') = true
        · simp only [hcq, ↓reduceIte] at h; split at h <;> try cases h
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          rcases h with ⟨rest, hrest, rfl⟩
          exact cleanNorm_cons.mpr ⟨⟨hctrl, hcr⟩, ih false false (qr + 1) cs' rest hrest⟩
        · simp only [hcq, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          rcases h with ⟨rest, hrest, rfl⟩
          exact cleanNorm_cons.mpr ⟨⟨hctrl, hcr⟩, ih false false 0 cs' rest hrest⟩
    | escape esc =>
      cases cs with
      | nil => simp [renderMultilineAtoms] at h
      | cons c cs' =>
        simp only [renderMultilineAtoms] at h
        cases hd : decodeBasicEscape esc with
        | none => simp [hd] at h
        | some c' =>
          simp only [hd] at h; split at h <;> try cases h
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          rcases h with ⟨rest, hrest, rfl⟩
          exact cleanNorm_append.mpr ⟨(cleanNorm_renderBasicEscapeChars hd).1, ih false false 0 cs' rest hrest⟩
    | lineTrim ws1 ws2 =>
      simp only [renderMultilineAtoms] at h; split at h <;> try cases h
      rename_i hws; simp only [Bool.and_eq_true] at hws
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨rest, hrest, rfl⟩
      have hcl2 : CleanNorm ws2.toList := by
        apply List.all_eq_true.mpr; intro c hcm
        have hm := List.all_eq_true.mp hws.2 c hcm
        simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hm
        rcases hm with (rfl | rfl) | rfl <;> decide
      simp only [List.cons_append, List.append_assoc]
      exact cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩,
        cleanNorm_append.mpr ⟨cleanNorm_horizWsStr hws.1,
          cleanNorm_cons.mpr ⟨⟨by decide, by decide⟩,
            cleanNorm_append.mpr ⟨hcl2, ih false true 0 cs rest hrest⟩⟩⟩⟩

end LeanSwe.Toml.Proofs
