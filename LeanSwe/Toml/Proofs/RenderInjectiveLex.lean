import LeanSwe.Toml.Model

/-!
# Lexical Left-Inverses for `Toml.Model.render` Injectivity

Proves `Impl`-independent left-inverse and CRLF-normalization lemmas for `Toml.Model`
trivia, horizontal whitespace, line suffixes, keys, dotted keys, and string literals.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

private theorem expandNewlines_nonNl {mask : List Bool} {c : Char} {cs : List Char} (hnl : c ≠ '\n') :
    expandNewlines mask (c :: cs) = (expandNewlines mask cs >>= fun r => some (c :: r)) := by
  cases mask with
  | nil => conv => lhs; unfold expandNewlines
           split <;> simp_all
  | cons b bs =>
    cases b
    · conv => lhs; unfold expandNewlines
      split <;> simp_all
    · conv => lhs; unfold expandNewlines
      split <;> simp_all

/-- `stripCrBeforeLf` recovers any `\r`-free list passed through `expandNewlines`. -/
theorem stripCrBeforeLf_expandNewlines :
    ∀ (mask : List Bool) (cs out : List Char),
      '\r' ∉ cs → expandNewlines mask cs = some out → stripCrBeforeLf out = cs := by
  intro mask cs
  induction cs generalizing mask with
  | nil =>
    intro out _ h
    cases mask with
    | nil => simp [expandNewlines] at h; subst h; rfl
    | cons _ _ => simp [expandNewlines] at h
  | cons c cs ih =>
    intro out hncr h
    have hcr : c ≠ '\r' := fun heq => hncr (heq ▸ List.mem_cons_self)
    have hncr_tl : '\r' ∉ cs := fun hm => hncr (List.mem_cons_of_mem _ hm)
    by_cases hnl : c = '\n'
    · subst hnl
      cases mask with
      | nil =>
        simp only [expandNewlines, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨rest, hrest, rfl⟩
        simp [stripCrBeforeLf, ih [] rest hncr_tl hrest]
      | cons b bs =>
        cases b <;>
          simp only [expandNewlines, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h <;>
          rcases h with ⟨rest, hrest, rfl⟩ <;>
          simp [stripCrBeforeLf, ih bs rest hncr_tl hrest]
    · rw [expandNewlines_nonNl hnl] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨rest, hrest, rfl⟩
      have hstep : stripCrBeforeLf (c :: rest) = c :: stripCrBeforeLf rest := by
        conv => lhs; unfold stripCrBeforeLf
        split <;> simp_all
      rw [hstep, ih mask rest hncr_tl hrest]

/-- Check that `s` contains no raw `'\r'` character. -/
abbrev NoCrStr (s : String) : Prop := '\r' ∉ s.toList

theorem noCrStr_append {a b : String} (ha : NoCrStr a) (hb : NoCrStr b) : NoCrStr (a ++ b) := by
  unfold NoCrStr at *
  rw [String.toList_append, List.mem_append, not_or]
  exact ⟨ha, hb⟩

theorem noCrStr_intercalate {sep : String} {xs : List String}
    (hsep : NoCrStr sep) (hxs : ∀ x ∈ xs, NoCrStr x) : NoCrStr (String.intercalate sep xs) := by
  match xs with
  | [] => simp [NoCrStr, String.intercalate_nil]
  | [x] => simpa [String.intercalate_singleton] using hxs x List.mem_cons_self
  | x :: y :: rest =>
    rw [String.intercalate_cons_cons]
    exact noCrStr_append (noCrStr_append (hxs x List.mem_cons_self) hsep)
      (noCrStr_intercalate hsep (fun z hz => hxs z (List.mem_cons_of_mem _ hz)))

theorem noCr_horizWsStr {s : String} (h : isHorizWsStr s = true) : NoCrStr s := by
  intro hm
  have hc := List.all_eq_true.mp h '\r' hm
  revert hc; decide

private theorem checkClosedTriviaAux_cons_ne_nl (b : Bool) (c : Char) (cs : List Char) (hnl : c ≠ '\n') :
    checkClosedTriviaAux b (c :: cs) =
      if b then !isDisallowedControl c && c != '\r' && checkClosedTriviaAux true cs
      else if isModelHorizWs c then checkClosedTriviaAux false cs
      else if c == '#' then checkClosedTriviaAux true cs else false := by
  cases b
  · conv => lhs; unfold checkClosedTriviaAux
    split <;> simp_all
  · conv => lhs; unfold checkClosedTriviaAux
    split <;> simp_all

private theorem checkEofTriviaAux_cons_ne_nl (b : Bool) (c : Char) (cs : List Char) (hnl : c ≠ '\n') :
    checkEofTriviaAux b (c :: cs) =
      if b then !isDisallowedControl c && c != '\r' && checkEofTriviaAux true cs
      else if isModelHorizWs c then checkEofTriviaAux false cs
      else if c == '#' then checkEofTriviaAux true cs else false := by
  cases b
  · conv => lhs; unfold checkEofTriviaAux
    split <;> simp_all
  · conv => lhs; unfold checkEofTriviaAux
    split <;> simp_all

theorem noCr_closedTriviaAux : ∀ (b : Bool) (cs : List Char), checkClosedTriviaAux b cs = true → '\r' ∉ cs := by
  intro b cs
  induction cs generalizing b with
  | nil => intro _; simp
  | cons c rest ih =>
    intro h
    by_cases hnl : c = '\n'
    · subst hnl
      have h' : checkClosedTriviaAux false rest = true := by cases b <;> simpa [checkClosedTriviaAux] using h
      intro hm; rcases List.mem_cons.mp hm with heq | htl
      · nomatch heq
      · exact ih false h' htl
    · rw [checkClosedTriviaAux_cons_ne_nl b c rest hnl] at h
      cases b with
      | true =>
        simp only [↓reduceIte, Bool.and_eq_true, bne_iff_ne] at h
        intro hm; rcases List.mem_cons.mp hm with rfl | htl
        · exact h.1.2 rfl
        · exact ih true h.2 htl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i hws
          intro hm; rcases List.mem_cons.mp hm with rfl | htl
          · revert hws; decide
          · exact ih false h htl
        · split at h
          · rename_i hhash
            have hc_hash := eq_of_beq hhash; subst hc_hash
            intro hm; rcases List.mem_cons.mp hm with hcr | htl
            · nomatch hcr
            · exact ih true h htl
          · cases h

theorem noCr_closedTrivia {s : String} (h : isClosedTrivia s = true) : NoCrStr s :=
  noCr_closedTriviaAux false s.toList h

theorem noCr_eofTriviaAux : ∀ (b : Bool) (cs : List Char), checkEofTriviaAux b cs = true → '\r' ∉ cs := by
  intro b cs
  induction cs generalizing b with
  | nil => intro _; simp
  | cons c rest ih =>
    intro h
    by_cases hnl : c = '\n'
    · subst hnl
      have h' : checkEofTriviaAux false rest = true := by cases b <;> simpa [checkEofTriviaAux] using h
      intro hm; rcases List.mem_cons.mp hm with heq | htl
      · nomatch heq
      · exact ih false h' htl
    · rw [checkEofTriviaAux_cons_ne_nl b c rest hnl] at h
      cases b with
      | true =>
        simp only [↓reduceIte, Bool.and_eq_true, bne_iff_ne] at h
        intro hm; rcases List.mem_cons.mp hm with rfl | htl
        · exact h.1.2 rfl
        · exact ih true h.2 htl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i hws
          intro hm; rcases List.mem_cons.mp hm with rfl | htl
          · revert hws; decide
          · exact ih false h htl
        · split at h
          · rename_i hhash
            have hc_hash := eq_of_beq hhash; subst hc_hash
            intro hm; rcases List.mem_cons.mp hm with hcr | htl
            · nomatch hcr
            · exact ih true h htl
          · cases h

theorem noCr_eofTrivia {s : String} (h : isEofTrivia s = true) : NoCrStr s :=
  noCr_eofTriviaAux false s.toList h

theorem noCr_escapeBasicChar (allowNl : Bool) (c : Char) : NoCrStr (escapeBasicChar allowNl c) := by
  unfold escapeBasicChar
  if h1 : (c == '\\') = true then simp only [h1, ↓reduceIte]; decide else
  if h2 : (c == '"') = true then simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; decide else
  if h3 : (c == '\x08') = true then simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]; decide else
  if h4 : (c == '\t') = true then simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]; decide else
  if h5 : (c == '\n') = true then cases allowNl <;> (simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]; decide) else
  if h6 : (c == '\x0c') = true then simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte]; decide else
  if h7 : (c == '\r') = true then simp only [h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ↓reduceIte]; decide else
  if h8 : isDisallowedControl c = true then
    have hlt : c.toNat < 256 := by
      simp only [isDisallowedControl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h8
      omega
    have hhex : ∀ m < 16, hexDigitUpper m ≠ '\r' := by
      have hall : (List.range 16).all (fun m => hexDigitUpper m != '\r') = true := by decide
      intro m hm
      simpa [bne_iff_ne] using List.all_eq_true.mp hall m (List.mem_range.mpr hm)
    have hd1 := (hhex (c.toNat / 16) (by omega)).symm
    have hd2 := (hhex (c.toNat % 16) (Nat.mod_lt _ (by decide))).symm
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_eq_true, ↓reduceIte]
    simp [NoCrStr, String.toList_append, hd1, hd2]
  else
    have hne : '\r' ≠ c := fun e => h7 (beq_iff_eq.mpr e.symm)
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_eq_true, ↓reduceIte]
    simp [NoCrStr, hne]

theorem noCr_escapeBasicBody (allowNl : Bool) (s : String) : NoCrStr (escapeBasicBody allowNl s) := by
  unfold NoCrStr escapeBasicBody
  rw [String.toList_join, List.mem_flatMap]
  rintro ⟨part, hpart, hcr⟩
  rcases List.mem_map.mp hpart with ⟨ch, _, rfl⟩
  exact noCr_escapeBasicChar allowNl ch hcr

theorem noCr_renderBasicEscapeChars {esc : BasicEscapeAtom} {c : Char}
    (hd : decodeBasicEscape esc = some c) : '\r' ∉ renderBasicEscapeChars esc := by
  have hex_nocr : ∀ {h d}, hexValModel? h = some d → '\r' ≠ h := by
    intro h d hh heq; subst heq; nomatch hh
  cases esc with
  | backspace | tab | linefeed | formfeed | carriageReturn | quote | backslash =>
    simp [renderBasicEscapeChars]
  | unicode4 h1 h2 h3 h4 =>
    simp only [decodeBasicEscape] at hd
    cases hh1 : hexValModel? h1 <;> cases hh2 : hexValModel? h2 <;>
      cases hh3 : hexValModel? h3 <;> cases hh4 : hexValModel? h4 <;>
      simp [hh1, hh2, hh3, hh4] at hd
    simp [renderBasicEscapeChars, hex_nocr hh1, hex_nocr hh2, hex_nocr hh3, hex_nocr hh4]
  | unicode8 h1 h2 h3 h4 h5 h6 h7 h8 =>
    simp only [decodeBasicEscape] at hd
    cases hh1 : hexValModel? h1 <;> cases hh2 : hexValModel? h2 <;>
      cases hh3 : hexValModel? h3 <;> cases hh4 : hexValModel? h4 <;>
      cases hh5 : hexValModel? h5 <;> cases hh6 : hexValModel? h6 <;>
      cases hh7 : hexValModel? h7 <;> cases hh8 : hexValModel? h8 <;>
      simp [hh1, hh2, hh3, hh4, hh5, hh6, hh7, hh8] at hd
    simp [renderBasicEscapeChars, hex_nocr hh1, hex_nocr hh2, hex_nocr hh3, hex_nocr hh4,
      hex_nocr hh5, hex_nocr hh6, hex_nocr hh7, hex_nocr hh8]

theorem noCr_renderBasicAtoms :
    ∀ (cs : List Char) (atoms : List BasicCharAtom) (enc : List Char),
      renderBasicAtoms cs atoms = some enc → '\r' ∉ enc
  | [], [], enc, h => by simp [renderBasicAtoms] at h; subst h; simp
  | c :: cs, .plain :: atoms, enc, h => by
    simp only [renderBasicAtoms] at h
    split at h
    · rename_i hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨rest, hrest, rfl⟩
      simp only [Bool.and_eq_true, bne_iff_ne] at hok
      intro hm
      rcases List.mem_cons.mp hm with rfl | htl
      · exact hok.1.2 rfl
      · exact noCr_renderBasicAtoms cs atoms rest hrest htl
    · cases h
  | c :: cs, .escape esc :: atoms, enc, h => by
    simp only [renderBasicAtoms] at h
    cases hd : decodeBasicEscape esc with
    | none => simp [hd] at h
    | some c' =>
      simp only [hd] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨rest, hrest, rfl⟩
        rw [List.mem_append, not_or]
        exact ⟨noCr_renderBasicEscapeChars hd, noCr_renderBasicAtoms cs atoms rest hrest⟩
      · cases h
  | [], _ :: _, _, h => by simp [renderBasicAtoms] at h
  | _ :: _, [], _, h => by simp [renderBasicAtoms] at h

theorem noCr_renderMultilineAtoms :
    ∀ (fl at_ : Bool) (qr : Nat) (cs : List Char) (atoms : List MultilineBasicAtom) (enc : List Char),
      renderMultilineAtoms fl at_ qr cs atoms = some enc → '\r' ∉ enc := by
  intro fl at_ qr cs atoms
  induction atoms generalizing fl at_ qr cs with
  | nil =>
    intro enc h
    cases cs with
    | nil => simp [renderMultilineAtoms] at h; subst h; simp
    | cons _ _ => simp [renderMultilineAtoms] at h
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
        have hne : '\r' ≠ c := fun heq => hc (by subst heq; decide)
        if h1 : (fl && c == '\n') = true then simp [h1] at h else
        if h2 : (at_ && (isModelHorizWs c || c == '\n')) = true then simp [h1, h2] at h else
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hq : (c == '"') = true
        · simp only [hq, ↓reduceIte] at h
          split at h
          · cases h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
            rcases h with ⟨rest, hrest, rfl⟩
            simp [hne, ih false false (qr + 1) cs' rest hrest]
        · simp only [hq, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          rcases h with ⟨rest, hrest, rfl⟩
          simp [hne, ih false false 0 cs' rest hrest]
    | escape esc =>
      cases cs with
      | nil => simp [renderMultilineAtoms] at h
      | cons c cs' =>
        simp only [renderMultilineAtoms] at h
        cases hd : decodeBasicEscape esc with
        | none => simp [hd] at h
        | some c' =>
          simp only [hd] at h
          split at h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
            rcases h with ⟨rest, hrest, rfl⟩
            rw [List.mem_append, not_or]
            exact ⟨noCr_renderBasicEscapeChars hd, ih false false 0 cs' rest hrest⟩
          · cases h
    | lineTrim ws1 ws2 =>
      simp only [renderMultilineAtoms] at h
      split at h
      · rename_i hws
        simp only [Bool.and_eq_true] at hws
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨rest, hrest, rfl⟩
        have hw1 : '\r' ∉ ws1.toList := noCr_horizWsStr hws.1
        have hw2 : '\r' ∉ ws2.toList := fun hm => by
          have hc := List.all_eq_true.mp hws.2 '\r' hm
          revert hc; decide
        simp [hw1, hw2, ih false true 0 cs rest hrest]
      · cases h

/-- Skip leading TOML horizontal whitespace characters. -/
def dropHoriz : List Char → List Char
  | c :: cs => if isModelHorizWs c then dropHoriz cs else c :: cs
  | [] => []

theorem dropHoriz_len_le : ∀ cs : List Char, (dropHoriz cs).length ≤ cs.length
  | [] => Nat.le_refl _
  | c :: cs => by
    unfold dropHoriz
    split
    · exact Nat.le_trans (dropHoriz_len_le cs) (Nat.le_succ _)
    · exact Nat.le_refl _

theorem dropHoriz_append {ws : String} {rem : List Char}
    (hws : isHorizWsStr ws = true) (hrem : ∀ c r, rem = c :: r → isModelHorizWs c = false) :
    dropHoriz (ws.toList ++ rem) = rem := by
  have haux : ∀ l : List Char, l.all isModelHorizWs = true → dropHoriz (l ++ rem) = rem := by
    intro l hl
    induction l with
    | nil =>
      cases rem with
      | nil => rfl
      | cons c r => simp [dropHoriz, hrem c r rfl]
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hl
      simp [dropHoriz, hl.1, ih hl.2]
  exact haux ws.toList hws

/-- Skip multiline trivia (`' '`, `'\t'`, `'\n'`, and `#...\n` comments). -/
def dropTrivia : Bool → List Char → List Char
  | _, [] => []
  | _, '\n' :: rest => dropTrivia false rest
  | true, _ :: rest => dropTrivia true rest
  | false, c :: rest =>
    if isModelHorizWs c then dropTrivia false rest
    else if c == '#' then dropTrivia true rest
    else c :: rest

private theorem dropTrivia_cons_ne_nl (b : Bool) (c : Char) (r : List Char) (hnl : c ≠ '\n') :
    dropTrivia b (c :: r) =
      if b then dropTrivia true r
      else if isModelHorizWs c then dropTrivia false r
      else if c == '#' then dropTrivia true r else c :: r := by
  cases b
  · conv => lhs; unfold dropTrivia
    split <;> simp_all
  · conv => lhs; unfold dropTrivia
    split <;> simp_all

theorem dropTrivia_closed_append :
    ∀ (b : Bool) (tr rem : List Char),
      checkClosedTriviaAux b tr = true →
      (∀ c r, rem = c :: r → isModelHorizWs c = false ∧ c ≠ '\n' ∧ c ≠ '#') →
      dropTrivia b (tr ++ rem) = rem := by
  intro b tr rem
  induction tr generalizing b with
  | nil =>
    intro htr hrem
    cases b with
    | true => simp [checkClosedTriviaAux] at htr
    | false =>
      rw [List.nil_append]
      cases rem with
      | nil => rfl
      | cons c r =>
        obtain ⟨hws, hnl, hhash⟩ := hrem c r rfl
        rw [dropTrivia_cons_ne_nl false c r hnl]
        simp [hws, beq_false_of_ne hhash]
  | cons c cs ih =>
    intro htr hrem
    by_cases hnl : c = '\n'
    · subst hnl
      have htr' : checkClosedTriviaAux false cs = true := by cases b <;> simpa [checkClosedTriviaAux] using htr
      simpa [dropTrivia] using ih false htr' hrem
    · rw [checkClosedTriviaAux_cons_ne_nl b c cs hnl] at htr
      rw [List.cons_append, dropTrivia_cons_ne_nl b c (cs ++ rem) hnl]
      cases b with
      | true =>
        simp only [↓reduceIte, Bool.and_eq_true] at htr ⊢
        exact ih true htr.2 hrem
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at htr ⊢
        split at htr
        · rename_i hws; simp [hws, ih false htr hrem]
        · rename_i hws
          split at htr
          · rename_i hhash; simp [hws, hhash, ih true htr hrem]
          · cases htr

theorem dropTrivia_eof : ∀ (b : Bool) (cs : List Char), checkEofTriviaAux b cs = true → dropTrivia b cs = [] := by
  intro b cs
  induction cs generalizing b with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro h
    by_cases hnl : c = '\n'
    · subst hnl
      exact ih false (by cases b <;> simpa [checkEofTriviaAux] using h)
    · rw [checkEofTriviaAux_cons_ne_nl b c rest hnl] at h
      rw [dropTrivia_cons_ne_nl b c rest hnl]
      cases b with
      | true =>
        simp only [↓reduceIte, Bool.and_eq_true] at h ⊢
        exact ih true h.2
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        split at h
        · rename_i hws; simp [hws, ih false h]
        · rename_i hws
          split at h
          · rename_i hhash; simp [hws, hhash, ih true h]
          · cases h

private def skipToNl : List Char → List Char
  | [] => []
  | '\n' :: r => r
  | _ :: r => skipToNl r

private theorem skipToNl_cons_ne_nl (c : Char) (r : List Char) (hnl : c ≠ '\n') :
    skipToNl (c :: r) = skipToNl r := by
  conv => lhs; unfold skipToNl
  split <;> simp_all

/-- Drop horizontal whitespace, optional `#...` comment, and terminating `\n` (or EOF). -/
def dropLineEnd (cs : List Char) : List Char :=
  match dropHoriz cs with
  | '#' :: r => skipToNl r
  | '\n' :: r => r
  | _ => []

theorem dropLineEnd_append {suf : LineSuffixTape} {rsuf lineEnd : String} {tail : List Char}
    (hsuf : renderLineSuffix suf = some rsuf)
    (hle : (lineEnd = "\n") ∨ (lineEnd = "" ∧ tail = [])) :
    dropLineEnd ((rsuf ++ lineEnd).toList ++ tail) = tail ∧ NoCrStr rsuf := by
  unfold renderLineSuffix at hsuf
  split at hsuf
  · cases hsuf
  · rename_i hws_not
    have hws : isHorizWsStr suf.ws = true := by cases h : isHorizWsStr suf.ws <;> simp_all
    cases hc : suf.comment with
    | none =>
      rw [hc] at hsuf; dsimp only at hsuf; injection hsuf with hrsuf; subst hrsuf
      refine ⟨?_, noCr_horizWsStr hws⟩
      rcases hle with rfl | ⟨rfl, rfl⟩
      · simp only [String.toList_append, List.append_assoc, show ("\n" : String).toList = ['\n'] from rfl, List.singleton_append]
        unfold dropLineEnd
        rw [dropHoriz_append hws (fun c r h => by injection h with heq _; subst heq; decide)]
        rfl
      · simp only [String.append_empty, List.append_nil]
        unfold dropLineEnd
        have hd := dropHoriz_append (rem := []) hws (fun _ _ h => nomatch h)
        rw [List.append_nil] at hd; rw [hd]
    | some comm =>
      rw [hc] at hsuf; dsimp only at hsuf
      split at hsuf
      · rename_i hclean
        injection hsuf with hrsuf; subst hrsuf
        have hnocr_c : NoCrStr comm := fun hm => by
          have h1 := List.all_eq_true.mp hclean '\r' hm; simp at h1
        have hnonl_aux : ∀ (cs : List Char) (l2 : List Char),
            (cs.all fun c => !isDisallowedControl c && c != '\n' && c != '\r') = true →
            skipToNl (cs ++ l2) = skipToNl l2 := by
          intro cs l2 hcs
          induction cs with
          | nil => rfl
          | cons ch rest ih =>
            simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hcs
            rw [List.cons_append, skipToNl_cons_ne_nl ch (rest ++ l2) hcs.1.1.2, ih hcs.2]
        refine ⟨?_, noCrStr_append (noCrStr_append (noCr_horizWsStr hws) (by decide)) hnocr_c⟩
        have hfull : ((suf.ws ++ "#" ++ comm ++ lineEnd).toList ++ tail) =
            suf.ws.toList ++ ('#' :: (comm.toList ++ (lineEnd.toList ++ tail))) := by
          simp [String.toList_append, List.append_assoc, show ("#" : String).toList = ['#'] from rfl]
        rw [hfull]
        unfold dropLineEnd
        rw [dropHoriz_append hws (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)]
        change skipToNl (comm.toList ++ (lineEnd.toList ++ tail)) = tail
        rw [hnonl_aux comm.toList _ hclean]
        rcases hle with rfl | ⟨rfl, rfl⟩
        · rfl
        · rfl
      · cases hsuf

end LeanSwe.Toml.Proofs
