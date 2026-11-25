import LeanSwe.Toml.Proofs.RenderInjectiveKeyStr

/-!
# Multiline Basic String Body Left-Inverse for `Toml.Model.render`

Proves `readMlBasicBody` is a left-inverse of `renderMultilineAtoms` and canonical
`escapeBasicBody true` without importing `Toml.Impl`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

/-- Skip leading horizontal whitespace and `'\n'` characters. -/
def dropHorizAndNl : List Char → List Char
  | c :: cs => if isModelHorizWs c || c == '\n' then dropHorizAndNl cs else c :: cs
  | [] => []

theorem dropHorizAndNl_len_le : ∀ cs : List Char, (dropHorizAndNl cs).length ≤ cs.length
  | [] => Nat.le_refl _
  | c :: cs => by
    unfold dropHorizAndNl
    split
    · exact Nat.le_trans (dropHorizAndNl_len_le cs) (Nat.le_succ _)
    · exact Nat.le_refl _

theorem dropHorizAndNl_append {ws : String} {rem : List Char}
    (hws : isHorizAndNlStr ws = true)
    (hrem : ∀ c r, rem = c :: r → isModelHorizWs c = false ∧ c ≠ '\n') :
    dropHorizAndNl (ws.toList ++ rem) = rem := by
  have haux : ∀ l : List Char, (l.all fun c => isModelHorizWs c || c == '\n') = true →
      dropHorizAndNl (l ++ rem) = rem := by
    intro l hl
    induction l with
    | nil =>
      cases rem with
      | nil => rfl
      | cons c r => obtain ⟨hw, hn⟩ := hrem c r rfl; simp [dropHorizAndNl, hw, beq_false_of_ne hn]
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hl
      simp [dropHorizAndNl, hl.1, ih hl.2]
  exact haux ws.toList hws

/-- Pure left-inverse decoder for multiline basic string bodies after `"""` (and optional opener `\n`). -/
def readMlBasicBody : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: '"' :: '"' :: '"' :: '"' :: '"' :: _ => none
  | '"' :: '"' :: '"' :: '"' :: '"' :: rest => some (['"', '"'], rest)
  | '"' :: '"' :: '"' :: '"' :: rest => some (['"'], rest)
  | '"' :: '"' :: '"' :: rest => some ([], rest)
  | '\\' :: rest =>
    match h1 : readBasicEscape rest with
    | some (ch, afterEsc) =>
      have : afterEsc.length < ('\\' :: rest).length := readBasicEscape_len_lt h1
      (readMlBasicBody afterEsc).map fun (cs, rem) => (ch :: cs, rem)
    | none =>
      match h2 : dropHoriz rest with
      | '\n' :: afterNl =>
        have : (dropHorizAndNl afterNl).length < ('\\' :: rest).length := by
          have a := dropHoriz_len_le rest
          have b := dropHorizAndNl_len_le afterNl
          rw [h2] at a; simp only [List.length_cons] at a ⊢; omega
        readMlBasicBody (dropHorizAndNl afterNl)
      | _ => none
  | c :: rest =>
    (readMlBasicBody rest).map fun (cs, rem) => (c :: cs, rem)
termination_by cs => cs.length

theorem readMlBasicBody_backslash (rest : List Char) :
    readMlBasicBody ('\\' :: rest) =
      match readBasicEscape rest with
      | some (ch, afterEsc) =>
        (readMlBasicBody afterEsc).map fun (cs, rem) => (ch :: cs, rem)
      | none =>
        match dropHoriz rest with
        | '\n' :: afterNl => readMlBasicBody (dropHorizAndNl afterNl)
        | _ => none := by
  (conv => lhs; unfold readMlBasicBody)
  split
  · contradiction
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ heq
    obtain ⟨_, rfl⟩ := List.cons.inj heq
    split <;> rename_i h1
    · simp [h1]
    · simp only [h1]; split <;> rename_i h2
      · rw [h2]; rfl
      · symm; split
        · rename_i afterNl heq2; exact False.elim (h2 afterNl heq2)
        · rfl
  · rename_i _ _ _ _ _ hnotbs heq
    exact False.elim (hnotbs (List.cons.inj heq).1.symm)

private theorem readMlBasicBody_close3 {rem : List Char} (hrem : ∀ c r, rem = c :: r → c ≠ '"') :
    readMlBasicBody ('"' :: '"' :: '"' :: rem) = some ([], rem) := by
  (conv => lhs; unfold readMlBasicBody)
  split
  · contradiction
  · rename_i _ heq; exact False.elim (hrem '"' _ (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2 rfl)
  · rename_i _ heq; exact False.elim (hrem '"' _ (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2 rfl)
  · rename_i _ heq; exact False.elim (hrem '"' _ (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2 rfl)
  · rename_i r heq; obtain ⟨_, rfl⟩ := List.cons.inj (List.cons.inj (List.cons.inj heq).2).2; rfl
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ _ _ _ hnot3 _ heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hnot3 rem rfl h1.symm)

private theorem readMlBasicBody_close4 {rem : List Char} (hrem : ∀ c r, rem = c :: r → c ≠ '"') :
    readMlBasicBody ('"' :: '"' :: '"' :: '"' :: rem) = some (['"'], rem) := by
  (conv => lhs; unfold readMlBasicBody)
  split
  · contradiction
  · rename_i _ heq; exact False.elim (hrem '"' _ (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2 rfl)
  · rename_i _ heq; exact False.elim (hrem '"' _ (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2 rfl)
  · rename_i r heq; obtain ⟨_, rfl⟩ := List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2; rfl
  · rename_i _ hnot4 heq; exact False.elim (hnot4 rem (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2.symm)
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ _ _ _ hnot3 _ heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hnot3 ('"' :: rem) rfl h1.symm)

private theorem readMlBasicBody_close5 {rem : List Char} (hrem : ∀ c r, rem = c :: r → c ≠ '"') :
    readMlBasicBody ('"' :: '"' :: '"' :: '"' :: '"' :: rem) = some (['"', '"'], rem) := by
  (conv => lhs; unfold readMlBasicBody)
  split
  · contradiction
  · rename_i _ heq; exact False.elim (hrem '"' _ (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2).2 rfl)
  · rename_i r heq; obtain ⟨_, rfl⟩ := List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2; rfl
  · rename_i _ _ hnot5 heq; exact False.elim (hnot5 rem (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2).2.symm)
  · rename_i _ _ hnot4 heq; exact False.elim (hnot4 ('"' :: rem) (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2.symm)
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ _ _ _ hnot3 _ heq; obtain ⟨rfl, h1⟩ := List.cons.inj heq; exact False.elim (hnot3 ('"' :: '"' :: rem) rfl h1.symm)

private theorem mlBasicStep_not_quote3 {c : Char} {tail : List Char}
    (hbs : c ≠ '\\') (hn3 : ¬(c = '"' ∧ ∃ t, tail = '"' :: '"' :: t)) :
    readMlBasicBody (c :: tail) = (readMlBasicBody tail).map fun (cs, rem) => (c :: cs, rem) := by
  conv => lhs; unfold readMlBasicBody
  split <;> first | simp_all | (exfalso; apply hn3; simp_all)

private theorem mlAtoms_props :
    ∀ (fl at_ : Bool) (qr : Nat) (cs : List Char) (atoms : List MultilineBasicAtom) (enc : List Char),
      renderMultilineAtoms fl at_ qr cs atoms = some enc →
      (enc = [] → cs = []) ∧
      (enc = ['"'] → cs = ['"']) ∧
      (qr ≥ 2 → ∀ r, enc ≠ '"' :: r) ∧
      (qr ≥ 1 → ∀ r, enc ≠ '"' :: '"' :: r) ∧
      (at_ = true → ∀ rem c0 r0, enc ++ ['"', '"', '"'] ++ rem = c0 :: r0 →
        isModelHorizWs c0 = false ∧ c0 ≠ '\n') := by
  intro fl at_ qr cs atoms
  induction atoms generalizing fl at_ qr cs with
  | nil =>
    intro enc h
    cases cs with
    | nil =>
      simp only [renderMultilineAtoms, Option.some.injEq] at h; subst h
      refine ⟨(fun _ => rfl), (fun h => nomatch h), (fun _ _ h => nomatch h), (fun _ _ h => nomatch h), ?_⟩
      intro _ _ c0 _ hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr; decide
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
        if h1 : (fl && c == '\n') = true then simp [h1] at h else
        if h2 : (at_ && (isModelHorizWs c || c == '\n')) = true then simp [h1, h2] at h else
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hcq : (c == '"') = true
        · simp only [hcq, ↓reduceIte] at h
          have hc_eq : c = '"' := eq_of_beq hcq; subst hc_eq
          split at h
          · cases h
          · rename_i hqr_lt
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
            rcases h with ⟨rest, hrest, rfl⟩
            obtain ⟨ih_nil, _, ih_q2, _, _⟩ := ih false false (qr + 1) cs' rest hrest
            refine ⟨(fun h => nomatch h), (fun h => by injection h with _ hr0; rw [ih_nil hr0]),
              (fun hge => absurd hge hqr_lt), (fun _ r hr => ?_), ?_⟩
            · injection hr with _ hr1
              exact ih_q2 (by omega) _ hr1
            · intro _ _ c0 _ hcr
              injection hcr with hc0; subst hc0; decide
        · simp only [hcq, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          have hc_ne : c ≠ '"' := fun heq => hcq (beq_iff_eq.mpr heq)
          rcases h with ⟨rest, _, rfl⟩
          refine ⟨(fun h => nomatch h), (fun h => by injection h with h0 _; exact absurd h0 hc_ne),
            (fun _ _ hr => by injection hr with h0 _; exact hc_ne h0),
            (fun _ _ hr => by injection hr with h0 _; exact hc_ne h0), ?_⟩
          intro hat_t _ c0 _ hcr
          injection hcr with hc0 _; subst hc0
          simp only [hat_t, Bool.true_and, Bool.or_eq_true, not_or, beq_iff_eq] at h2
          exact ⟨Bool.eq_false_iff.mpr h2.1, h2.2⟩
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
            rcases h with ⟨rest, _, rfl⟩
            obtain ⟨escBody, hesc, _⟩ := readBasicEscape_renderBasicEscapeChars hd []
            rw [hesc]
            refine ⟨(fun h => nomatch h), (fun h => by injection h with h0 _; cases h0),
              (fun _ _ hr => by injection hr with h0 _; cases h0),
              (fun _ _ hr => by injection hr with h0 _; cases h0), ?_⟩
            intro _ _ c0 _ hcr; simp only [List.cons_append, List.cons.injEq] at hcr
            rcases hcr with ⟨rfl, _⟩; decide
          · cases h
    | lineTrim ws1 ws2 =>
      simp only [renderMultilineAtoms] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨rest, _, rfl⟩
        refine ⟨(fun h => nomatch h), (fun h => by injection h with h0 _; cases h0),
          (fun _ _ hr => by injection hr with h0 _; cases h0),
          (fun _ _ hr => by injection hr with h0 _; cases h0), ?_⟩
        intro _ _ c0 _ hcr; simp only [List.cons_append, List.cons.injEq] at hcr
        rcases hcr with ⟨rfl, _⟩; decide
      · cases h

theorem readMlBasicBody_atoms :
    ∀ (fl at_ : Bool) (qr : Nat) (cs : List Char) (atoms : List MultilineBasicAtom) (enc rem : List Char),
      renderMultilineAtoms fl at_ qr cs atoms = some enc →
      (∀ c r, rem = c :: r → c ≠ '"') →
      readMlBasicBody (enc ++ ['"', '"', '"'] ++ rem) = some (cs, rem) := by
  intro fl at_ qr cs atoms
  induction atoms generalizing fl at_ qr cs with
  | nil =>
    intro enc rem h hrem
    cases cs with
    | nil =>
      simp only [renderMultilineAtoms, Option.some.injEq] at h; subst h
      exact readMlBasicBody_close3 hrem
    | cons _ _ => simp [renderMultilineAtoms] at h
  | cons atom atoms ih_atoms =>
    intro enc rem h hrem
    cases atom with
    | plain =>
      cases cs with
      | nil => simp [renderMultilineAtoms] at h
      | cons c cs' =>
        simp only [renderMultilineAtoms] at h
        if hc : (c == '\\' || c == '\r' || isDisallowedControl c) = true then simp [hc] at h else
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
        have hbs : c ≠ '\\' := by intro heq; subst heq; simp at hc
        if h1 : (fl && c == '\n') = true then simp [h1] at h else
        if h2 : (at_ && (isModelHorizWs c || c == '\n')) = true then simp [h1, h2] at h else
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hcq : (c == '"') = true
        · simp only [hcq, ↓reduceIte] at h
          have hc_eq : c = '"' := eq_of_beq hcq; subst hc_eq
          split at h
          · cases h
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
            rcases h with ⟨rest, hrest, rfl⟩
            obtain ⟨hnil, hsingle, _, hno2, _⟩ := mlAtoms_props false false (qr + 1) cs' atoms rest hrest
            have ih := ih_atoms false false (qr + 1) cs' rest rem hrest hrem
            rcases rest with _ | ⟨c1, _ | ⟨c2, rtail⟩⟩
            · rw [hnil rfl]; exact readMlBasicBody_close4 hrem
            · by_cases hc1 : c1 = '"'
              · subst hc1; rw [hsingle rfl]; exact readMlBasicBody_close5 hrem
              · have hn3 : ¬('"' = '"' ∧ ∃ t, (c1 :: ['"', '"', '"'] ++ rem) = '"' :: '"' :: t) := by
                  rintro ⟨_, t, ht⟩; simp only [List.cons_append, List.cons.injEq] at ht; exact hc1 ht.1
                change readMlBasicBody ('"' :: (c1 :: ['"', '"', '"'] ++ rem)) = _
                rw [mlBasicStep_not_quote3 hbs hn3]; simpa using ih
            · have hn3 : ¬('"' = '"' ∧ ∃ t, (c1 :: c2 :: rtail ++ ['"', '"', '"'] ++ rem) = '"' :: '"' :: t) := by
                rintro ⟨_, t, ht⟩
                simp only [List.cons_append, List.cons.injEq] at ht
                exact hno2 (by omega) rtail (by rw [ht.1, ht.2.1])
              change readMlBasicBody ('"' :: (c1 :: c2 :: rtail ++ ['"', '"', '"'] ++ rem)) = _
              rw [mlBasicStep_not_quote3 hbs hn3]; simpa [List.cons_append, List.append_assoc] using ih
        · simp only [hcq, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          have hc_ne : c ≠ '"' := fun heq => hcq (beq_iff_eq.mpr heq)
          rcases h with ⟨rest, hrest, rfl⟩
          have ih := ih_atoms false false 0 cs' rest rem hrest hrem
          have hn3 : ¬(c = '"' ∧ ∃ t, (rest ++ ['"', '"', '"'] ++ rem) = '"' :: '"' :: t) :=
            fun ⟨heq, _⟩ => hc_ne heq
          change readMlBasicBody (c :: (rest ++ ['"', '"', '"'] ++ rem)) = _
          rw [mlBasicStep_not_quote3 hbs hn3, ih]; rfl
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
          · rename_i hceq
            have hc : c = c' := eq_of_beq hceq; subst hc
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
            rcases h with ⟨rest, hrest, rfl⟩
            obtain ⟨escBody, hesc, hread⟩ := readBasicEscape_renderBasicEscapeChars hd (rest ++ ['"', '"', '"'] ++ rem)
            have ih := ih_atoms false false 0 cs' rest rem hrest hrem
            have heq_in : (renderBasicEscapeChars esc ++ rest) ++ ['"', '"', '"'] ++ rem =
                '\\' :: (escBody ++ (rest ++ ['"', '"', '"'] ++ rem)) := by simp [hesc, List.append_assoc]
            rw [heq_in, readMlBasicBody_backslash, hread]; dsimp only; rw [ih]; rfl
          · cases h
    | lineTrim ws1 ws2 =>
      simp only [renderMultilineAtoms] at h
      split at h
      · rename_i hws
        simp only [Bool.and_eq_true] at hws
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨rest, hrest, rfl⟩
        obtain ⟨_, _, _, _, hat_hd⟩ := mlAtoms_props false true 0 cs atoms rest hrest
        have ih := ih_atoms false true 0 cs rest rem hrest hrem
        let tail := ws2.toList ++ (rest ++ ['"', '"', '"'] ++ rem)
        have hno_esc : readBasicEscape (ws1.toList ++ '\n' :: tail) = none := by
          cases hwl : ws1.toList with
          | nil => simp [readBasicEscape]
          | cons w ws =>
            have hmw := List.all_eq_true.mp hws.1 w (by rw [hwl]; simp)
            simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hmw
            rcases hmw with rfl | rfl <;> simp [readBasicEscape]
        have hdrop1 : dropHoriz (ws1.toList ++ '\n' :: tail) = '\n' :: tail :=
          dropHoriz_append hws.1 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)
        have hdrop2 : dropHorizAndNl tail = rest ++ ['"', '"', '"'] ++ rem :=
          dropHorizAndNl_append hws.2 (by simpa [List.append_assoc] using hat_hd rfl rem)
        have hassoc : ('\\' :: ws1.toList ++ '\n' :: ws2.toList ++ rest) ++ ['"', '"', '"'] ++ rem =
            '\\' :: (ws1.toList ++ '\n' :: tail) := by
          dsimp only [tail]; simp [List.append_assoc]
        rw [hassoc, readMlBasicBody_backslash, hno_esc, hdrop1]
        have hm : (match '\n' :: tail with | '\n' :: afterNl => readMlBasicBody (dropHorizAndNl afterNl) | _ => none) =
            readMlBasicBody (dropHorizAndNl tail) := rfl
        rw [hm, hdrop2]; dsimp only; exact ih
      · cases h

theorem readMlBasicBody_escapeBasicBody (s : String) (rem : List Char)
    (hrem : ∀ c r, rem = c :: r → c ≠ '"') :
    readMlBasicBody ((escapeBasicBody true s).toList ++ ['"', '"', '"'] ++ rem) = some (s.toList, rem) := by
  have heq : (escapeBasicBody true s).toList = s.toList.flatMap (fun c => (escapeBasicChar true c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  rw [heq]
  induction s.toList with
  | nil => exact readMlBasicBody_close3 hrem
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc]
    rcases escapeBasicChar_atom true c with ⟨hc_eq, hq, hbs, _, _, _⟩ | ⟨esc, hd, hesc_eq⟩
    · rw [hc_eq, List.singleton_append]
      have hn3 : ¬(c = '"' ∧ ∃ t, (cs.flatMap (fun x => (escapeBasicChar true x).toList) ++ ['"', '"', '"'] ++ rem) = '"' :: '"' :: t) :=
        fun ⟨heq', _⟩ => hq heq'
      rw [← List.append_assoc]
      change readMlBasicBody (c :: (cs.flatMap (fun x => (escapeBasicChar true x).toList) ++ ['"', '"', '"'] ++ rem)) = _
      rw [mlBasicStep_not_quote3 hbs hn3, ih]; rfl
    · obtain ⟨escBody, hrend, hread⟩ := readBasicEscape_renderBasicEscapeChars hd
        (cs.flatMap (fun x => (escapeBasicChar true x).toList) ++ ['"', '"', '"'] ++ rem)
      have heq_in : ((escapeBasicChar true c).toList ++ cs.flatMap (fun x => (escapeBasicChar true x).toList)) ++ (['"', '"', '"'] ++ rem) =
          '\\' :: (escBody ++ (cs.flatMap (fun x => (escapeBasicChar true x).toList) ++ ['"', '"', '"'] ++ rem)) := by
        simp [hesc_eq, hrend, List.append_assoc]
      rw [heq_in, readMlBasicBody_backslash, hread]
      dsimp only; rw [ih]; rfl

end LeanSwe.Toml.Proofs
