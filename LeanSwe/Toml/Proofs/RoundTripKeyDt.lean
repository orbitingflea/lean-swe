import LeanSwe.Toml.Proofs.RoundTripStr

/-!
# Dotted-Key, String-Literal, and DateTime Render-to-Parse Soundness (`RoundTripKeyDt`)

Connects `renderDottedKey`, `renderStringLiteral`, `renderDate`, `renderTime`, and `renderOffset`
to `Impl.parseDottedKey`, `Impl.parseValueFuel`, `Impl.parseDatePart`, `Impl.parseTimePart`, and
`Impl.parseOffsetPart`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

/-- Every `DottedKeyTape` rendered by `Model.renderDottedKey` parses cleanly via `Impl.parseDottedKey`. -/
theorem renderDottedKey_parseDottedKey {dk : DottedKeyTape} {rdk wsAfter : String} {rem : List Char}
    (hr : renderDottedKey dk = some rdk) (hws : isHorizWsStr wsAfter = true)
    (hrem : ∀ c r, rem = c :: r → isModelHorizWs c = false ∧ isBareKeyChar c = false ∧ c ≠ '.' ∧ c ≠ '"' ∧ c ≠ '\'') :
    CleanNorm rdk.toList ∧ rdk.toList ≠ [] ∧
    parseDottedKey (rdk.toList ++ wsAfter.toList ++ rem) = .ok (dk.path, rem) := by
  simp only [renderDottedKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
  rcases hr with ⟨rk0, hrk0, tail0, htail0, rfl⟩
  suffices hmain : ∀ (k0 : String) (s0 : KeyStyle) (segs : List DottedSegCont) (rk tl : String),
      renderKey k0 s0 = some rk → renderDottedKeyCont segs = some tl →
      CleanNorm (rk ++ tl).toList ∧ (rk ++ tl).toList ≠ [] ∧
      (1 + segs.length ≤ (rk ++ tl).toList.length) ∧
      ∀ fuel, 1 + segs.length ≤ fuel →
        parseDottedKeyFuel fuel ((rk ++ tl).toList ++ wsAfter.toList ++ rem) =
          .ok (k0 :: segs.map DottedSegCont.key, rem) by
    obtain ⟨hcl, hne, hlen, hf⟩ := hmain dk.firstKey dk.firstStyle dk.rest rk0 tail0 hrk0 htail0
    refine ⟨hcl, hne, ?_⟩
    unfold parseDottedKey
    exact hf _ (by simp only [List.length_append] at *; omega)
  intro k0 s0 segs
  induction segs generalizing k0 s0 with
  | nil =>
    intro rk tl hrk htl
    simp only [renderDottedKeyCont, Option.some.injEq] at htl; subst htl
    rw [String.append_empty]
    have hrem_seg : ∀ c r, wsAfter.toList ++ rem = c :: r → isBareKeyChar c = false ∧ c ≠ '"' ∧ c ≠ '\'' := by
      intro c r hcr
      cases hwl : wsAfter.toList with
      | nil => rw [hwl, List.nil_append] at hcr; obtain ⟨_, hb, _, hq1, hq2⟩ := hrem c r hcr; exact ⟨hb, hq1, hq2⟩
      | cons w ws =>
        rw [hwl, List.cons_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr
        have hmw := List.all_eq_true.mp hws w (by rw [hwl]; simp)
        simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hmw
        rcases hmw with rfl | rfl <;> decide
    obtain ⟨hcl_rk, hne_rk, hp_seg⟩ := renderKey_parseKeySegment hrk hrem_seg
    have hpos_rk : 1 + ([] : List DottedSegCont).length ≤ rk.toList.length := by
      cases h : rk.toList with
      | nil => exact absurd h hne_rk
      | cons _ _ => simp +arith
    refine ⟨hcl_rk, hne_rk, hpos_rk, fun fuel hf => ?_⟩
    cases fuel with | zero => omega | succ f =>
    rw [List.append_assoc]
    unfold parseDottedKeyFuel
    simp only [bind, Except.bind, hp_seg, skipHorizWs_eq_dropHoriz, dropHoriz_append hws (fun c r h => (hrem c r h).1)]
    cases rem with
    | nil => rfl
    | cons c r =>
      have hnd := (hrem c r rfl).2.2.1
      split
      · rename_i r3 heq; exact absurd (List.cons.inj heq).1 hnd
      · rfl
  | cons seg rest ih =>
    intro rk tl hrk htl
    unfold renderDottedKeyCont at htl; split at htl <;> try (simp at htl; done)
    rename_i hws_seg; simp at hws_seg
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htl
    rcases htl with ⟨rk1, hrk1, tl1, htl1, rfl⟩
    have hrem_seg : ∀ c r, (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1).toList ++ wsAfter.toList ++ rem = c :: r →
        isBareKeyChar c = false ∧ c ≠ '"' ∧ c ≠ '\'' := by
      intro c r hcr
      simp only [String.toList_append, List.append_assoc, show ("." : String).toList = ['.'] from rfl, List.cons_append, List.nil_append] at hcr
      cases hwl : seg.wsBeforeDot.toList with
      | nil => rw [hwl, List.nil_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr; decide
      | cons w ws =>
        rw [hwl, List.cons_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr
        have hmw := List.all_eq_true.mp hws_seg.1 w (by rw [hwl]; simp)
        simp only [isModelHorizWs, Bool.or_eq_true, beq_iff_eq] at hmw
        rcases hmw with rfl | rfl <;> decide
    obtain ⟨hcl0, hne0, hp0⟩ := renderKey_parseKeySegment hrk hrem_seg
    obtain ⟨hcl_r, _, hlen_r, ih_f⟩ := ih seg.key seg.style rk1 tl1 hrk1 htl1
    obtain ⟨_, _, c1, r1', hrk1_l, hc1⟩ := readKeySeg_renderKey (rem := []) hrk1 (fun _ _ e => nomatch e)
    have hcl_all : CleanNorm (rk ++ (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1)).toList := by
      simp only [String.toList_append, List.append_assoc] at hcl_r ⊢
      exact cleanNorm_append.mpr ⟨hcl0, cleanNorm_append.mpr ⟨cleanNorm_horizWsStr hws_seg.1,
        cleanNorm_append.mpr ⟨by decide, cleanNorm_append.mpr ⟨cleanNorm_horizWsStr hws_seg.2, hcl_r⟩⟩⟩⟩
    have hlen_all : 1 + (seg :: rest).length ≤ (rk ++ (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1)).toList.length := by
      have hpos0 : 1 ≤ rk.toList.length := by
        cases h : rk.toList with
        | nil => exact absurd h hne0
        | cons _ _ => simp +arith
      simp only [String.toList_append, List.length_append, List.length_cons] at hlen_r ⊢
      have : ("." : String).toList.length = 1 := rfl
      omega
    refine ⟨hcl_all, by simp [String.toList_append, hne0], hlen_all, fun fuel hf => ?_⟩
    cases fuel with | zero => omega | succ f =>
    have hassoc : (rk ++ (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1)).toList ++ wsAfter.toList ++ rem =
        rk.toList ++ ((seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1).toList ++ wsAfter.toList ++ rem) := by
      simp [String.toList_append, List.append_assoc]
    rw [hassoc]
    unfold parseDottedKeyFuel
    simp only [bind, Except.bind, hp0]
    have hdrop1 : skipHorizWs ((seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1).toList ++ wsAfter.toList ++ rem) =
        '.' :: (seg.wsAfterDot.toList ++ ((rk1 ++ tl1).toList ++ wsAfter.toList ++ rem)) := by
      simp only [String.toList_append, List.append_assoc, show ("." : String).toList = ['.'] from rfl, List.cons_append, List.nil_append]
      rw [skipHorizWs_eq_dropHoriz, dropHoriz_append hws_seg.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
    rw [hdrop1]; simp only []
    have hdrop2 : skipHorizWs (seg.wsAfterDot.toList ++ ((rk1 ++ tl1).toList ++ wsAfter.toList ++ rem)) =
        (rk1 ++ tl1).toList ++ wsAfter.toList ++ rem := by
      rw [skipHorizWs_eq_dropHoriz]
      refine dropHoriz_append hws_seg.2 (fun c r hcr => ?_)
      simp only [String.toList_append, hrk1_l, List.cons_append] at hcr
      obtain ⟨rfl, _⟩ := List.cons.inj hcr; exact hc1.1
    rw [hdrop2, ih_f f (by simp at hf; omega)]; rfl

/-- Every string literal rendered by `Model.renderStringLiteral` parses cleanly via `Impl.parseValueFuel`. -/
theorem renderStringLiteral_parseValueFuel (numApi : CharNumApi) {s : String} {st : StringStyle} {rs : String}
    (hr : renderStringLiteral s st = some rs) {rem : List Char}
    (hrem : ∀ c r, rem = c :: r → c ≠ '"' ∧ c ≠ '\'') {fuel : Nat} (hf : 1 ≤ fuel) :
    CleanNorm rs.toList ∧ rs.toList ≠ [] ∧ parseValueFuel numApi fuel (rs.toList ++ rem) = .ok (.string s, rem) := by
  cases fuel with | zero => omega | succ f =>
  cases st with
  | basic atoms? =>
    cases atoms? with
    | none =>
      simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
      obtain ⟨hnoq, hp⟩ := escapeBasicBody_false_parse s
      have hnot2 : ∀ t, ((escapeBasicBody false s).toList ++ '"' :: rem) ≠ '"' :: '"' :: t := by
        intro t ht
        cases hbl : (escapeBasicBody false s).toList with
        | nil =>
          rw [hbl, List.nil_append] at ht; obtain ⟨_, ht2⟩ := List.cons.inj ht
          cases rem with | nil => nomatch ht2 | cons cr rr => exact (hrem cr rr rfl).1 (List.cons.inj ht2).1
        | cons b0 bs => rw [hbl, List.cons_append] at ht; exact hnoq b0 bs hbl (List.cons.inj ht).1
      refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, cleanNorm_escapeBasicBody false s⟩, by decide⟩,
        by simp [String.toList_append], ?_⟩
      simp only [String.toList_append, show ("\"" : String).toList = ['"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      have hstep : parseValueFuel numApi (f + 1) ('"' :: ((escapeBasicBody false s).toList ++ '"' :: rem)) =
          (parseBasicStringBody ((escapeBasicBody false s).toList ++ '"' :: rem) >>= fun (s', af) => .ok (.string s', af)) := by
        simp [parseValueFuel]
      rw [hstep, hp]; rfl
    | some atoms =>
      simp only [renderStringLiteral, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨enc, henc, rfl⟩
      obtain ⟨hcl_enc, hnoq, hp_f⟩ := renderBasicAtoms_parse s.toList atoms enc henc
      have hnot2 : ∀ t, (enc ++ '"' :: rem) ≠ '"' :: '"' :: t := by
        intro t ht
        cases hel : enc with
        | nil =>
          rw [hel, List.nil_append] at ht; obtain ⟨_, ht2⟩ := List.cons.inj ht
          cases rem with | nil => nomatch ht2 | cons cr rr => exact (hrem cr rr rfl).1 (List.cons.inj ht2).1
        | cons b0 bs => rw [hel, List.cons_append] at ht; exact hnoq b0 bs hel (List.cons.inj ht).1
      refine ⟨by simp only [String.toList_append, String.toList_ofList]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hcl_enc⟩, by decide⟩,
        by simp [String.toList_append], ?_⟩
      simp only [String.toList_append, String.toList_ofList, show ("\"" : String).toList = ['"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      have hstep : parseValueFuel numApi (f + 1) ('"' :: (enc ++ '"' :: rem)) =
          (parseBasicStringBody (enc ++ '"' :: rem) >>= fun (s', af) => .ok (.string s', af)) := by
        simp [parseValueFuel]
      rw [hstep]
      have hp_b : parseBasicStringBody (enc ++ '"' :: rem) = .ok (s, rem) := by
        unfold parseBasicStringBody
        simpa [String.ofList_toList] using hp_f ((enc ++ '"' :: rem).length + 1) [] rem (by simp only [List.length_append, List.length_cons]; omega)
      rw [hp_b]; rfl
  | multilineBasic custom? =>
    cases custom? with
    | none =>
      simp only [renderStringLiteral, Option.some.injEq] at hr; subst hr
      refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, cleanNorm_escapeBasicBody true s⟩, by decide⟩,
        by simp [String.toList_append], ?_⟩
      simp only [String.toList_append, show ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] from rfl,
        show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      let body := (escapeBasicBody true s).toList ++ ('"' :: '"' :: '"' :: rem)
      have hread := readMlBasicBody_escapeBasicBody s rem (fun c r h => (hrem c r h).1)
      have hp_m := readMlBasicBody_imp_parse (body.length + 1) body s.toList rem []
        (by simpa [body, List.append_assoc] using hread) (Nat.le_refl _)
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hp_m
      simp only [parseValueFuel, parseMultilineBasicString, bind, Except.bind]
      rw [hp_m]
    | some pair =>
      rcases pair with ⟨leadNl, atoms⟩
      simp only [renderStringLiteral, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨enc, henc, rfl⟩
      have hcl_enc := cleanNorm_renderMultilineAtoms (!leadNl) false 0 s.toList atoms enc henc
      have hread := readMlBasicBody_atoms (!leadNl) false 0 s.toList atoms enc rem henc (fun c r h => (hrem c r h).1)
      let body := enc ++ ('"' :: '"' :: '"' :: rem)
      have hp_m := readMlBasicBody_imp_parse (body.length + 1) body s.toList rem [] (by simpa [body, List.append_assoc] using hread) (Nat.le_refl _)
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hp_m
      cases leadNl with
      | true =>
        refine ⟨by simp only [↓reduceIte, String.toList_append, String.toList_ofList]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hcl_enc⟩, by decide⟩,
          by simp [String.toList_append], ?_⟩
        simp only [↓reduceIte, String.toList_append, String.toList_ofList,
          show ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] from rfl,
          show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
        simp only [parseValueFuel, parseMultilineBasicString, bind, Except.bind]
        rw [hp_m]
      | false =>
        refine ⟨by simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append, String.toList_ofList]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hcl_enc⟩, by decide⟩,
          by simp [String.toList_append], ?_⟩
        have hno_nl : ∀ r', body ≠ '\n' :: r' := by
          intro r' hr'
          dsimp only [body] at hr'
          cases atoms with
          | nil =>
            cases hsl : s.toList with
            | nil => rw [hsl] at henc; injection henc with e; subst e; nomatch hr'
            | cons _ _ => rw [hsl] at henc; nomatch henc
          | cons a0 as =>
            cases a0 with
            | plain =>
              cases hsl : s.toList with
              | nil => rw [hsl] at henc; simp [renderMultilineAtoms] at henc
              | cons c0 cs0 =>
                rw [hsl] at henc; unfold renderMultilineAtoms at henc
                if hc : (c0 == '\\' || c0 == '\r' || isDisallowedControl c0) = true then simp [hc] at henc else
                simp only [hc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and] at henc
                split at henc
                · cases henc
                · rename_i hnl_ne
                  split at henc
                  · cases henc
                  · split at henc
                    · split at henc
                      · nomatch henc
                      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                        rcases henc with ⟨_, _, rfl⟩; exact hnl_ne (beq_iff_eq.mpr (List.cons.inj hr').1)
                    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                      rcases henc with ⟨_, _, rfl⟩; exact hnl_ne (beq_iff_eq.mpr (List.cons.inj hr').1)
            | escape esc =>
              cases hsl : s.toList with
              | nil => rw [hsl] at henc; simp [renderMultilineAtoms] at henc
              | cons c0 cs0 =>
                rw [hsl] at henc; unfold renderMultilineAtoms at henc
                cases hd : decodeBasicEscape esc with
                | none => simp [hd] at henc
                | some c' =>
                  simp only [hd] at henc; split at henc <;> try (simp at henc; done)
                  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                  rcases henc with ⟨_, _, rfl⟩
                  obtain ⟨_, hr0, _⟩ := readBasicEscape_renderBasicEscapeChars hd []
                  rw [hr0] at hr'; nomatch hr'
            | lineTrim _ _ =>
              simp only [renderMultilineAtoms] at henc; split at henc
              · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at henc
                rcases henc with ⟨_, _, rfl⟩; nomatch hr'
              · nomatch henc
        rcases hbl : body with _ | ⟨b0, bs⟩
        · simp [body] at hbl
        · have hb0 : b0 ≠ '\n' := fun e => hno_nl bs (by rw [hbl, e])
          dsimp only [body] at hbl hp_m
          simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append, String.toList_ofList,
            show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
          rw [hbl] at hp_m ⊢
          simp only [List.length_cons] at hp_m
          simp [parseValueFuel, parseMultilineBasicString, hb0, hp_m, bind, Except.bind]
  | literal =>
    simp only [renderStringLiteral] at hr; split at hr <;> try (simp at hr; done)
    rename_i hcond; injection hr with hrs; subst hrs
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    have hnq : '\'' ∉ s.toList := by simpa [String.contains_char_eq] using hcond.2
    have hnl : '\n' ∉ s.toList := fun hm => by have h1 := List.all_eq_true.mp hcond.1 '\n' hm; simp at h1
    have hcl_s : CleanNorm s.toList := List.all_eq_true.mpr fun c hc => by
      have h1 := List.all_eq_true.mp hcond.1 c hc; simp only [Bool.and_eq_true] at h1 ⊢; exact ⟨h1.1.1, h1.2⟩
    have hnot2 : ∀ t, (s.toList ++ '\'' :: rem) ≠ '\'' :: '\'' :: t := by
      intro t ht
      cases hsl : s.toList with
      | nil =>
        rw [hsl, List.nil_append] at ht; obtain ⟨_, ht2⟩ := List.cons.inj ht
        cases rem with | nil => nomatch ht2 | cons cr rr => exact (hrem cr rr rfl).2 (List.cons.inj ht2).1
      | cons c0 cs0 => rw [hsl, List.cons_append] at ht; exact hnq (by rw [hsl, (List.cons.inj ht).1]; simp)
    refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hcl_s⟩, by decide⟩,
      by simp [String.toList_append], ?_⟩
    simp only [String.toList_append, show ("'" : String).toList = ['\''] from rfl, List.cons_append, List.nil_append, List.append_assoc]
    have hstep : parseValueFuel numApi (f + 1) ('\'' :: (s.toList ++ '\'' :: rem)) =
        (parseLiteralStringBody [] (s.toList ++ '\'' :: rem) >>= fun (s', af) => .ok (.string s', af)) := by
      simp [parseValueFuel]
    rw [hstep, parseLiteralStringBody_append s.toList [] rem hnl hnq]
    simp [String.ofList_toList, bind, Except.bind]
  | multilineLiteral leadNl =>
    simp only [renderStringLiteral] at hr; split at hr <;> try (simp at hr; done)
    rename_i hcond; injection hr with hrs; subst hrs
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    rcases hcond with ⟨⟨hclean, hlead⟩, hno_sub⟩
    have hno3 := no_triple_single_quote_of_not_containsSubstr s hno_sub
    let body := s.toList ++ ('\'' :: '\'' :: '\'' :: rem)
    have hread := readMlLiteralBody_list s.toList rem hno3 (fun c r h => (hrem c r h).2)
    have hp_m := readMlLiteralBody_imp_parse (body.length + 1) body s.toList rem [] (by simpa [body, List.append_assoc] using hread) (Nat.le_refl _)
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hp_m
    cases leadNl with
    | true =>
      refine ⟨by simp only [↓reduceIte, String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hclean⟩, by decide⟩,
        by simp [String.toList_append], ?_⟩
      simp only [↓reduceIte, String.toList_append,
        show ("'''\n" : String).toList = ['\'', '\'', '\'', '\n'] from rfl,
        show ("'''" : String).toList = ['\'', '\'', '\''] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      simp only [parseValueFuel, parseMultilineLiteralString, bind, Except.bind]
      rw [hp_m]
    | false =>
      refine ⟨by simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hclean⟩, by decide⟩,
        by simp [String.toList_append], ?_⟩
      simp only [Bool.false_or, bne_iff_ne] at hlead
      have hno_nl : ∀ r', body ≠ '\n' :: r' := by
        intro r' hr'; dsimp only [body] at hr'
        cases hsl : s.toList with
        | nil => simp [hsl] at hr'
        | cons c0 cs0 => rw [hsl, List.cons_append] at hr'; exact hlead (by simp [hsl, (List.cons.inj hr').1])
      rcases hbl : body with _ | ⟨b0, bs⟩
      · simp [body] at hbl
      · have hb0 : b0 ≠ '\n' := fun e => hno_nl bs (by rw [hbl, e])
        dsimp only [body] at hbl hp_m
        simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append,
          show ("'''" : String).toList = ['\'', '\'', '\''] from rfl, List.cons_append, List.nil_append, List.append_assoc]
        rw [hbl] at hp_m ⊢
        simp only [List.length_cons] at hp_m
        simp [parseValueFuel, parseMultilineLiteralString, hb0, hp_m, bind, Except.bind]

private theorem dite_trueR {α : Type} {P : Prop} [Decidable P] {f : P → α} {g : ¬ P → α} (h : P) :
    dite P f g = f h := by split <;> first | rfl | contradiction

private theorem twoDigits_padNatZeroR (n : Nat) (hn : n < 100) :
    ∃ c1 c2, (padNatZero 2 n).toList = [c1, c2] ∧ twoDigitsNat? c1 c2 = some n ∧
      isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true := by
  obtain ⟨hd, hf, hl⟩ := padNatZero_props 2 n
  have hlen := hl (by decide) (by change n < 100; omega)
  rcases hcs : (padNatZero 2 n).toList with _ | ⟨c1, _ | ⟨c2, _ | _⟩⟩ <;> rw [hcs] at hlen <;> try simp at hlen
  rw [hcs] at hd hf
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.foldl_cons, List.foldl_nil,
    Nat.zero_mul, Nat.zero_add, show '0'.toNat = 48 from rfl] at hd hf
  exact ⟨c1, c2, rfl, by simp [twoDigitsNat?, show isAsciiDigit = isAsciiDigitModel from rfl, hd.1, hd.2, digitVal, hf], hd.1, hd.2⟩

private theorem fourDigits_padNatZeroR (y : Nat) (hy : y < 10000) :
    ∃ c1 c2 c3 c4, (padNatZero 4 y).toList = [c1, c2, c3, c4] ∧ fourDigitsNat? c1 c2 c3 c4 = some y ∧
      isAsciiDigit c1 = true ∧ isAsciiDigit c2 = true ∧ isAsciiDigit c3 = true ∧ isAsciiDigit c4 = true := by
  obtain ⟨hd, hf, hl⟩ := padNatZero_props 4 y
  have hlen := hl (by decide) (by change y < 10000; omega)
  rcases hcs : (padNatZero 4 y).toList with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | _⟩⟩⟩⟩ <;> rw [hcs] at hlen <;> try simp at hlen
  rw [hcs] at hd hf
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.foldl_cons, List.foldl_nil,
    Nat.zero_mul, Nat.zero_add, show '0'.toNat = 48 from rfl] at hd hf
  exact ⟨c1, c2, c3, c4, rfl, by simp [fourDigitsNat?, show isAsciiDigit = isAsciiDigitModel from rfl, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, digitVal, hf],
    hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩

private theorem cleanNorm_digits {cs : List Char} (h : cs.all isAsciiDigitModel = true) : CleanNorm cs := by
  apply List.all_eq_true.mpr; intro c hc
  have hd := List.all_eq_true.mp h c hc
  have h1 : '0' ≤ c ∧ c ≤ '9' := by simpa [isAsciiDigitModel] using hd
  have := UInt32.le_iff_toNat_le.mp h1.1; have := UInt32.le_iff_toNat_le.mp h1.2
  have : '0'.val.toNat = 48 := rfl; have : '9'.val.toNat = 57 := rfl; have : c.toNat = c.val.toNat := rfl
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
  refine ⟨by simp [isDisallowedControl]; omega, fun h0 => by subst h0; revert hd; decide⟩

/-- `Model.renderDate` outputs parse cleanly via `Impl.parseDatePart`. -/
theorem renderDate_parseDatePart {d : Std.Time.PlainDate} {ds : String} (hr : renderDate d = some ds) :
    CleanNorm ds.toList ∧
    ∀ rest, parseDatePart (ds.toList ++ rest) = .ok (d, rest) ∧ hasDatePrefix (ds.toList ++ rest) = true := by
  simp only [renderDate] at hr; split at hr <;> try (simp at hr; done)
  rename_i hvd; injection hr with hds; subst hds
  have hv_lo : @LE.le Int _ 0 d.year := (decide_eq_true_eq.mp hvd).1
  have hv_hi : @LE.le Int _ d.year 9999 := (decide_eq_true_eq.mp hvd).2
  have hn_eq : Int.ofNat d.year.toNat = (d.year : Int) := Int.toNat_of_nonneg hv_lo
  have hy_nat : d.year.toNat < 10000 := by omega
  have hm_prop := d.month.property; have hd_prop := d.day.property
  obtain ⟨y1, y2, y3, y4, hy_l, hy_f, ay1, ay2, ay3, ay4⟩ := fourDigits_padNatZeroR d.year.toNat hy_nat
  obtain ⟨m1, m2, hm_l, hm_t, am1, am2⟩ := twoDigits_padNatZeroR d.month.val.toNat (by omega)
  obtain ⟨d1, d2, hd_l, hd_t, ad1, ad2⟩ := twoDigits_padNatZeroR d.day.val.toNat (by omega)
  have hlist : (padNatZero 4 d.year.toNat ++ "-" ++ padNatZero 2 d.month.val.toNat ++ "-" ++ padNatZero 2 d.day.val.toNat).toList =
      [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] := by
    simp only [String.toList_append, hy_l, hm_l, hd_l, show ("-" : String).toList = ['-'] from rfl]; rfl
  have hm_ok : d.month.val.toNat ≥ 1 ∧ d.month.val.toNat ≤ 12 := ⟨by omega, by omega⟩
  have hd_ok : d.day.val.toNat ≥ 1 ∧ d.day.val.toNat ≤ 31 := ⟨by omega, by omega⟩
  have hcal : Std.Time.PlainDate.ofYearMonthDay? (Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat))
      (Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok) (Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok) = some d := by
    rw [show Std.Time.Year.Offset.ofInt (Int.ofNat d.year.toNat) = d.year from hn_eq,
      show Std.Time.Month.Ordinal.ofNat d.month.val.toNat hm_ok = d.month from Subtype.ext (Int.toNat_of_nonneg (by omega)),
      show Std.Time.Day.Ordinal.ofNat d.day.val.toNat hd_ok = d.day from Subtype.ext (Int.toNat_of_nonneg (by omega)),
      Std.Time.PlainDate.ofYearMonthDay?]
    exact dite_trueR d.valid
  refine ⟨by
      simp only [String.toList_append]
      exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
        ⟨cleanNorm_append.mpr ⟨cleanNorm_digits (padNatZero_props 4 _).1, by decide⟩,
          cleanNorm_digits (padNatZero_props 2 _).1⟩, by decide⟩,
        cleanNorm_digits (padNatZero_props 2 _).1⟩,
    fun rest => ⟨?_, by rw [hlist]; simp [hasDatePrefix, ay1, ay2, ay3, ay4, am1, am2, ad1, ad2]⟩⟩
  rw [hlist]; simp only [List.cons_append, List.nil_append, parseDatePart, hy_f, hm_t, hd_t]
  rw [dite_trueR hm_ok, dite_trueR hd_ok, hcal]; simp [hvd]

private theorem takeDigits_appendR :
    ∀ (ds acc rest : List Char), ds.all isAsciiDigitModel = true →
      (∀ c r, rest = c :: r → isAsciiDigit c = false) →
      takeDigits acc (ds ++ rest) = (acc.reverse ++ ds, rest)
  | [], acc, [], _, _ => by simp [takeDigits]
  | [], acc, c :: r, _, hrest => by simp [takeDigits, hrest c r rfl]
  | d :: ds, acc, rest, hds, hrest => by
    simp only [List.all_cons, Bool.and_eq_true] at hds
    have hd : isAsciiDigit d = true := hds.1
    simp [takeDigits, hd, takeDigits_appendR ds (d :: acc) rest hds.2 hrest, List.reverse_cons, List.append_assoc]

private theorem fracDigitsToNanos_eq_model (ds : List Char) :
    fracDigitsToNanos ds = fracDigitsToNanosModel ds := by
  have haux : ∀ k acc l, fracDigitsToNanosAux k acc l = fracDigitsToNanosAuxModel k acc l := by
    intro k; induction k with
    | zero => intro _ _; rfl
    | succ k ih => intro acc l; cases l <;> exact ih _ _
  simp [fracDigitsToNanos, fracDigitsToNanosModel, haux]

/-- `Model.renderTime` outputs parse cleanly via `Impl.parseTimePart`. -/
theorem renderTime_parseTimePart {t : Std.Time.PlainTime} {fl : Option String} {ts : String}
    (hr : renderTime t fl = some ts) :
    CleanNorm ts.toList ∧
    ∀ rest, (∀ c r, rest = c :: r → isAsciiDigit c = false ∧ c ≠ '.') →
      parseTimePart (ts.toList ++ rest) = .ok (t, rest) ∧ hasTimePrefix (ts.toList ++ rest) = true := by
  unfold renderTime at hr
  split at hr <;> try (simp at hr; done)
  rename_i hvt_not; have hvt : validTomlTime t = true := by cases h : validTomlTime t <;> simp_all
  have hvt_sec : t.second.val ≤ 59 := by simpa [validTomlTime] using hvt
  have hh_p := t.hour.property; have hm_p := t.minute.property; have hs_p := t.second.property; have hn_p := t.nanosecond.property
  obtain ⟨h1, h2, hh_l, hh_t, ah1, ah2⟩ := twoDigits_padNatZeroR t.hour.val.toNat (by omega)
  obtain ⟨m1, m2, hm_l, hm_t, am1, am2⟩ := twoDigits_padNatZeroR t.minute.val.toNat (by omega)
  obtain ⟨s1, s2, hs_l, hs_t, as1, as2⟩ := twoDigits_padNatZeroR t.second.val.toNat (by omega)
  have hh_ok : t.hour.val.toNat ≤ 23 := by omega
  have mm_ok : t.minute.val.toNat ≤ 59 := by omega
  have ss_ok : t.second.val.toNat ≤ 59 := by omega
  have mk_tm (ns : Std.Time.Nanosecond.Ordinal) (hns : ns = t.nanosecond) :
      Std.Time.PlainTime.mk (Std.Time.Hour.Ordinal.ofNat t.hour.val.toNat hh_ok)
        (Std.Time.Minute.Ordinal.ofNat t.minute.val.toNat mm_ok)
        (Std.Time.Second.Ordinal.ofNat t.second.val.toNat (Nat.le_trans ss_ok (by decide))) ns = t :=
    Std.Time.PlainTime.ext (Subtype.ext (Int.toNat_of_nonneg (by omega)))
      (Subtype.ext (Int.toNat_of_nonneg (by omega))) (Subtype.ext (Int.toNat_of_nonneg (by omega))) hns
  have hbase : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat).toList =
      [h1, h2, ':', m1, m2, ':', s1, s2] := by
    simp only [String.toList_append, hh_l, hm_l, hs_l, show (":" : String).toList = [':'] from rfl]; rfl
  have hcl_base : CleanNorm (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++ padNatZero 2 t.second.val.toNat).toList := by
    simp only [String.toList_append]
    exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr
      ⟨cleanNorm_digits (padNatZero_props 2 _).1, by decide⟩, cleanNorm_digits (padNatZero_props 2 _).1⟩, by decide⟩,
      cleanNorm_digits (padNatZero_props 2 _).1⟩
  cases fl with
  | none =>
    dsimp only at hr; split at hr <;> try (simp at hr; done)
    rename_i hn0; injection hr with hts; subst hts
    have htm := mk_tm 0 (Subtype.ext (by change (0 : Int) = t.nanosecond.val; exact (eq_of_beq hn0).symm))
    refine ⟨hcl_base, fun rest hrest => ⟨?_, by rw [hbase]; simp [hasTimePrefix, ah1, ah2, am1, am2, as1, as2]⟩⟩
    rw [hbase]
    simp only [List.cons_append, List.nil_append, parseTimePart, hh_t, hm_t, hs_t, hh_ok, mm_ok, ss_ok, ↓reduceDIte]
    split
    · rename_i _ fs; exact absurd rfl (hrest '.' fs rfl).2
    · rw [htm]
  | some ds =>
    dsimp only at hr; split at hr <;> try (simp at hr; done)
    rename_i hds_ok; injection hr with hts; subst hts
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hds_ok
    have hne_ds : ds.toList.isEmpty = false := by
      cases hdl : ds.toList with
      | nil =>
        have hds_emp : ds = "" := by rw [← String.ofList_toList (s := ds), hdl]
        rw [hds_emp] at hds_ok; nomatch hds_ok.1.1
      | cons _ _ => rfl
    have hfull : (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
        padNatZero 2 t.second.val.toNat ++ "." ++ ds).toList =
        [h1, h2, ':', m1, m2, ':', s1, s2] ++ ('.' :: ds.toList) := by
      rw [String.toList_append, String.toList_append, hbase]
      simp [show ("." : String).toList = ['.'] from rfl]
    have hcl_full : CleanNorm (padNatZero 2 t.hour.val.toNat ++ ":" ++ padNatZero 2 t.minute.val.toNat ++ ":" ++
        padNatZero 2 t.second.val.toNat ++ "." ++ ds).toList := by
      rw [String.toList_append, String.toList_append]
      exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨hcl_base, by decide⟩, cleanNorm_digits hds_ok.1.2⟩
    refine ⟨hcl_full, fun rest hrest => ⟨?_, by rw [hfull]; simp [hasTimePrefix, ah1, ah2, am1, am2, as1, as2]⟩⟩
    have htk : takeDigits [] (ds.toList ++ rest) = (ds.toList, rest) := by
      simpa using takeDigits_appendR ds.toList [] rest hds_ok.1.2 (fun c r h => (hrest c r h).1)
    let nano := fracDigitsToNanos ds.toList
    have hnano_le : nano ≤ 999999999 := Nat.min_le_left _ _
    have htm := mk_tm (Std.Time.Nanosecond.Ordinal.ofNat nano hnano_le)
      (Subtype.ext (by
        change Int.ofNat nano = t.nanosecond.val
        dsimp only [nano]
        rw [fracDigitsToNanos_eq_model, hds_ok.2]
        exact Int.toNat_of_nonneg (by omega)))
    rw [hfull]
    simp only [List.cons_append, List.nil_append, parseTimePart, hh_t, hm_t, hs_t, hh_ok, mm_ok, ss_ok, ↓reduceDIte, htk, hne_ds, Bool.false_eq_true, ↓reduceIte]
    rw [htm]

/-- `Model.renderOffset` outputs parse cleanly via `Impl.parseOffsetPart`. -/
theorem renderOffset_parseOffsetPartR {o : Std.Time.TimeZone.Offset} {style : OffsetStyle} {os : String}
    (hr : renderOffset o style = some os) :
    CleanNorm os.toList ∧ os.toList ≠ [] ∧ parseOffsetPart os.toList = .ok o ∧
    (∀ c r, os.toList = c :: r → isAsciiDigit c = false ∧ c ≠ '.') := by
  unfold renderOffset at hr
  split at hr <;> try (simp at hr; done)
  rename_i hvo_not; have hvo : validTomlOffset o = true := by cases h : validTomlOffset o <;> simp_all
  have hvo' : o.second.val % 60 = 0 ∧ -86340 ≤ o.second.val ∧ o.second.val ≤ 86340 := by simpa [validTomlOffset] using hvo
  by_cases hz : o.second.val = 0
  · have ho_eq : Std.Time.TimeZone.Offset.ofSeconds 0 = o :=
      Std.Time.TimeZone.Offset.ext (Std.Time.Internal.UnitVal.ext hz.symm)
    simp only [hz, beq_self_eq_true, ↓reduceIte] at hr
    cases style <;> simp only [Option.some.injEq] at hr <;> subst hr
    · exact ⟨by decide, by decide, by rw [show ("Z" : String).toList = ['Z'] from rfl, parseOffsetPart, ho_eq],
        fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide⟩
    · exact ⟨by decide, by decide, by rw [show ("z" : String).toList = ['z'] from rfl, parseOffsetPart, ho_eq],
        fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide⟩
    · have hl : ("+00:00" : String).toList = ['+', '0', '0', ':', '0', '0'] := rfl
      refine ⟨by decide, by decide, ?_, fun c r h => by rw [hl] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; decide⟩
      rw [hl, show parseOffsetPart ['+', '0', '0', ':', '0', '0'] = .ok (Std.Time.TimeZone.Offset.ofSeconds 0) by
        simp [parseOffsetPart, show twoDigitsNat? '0' '0' = some 0 from rfl, validTomlOffset]; rfl, ho_eq]
    · have hl : ("-00:00" : String).toList = ['-', '0', '0', ':', '0', '0'] := rfl
      refine ⟨by decide, by decide, ?_, fun c r h => by rw [hl] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; decide⟩
      rw [hl, show parseOffsetPart ['-', '0', '0', ':', '0', '0'] = .ok (Std.Time.TimeZone.Offset.ofSeconds 0) by
        simp [parseOffsetPart, show twoDigitsNat? '0' '0' = some 0 from rfl, validTomlOffset]; rfl, ho_eq]
  · simp only [beq_false_of_ne hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hr; subst hr
    let hh := o.second.val.natAbs / 60 / 60
    let mm := (o.second.val.natAbs / 60) % 60
    have hdiv_lt : hh ≤ 23 := by dsimp [hh]; omega
    have hmod_lt : mm ≤ 59 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
    obtain ⟨h1, h2, hh_l, hh_t, _, _⟩ := twoDigits_padNatZeroR hh (by omega)
    obtain ⟨m1, m2, hm_l, hm_t, _, _⟩ := twoDigits_padNatZeroR mm (by omega)
    have hmod60 : o.second.val.natAbs % 60 = 0 := by have := hvo'.1; omega
    have htotal : hh * 3600 + mm * 60 = o.second.val.natAbs := by dsimp [hh, mm]; omega
    have hsgn_c : (if o.second.val < 0 then "-" else "+").toList = [if decide (o.second.val < 0) then '-' else '+'] := by
      split <;> simp_all
    have hlist : ((if o.second.val < 0 then "-" else "+") ++ padNatZero 2 hh ++ ":" ++ padNatZero 2 mm).toList =
        [if decide (o.second.val < 0) then '-' else '+', h1, h2, ':', m1, m2] := by
      simp only [String.toList_append, hsgn_c, hh_l, hm_l, show (":" : String).toList = [':'] from rfl]; rfl
    have hcl_sgn : CleanNorm (if o.second.val < 0 then "-" else "+").toList := by split <;> decide
    have hcl_all : CleanNorm ((if o.second.val < 0 then "-" else "+") ++ padNatZero 2 hh ++ ":" ++ padNatZero 2 mm).toList := by
      simp only [String.toList_append]
      exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨hcl_sgn, cleanNorm_digits (padNatZero_props 2 _).1⟩, by decide⟩,
        cleanNorm_digits (padNatZero_props 2 _).1⟩
    have hne_abs : Int.ofNat o.second.val.natAbs ≠ 0 := fun h0 =>
      hz (Int.natAbs_eq_zero.mp (Int.ofNat.inj h0))
    have hsec_eq : (if Int.ofNat (hh * 3600 + mm * 60) == 0 then (0 : Int)
        else if (if decide (o.second.val < 0) then '-' else '+') == '-' then -Int.ofNat (hh * 3600 + mm * 60)
        else Int.ofNat (hh * 3600 + mm * 60)) = o.second.val := by
      rw [htotal, beq_false_of_ne hne_abs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hneg : o.second.val < 0
      · simp only [decide_eq_true hneg, ↓reduceIte, beq_self_eq_true]
        exact (congrArg Neg.neg (Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg))).trans (Int.neg_neg _)
      · simp only [decide_eq_false hneg, Bool.false_eq_true, ↓reduceIte, show ('+' == '-') = false from rfl]
        exact Int.natAbs_of_nonneg (Int.not_lt.mp hneg)
    have ho_eq : Std.Time.TimeZone.Offset.ofSeconds (Std.Time.Second.Offset.ofInt o.second.val) = o :=
      Std.Time.TimeZone.Offset.ext (Std.Time.Internal.UnitVal.ext rfl)
    refine ⟨hcl_all, by rw [hlist]; simp, ?_, fun c r hcr => by
      rw [hlist] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr; cases decide (o.second.val < 0) <;> decide⟩
    rw [hlist]
    have hsgn_ok : ((if decide (o.second.val < 0) then '-' else '+') == '+' ||
        (if decide (o.second.val < 0) then '-' else '+') == '-') = true := by
      cases decide (o.second.val < 0) <;> decide
    have hbnd_ok : (decide (hh ≤ 23) && decide (mm ≤ 59)) = true := by simp [hdiv_lt, hmod_lt]
    simp only [parseOffsetPart, hsgn_ok, hh_t, hm_t, hbnd_ok, ↓reduceIte]
    rw [hsec_eq, ho_eq, validTomlOffsetImpl_eq, hvo]; rfl

end LeanSwe.Toml.Proofs
