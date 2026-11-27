import LeanSweProofs.Toml.Proofs.RoundTripLex

/-!
# String Body & Key Segment Render-to-Parse Soundness (`RoundTripStr`)

Connects `renderBasicAtoms`, `escapeBasicBody`, literal string bodies, multiline string
decoders, and `renderKey` to `Impl.parseBasicStringBodyFuel`, `Impl.parseLiteralStringBody`,
`Impl.parseMultilineBasicBodyFuel`, `Impl.parseMultilineLiteralBodyFuel`, and `Impl.parseKeySegment`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

/-- `renderBasicAtoms` outputs parse cleanly via `Impl.parseBasicStringBodyFuel`. -/
theorem renderBasicAtoms_parse :
    ∀ (cs : List Char) (atoms : List BasicCharAtom) (enc : List Char),
      renderBasicAtoms cs atoms = some enc →
      CleanNorm enc ∧
      (∀ c r, enc = c :: r → c ≠ '"') ∧
      ∀ fuel acc rem, enc.length + 1 ≤ fuel →
        parseBasicStringBodyFuel fuel acc (enc ++ '"' :: rem) = .ok (String.ofList (acc.reverse ++ cs), rem)
  | [], [], enc, h => by
    simp only [renderBasicAtoms, Option.some.injEq] at h; subst h
    refine ⟨rfl, (fun _ _ e => nomatch e), fun fuel acc rem hf => ?_⟩
    cases fuel with | zero => omega | succ _ => simp [parseBasicStringBodyFuel]
  | c :: cs, .plain :: atoms, enc, h => by
    simp only [renderBasicAtoms] at h; split at h <;> try (simp at h; done)
    rename_i hok; simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hok
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨rest, hrest, rfl⟩
    obtain ⟨hcl_r, _, ih_p⟩ := renderBasicAtoms_parse cs atoms rest hrest
    refine ⟨cleanNorm_cons.mpr ⟨⟨hok.2, hok.1.2⟩, hcl_r⟩,
      (fun _ _ e => by obtain ⟨rfl, _⟩ := List.cons.inj e; exact hok.1.1.1.1),
      fun fuel acc rem hf => ?_⟩
    cases fuel with | zero => omega | succ f =>
    have hstep : parseBasicStringBodyFuel (f + 1) acc (c :: (rest ++ '"' :: rem)) =
        parseBasicStringBodyFuel f (c :: acc) (rest ++ '"' :: rem) := by
      have hnl := hok.1.1.2; have hq := hok.1.1.1.1; have hbs := hok.1.1.1.2
      conv => lhs; unfold parseBasicStringBodyFuel
      split <;> simp_all
    rw [List.cons_append, hstep, ih_p f (c :: acc) rem (by simp at hf; omega)]
    simp [List.reverse_cons, List.append_assoc]
  | c :: cs, .escape esc :: atoms, enc, h => by
    simp only [renderBasicAtoms] at h
    cases hd : decodeBasicEscape esc with
    | none => simp [hd] at h
    | some c' =>
      simp only [hd] at h; split at h <;> try (simp at h; done)
      rename_i hceq; have hc := eq_of_beq hceq; subst hc
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨rest, hrest, rfl⟩
      obtain ⟨hcl_r, _, ih_p⟩ := renderBasicAtoms_parse cs atoms rest hrest
      refine ⟨cleanNorm_append.mpr ⟨(cleanNorm_renderBasicEscapeChars hd).1, hcl_r⟩,
        (fun c0 r0 e => by obtain ⟨eb, hr0, _⟩ := readBasicEscape_renderBasicEscapeChars hd []; rw [hr0, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; decide),
        fun fuel acc rem hf => ?_⟩
      cases fuel with | zero => omega | succ f =>
      obtain ⟨eb, hr_eb, hrd_eb⟩ := readBasicEscape_renderBasicEscapeChars hd (rest ++ '"' :: rem)
      have hp_esc := readBasicEscape_imp_parseBasicEscape hrd_eb
      have hlen_ge : rest.length + 1 ≤ f := by
        rw [hr_eb] at hf; simp only [List.length_append, List.length_cons] at hf; omega
      simp only [hr_eb, List.cons_append, List.append_assoc, parseBasicStringBodyFuel, bind, Except.bind, hp_esc]
      simpa [List.reverse_cons, List.append_assoc] using ih_p f (c :: acc) rem hlen_ge
  | [], _ :: _, _, h => by simp [renderBasicAtoms] at h
  | _ :: _, [], _, h => by simp [renderBasicAtoms] at h

/-- Canonical `escapeBasicBody false s` parses cleanly via `Impl.parseBasicStringBody`. -/
theorem escapeBasicBody_false_parse (s : String) :
    (∀ c r, (escapeBasicBody false s).toList = c :: r → c ≠ '"') ∧
    ∀ rem, parseBasicStringBody ((escapeBasicBody false s).toList ++ '"' :: rem) = .ok (s, rem) := by
  have heq : (escapeBasicBody false s).toList = s.toList.flatMap (fun c => (escapeBasicChar false c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  have hfuel_p : ∀ (cs : List Char) (fuel : Nat) (acc rem : List Char),
      (cs.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤ fuel →
      parseBasicStringBodyFuel fuel acc (cs.flatMap (fun c => (escapeBasicChar false c).toList) ++ '"' :: rem) =
        .ok (String.ofList (acc.reverse ++ cs), rem) := by
    intro cs; induction cs with
    | nil => intro fuel acc rem hf; cases fuel with | zero => omega | succ _ => simp [parseBasicStringBodyFuel]
    | cons c cs ih =>
      intro fuel acc rem hf
      cases fuel with | zero => omega | succ f =>
      rw [List.flatMap_cons] at hf
      rw [List.flatMap_cons, List.append_assoc]
      rcases escapeBasicChar_atom false c with ⟨hc_l, hq, hbs, _, _, hnl_or⟩ | ⟨esc, hd, hesc_l⟩
      · have hnl : c ≠ '\n' := hnl_or.elim (fun h => nomatch h) id
        rw [hc_l, List.cons_append, List.nil_append]
        have hstep : parseBasicStringBodyFuel (f + 1) acc (c :: (cs.flatMap (fun x => (escapeBasicChar false x).toList) ++ '"' :: rem)) =
            parseBasicStringBodyFuel f (c :: acc) (cs.flatMap (fun x => (escapeBasicChar false x).toList) ++ '"' :: rem) := by
          conv => lhs; unfold parseBasicStringBodyFuel
          split <;> simp_all
        rw [hstep, ih f (c :: acc) rem (by rw [hc_l] at hf; simp only [List.length_append, List.length_cons] at hf; omega)]
        simp [List.reverse_cons, List.append_assoc]
      · obtain ⟨eb, hrend, hread⟩ := readBasicEscape_renderBasicEscapeChars hd
          (cs.flatMap (fun x => (escapeBasicChar false x).toList) ++ '"' :: rem)
        have hp := readBasicEscape_imp_parseBasicEscape hread
        rw [hesc_l, hrend, List.cons_append]
        simp only [parseBasicStringBodyFuel, bind, Except.bind, hp]
        rw [ih f (c :: acc) rem (by rw [hesc_l, hrend] at hf; simp only [List.length_append, List.length_cons] at hf; omega)]
        simp [List.reverse_cons, List.append_assoc]
  refine ⟨fun c r hcr => ?_, fun rem => ?_⟩
  · rw [heq] at hcr
    cases hsl : s.toList with
    | nil => simp [hsl] at hcr
    | cons c0 cs0 =>
      rw [hsl, List.flatMap_cons] at hcr
      rcases escapeBasicChar_atom false c0 with ⟨hc0, hq0, _⟩ | ⟨esc, hd, hesc0⟩
      · rw [hc0, List.cons_append, List.nil_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr; exact hq0
      · obtain ⟨_, hr0, _⟩ := readBasicEscape_renderBasicEscapeChars hd []
        rw [hesc0, hr0, List.cons_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr; decide
  · unfold parseBasicStringBody
    have hlen : (s.toList.flatMap (fun c => (escapeBasicChar false c).toList)).length + 1 ≤
        ((escapeBasicBody false s).toList ++ '"' :: rem).length + 1 := by
      rw [heq]; simp only [List.length_append, List.length_cons]; omega
    rw [heq] at hlen ⊢
    simpa [String.ofList_toList] using hfuel_p s.toList _ [] rem hlen

/-- `Impl.parseLiteralStringBody` consumes single-line literal bodies free of `'\n'` and `'\''`. -/
theorem parseLiteralStringBody_append :
    ∀ (cs acc rem : List Char), '\n' ∉ cs → '\'' ∉ cs →
      parseLiteralStringBody acc (cs ++ '\'' :: rem) = .ok (String.ofList (acc.reverse ++ cs), rem)
  | [], acc, rem, _, _ => by simp [parseLiteralStringBody]
  | c :: cs, acc, rem, hnl, hnq => by
    have hc_nl : c ≠ '\n' := fun h0 => by subst h0; exact hnl List.mem_cons_self
    have hc_q : c ≠ '\'' := fun h0 => by subst h0; exact hnq List.mem_cons_self
    have hstep : parseLiteralStringBody acc (c :: (cs ++ '\'' :: rem)) =
        parseLiteralStringBody (c :: acc) (cs ++ '\'' :: rem) := by
      conv => lhs; unfold parseLiteralStringBody
      split <;> simp_all
    rw [List.cons_append, hstep,
        parseLiteralStringBody_append cs (c :: acc) rem
          (fun hm => hnl (List.mem_cons_of_mem _ hm))
          (fun hm => hnq (List.mem_cons_of_mem _ hm))]
    simp [List.reverse_cons, List.append_assoc]

/-- `readMlBasicBody` soundness for `Impl.parseMultilineBasicBodyFuel`. -/
theorem readMlBasicBody_imp_parse (fuel : Nat) :
    ∀ (cs out rem acc : List Char),
      readMlBasicBody cs = some (out, rem) →
      cs.length + 1 ≤ fuel →
      parseMultilineBasicBodyFuel fuel acc cs = .ok (String.ofList (acc.reverse ++ out), rem) := by
  induction fuel with
  | zero => intro _ _ _ _ _ hf; omega
  | succ f ih =>
    intro cs out rem acc h hf
    match cs with
    | [] => simp [readMlBasicBody] at h
    | c :: rest =>
      by_cases hbs : c = '\\'
      · subst hbs
        cases he : readBasicEscape rest with
        | some pair =>
          rcases pair with ⟨ch, afterEsc⟩
          have hlt := readBasicEscape_len_lt he
          have hp := readBasicEscape_imp_parseBasicEscape he
          have h' : (readMlBasicBody afterEsc).map (fun (cs', r') => (ch :: cs', r')) = some (out, rem) := by
            simpa [readMlBasicBody_backslash, he] using h
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h'
          rcases h' with ⟨⟨cs', rem'⟩, hrec, rfl, rfl⟩
          simp only [parseMultilineBasicBodyFuel, hp]
          simpa [List.reverse_cons, List.append_assoc] using ih afterEsc cs' rem' (ch :: acc) hrec (by simp at hlt hf; omega)
        | none =>
          obtain ⟨err, hp_err⟩ := readBasicEscape_none_imp_err he
          have h' := h; rw [readMlBasicBody_backslash, he] at h'; dsimp only at h'
          cases hd : dropHoriz rest with
          | nil => rw [hd] at h'; nomatch h'
          | cons c0 afterNl =>
            rw [hd] at h'
            by_cases hnl : c0 = '\n'
            · subst hnl
              have hl1 := dropHoriz_len_le rest; have hl2 := dropHorizAndNl_len_le afterNl; rw [hd] at hl1
              simp only [parseMultilineBasicBodyFuel, hp_err, skipHorizWs_eq_dropHoriz, hd, skipHorizAndNl_eq_dropHorizAndNl]
              exact ih (dropHorizAndNl afterNl) out rem acc h' (by simp at hl1 hf; omega)
            · split at h'
              · rename_i heq; exact absurd (List.cons.inj heq).1 hnl
              · nomatch h'
      · by_cases hq3 : c = '"' ∧ ∃ t, rest = '"' :: '"' :: t
        · rcases hq3 with ⟨rfl, t, rfl⟩
          rcases t with _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, r6⟩⟩⟩
          · simp only [readMlBasicBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
            simp [parseMultilineBasicBodyFuel]
          · by_cases h4 : c4 = '"'
            · subst h4; simp only [readMlBasicBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
              simp [parseMultilineBasicBodyFuel, List.reverse_cons]
            · simp [readMlBasicBody, h4] at h; rcases h with ⟨rfl, rfl⟩
              simp [parseMultilineBasicBodyFuel, h4]
          · by_cases h4 : c4 = '"'
            · subst h4
              by_cases h5 : c5 = '"'
              · subst h5; simp only [readMlBasicBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
                simp [parseMultilineBasicBodyFuel, List.reverse_cons, List.append_assoc]
              · simp [readMlBasicBody, h5] at h; rcases h with ⟨rfl, rfl⟩
                simp [parseMultilineBasicBodyFuel, h5, List.reverse_cons]
            · simp [readMlBasicBody, h4] at h; rcases h with ⟨rfl, rfl⟩
              simp [parseMultilineBasicBodyFuel, h4]
          · by_cases h4 : c4 = '"'
            · subst h4
              by_cases h5 : c5 = '"'
              · subst h5
                by_cases h6 : c6 = '"'
                · subst h6; simp [readMlBasicBody] at h
                · simp [readMlBasicBody, h6] at h; rcases h with ⟨rfl, rfl⟩
                  simp [parseMultilineBasicBodyFuel, h6, List.reverse_cons, List.append_assoc]
              · simp [readMlBasicBody, h5] at h; rcases h with ⟨rfl, rfl⟩
                simp [parseMultilineBasicBodyFuel, h5, List.reverse_cons]
            · simp [readMlBasicBody, h4] at h; rcases h with ⟨rfl, rfl⟩
              simp [parseMultilineBasicBodyFuel, h4]
        · have hr_step : readMlBasicBody (c :: rest) = (readMlBasicBody rest).map fun (cs', r') => (c :: cs', r') := by
            conv => lhs; unfold readMlBasicBody
            split <;> first | simp_all | (exfalso; apply hq3; simp_all)
          have hp_step : parseMultilineBasicBodyFuel (f + 1) acc (c :: rest) = parseMultilineBasicBodyFuel f (c :: acc) rest := by
            conv => lhs; unfold parseMultilineBasicBodyFuel
            split <;> first | simp_all | (exfalso; apply hq3; simp_all)
          rw [hr_step] at h; simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          rcases h with ⟨⟨cs', rem'⟩, hrec, rfl, rfl⟩
          rw [hp_step]
          simpa [List.reverse_cons, List.append_assoc] using ih rest cs' rem' (c :: acc) hrec (by simp at hf; omega)

/-- `readMlLiteralBody` soundness for `Impl.parseMultilineLiteralBodyFuel`. -/
theorem readMlLiteralBody_imp_parse (fuel : Nat) :
    ∀ (cs out rem acc : List Char),
      readMlLiteralBody cs = some (out, rem) →
      cs.length + 1 ≤ fuel →
      parseMultilineLiteralBodyFuel fuel acc cs = .ok (String.ofList (acc.reverse ++ out), rem) := by
  induction fuel with
  | zero => intro _ _ _ _ _ hf; omega
  | succ f ih =>
    intro cs out rem acc h hf
    match cs with
    | [] => simp [readMlLiteralBody] at h
    | c :: rest =>
      by_cases hq3 : c = '\'' ∧ ∃ t, rest = '\'' :: '\'' :: t
      · rcases hq3 with ⟨rfl, t, rfl⟩
        rcases t with _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, r6⟩⟩⟩
        · simp only [readMlLiteralBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
          simp [parseMultilineLiteralBodyFuel]
        · by_cases h4 : c4 = '\''
          · subst h4; simp only [readMlLiteralBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
            simp [parseMultilineLiteralBodyFuel, List.reverse_cons]
          · simp [readMlLiteralBody, h4] at h; rcases h with ⟨rfl, rfl⟩
            simp [parseMultilineLiteralBodyFuel, h4]
        · by_cases h4 : c4 = '\''
          · subst h4
            by_cases h5 : c5 = '\''
            · subst h5; simp only [readMlLiteralBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
              simp [parseMultilineLiteralBodyFuel, List.reverse_cons, List.append_assoc]
            · simp [readMlLiteralBody, h5] at h; rcases h with ⟨rfl, rfl⟩
              simp [parseMultilineLiteralBodyFuel, h5, List.reverse_cons]
          · simp [readMlLiteralBody, h4] at h; rcases h with ⟨rfl, rfl⟩
            simp [parseMultilineLiteralBodyFuel, h4]
        · by_cases h4 : c4 = '\''
          · subst h4
            by_cases h5 : c5 = '\''
            · subst h5
              by_cases h6 : c6 = '\''
              · subst h6; simp [readMlLiteralBody] at h
              · simp [readMlLiteralBody, h6] at h; rcases h with ⟨rfl, rfl⟩
                simp [parseMultilineLiteralBodyFuel, h6, List.reverse_cons, List.append_assoc]
            · simp [readMlLiteralBody, h5] at h; rcases h with ⟨rfl, rfl⟩
              simp [parseMultilineLiteralBodyFuel, h5, List.reverse_cons]
          · simp [readMlLiteralBody, h4] at h; rcases h with ⟨rfl, rfl⟩
            simp [parseMultilineLiteralBodyFuel, h4]
      · have hr_step : readMlLiteralBody (c :: rest) = (readMlLiteralBody rest).map fun (cs', r') => (c :: cs', r') := by
          conv => lhs; unfold readMlLiteralBody
          split <;> first | simp_all | (exfalso; apply hq3; simp_all)
        have hp_step : parseMultilineLiteralBodyFuel (f + 1) acc (c :: rest) = parseMultilineLiteralBodyFuel f (c :: acc) rest := by
          conv => lhs; unfold parseMultilineLiteralBodyFuel
          split <;> first | simp_all | (exfalso; apply hq3; simp_all)
        rw [hr_step] at h; simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        rcases h with ⟨⟨cs', rem'⟩, hrec, rfl, rfl⟩
        rw [hp_step]
        simpa [List.reverse_cons, List.append_assoc] using ih rest cs' rem' (c :: acc) hrec (by simp at hf; omega)

private theorem takeBareKeyChars_append :
    ∀ (ks acc rem : List Char), ks.all isBareKeyChar = true →
      (∀ c r, rem = c :: r → isBareKeyChar c = false) →
      takeBareKeyChars acc (ks ++ rem) = (acc.reverse ++ ks, rem)
  | [], acc, [], _, _ => by simp [takeBareKeyChars]
  | [], acc, c :: r, _, hrem => by simp [takeBareKeyChars, hrem c r rfl]
  | k :: ks, acc, rem, hks, hrem => by
    simp only [List.all_cons, Bool.and_eq_true] at hks
    simp [takeBareKeyChars, hks.1, takeBareKeyChars_append ks (k :: acc) rem hks.2 hrem, List.reverse_cons, List.append_assoc]

/-- Every key rendered by `Model.renderKey` parses cleanly via `Impl.parseKeySegment`. -/
theorem renderKey_parseKeySegment {k : String} {ks : KeyStyle} {rk : String} {rem : List Char}
    (hr : renderKey k ks = some rk)
    (hrem : ∀ c r, rem = c :: r → isBareKeyChar c = false ∧ c ≠ '"' ∧ c ≠ '\'') :
    CleanNorm rk.toList ∧ rk.toList ≠ [] ∧ parseKeySegment (rk.toList ++ rem) = .ok (k, rem) := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr; split at hr <;> try (simp at hr; done)
    rename_i hbare; injection hr with hrk; subst hrk
    simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
    have hcl_bare : CleanNorm k.toList := by
      apply List.all_eq_true.mpr; intro c hc
      have hb := List.all_eq_true.mp hbare.2 c hc
      have hlt : c.toNat < 128 := by
        simp only [isBareKeyChar, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
        rcases hb with ((((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | rfl) | rfl)
        · have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true h2)
          have : 'Z'.val.toNat = 90 := rfl; have : c.toNat = c.val.toNat := rfl; omega
        · have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true h2)
          have : 'z'.val.toNat = 122 := rfl; have : c.toNat = c.val.toNat := rfl; omega
        · have := UInt32.le_iff_toNat_le.mp (of_decide_eq_true h2)
          have : '9'.val.toNat = 57 := rfl; have : c.toNat = c.val.toNat := rfl; omega
        · decide
        · decide
      have hall : (List.range 128).all (fun m =>
          let x := Char.ofNat m
          !isBareKeyChar x || (!isDisallowedControl x && x != '\r')) = true := by decide
      simpa [Char.ofNat_toNat, hb] using List.all_eq_true.mp hall c.toNat (List.mem_range.mpr hlt)
    cases hkl : k.toList with
    | nil =>
      have : k = "" := by rw [← String.ofList_toList (s := k), hkl]
      subst this; simp at hbare
    | cons c0 cs0 =>
      have hc0 := isBareKeyChar_not_special (List.all_eq_true.mp hbare.2 c0 (by rw [hkl]; simp))
      have hstep : parseKeySegment (c0 :: (cs0 ++ rem)) =
          (let (ks', rem') := takeBareKeyChars [] (c0 :: (cs0 ++ rem))
           if ks'.isEmpty then .error (mkErr .parseError "expected key") else .ok (String.ofList ks', rem')) := by
        have h1 := hc0.2.2.2.2.2.2.1; have h2 := hc0.2.2.2.2.2.2.2.1
        conv => lhs; unfold parseKeySegment
        split <;> simp_all
      have htk := takeBareKeyChars_append k.toList [] rem hbare.2 (fun c r h => (hrem c r h).1)
      rw [hkl] at hcl_bare htk
      refine ⟨hcl_bare, by simp, ?_⟩
      rw [List.cons_append, hstep, ← List.cons_append, htk]
      simp only [List.reverse_nil, List.nil_append, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [← hkl, String.ofList_toList]
  | basic atoms? =>
    cases atoms? with
    | none =>
      simp only [renderKey, Option.some.injEq] at hr; subst hr
      obtain ⟨hnoq, hp⟩ := escapeBasicBody_false_parse k
      have hnot2 : ∀ t, ((escapeBasicBody false k).toList ++ '"' :: rem) ≠ '"' :: '"' :: t := by
        intro t ht
        cases hbl : (escapeBasicBody false k).toList with
        | nil =>
          rw [hbl, List.nil_append] at ht; obtain ⟨_, ht2⟩ := List.cons.inj ht
          cases rem with | nil => nomatch ht2 | cons cr rr => exact (hrem cr rr rfl).2.1 (List.cons.inj ht2).1
        | cons b0 bs =>
          rw [hbl, List.cons_append] at ht; exact hnoq b0 bs hbl (List.cons.inj ht).1
      refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, cleanNorm_escapeBasicBody false k⟩, by decide⟩,
        by simp [String.toList_append], ?_⟩
      simp only [String.toList_append, show ("\"" : String).toList = ['"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      have hstep : parseKeySegment ('"' :: ((escapeBasicBody false k).toList ++ '"' :: rem)) =
          parseBasicStringBody ((escapeBasicBody false k).toList ++ '"' :: rem) := by
        simp [parseKeySegment]
      rw [hstep, hp]
    | some atoms =>
      simp only [renderKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨enc, henc, rfl⟩
      obtain ⟨hcl_enc, hnoq, hp_f⟩ := renderBasicAtoms_parse k.toList atoms enc henc
      have hnot2 : ∀ t, (enc ++ '"' :: rem) ≠ '"' :: '"' :: t := by
        intro t ht
        cases hel : enc with
        | nil =>
          rw [hel, List.nil_append] at ht; obtain ⟨_, ht2⟩ := List.cons.inj ht
          cases rem with | nil => nomatch ht2 | cons cr rr => exact (hrem cr rr rfl).2.1 (List.cons.inj ht2).1
        | cons b0 bs =>
          rw [hel, List.cons_append] at ht; exact hnoq b0 bs hel (List.cons.inj ht).1
      refine ⟨by simp only [String.toList_append, String.toList_ofList]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hcl_enc⟩, by decide⟩,
        by simp [String.toList_append], ?_⟩
      simp only [String.toList_append, String.toList_ofList, show ("\"" : String).toList = ['"'] from rfl, List.cons_append, List.nil_append, List.append_assoc]
      have hstep : parseKeySegment ('"' :: (enc ++ '"' :: rem)) = parseBasicStringBody (enc ++ '"' :: rem) := by
        simp [parseKeySegment]
      rw [hstep]; unfold parseBasicStringBody
      simpa [String.ofList_toList] using hp_f ((enc ++ '"' :: rem).length + 1) [] rem (by simp only [List.length_append, List.length_cons]; omega)
  | literal =>
    simp only [renderKey] at hr; split at hr <;> try (simp at hr; done)
    rename_i hcond; injection hr with hrk; subst hrk
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    have hnq : '\'' ∉ k.toList := by simpa [String.contains_char_eq] using hcond.2
    have hnl : '\n' ∉ k.toList := fun hm => by have h1 := List.all_eq_true.mp hcond.1 '\n' hm; simp at h1
    have hcl_k : CleanNorm k.toList := List.all_eq_true.mpr fun c hc => by
      have h1 := List.all_eq_true.mp hcond.1 c hc; simp only [Bool.and_eq_true] at h1 ⊢; exact ⟨h1.1.1, h1.2⟩
    have hnot2 : ∀ t, (k.toList ++ '\'' :: rem) ≠ '\'' :: '\'' :: t := by
      intro t ht
      cases hkl : k.toList with
      | nil =>
        rw [hkl, List.nil_append] at ht; obtain ⟨_, ht2⟩ := List.cons.inj ht
        cases rem with | nil => nomatch ht2 | cons cr rr => exact (hrem cr rr rfl).2.2 (List.cons.inj ht2).1
      | cons c0 cs0 =>
        rw [hkl, List.cons_append] at ht; exact hnq (by rw [hkl, (List.cons.inj ht).1]; simp)
    refine ⟨by simp only [String.toList_append]; exact cleanNorm_append.mpr ⟨cleanNorm_append.mpr ⟨by decide, hcl_k⟩, by decide⟩,
      by simp [String.toList_append], ?_⟩
    simp only [String.toList_append, show ("'" : String).toList = ['\''] from rfl, List.cons_append, List.nil_append, List.append_assoc]
    have hstep : parseKeySegment ('\'' :: (k.toList ++ '\'' :: rem)) = parseLiteralStringBody [] (k.toList ++ '\'' :: rem) := by
      simp [parseKeySegment]
    rw [hstep, parseLiteralStringBody_append k.toList [] rem hnl hnq]
    simp [String.ofList_toList]

end LeanSwe.Toml.Proofs
