import LeanSweProofs.Toml.Proofs.RenderInjectiveLex

/-!
# Key & String Left-Inverses for `Toml.Model.render` Injectivity

Proves `Impl`-independent left-inverse decoders for `renderKey`, `renderDottedKey`,
and `renderStringLiteral` across all key and string styles in `Toml.Model`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

/-- Decode one backslash escape at the head of `cs` (after `'\\'`). -/
def readBasicEscape : List Char → Option (Char × List Char)
  | 'b' :: r => some ('\x08', r)
  | 't' :: r => some ('\t', r)
  | 'n' :: r => some ('\n', r)
  | 'f' :: r => some ('\x0c', r)
  | 'r' :: r => some ('\r', r)
  | '"' :: r => some ('"', r)
  | '\\' :: r => some ('\\', r)
  | 'u' :: h1 :: h2 :: h3 :: h4 :: r =>
    (decodeBasicEscape (.unicode4 h1 h2 h3 h4)).map (·, r)
  | 'U' :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: r =>
    (decodeBasicEscape (.unicode8 h1 h2 h3 h4 h5 h6 h7 h8)).map (·, r)
  | _ => none

theorem readBasicEscape_len_lt {cs : List Char} {ch : Char} {after : List Char}
    (h : readBasicEscape cs = some (ch, after)) : after.length < ('\\' :: cs).length := by
  unfold readBasicEscape at h
  split at h <;> try (simp at h; done)
  all_goals simp only [Option.some.injEq, Option.map_eq_some_iff, Prod.mk.injEq] at h
  all_goals first
    | (rcases h with ⟨_, rfl⟩; simp +arith)
    | (rcases h with ⟨_, _, _, rfl⟩; simp +arith)

theorem readBasicEscape_renderBasicEscapeChars {esc : BasicEscapeAtom} {c : Char}
    (hd : decodeBasicEscape esc = some c) (tail : List Char) :
    ∃ escBody, renderBasicEscapeChars esc = '\\' :: escBody ∧
      readBasicEscape (escBody ++ tail) = some (c, tail) := by
  cases esc <;> refine ⟨_, rfl, ?_⟩ <;>
    first | (simp [readBasicEscape, hd]; done) | (simp [decodeBasicEscape] at hd; simp [readBasicEscape]; exact hd)

theorem hexValModel_hexDigitUpper {n : Nat} (hn : n < 16) :
    hexValModel? (hexDigitUpper n) = some n := by
  have hall : (List.range 16).all (fun m => hexValModel? (hexDigitUpper m) == some m) = true := by decide
  simpa [beq_iff_eq] using List.all_eq_true.mp hall n (List.mem_range.mpr hn)

theorem escapeBasicChar_atom (allowNl : Bool) (c : Char) :
    ((escapeBasicChar allowNl c).toList = [c] ∧
      c ≠ '"' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ isDisallowedControl c = false ∧ (allowNl = true ∨ c ≠ '\n')) ∨
    ∃ esc, decodeBasicEscape esc = some c ∧ (escapeBasicChar allowNl c).toList = renderBasicEscapeChars esc := by
  if h1 : c = '\\' then subst h1; exact Or.inr ⟨.backslash, rfl, by cases allowNl <;> rfl⟩ else
  if h2 : c = '"' then subst h2; exact Or.inr ⟨.quote, rfl, by cases allowNl <;> rfl⟩ else
  if h3 : c = '\x08' then subst h3; exact Or.inr ⟨.backspace, rfl, by cases allowNl <;> rfl⟩ else
  if h4 : c = '\t' then subst h4; exact Or.inr ⟨.tab, rfl, by cases allowNl <;> rfl⟩ else
  if h5 : c = '\n' then
    subst h5
    cases allowNl with
    | false => exact Or.inr ⟨.linefeed, rfl, rfl⟩
    | true => exact Or.inl ⟨rfl, by decide, by decide, by decide, by decide, Or.inl rfl⟩
  else
  if h6 : c = '\x0c' then subst h6; exact Or.inr ⟨.formfeed, rfl, by cases allowNl <;> rfl⟩ else
  if h7 : c = '\r' then subst h7; exact Or.inr ⟨.carriageReturn, rfl, by cases allowNl <;> rfl⟩ else
  if h8 : isDisallowedControl c = true then
    have hlt : c.toNat < 256 := by
      simp only [isDisallowedControl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h8
      omega
    have hv1 := hexValModel_hexDigitUpper (n := c.toNat / 16) (by omega)
    have hv2 := hexValModel_hexDigitUpper (n := c.toNat % 16) (Nat.mod_lt _ (by decide))
    refine Or.inr ⟨.unicode4 '0' '0' (hexDigitUpper (c.toNat / 16)) (hexDigitUpper (c.toNat % 16)), ?_, ?_⟩
    · have h0 : hexValModel? '0' = some 0 := rfl
      have hbad : (c.toNat > 0x10FFFF || (0xD800 ≤ c.toNat && c.toNat ≤ 0xDFFF)) = false := by
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [decodeBasicEscape, h0, hv1, hv2, show ((0 * 16 + 0) * 16 + c.toNat / 16) * 16 + c.toNat % 16 = c.toNat by omega,
        hbad, Bool.false_eq_true, ↓reduceIte, Char.ofNat_toNat]
    · have hesc : escapeBasicChar allowNl c =
          "\\u00" ++ String.ofList [hexDigitUpper (c.toNat / 16), hexDigitUpper (c.toNat % 16)] := by
        simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, h8]
      simp [hesc, renderBasicEscapeChars]
  else
    have h8f : isDisallowedControl c = false := Bool.eq_false_iff.mpr h8
    have hesc : escapeBasicChar allowNl c = String.singleton c := by
      simp [escapeBasicChar, h1, h2, h3, h4, h5, h6, h7, h8]
    exact Or.inl ⟨by rw [hesc, String.toList_singleton], h2, h1, h7, h8f, Or.inr h5⟩

/-- Pure left-inverse decoder for single-line basic string/key bodies after opening `'"'`. -/
def readBasicBody : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: rest => some ([], rest)
  | '\\' :: rest =>
    match h : readBasicEscape rest with
    | some (ch, afterEsc) =>
      have : afterEsc.length < ('\\' :: rest).length := readBasicEscape_len_lt h
      match readBasicBody afterEsc with
      | some (cs, rem) => some (ch :: cs, rem)
      | none => none
    | none => none
  | c :: rest =>
    match readBasicBody rest with
    | some (cs, rem) => some (c :: cs, rem)
    | none => none
termination_by cs => cs.length

theorem readBasicBody_backslash (rest : List Char) :
    readBasicBody ('\\' :: rest) =
      match readBasicEscape rest with
      | some (ch, afterEsc) =>
        match readBasicBody afterEsc with
        | some (cs, rem) => some (ch :: cs, rem)
        | none => none
      | none => none := by
  (conv => lhs; unfold readBasicBody)
  split
  · contradiction
  · rename_i _ heq; nomatch (List.cons.inj heq).1
  · rename_i _ heq; obtain ⟨_, rfl⟩ := List.cons.inj heq; split <;> rename_i heq' <;> simp [heq']
  · rename_i _ _ hnotbs heq; exact False.elim (hnotbs (List.cons.inj heq).1.symm)

theorem readBasicBody_len_lt :
    ∀ {cs out rem : List Char}, readBasicBody cs = some (out, rem) → rem.length < ('"' :: cs).length
  | [], _, _, h => by simp [readBasicBody] at h
  | '"' :: rest, _, rem, h => by
    simp only [readBasicBody, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩; simp +arith
  | '\\' :: rest, out, rem, h => by
    have h' : (match hr : readBasicEscape rest with
        | some (ch, afterEsc) =>
          match readBasicBody afterEsc with
          | some (cs, rem) => some (ch :: cs, rem)
          | none => none
        | none => none) = some (out, rem) := by simpa [readBasicBody] using h
    split at h'
    · rename_i ch afterEsc hr
      have hlt := readBasicEscape_len_lt hr
      cases hb : readBasicBody afterEsc with
      | none => simp [hb] at h'
      | some p =>
        rw [hb] at h'; simp only [Option.some.injEq, Prod.mk.injEq] at h'
        rcases h' with ⟨_, rfl⟩
        have ih := readBasicBody_len_lt hb
        simp only [List.length_cons] at hlt ih ⊢; omega
    · cases h'
  | c :: rest, out, rem, h => by
    by_cases hq : c = '"'
    · subst hq; simp only [readBasicBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; simp +arith
    · by_cases hbs : c = '\\'
      · subst hbs
        have h' : (match hr : readBasicEscape rest with
            | some (ch, afterEsc) =>
              match readBasicBody afterEsc with
              | some (cs, rem) => some (ch :: cs, rem)
              | none => none
            | none => none) = some (out, rem) := by simpa [readBasicBody] using h
        split at h'
        · rename_i ch afterEsc hr
          have hlt := readBasicEscape_len_lt hr
          cases hb : readBasicBody afterEsc with
          | none => simp [hb] at h'
          | some p =>
            rw [hb] at h'; simp only [Option.some.injEq, Prod.mk.injEq] at h'
            rcases h' with ⟨_, rfl⟩
            have ih := readBasicBody_len_lt hb
            simp only [List.length_cons] at hlt ih ⊢; omega
        · cases h'
      · have hstep : readBasicBody (c :: rest) =
            (match readBasicBody rest with | some (cs, rem) => some (c :: cs, rem) | none => none) := by
          conv => lhs; unfold readBasicBody
          split <;> simp_all
        rw [hstep] at h
        cases hb : readBasicBody rest with
        | none => simp [hb] at h
        | some p =>
          rw [hb] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, rfl⟩
          have ih := readBasicBody_len_lt hb
          simp only [List.length_cons] at ih ⊢; omega
termination_by cs => cs.length

theorem readBasicBody_renderBasicAtoms :
    ∀ (cs : List Char) (atoms : List BasicCharAtom) (enc rem : List Char),
      renderBasicAtoms cs atoms = some enc →
      readBasicBody (enc ++ '"' :: rem) = some (cs, rem)
  | [], [], enc, rem, h => by simp [renderBasicAtoms] at h; subst h; simp [readBasicBody]
  | c :: cs, .plain :: atoms, enc, rem, h => by
    simp only [renderBasicAtoms] at h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true, bne_iff_ne] at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨rest, hrest, rfl⟩
      have hq : c ≠ '"' := hok.1.1.1.1
      have hbs : c ≠ '\\' := hok.1.1.1.2
      have hstep : readBasicBody (c :: (rest ++ '"' :: rem)) =
          match readBasicBody (rest ++ '"' :: rem) with
          | some (cs', rem') => some (c :: cs', rem') | none => none := by
        conv => lhs; unfold readBasicBody
        split <;> simp_all
      rw [List.cons_append, hstep, readBasicBody_renderBasicAtoms cs atoms rest rem hrest]
    · cases h
  | c :: cs, .escape esc :: atoms, enc, rem, h => by
    simp only [renderBasicAtoms] at h
    cases hd : decodeBasicEscape esc with
    | none => simp [hd] at h
    | some c' =>
      simp only [hd] at h
      split at h
      · rename_i hceq
        have hc : c = c' := eq_of_beq hceq; subst hc
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨rest, hrest, rfl⟩
        obtain ⟨escBody, hesc_eq, hread⟩ := readBasicEscape_renderBasicEscapeChars hd (rest ++ '"' :: rem)
        rw [hesc_eq, List.cons_append, List.cons_append, List.append_assoc, readBasicBody_backslash, hread]
        simp [readBasicBody_renderBasicAtoms cs atoms rest rem hrest]
      · cases h
  | [], _ :: _, _, _, h => by simp [renderBasicAtoms] at h
  | _ :: _, [], _, _, h => by simp [renderBasicAtoms] at h

theorem readBasicBody_escapeBasicBody (s : String) (rem : List Char) :
    readBasicBody ((escapeBasicBody false s).toList ++ '"' :: rem) = some (s.toList, rem) := by
  have heq : (escapeBasicBody false s).toList = s.toList.flatMap (fun c => (escapeBasicChar false c).toList) := by
    simp [escapeBasicBody, String.toList_join, List.flatMap_map]
  rw [heq]
  induction s.toList with
  | nil => simp [readBasicBody]
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc]
    rcases escapeBasicChar_atom false c with ⟨hc_eq, hq, hbs, _, _, _⟩ | ⟨esc, hd, hesc_eq⟩
    · rw [hc_eq, List.singleton_append]
      have hstep : readBasicBody (c :: (cs.flatMap (fun x => (escapeBasicChar false x).toList) ++ '"' :: rem)) =
          match readBasicBody (cs.flatMap (fun x => (escapeBasicChar false x).toList) ++ '"' :: rem) with
          | some (cs', rem') => some (c :: cs', rem') | none => none := by
        conv => lhs; unfold readBasicBody
        split <;> simp_all
      rw [hstep, ih]
    · obtain ⟨escBody, hrend, hread⟩ := readBasicEscape_renderBasicEscapeChars hd
        (cs.flatMap (fun x => (escapeBasicChar false x).toList) ++ '"' :: rem)
      rw [hesc_eq, hrend, List.cons_append, readBasicBody_backslash, hread]
      simp [ih]

/-- Pure left-inverse decoder for single-line literal string/key bodies after opening `'\''`. -/
def readLiteralBody : List Char → Option (List Char × List Char)
  | [] => none
  | '\'' :: rest => some ([], rest)
  | c :: rest =>
    match readLiteralBody rest with
    | some (cs, rem) => some (c :: cs, rem)
    | none => none

theorem readLiteralBody_len_lt :
    ∀ {cs out rem : List Char}, readLiteralBody cs = some (out, rem) → rem.length < ('\'' :: cs).length
  | [], _, _, h => by simp [readLiteralBody] at h
  | '\'' :: rest, _, rem, h => by
    simp only [readLiteralBody, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩; simp +arith
  | c :: rest, out, rem, h => by
    by_cases hq : c = '\''
    · subst hq; simp only [readLiteralBody, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; simp +arith
    · have hstep : readLiteralBody (c :: rest) =
          (match readLiteralBody rest with | some (cs, rem) => some (c :: cs, rem) | none => none) := by
        conv => lhs; unfold readLiteralBody
        split <;> simp_all
      rw [hstep] at h
      cases hb : readLiteralBody rest with
      | none => simp [hb] at h
      | some p =>
        rw [hb] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        have ih := readLiteralBody_len_lt hb
        simp only [List.length_cons] at ih ⊢; omega

theorem readLiteralBody_append :
    ∀ (cs rem : List Char), '\'' ∉ cs → readLiteralBody (cs ++ '\'' :: rem) = some (cs, rem)
  | [], rem, _ => by simp [readLiteralBody]
  | c :: cs, rem, hnq => by
    have hc : c ≠ '\'' := by intro heq; subst heq; exact hnq List.mem_cons_self
    have hstep : readLiteralBody (c :: (cs ++ '\'' :: rem)) =
        match readLiteralBody (cs ++ '\'' :: rem) with
        | some (cs', rem') => some (c :: cs', rem') | none => none := by
      conv => lhs; unfold readLiteralBody
      split <;> simp_all
    rw [List.cons_append, hstep, readLiteralBody_append cs rem (fun hm => hnq (List.mem_cons_of_mem _ hm))]

/-- Consume leading ASCII bare-key characters. -/
def readBareKey : List Char → List Char × List Char
  | c :: cs => if isBareKeyChar c then let (ks, rem) := readBareKey cs; (c :: ks, rem) else ([], c :: cs)
  | [] => ([], [])

theorem readBareKey_len_le : ∀ cs : List Char, (readBareKey cs).2.length ≤ cs.length
  | [] => Nat.le_refl _
  | c :: cs => by
    unfold readBareKey
    split
    · exact Nat.le_trans (readBareKey_len_le cs) (Nat.le_succ _)
    · exact Nat.le_refl _

theorem readBareKey_append :
    ∀ (ks rem : List Char), ks.all isBareKeyChar = true →
      (∀ c r, rem = c :: r → isBareKeyChar c = false) →
      readBareKey (ks ++ rem) = (ks, rem)
  | [], [], _, _ => rfl
  | [], c :: r, _, hrem => by simp [readBareKey, hrem c r rfl]
  | k :: ks, rem, hks, hrem => by
    simp only [List.all_cons, Bool.and_eq_true] at hks
    simp [readBareKey, hks.1, readBareKey_append ks rem hks.2 hrem]

/-- Pure left-inverse decoder for a single rendered key segment. -/
def readKeySeg : List Char → Option (String × List Char)
  | '"' :: rest => (readBasicBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | '\'' :: rest => (readLiteralBody rest).map fun (cs, rem) => (String.ofList cs, rem)
  | cs =>
    let (ks, rem) := readBareKey cs
    if ks.isEmpty then none else some (String.ofList ks, rem)

theorem readKeySeg_len_lt {cs : List Char} {k : String} {rem : List Char}
    (h : readKeySeg cs = some (k, rem)) : rem.length < cs.length := by
  match cs with
  | [] => simp [readKeySeg, readBareKey] at h
  | '"' :: rest =>
    simp only [readKeySeg, Option.map_eq_some_iff] at h
    rcases h with ⟨⟨_, rem'⟩, hb, _, rfl⟩
    exact readBasicBody_len_lt hb
  | '\'' :: rest =>
    simp only [readKeySeg, Option.map_eq_some_iff] at h
    rcases h with ⟨⟨_, rem'⟩, hb, _, rfl⟩
    exact readLiteralBody_len_lt hb
  | c :: rest =>
    by_cases hq1 : c = '"'
    · subst hq1; simp only [readKeySeg, Option.map_eq_some_iff] at h
      rcases h with ⟨⟨_, rem'⟩, hb, _, rfl⟩; exact readBasicBody_len_lt hb
    · by_cases hq2 : c = '\''
      · subst hq2; simp only [readKeySeg, Option.map_eq_some_iff] at h
        rcases h with ⟨⟨_, rem'⟩, hb, _, rfl⟩; exact readLiteralBody_len_lt hb
      · have hstep : readKeySeg (c :: rest) =
            (let (ks, rem') := readBareKey (c :: rest)
             if ks.isEmpty then none else some (String.ofList ks, rem')) := by
          conv => lhs; unfold readKeySeg
          split <;> simp_all
        rw [hstep] at h
        by_cases hbk : isBareKeyChar c = true
        · have hrb_eq : readBareKey (c :: rest) = (c :: (readBareKey rest).1, (readBareKey rest).2) := by
            simp [readBareKey, hbk]
          rw [hrb_eq] at h
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, rfl⟩
          exact Nat.lt_of_le_of_lt (readBareKey_len_le rest) (Nat.lt_succ_self _)
        · have hbkf := Bool.eq_false_iff.mpr hbk
          have hrb_eq : readBareKey (c :: rest) = ([], c :: rest) := by simp [readBareKey, hbkf]
          rw [hrb_eq] at h; simp at h

theorem isBareKeyChar_not_special {c : Char} (h : isBareKeyChar c = true) :
    isModelHorizWs c = false ∧ c ≠ '\n' ∧ c ≠ '#' ∧ c ≠ '[' ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ '"' ∧ c ≠ '\'' ∧ c ≠ '\r' := by
  have hlt : c.toNat < 128 := by
    simp only [isBareKeyChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ((((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | rfl) | rfl) <;>
      first | decide | (have : c.toNat ≤ 122 := Nat.le_trans h2 (by decide); omega)
  have hall : (List.range 128).all (fun n =>
      let x := Char.ofNat n
      !isBareKeyChar x || (!isModelHorizWs x && x != '\n' && x != '#' && x != '[' && x != ']' &&
        x != '}' && x != '"' && x != '\'' && x != '\r')) = true := by decide
  have hm := List.all_eq_true.mp hall c.toNat (List.mem_range.mpr hlt)
  simp only [Char.ofNat_toNat, h, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hm
  exact ⟨hm.1.1.1.1.1.1.1.1, hm.1.1.1.1.1.1.1.2, hm.1.1.1.1.1.1.2, hm.1.1.1.1.1.2,
    hm.1.1.1.1.2, hm.1.1.1.2, hm.1.1.2, hm.1.2, hm.2⟩

theorem readKeySeg_renderKey {k : String} {ks : KeyStyle} {rk : String} {rem : List Char}
    (hr : renderKey k ks = some rk) (hrem : ∀ c r, rem = c :: r → isBareKeyChar c = false) :
    readKeySeg (rk.toList ++ rem) = some (k, rem) ∧ NoCrStr rk ∧
      ∃ c0 r0, rk.toList = c0 :: r0 ∧ isModelHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ '[' := by
  cases ks with
  | bare =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hbare; injection hr with hrk; subst hrk
      simp only [isValidBareKey, Bool.and_eq_true, Bool.not_eq_true'] at hbare
      cases hkl : k.toList with
      | nil =>
        have hk0 : k = "" := by rw [← String.ofList_toList (s := k), hkl]
        subst hk0; simp at hbare
      | cons c0 cs0 =>
        have hc0 := isBareKeyChar_not_special (List.all_eq_true.mp hbare.2 c0 (by rw [hkl]; simp))
        have hstep : readKeySeg (c0 :: (cs0 ++ rem)) =
            (let (ks', rem') := readBareKey (c0 :: (cs0 ++ rem))
             if ks'.isEmpty then none else some (String.ofList ks', rem')) := by
          have hnq1 := hc0.2.2.2.2.2.2.1
          have hnq2 := hc0.2.2.2.2.2.2.2.1
          conv => lhs; unfold readKeySeg
          split <;> simp_all
        have hrb := readBareKey_append k.toList rem hbare.2 hrem
        refine ⟨?_, ?_, c0, cs0, rfl, hc0.1, hc0.2.1, hc0.2.2.1, hc0.2.2.2.1⟩
        · rw [List.cons_append, hstep, ← List.cons_append, ← hkl, hrb]
          dsimp only; rw [String.ofList_toList, hkl]; simp
        · intro hm
          exact (isBareKeyChar_not_special (List.all_eq_true.mp hbare.2 '\r' hm)).2.2.2.2.2.2.2.2 rfl
    · cases hr
  | basic atoms? =>
    cases atoms? with
    | none =>
      simp only [renderKey, Option.some.injEq] at hr; subst hr
      have hnocr := noCrStr_append (noCrStr_append (show NoCrStr "\"" by decide) (noCr_escapeBasicBody false k)) (show NoCrStr "\"" by decide)
      refine ⟨?_, hnocr, '"', (escapeBasicBody false k ++ "\"").toList, by simp [String.toList_append],
        by decide, by decide, by decide, by decide⟩
      simp only [String.toList_append, show ("\"" : String).toList = ['"'] from rfl,
        List.cons_append, List.nil_append, List.append_assoc, readKeySeg]
      rw [readBasicBody_escapeBasicBody k rem]
      simp [String.ofList_toList]
    | some atoms =>
      simp only [renderKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
      rcases hr with ⟨enc, henc, rfl⟩
      have hnocr : NoCrStr ("\"" ++ String.ofList enc ++ "\"") := by
        refine noCrStr_append (noCrStr_append (show NoCrStr "\"" by decide) ?_) (show NoCrStr "\"" by decide)
        simpa [NoCrStr, String.toList_ofList] using noCr_renderBasicAtoms k.toList atoms enc henc
      refine ⟨?_, hnocr, '"', (String.ofList enc ++ "\"").toList, by simp [String.toList_append],
        by decide, by decide, by decide, by decide⟩
      simp only [String.toList_append, String.toList_ofList, show ("\"" : String).toList = ['"'] from rfl,
        List.cons_append, List.nil_append, List.append_assoc, readKeySeg]
      rw [readBasicBody_renderBasicAtoms k.toList atoms enc rem henc]
      simp [String.ofList_toList]
  | literal =>
    simp only [renderKey] at hr
    split at hr
    · rename_i hcond; injection hr with hrk; subst hrk
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hnq : '\'' ∉ k.toList := by simpa [String.contains_char_eq] using hcond.2
      have hnocr : NoCrStr ("'" ++ k ++ "'") := by
        refine noCrStr_append (noCrStr_append (show NoCrStr "'" by decide) ?_) (show NoCrStr "'" by decide)
        intro hm; have hc := List.all_eq_true.mp hcond.1 '\r' hm; simp at hc
      refine ⟨?_, hnocr, '\'', (k ++ "'").toList, by simp [String.toList_append],
        by decide, by decide, by decide, by decide⟩
      simp only [String.toList_append, show ("'" : String).toList = ['\''] from rfl,
        List.cons_append, List.nil_append, List.append_assoc, readKeySeg]
      rw [readLiteralBody_append k.toList rem hnq]
      simp [String.ofList_toList]
    · cases hr

/-- Pure left-inverse decoder for `renderDottedKey` (leaving `dropHoriz rem`). -/
def readDottedKey (cs : List Char) : Option (List String × List Char) :=
  match hk : readKeySeg cs with
  | none => none
  | some (k, r1) =>
    match hd : dropHoriz r1 with
    | '.' :: r2 =>
      have hlt : (dropHoriz r2).length < cs.length := by
        have h1 := readKeySeg_len_lt hk
        have h2 := dropHoriz_len_le r1
        have h3 := dropHoriz_len_le r2
        rw [hd] at h2; simp only [List.length_cons] at h2; omega
      match readDottedKey (dropHoriz r2) with
      | some (ks, r3) => some (k :: ks, r3)
      | none => none
    | other => some ([k], other)
termination_by cs.length

theorem readDottedKeyCont_spec :
    ∀ (segs : List DottedSegCont) (contStr : String) (rem : List Char),
      renderDottedKeyCont segs = some contStr →
      (∀ c r, rem = c :: r → isModelHorizWs c = false ∧ isBareKeyChar c = false ∧ c ≠ '.') →
      NoCrStr contStr ∧
        match segs with
        | [] => contStr = ""
        | seg :: rest =>
          dropHoriz (contStr.toList ++ rem) =
            '.' :: (seg.wsAfterDot.toList ++ ((match renderKey seg.key seg.style with | some s => s | none => "") ++
              (match renderDottedKeyCont rest with | some s => s | none => "")).toList ++ rem)
  | [], contStr, _, h, _ => by
    simp only [renderDottedKeyCont, Option.some.injEq] at h; subst h
    exact ⟨by decide, rfl⟩
  | seg :: rest, contStr, rem, h, hrem => by
    unfold renderDottedKeyCont at h
    split at h
    · cases h
    · rename_i hws_ok
      simp at hws_ok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨rk, hrk, tail, htail, rfl⟩
      obtain ⟨_, hnocr_rk, _⟩ := readKeySeg_renderKey (rem := []) hrk (fun _ _ h => nomatch h)
      obtain ⟨hnocr_tl, _⟩ := readDottedKeyCont_spec rest tail rem htail hrem
      refine ⟨noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append (noCr_horizWsStr hws_ok.1) (show NoCrStr "." by decide))
        (noCr_horizWsStr hws_ok.2)) hnocr_rk) hnocr_tl, ?_⟩
      simp only [hrk, htail, String.toList_append, List.append_assoc,
        show ("." : String).toList = ['.'] from rfl, List.singleton_append]
      rw [dropHoriz_append hws_ok.1 (fun c r hc => by obtain ⟨rfl, _⟩ := List.cons.inj hc; decide), List.cons_append]

theorem readDottedKey_renderDottedKey {dk : DottedKeyTape} {rdk : String} {wsAfter : String} {rem : List Char}
    (hr : renderDottedKey dk = some rdk) (hws : isHorizWsStr wsAfter = true)
    (hrem : ∀ c r, rem = c :: r → isModelHorizWs c = false ∧ isBareKeyChar c = false ∧ c ≠ '.') :
    readDottedKey (rdk.toList ++ wsAfter.toList ++ rem) = some (dk.path, rem) ∧ NoCrStr rdk ∧
      ∃ c0 r0, rdk.toList = c0 :: r0 ∧ isModelHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ '[' := by
  simp only [renderDottedKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr
  rcases hr with ⟨rk0, hrk0, tail0, htail0, rfl⟩
  suffices hmain : ∀ (k0 : String) (s0 : KeyStyle) (segs : List DottedSegCont) (rk : String) (tl : String),
      renderKey k0 s0 = some rk → renderDottedKeyCont segs = some tl →
      readDottedKey ((rk ++ tl).toList ++ wsAfter.toList ++ rem) =
        some (k0 :: segs.map DottedSegCont.key, rem) ∧ NoCrStr (rk ++ tl) ∧
        ∃ c0 r0, (rk ++ tl).toList = c0 :: r0 ∧ isModelHorizWs c0 = false ∧ c0 ≠ '\n' ∧ c0 ≠ '#' ∧ c0 ≠ '[' by
    exact hmain dk.firstKey dk.firstStyle dk.rest rk0 tail0 hrk0 htail0
  intro k0 s0 segs
  induction segs generalizing k0 s0 with
  | nil =>
    intro rk tl hrk htl
    simp only [renderDottedKeyCont, Option.some.injEq] at htl; subst htl
    rw [String.append_empty]
    have hrem_bare : ∀ c r, wsAfter.toList ++ rem = c :: r → isBareKeyChar c = false := by
      intro c r hcr
      cases hwl : wsAfter.toList with
      | nil => rw [hwl, List.nil_append] at hcr; exact (hrem c r hcr).2.1
      | cons w ws =>
        rw [hwl, List.cons_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr
        have hmw := List.all_eq_true.mp hws w (by rw [hwl]; simp)
        cases hbk : isBareKeyChar w
        · rfl
        · rw [(isBareKeyChar_not_special hbk).1] at hmw; cases hmw
    obtain ⟨hks, hnocr, c0, r0, hlist, hc0⟩ := readKeySeg_renderKey hrk hrem_bare
    refine ⟨?_, hnocr, c0, r0, hlist, hc0⟩
    rw [List.append_assoc]
    unfold readDottedKey
    split
    · rename_i hk; rw [hks] at hk; cases hk
    · rename_i k r1 hk
      rw [hks] at hk; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk)
      have hdh := dropHoriz_append hws (fun c r h => (hrem c r h).1)
      split
      · rename_i r2 hd; rw [hdh] at hd; exact absurd rfl ((hrem '.' r2 hd).2.2)
      · rw [hdh]; rfl
  | cons seg rest ih =>
    intro rk tl hrk htl
    unfold renderDottedKeyCont at htl
    split at htl
    · cases htl
    · rename_i hws_seg
      simp at hws_seg
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htl
      rcases htl with ⟨rk1, hrk1, tl1, htl1, rfl⟩
      have hrem_seg : ∀ c r, (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1).toList ++ wsAfter.toList ++ rem = c :: r →
          isBareKeyChar c = false := by
        intro c r hcr
        simp only [String.toList_append, List.append_assoc, show ("." : String).toList = ['.'] from rfl, List.singleton_append] at hcr
        cases hwl : seg.wsBeforeDot.toList with
        | nil =>
          rw [hwl, List.nil_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr; decide
        | cons w ws =>
          rw [hwl, List.cons_append] at hcr; obtain ⟨rfl, _⟩ := List.cons.inj hcr
          have hmw := List.all_eq_true.mp hws_seg.1 w (by rw [hwl]; simp)
          cases hbk : isBareKeyChar w
          · rfl
          · rw [(isBareKeyChar_not_special hbk).1] at hmw; cases hmw
      obtain ⟨hks0, hnocr0, c0, r0, hlist0, hc0⟩ := readKeySeg_renderKey hrk hrem_seg
      obtain ⟨ih_read, hnocr_rest, c1, r1, hlist1, hc1⟩ := ih seg.key seg.style rk1 tl1 hrk1 htl1
      have hnocr_seg : NoCrStr (rk ++ (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1)) := by
        have hb1 := noCr_horizWsStr hws_seg.1
        have hb2 := noCr_horizWsStr hws_seg.2
        have hdot : NoCrStr "." := by decide
        simp only [NoCrStr, String.toList_append, List.mem_append, not_or] at hnocr0 hnocr_rest hb1 hb2 hdot ⊢
        exact ⟨hnocr0, ⟨⟨⟨hb1, hdot⟩, hb2⟩, hnocr_rest.1⟩, hnocr_rest.2⟩
      refine ⟨?_, hnocr_seg, c0, r0 ++ (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1).toList,
        by simp [String.toList_append, hlist0], hc0⟩
      have hassoc : (rk ++ (seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1)).toList ++ wsAfter.toList ++ rem =
          rk.toList ++ ((seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1).toList ++ wsAfter.toList ++ rem) := by
        simp [String.toList_append, List.append_assoc]
      rw [hassoc]
      unfold readDottedKey
      split
      · rename_i hk; rw [hks0] at hk; cases hk
      · rename_i k r1' hk
        rw [hks0] at hk; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hk)
        have hdrop1 : dropHoriz ((seg.wsBeforeDot ++ "." ++ seg.wsAfterDot ++ rk1 ++ tl1).toList ++ wsAfter.toList ++ rem) =
            '.' :: (seg.wsAfterDot.toList ++ ((rk1 ++ tl1).toList ++ wsAfter.toList ++ rem)) := by
          simp only [String.toList_append, List.append_assoc, show ("." : String).toList = ['.'] from rfl, List.singleton_append]
          rw [dropHoriz_append hws_seg.1 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide), List.cons_append]
        have hdrop2 : dropHoriz (seg.wsAfterDot.toList ++ ((rk1 ++ tl1).toList ++ wsAfter.toList ++ rem)) =
            (rk1 ++ tl1).toList ++ wsAfter.toList ++ rem := by
          refine dropHoriz_append hws_seg.2 (fun c r hcr => ?_)
          rw [hlist1, List.cons_append, List.cons_append] at hcr
          obtain ⟨rfl, _⟩ := List.cons.inj hcr; exact hc1.1
        split
        · rename_i r2 hd
          rw [hdrop1] at hd; have hr2 := (List.cons.inj hd).2; subst hr2
          dsimp only; rw [hdrop2, ih_read]; rfl
        · rename_i hd
          rw [hdrop1] at hd; exact False.elim (hd _ rfl)

end LeanSwe.Toml.Proofs
