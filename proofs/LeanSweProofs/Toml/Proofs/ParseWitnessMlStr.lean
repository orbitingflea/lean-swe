import LeanSweProofs.Toml.Proofs.ParseWitnessLex

/-!
# Multiline String Parse-to-Render Completeness Witnesses

Constructs `StringStyle.multilineBasic` and `StringStyle.multilineLiteral` witnesses for
`Impl.parseMultilineBasicString` and `Impl.parseMultilineLiteralString`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl

private theorem parseMlBasicStep (fuel : Nat) (acc0 cs : List Char) :
    parseMultilineBasicBodyFuel (fuel + 1) acc0 cs =
      match cs with
      | [] => .error (mkErr .parseError "unterminated multiline basic string")
      | '"' :: '"' :: '"' :: '"' :: '"' :: '"' :: _ =>
        .error (mkErr .parseError "too many consecutive quotes at end of multiline basic string")
      | '"' :: '"' :: '"' :: '"' :: '"' :: rest =>
        .ok (String.ofList ('"' :: '"' :: acc0).reverse, rest)
      | '"' :: '"' :: '"' :: '"' :: rest =>
        .ok (String.ofList ('"' :: acc0).reverse, rest)
      | '"' :: '"' :: '"' :: rest =>
        .ok (String.ofList acc0.reverse, rest)
      | '\\' :: rest =>
        match parseBasicEscape rest with
        | .ok (ch, afterEsc) => parseMultilineBasicBodyFuel fuel (ch :: acc0) afterEsc
        | .error err =>
          match skipHorizWs rest with
          | '\n' :: afterNl => parseMultilineBasicBodyFuel fuel acc0 (skipHorizAndNl afterNl)
          | _ =>
            match rest with
            | 'u' :: _ => .error err
            | 'U' :: _ => .error err
            | _ => .error (mkErr .parseError "invalid escape sequence in multiline basic string")
      | c :: rest => parseMultilineBasicBodyFuel fuel (c :: acc0) rest := by
  (conv => lhs; unfold parseMultilineBasicBodyFuel)
  split
  · contradiction
  · rfl
  · rfl
  · rename_i rest _ _; cases rest with | nil => rfl | cons r0 rs => by_cases hq : r0 = '"' <;> subst_vars <;> simp_all
  · rename_i rest _ _ _; cases rest with | nil => rfl | cons r0 rs => by_cases hq : r0 = '"' <;> subst_vars <;> simp_all
  · rename_i rest _ _ _ _; cases rest with | nil => rfl | cons r0 rs => by_cases hq : r0 = '"' <;> subst_vars <;> simp_all
  · simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at *; subst_vars; rfl
  · simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at *; subst_vars; rfl

private theorem parseMlBasicBody_aux (fuel : Nat) :
    ∀ (acc0 cs : List Char) {fl at_ : Bool} {qr : Nat} {s : String} {after : List Char},
      CleanNorm cs →
      (fl = true → ∀ r, cs ≠ '\n' :: r) →
      (at_ = true → ∀ c r, cs = c :: r → isModelHorizWs c = false ∧ c ≠ '\n') →
      qr ≤ 2 →
      (qr ≥ 1 → ∀ r, cs ≠ '"' :: '"' :: r) →
      (qr ≥ 2 → ∀ r, cs ≠ '"' :: r) →
      parseMultilineBasicBodyFuel fuel acc0 cs = .ok (s, after) →
      ∃ csTail atoms enc,
        s = String.ofList (acc0.reverse ++ csTail) ∧
        renderMultilineAtoms fl at_ qr csTail atoms = some enc ∧
        cs = enc ++ ['"', '"', '"'] ++ after := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; nomatch h
  | succ fuel ih =>
    intro acc0 cs fl at_ qr s after hcl hfl hat hqr_le hqr1 hqr2 h
    rw [parseMlBasicStep] at h
    split at h
    · nomatch h
    · nomatch h
    · rename_i rest _
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have hqr0 : qr = 0 := by
        cases qr with
        | zero => rfl
        | succ k => exact absurd rfl (hqr1 (Nat.succ_le_succ (Nat.zero_le k)) _)
      subst hqr0
      refine ⟨['"', '"'], [.plain, .plain], ['"', '"'], by simp [List.reverse_cons, List.append_assoc], ?_, rfl⟩
      simp [renderMultilineAtoms, isModelHorizWs, isDisallowedControl]
    · rename_i rest _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have hqr0 : qr = 0 := by
        cases qr with
        | zero => rfl
        | succ k => exact absurd rfl (hqr1 (Nat.succ_le_succ (Nat.zero_le k)) _)
      subst hqr0
      refine ⟨['"'], [.plain], ['"'], by simp [List.reverse_cons], ?_, rfl⟩
      simp [renderMultilineAtoms, isModelHorizWs, isDisallowedControl]
    · rename_i rest _ _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact ⟨[], [], [], by simp, rfl, rfl⟩
    · rename_i rest
      cases hesc : parseBasicEscape rest with
      | ok pair =>
        rcases pair with ⟨ch, afterEsc⟩; rw [hesc] at h
        obtain ⟨esc, hdec, hesc_cs⟩ := parseBasicEscape_witness hesc
        have hcl_after : CleanNorm afterEsc := (cleanNorm_of_suffix hcl hesc_cs).2
        obtain ⟨csTail, atoms, enc, hs, hrend, hafter_eq⟩ :=
          ih (ch :: acc0) afterEsc (fl := false) (at_ := false) (qr := 0)
            hcl_after (fun e => nomatch e) (fun e => nomatch e)
            (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h
        refine ⟨ch :: csTail, .escape esc :: atoms, renderBasicEscapeChars esc ++ enc,
          by simpa [List.reverse_cons, List.append_assoc] using hs,
          by simp [renderMultilineAtoms, hdec, hrend], ?_⟩
        rw [hafter_eq] at hesc_cs
        have hcons : '\\' :: rest = '\\' :: ((renderBasicEscapeChars esc).tail ++ (enc ++ ['"', '"', '"'] ++ after)) := by
          cases esc <;> simpa [renderBasicEscapeChars, List.cons_append, List.append_assoc] using hesc_cs
        obtain ⟨_, rfl⟩ := List.cons.inj hcons
        cases esc <;> simp [renderBasicEscapeChars, List.append_assoc]
      | error err =>
        rw [hesc] at h; dsimp only at h
        cases hsw : skipHorizWs rest with
        | cons cNl afterNl =>
          rw [hsw] at h
          by_cases hnl_c : cNl = '\n'
          · subst hnl_c
            have hcl_rest := (cleanNorm_cons.mp hcl).2
            obtain ⟨hr_eq, hws1_ok⟩ := skipHorizWs_witness rest
            rw [hsw] at hr_eq
            have hcl_afterNl : CleanNorm afterNl := (cleanNorm_cons.mp (cleanNorm_of_suffix hcl_rest hr_eq).2).2
            obtain ⟨hanl_eq, hws2_ok, hanl_hd⟩ := skipHorizAndNl_witness afterNl
            have hcl_skip : CleanNorm (skipHorizAndNl afterNl) := (cleanNorm_of_suffix hcl_afterNl hanl_eq).2
            obtain ⟨csTail, atoms, enc, hs, hrend, hskip_eq⟩ :=
              ih acc0 (skipHorizAndNl afterNl) (fl := false) (at_ := true) (qr := 0)
                hcl_skip (fun e => nomatch e) (fun _ => hanl_hd)
                (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h
            let ws1 := String.ofList (takeHorizPrefix rest)
            let ws2 := String.ofList (takeHorizAndNlPrefix afterNl)
            refine ⟨csTail, .lineTrim ws1 ws2 :: atoms, '\\' :: ws1.toList ++ '\n' :: ws2.toList ++ enc,
              hs, ?_, ?_⟩
            · simp [renderMultilineAtoms, ws1, ws2, hws1_ok, hws2_ok, hrend]
            · (conv => lhs; rw [hr_eq, hanl_eq, hskip_eq])
              simp [ws1, ws2, String.toList_ofList, List.append_assoc]
          · split at h
            · rename_i _ heq; exact absurd (List.cons.inj heq).1 hnl_c
            · split at h <;> simp at h
        | nil =>
          rw [hsw] at h; dsimp only at h
          split at h <;> simp at h
    · rename_i c rest _ _ _ hnot3 hbs
      obtain ⟨⟨hctrl, hcr⟩, hcl_rest⟩ := cleanNorm_cons.mp hcl
      have hbs' : c ≠ '\\' := hbs
      have hc_bad : (c == '\\' || c == '\r' || isDisallowedControl c) = false := by
        simp [beq_false_of_ne hbs', beq_false_of_ne hcr, hctrl]
      have hfl_ok : (fl && c == '\n') = false := by
        cases fl with
        | false => rfl
        | true =>
          have hne_nl : c ≠ '\n' := by rintro rfl; exact hfl rfl rest rfl
          simp [beq_false_of_ne hne_nl]
      have hat_ok : (at_ && (isModelHorizWs c || c == '\n')) = false := by
        cases at_ with
        | false => rfl
        | true =>
          obtain ⟨hw, hn⟩ := hat rfl c rest rfl
          simp [hw, beq_false_of_ne hn]
      by_cases hcq : c = '"'
      · subst hcq
        have hqr_lt2 : ¬(qr ≥ 2) := fun hge => hqr2 hge rest rfl
        have hr_not2 : ∀ r', rest ≠ '"' :: '"' :: r' := fun r' hr' => hnot3 r' rfl hr'
        have hr_not1 : qr + 1 ≥ 2 → ∀ r', rest ≠ '"' :: r' := fun hge r' hr' =>
          hqr1 (by omega) r' (by simp [hr'])
        obtain ⟨csTail, atoms, enc, hs, hrend, hrest_eq⟩ :=
          ih ('"' :: acc0) rest (fl := false) (at_ := false) (qr := qr + 1)
            hcl_rest (fun e => nomatch e) (fun e => nomatch e) (by omega) (fun _ => hr_not2) hr_not1 h
        refine ⟨'"' :: csTail, .plain :: atoms, '"' :: enc,
          by simpa [List.reverse_cons, List.append_assoc] using hs, ?_, by simp [hrest_eq]⟩
        simp [renderMultilineAtoms, isDisallowedControl, isModelHorizWs, hqr_lt2, hrend]
      · obtain ⟨csTail, atoms, enc, hs, hrend, hrest_eq⟩ :=
          ih (c :: acc0) rest (fl := false) (at_ := false) (qr := 0)
            hcl_rest (fun e => nomatch e) (fun e => nomatch e)
            (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h
        refine ⟨c :: csTail, .plain :: atoms, c :: enc,
          by simpa [List.reverse_cons, List.append_assoc] using hs, ?_, by simp [hrest_eq]⟩
        simp [renderMultilineAtoms, hc_bad, hfl_ok, hat_ok, beq_false_of_ne hcq, hrend]

/-- `parseMultilineBasicString` produces a `StringStyle.multilineBasic` witness. -/
theorem parseMultilineBasicString_witness {rest after : List Char} {s : String}
    (hcl : CleanNorm rest) (h : parseMultilineBasicString rest = .ok (s, after)) :
    ∃ style rs, renderStringLiteral s style = some rs ∧ '"' :: '"' :: '"' :: rest = rs.toList ++ after := by
  cases rest with
  | cons c0 r0 =>
    by_cases hnl : c0 = '\n'
    · subst hnl
      unfold parseMultilineBasicString at h; dsimp only at h
      obtain ⟨csTail, atoms, enc, hs, hrend, hr0_eq⟩ :=
        parseMlBasicBody_aux (r0.length + 1) [] r0 (fl := false) (at_ := false) (qr := 0)
          (cleanNorm_cons.mp hcl).2 (fun e => nomatch e) (fun e => nomatch e)
          (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h
      simp only [List.reverse_nil, List.nil_append] at hs; subst hs
      refine ⟨.multilineBasic (some (true, atoms)), "\"\"\"\n" ++ String.ofList enc ++ "\"\"\"", ?_, ?_⟩
      · simp [renderStringLiteral, String.toList_ofList, hrend]
      · simp [hr0_eq, String.toList_append, String.toList_ofList,
          show ("\"\"\"\n" : String).toList = ['"', '"', '"', '\n'] from rfl,
          show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.append_assoc]
    · have h' : parseMultilineBasicBodyFuel ((c0 :: r0).length + 1) [] (c0 :: r0) = .ok (s, after) := by
        unfold parseMultilineBasicString at h; dsimp only at h
        split at h
        · rename_i r heq; exact absurd (List.cons.inj heq).1 hnl
        · rename_i r _; exact h
      obtain ⟨csTail, atoms, enc, hs, hrend, hrest_eq⟩ :=
        parseMlBasicBody_aux ((c0 :: r0).length + 1) [] (c0 :: r0) (fl := true) (at_ := false) (qr := 0)
          hcl (fun _ _ heq => hnl (List.cons.inj heq).1) (fun e => nomatch e)
          (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h'
      simp only [List.reverse_nil, List.nil_append] at hs; subst hs
      refine ⟨.multilineBasic (some (false, atoms)), "\"\"\"" ++ String.ofList enc ++ "\"\"\"", ?_, ?_⟩
      · simp [renderStringLiteral, String.toList_ofList, hrend]
      · simp [hrest_eq, String.toList_append, String.toList_ofList,
          show ("\"\"\"" : String).toList = ['"', '"', '"'] from rfl, List.append_assoc]
  | nil => simp [parseMultilineBasicString, parseMultilineBasicBodyFuel] at h

private def utf8SumW : List Char → Nat | [] => 0 | c :: cs => c.utf8Size + utf8SumW cs

private theorem utf8SumW_append (a b : List Char) : utf8SumW (a ++ b) = utf8SumW a + utf8SumW b := by
  induction a <;> simp_all [utf8SumW, Nat.add_assoc]

private theorem utf8ByteSize_eq_utf8SumW (s : String) : s.utf8ByteSize = utf8SumW s.toList := by
  suffices ∀ cs, (String.ofList cs).utf8ByteSize = utf8SumW cs by simpa [String.ofList_toList] using this s.toList
  intro cs; induction cs with
  | nil => rfl
  | cons c cs ih => rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton, ih, utf8SumW]

private theorem utf8GetAux_append_addW (a b : List Char) (i₀ : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (a ++ b) i₀ ⟨i₀.byteIdx + utf8SumW a⟩ =
      String.Pos.Raw.utf8GetAux b ⟨i₀.byteIdx + utf8SumW a⟩ ⟨i₀.byteIdx + utf8SumW a⟩ := by
  induction a generalizing i₀ with
  | nil => simp [utf8SumW]
  | cons c cs ih =>
    simp only [List.cons_append, utf8SumW]; rw [String.Pos.Raw.utf8GetAux.eq_def]
    have := Char.utf8Size_pos c
    have hne : i₀ ≠ ⟨i₀.byteIdx + (c.utf8Size + utf8SumW cs)⟩ := fun heq => by
      have := congrArg String.Pos.Raw.byteIdx heq; dsimp at this; omega
    simp only [hne, ↓reduceIte, show i₀ + c = ⟨i₀.byteIdx + c.utf8Size⟩ from String.Pos.Raw.ext String.Pos.Raw.byteIdx_add_char]
    rw [show i₀.byteIdx + (c.utf8Size + utf8SumW cs) = (i₀.byteIdx + c.utf8Size) + utf8SumW cs by omega]
    exact ih _

private theorem get_at_utf8SumW (s : String) (a : List Char) (c : Char) (b : List Char) (h : s.toList = a ++ c :: b) :
    String.Pos.Raw.get s ⟨utf8SumW a⟩ = c ∧ String.Pos.Raw.next s ⟨utf8SumW a⟩ = ⟨utf8SumW a + c.utf8Size⟩ ∧
      String.Pos.Raw.atEnd s ⟨utf8SumW a⟩ = false := by
  have hget : String.Pos.Raw.get s ⟨utf8SumW a⟩ = c := by
    change String.Pos.Raw.utf8GetAux s.toList 0 ⟨utf8SumW a⟩ = c
    rw [h, show (⟨utf8SumW a⟩ : String.Pos.Raw) = ⟨(0 : String.Pos.Raw).byteIdx + utf8SumW a⟩ by simp [String.Pos.Raw.byteIdx_zero],
      utf8GetAux_append_addW a (c :: b) 0, String.Pos.Raw.utf8GetAux.eq_def]; simp
  refine ⟨hget, String.Pos.Raw.ext (by change ((⟨utf8SumW a⟩ : String.Pos.Raw) + String.Pos.Raw.get s ⟨utf8SumW a⟩).byteIdx = _; rw [hget]; exact String.Pos.Raw.byteIdx_add_char), ?_⟩
  rw [String.Pos.Raw.atEnd.eq_1, decide_eq_false_iff_not]
  have hsz : s.utf8ByteSize = utf8SumW a + (c.utf8Size + utf8SumW b) := by rw [utf8ByteSize_eq_utf8SumW, h, utf8SumW_append, utf8SumW]
  have := Char.utf8Size_pos c; dsimp only; omega

private theorem splitOnAux_no_tripleQuote (s : String) (hno3 : ∀ a b, s.toList ≠ a ++ ['\'', '\'', '\''] ++ b)
    (b i j : String.Pos.Raw) (r : List String) :
    ∀ (pref rem : List Char) (k : Nat), k < 3 → j = ⟨k⟩ → i = ⟨utf8SumW pref + k⟩ →
      s.toList = pref ++ (List.replicate k '\'' ++ rem) →
      (s.splitOnAux "'''" b i j r).length = r.length + 1 := by
  have hrep_sum : ∀ pref k, utf8SumW (pref ++ List.replicate k '\'') = utf8SumW pref + k := fun pref k => by
    rw [utf8SumW_append]; suffices utf8SumW (List.replicate k '\'') = k by rw [this]
    induction k with | zero => rfl | succ k ih => rw [List.replicate_succ, utf8SumW, ih]; change 1 + k = k + 1; omega
  have hsep_all : ∀ k, k < 3 → String.Pos.Raw.get "'''" ⟨k⟩ = '\'' ∧ String.Pos.Raw.next "'''" ⟨k⟩ = ⟨k + 1⟩ ∧
      String.Pos.Raw.atEnd "'''" ⟨k + 1⟩ = decide (k = 2) :=
    fun k hk => by match k with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => omega
  fun_induction String.splitOnAux s "'''" b i j r with
  | case1 => intros; simp +zetaDelta
  | case2 b i j r hati hmatch _ _ hatj _ =>
    intro pref rem k hk hj hi hs
    exfalso
    cases rem with
    | nil =>
      rw [List.append_nil] at hs
      have hsz : s.utf8ByteSize = utf8SumW pref + k := by rw [utf8ByteSize_eq_utf8SumW, hs, hrep_sum]
      rw [String.Pos.Raw.atEnd.eq_1, hi, hsz] at hati; simp at hati
    | cons c rem' =>
      have hsep := hsep_all k hk
      obtain ⟨hget, _, _⟩ := get_at_utf8SumW s (pref ++ List.replicate k '\'') c rem' (by simp [hs])
      rw [hrep_sum] at hget
      have hc : c = '\'' := by simpa [hi, hj, hget, hsep.1] using hmatch
      subst hc
      have hk2 : k = 2 := by simpa +zetaDelta [hj, hsep.2.1, hsep.2.2] using hatj
      subst hk2
      exact hno3 pref rem' (by simpa [List.replicate] using hs)
  | case3 b i j r hati hmatch _ _ hatj ih =>
    intro pref rem k hk hj hi hs
    cases rem with
    | nil =>
      rw [List.append_nil] at hs
      have hsz : s.utf8ByteSize = utf8SumW pref + k := by rw [utf8ByteSize_eq_utf8SumW, hs, hrep_sum]
      rw [String.Pos.Raw.atEnd.eq_1, hi, hsz] at hati; simp at hati
    | cons c rem' =>
      have hsep := hsep_all k hk
      obtain ⟨hget, hnext, _⟩ := get_at_utf8SumW s (pref ++ List.replicate k '\'') c rem' (by simp [hs])
      rw [hrep_sum] at hget hnext
      have hc : c = '\'' := by simpa [hi, hj, hget, hsep.1] using hmatch
      subst hc
      have hk_lt : k + 1 < 3 := by
        have hatj' : ¬ String.Pos.Raw.atEnd "'''" (String.Pos.Raw.next "'''" j) = true := hatj
        rw [hj, hsep.2.1, hsep.2.2] at hatj'; simp at hatj'; omega
      have hrep : List.replicate (k + 1) '\'' ++ rem' = List.replicate k '\'' ++ '\'' :: rem' := by
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
      exact ih pref rem' (k + 1) hk_lt (by change String.Pos.Raw.next "'''" j = _; rw [hj, hsep.2.1])
        (by change String.Pos.Raw.next s i = _; rw [hi, hnext]; exact String.Pos.Raw.ext (by dsimp; change utf8SumW pref + k + 1 = _; omega))
        (by rw [hrep]; exact hs)
  | case4 b i j r hati _ ih =>
    intro pref rem k hk hj hi hs
    cases rem with
    | nil =>
      rw [List.append_nil] at hs
      have hsz : s.utf8ByteSize = utf8SumW pref + k := by rw [utf8ByteSize_eq_utf8SumW, hs, hrep_sum]
      rw [String.Pos.Raw.atEnd.eq_1, hi, hsz] at hati; simp at hati
    | cons c rem' =>
      have hun : i.unoffsetBy j = ⟨utf8SumW pref⟩ := by rw [hi, hj]; apply String.Pos.Raw.ext; dsimp [String.Pos.Raw.unoffsetBy]; omega
      cases hrep_eq : List.replicate k '\'' ++ c :: rem' with
      | nil => cases k <;> simp at hrep_eq
      | cons c0 suf' =>
        obtain ⟨_, hnext0, _⟩ := get_at_utf8SumW s pref c0 suf' (by rw [hs, hrep_eq])
        exact ih (pref ++ [c0]) suf' 0 (by decide) rfl
          (by rw [hun, hnext0]; simp [utf8SumW_append, utf8SumW]) (by simp [hs, hrep_eq])

private theorem containsSubstr_tripleSingle_false {s : String}
    (hno3 : ∀ a b, s.toList ≠ a ++ ['\'', '\'', '\''] ++ b) : containsSubstr s "'''" = false := by
  simp only [containsSubstr, decide_eq_false_iff_not, Nat.not_lt]
  rw [show s.splitOn "'''" = s.splitOnAux "'''" 0 0 0 [] by simp [String.splitOn, show ("'''" == "") = false from rfl]]
  rw [splitOnAux_no_tripleQuote s hno3 0 0 0 [] [] s.toList 0 (by decide) rfl rfl (by simp)]
  decide

private theorem parseMlLiteralStep (fuel : Nat) (acc0 cs : List Char) :
    parseMultilineLiteralBodyFuel (fuel + 1) acc0 cs =
      match cs with
      | [] => .error (mkErr .parseError "unterminated multiline literal string")
      | '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: _ =>
        .error (mkErr .parseError "too many consecutive single quotes at end of multiline literal string")
      | '\'' :: '\'' :: '\'' :: '\'' :: '\'' :: rest =>
        .ok (String.ofList ('\'' :: '\'' :: acc0).reverse, rest)
      | '\'' :: '\'' :: '\'' :: '\'' :: rest =>
        .ok (String.ofList ('\'' :: acc0).reverse, rest)
      | '\'' :: '\'' :: '\'' :: rest =>
        .ok (String.ofList acc0.reverse, rest)
      | c :: rest => parseMultilineLiteralBodyFuel fuel (c :: acc0) rest := by
  (conv => lhs; unfold parseMultilineLiteralBodyFuel)
  split
  · contradiction
  · rfl
  · rfl
  · rename_i rest _ _; cases rest with | nil => rfl | cons r0 rs => by_cases hq : r0 = '\'' <;> subst_vars <;> simp_all
  · rename_i rest _ _ _; cases rest with | nil => rfl | cons r0 rs => by_cases hq : r0 = '\'' <;> subst_vars <;> simp_all
  · rename_i rest _ _ _ _; cases rest with | nil => rfl | cons r0 rs => by_cases hq : r0 = '\'' <;> subst_vars <;> simp_all
  · simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at *; subst_vars; rfl

private theorem parseMlLiteralBody_aux (fuel : Nat) :
    ∀ (acc0 cs : List Char) {qr : Nat} {s : String} {after : List Char},
      CleanNorm cs →
      qr ≤ 2 →
      (qr ≥ 1 → ∀ r, cs ≠ '\'' :: '\'' :: r) →
      (qr ≥ 2 → ∀ r, cs ≠ '\'' :: r) →
      parseMultilineLiteralBodyFuel fuel acc0 cs = .ok (s, after) →
      ∃ csTail,
        s = String.ofList (acc0.reverse ++ csTail) ∧
        cs = csTail ++ ['\'', '\'', '\''] ++ after ∧
        (∀ a b, List.replicate qr '\'' ++ csTail ≠ a ++ ['\'', '\'', '\''] ++ b) := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; nomatch h
  | succ fuel ih =>
    intro acc0 cs qr s after hcl hqr_le hqr1 hqr2 h
    rw [parseMlLiteralStep] at h
    split at h
    · nomatch h
    · nomatch h
    · rename_i rest _
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have hqr0 : qr = 0 := by
        cases qr with | zero => rfl | succ k => exact absurd rfl (hqr1 (Nat.succ_le_succ (Nat.zero_le k)) _)
      subst hqr0
      refine ⟨['\'', '\''], by simp [List.reverse_cons, List.append_assoc], rfl, fun a b hab => ?_⟩
      have := congrArg List.length hab; simp at this; omega
    · rename_i rest _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      have hqr0 : qr = 0 := by
        cases qr with | zero => rfl | succ k => exact absurd rfl (hqr1 (Nat.succ_le_succ (Nat.zero_le k)) _)
      subst hqr0
      refine ⟨['\''], by simp [List.reverse_cons], rfl, fun a b hab => ?_⟩
      have := congrArg List.length hab; simp at this; omega
    · rename_i rest _ _ _
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨[], by simp, rfl, fun a b hab => ?_⟩
      have := congrArg List.length hab; simp at this; omega
    · rename_i c rest _ _ _ hnot3
      have hcl_rest := (cleanNorm_cons.mp hcl).2
      by_cases hcq : c = '\''
      · subst hcq
        have hqr_lt2 : qr < 2 := Nat.lt_of_le_of_ne hqr_le (fun heq => hqr2 (heq ▸ Nat.le_refl _) rest rfl)
        have hr_not2 : ∀ r', rest ≠ '\'' :: '\'' :: r' := fun r' hr' => hnot3 r' rfl hr'
        have hr_not1 : qr + 1 ≥ 2 → ∀ r', rest ≠ '\'' :: r' := fun hge r' hr' =>
          hqr1 (by omega) r' (by simp [hr'])
        obtain ⟨csTail, hs, hrest_eq, hno3⟩ :=
          ih ('\'' :: acc0) rest (qr := qr + 1) hcl_rest (by omega) (fun _ => hr_not2) hr_not1 h
        refine ⟨'\'' :: csTail, by simpa [List.reverse_cons, List.append_assoc] using hs, by simp [hrest_eq], ?_⟩
        intro a b hab
        have hrep : List.replicate (qr + 1) '\'' ++ csTail = List.replicate qr '\'' ++ ('\'' :: csTail) := by
          rw [List.replicate_succ', List.append_assoc, List.singleton_append]
        exact hno3 a b (hrep.trans hab)
      · obtain ⟨csTail, hs, hrest_eq, hno3⟩ :=
          ih (c :: acc0) rest (qr := 0) hcl_rest (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h
        refine ⟨c :: csTail, by simpa [List.reverse_cons, List.append_assoc] using hs, by simp [hrest_eq], ?_⟩
        intro a b hab
        simp only [List.replicate_zero, List.nil_append] at hno3
        have hlong : qr < a.length := by
          by_cases hle : a.length ≤ qr
          · have h1 := congrArg (·[qr]?) hab
            rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self, List.getElem?_cons_zero] at h1
            have h2 : ((a ++ ['\'', '\'', '\''] ++ b)[qr]?) = some '\'' := by
              rw [List.append_assoc, List.getElem?_append_right hle]
              match hd : qr - a.length with
              | 0 => rfl
              | 1 => rfl
              | 2 => rfl
              | _ + 3 => omega
            rw [h2] at h1; exact absurd (Option.some.inj h1) hcq
          · omega
        have hdrop := congrArg (List.drop (qr + 1)) hab
        have hd_l : List.drop (qr + 1) (List.replicate qr '\'' ++ c :: csTail) = csTail := by
          rw [show List.replicate qr '\'' ++ c :: csTail = (List.replicate qr '\'' ++ [c]) ++ csTail by simp,
            List.drop_append_of_le_length (by simp)]; simp
        have hd_r : List.drop (qr + 1) (a ++ ['\'', '\'', '\''] ++ b) = List.drop (qr + 1) a ++ ['\'', '\'', '\''] ++ b := by
          rw [List.append_assoc, List.drop_append_of_le_length (by omega), ← List.append_assoc]
        rw [hd_l, hd_r] at hdrop
        exact hno3 (List.drop (qr + 1) a) b hdrop

/-- `parseMultilineLiteralString` produces a `StringStyle.multilineLiteral` witness. -/
theorem parseMultilineLiteralString_witness {rest after : List Char} {s : String}
    (hcl : CleanNorm rest) (h : parseMultilineLiteralString rest = .ok (s, after)) :
    ∃ style rs, renderStringLiteral s style = some rs ∧ '\'' :: '\'' :: '\'' :: rest = rs.toList ++ after := by
  cases rest with
  | nil => simp [parseMultilineLiteralString, parseMultilineLiteralBodyFuel] at h
  | cons c0 r0 =>
    by_cases hnl : c0 = '\n'
    · subst hnl
      unfold parseMultilineLiteralString at h; dsimp only at h
      have hcl_r0 := (cleanNorm_cons.mp hcl).2
      obtain ⟨csTail, hs, hr0_eq, hno3⟩ := parseMlLiteralBody_aux (r0.length + 1) [] r0 (qr := 0)
        hcl_r0 (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h
      simp only [List.reverse_nil, List.nil_append] at hs; subst hs
      have hcl_tail : CleanNorm csTail := (cleanNorm_of_suffix hcl_r0 (by rw [List.append_assoc] at hr0_eq; exact hr0_eq)).1
      have hclean_s : ((String.ofList csTail).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
        rw [String.toList_ofList]; exact hcl_tail
      have hno_sub := containsSubstr_tripleSingle_false (s := String.ofList csTail)
        (by simpa [String.toList_ofList] using hno3)
      refine ⟨.multilineLiteral true, "'''\n" ++ String.ofList csTail ++ "'''", ?_, ?_⟩
      · unfold renderStringLiteral; dsimp only; rw [hclean_s, hno_sub]; rfl
      · simp [hr0_eq, String.toList_append, String.toList_ofList,
          show ("'''\n" : String).toList = ['\'', '\'', '\'', '\n'] from rfl,
          show ("'''" : String).toList = ['\'', '\'', '\''] from rfl, List.append_assoc]
    · have h' : parseMultilineLiteralBodyFuel ((c0 :: r0).length + 1) [] (c0 :: r0) = .ok (s, after) := by
        unfold parseMultilineLiteralString at h; dsimp only at h
        split at h
        · rename_i r heq; exact absurd (List.cons.inj heq).1 hnl
        · rename_i r _; exact h
      obtain ⟨csTail, hs, hrest_eq, hno3⟩ := parseMlLiteralBody_aux ((c0 :: r0).length + 1) [] (c0 :: r0) (qr := 0)
        hcl (Nat.zero_le _) (fun e => nomatch e) (fun e => nomatch e) h'
      simp only [List.reverse_nil, List.nil_append] at hs; subst hs
      have hcl_tail : CleanNorm csTail := (cleanNorm_of_suffix hcl (by rw [List.append_assoc] at hrest_eq; exact hrest_eq)).1
      have hclean_s : ((String.ofList csTail).toList.all fun c => !isDisallowedControl c && c != '\r') = true := by
        rw [String.toList_ofList]; exact hcl_tail
      have hno_sub := containsSubstr_tripleSingle_false (s := String.ofList csTail)
        (by simpa [String.toList_ofList] using hno3)
      have hno_lead : ((String.ofList csTail).toList.head? != some '\n') = true := by
        rw [String.toList_ofList, bne_iff_ne]
        cases csTail with
        | nil => decide
        | cons t0 ts =>
          simp only [List.cons_append, List.cons.injEq] at hrest_eq
          simp [hrest_eq.1 ▸ hnl]
      refine ⟨.multilineLiteral false, "'''" ++ String.ofList csTail ++ "'''", ?_, ?_⟩
      · unfold renderStringLiteral; dsimp only; rw [hclean_s, Bool.false_or, hno_lead, hno_sub]; rfl
      · simp [hrest_eq, String.toList_append, String.toList_ofList,
          show ("'''" : String).toList = ['\'', '\'', '\''] from rfl, List.append_assoc]

end LeanSwe.Toml.Proofs
