import LeanSwe.NumParse.Model
import LeanSwe.NumParse.Model.FormatIntWitness

namespace LeanSwe.NumParse.Model

/-- Render a positive scientific pair `(mant, exp10)` strictly in scientific notation (`d.ddde±k` or `de±k`). -/
def renderScientificModel (neg : Bool) (mant : Nat) (exp10 : Int) : String :=
  let ds := natToDecCharsPosModel mant []
  let prefixChars := if neg then ['-'] else []
  match ds with
  | [] => "0.0"
  | [d] => String.ofList (prefixChars ++ [d, 'e'] ++ formatIntCharsModel exp10)
  | d :: rest =>
    let adjExp := exp10 + Int.ofNat rest.length
    String.ofList (prefixChars ++ [d, '.'] ++ rest ++ ['e'] ++ formatIntCharsModel adjExp)

private theorem list_contains_false_of_forall_model {cs : List Char} {x : Char}
    (h : ∀ c ∈ cs, c ≠ x) : cs.contains x = false := by
  simp only [Bool.eq_false_iff]; intro hc; exact absurd rfl (h x (List.contains_iff_mem.mp hc))

private theorem consumeDecFloatDigits_append_dec_model
    (ds : List Char) (hds : ∀ c ∈ ds, isDecDigit c = true) (rest : List Char)
    (hrest : rest = [] ∨ ∃ r0 rem, rest = r0 :: rem ∧ isDecDigit r0 = false ∧ r0 ≠ '_')
    (acc count : Nat) :
    consumeDecFloatDigits acc count (ds ++ rest) = .ok (ds.foldl decStepModel acc, count + ds.length, rest) := by
  induction ds generalizing acc count with
  | nil =>
    simp only [List.nil_append, List.foldl_nil, List.length_nil, Nat.add_zero]
    rcases hrest with rfl | ⟨r0, rem, rfl, hnd, hnu⟩
    · rw [consumeDecFloatDigits.eq_1]
    · rw [consumeDecFloatDigits.eq_4 acc count r0 rem (fun _ _ h => absurd h hnu) (fun h => absurd h hnu)]; simp [hnd]
  | cons d ds ih =>
    have hd := hds d (by simp)
    have hdnu : d ≠ '_' := decDigit_ne_of_false_model hd (by decide)
    rw [List.cons_append, consumeDecFloatDigits.eq_4 acc count d (ds ++ rest)
      (fun _ _ h => absurd h hdnu) (fun h => absurd h hdnu)]
    simp only [hd, ↓reduceIte, List.foldl_cons, List.length_cons, decStepModel]
    rw [ih (fun c hc => hds c (by simp [hc])) (acc * 10 + (d.toNat - '0'.toNat)) (count + 1),
        show count + 1 + ds.length = count + (ds.length + 1) by omega]

private theorem parseFloatIntPart_valid_model
    (ds : List Char) (hne : ds ≠ []) (hds : ∀ c ∈ ds, isDecDigit c = true)
    (hhead : ds = ['0'] ∨ ds.head? ≠ some '0')
    (r0 : Char) (rem : List Char) (hr0_nd : isDecDigit r0 = false) (hr0_nu : r0 ≠ '_') :
    parseFloatIntPart (ds ++ r0 :: rem) = .ok (ds.foldl decStepModel 0, r0 :: rem) := by
  rcases hhead with rfl | hhd
  · simp only [List.singleton_append, List.foldl_cons, List.foldl_nil, decStepModel, Nat.zero_mul, Nat.zero_add,
      show '0'.toNat - '0'.toNat = 0 by decide]
    unfold parseFloatIntPart; simp [hr0_nd, beq_false_of_ne hr0_nu]
  · cases ds with
    | nil => exact absurd rfl hne
    | cons d ds =>
      have hd := hds d (by simp)
      have hdz : d ≠ '0' := fun h => hhd (by simp [h])
      have hdnu : d ≠ '_' := decDigit_ne_of_false_model hd (by decide)
      rw [List.cons_append, parseFloatIntPart.eq_5 d (ds ++ r0 :: rem) hdnu hdz]
      simp only [hd, ↓reduceIte]
      rw [consumeDecFloatDigits_append_dec_model ds (fun c hc => hds c (by simp [hc])) (r0 :: rem)
        (Or.inr ⟨r0, rem, rfl, hr0_nd, hr0_nu⟩) (d.toNat - '0'.toNat) 1]
      simp [decStepModel]

private theorem parseFloatExpPart_digit_list_model (ds : List Char) (hne : ds ≠ [])
    (hds : ∀ c ∈ ds, isDecDigit c = true) :
    parseFloatExpPart ds = .ok (Int.ofNat (ds.foldl decStepModel 0), []) ∧
      parseFloatExpPart ('-' :: ds) = .ok (-Int.ofNat (ds.foldl decStepModel 0), []) := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds =>
    have hd := hds d (by simp)
    have hp : d ≠ '+' := decDigit_ne_of_false_model hd (by decide)
    have hm : d ≠ '-' := decDigit_ne_of_false_model hd (by decide)
    have hu : d ≠ '_' := decDigit_ne_of_false_model hd (by decide)
    have hcon := consumeDecFloatDigits_append_dec_model ds (fun c hc => hds c (by simp [hc])) [] (Or.inl rfl) (d.toNat - '0'.toNat) 1
    simp only [List.append_nil] at hcon
    have hfold : ds.foldl decStepModel (d.toNat - '0'.toNat) = (d :: ds).foldl decStepModel 0 := by simp [decStepModel]
    have hmatch : (parseFloatExpPart.match_1 (fun _ => Bool × List Char) (d :: ds)
        (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, d :: ds))) = (false, d :: ds) := by
      split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
    have hstep : ∀ (neg : Bool),
        parseFloatExpPart ((if neg then '-' else '+') :: d :: ds) =
          .ok (if neg then -Int.ofNat ((d :: ds).foldl decStepModel 0) else Int.ofNat ((d :: ds).foldl decStepModel 0), []) := by
      intro neg
      have hs : parseFloatExpPart.match_1 (fun _ => Bool × List Char) ((if neg then '-' else '+') :: d :: ds)
          (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, (if neg then '-' else '+') :: d :: ds)) = (neg, d :: ds) := by
        cases neg <;> rfl
      unfold parseFloatExpPart; dsimp only; rw [hs]; dsimp only
      split
      · contradiction
      · rename_i h; exact absurd (List.cons.inj h).1 hu
      · rename_i c rest _ h; rcases List.cons.inj h with ⟨rfl, rfl⟩
        simp only [hd, ↓reduceIte]; rw [hcon, hfold]
    have hpos : parseFloatExpPart (d :: ds) = parseFloatExpPart ('+' :: d :: ds) := by
      unfold parseFloatExpPart; dsimp only; rw [hmatch]; rfl
    exact ⟨by rw [hpos]; simpa using hstep false, by simpa using hstep true⟩

private theorem parseFloatExpPart_formatIntCharsModel (e : Int) :
    parseFloatExpPart (formatIntCharsModel e) = .ok (e, []) := by
  cases e with
  | ofNat n =>
    cases n with
    | zero => exact (parseFloatExpPart_digit_list_model ['0'] (by simp) (by simp; decide)).1
    | succ m =>
      have h := (parseFloatExpPart_digit_list_model (natToDecCharsPosModel (m + 1) [])
        (natToDecCharsPosModel_nonempty (Nat.succ_pos m)) (natToDecCharsPosModel_all_dec (m + 1))).1
      have hev := natToDecCharsPosModel_eval (m + 1) 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
      rw [hev] at h; exact h
  | negSucc m =>
    have h := (parseFloatExpPart_digit_list_model (natToDecCharsPosModel (m + 1) [])
      (natToDecCharsPosModel_nonempty (Nat.succ_pos m)) (natToDecCharsPosModel_all_dec (m + 1))).2
    have hev := natToDecCharsPosModel_eval (m + 1) 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
    rw [hev] at h; exact h

private theorem parseFloatModelChars_pfx_eq_model (neg : Bool) (d : Char) (rest : List Char)
    (hd : isDecDigit d = true) :
    parseFloatModelChars ((if neg then ['-'] else []) ++ d :: rest) =
      parseFloatModelChars ((if neg then '-' else '+') :: d :: rest) := by
  cases neg with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    have hp : d ≠ '+' := decDigit_ne_of_false_model hd (by decide)
    have hm : d ≠ '-' := decDigit_ne_of_false_model hd (by decide)
    have hmatch : (parseFloatExpPart.match_1 (fun _ => Bool × List Char) (d :: rest)
        (fun r => (false, r)) (fun r => (true, r)) (fun _ => (false, d :: rest))) = (false, d :: rest) := by
      split <;> first | (rename_i h; exact absurd (List.cons.inj h).1 hp) | (rename_i h; exact absurd (List.cons.inj h).1 hm) | rfl
    unfold parseFloatModelChars; dsimp only; rw [hmatch]; rfl

private theorem parseFloatModel_withDot_model (neg : Bool) (intDs fracDs : List Char) (exp? : Option Int)
    (hint_ne : intDs ≠ []) (hint_dec : ∀ c ∈ intDs, isDecDigit c = true)
    (hint_hd : intDs = ['0'] ∨ intDs.head? ≠ some '0')
    (hfrac_ne : fracDs ≠ []) (hfrac_dec : ∀ c ∈ fracDs, isDecDigit c = true) :
    let pfx := if neg then ['-'] else []
    let expTail := match exp? with | none => [] | some e => 'e' :: formatIntCharsModel e
    let s := String.ofList (pfx ++ intDs ++ '.' :: fracDs ++ expTail)
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      parseFloatModel s = .ok (evalFloat neg ((intDs ++ fracDs).foldl decStepModel 0)
        (match exp? with | none => -Int.ofNat fracDs.length | some e => e - Int.ofNat fracDs.length)) := by
  cases intDs with
  | nil => exact absurd rfl hint_ne
  | cons d0 ds0 =>
    cases fracDs with
    | nil => exact absurd rfl hfrac_ne
    | cons f0 frest =>
      dsimp only
      let pfx := if neg then ['-'] else []
      let expTail := match exp? with | none => [] | some e => 'e' :: formatIntCharsModel e
      have hnu : ∀ c ∈ pfx ++ (d0 :: ds0) ++ '.' :: (f0 :: frest) ++ expTail, c ≠ '_' := by
        intro c hc; simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with ((h1 | (rfl | h1)) | (rfl | rfl | h1)) | h1
        · cases neg <;> simp [pfx] at h1; subst h1; decide
        · exact decDigit_ne_of_false_model (hint_dec c (by simp)) (by decide)
        · exact decDigit_ne_of_false_model (hint_dec c (by simp [h1])) (by decide)
        · decide
        · exact decDigit_ne_of_false_model (hfrac_dec c (by simp)) (by decide)
        · exact decDigit_ne_of_false_model (hfrac_dec c (by simp [h1])) (by decide)
        · cases exp? with
          | none => simp [expTail] at h1
          | some e => rcases List.mem_cons.mp h1 with rfl | h1'; decide; exact formatIntCharsModel_ne_underscore e c h1'
      refine ⟨?_, Or.inl (by simp [String.contains_char_eq, String.toList_ofList]), ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_false_of_forall_model hnu
      · unfold parseFloatModel; rw [String.toList_ofList]
        have hd0 := hint_dec d0 (by simp)
        have hre : pfx ++ (d0 :: ds0) ++ '.' :: (f0 :: frest) ++ expTail =
            pfx ++ d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)) := by simp [List.append_assoc]
        rw [hre, parseFloatModelChars_pfx_eq_model neg d0 _ hd0]
        have hsign : parseFloatExpPart.match_1 (fun _ => Bool × List Char)
            ((if neg then '-' else '+') :: d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)))
            (fun r => (false, r)) (fun r => (true, r))
            (fun _ => (false, (if neg then '-' else '+') :: d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)))) =
            (neg, d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail))) := by
          cases neg <;> rfl
        unfold parseFloatModelChars; dsimp only; rw [hsign]; dsimp only
        have hi : d0 ≠ 'i' := decDigit_ne_of_false_model hd0 (by decide)
        have hn : d0 ≠ 'n' := decDigit_ne_of_false_model hd0 (by decide)
        split
        · rename_i h; exact absurd (List.cons.inj h).1 hi
        · rename_i h; exact absurd (List.cons.inj h).1 hn
        · have hpint := parseFloatIntPart_valid_model (d0 :: ds0) hint_ne hint_dec hint_hd '.' ((f0 :: frest) ++ expTail) (by decide) (by decide)
          rw [show d0 :: (ds0 ++ '.' :: ((f0 :: frest) ++ expTail)) = (d0 :: ds0) ++ '.' :: ((f0 :: frest) ++ expTail) by simp, hpint]
          have hf0 := hfrac_dec f0 (by simp)
          have htail : expTail = [] ∨ ∃ r0 rem, expTail = r0 :: rem ∧ isDecDigit r0 = false ∧ r0 ≠ '_' := by
            cases exp? with | none => exact Or.inl rfl | some e => exact Or.inr ⟨'e', formatIntCharsModel e, rfl, by decide, by decide⟩
          have hcon := consumeDecFloatDigits_append_dec_model frest (fun c hc => hfrac_dec c (by simp [hc])) expTail
            htail ((d0 :: ds0).foldl decStepModel 0 * 10 + (f0.toNat - '0'.toNat)) 1
          have hmant : frest.foldl decStepModel ((d0 :: ds0).foldl decStepModel 0 * 10 + (f0.toNat - '0'.toNat)) =
              ((d0 :: ds0) ++ f0 :: frest).foldl decStepModel 0 := by rw [List.foldl_append, List.foldl_cons]; rfl
          have hlen : 1 + frest.length = (f0 :: frest).length := by simp [Nat.add_comm]
          rw [List.cons_append]; simp only []
          have hf0u : f0 ≠ '_' := decDigit_ne_of_false_model hf0 (by decide)
          split
          · rename_i h; exact absurd (List.cons.inj h).1 hf0u
          · rename_i c rest2 _ h; rcases List.cons.inj h with ⟨rfl, rfl⟩
            simp only [hf0, ↓reduceIte, hcon, hmant, hlen]
            cases exp? with
            | none => rfl
            | some e => simp only [expTail, parseFloatExpPart_formatIntCharsModel, List.isEmpty_nil, ↓reduceIte]
          · rename_i h; cases h

/-- `renderScientificModel` emits underscore-free scientific notation that parses back to `evalFloat`. -/
theorem renderScientificModel_spec (neg : Bool) (mant : Nat) (hm : 0 < mant) (exp10 : Int) :
    let s := renderScientificModel neg mant exp10
    (!s.contains '_') = true ∧
      (s.contains '.' = true ∨ s.contains 'e' = true ∨ s.contains 'E' = true) ∧
      parseFloatModel s = Except.ok (evalFloat neg mant exp10) := by
  unfold renderScientificModel
  have hall := natToDecCharsPosModel_all_dec mant
  have hhd := natToDecCharsPosModel_head_ne_zero hm
  have hev := natToDecCharsPosModel_eval mant 0; simp only [Nat.zero_mul, Nat.zero_add] at hev
  cases hds : natToDecCharsPosModel mant [] with
  | nil => exact absurd hds (natToDecCharsPosModel_nonempty hm)
  | cons d rest =>
    rw [hds] at hall hhd hev
    have hd : isDecDigit d = true := hall d (by simp)
    have hd0 : d ≠ '0' := fun h => hhd (by simp [h])
    cases rest with
    | nil =>
      let pfx := if neg then ['-'] else []
      have hnu : ∀ c ∈ pfx ++ [d, 'e'] ++ formatIntCharsModel exp10, c ≠ '_' := by
        intro c hc; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with (h1 | rfl | rfl) | h2
        · cases neg <;> simp [pfx] at h1; subst h1; decide
        · exact decDigit_ne_of_false_model hd (by decide)
        · decide
        · exact formatIntCharsModel_ne_underscore exp10 c h2
      refine ⟨?_, Or.inr (Or.inl (by simp [String.contains_char_eq, String.toList_ofList])), ?_⟩
      · simp only [String.contains_char_eq, String.toList_ofList, Bool.not_eq_true']
        exact list_contains_false_of_forall_model hnu
      · unfold parseFloatModel; rw [String.toList_ofList, List.append_assoc]
        change parseFloatModelChars (pfx ++ d :: 'e' :: formatIntCharsModel exp10) = _
        rw [parseFloatModelChars_pfx_eq_model neg d _ hd]
        have hsign : parseFloatExpPart.match_1 (fun _ => Bool × List Char)
            ((if neg then '-' else '+') :: d :: 'e' :: formatIntCharsModel exp10)
            (fun r => (false, r)) (fun r => (true, r))
            (fun _ => (false, (if neg then '-' else '+') :: d :: 'e' :: formatIntCharsModel exp10)) =
            (neg, d :: 'e' :: formatIntCharsModel exp10) := by
          cases neg <;> rfl
        unfold parseFloatModelChars; dsimp only; rw [hsign]; dsimp only
        split
        · rename_i h; exact absurd (List.cons.inj h).1 (decDigit_ne_of_false_model hd (by decide))
        · rename_i h; exact absurd (List.cons.inj h).1 (decDigit_ne_of_false_model hd (by decide))
        · have hpint := parseFloatIntPart_valid_model [d] (by simp) (by simpa using hd) (Or.inr (by simp [hd0]))
            'e' (formatIntCharsModel exp10) (by decide) (by decide)
          rw [show d :: 'e' :: formatIntCharsModel exp10 = [d] ++ 'e' :: formatIntCharsModel exp10 from rfl, hpint, hev]
          simp [parseFloatExpPart_formatIntCharsModel]
    | cons r0 rs =>
      have hspec := parseFloatModel_withDot_model neg [d] (r0 :: rs) (some (exp10 + Int.ofNat (r0 :: rs).length))
        (by simp) (by simpa using hd) (Or.inr (by simp [hd0])) (by simp) (fun c hc => hall c (by simp [hc]))
      have hre : (if neg then ['-'] else []) ++ [d, '.'] ++ (r0 :: rs) ++ ['e'] ++
            formatIntCharsModel (exp10 + Int.ofNat (r0 :: rs).length) =
          (if neg then ['-'] else []) ++ [d] ++ '.' :: (r0 :: rs) ++ 'e' ::
            formatIntCharsModel (exp10 + Int.ofNat (r0 :: rs).length) := by simp [List.append_assoc]
      have hfold : ([d] ++ (r0 :: rs)).foldl decStepModel 0 = mant := hev
      have hexp : exp10 + Int.ofNat (r0 :: rs).length - Int.ofNat (r0 :: rs).length = exp10 := by omega
      dsimp only at hspec ⊢; rw [hre]; rw [hfold, hexp] at hspec; exact hspec

end LeanSwe.NumParse.Model
