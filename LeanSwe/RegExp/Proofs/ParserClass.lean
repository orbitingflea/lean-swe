import LeanSwe.RegExp.Interface
import LeanSwe.RegExp.Model

namespace LeanSwe.RegExp.Proofs

/-- Map an `Internal.CharPred` to `Model.CharPred`. -/
def toPred : Internal.CharPred → Model.CharPred
  | .digit => .digit
  | .nonDigit => .nonDigit
  | .word => .word
  | .nonWord => .nonWord
  | .space => .space
  | .nonSpace => .nonSpace

/-- Map an `Internal.CharAtom` to `Model.CharAtom`. -/
def toAtom : Internal.CharAtom → Model.CharAtom
  | .any => .any
  | .pred p => .pred (toPred p)
  | .literal c => .literal c
  | .charClass neg ranges preds => .charClass neg ranges (preds.map toPred)

/-- Map an `Internal.RegexAst` to `Model.Regex`. -/
def toModel : Internal.RegexAst → Model.Regex
  | .empty => .empty
  | .char atom => .char (toAtom atom)
  | .anchorStart => .anchorStart
  | .anchorEnd => .anchorEnd
  | .wordBoundary pos => .wordBoundary pos
  | .seq l r => .seq (toModel l) (toModel r)
  | .alt l r => .alt (toModel l) (toModel r)
  | .rep inner minVal max? greedy => .rep (toModel inner) minVal max? greedy

private theorem charPredMatches_eq (p : Internal.CharPred) (c : Char) :
    Internal.charPredMatches p c = Model.charPredMatches (toPred p) c := by
  cases p <;> rfl

/-- Pointwise congruence for `List.flatMap` over list membership. -/
theorem list_flatMap_congr {α β : Type _} {f g : α → List β} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem list_any_pred_eq (preds : List Internal.CharPred) (c : Char) :
    (preds.any fun p => Internal.charPredMatches p c) =
      ((preds.map toPred).any fun p => Model.charPredMatches p c) := by
  rw [List.any_map]
  congr 1
  funext p
  exact charPredMatches_eq p c

/-- `Internal.charAtomMatches` agrees with `Model.charAtomMatches` via `toAtom`. -/
theorem charAtomMatches_eq (atom : Internal.CharAtom) (c : Char) :
    Internal.charAtomMatches atom c = Model.charAtomMatches (toAtom atom) c := by
  cases atom with
  | any => rfl
  | pred p => exact charPredMatches_eq p c
  | literal x => rfl
  | charClass neg ranges preds =>
    simp [Internal.charAtomMatches, Model.charAtomMatches, toAtom, list_any_pred_eq]

/-- Dropping `i < xs.size` elements from `xs.toList` exposes `xs[i]`. -/
theorem array_drop_cons {α : Type _} (xs : Array α) {i : Nat} (hi : i < xs.size) :
    xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
  have hi' : i < xs.toList.length := by simpa using hi
  exact (List.getElem_cons_drop (as := xs.toList) (i := i) hi').symm

/-- Dropping `i ≥ xs.size` elements from `xs.toList` yields `[]`. -/
theorem array_drop_nil {α : Type _} (xs : Array α) {i : Nat} (hi : ¬ i < xs.size) :
    xs.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hi)

/-- In-bounds `a[i]!` equals `a[i]`. -/
theorem arr_getElem! {α : Type _} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] :=
  getElem!_pos a i h

/-- `Internal.mkError` preserves error kind and produces a non-empty message. -/
theorem mkError_ok_props (k : RegexErrorKind) (msg : String) :
    (Internal.mkError k msg).kind = k ∧ (Internal.mkError k msg).message ≠ "" := by
  refine ⟨rfl, ?_⟩
  simp only [Internal.mkError]
  split
  · decide
  · next h =>
    intro heq
    rw [heq] at h
    exact h rfl

/-- Parser-state equivalence relating cursor index `p` in `chars` to suffix `rest`. -/
def ParseResultEq {α β : Type} (lift : α → β) (chars : Array Char) :
    Except RegexError (α × Nat) → Except RegexErrorKind (β × List Char) → Prop
  | .error e, .error k => e.kind = k ∧ e.message ≠ ""
  | .ok (a, p), .ok (b, rest) => b = lift a ∧ chars.toList.drop p = rest
  | _, _ => False

private theorem decodeClassEscape_eq (c : Char) :
    match Internal.decodeClassEscape c, Model.decodeClassEscape c with
    | .single a, .single b => a = b
    | .pred a, .pred b => toPred a = b
    | _, _ => False := by
  by_cases h1 : c = 'd'; · subst h1; rfl
  by_cases h2 : c = 'D'; · subst h2; rfl
  by_cases h3 : c = 'w'; · subst h3; rfl
  by_cases h4 : c = 'W'; · subst h4; rfl
  by_cases h5 : c = 's'; · subst h5; rfl
  by_cases h6 : c = 'S'; · subst h6; rfl
  by_cases h7 : c = 'n'; · subst h7; rfl
  by_cases h8 : c = 'r'; · subst h8; rfl
  by_cases h9 : c = 't'; · subst h9; rfl
  simp [Internal.decodeClassEscape, Model.decodeClassEscape]

private theorem model_parseClassBody_char (neg : Bool) (ranges : List (Char × Char))
    (preds : List Model.CharPred) (c : Char) (rest : List Char)
    (h1 : c ≠ ']') (h2 : c ≠ '\\') :
    Model.parseClassBody neg ranges preds (c :: rest) =
      Model.parseClassAfter neg ranges preds c rest := by
  rw [Model.parseClassBody] <;> simp [h1, h2]

private theorem model_parseClassAfter_char (neg : Bool) (ranges : List (Char × Char))
    (preds : List Model.CharPred) (lo c : Char) (rest : List Char)
    (h1 : c ≠ ']') (h2 : c ≠ '-') (h3 : c ≠ '\\') :
    Model.parseClassAfter neg ranges preds lo (c :: rest) =
      Model.parseClassAfter neg ((lo, lo) :: ranges) preds c rest := by
  rw [Model.parseClassAfter] <;> simp [h1, h2, h3]

private theorem model_parseClassRange_char (neg : Bool) (ranges : List (Char × Char))
    (preds : List Model.CharPred) (lo c : Char) (rest : List Char)
    (h1 : c ≠ ']') (h2 : c ≠ '\\') :
    Model.parseClassRange neg ranges preds lo (c :: rest) =
      if lo.toNat > c.toNat then .error .invalidSyntax
      else Model.parseClassBody neg ((lo, c) :: ranges) preds rest := by
  rw [Model.parseClassRange] <;> simp [h1, h2]

private theorem parseClassTriple_eq :
    ∀ (n : Nat) (chars : Array Char) (pos : Nat),
      chars.size - pos ≤ n →
      (∀ neg ranges preds,
        ParseResultEq toAtom chars
          (Internal.parseClassBody chars neg ranges preds pos)
          (Model.parseClassBody neg ranges (preds.map toPred) (chars.toList.drop pos))) ∧
      (∀ neg ranges preds lo,
        ParseResultEq toAtom chars
          (Internal.parseClassAfter chars neg ranges preds lo pos)
          (Model.parseClassAfter neg ranges (preds.map toPred) lo (chars.toList.drop pos))) ∧
      (∀ neg ranges preds lo,
        ParseResultEq toAtom chars
          (Internal.parseClassRange chars neg ranges preds lo pos)
          (Model.parseClassRange neg ranges (preds.map toPred) lo (chars.toList.drop pos))) := by
  intro n
  induction n with
  | zero =>
    intro chars pos hle
    have hge : ¬ pos < chars.size := by omega
    have hnil : chars.toList.drop pos = [] := array_drop_nil chars hge
    refine ⟨?_, ?_, ?_⟩
    · intro neg ranges preds
      rw [Internal.parseClassBody]
      simp only [hge, ↓reduceDIte, hnil, Model.parseClassBody]
      exact mkError_ok_props .unexpectedEof _
    · intro neg ranges preds lo
      rw [Internal.parseClassAfter]
      simp only [hge, ↓reduceDIte, hnil, Model.parseClassAfter]
      exact mkError_ok_props .unexpectedEof _
    · intro neg ranges preds lo
      rw [Internal.parseClassRange]
      simp only [hge, ↓reduceDIte, hnil, Model.parseClassRange]
      exact mkError_ok_props .unexpectedEof _
  | succ n ih =>
    intro chars pos hle
    by_cases h : pos < chars.size
    · have hc := array_drop_cons chars h
      refine ⟨?_, ?_, ?_⟩
      · intro neg ranges preds
        rw [Internal.parseClassBody]
        simp only [h, ↓reduceDIte, hc]
        by_cases hbr : chars[pos] = ']'
        · simp only [hbr, beq_self_eq_true, ↓reduceIte, Model.parseClassBody, List.isEmpty_map]
          split
          · exact mkError_ok_props .invalidSyntax _
          · simp [ParseResultEq, toAtom]
        · have hneBr : (chars[pos] == ']') = false := beq_false_of_ne hbr
          simp only [hneBr, Bool.false_eq_true, ↓reduceIte]
          by_cases hbs : chars[pos] = '\\'
          · simp only [hbs, beq_self_eq_true, ↓reduceIte]
            by_cases h1 : pos + 1 < chars.size
            · have hc1 := array_drop_cons chars h1
              simp only [h1, ↓reduceDIte, hc1, Model.parseClassBody]
              have hdec := decodeClassEscape_eq chars[pos + 1]
              cases hdi : Internal.decodeClassEscape chars[pos + 1] with
              | single lo =>
                cases hdm : Model.decodeClassEscape chars[pos + 1] with
                | single lom =>
                  simp only [hdi, hdm] at hdec ⊢
                  subst hdec
                  exact (ih chars (pos + 2) (by omega)).2.1 neg ranges preds lo
                | pred => simp [hdi, hdm] at hdec
              | pred pi =>
                cases hdm : Model.decodeClassEscape chars[pos + 1] with
                | single => simp [hdi, hdm] at hdec
                | pred pm =>
                  simp only [hdi, hdm] at hdec ⊢
                  have hrec := (ih chars (pos + 2) (by omega)).1 neg ranges (pi :: preds)
                  simpa [List.map_cons, hdec] using hrec
            · have hnil1 := array_drop_nil chars h1
              simp only [h1, ↓reduceDIte, hnil1, Model.parseClassBody]
              exact mkError_ok_props .unexpectedEof _
          · have hneBs : (chars[pos] == '\\') = false := beq_false_of_ne hbs
            simp only [hneBs, Bool.false_eq_true, ↓reduceIte]
            rw [model_parseClassBody_char _ _ _ _ _ hbr hbs]
            exact (ih chars (pos + 1) (by omega)).2.1 neg ranges preds chars[pos]
      · intro neg ranges preds lo
        rw [Internal.parseClassAfter]
        simp only [h, ↓reduceDIte, hc]
        by_cases hbr : chars[pos] = ']'
        · rw [hbr, Model.parseClassAfter]
          simp only [beq_self_eq_true, ↓reduceIte]
          simp [ParseResultEq, toAtom, List.map_reverse]
        · have hneBr : (chars[pos] == ']') = false := beq_false_of_ne hbr
          simp only [hneBr, Bool.false_eq_true, ↓reduceIte]
          by_cases hdash : chars[pos] = '-'
          · simp only [hdash, beq_self_eq_true, ↓reduceIte, Model.parseClassAfter]
            exact (ih chars (pos + 1) (by omega)).2.2 neg ranges preds lo
          · have hneDash : (chars[pos] == '-') = false := beq_false_of_ne hdash
            simp only [hneDash, Bool.false_eq_true, ↓reduceIte]
            by_cases hbs : chars[pos] = '\\'
            · simp only [hbs, beq_self_eq_true, ↓reduceIte]
              by_cases h1 : pos + 1 < chars.size
              · have hc1 := array_drop_cons chars h1
                simp only [h1, ↓reduceDIte, hc1, Model.parseClassAfter]
                have hdec := decodeClassEscape_eq chars[pos + 1]
                cases hdi : Internal.decodeClassEscape chars[pos + 1] with
                | single lo2 =>
                  cases hdm : Model.decodeClassEscape chars[pos + 1] with
                  | single lo2m =>
                    simp only [hdi, hdm] at hdec ⊢
                    subst hdec
                    exact (ih chars (pos + 2) (by omega)).2.1 neg ((lo, lo) :: ranges) preds lo2
                  | pred => simp [hdi, hdm] at hdec
                | pred pi =>
                  cases hdm : Model.decodeClassEscape chars[pos + 1] with
                  | single => simp [hdi, hdm] at hdec
                  | pred pm =>
                    simp only [hdi, hdm] at hdec ⊢
                    have hrec := (ih chars (pos + 2) (by omega)).1 neg ((lo, lo) :: ranges) (pi :: preds)
                    simpa [List.map_cons, hdec] using hrec
              · have hnil1 := array_drop_nil chars h1
                simp only [h1, ↓reduceDIte, hnil1, Model.parseClassAfter]
                exact mkError_ok_props .unexpectedEof _
            · have hneBs : (chars[pos] == '\\') = false := beq_false_of_ne hbs
              simp only [hneBs, Bool.false_eq_true, ↓reduceIte]
              rw [model_parseClassAfter_char _ _ _ _ _ _ hbr hdash hbs]
              exact (ih chars (pos + 1) (by omega)).2.1 neg ((lo, lo) :: ranges) preds chars[pos]
      · intro neg ranges preds lo
        rw [Internal.parseClassRange]
        simp only [h, ↓reduceDIte, hc]
        by_cases hbr : chars[pos] = ']'
        · rw [hbr, Model.parseClassRange]
          simp only [beq_self_eq_true, ↓reduceIte]
          simp [ParseResultEq, toAtom, List.map_reverse]
        · have hneBr : (chars[pos] == ']') = false := beq_false_of_ne hbr
          simp only [hneBr, Bool.false_eq_true, ↓reduceIte]
          by_cases hbs : chars[pos] = '\\'
          · simp only [hbs, beq_self_eq_true, ↓reduceIte]
            by_cases h1 : pos + 1 < chars.size
            · have hc1 := array_drop_cons chars h1
              simp only [h1, ↓reduceDIte]
              rw [hc1, Model.parseClassRange]
              have hdec := decodeClassEscape_eq chars[pos + 1]
              cases hdi : Internal.decodeClassEscape chars[pos + 1] with
              | single hi =>
                cases hdm : Model.decodeClassEscape chars[pos + 1] with
                | single him =>
                  simp only [hdi, hdm] at hdec ⊢
                  subst hdec
                  split
                  · exact mkError_ok_props .invalidSyntax _
                  · exact (ih chars (pos + 2) (by omega)).1 neg ((lo, hi) :: ranges) preds
                | pred => simp [hdi, hdm] at hdec
              | pred pi =>
                cases hdm : Model.decodeClassEscape chars[pos + 1] with
                | single => simp [hdi, hdm] at hdec
                | pred pm =>
                  simp only [hdi, hdm] at hdec ⊢
                  have hrec :=
                    (ih chars (pos + 2) (by omega)).1 neg (('-', '-') :: (lo, lo) :: ranges) (pi :: preds)
                  simpa [List.map_cons, hdec] using hrec
            · have hnil1 := array_drop_nil chars h1
              simp only [h1, ↓reduceDIte]
              rw [hnil1, Model.parseClassRange]
              exact mkError_ok_props .unexpectedEof _
          · have hneBs : (chars[pos] == '\\') = false := beq_false_of_ne hbs
            simp only [hneBs, Bool.false_eq_true, ↓reduceIte]
            rw [model_parseClassRange_char _ _ _ _ _ _ hbr hbs]
            split
            · exact mkError_ok_props .invalidSyntax _
            · exact (ih chars (pos + 1) (by omega)).1 neg ((lo, chars[pos]) :: ranges) preds
    · have hnil : chars.toList.drop pos = [] := array_drop_nil chars h
      refine ⟨?_, ?_, ?_⟩
      · intro neg ranges preds
        rw [Internal.parseClassBody]
        simp only [h, ↓reduceDIte, hnil, Model.parseClassBody]
        exact mkError_ok_props .unexpectedEof _
      · intro neg ranges preds lo
        rw [Internal.parseClassAfter]
        simp only [h, ↓reduceDIte, hnil, Model.parseClassAfter]
        exact mkError_ok_props .unexpectedEof _
      · intro neg ranges preds lo
        rw [Internal.parseClassRange]
        simp only [h, ↓reduceDIte, hnil, Model.parseClassRange]
        exact mkError_ok_props .unexpectedEof _

/-- `Internal.parseCharClass` matches `Model.parseCharClass`. -/
theorem parseCharClass_eq (chars : Array Char) (pos : Nat) :
    ParseResultEq toAtom chars (Internal.parseCharClass chars pos)
      (Model.parseCharClass (chars.toList.drop pos)) := by
  unfold Internal.parseCharClass
  by_cases h : pos < chars.size
  · have hc := array_drop_cons chars h
    simp only [h, ↓reduceDIte, hc]
    by_cases hcar : chars[pos] = '^'
    · simp only [hcar, beq_self_eq_true, ↓reduceIte, Model.parseCharClass]
      exact (parseClassTriple_eq (chars.size - (pos + 1)) chars (pos + 1) (Nat.le_refl _)).1 true [] []
    · have hne : (chars[pos] == '^') = false := beq_false_of_ne hcar
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hmod :
          Model.parseCharClass (chars[pos] :: chars.toList.drop (pos + 1)) =
            Model.parseClassBody false [] [] (chars[pos] :: chars.toList.drop (pos + 1)) := by
        simp [Model.parseCharClass, hcar]
      rw [hmod, ← hc]
      exact (parseClassTriple_eq (chars.size - pos) chars pos (Nat.le_refl _)).1 false [] []
  · have hnil := array_drop_nil chars h
    simp only [h, ↓reduceDIte, hnil, Model.parseCharClass]
    have hbody := (parseClassTriple_eq 0 chars pos (by omega)).1 false [] []
    rwa [hnil] at hbody

private theorem parseDigits_eq :
    ∀ (n : Nat) (chars : Array Char) (acc count pos : Nat),
      chars.size - pos ≤ n →
      let r1 := Internal.parseDigits chars acc count pos
      let r2 := Model.parseDigits acc count (chars.toList.drop pos)
      r2.1 = r1.1 ∧ r2.2.1 = r1.2.1 ∧ chars.toList.drop r1.2.2 = r2.2.2 := by
  intro n
  induction n with
  | zero =>
    intro chars acc count pos hle
    have hge : ¬ pos < chars.size := by omega
    have hnil := array_drop_nil chars hge
    rw [Internal.parseDigits]
    simp only [hge, ↓reduceDIte, hnil, Model.parseDigits]
    exact ⟨trivial, trivial, trivial⟩
  | succ n ih =>
    intro chars acc count pos hle
    by_cases h : pos < chars.size
    · have hc := array_drop_cons chars h
      rw [Internal.parseDigits]
      simp only [h, ↓reduceDIte, hc, Model.parseDigits]
      have hdig : Internal.isDigitChar chars[pos] = Model.isDigitChar chars[pos] := rfl
      rw [hdig]
      split
      · exact ih chars _ _ (pos + 1) (by omega)
      · exact ⟨rfl, rfl, hc⟩
    · have hnil := array_drop_nil chars h
      rw [Internal.parseDigits]
      simp [h, hnil, Model.parseDigits]

/-- `Internal.parseBraceQuantifier` matches `Model.parseBraceQuantifier`. -/
theorem parseBraceQuantifier_eq (chars : Array Char) (pos : Nat) :
    match Internal.parseBraceQuantifier chars pos,
        Model.parseBraceQuantifier (chars.toList.drop pos) with
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | .ok (lo, hi?, p), .ok (lo', hi'?, rest) =>
      lo' = lo ∧ hi'? = hi? ∧ chars.toList.drop p = rest
    | _, _ => False := by
  unfold Internal.parseBraceQuantifier Model.parseBraceQuantifier
  have hd1 := parseDigits_eq (chars.size - pos) chars 0 0 pos (Nat.le_refl _)
  dsimp only at hd1
  cases hid1 : Internal.parseDigits chars 0 0 pos with | mk minVal r1 =>
  cases r1 with | mk minDigits pos1 =>
  cases hmd1 : Model.parseDigits 0 0 (chars.toList.drop pos) with | mk minValM r1M =>
  cases r1M with | mk minDigitsM rest1M =>
  rw [hid1, hmd1] at hd1
  rcases hd1 with ⟨hv1, hc1, hrest1⟩
  dsimp only at hv1 hc1 hrest1
  subst hv1 hc1
  dsimp only
  have hmax : Internal.maxRepetitionCount = Model.maxRepetitionCount := rfl
  rw [hmax]
  by_cases hmin0 : minDigitsM = 0
  · simp [hmin0, mkError_ok_props .invalidSyntax _]
  have hmin0' : (minDigitsM == 0) = false := beq_false_of_ne hmin0
  simp only [hmin0', Bool.false_eq_true, ↓reduceIte]
  by_cases hminMax : minValM > Model.maxRepetitionCount
  · simp [hminMax, mkError_ok_props .invalidSyntax _]
  simp only [hminMax, ↓reduceIte]
  rw [← hrest1]
  by_cases h1 : pos1 < chars.size
  · have hc1' := array_drop_cons chars h1
    simp only [h1, ↓reduceDIte, hc1']
    by_cases hcl : chars[pos1] = '}'
    · simp [hcl]
    · have hneCl : (chars[pos1] == '}') = false :=
        beq_false_of_ne hcl
      simp only [hneCl, Bool.false_eq_true, ↓reduceIte]
      by_cases hcm : chars[pos1] = ','
      · simp only [hcm, beq_self_eq_true, ↓reduceIte]
        by_cases h2 : pos1 + 1 < chars.size
        · have hc2' := array_drop_cons chars h2
          simp only [h2, ↓reduceDIte, hc2']
          by_cases hcl2 : chars[pos1 + 1] = '}'
          · simp [hcl2]
          · have hneCl2 : (chars[pos1 + 1] == '}') = false := beq_false_of_ne hcl2
            simp only [hneCl2, Bool.false_eq_true, ↓reduceIte]
            have hd2 := parseDigits_eq (chars.size - (pos1 + 1)) chars 0 0 (pos1 + 1) (Nat.le_refl _)
            dsimp only at hd2
            rw [hc2'] at hd2
            cases hid2 : Internal.parseDigits chars 0 0 (pos1 + 1) with | mk maxVal r2 =>
            cases r2 with | mk maxDigits pos3 =>
            cases hmd2 : Model.parseDigits 0 0 (chars[pos1 + 1] :: chars.toList.drop (pos1 + 1 + 1)) with | mk maxValM r2M =>
            cases r2M with | mk maxDigitsM rest3M =>
            rw [hid2, hmd2] at hd2
            rcases hd2 with ⟨hv2, hc2, hrest2⟩
            dsimp only at hv2 hc2 hrest2
            subst hv2 hc2
            simp [hcl2]
            by_cases hmax0 : maxDigitsM = 0
            · simp [hmax0, mkError_ok_props .invalidSyntax _]
            simp only [hmax0, ↓reduceIte]
            by_cases hmaxMax : maxValM > Model.maxRepetitionCount
            · simp [hmaxMax, mkError_ok_props .invalidSyntax _]
            simp only [hmaxMax, ↓reduceIte]
            by_cases hltMin : maxValM < minValM
            · simp [hltMin, mkError_ok_props .invalidSyntax _]
            simp only [hltMin, ↓reduceIte]
            rw [← hrest2]
            by_cases h3 : pos3 < chars.size
            · have hc3' := array_drop_cons chars h3
              simp only [h3, ↓reduceDIte, hc3']
              by_cases hcl3 : chars[pos3] = '}'
              · simp [hcl3]
              · simp [hcl3]
                exact mkError_ok_props .invalidSyntax _
            · have hnil3 := array_drop_nil chars h3
              simp only [h3, ↓reduceDIte, hnil3]
              exact mkError_ok_props .unexpectedEof _
        · have hnil2 := array_drop_nil chars h2
          simp only [h2, ↓reduceDIte, hnil2]
          exact mkError_ok_props .unexpectedEof _
      · have hneCm : (chars[pos1] == ',') = false :=
          beq_false_of_ne hcm
        simp [hneCm, hcl, hcm]
        exact mkError_ok_props .invalidSyntax _
  · have hnil1 := array_drop_nil chars h1
    simp only [h1, ↓reduceDIte, hnil1]
    exact mkError_ok_props .unexpectedEof _

/-- `Internal.parseEscape` matches `Model.parseEscape`. -/
theorem parseEscape_eq (chars : Array Char) (pos : Nat) :
    ParseResultEq toModel chars (Internal.parseEscape chars pos)
      (Model.parseEscape (chars.toList.drop pos)) := by
  unfold Internal.parseEscape
  by_cases h : pos < chars.size
  · have hc := array_drop_cons chars h
    simp only [h, ↓reduceDIte, hc, Model.parseEscape]
    by_cases h1 : chars[pos] = 'd'; · simp [h1, ParseResultEq, toModel, toAtom, toPred]
    by_cases h2 : chars[pos] = 'D'; · simp [h2, ParseResultEq, toModel, toAtom, toPred]
    by_cases h3 : chars[pos] = 'w'; · simp [h3, ParseResultEq, toModel, toAtom, toPred]
    by_cases h4 : chars[pos] = 'W'; · simp [h4, ParseResultEq, toModel, toAtom, toPred]
    by_cases h5 : chars[pos] = 's'; · simp [h5, ParseResultEq, toModel, toAtom, toPred]
    by_cases h6 : chars[pos] = 'S'; · simp [h6, ParseResultEq, toModel, toAtom, toPred]
    by_cases h7 : chars[pos] = 'b'; · simp [h7, ParseResultEq, toModel]
    by_cases h8 : chars[pos] = 'B'; · simp [h8, ParseResultEq, toModel]
    by_cases h9 : chars[pos] = 'n'; · simp [h9, ParseResultEq, toModel, toAtom]
    by_cases h10 : chars[pos] = 'r'; · simp [h10, ParseResultEq, toModel, toAtom]
    by_cases h11 : chars[pos] = 't'; · simp [h11, ParseResultEq, toModel, toAtom]
    simp [ParseResultEq, toModel, toAtom]
  · have hnil := array_drop_nil chars h
    simp only [h, ↓reduceDIte, hnil, Model.parseEscape]
    exact mkError_ok_props .unexpectedEof _

/-- `Internal.parseLazyFlag` matches `Model.parseLazyFlag`. -/
theorem parseLazyFlag_eq (chars : Array Char) (pos : Nat) :
    let r1 := Internal.parseLazyFlag chars pos
    let r2 := Model.parseLazyFlag (chars.toList.drop pos)
    r2.1 = r1.1 ∧ chars.toList.drop r1.2 = r2.2 := by
  unfold Internal.parseLazyFlag
  by_cases h : pos < chars.size
  · have hc := array_drop_cons chars h
    simp only [h, ↓reduceDIte, hc]
    by_cases hq : chars[pos] = '?'
    · simp [hq, Model.parseLazyFlag]
    · have hne : (chars[pos] == '?') = false := beq_false_of_ne hq
      have hmod : Model.parseLazyFlag (chars[pos] :: chars.toList.drop (pos + 1)) =
          (true, chars[pos] :: chars.toList.drop (pos + 1)) := by
        simp [Model.parseLazyFlag, hq]
      simp [hne, hmod, hc]
  · have hnil := array_drop_nil chars h
    simp only [h, ↓reduceDIte, hnil, Model.parseLazyFlag]
    exact ⟨trivial, trivial⟩

/-- `Internal.rejectExtraQuantifier` matches `Model.rejectExtraQuantifier`. -/
theorem rejectExtraQuantifier_eq (chars : Array Char) (pos : Nat) :
    match Internal.rejectExtraQuantifier chars pos,
        Model.rejectExtraQuantifier (chars.toList.drop pos) with
    | .ok (), .ok () => True
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  unfold Internal.rejectExtraQuantifier
  by_cases h : pos < chars.size
  · have hc := array_drop_cons chars h
    simp only [h, ↓reduceDIte, hc, Model.rejectExtraQuantifier]
    by_cases h1 : chars[pos] = '*'
    · simp [h1, mkError_ok_props .invalidSyntax _]
    by_cases h2 : chars[pos] = '+'
    · simp [h2, mkError_ok_props .invalidSyntax _]
    by_cases h3 : chars[pos] = '?'
    · simp [h3, mkError_ok_props .invalidSyntax _]
    by_cases h4 : chars[pos] = '{'
    · simp [h4, mkError_ok_props .invalidSyntax _]
    simp [h1, h2, h3, h4]
  · have hnil := array_drop_nil chars h
    simp only [h, ↓reduceDIte, hnil, Model.rejectExtraQuantifier]


end LeanSwe.RegExp.Proofs
