import LeanSwe.RegExp.Interface
import LeanSwe.RegExp.SpecTests

namespace LeanSwe.RegExp.Proofs

open Core
open Core.NondetTest

private def toPred : Internal.CharPred → Model.CharPred
  | .digit => .digit
  | .nonDigit => .nonDigit
  | .word => .word
  | .nonWord => .nonWord
  | .space => .space
  | .nonSpace => .nonSpace

private def toAtom : Internal.CharAtom → Model.CharAtom
  | .any => .any
  | .pred p => .pred (toPred p)
  | .literal c => .literal c
  | .charClass neg ranges preds => .charClass neg ranges (preds.map toPred)

private def toModel : Internal.RegexAst → Model.Regex
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

private theorem list_flatMap_congr {α β : Type _} {f g : α → List β} {xs : List α}
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

private theorem charAtomMatches_eq (atom : Internal.CharAtom) (c : Char) :
    Internal.charAtomMatches atom c = Model.charAtomMatches (toAtom atom) c := by
  cases atom with
  | any => rfl
  | pred p => exact charPredMatches_eq p c
  | literal x => rfl
  | charClass neg ranges preds =>
    simp [Internal.charAtomMatches, Model.charAtomMatches, toAtom, list_any_pred_eq]

private theorem array_drop_cons {α : Type _} (xs : Array α) {i : Nat} (hi : i < xs.size) :
    xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
  have hi' : i < xs.toList.length := by simpa using hi
  exact (List.getElem_cons_drop (as := xs.toList) (i := i) hi').symm

private theorem array_drop_nil {α : Type _} (xs : Array α) {i : Nat} (hi : ¬ i < xs.size) :
    xs.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hi)

private theorem arr_getElem! {α : Type _} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] :=
  getElem!_pos a i h

private theorem mkError_ok_props (k : RegexErrorKind) (msg : String) :
    (Internal.mkError k msg).kind = k ∧ (Internal.mkError k msg).message ≠ "" := by
  refine ⟨rfl, ?_⟩
  simp only [Internal.mkError]
  split
  · decide
  · next h =>
    intro heq
    rw [heq] at h
    exact h rfl

private def ParseResultEq {α β : Type} (lift : α → β) (chars : Array Char) :
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

private theorem parseCharClass_eq (chars : Array Char) (pos : Nat) :
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

private theorem parseBraceQuantifier_eq (chars : Array Char) (pos : Nat) :
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

private theorem parseEscape_eq (chars : Array Char) (pos : Nat) :
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

private theorem parseLazyFlag_eq (chars : Array Char) (pos : Nat) :
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

private theorem rejectExtraQuantifier_eq (chars : Array Char) (pos : Nat) :
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

private theorem parseQuantifierSuffix_eq (atom : Internal.RegexAst) (chars : Array Char) (pos : Nat) :
    ParseResultEq toModel chars (Internal.parseQuantifierSuffix atom chars pos)
      (Model.parseQuantifierSuffix (toModel atom) (chars.toList.drop pos)) := by
  unfold Internal.parseQuantifierSuffix
  by_cases h : pos < chars.size
  · have hc := array_drop_cons chars h
    simp only [h, ↓reduceDIte, hc]
    by_cases hst : chars[pos] = '*'
    · simp only [hst, beq_self_eq_true, ↓reduceIte, Model.parseQuantifierSuffix]
      have hl := parseLazyFlag_eq chars (pos + 1)
      dsimp only at hl
      rw [← hl.1, ← hl.2]
      have hr := rejectExtraQuantifier_eq chars (Internal.parseLazyFlag chars (pos + 1)).2
      cases hr1 : Internal.rejectExtraQuantifier chars (Internal.parseLazyFlag chars (pos + 1)).2 <;>
        cases hr2 : Model.rejectExtraQuantifier (chars.toList.drop (Internal.parseLazyFlag chars (pos + 1)).2) <;>
        rw [hr1, hr2] at hr
      · exact hr
      · exact False.elim hr
      · exact False.elim hr
      · simp [ParseResultEq, Except.map, toModel, hl.2]
    · have hneSt : (chars[pos] == '*') = false := beq_false_of_ne hst
      simp only [hneSt, Bool.false_eq_true, ↓reduceIte]
      by_cases hpl : chars[pos] = '+'
      · simp only [hpl, beq_self_eq_true, ↓reduceIte, Model.parseQuantifierSuffix]
        have hl := parseLazyFlag_eq chars (pos + 1)
        dsimp only at hl
        rw [← hl.1, ← hl.2]
        have hr := rejectExtraQuantifier_eq chars (Internal.parseLazyFlag chars (pos + 1)).2
        cases hr1 : Internal.rejectExtraQuantifier chars (Internal.parseLazyFlag chars (pos + 1)).2 <;>
          cases hr2 : Model.rejectExtraQuantifier (chars.toList.drop (Internal.parseLazyFlag chars (pos + 1)).2) <;>
          rw [hr1, hr2] at hr
        · exact hr
        · exact False.elim hr
        · exact False.elim hr
        · simp [ParseResultEq, Except.map, toModel, hl.2]
      · have hnePl : (chars[pos] == '+') = false := beq_false_of_ne hpl
        simp only [hnePl, Bool.false_eq_true, ↓reduceIte]
        by_cases hqm : chars[pos] = '?'
        · simp only [hqm, beq_self_eq_true, ↓reduceIte, Model.parseQuantifierSuffix]
          have hl := parseLazyFlag_eq chars (pos + 1)
          dsimp only at hl
          rw [← hl.1, ← hl.2]
          have hr := rejectExtraQuantifier_eq chars (Internal.parseLazyFlag chars (pos + 1)).2
          cases hr1 : Internal.rejectExtraQuantifier chars (Internal.parseLazyFlag chars (pos + 1)).2 <;>
            cases hr2 : Model.rejectExtraQuantifier (chars.toList.drop (Internal.parseLazyFlag chars (pos + 1)).2) <;>
            rw [hr1, hr2] at hr
          · exact hr
          · exact False.elim hr
          · exact False.elim hr
          · simp [ParseResultEq, Except.map, toModel, hl.2]
        · have hneQm : (chars[pos] == '?') = false := beq_false_of_ne hqm
          simp only [hneQm, Bool.false_eq_true, ↓reduceIte]
          by_cases hbr : chars[pos] = '{'
          · simp only [hbr, beq_self_eq_true, ↓reduceIte, Model.parseQuantifierSuffix]
            have hb := parseBraceQuantifier_eq chars (pos + 1)
            cases hi : Internal.parseBraceQuantifier chars (pos + 1) with
            | error e =>
              cases hm : Model.parseBraceQuantifier (chars.toList.drop (pos + 1)) with
              | error k => rw [hi, hm] at hb; exact hb
              | ok => rw [hi, hm] at hb; exact False.elim hb
            | ok v1 =>
              cases hm : Model.parseBraceQuantifier (chars.toList.drop (pos + 1)) with
              | error => rw [hi, hm] at hb; exact False.elim hb
              | ok v2 =>
                obtain ⟨lo, hi?, p⟩ := v1
                obtain ⟨lo', hi'?, rest⟩ := v2
                rw [hi, hm] at hb
                rcases hb with ⟨rfl, rfl, hd⟩
                simp only [bind, Except.bind]
                have hl := parseLazyFlag_eq chars p
                dsimp only at hl
                rw [← hd, ← hl.1, ← hl.2]
                have hr := rejectExtraQuantifier_eq chars (Internal.parseLazyFlag chars p).2
                cases hr1 : Internal.rejectExtraQuantifier chars (Internal.parseLazyFlag chars p).2 <;>
                  cases hr2 : Model.rejectExtraQuantifier (chars.toList.drop (Internal.parseLazyFlag chars p).2) <;>
                  rw [hr1, hr2] at hr
                · exact hr
                · exact False.elim hr
                · exact False.elim hr
                · simp [ParseResultEq, pure, Except.pure, toModel]
          · have hneBr : (chars[pos] == '{') = false := beq_false_of_ne hbr
            simp [hneBr, Model.parseQuantifierSuffix, hst, hpl, hqm, hbr, ParseResultEq, hc]
  · have hnil := array_drop_nil chars h
    simp only [h, ↓reduceDIte, hnil, Model.parseQuantifierSuffix]
    exact ⟨rfl, hnil⟩

private theorem isSeqStop_eq (chars : Array Char) (pos : Nat) :
    Internal.isSeqStop chars pos =
      match chars.toList.drop pos with
      | [] | '|' :: _ | ')' :: _ => true
      | _ => false := by
  unfold Internal.isSeqStop
  by_cases h : pos < chars.size
  · have hc := array_drop_cons chars h
    simp only [h, ↓reduceDIte, hc]
    by_cases h1 : chars[pos] = '|'
    · simp [h1]
    by_cases h2 : chars[pos] = ')'
    · simp [h2]
    simp [h1, h2]
  · have hnil := array_drop_nil chars h
    simp [h, hnil]

private def modelGroupBody (fuel : Nat) (cs : List Char) :
    Except RegexErrorKind (Model.Regex × List Char) :=
  match Model.parseAlt fuel cs with
  | .error err => .error err
  | .ok (inner, rest1) =>
    match rest1 with
    | ')' :: rest2 => Except.ok (inner, rest2)
    | [] => .error .unexpectedEof
    | _ => .error .invalidSyntax

private theorem modelGroupBody_bind_eq (x : Except RegexErrorKind (Model.Regex × List Char)) :
    (do
      let (inner, rest1) ← x
      match rest1 with
      | ')' :: rest2 => return (inner, rest2)
      | [] => .error .unexpectedEof
      | _ => .error .invalidSyntax) =
    (match x with
    | .error err => .error err
    | .ok (inner, rest1) =>
      match rest1 with
      | ')' :: rest2 => Except.ok (inner, rest2)
      | [] => .error .unexpectedEof
      | _ => .error .invalidSyntax) := by
  cases x with
  | error e => rfl
  | ok v =>
    rcases v with ⟨inner, rest1⟩
    cases rest1 with
    | nil => rfl
    | cons c r => by_cases hc : c = ')' <;> simp [hc, bind, Except.bind, pure, Except.pure]

private theorem model_parseAtom_lparen_noncap (fuel : Nat) (rest : List Char) :
    Model.parseAtom (fuel + 1) ('(' :: '?' :: ':' :: rest) = modelGroupBody fuel rest := by
  unfold Model.parseAtom modelGroupBody
  dsimp only
  exact modelGroupBody_bind_eq (Model.parseAlt fuel rest)

private theorem model_parseAtom_lparen_cap (fuel : Nat) (cs : List Char)
    (h : ¬ ∃ r, cs = '?' :: ':' :: r) :
    Model.parseAtom (fuel + 1) ('(' :: cs) = modelGroupBody fuel cs := by
  unfold Model.parseAtom modelGroupBody
  dsimp only
  cases cs with
  | nil => exact modelGroupBody_bind_eq _
  | cons c1 r1 =>
    by_cases h1 : c1 = '?'
    · subst h1
      cases r1 with
      | nil => exact modelGroupBody_bind_eq _
      | cons c2 r2 =>
        by_cases h2 : c2 = ':'
        · subst h2; exact False.elim (h ⟨r2, rfl⟩)
        · simp [h2]; exact modelGroupBody_bind_eq _
    · simp [h1]; exact modelGroupBody_bind_eq _

private theorem parseMain_eq :
    ∀ (fuel : Nat) (chars : Array Char) (pos : Nat),
      ParseResultEq toModel chars (Internal.parseAlt fuel chars pos)
        (Model.parseAlt fuel (chars.toList.drop pos)) ∧
      ParseResultEq toModel chars (Internal.parseSeq fuel chars pos)
        (Model.parseSeq fuel (chars.toList.drop pos)) ∧
      ParseResultEq toModel chars (Internal.parseAtom fuel chars pos)
        (Model.parseAtom fuel (chars.toList.drop pos)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro chars pos
    refine ⟨?_, ?_, ?_⟩ <;>
      · simp only [Internal.parseAlt, Internal.parseSeq, Internal.parseAtom,
          Model.parseAlt, Model.parseSeq, Model.parseAtom]
        exact mkError_ok_props .unexpectedEof _
  | succ fuel ih =>
    intro chars pos
    refine ⟨?_, ?_, ?_⟩
    · simp only [Internal.parseAlt, Model.parseAlt, bind, Except.bind]
      have hs := (ih chars pos).2.1
      cases hi : Internal.parseSeq fuel chars pos with
      | error e =>
        cases hm : Model.parseSeq fuel (chars.toList.drop pos) with
        | error k => rw [hi, hm] at hs; exact hs
        | ok => rw [hi, hm] at hs; exact False.elim hs
      | ok v =>
        cases hm : Model.parseSeq fuel (chars.toList.drop pos) with
        | error => rw [hi, hm] at hs; exact False.elim hs
        | ok vm =>
          rw [hi, hm] at hs
          obtain ⟨lhs, pos1⟩ := v
          obtain ⟨lhsm, restm⟩ := vm
          rcases hs with ⟨rfl, hd1⟩
          rw [← hd1]
          by_cases hpos1 : pos1 < chars.size
          · have hc1 := array_drop_cons chars hpos1
            simp only [hpos1, ↓reduceDIte, hc1]
            by_cases hbar : chars[pos1] = '|'
            · simp only [hbar, beq_self_eq_true, ↓reduceIte]
              have ha := (ih chars (pos1 + 1)).1
              cases hai : Internal.parseAlt fuel chars (pos1 + 1) with
              | error =>
                cases ham : Model.parseAlt fuel (chars.toList.drop (pos1 + 1)) <;>
                  rw [hai, ham] at ha
                · exact ha
                · exact False.elim ha
              | ok v2 =>
                cases ham : Model.parseAlt fuel (chars.toList.drop (pos1 + 1)) with
                | error => rw [hai, ham] at ha; exact False.elim ha
                | ok vm2 =>
                  rw [hai, ham] at ha
                  obtain ⟨rhs, pos2⟩ := v2
                  obtain ⟨rhsm, rest2m⟩ := vm2
                  rcases ha with ⟨rfl, hd2⟩
                  simp [ParseResultEq, pure, Except.pure, toModel, hd2]
            · have hne : (chars[pos1] == '|') = false := beq_false_of_ne hbar
              simp [hne, hbar, hc1, ParseResultEq, pure, Except.pure]
          · have hnil1 := array_drop_nil chars hpos1
            simp [hpos1, hnil1, ParseResultEq, pure, Except.pure]
    · simp only [Internal.parseSeq]
      by_cases h : pos < chars.size
      · have hc := array_drop_cons chars h
        simp only [h, ↓reduceDIte]
        by_cases hstop : chars[pos] = '|' ∨ chars[pos] = ')'
        · have hb : (chars[pos] == '|' || chars[pos] == ')') = true := by
            rcases hstop with h1 | h1 <;> simp [h1]
          simp only [hb, ↓reduceIte]
          rw [hc]
          rcases hstop with h1 | h1 <;>
            simp [h1, hc, Model.parseSeq, ParseResultEq, toModel]
        · have hstop' := not_or.mp hstop
          have hnb : (chars[pos] == '|' || chars[pos] == ')') = false := by
            simp [hstop'.1, hstop'.2]
          simp only [hnb, Bool.false_eq_true, ↓reduceIte]
          by_cases hq : Internal.isLeadingQuantifier chars[pos] = true
          · simp only [hq, ↓reduceIte, hc]
            have hq' : ((chars[pos] = '*' ∨ chars[pos] = '+') ∨ chars[pos] = '?') ∨ chars[pos] = '{' := by
              unfold Internal.isLeadingQuantifier at hq
              simpa [Bool.or_eq_true, beq_iff_eq] using hq
            rcases hq' with ((h1 | h1) | h1) | h1 <;>
              simp [h1, Model.parseSeq, ParseResultEq, mkError_ok_props .invalidSyntax _]
          · have hnq : (Internal.isLeadingQuantifier chars[pos]) = false :=
              Bool.eq_false_iff.mpr hq
            simp only [hnq, Bool.false_eq_true, ↓reduceIte]
            have hnq' : chars[pos] ≠ '*' ∧ chars[pos] ≠ '+' ∧ chars[pos] ≠ '?' ∧ chars[pos] ≠ '{' := by
              unfold Internal.isLeadingQuantifier at hnq
              simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnq
              exact ⟨hnq.1.1.1, hnq.1.1.2, hnq.1.2, hnq.2⟩
            rw [hc]
            have hm_seq : Model.parseSeq (fuel + 1) (chars[pos] :: chars.toList.drop (pos + 1)) =
                (do
                  let (atom, rest1) ← Model.parseAtom fuel (chars[pos] :: chars.toList.drop (pos + 1))
                  let (quant, rest2) ← Model.parseQuantifierSuffix atom rest1
                  match rest2 with
                  | [] | '|' :: _ | ')' :: _ => return (quant, rest2)
                  | _ =>
                    let (tail, rest3) ← Model.parseSeq fuel rest2
                    return (.seq quant tail, rest3)) := by
              simp [Model.parseSeq, hstop'.1, hstop'.2, hnq'.1, hnq'.2.1, hnq'.2.2.1, hnq'.2.2.2,
                bind, Except.bind, pure, Except.pure]
              rfl
            rw [hm_seq]
            simp only [bind, Except.bind]
            have ha := (ih chars pos).2.2
            rw [hc] at ha
            cases hai : Internal.parseAtom fuel chars pos with
            | error =>
              cases ham : Model.parseAtom fuel (chars[pos] :: chars.toList.drop (pos + 1)) <;>
                rw [hai, ham] at ha
              · exact ha
              · exact False.elim ha
            | ok v1 =>
              cases ham : Model.parseAtom fuel (chars[pos] :: chars.toList.drop (pos + 1)) with
              | error => rw [hai, ham] at ha; exact False.elim ha
              | ok vm1 =>
                rw [hai, ham] at ha
                dsimp only
                obtain ⟨atom, pos1⟩ := v1
                obtain ⟨atomM, rest1M⟩ := vm1
                rcases ha with ⟨rfl, hd1⟩
                rw [← hd1]
                have hqs := parseQuantifierSuffix_eq atom chars pos1
                cases hqi : Internal.parseQuantifierSuffix atom chars pos1 with
                | error =>
                  cases hqm : Model.parseQuantifierSuffix (toModel atom) (chars.toList.drop pos1) <;>
                    rw [hqi, hqm] at hqs
                  · exact hqs
                  · exact False.elim hqs
                | ok v2 =>
                  cases hqm : Model.parseQuantifierSuffix (toModel atom) (chars.toList.drop pos1) with
                  | error => rw [hqi, hqm] at hqs; exact False.elim hqs
                  | ok vm2 =>
                    rw [hqi, hqm] at hqs
                    dsimp only
                    obtain ⟨quant, pos2⟩ := v2
                    obtain ⟨quantM, rest2M⟩ := vm2
                    rcases hqs with ⟨rfl, hd2⟩
                    rw [← hd2]
                    have hiss := isSeqStop_eq chars pos2
                    cases hss : Internal.isSeqStop chars pos2 with
                    | true =>
                      rw [hss] at hiss
                      cases hrest2 : chars.toList.drop pos2 with
                      | nil =>
                        simp [hrest2, ParseResultEq, pure, Except.pure]
                      | cons c2 tail2 =>
                        simp only [hrest2] at hiss
                        by_cases hc2b : c2 = '|'
                        · subst hc2b; simp [hrest2, ParseResultEq, pure, Except.pure]
                        · by_cases hc2p : c2 = ')'
                          · subst hc2p; simp [hrest2, ParseResultEq, pure, Except.pure]
                          · simp [hc2b, hc2p] at hiss
                    | false =>
                      rw [hss] at hiss
                      cases hrest2 : chars.toList.drop pos2 with
                      | nil => simp [hrest2] at hiss
                      | cons c2 tail2 =>
                        simp only [hrest2] at hiss
                        by_cases hc2b : c2 = '|'
                        · subst hc2b; simp at hiss
                        · by_cases hc2p : c2 = ')'
                          · subst hc2p; simp at hiss
                          · have hs := (ih chars pos2).2.1
                            rw [hrest2] at hs
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            cases hsi : Internal.parseSeq fuel chars pos2 with
                            | error err =>
                              dsimp only [bind, Except.bind, pure, Except.pure]
                              split
                              · contradiction
                              · next tail heq => exact False.elim (hc2b (List.cons.inj heq).1)
                              · next tail heq => exact False.elim (hc2p (List.cons.inj heq).1)
                              · cases hsm : Model.parseSeq fuel (c2 :: tail2) <;>
                                  rw [hsi, hsm] at hs
                                · exact hs
                                · exact False.elim hs
                            | ok v3 =>
                              dsimp only [bind, Except.bind, pure, Except.pure]
                              split
                              · contradiction
                              · next tail heq => exact False.elim (hc2b (List.cons.inj heq).1)
                              · next tail heq => exact False.elim (hc2p (List.cons.inj heq).1)
                              · cases hsm : Model.parseSeq fuel (c2 :: tail2) with
                                | error => rw [hsi, hsm] at hs; exact False.elim hs
                                | ok vm3 =>
                                  rw [hsi, hsm] at hs
                                  obtain ⟨tail, pos3⟩ := v3
                                  obtain ⟨tailm, rest3m⟩ := vm3
                                  rcases hs with ⟨rfl, hd3⟩
                                  simp [ParseResultEq, toModel, hd3]
      · have hnil := array_drop_nil chars h
        simp [h, hnil, Model.parseSeq, ParseResultEq, toModel]
    · simp only [Internal.parseAtom]
      by_cases h : pos < chars.size
      · have hc := array_drop_cons chars h
        simp only [h, ↓reduceDIte, hc]
        by_cases hdot : chars[pos] = '.'
        · simp [hdot, Model.parseAtom, ParseResultEq, toModel, toAtom]
        have hndot : (chars[pos] == '.') = false := beq_false_of_ne hdot
        simp only [hndot, Bool.false_eq_true, ↓reduceIte]
        by_cases hcar : chars[pos] = '^'
        · simp [hcar, Model.parseAtom, ParseResultEq, toModel]
        have hncar : (chars[pos] == '^') = false := beq_false_of_ne hcar
        simp only [hncar, Bool.false_eq_true, ↓reduceIte]
        by_cases hdol : chars[pos] = '$'
        · simp [hdol, Model.parseAtom, ParseResultEq, toModel]
        have hndol : (chars[pos] == '$') = false := beq_false_of_ne hdol
        simp only [hndol, Bool.false_eq_true, ↓reduceIte]
        by_cases hbs : chars[pos] = '\\'
        · simp only [hbs, beq_self_eq_true, ↓reduceIte, Model.parseAtom]
          exact parseEscape_eq chars (pos + 1)
        have hnbs : (chars[pos] == '\\') = false := beq_false_of_ne hbs
        simp only [hnbs, Bool.false_eq_true, ↓reduceIte]
        by_cases hlb : chars[pos] = '['
        · simp only [hlb, beq_self_eq_true, ↓reduceIte, Model.parseAtom, Except.map]
          have hcc := parseCharClass_eq chars (pos + 1)
          cases hci : Internal.parseCharClass chars (pos + 1) <;>
            cases hcm : Model.parseCharClass (chars.toList.drop (pos + 1)) <;>
            rw [hci, hcm] at hcc
          · exact hcc
          · exact False.elim hcc
          · exact False.elim hcc
          · simp [ParseResultEq, toModel] at hcc ⊢; exact hcc
        have hnlb : (chars[pos] == '[') = false := beq_false_of_ne hlb
        simp only [hnlb, Bool.false_eq_true, ↓reduceIte]
        by_cases hlp : chars[pos] = '('
        · simp only [hlp, beq_self_eq_true, ↓reduceIte]
          have hbody : ∃ bodyPos : Nat,
              (if h2 : pos + 1 + 1 < chars.size then
                  if chars[pos + 1] == '?' && chars[pos + 1 + 1] == ':' then pos + 1 + 2 else pos + 1
                else pos + 1) = bodyPos ∧
              Model.parseAtom (fuel + 1) ('(' :: chars.toList.drop (pos + 1)) =
                modelGroupBody fuel (chars.toList.drop bodyPos) := by
            by_cases h1 : pos + 1 < chars.size
            · have hc1 := array_drop_cons chars h1
              by_cases h2 : pos + 1 + 1 < chars.size
              · have hc2 := array_drop_cons chars h2
                by_cases hqc : chars[pos + 1] = '?'
                · by_cases hcc : chars[pos + 1 + 1] = ':'
                  · refine ⟨pos + 1 + 2, by simp [h2, hqc, hcc], ?_⟩
                    have hpos : pos + 1 + 1 + 1 = pos + 1 + 2 := by omega
                    rw [hc1, hc2, hqc, hcc, hpos, model_parseAtom_lparen_noncap]
                  · refine ⟨pos + 1, by simp [h2, hqc, hcc], ?_⟩
                    rw [model_parseAtom_lparen_cap]
                    intro ⟨r, hr⟩
                    rw [hc1, hc2] at hr
                    exact hcc (List.cons.inj (List.cons.inj hr).2).1
                · refine ⟨pos + 1, by simp [h2, hqc], ?_⟩
                  rw [model_parseAtom_lparen_cap]
                  intro ⟨r, hr⟩
                  rw [hc1] at hr
                  exact hqc (List.cons.inj hr).1
              · have hnil2 := array_drop_nil chars h2
                refine ⟨pos + 1, by simp [h2], ?_⟩
                rw [model_parseAtom_lparen_cap]
                intro ⟨r, hr⟩
                rw [hc1, hnil2] at hr
                have hr2 := (List.cons.inj hr).2
                cases hr2
            · have h2 : ¬ pos + 1 + 1 < chars.size := by omega
              have hnil1 := array_drop_nil chars h1
              refine ⟨pos + 1, by simp [h2], ?_⟩
              rw [model_parseAtom_lparen_cap]
              intro ⟨r, hr⟩
              rw [hnil1] at hr
              cases hr
          rcases hbody with ⟨bodyPos, hbp, hm_atom⟩
          rw [hbp, hm_atom, modelGroupBody]
          simp only [bind, Except.bind, pure, Except.pure]
          have ha := (ih chars bodyPos).1
          cases hai : Internal.parseAlt fuel chars bodyPos with
          | error =>
            cases ham : Model.parseAlt fuel (chars.toList.drop bodyPos) <;>
              rw [hai, ham] at ha
            · dsimp only; exact ha
            · exact False.elim ha
          | ok v1 =>
            cases ham : Model.parseAlt fuel (chars.toList.drop bodyPos) with
            | error => rw [hai, ham] at ha; exact False.elim ha
            | ok vm1 =>
              rw [hai, ham] at ha
              dsimp only
              obtain ⟨inner, pos1⟩ := v1
              obtain ⟨innerM, rest1M⟩ := vm1
              rcases ha with ⟨rfl, hd1⟩
              rw [← hd1]
              by_cases h1 : pos1 < chars.size
              · have hc1 := array_drop_cons chars h1
                simp only [h1, ↓reduceDIte, hc1]
                by_cases hrp : chars[pos1] = ')'
                · simp [hrp, ParseResultEq]
                · have hner : (chars[pos1] == ')') = false := beq_false_of_ne hrp
                  simp [hner, hrp]
                  exact mkError_ok_props .invalidSyntax _
              · have hnil1 := array_drop_nil chars h1
                simp only [h1, ↓reduceDIte, hnil1]
                exact mkError_ok_props .unexpectedEof _
        · have hnlp : (chars[pos] == '(') = false := beq_false_of_ne hlp
          simp only [hnlp, Bool.false_eq_true, ↓reduceIte]
          have hm_lit : Model.parseAtom (fuel + 1) (chars[pos] :: chars.toList.drop (pos + 1)) =
              .ok (.char (.literal chars[pos]), chars.toList.drop (pos + 1)) := by
            simp [Model.parseAtom]
          rw [hm_lit]
          simp [ParseResultEq, toModel, toAtom]
      · have hnil := array_drop_nil chars h
        simp [h, hnil, Model.parseAtom, ParseResultEq, mkError_ok_props .unexpectedEof _]

private theorem parseRegex_eq (pat : String) :
    match Internal.parseRegex pat, Model.parseRegex pat with
    | .ok ast, .ok m => m = toModel ast
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  unfold Internal.parseRegex Model.parseRegex Model.parseRegexChars
  dsimp only
  cases hpl : pat.toList with
  | nil =>
    have hemp : ([] : List Char).toArray.isEmpty = true := rfl
    simp [hemp, toModel]
  | cons c rest =>
    have hemp : (c :: rest).toArray.isEmpty = false := rfl
    have hlen : (c :: rest).toArray.size = (c :: rest).length := rfl
    simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    have ha := (parseMain_eq ((c :: rest).toArray.size * 4 + 4) (c :: rest).toArray 0).1
    have hdrop0 : (c :: rest).toArray.toList.drop 0 = c :: rest := rfl
    rw [hdrop0] at ha
    cases hai : Internal.parseAlt ((c :: rest).toArray.size * 4 + 4) (c :: rest).toArray 0 with
    | error =>
      cases ham : Model.parseAlt ((c :: rest).length * 4 + 4) (c :: rest) <;>
        rw [hai, hlen, ham] at ha
      · exact ha
      · exact False.elim ha
    | ok v =>
      cases ham : Model.parseAlt ((c :: rest).length * 4 + 4) (c :: rest) with
      | error => rw [hai, hlen, ham] at ha; exact False.elim ha
      | ok vm =>
        rw [hai, hlen, ham] at ha
        obtain ⟨ast, pos⟩ := v
        obtain ⟨astm, restm⟩ := vm
        rcases ha with ⟨rfl, hd⟩
        dsimp only
        rw [← hd]
        by_cases hpos : pos < (c :: rest).toArray.size
        · have hc := array_drop_cons (c :: rest).toArray hpos
          have hpos' : pos < rest.length + 1 := by simpa using hpos
          simp [hpos', hc]
          exact mkError_ok_props .invalidSyntax _
        · have hnil := array_drop_nil (c :: rest).toArray hpos
          have hpos' : ¬ pos < rest.length + 1 := by simpa using hpos
          simp [hpos', hnil]

private theorem utf8ByteOffset_succ (cs : List Char) {i : Nat} (hi : i < cs.length) :
    Model.utf8ByteOffset cs (i + 1) = Model.utf8ByteOffset cs i + cs[i].utf8Size := by
  rw [Model.utf8ByteOffset, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  rfl

private theorem buildByteOffsets_loop_inv :
    ∀ (n : Nat) (chars : Array Char) (i acc : Nat) (out : Array Nat),
      chars.size - i ≤ n →
      i ≤ chars.size →
      out.size = i + 1 →
      acc = Model.utf8ByteOffset chars.toList i →
      (∀ k ≤ i, out[k]! = Model.utf8ByteOffset chars.toList k) →
      let res := Internal.buildByteOffsets.loop chars i acc out
      res.size = chars.size + 1 ∧ ∀ k ≤ chars.size, res[k]! = Model.utf8ByteOffset chars.toList k := by
  intro n
  induction n with
  | zero =>
    intro chars i acc out hle hi hs ha hinv
    have hge : ¬ i < chars.size := by omega
    have hieq : i = chars.size := by omega
    subst hieq
    rw [Internal.buildByteOffsets.loop]
    simp only [hge, ↓reduceDIte]
    exact ⟨hs, hinv⟩
  | succ n ih =>
    intro chars i acc out hle hi hs ha hinv
    by_cases h : i < chars.size
    · rw [Internal.buildByteOffsets.loop]
      simp only [h, ↓reduceDIte]
      have hacc' : acc + chars[i].utf8Size = Model.utf8ByteOffset chars.toList (i + 1) := by
        rw [ha, utf8ByteOffset_succ chars.toList (by simpa using h)]
        rfl
      apply ih chars (i + 1) (acc + chars[i].utf8Size) (out.push (acc + chars[i].utf8Size))
        (by omega) h (by simp [hs]) hacc'
      intro k hk
      by_cases hki : k ≤ i
      · have hlt : k < out.size := by omega
        have hlt2 : k < (out.push (acc + chars[i].utf8Size)).size := by simp; omega
        simp only [getElem!_pos, hlt2, Array.getElem_push_lt hlt]
        have hk' := hinv k hki
        simp only [getElem!_pos, hlt] at hk'
        exact hk'
      · have hkeq : k = i + 1 := by omega
        subst hkeq
        have hlt2 : i + 1 < (out.push (acc + chars[i].utf8Size)).size := by simp [hs]
        have hget := arr_getElem! (out.push (acc + chars[i].utf8Size)) (i + 1) hlt2
        have hpush : (out.push (acc + chars[i].utf8Size))[i + 1] = acc + chars[i].utf8Size := by
          simpa [hs] using Array.getElem_push_eq (xs := out) (x := acc + chars[i].utf8Size)
        rw [hget, hpush]
        exact hacc'
    · have hieq : i = chars.size := by omega
      subst hieq
      rw [Internal.buildByteOffsets.loop]
      simp only [h, ↓reduceDIte]
      exact ⟨hs, hinv⟩

private theorem buildByteOffsets_spec (chars : Array Char) :
    (Internal.buildByteOffsets chars).size = chars.size + 1 ∧
    ∀ k ≤ chars.size, (Internal.buildByteOffsets chars)[k]! = Model.utf8ByteOffset chars.toList k := by
  unfold Internal.buildByteOffsets
  refine buildByteOffsets_loop_inv chars.size chars 0 0 ((Array.mkEmpty (chars.size + 1)).push 0)
    (Nat.le_refl _) (Nat.zero_le _) (by simp) (by simp [Model.utf8ByteOffset]) ?_
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  simp [Model.utf8ByteOffset]

private theorem dedupFirstAux_eq (seen xs : List Nat) :
    Internal.dedupFirstAux seen xs = Model.dedupFirstAux seen xs := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x rest ih =>
    simp only [Internal.dedupFirstAux, Model.dedupFirstAux]
    split <;> simp [ih]

private theorem dedupFirstBoolAux_eq (bound : Nat) :
    ∀ (seenList : List Nat) (seen : Array Bool) (xs : List Nat),
      seen.size = bound + 1 →
      (∀ i ≤ bound, seen[i]! = decide (i ∈ seenList)) →
      (∀ x ∈ xs, x ≤ bound) →
      Internal.dedupFirstBoolAux seen xs = Model.dedupFirstAux seenList xs := by
  intro seenList seen xs hs hinv hbd
  induction xs generalizing seenList seen with
  | nil => rfl
  | cons x rest ih =>
    have hx : x ≤ bound := hbd x (by simp)
    have hinvx := hinv x hx
    simp only [Internal.dedupFirstBoolAux, Model.dedupFirstAux, hinvx]
    by_cases hm : x ∈ seenList
    · have hcon : seenList.contains x = true := List.contains_iff_mem.mpr hm
      simp only [hm, decide_true, ↓reduceIte, hcon]
      exact ih seenList seen hs hinv (fun y hy => hbd y (by simp [hy]))
    · have hcon : seenList.contains x = false :=
        Bool.eq_false_iff.mpr fun h => hm (List.contains_iff_mem.mp h)
      simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, hcon]
      congr 1
      apply ih (x :: seenList) (seen.setIfInBounds x true) (by simp [hs])
      · intro i hi
        have his : i < seen.size := by omega
        simp only [getElem!_pos, Array.size_setIfInBounds, his, Array.getElem_setIfInBounds]
        by_cases hxi : x = i
        · subst hxi; simp
        · by_cases hmem : i ∈ seenList
          · have hi' := hinv i hi
            have hget := arr_getElem! seen i his
            rw [hget, decide_eq_true hmem] at hi'
            simp [hxi, hi', hmem, Ne.symm hxi]
          · have hi' := hinv i hi
            have hget := arr_getElem! seen i his
            rw [hget, decide_eq_false hmem] at hi'
            simp [hxi, hi', hmem, Ne.symm hxi]
      · exact fun y hy => hbd y (by simp [hy])

private theorem dedupFirstFast_eq (bound : Nat) (xs : List Nat) (hbd : ∀ x ∈ xs, x ≤ bound) :
    Internal.dedupFirstFast bound xs = Model.dedupFirst xs := by
  unfold Internal.dedupFirstFast Model.dedupFirst
  cases xs with
  | nil => rfl
  | cons x rest =>
    cases rest with
    | nil => simp [Model.dedupFirstAux]
    | cons y rest2 =>
      dsimp only
      split
      · exact dedupFirstAux_eq [] (x :: y :: rest2)
      · apply dedupFirstBoolAux_eq bound [] (Array.replicate (bound + 1) false) (x :: y :: rest2)
          (by simp)
        · intro i hi
          have hlt : i < (Array.replicate (bound + 1) false).size := by simp; omega
          have hget := arr_getElem! (Array.replicate (bound + 1) false) i hlt
          simp [hget]
        · exact hbd

private theorem isWordAt_eq (chars : Array Char) (idx : Nat) :
    Internal.isWordAt chars idx = Model.isWordAt chars.toList idx := by
  unfold Internal.isWordAt Model.isWordAt
  have hg : chars[idx]? = chars.toList[idx]? := by simp
  rw [hg]
  cases chars.toList[idx]? <;> rfl

private theorem isWordBoundary_eq (chars : Array Char) (idx : Nat) :
    Internal.isWordBoundary chars idx = Model.isWordBoundary chars.toList idx := by
  simp [Internal.isWordBoundary, Model.isWordBoundary, isWordAt_eq]

private def TabMatches (n : Nat) (tab : Array (List Nat)) (spec : Nat → List Nat) : Prop :=
  tab.size = n + 1 ∧ ∀ pos ≤ n, tab[pos]! = spec pos ∧ ∀ p ∈ tab[pos]!, pos ≤ p ∧ p ≤ n

private theorem idTab_matches (n : Nat) :
    TabMatches n (Internal.idTab n) (fun pos => [pos]) := by
  refine ⟨by simp [Internal.idTab], ?_⟩
  intro pos hpos
  have hlt : pos < (Internal.idTab n).size := by simp [Internal.idTab]; omega
  refine ⟨by simp [Internal.idTab, getElem!_pos, Nat.lt_succ_of_le hpos], ?_⟩
  intro p hp
  simp [Internal.idTab, getElem!_pos, Nat.lt_succ_of_le hpos] at hp
  subst hp
  exact ⟨Nat.le_refl _, hpos⟩

private theorem dedupFirst_mem_iff (xs : List Nat) (a : Nat) :
    a ∈ Model.dedupFirst xs ↔ a ∈ xs := by
  have haux : ∀ seen ys, a ∈ Model.dedupFirstAux seen ys ↔ a ∈ ys ∧ a ∉ seen := by
    intro seen ys
    induction ys generalizing seen with
    | nil => simp [Model.dedupFirstAux]
    | cons x rest ih =>
      simp only [Model.dedupFirstAux]
      by_cases hc : seen.contains x = true
      · have hx := List.contains_iff_mem.mp hc
        simp only [hc, ↓reduceIte, ih, List.mem_cons]
        constructor
        · rintro ⟨ha, hns⟩; exact ⟨Or.inr ha, hns⟩
        · rintro ⟨rfl | ha, hns⟩
          · exact absurd hx hns
          · exact ⟨ha, hns⟩
      · have hx : x ∉ seen := fun h => hc (List.contains_iff_mem.mpr h)
        simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨ha, hns⟩)
          · exact ⟨Or.inl rfl, hx⟩
          · exact ⟨Or.inr ha, fun hm => hns (Or.inr hm)⟩
        · rintro ⟨rfl | ha, hns⟩
          · exact Or.inl rfl
          · by_cases hax : a = x
            · exact Or.inl hax
            · exact Or.inr ⟨ha, fun hm => by
                rcases hm with rfl | hm'
                · exact hax rfl
                · exact hns hm'⟩
  simp [Model.dedupFirst, haux]

private theorem composeTab_matches {n : Nat} {t1 t2 : Array (List Nat)} {s1 s2 : Nat → List Nat}
    (h1 : TabMatches n t1 s1) (h2 : TabMatches n t2 s2) :
    TabMatches n (Internal.composeTab n t1 t2) (fun pos => Model.dedupFirst ((s1 pos).flatMap s2)) := by
  refine ⟨by simp [Internal.composeTab], ?_⟩
  intro pos hpos
  have hpos1 : pos < t1.size := by rw [h1.1]; omega
  have ht1 := h1.2 pos hpos
  have hflat : (t1[pos]!.flatMap fun mid => t2[mid]!) = (s1 pos).flatMap s2 := by
    rw [ht1.1]
    apply list_flatMap_congr
    intro mid hmid
    have hm' : mid ∈ t1[pos]! := by rw [ht1.1]; exact hmid
    exact (h2.2 mid (ht1.2 mid hm').2).1
  have hbd : ∀ p ∈ (t1[pos]!.flatMap fun mid => t2[mid]!), p ≤ n := by
    intro p hp
    simp only [List.mem_flatMap] at hp
    rcases hp with ⟨mid, hmid, hp'⟩
    have hm := ht1.2 mid hmid
    exact ((h2.2 mid hm.2).2 p hp').2
  have hrow : (Internal.composeTab n t1 t2)[pos]! = Model.dedupFirst ((s1 pos).flatMap s2) := by
    simp only [Internal.composeTab, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn]
    rw [dedupFirstFast_eq n _ hbd, hflat]
  refine ⟨hrow, ?_⟩
  intro p hp
  rw [hrow, dedupFirst_mem_iff, List.mem_flatMap] at hp
  rcases hp with ⟨mid, hmid, hp'⟩
  have hm' : mid ∈ t1[pos]! := by rw [ht1.1]; exact hmid
  have bm := ht1.2 mid hm'
  have hp'' : p ∈ t2[mid]! := by rw [(h2.2 mid bm.2).1]; exact hp'
  have bp := (h2.2 mid bm.2).2 p hp''
  omega

private theorem altTab_matches {n : Nat} {t1 t2 : Array (List Nat)} {s1 s2 : Nat → List Nat}
    (h1 : TabMatches n t1 s1) (h2 : TabMatches n t2 s2) :
    TabMatches n (Internal.altTab n t1 t2) (fun pos => Model.dedupFirst (s1 pos ++ s2 pos)) := by
  refine ⟨by simp [Internal.altTab], ?_⟩
  intro pos hpos
  have ht1 := h1.2 pos hpos
  have ht2 := h2.2 pos hpos
  have hbd : ∀ p ∈ t1[pos]! ++ t2[pos]!, p ≤ n := by
    intro p hp
    rcases List.mem_append.mp hp with hp1 | hp2
    · exact (ht1.2 p hp1).2
    · exact (ht2.2 p hp2).2
  have hrow : (Internal.altTab n t1 t2)[pos]! = Model.dedupFirst (s1 pos ++ s2 pos) := by
    simp only [Internal.altTab, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn]
    rw [dedupFirstFast_eq n _ hbd, ht1.1, ht2.1]
  refine ⟨hrow, ?_⟩
  intro p hp
  rw [hrow, dedupFirst_mem_iff, List.mem_append] at hp
  rcases hp with hp1 | hp2
  · have hp1' : p ∈ t1[pos]! := by rw [ht1.1]; exact hp1
    exact ht1.2 p hp1'
  · have hp2' : p ∈ t2[pos]! := by rw [ht2.1]; exact hp2
    exact ht2.2 p hp2'

private theorem optStep_matches {n : Nat} {stepTab acc : Array (List Nat)}
    {step g : Nat → List Nat} (hstep : TabMatches n stepTab step) (hacc : TabMatches n acc g)
    (greedy : Bool) :
    TabMatches n (Internal.optStep n stepTab greedy acc)
      (fun pos =>
        let more := Model.dedupFirst ((step pos).flatMap g)
        if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more)) := by
  refine ⟨by simp [Internal.optStep], ?_⟩
  intro pos hpos
  have hst := hstep.2 pos hpos
  have hflat : (stepTab[pos]!.flatMap fun mid => acc[mid]!) = (step pos).flatMap g := by
    rw [hst.1]
    apply list_flatMap_congr
    intro mid hmid
    have hm' : mid ∈ stepTab[pos]! := by rw [hst.1]; exact hmid
    exact (hacc.2 mid (hst.2 mid hm').2).1
  have hbdMore : ∀ p ∈ (stepTab[pos]!.flatMap fun mid => acc[mid]!), p ≤ n := by
    intro p hp
    rw [List.mem_flatMap] at hp
    rcases hp with ⟨mid, hmid, hp'⟩
    have hm := hst.2 mid hmid
    exact ((hacc.2 mid hm.2).2 p hp').2
  have hmoreEq :
      Internal.dedupFirstFast n (stepTab[pos]!.flatMap fun mid => acc[mid]!) =
        Model.dedupFirst ((step pos).flatMap g) := by
    rw [dedupFirstFast_eq n _ hbdMore, hflat]
  have hmoreBds : ∀ p ∈ Model.dedupFirst ((step pos).flatMap g), pos ≤ p ∧ p ≤ n := by
    intro p hp
    rw [dedupFirst_mem_iff, List.mem_flatMap] at hp
    rcases hp with ⟨mid, hmid, hp'⟩
    have hm' : mid ∈ stepTab[pos]! := by rw [hst.1]; exact hmid
    have bm := hst.2 mid hm'
    have hp'' : p ∈ acc[mid]! := by rw [(hacc.2 mid bm.2).1]; exact hp'
    have bp := (hacc.2 mid bm.2).2 p hp''
    omega
  have hrow :
      (Internal.optStep n stepTab greedy acc)[pos]! =
        let more := Model.dedupFirst ((step pos).flatMap g)
        if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more) := by
    simp only [Internal.optStep, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, hmoreEq]
    cases greedy
    · have hbd : ∀ p ∈ pos :: Model.dedupFirst ((step pos).flatMap g), p ≤ n := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hpos
        · exact (hmoreBds p hp').2
      simp [dedupFirstFast_eq n _ hbd]
    · have hbd : ∀ p ∈ Model.dedupFirst ((step pos).flatMap g) ++ [pos], p ≤ n := by
        intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · exact (hmoreBds p hp').2
        · simp only [List.mem_singleton] at hp'; subst hp'; exact hpos
      simp [dedupFirstFast_eq n _ hbd]
  refine ⟨hrow, ?_⟩
  intro p hp
  rw [hrow] at hp
  dsimp only at hp
  cases greedy <;> simp only [Bool.false_eq_true, ↓reduceIte, dedupFirst_mem_iff] at hp
  · rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨Nat.le_refl _, hpos⟩
    · exact hmoreBds p hp'
  · rcases List.mem_append.mp hp with hp' | hp'
    · exact hmoreBds p hp'
    · simp only [List.mem_singleton] at hp'; subst hp'; exact ⟨Nat.le_refl _, hpos⟩

private def iterSpec (F : (Nat → List Nat) → (Nat → List Nat)) (g0 : Nat → List Nat) :
    Nat → Nat → List Nat
  | 0 => g0
  | k + 1 => F (iterSpec F g0 k)

private theorem iterSpec_fix {n : Nat} {F : (Nat → List Nat) → (Nat → List Nat)}
    (hExt : ∀ g1 g2, (∀ pos ≤ n, g1 pos = g2 pos) → ∀ pos ≤ n, F g1 pos = F g2 pos)
    {g : Nat → List Nat} (hfix : ∀ pos ≤ n, F g pos = g pos) :
    ∀ k pos, pos ≤ n → iterSpec F g k pos = g pos := by
  intro k
  induction k with
  | zero => intro pos _; rfl
  | succ k ih =>
    intro pos hpos
    calc iterSpec F g (k + 1) pos
        = F (iterSpec F g k) pos := rfl
      _ = F g pos := hExt _ _ ih pos hpos
      _ = g pos := hfix pos hpos

private theorem iterTab_matches {n : Nat} {f : Array (List Nat) → Array (List Nat)}
    {F : (Nat → List Nat) → (Nat → List Nat)}
    (hf : ∀ acc g, TabMatches n acc g → TabMatches n (f acc) (F g))
    (hExt : ∀ g1 g2, (∀ pos ≤ n, g1 pos = g2 pos) → ∀ pos ≤ n, F g1 pos = F g2 pos) :
    ∀ k acc g, TabMatches n acc g →
      TabMatches n (Internal.iterTab f k acc) (iterSpec F g k) := by
  intro k
  induction k with
  | zero =>
    intro acc g hacc
    exact hacc
  | succ k ih =>
    intro acc g hacc
    simp only [Internal.iterTab]
    have hnext := hf acc g hacc
    by_cases heq : f acc == acc
    · simp only [heq, ↓reduceIte]
      have heq' : f acc = acc := beq_iff_eq.mp heq
      have hfix : ∀ pos ≤ n, F g pos = g pos := by
        intro pos hpos
        rw [← (hnext.2 pos hpos).1, heq', (hacc.2 pos hpos).1]
      refine ⟨hacc.1, ?_⟩
      intro pos hpos
      rw [iterSpec_fix hExt hfix (k + 1) pos hpos]
      exact hacc.2 pos hpos
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      have hrec := ih (f acc) (F g) hnext
      refine ⟨hrec.1, ?_⟩
      intro pos hpos
      have hspec : ∀ pos ≤ n, iterSpec F (F g) k pos = iterSpec F g (k + 1) pos := by
        clear hrec hnext hacc heq ih
        induction k with
        | zero => intro pos _; rfl
        | succ m ihm =>
          intro pos hpos
          exact hExt _ _ ihm pos hpos
      rw [← hspec pos hpos]
      exact hrec.2 pos hpos

private theorem iterSpec_compose_eq_evalExact (step : Nat → List Nat) :
    ∀ k pos, iterSpec (fun g p => Model.dedupFirst ((step p).flatMap g)) (fun p => [p]) k pos =
      Model.evalExact step k pos := by
  intro k
  induction k with
  | zero => intro pos; rfl
  | succ k ih =>
    intro pos
    simp only [iterSpec, Model.evalExact]
    have hfn : iterSpec (fun g p => Model.dedupFirst ((step p).flatMap g)) (fun p => [p]) k =
        Model.evalExact step k := funext (ih)
    rw [hfn]

private theorem iterSpec_opt_eq_evalOpt (step : Nat → List Nat) (greedy : Bool) :
    ∀ k pos, iterSpec
        (fun g p =>
          let more := Model.dedupFirst ((step p).flatMap g)
          if greedy then Model.dedupFirst (more ++ [p]) else Model.dedupFirst (p :: more))
        (fun p => [p]) k pos =
      Model.evalOpt step greedy k pos := by
  intro k
  induction k with
  | zero => intro pos; rfl
  | succ k ih =>
    intro pos
    simp only [iterSpec, Model.evalOpt]
    have hfn : iterSpec
        (fun g p =>
          let more := Model.dedupFirst ((step p).flatMap g)
          if greedy then Model.dedupFirst (more ++ [p]) else Model.dedupFirst (p :: more))
        (fun p => [p]) k = Model.evalOpt step greedy k := funext ih
    rw [hfn]

private theorem evalStarAux_fuel_indep {n : Nat} {step : Nat → List Nat}
    (hstep : ∀ i j, i ≤ n → j ∈ step i → i ≤ j ∧ j ≤ n) (greedy : Bool) :
    ∀ (d q fuel : Nat), q ≤ n → n - q ≤ d → n - q ≤ fuel →
      Model.evalStarAux step greedy fuel q = Model.evalStarAux step greedy (n - q) q ∧
      ∀ p ∈ Model.evalStarAux step greedy (n - q) q, q ≤ p ∧ p ≤ n := by
  intro d
  induction d with
  | zero =>
    intro q fuel hq hqd hqf
    have hqn : q = n := by omega
    subst hqn
    have hf : Model.evalStarAux step greedy fuel q = [q] := by
      cases fuel with
      | zero => rfl
      | succ fuel' =>
        have hempty : (step q).filter (· > q) = [] := by
          rw [List.filter_eq_nil_iff]
          intro p hp
          have hb := hstep q p (Nat.le_refl _) hp
          simp; omega
        simp only [Model.evalStarAux, hempty, List.flatMap_nil]
        have hd : Model.dedupFirst [] = [] := rfl
        rw [hd]
        cases greedy <;> rfl
    rw [hf]
    simp only [Nat.sub_self, Model.evalStarAux, List.mem_singleton]
    exact ⟨trivial, fun p hp => by subst hp; exact ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
  | succ d ih =>
    intro q fuel hq hqd hqf
    by_cases hqn : q = n
    · have h0 := ih n fuel (Nat.le_refl _) (by omega) (by omega)
      subst hqn
      exact h0
    · have hlt : q < n := Nat.lt_of_le_of_ne hq hqn
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hrem : ∃ r, n - q = r + 1 := ⟨n - q - 1, by omega⟩
      obtain ⟨r, hr⟩ := hrem
      have hrec_eq :
          ((step q).filter (· > q)).flatMap (Model.evalStarAux step greedy f) =
            ((step q).filter (· > q)).flatMap (Model.evalStarAux step greedy r) := by
        apply list_flatMap_congr
        intro p hp
        simp only [List.mem_filter, decide_eq_true_eq] at hp
        have hp_le := (hstep q p hq hp.1).2
        have hp_d : n - p ≤ d := by omega
        have h1 := (ih p f hp_le hp_d (by omega)).1
        have h2 := (ih p r hp_le hp_d (by omega)).1
        rw [h1, h2]
      have hmore_bds :
          ∀ p ∈ Model.dedupFirst (((step q).filter (· > q)).flatMap (Model.evalStarAux step greedy r)),
            q ≤ p ∧ p ≤ n := by
        intro p hp
        rw [dedupFirst_mem_iff, List.mem_flatMap] at hp
        rcases hp with ⟨mid, hmid, hp'⟩
        simp only [List.mem_filter, decide_eq_true_eq] at hmid
        have hm_le := (hstep q mid hq hmid.1).2
        have hp_eq := (ih mid r hm_le (by omega) (by omega)).1
        rw [hp_eq] at hp'
        have bp := (ih mid r hm_le (by omega) (by omega)).2 p hp'
        omega
      constructor
      · rw [hr]
        simp only [Model.evalStarAux, hrec_eq]
      · rw [hr]
        intro p hp
        simp only [Model.evalStarAux] at hp
        cases greedy <;> simp only [Bool.false_eq_true, ↓reduceIte, dedupFirst_mem_iff] at hp
        · rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨Nat.le_refl _, hq⟩
          · exact hmore_bds p hp'
        · rcases List.mem_append.mp hp with hp' | hp'
          · exact hmore_bds p hp'
          · simp only [List.mem_singleton] at hp'; subst hp'; exact ⟨Nat.le_refl _, hq⟩

private theorem fillStarAux_matches {n : Nat} {stepTab : Array (List Nat)} {step : Nat → List Nat}
    (hstep : TabMatches n stepTab step) (greedy : Bool) :
    ∀ (rem : Nat) (acc : Array (List Nat)),
      rem ≤ n →
      acc.size = n + 1 →
      (∀ q, rem ≤ q → q ≤ n →
        acc[q]! = Model.evalStarAux step greedy (n - q) q ∧ ∀ p ∈ acc[q]!, q ≤ p ∧ p ≤ n) →
      TabMatches n (Internal.fillStarAux n stepTab greedy rem acc)
        (fun q => Model.evalStarAux step greedy (n - q) q) := by
  intro rem
  induction rem with
  | zero =>
    intro acc _ hs hinv
    refine ⟨hs, ?_⟩
    intro pos hpos
    exact hinv pos (Nat.zero_le _) hpos
  | succ rem ih =>
    intro acc hrem hs hinv
    simp only [Internal.fillStarAux]
    have hlt : rem < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hrem
    have hst := hstep.2 rem (Nat.le_of_lt hlt)
    have hstep_bds : ∀ i j, i ≤ n → j ∈ step i → i ≤ j ∧ j ≤ n := by
      intro i j hi hj
      have hj' : j ∈ stepTab[i]! := by rw [(hstep.2 i hi).1]; exact hj
      exact (hstep.2 i hi).2 j hj'
    have hnext_eq :
        ((stepTab[rem]!).filter (· > rem)).flatMap (fun q => acc[q]!) =
          ((step rem).filter (· > rem)).flatMap (Model.evalStarAux step greedy (n - rem - 1)) := by
      rw [hst.1]
      apply list_flatMap_congr
      intro q hq
      simp only [List.mem_filter, decide_eq_true_eq] at hq
      have hq_le := (hstep_bds rem q (Nat.le_of_lt hlt) hq.1).2
      have hq_acc := (hinv q hq.2 hq_le).1
      have hq_fuel := (evalStarAux_fuel_indep hstep_bds greedy (n - q) q (n - rem - 1)
        hq_le (Nat.le_refl _) (by omega)).1
      rw [hq_acc, hq_fuel]
    have hbdMore : ∀ p ∈ ((stepTab[rem]!).filter (· > rem)).flatMap (fun q => acc[q]!), p ≤ n := by
      intro p hp
      rw [List.mem_flatMap] at hp
      rcases hp with ⟨q, hq, hp'⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hq
      have hq_le := (hst.2 q hq.1).2
      exact ((hinv q hq.2 hq_le).2 p hp').2
    have hmoreEq :
        Internal.dedupFirstFast n (((stepTab[rem]!).filter (· > rem)).flatMap fun q => acc[q]!) =
          Model.dedupFirst (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step greedy (n - rem - 1))) := by
      rw [dedupFirstFast_eq n _ hbdMore, hnext_eq]
    have hrow_eq :
        (if greedy then
            Internal.dedupFirstFast n
              (Internal.dedupFirstFast n (((stepTab[rem]!).filter (· > rem)).flatMap fun q => acc[q]!) ++ [rem])
          else
            Internal.dedupFirstFast n
              (rem :: Internal.dedupFirstFast n (((stepTab[rem]!).filter (· > rem)).flatMap fun q => acc[q]!))) =
          Model.evalStarAux step greedy (n - rem) rem := by
      have hsub : n - rem = (n - rem - 1) + 1 := by omega
      rw [hsub, Model.evalStarAux, hmoreEq]
      have hmore_le :
          ∀ p ∈ Model.dedupFirst (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step greedy (n - rem - 1))),
            p ≤ n := by
        intro p hp
        rw [dedupFirst_mem_iff, List.mem_flatMap] at hp
        rcases hp with ⟨q, hq, hp'⟩
        simp only [List.mem_filter, decide_eq_true_eq] at hq
        have hq_le := (hstep_bds rem q (Nat.le_of_lt hlt) hq.1).2
        have hq_fuel := (evalStarAux_fuel_indep hstep_bds greedy (n - q) q (n - rem - 1)
          hq_le (Nat.le_refl _) (by omega)).1
        rw [hq_fuel] at hp'
        exact ((evalStarAux_fuel_indep hstep_bds greedy (n - q) q (n - rem - 1)
          hq_le (Nat.le_refl _) (by omega)).2 p hp').2
      cases hgr : greedy
      · have hbd :
            ∀ p ∈ rem :: Model.dedupFirst
              (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step false (n - rem - 1))), p ≤ n := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Nat.le_of_lt hlt
          · rw [← hgr] at hp'; exact hmore_le p hp'
        simp [dedupFirstFast_eq n _ hbd]
      · have hbd :
            ∀ p ∈ Model.dedupFirst
              (((step rem).filter (· > rem)).flatMap (Model.evalStarAux step true (n - rem - 1))) ++ [rem], p ≤ n := by
          intro p hp
          rcases List.mem_append.mp hp with hp' | hp'
          · rw [← hgr] at hp'; exact hmore_le p hp'
          · simp only [List.mem_singleton] at hp'; subst hp'; exact Nat.le_of_lt hlt
        simp [dedupFirstFast_eq n _ hbd]
    have hrow_bds : ∀ p ∈ Model.evalStarAux step greedy (n - rem) rem, rem ≤ p ∧ p ≤ n :=
      (evalStarAux_fuel_indep hstep_bds greedy (n - rem) rem (n - rem) (Nat.le_of_lt hlt)
        (Nat.le_refl _) (Nat.le_refl _)).2
    apply ih _ (by omega) (by simp [hs])
    intro q hqr hqn
    have hqs : q < acc.size := by omega
    simp only [getElem!_pos, Array.size_setIfInBounds, hqs, Array.getElem_setIfInBounds]
    by_cases heq : q = rem
    · subst heq
      simp only [↓reduceIte, hrow_eq]
      exact ⟨trivial, hrow_bds⟩
    · have hne : rem ≠ q := Ne.symm heq
      have hgt : rem + 1 ≤ q := by omega
      simp only [hne, ↓reduceIte]
      have hget := arr_getElem! acc q hqs
      rw [← hget]
      exact hinv q hgt hqn

private theorem starTab_matches {n : Nat} {stepTab : Array (List Nat)} {step : Nat → List Nat}
    (hstep : TabMatches n stepTab step) (greedy : Bool) :
    TabMatches n (Internal.starTab n stepTab greedy)
      (fun p => Model.evalStarAux step greedy (n - p) p) := by
  unfold Internal.starTab
  apply fillStarAux_matches hstep greedy n (Array.replicate (n + 1) [n]) (Nat.le_refl _) (by simp)
  intro q hnq hqn
  have hq : q = n := by omega
  subst hq
  simp only [Nat.sub_self, Model.evalStarAux, getElem!_pos, Array.size_replicate,
    Nat.lt_succ_self, Array.getElem_replicate, List.mem_singleton]
  exact ⟨trivial, fun p hp => by subst hp; exact ⟨Nat.le_refl _, Nat.le_refl _⟩⟩

private theorem evalTable_matches (chars : Array Char) (ast : Internal.RegexAst) :
    TabMatches chars.size (Internal.evalTable chars ast)
      (Model.evalAt chars.toList (toModel ast)) := by
  induction ast with
  | empty => exact idTab_matches chars.size
  | char atom =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    have hget : chars[pos]? = chars.toList[pos]? := by simp
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel, hget]
    cases hch : chars.toList[pos]? with
    | none => simp
    | some c =>
      simp only [charAtomMatches_eq atom c]
      split
      · simp only [List.mem_singleton]
        have hlt : pos < chars.toList.length := (List.getElem?_eq_some_iff.mp hch).1
        have hlt' : pos < chars.size := by simpa using hlt
        exact ⟨trivial, fun p hp => by subst hp; omega⟩
      · simp
  | anchorStart =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel]
    by_cases h0 : pos = 0
    · subst h0; simp
    · simp [h0]
  | anchorEnd =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel, Array.length_toList]
    by_cases he : pos = chars.size
    · subst he; simp
    · simp [he]
  | wordBoundary positive =>
    refine ⟨by simp [Internal.evalTable], ?_⟩
    intro pos hpos
    simp only [Internal.evalTable, getElem!_pos, Array.size_ofFn, Nat.lt_succ_of_le hpos,
      Array.getElem_ofFn, Model.evalAt, toModel, isWordBoundary_eq]
    split
    · simp only [List.mem_singleton]
      exact ⟨trivial, fun p hp => by subst hp; exact ⟨Nat.le_refl _, hpos⟩⟩
    · simp
  | seq r1 r2 ih1 ih2 =>
    exact composeTab_matches ih1 ih2
  | alt r1 r2 ih1 ih2 =>
    exact altTab_matches ih1 ih2
  | rep inner minVal max? greedy ih =>
    simp only [Internal.evalTable, Model.evalAt, toModel]
    have hcomposeExt :
        ∀ g1 g2 : Nat → List Nat, (∀ pos ≤ chars.size, g1 pos = g2 pos) →
          ∀ pos ≤ chars.size,
            Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g1) =
              Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g2) := by
      intro g1 g2 hg pos hpos
      congr 1
      apply list_flatMap_congr
      intro mid hmid
      have hm' : mid ∈ (Internal.evalTable chars inner)[pos]! := by rw [(ih.2 pos hpos).1]; exact hmid
      exact hg mid ((ih.2 pos hpos).2 mid hm').2
    have hbase :=
      iterTab_matches (fun acc g ha => composeTab_matches ih ha) hcomposeExt minVal
        (Internal.idTab chars.size) (fun p => [p]) (idTab_matches chars.size)
    have hbase' :
        TabMatches chars.size
          (Internal.iterTab (Internal.composeTab chars.size (Internal.evalTable chars inner)) minVal
            (Internal.idTab chars.size))
          (Model.evalExact (Model.evalAt chars.toList (toModel inner)) minVal) := by
      refine ⟨hbase.1, ?_⟩
      intro pos hpos
      rw [← iterSpec_compose_eq_evalExact]
      exact hbase.2 pos hpos
    cases max? with
    | none =>
      exact composeTab_matches hbase' (starTab_matches ih greedy)
    | some maxVal =>
      by_cases hlt : maxVal < minVal
      · simp only [hlt, ↓reduceIte]
        refine ⟨by simp, ?_⟩
        intro pos hpos
        have hlt' : pos < (Array.replicate (chars.size + 1) ([] : List Nat)).size := by simp; omega
        have hget := arr_getElem! (Array.replicate (chars.size + 1) ([] : List Nat)) pos hlt'
        simp [hget]
      · simp only [hlt, ↓reduceIte]
        have hoptExt :
            ∀ g1 g2 : Nat → List Nat, (∀ pos ≤ chars.size, g1 pos = g2 pos) →
              ∀ pos ≤ chars.size,
                (let more := Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g1)
                 if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more)) =
                (let more := Model.dedupFirst ((Model.evalAt chars.toList (toModel inner) pos).flatMap g2)
                 if greedy then Model.dedupFirst (more ++ [pos]) else Model.dedupFirst (pos :: more)) := by
          intro g1 g2 hg pos hpos
          have heq := hcomposeExt g1 g2 hg pos hpos
          dsimp only
          rw [heq]
        have hopt :=
          iterTab_matches (fun acc g ha => optStep_matches ih ha greedy) hoptExt
            (maxVal - minVal) (Internal.idTab chars.size) (fun p => [p]) (idTab_matches chars.size)
        have hopt' :
            TabMatches chars.size
              (Internal.iterTab (Internal.optStep chars.size (Internal.evalTable chars inner) greedy)
                (maxVal - minVal) (Internal.idTab chars.size))
              (Model.evalOpt (Model.evalAt chars.toList (toModel inner)) greedy (maxVal - minVal)) := by
          refine ⟨hopt.1, ?_⟩
          intro pos hpos
          rw [← iterSpec_opt_eq_evalOpt]
          exact hopt.2 pos hpos
        exact composeTab_matches hbase' hopt'

private theorem findFirstIdxAux_eq {n : Nat} {tab : Array (List Nat)} {r : Model.Regex}
    {cs : List Char} (ht : TabMatches n tab (Model.evalAt cs r)) :
    ∀ rem pos, pos + rem = n →
      Internal.findFirstIdxAux tab rem pos = Model.findFirstIdxAux r cs rem pos ∧
      (∀ i j, Internal.findFirstIdxAux tab rem pos = some (i, j) → pos ≤ i ∧ i ≤ j ∧ j ≤ n) := by
  intro rem
  induction rem with
  | zero =>
    intro pos hsum
    have hpos : pos ≤ n := by omega
    rw [Internal.findFirstIdxAux, Model.findFirstIdxAux, (ht.2 pos hpos).1]
    refine ⟨rfl, ?_⟩
    intro i j hij
    cases hrow : Model.evalAt cs r pos with
    | nil => simp [hrow] at hij
    | cons p rest =>
      simp only [hrow, Option.some.injEq, Prod.mk.injEq] at hij
      rcases hij with ⟨rfl, rfl⟩
      have hp : p ∈ tab[pos]! := by rw [(ht.2 pos hpos).1, hrow]; simp
      have bp := (ht.2 pos hpos).2 p hp
      exact ⟨Nat.le_refl _, bp.1, bp.2⟩
  | succ rem ih =>
    intro pos hsum
    have hpos : pos ≤ n := by omega
    rw [Internal.findFirstIdxAux, Model.findFirstIdxAux, (ht.2 pos hpos).1]
    cases hrow : Model.evalAt cs r pos with
    | nil =>
      simp only
      have hrec := ih (pos + 1) (by omega)
      refine ⟨hrec.1, ?_⟩
      intro i j hij
      have b := hrec.2 i j hij
      omega
    | cons p rest =>
      simp only
      refine ⟨trivial, ?_⟩
      intro i j hij
      have hij' : pos = i ∧ p = j := by simpa [hrow] using hij
      rcases hij' with ⟨rfl, rfl⟩
      have hp' : p ∈ tab[pos]! := by rw [(ht.2 pos hpos).1, hrow]; simp
      have bp := (ht.2 pos hpos).2 p hp'
      exact ⟨Nat.le_refl _, bp.1, bp.2⟩

private theorem findFirstIdx_eq (chars : Array Char) (ast : Internal.RegexAst) (start : Nat) :
    Internal.findFirstIdx (Internal.evalTable chars ast) chars.size start =
      Model.findFirstIdx (toModel ast) chars.toList start ∧
    (∀ i j, Internal.findFirstIdx (Internal.evalTable chars ast) chars.size start = some (i, j) →
      start ≤ i ∧ i ≤ j ∧ j ≤ chars.size) := by
  unfold Internal.findFirstIdx Model.findFirstIdx
  simp only [Array.length_toList]
  by_cases hs : start ≤ chars.size
  · simp only [hs, ↓reduceIte]
    exact findFirstIdxAux_eq (evalTable_matches chars ast) (chars.size - start) start (by omega)
  · simp [hs]

private theorem findAllIdxAux_eq (chars : Array Char) (ast : Internal.RegexAst) :
    ∀ fuel cursor,
      Internal.findAllIdxAux (Internal.evalTable chars ast) chars.size fuel cursor =
        Model.findAllIdxAux (toModel ast) chars.toList fuel cursor ∧
      ∀ sp ∈ Internal.findAllIdxAux (Internal.evalTable chars ast) chars.size fuel cursor,
        sp.1 ≤ sp.2 ∧ sp.2 ≤ chars.size := by
  intro fuel
  induction fuel with
  | zero => intro cursor; simp [Internal.findAllIdxAux, Model.findAllIdxAux]
  | succ fuel ih =>
    intro cursor
    rw [Internal.findAllIdxAux, Model.findAllIdxAux]
    have hf := findFirstIdx_eq chars ast cursor
    rw [hf.1]
    cases hres : Model.findFirstIdx (toModel ast) chars.toList cursor with
    | none => simp
    | some v =>
      obtain ⟨i, j⟩ := v
      have hbd := hf.2 i j (by rw [hf.1, hres])
      simp only [Array.length_toList]
      split
      · simp only [List.mem_cons]
        have hrec := ih j
        refine ⟨congrArg ((i, j) :: ·) hrec.1, ?_⟩
        rintro sp (rfl | hsp)
        · exact ⟨hbd.2.1, hbd.2.2⟩
        · exact hrec.2 sp hsp
      · split
        · simp only [List.mem_cons]
          have hrec := ih (j + 1)
          refine ⟨congrArg ((i, j) :: ·) hrec.1, ?_⟩
          rintro sp (rfl | hsp)
          · exact ⟨hbd.2.1, hbd.2.2⟩
          · exact hrec.2 sp hsp
        · simp [hbd.2.1, hbd.2.2]

private theorem findAllIdx_eq (chars : Array Char) (ast : Internal.RegexAst) :
    Internal.findAllIdx chars ast = Model.findAllIdx (toModel ast) chars.toList ∧
    ∀ sp ∈ Internal.findAllIdx chars ast, sp.1 ≤ sp.2 ∧ sp.2 ≤ chars.size := by
  unfold Internal.findAllIdx Model.findAllIdx
  simpa [Array.length_toList] using findAllIdxAux_eq chars ast (chars.size + 1) 0

private theorem mkMatchSpanFast_eq (chars : Array Char) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ chars.size) :
    Internal.mkMatchSpanFast chars (Internal.buildByteOffsets chars) i j =
      Model.mkMatchSpan chars.toList i j := by
  have hb := buildByteOffsets_spec chars
  unfold Internal.mkMatchSpanFast Model.mkMatchSpan
  rw [Array.toList_extract, List.extract_eq_take_drop,
    hb.2 i (Nat.le_trans hij hj), hb.2 j hj]

private theorem list_extract_prefix {α : Type _} (xs : Array α) (cursor i : Nat) :
    (xs.extract cursor i).toList = (xs.toList.drop cursor).take (i - cursor) := by
  rw [Array.toList_extract, List.extract_eq_take_drop]

private theorem replaceSpansFast_eq (chars : Array Char) (rep : String) :
    ∀ (cursor : Nat) (spans : List (Nat × Nat)),
      Internal.replaceSpansFast chars rep cursor spans =
        Model.replaceSpans chars.toList rep cursor spans := by
  intro cursor spans
  induction spans generalizing cursor with
  | nil =>
    simp only [Internal.replaceSpansFast, Model.replaceSpans, list_extract_prefix]
    rw [List.take_of_length_le (by simp)]
  | cons sp rest ih =>
    obtain ⟨i, j⟩ := sp
    simp only [Internal.replaceSpansFast, Model.replaceSpans, list_extract_prefix]
    rw [ih j]

private theorem splitSpansFast_eq (chars : Array Char) :
    ∀ (cursor : Nat) (spans : List (Nat × Nat)),
      Internal.splitSpansFast chars cursor spans =
        Model.splitSpans chars.toList cursor spans := by
  intro cursor spans
  induction spans generalizing cursor with
  | nil =>
    simp only [Internal.splitSpansFast, Model.splitSpans, list_extract_prefix]
    rw [List.take_of_length_le (by simp)]
  | cons sp rest ih =>
    obtain ⟨i, j⟩ := sp
    simp only [Internal.splitSpansFast, Model.splitSpans, list_extract_prefix]
    rw [ih j]

private theorem testPattern_matchesModel_props (pat hay : String) :
    match testPattern pat hay, Model.testPatternModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [testPattern, Internal.testPattern, Model.testPatternModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      have hf := (findFirstIdx_eq hay.toList.toArray ast 0).1
      rw [List.size_toArray] at hf
      simp [hf]

private theorem findFirst_matchesModel_props (pat hay : String) :
    match findFirst pat hay, Model.findFirstModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [findFirst, Internal.findFirst, Model.findFirstModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hf := findFirstIdx_eq chars ast 0
      have hf1 : Internal.findFirstIdx (Internal.evalTable chars ast) chars.size 0 =
          Model.findFirstIdx (toModel ast) hay.toList 0 := hf.1
      cases hres : Model.findFirstIdx (toModel ast) hay.toList 0 with
      | none =>
        have hres' : Internal.findFirstIdx (Internal.evalTable hay.toList.toArray ast)
            hay.toList.toArray.size 0 = none :=
          hf1.trans hres
        rw [hres']
        rfl
      | some v =>
        obtain ⟨i, j⟩ := v
        have hres' : Internal.findFirstIdx (Internal.evalTable chars ast) chars.size 0 = some (i, j) :=
          hf1.trans hres
        have hbd := hf.2 i j hres'
        have hres'' : Internal.findFirstIdx (Internal.evalTable hay.toList.toArray ast)
            hay.toList.toArray.size 0 = some (i, j) := hres'
        rw [hres'', Option.map_some]
        exact congrArg some (mkMatchSpanFast_eq chars hbd.2.1 hbd.2.2)

private theorem findAll_matchesModel_props (pat hay : String) :
    match findAll pat hay, Model.findAllModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [findAll, Internal.findAll, Model.findAllModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hfa := findAllIdx_eq chars ast
      have hfa' : Internal.findAllIdx chars ast = Model.findAllIdx (toModel ast) hay.toList := hfa.1
      simp only [chars, hfa']
      congr 1
      apply List.map_congr_left
      intro sp hsp
      have hbd := hfa.2 sp (by rw [hfa']; exact hsp)
      exact mkMatchSpanFast_eq chars hbd.1 hbd.2

private theorem countMatches_matchesModel_props (pat hay : String) :
    match countMatches pat hay, Model.countMatchesModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [countMatches, Internal.countMatches, Model.countMatchesModel, Except.map]
  have hfa := findAll_matchesModel_props pat hay
  simp only [findAll] at hfa
  cases h1 : Internal.findAll pat hay <;> cases h2 : Model.findAllModel pat hay <;> rw [h1, h2] at hfa
  · exact hfa
  · exact False.elim hfa
  · exact False.elim hfa
  · simp [hfa]

private theorem replaceAll_matchesModel_props (pat hay rep : String) :
    match replaceAll pat hay rep, Model.replaceAllModel pat hay rep with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [replaceAll, Internal.replaceAll, Model.replaceAllModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hfa := (findAllIdx_eq chars ast).1
      have hrep := replaceSpansFast_eq chars rep 0 (Internal.findAllIdx chars ast)
      simpa [chars, hfa] using hrep

private theorem splitBy_matchesModel_props (pat hay : String) :
    match splitBy pat hay, Model.splitByModel pat hay with
    | .ok a, .ok b => a = b
    | .error e, .error k => e.kind = k ∧ e.message ≠ ""
    | _, _ => False := by
  simp only [splitBy, Internal.splitBy, Model.splitByModel, Except.map]
  have hp := parseRegex_eq pat
  cases hpi : Internal.parseRegex pat with
  | error e =>
    cases hpm : Model.parseRegex pat with
    | error k => rw [hpi, hpm] at hp; exact hp
    | ok => rw [hpi, hpm] at hp; exact False.elim hp
  | ok ast =>
    cases hpm : Model.parseRegex pat with
    | error => rw [hpi, hpm] at hp; exact False.elim hp
    | ok m =>
      rw [hpi, hpm] at hp
      dsimp only at hp ⊢
      subst hp
      let chars := hay.toList.toArray
      have hfa := (findAllIdx_eq chars ast).1
      have hsp := splitSpansFast_eq chars 0 (Internal.findAllIdx chars ast)
      simpa [chars, hfa] using hsp

private theorem utf8ByteSize_ofList (l : List Char) :
    (String.ofList l).utf8ByteSize = (l.map Char.utf8Size).sum := by
  induction l with
  | nil => simp
  | cons c cs ih => simp [String.ofList_cons, Char.utf8Size, ih]

private theorem utf8ByteOffset_mono_le (cs : List Char) {i j : Nat} (hij : i ≤ j) :
    Model.utf8ByteOffset cs i ≤ Model.utf8ByteOffset cs j ∧
      Model.utf8ByteOffset cs j ≤ (String.ofList cs).utf8ByteSize := by
  rw [utf8ByteSize_ofList]
  have h1 : Model.utf8ByteOffset cs i ≤ Model.utf8ByteOffset cs j := by
    simp only [Model.utf8ByteOffset]
    have hj' : cs.take j = cs.take (i + (j - i)) := by rw [Nat.add_sub_of_le hij]
    have htake : cs.take j = cs.take i ++ (cs.drop i).take (j - i) := by
      rw [hj', List.take_add]
    rw [htake, List.map_append, List.sum_append]
    exact Nat.le_add_right _ _
  have h2 : Model.utf8ByteOffset cs j ≤ (cs.map Char.utf8Size).sum := by
    simp only [Model.utf8ByteOffset]
    have hsplit : cs = cs.take j ++ cs.drop j := (List.take_append_drop j cs).symm
    have hsum : (cs.map Char.utf8Size).sum =
        ((cs.take j).map Char.utf8Size).sum + ((cs.drop j).map Char.utf8Size).sum := by
      calc (cs.map Char.utf8Size).sum
          = ((cs.take j ++ cs.drop j).map Char.utf8Size).sum := by rw [← hsplit]
        _ = ((cs.take j).map Char.utf8Size).sum + ((cs.drop j).map Char.utf8Size).sum := by
          rw [List.map_append, List.sum_append]
    rw [hsum]
    exact Nat.le_add_right _ _
  exact ⟨h1, h2⟩

/-- Proof of `test_regex_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_regex_onError_returnsNonEmptyMessage :
    AllPass (test_regex_onError_returnsNonEmptyMessage defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := testPattern_matchesModel_props pat hay
  cases h1 : testPattern pat hay with
  | error e =>
    cases h2 : Model.testPatternModel pat hay with
    | error k =>
      rw [h1, h2] at hm
      simp [assert, hm.2]
    | ok =>
      rw [h1, h2] at hm
      exact False.elim hm
  | ok b =>
    simp [assume]

private theorem empty_toList_eq : "".toList = [] := by decide

private theorem parseRegex_empty_eq : Internal.parseRegex "" = .ok .empty := by
  simp [Internal.parseRegex, Array.isEmpty]

private theorem testPattern_empty_eq (hay : String) (h : hay.toList = []) :
    testPattern "" hay = .ok true := by
  simp [testPattern, Internal.testPattern, parseRegex_empty_eq, Except.map,
    Internal.findFirstIdx, Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab, h]

/-- Non-vacuity `CanReach` witness for `test_regex_onError_returnsNonEmptyMessage`. -/
theorem reach_regex_onError_returnsNonEmptyMessage :
    CanReach (test_regex_onError_returnsNonEmptyMessage defaultApi) := by
  refine ⟨"[", "hello", ?_⟩
  have hl : "[".toList = ['['] := by decide
  simp [defaultApi, testPattern, Internal.testPattern, Internal.parseRegex, hl, Array.isEmpty,
    Internal.parseAlt, Internal.parseSeq, Internal.parseAtom, Internal.parseCharClass,
    Internal.parseClassBody, Internal.isLeadingQuantifier, Internal.mkError,
    bind, Except.bind, Except.map, assert]

/-- Proof of `test_regex_testPattern_iff_findFirstSome` for `defaultApi`. -/
theorem proof_regex_testPattern_iff_findFirstSome :
    AllPass (test_regex_testPattern_iff_findFirstSome defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have htp := testPattern_matchesModel_props pat hay
  have hff := findFirst_matchesModel_props pat hay
  cases h1 : testPattern pat hay with
  | error => simp [assume]
  | ok b =>
    rw [h1] at htp
    cases h2 : Model.testPatternModel pat hay with
    | error => rw [h2] at htp; exact False.elim htp
    | ok bm =>
      rw [h2] at htp
      subst htp
      cases hp : Model.parseRegex pat with
      | error => simp [Model.testPatternModel, hp, Except.map] at h2
      | ok r =>
        simp only [Model.testPatternModel, hp, Except.map, Except.ok.injEq] at h2
        have hffm : Model.findFirstModel pat hay =
            .ok ((Model.findFirstIdx r hay.toList 0).map fun (i, j) =>
              Model.mkMatchSpan hay.toList i j) := by
          simp [Model.findFirstModel, hp, Except.map]
        rw [hffm] at hff
        cases h3 : findFirst pat hay with
        | error => rw [h3] at hff; exact False.elim hff
        | ok sp? =>
          rw [h3] at hff
          simp only at hff
          subst hff
          simp [assert, ← h2]

/-- Non-vacuity `CanReach` witness for `test_regex_testPattern_iff_findFirstSome`. -/
theorem reach_regex_testPattern_iff_findFirstSome :
    CanReach (test_regex_testPattern_iff_findFirstSome defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h1 := testPattern_empty_eq "" empty_toList_eq
  have h2 : findFirst "" "" = .ok (some { matched := "", startByte := 0, stopByte := 0 }) := by
    simp [findFirst, Internal.findFirst, parseRegex_empty_eq, Except.map,
      Internal.findFirstIdx, Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.mkMatchSpanFast, Internal.buildByteOffsets, Internal.buildByteOffsets.loop]
  simp [defaultApi, h1, h2, assert]

/-- Proof of `test_regex_countMatches_eq_findAllSize` for `defaultApi`. -/
theorem proof_regex_countMatches_eq_findAllSize :
    AllPass (test_regex_countMatches_eq_findAllSize defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.countMatches, RegExp.findAll, Internal.countMatches]
  cases Internal.findAll pat hay <;> simp [Except.map, assume, assert]

/-- Non-vacuity `CanReach` witness for `test_regex_countMatches_eq_findAllSize`. -/
theorem reach_regex_countMatches_eq_findAllSize :
    CanReach (test_regex_countMatches_eq_findAllSize defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h2i : Internal.findAll "" "" = .ok #[{ matched := "", startByte := 0, stopByte := 0 }] := by
    simp [Internal.findAll, parseRegex_empty_eq, Except.map,
      Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.mkMatchSpanFast, Internal.buildByteOffsets, Internal.buildByteOffsets.loop]
  have h2 : findAll "" "" = .ok #[{ matched := "", startByte := 0, stopByte := 0 }] := h2i
  have h1 : countMatches "" "" = .ok 1 := by
    simp [countMatches, Internal.countMatches, h2i, Except.map]
  simp [defaultApi, h1, h2, assert]

/-- Proof of `test_regex_findAll_spansValid` for `defaultApi`. -/
theorem proof_regex_findAll_spansValid :
    AllPass (test_regex_findAll_spansValid defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.findAll, Internal.findAll]
  cases hp : Internal.parseRegex pat with
  | error e => simp [Except.map, assume]
  | ok ast =>
    simp only [Except.map, assume, assert]
    intro i hi
    let chars := hay.toList.toArray
    have hfa := findAllIdx_eq chars ast
    let idxList := Internal.findAllIdx chars ast
    have hi' : i < idxList.length := by simpa [idxList] using hi
    have hmem : idxList[i] ∈ idxList := List.getElem_mem hi'
    have hbd := hfa.2 idxList[i] hmem
    have hb := buildByteOffsets_spec chars
    have hmono := utf8ByteOffset_mono_le hay.toList hbd.1
    rw [String.ofList_toList] at hmono
    have hsp_eq :
        ((idxList.map fun (a, b) =>
            Internal.mkMatchSpanFast chars (Internal.buildByteOffsets chars) a b).toArray)[i]! =
          Internal.mkMatchSpanFast chars (Internal.buildByteOffsets chars) idxList[i].1 idxList[i].2 := by
      simp [hi']
    rw [hsp_eq]
    unfold Internal.mkMatchSpanFast
    rw [hb.2 idxList[i].1 (Nat.le_trans hbd.1 hbd.2), hb.2 idxList[i].2 hbd.2]
    exact ⟨⟨by simpa [chars] using hmono.1, by simpa [chars] using hmono.2⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_findAll_spansValid`. -/
theorem reach_regex_findAll_spansValid :
    CanReach (test_regex_findAll_spansValid defaultApi) := by
  have hidx : Internal.findAllIdx #[] Internal.RegexAst.empty = [(0, 0)] := by
    simp [Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab]
  refine ⟨"", "", 0, ?_, ?_⟩
  · simp [hidx]
  · simp [hidx, Internal.mkMatchSpanFast, Internal.buildByteOffsets,
      Internal.buildByteOffsets.loop, assert]

/-- Proof of `test_regex_splitBy_nonEmpty` for `defaultApi`. -/
theorem proof_regex_splitBy_nonEmpty :
    AllPass (test_regex_splitBy_nonEmpty defaultApi) := by
  intro pat hay
  simp only [defaultApi, RegExp.splitBy, Internal.splitBy]
  cases hp : Internal.parseRegex pat with
  | error e => simp [Except.map, assume]
  | ok ast =>
    simp only [Except.map, assert]
    refine ⟨?_, trivial⟩
    cases Internal.findAllIdx hay.toList.toArray ast <;> simp [Internal.splitSpansFast]

/-- Non-vacuity `CanReach` witness for `test_regex_splitBy_nonEmpty`. -/
theorem reach_regex_splitBy_nonEmpty :
    CanReach (test_regex_splitBy_nonEmpty defaultApi) := by
  refine ⟨"", "", ?_⟩
  have h1 : splitBy "" "" = .ok #["", ""] := by
    simp [splitBy, Internal.splitBy, parseRegex_empty_eq, Except.map,
      Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.splitSpansFast]
  simp [defaultApi, h1, assert]

/-- Proof of `test_regex_emptyPattern_matchesAnyHaystack` for `defaultApi`. -/
theorem proof_regex_emptyPattern_matchesAnyHaystack :
    AllPass (test_regex_emptyPattern_matchesAnyHaystack defaultApi) := by
  intro hay
  simp only [defaultApi, RegExp.testPattern, Internal.testPattern, parseRegex_empty_eq]
  simp only [Except.map, assert]
  let chars := hay.toList.toArray
  have ht := (evalTable_matches chars .empty).2 0 (Nat.zero_le _)
  unfold Internal.findFirstIdx
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  cases hsz : chars.size with
  | zero =>
    simp only [Internal.findFirstIdxAux]
    rw [ht.1]
    simp [Model.evalAt, toModel]
  | succ m =>
    simp only [Internal.findFirstIdxAux]
    rw [ht.1]
    simp [Model.evalAt, toModel]

/-- Non-vacuity `CanReach` witness for `test_regex_emptyPattern_matchesAnyHaystack`. -/
theorem reach_regex_emptyPattern_matchesAnyHaystack :
    CanReach (test_regex_emptyPattern_matchesAnyHaystack defaultApi) := by
  refine ⟨"abc", ?_⟩
  have habc : "abc".toList = ['a', 'b', 'c'] := by decide
  have h1 : testPattern "" "abc" = .ok true := by
    simp [testPattern, Internal.testPattern, parseRegex_empty_eq, Except.map,
      Internal.findFirstIdx, Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab, habc]
  simp [defaultApi, h1, assert]

/-- Proof of `test_regex_replaceAll_emptyOnEmpty_eqReplacement` for `defaultApi`. -/
theorem proof_regex_replaceAll_emptyOnEmpty_eqReplacement :
    AllPass (test_regex_replaceAll_emptyOnEmpty_eqReplacement defaultApi) := by
  intro rep
  have hr := replaceAll_matchesModel_props "" "" rep
  have hm : Model.replaceAllModel "" "" rep = .ok rep := by
    simp [Model.replaceAllModel, Model.parseRegex, Model.parseRegexChars,
      Except.map, Model.findAllIdx, Model.findAllIdxAux, Model.findFirstIdx,
      Model.findFirstIdxAux, Model.evalAt, Model.replaceSpans]
  rw [hm] at hr
  cases ha : replaceAll "" "" rep with
  | error => rw [ha] at hr; exact False.elim hr
  | ok out =>
    rw [ha] at hr
    simpa [defaultApi, ha, assert] using hr

/-- Non-vacuity `CanReach` witness for `test_regex_replaceAll_emptyOnEmpty_eqReplacement`. -/
theorem reach_regex_replaceAll_emptyOnEmpty_eqReplacement :
    CanReach (test_regex_replaceAll_emptyOnEmpty_eqReplacement defaultApi) := by
  refine ⟨"X", ?_⟩
  have h1 : replaceAll "" "" "X" = .ok "X" := by
    simp [replaceAll, Internal.replaceAll, parseRegex_empty_eq, Except.map,
      Internal.findAllIdx, Internal.findAllIdxAux, Internal.findFirstIdx,
      Internal.findFirstIdxAux, Internal.evalTable, Internal.idTab,
      Internal.replaceSpansFast]
  simp [defaultApi, h1, assert]

/-- Proof of `test_regex_testPattern_matchesModel` for `defaultApi`. -/
theorem proof_regex_testPattern_matchesModel :
    AllPass (test_regex_testPattern_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := testPattern_matchesModel_props pat hay
  cases h1 : testPattern pat hay <;> cases h2 : Model.testPatternModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_findFirst_matchesModel` for `defaultApi`. -/
theorem proof_regex_findFirst_matchesModel :
    AllPass (test_regex_findFirst_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := findFirst_matchesModel_props pat hay
  cases h1 : findFirst pat hay <;> cases h2 : Model.findFirstModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_findAll_matchesModel` for `defaultApi`. -/
theorem proof_regex_findAll_matchesModel :
    AllPass (test_regex_findAll_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := findAll_matchesModel_props pat hay
  cases h1 : findAll pat hay <;> cases h2 : Model.findAllModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_countMatches_matchesModel` for `defaultApi`. -/
theorem proof_regex_countMatches_matchesModel :
    AllPass (test_regex_countMatches_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := countMatches_matchesModel_props pat hay
  cases h1 : countMatches pat hay <;> cases h2 : Model.countMatchesModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_replaceAll_matchesModel` for `defaultApi`. -/
theorem proof_regex_replaceAll_matchesModel :
    AllPass (test_regex_replaceAll_matchesModel defaultApi) := by
  intro pat hay rep
  simp only [defaultApi]
  have hm := replaceAll_matchesModel_props pat hay rep
  cases h1 : replaceAll pat hay rep <;> cases h2 : Model.replaceAllModel pat hay rep <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

/-- Proof of `test_regex_splitBy_matchesModel` for `defaultApi`. -/
theorem proof_regex_splitBy_matchesModel :
    AllPass (test_regex_splitBy_matchesModel defaultApi) := by
  intro pat hay
  simp only [defaultApi]
  have hm := splitBy_matchesModel_props pat hay
  cases h1 : splitBy pat hay <;> cases h2 : Model.splitByModel pat hay <;>
    rw [h1, h2] at hm
  · simp [assert, hm]
  · exact False.elim hm
  · exact False.elim hm
  · simp [assert, hm]

end LeanSwe.RegExp.Proofs
