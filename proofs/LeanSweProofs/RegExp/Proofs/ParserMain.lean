import LeanSwe.RegExp.Interface
import LeanSweProofs.RegExp.Model
import LeanSweProofs.RegExp.Proofs.ParserClass

namespace LeanSwe.RegExp.Proofs

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

/-- `Internal.parseRegex` matches `Model.parseRegex` via `toModel` with non-empty errors. -/
theorem parseRegex_eq (pat : String) :
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


end LeanSwe.RegExp.Proofs
