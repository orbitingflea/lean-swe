import Core.Obeys
import LeanSwe.Glob.Interface
import LeanSweProofs.Glob.Model
import LeanSweProofs.Glob.Proofs.ParserMatch

namespace LeanSwe.Glob.Proofs

open Core

private def NonEmptyErr {α : Type} (r : Except GlobError α) : Prop :=
  ∀ e, r = .error e → e.message ≠ ""

private theorem nonEmptyErr_ok {α : Type} (a : α) : NonEmptyErr (.ok a) := by
  intro _ h; cases h

private theorem nonEmptyErr_pure {α : Type} (a : α) : NonEmptyErr (pure a : Except GlobError α) :=
  nonEmptyErr_ok a

private theorem nonEmptyErr_error {α : Type} {e : GlobError} (he : e.message ≠ "") :
    NonEmptyErr (.error e : Except GlobError α) := by
  intro e' h; simp only [Except.error.injEq] at h; subst h; exact he

private theorem nonEmptyErr_bind {α β : Type} {x : Except GlobError α}
    {f : α → Except GlobError β} (hx : NonEmptyErr x) (hf : ∀ a, NonEmptyErr (f a)) :
    NonEmptyErr (x >>= f) := by
  cases x with
  | error e =>
    intro e' h
    simp only [bind, Except.bind, Except.error.injEq] at h
    subst h
    exact hx e rfl
  | ok a =>
    intro e' h
    exact hf a e' h

private theorem nonEmptyErr_map {α β : Type} {x : Except GlobError α} {f : α → β}
    (hx : NonEmptyErr x) : NonEmptyErr (f <$> x) := by
  cases x with
  | error e =>
    intro e' h
    simp only [Functor.map, Except.map, Except.error.injEq] at h
    subst h
    exact hx e rfl
  | ok _ =>
    intro _ h
    simp [Functor.map, Except.map] at h

private theorem invalidRangeErr_msg_ne_empty (lo hi : Char) :
    (Internal.invalidRangeErr lo hi).message ≠ "" := by
  intro h
  have hlen : (Internal.invalidRangeErr lo hi).message.length = 0 := by rw [h]; rfl
  simp [Internal.invalidRangeErr, String.length_append] at hlen
  have hdash : ("-" : String).length = 0 := by simpa [toString] using hlen.1.1.2
  contradiction

private theorem readClassAtom_nonEmptyErr (cs : List Char) :
    NonEmptyErr (Internal.readClassAtom cs) := by
  unfold Internal.readClassAtom
  split
  · exact nonEmptyErr_error (by decide)
  · exact nonEmptyErr_error (by decide)
  · exact nonEmptyErr_ok _
  · exact nonEmptyErr_ok _

private theorem parseClassItems_nonEmptyErr_aux (n : Nat) :
    ∀ cs acc, cs.length ≤ n → NonEmptyErr (Internal.parseClassItems cs acc) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro cs acc hn
    rw [Internal.parseClassItems.eq_def]
    split
    · exact nonEmptyErr_error (by decide)
    · split
      · exact nonEmptyErr_error (by decide)
      · exact nonEmptyErr_ok _
    · refine nonEmptyErr_bind (readClassAtom_nonEmptyErr _) fun ⟨lo, ⟨afterLo, hLo⟩⟩ => ?_
      have hStep : afterLo.length < n := by
        rw [List.length_cons] at hn hLo
        omega
      dsimp only
      split
      · exact nonEmptyErr_ok _
      · refine nonEmptyErr_bind (readClassAtom_nonEmptyErr _) fun ⟨hi, ⟨afterHi, hHi⟩⟩ => ?_
        have hStep2 : afterHi.length < n :=
          Nat.lt_trans hHi (Nat.lt_trans (Nat.lt_succ_self _) hStep)
        dsimp only
        split
        · refine nonEmptyErr_bind (ih afterHi.length hStep2 afterHi _ (Nat.le_refl _)) ?_
          intro ⟨_, ⟨_, _⟩⟩; exact nonEmptyErr_pure _
        · exact nonEmptyErr_error (invalidRangeErr_msg_ne_empty lo hi)
      · refine nonEmptyErr_bind (ih _ hStep _ _ (Nat.le_refl _)) ?_
        intro ⟨_, ⟨_, _⟩⟩; exact nonEmptyErr_pure _

private theorem parseClassItems_nonEmptyErr (cs : List Char) (acc : List Internal.CharClassItem) :
    NonEmptyErr (Internal.parseClassItems cs acc) :=
  parseClassItems_nonEmptyErr_aux cs.length cs acc (Nat.le_refl _)

private theorem parseCharClass_nonEmptyErr (cs : List Char) :
    NonEmptyErr (Internal.parseCharClass cs) := by
  unfold Internal.parseCharClass
  split
  · exact nonEmptyErr_bind (parseClassItems_nonEmptyErr _ []) fun ⟨items, ⟨r, _⟩⟩ =>
      nonEmptyErr_pure _
  · exact nonEmptyErr_bind (parseClassItems_nonEmptyErr _ []) fun ⟨items, ⟨r, _⟩⟩ =>
      nonEmptyErr_pure _

private theorem parseAtoms_nonEmptyErr (cs : List Char) :
    NonEmptyErr (Internal.parseAtoms cs) := by
  rw [Internal.parseAtoms.eq_def]
  split
  · exact nonEmptyErr_ok _
  · exact nonEmptyErr_error (by decide)
  · exact nonEmptyErr_bind (parseAtoms_nonEmptyErr _) fun _ => nonEmptyErr_pure _
  · exact nonEmptyErr_bind (parseAtoms_nonEmptyErr _) fun t => by
      cases t with
      | nil => exact nonEmptyErr_pure _
      | cons hd _ => cases hd <;> exact nonEmptyErr_pure _
  · exact nonEmptyErr_bind (parseAtoms_nonEmptyErr _) fun _ => nonEmptyErr_pure _
  · refine nonEmptyErr_bind (parseCharClass_nonEmptyErr _) fun ⟨_, ⟨after, _⟩⟩ => ?_
    exact nonEmptyErr_bind (parseAtoms_nonEmptyErr after) fun _ => nonEmptyErr_pure _
  · exact nonEmptyErr_bind (parseAtoms_nonEmptyErr _) fun _ => nonEmptyErr_pure _
termination_by cs.length
decreasing_by all_goals (simp only [*, List.length_cons] at *; omega)

private theorem parseSegment_nonEmptyErr (seg : List Char) :
    NonEmptyErr (Internal.parseSegment seg) := by
  unfold Internal.parseSegment
  split
  · exact nonEmptyErr_ok _
  · exact nonEmptyErr_map (parseAtoms_nonEmptyErr seg)

private theorem parseSegList_nonEmptyErr (segs : List (List Char)) :
    NonEmptyErr (Internal.parseSegList segs) := by
  induction segs with
  | nil => exact nonEmptyErr_ok _
  | cons seg rest ih =>
    unfold Internal.parseSegList
    refine nonEmptyErr_bind (parseSegment_nonEmptyErr seg) fun p => ?_
    refine nonEmptyErr_bind ih fun ps => ?_
    cases p with
    | atoms _ => exact nonEmptyErr_pure _
    | globStar =>
      cases ps with
      | nil => exact nonEmptyErr_pure _
      | cons hd _ => cases hd <;> exact nonEmptyErr_pure _

/-- `Internal.compilePattern` always emits a non-empty diagnostic message on error. -/
theorem compilePattern_err_ne_empty {pat : String} {err : GlobError}
    (h : Internal.compilePattern pat = .error err) : err.message ≠ "" :=
  parseSegList_nonEmptyErr _ err h

private theorem model_parseAtoms_lbracket (rest : List Char) :
    Model.parseAtoms ('[' :: rest) = modelParseClass rest := by
  cases rest with
  | nil => rfl
  | cons d tail =>
    by_cases hdBang : d = '!'
    · subst hdBang; rfl
    · unfold modelParseClass
      rw [Model.parseAtoms.eq_def]
      split
      · rename_i heq; cases heq
      · rename_i heq; cases heq
      · rename_i heq; cases heq
      · rename_i heq; cases heq
      · rename_i heq; cases heq
      · rename_i heq; injection heq with _ h2; injection h2 with h3; exact absurd h3 hdBang
      · rename_i heq
        injection heq with _ hr
        subst hr
        split
        · rename_i h; injection h with hd; exact absurd hd hdBang
        · rfl
      · rename_i hNot heq
        injection heq with hc hr
        subst hc hr
        exact absurd rfl hNot

private theorem internal_parseAtoms_lbracket (rest : List Char) :
    Internal.parseAtoms ('[' :: rest) =
      (do
        let (cc, ⟨after, _⟩) ← Internal.parseCharClass rest
        let tail ← Internal.parseAtoms after
        pure (Internal.SegAtom.charClass cc :: tail)) := by
  rw [Internal.parseAtoms.eq_def]; rfl

private theorem internal_parseAtoms_lit (c : Char) (rest : List Char)
    (hBs : c ≠ '\\') (hStar : c ≠ '*') (hQ : c ≠ '?') (hLbr : c ≠ '[') :
    Internal.parseAtoms (c :: rest) = (Internal.parseAtoms rest).map (.lit c :: ·) := by
  rw [Internal.parseAtoms.eq_def]
  split <;> rename_i heq <;> first
    | (cases heq; done)
    | (injection heq with hc; first
        | exact absurd hc hBs
        | exact absurd hc hStar
        | exact absurd hc hQ
        | exact absurd hc hLbr)
    | (injection heq with hc hr; subst hc hr
       simp only [bind, Except.bind, pure, Except.pure, Except.map])

private theorem model_parseAtoms_lit (c : Char) (rest : List Char)
    (hBs : c ≠ '\\') (hStar : c ≠ '*') (hQ : c ≠ '?') (hLbr : c ≠ '[') :
    Model.parseAtoms (c :: rest) = (Model.parseAtoms rest).map (.lit c :: ·) := by
  rw [Model.parseAtoms.eq_def]
  split <;> rename_i heq <;> first
    | (cases heq; done)
    | (injection heq with hc; first
        | exact absurd hc hBs
        | exact absurd hc hStar
        | exact absurd hc hQ
        | exact absurd hc hLbr)
    | (injection heq with hc hr; subst hc hr; rfl)

private def AtomsMatch (cs : List Char) : Prop :=
  match Internal.parseAtoms cs, Model.parseAtoms cs with
  | .error e, .error k => e.kind = k
  | .ok a1, .ok a2 => ∀ s, Internal.matchSegAtoms a1 s = Model.evalSeg a2 s
  | _, _ => False

private theorem parseAtoms_match_aux (n : Nat) :
    ∀ cs : List Char, cs.length ≤ n → AtomsMatch cs := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro cs hLen
    unfold AtomsMatch
    rw [Internal.parseAtoms.eq_def]
    cases cs with
    | nil =>
      simp only [Model.parseAtoms]
      intro s
      cases s <;> simp [Internal.matchSegAtoms, Model.evalSeg]
    | cons c rest =>
      by_cases hcBs : c = '\\'
      · subst hcBs
        cases rest with
        | nil => simp [Internal.trailingEscapeErr, Model.parseAtoms]
        | cons d tail =>
          have hSub : tail.length < n := by rw [List.length_cons, List.length_cons] at hLen; omega
          have hRec := ih tail.length hSub tail (Nat.le_refl _)
          unfold AtomsMatch at hRec
          simp only [Model.parseAtoms, bind, Except.bind, pure, Except.pure, Except.map] at hRec ⊢
          cases h1 : Internal.parseAtoms tail with
          | error e1 =>
            cases h2 : Model.parseAtoms tail with
            | error k2 => simp only [h1, h2] at hRec ⊢; exact hRec
            | ok a2 => simp only [h1, h2] at hRec
          | ok a1 =>
            cases h2 : Model.parseAtoms tail with
            | error k2 => simp only [h1, h2] at hRec
            | ok a2 =>
              simp only [h1, h2] at hRec ⊢
              intro s
              cases s with
              | nil => simp [Internal.matchSegAtoms, Model.evalSeg]
              | cons ch cs' =>
                simp [Internal.matchSegAtoms, Model.evalSeg, hRec cs']
      · by_cases hcStar : c = '*'
        · subst hcStar
          have hSub : rest.length < n := by rw [List.length_cons] at hLen; omega
          have hRec := ih rest.length hSub rest (Nat.le_refl _)
          unfold AtomsMatch at hRec
          simp only [Model.parseAtoms, bind, Except.bind, pure, Except.pure, Except.map] at hRec ⊢
          cases h1 : Internal.parseAtoms rest with
          | error e1 =>
            cases h2 : Model.parseAtoms rest with
            | error k2 => simp only [h1, h2] at hRec ⊢; exact hRec
            | ok a2 => simp only [h1, h2] at hRec
          | ok a1 =>
            cases h2 : Model.parseAtoms rest with
            | error k2 => simp only [h1, h2] at hRec
            | ok a2 =>
              simp only [h1, h2] at hRec ⊢
              cases a1 with
              | nil =>
                intro s
                rw [matchSegAtoms_eq_evalSeg]
                simp only [List.map_cons, toModelAtom]
                exact evalSeg_star_congr (fun s' => by rw [← matchSegAtoms_eq_evalSeg]; exact hRec s') s
              | cons hd tl =>
                cases hd with
                | star =>
                  intro s
                  have hCongr := @evalSeg_star_congr ((Internal.SegAtom.star :: tl).map toModelAtom) a2
                    (fun s' => (matchSegAtoms_eq_evalSeg _ s').symm.trans (hRec s')) s
                  simp only [List.map_cons, toModelAtom] at hCongr
                  rw [evalSeg_star_star] at hCongr
                  exact (matchSegAtoms_eq_evalSeg _ s).trans hCongr
                | _ =>
                  intro s
                  rw [matchSegAtoms_eq_evalSeg]
                  simp only [List.map_cons, toModelAtom]
                  exact evalSeg_star_congr (fun s' =>
                    (matchSegAtoms_eq_evalSeg _ s').symm.trans (hRec s')) s
        · by_cases hcQ : c = '?'
          · subst hcQ
            have hSub : rest.length < n := by rw [List.length_cons] at hLen; omega
            have hRec := ih rest.length hSub rest (Nat.le_refl _)
            unfold AtomsMatch at hRec
            simp only [Model.parseAtoms, bind, Except.bind, pure, Except.pure, Except.map] at hRec ⊢
            cases h1 : Internal.parseAtoms rest with
            | error e1 =>
              cases h2 : Model.parseAtoms rest with
              | error k2 => simp only [h1, h2] at hRec ⊢; exact hRec
              | ok a2 => simp only [h1, h2] at hRec
            | ok a1 =>
              cases h2 : Model.parseAtoms rest with
              | error k2 => simp only [h1, h2] at hRec
              | ok a2 =>
                simp only [h1, h2] at hRec ⊢
                intro s
                cases s with
                | nil => simp [Internal.matchSegAtoms, Model.evalSeg]
                | cons ch cs' => simp [Internal.matchSegAtoms, Model.evalSeg, hRec cs']
          · by_cases hcLbr : c = '['
            · subst hcLbr
              have hCC := parseCharClass_match rest
              unfold CharClassMatch at hCC
              rw [← Internal.parseAtoms.eq_def, internal_parseAtoms_lbracket,
                model_parseAtoms_lbracket]
              cases hRes : Internal.parseCharClass rest with
              | error e =>
                rw [hRes] at hCC
                dsimp only at hCC ⊢
                simp only [bind, Except.bind]
                rw [hCC]
              | ok q =>
                rcases q with ⟨cc, ⟨after, hAfter⟩⟩
                rw [hRes] at hCC
                dsimp only at hCC ⊢
                have hLenAfter : after.length < n := by
                  rw [List.length_cons] at hLen
                  omega
                have hRec := ih after.length hLenAfter after (Nat.le_refl _)
                unfold AtomsMatch at hRec
                rw [hCC]
                simp only [bind, Except.bind, pure, Except.pure, Except.map]
                cases h1 : Internal.parseAtoms after with
                | error e1 =>
                  cases h2 : Model.parseAtoms after with
                  | error k2 => rw [h1, h2] at hRec; exact hRec
                  | ok a2 => rw [h1, h2] at hRec; try exact False.elim hRec
                | ok a1 =>
                  cases h2 : Model.parseAtoms after with
                  | error k2 => rw [h1, h2] at hRec; try exact False.elim hRec
                  | ok a2 =>
                    rw [h1, h2] at hRec
                    intro s
                    cases s with
                    | nil => simp [Internal.matchSegAtoms, Model.evalSeg]
                    | cons ch cs' =>
                      simp [Internal.matchSegAtoms, Model.evalSeg, matchCharClass_eq_model, hRec cs']
            · have hSub : rest.length < n := by rw [List.length_cons] at hLen; omega
              have hRec := ih rest.length hSub rest (Nat.le_refl _)
              unfold AtomsMatch at hRec
              rw [← Internal.parseAtoms.eq_def, internal_parseAtoms_lit c rest hcBs hcStar hcQ hcLbr,
                model_parseAtoms_lit c rest hcBs hcStar hcQ hcLbr]
              simp only [Except.map]
              cases h1 : Internal.parseAtoms rest with
              | error e1 =>
                cases h2 : Model.parseAtoms rest with
                | error k2 => rw [h1, h2] at hRec; exact hRec
                | ok a2 => rw [h1, h2] at hRec; try exact False.elim hRec
              | ok a1 =>
                cases h2 : Model.parseAtoms rest with
                | error k2 => rw [h1, h2] at hRec; try exact False.elim hRec
                | ok a2 =>
                  rw [h1, h2] at hRec
                  intro s
                  cases s with
                  | nil => simp [Internal.matchSegAtoms, Model.evalSeg]
                  | cons ch cs' => simp [Internal.matchSegAtoms, Model.evalSeg, hRec cs']

private theorem parseAtoms_match (cs : List Char) : AtomsMatch cs :=
  parseAtoms_match_aux cs.length cs (Nat.le_refl _)

private def SegMatch (seg : List Char) : Prop :=
  match Internal.parseSegment seg, Model.parseSegment seg with
  | .error e, .error k => e.kind = k
  | .ok .globStar, .ok .globStar => True
  | .ok (.atoms a1), .ok (.atoms a2) => ∀ s, Internal.matchSegAtoms a1 s = Model.evalSeg a2 s
  | _, _ => False

private theorem parseSegment_match (seg : List Char) : SegMatch seg := by
  unfold SegMatch Internal.parseSegment Model.parseSegment
  by_cases hGS : (seg == ['*', '*']) = true
  · simp [hGS]
  · simp only [hGS, Bool.false_eq_true, ↓reduceIte, Except.map]
    have h := parseAtoms_match seg
    unfold AtomsMatch at h
    cases h1 : Internal.parseAtoms seg with
    | error e1 =>
      cases h2 : Model.parseAtoms seg with
      | error k2 => rw [h1, h2] at h; exact h
      | ok a2 => rw [h1, h2] at h; exact False.elim h
    | ok a1 =>
      cases h2 : Model.parseAtoms seg with
      | error k2 => rw [h1, h2] at h; exact False.elim h
      | ok a2 => rw [h1, h2] at h; exact h

private def SegListMatch (segs : List (List Char)) : Prop :=
  match Internal.parseSegList segs, Model.parseSegments segs with
  | .error e, .error k => e.kind = k
  | .ok ps1, .ok ps2 => ∀ ss, Internal.matchSegPats ps1 ss = Model.evalPath ps2 ss
  | _, _ => False

private theorem parseSegList_match (segs : List (List Char)) : SegListMatch segs := by
  induction segs with
  | nil =>
    unfold SegListMatch
    intro ss
    cases ss <;> simp [Internal.matchSegPats, Model.evalPath]
  | cons seg rest ih =>
    unfold SegListMatch at ih ⊢
    simp only [Internal.parseSegList, Model.parseSegments, bind, Except.bind, pure, Except.pure]
    have hSeg := parseSegment_match seg
    unfold SegMatch at hSeg
    cases hp1 : Internal.parseSegment seg with
    | error e1 =>
      cases hp2 : Model.parseSegment seg with
      | error k2 => rw [hp1, hp2] at hSeg; exact hSeg
      | ok p2 => rw [hp1, hp2] at hSeg; try exact False.elim hSeg
    | ok p1 =>
      cases hp2 : Model.parseSegment seg with
      | error k2 =>
        rw [hp1, hp2] at hSeg
        cases p1 <;> exact False.elim hSeg
      | ok p2 =>
        rw [hp1, hp2] at hSeg
        cases hps1 : Internal.parseSegList rest with
        | error e1 =>
          cases hps2 : Model.parseSegments rest with
          | error k2 => rw [hps1, hps2] at ih; exact ih
          | ok ps2 => rw [hps1, hps2] at ih; exact False.elim ih
        | ok ps1 =>
          cases hps2 : Model.parseSegments rest with
          | error k2 => rw [hps1, hps2] at ih; exact False.elim ih
          | ok ps2 =>
            rw [hps1, hps2] at ih
            dsimp only at ih
            cases p1 with
            | globStar =>
              cases p2 with
              | atoms _ => exact False.elim hSeg
              | globStar =>
                cases ps1 with
                | nil =>
                  intro ss
                  rw [matchSegPats_eq_evalPath]
                  simp only [List.map_cons, toModelSeg]
                  exact evalPath_globStar_congr (fun ss' => by
                    rw [← matchSegPats_eq_evalPath]; exact ih ss') ss
                | cons hd tl =>
                  cases hd with
                  | globStar =>
                    intro ss
                    have hCongr := @evalPath_globStar_congr ((Internal.SegmentPat.globStar :: tl).map toModelSeg) ps2
                      (fun ss' => (matchSegPats_eq_evalPath _ ss').symm.trans (ih ss')) ss
                    simp only [List.map_cons, toModelSeg] at hCongr
                    rw [evalPath_globStar_globStar] at hCongr
                    exact (matchSegPats_eq_evalPath _ ss).trans hCongr
                  | atoms _ =>
                    intro ss
                    rw [matchSegPats_eq_evalPath]
                    simp only [List.map_cons, toModelSeg]
                    exact evalPath_globStar_congr (fun ss' =>
                      (matchSegPats_eq_evalPath _ ss').symm.trans (ih ss')) ss
            | atoms a1 =>
              cases p2 with
              | globStar => exact False.elim hSeg
              | atoms a2 =>
                intro ss
                cases ss with
                | nil => simp [Internal.matchSegPats, Model.evalPath]
                | cons s ss' =>
                  simp only [Internal.matchSegPats, Model.evalPath]
                  rw [hSeg s, ih ss']

private theorem compilePattern_match (pat : String) :
    match Internal.compilePattern pat, Model.parsePattern pat with
    | .error e, .error k => e.kind = k
    | .ok ps1, .ok ps2 => ∀ ss, Internal.matchSegPats ps1 ss = Model.evalPath ps2 ss
    | _, _ => False := by
  simp only [Internal.compilePattern, Model.parsePattern, splitOnChar_slash_eq_splitSlash]
  exact parseSegList_match (Model.splitSlash pat.toList)

/-- Full public `Interface` obedience of `LeanSwe.Glob` against `LeanSwe.Glob.Model`. -/
theorem obeys_model :
    Core.ObeysPure LeanSwe.Glob.validate Model.allowedValidate ∧
    Core.ObeysPure2 LeanSwe.Glob.isMatch Model.allowedIsMatch ∧
    Core.ObeysPure2 LeanSwe.Glob.filter Model.allowedFilter ∧
    Core.ObeysPure2 LeanSwe.Glob.countMatches Model.allowedCountMatches ∧
    Core.ObeysPureEq LeanSwe.Glob.escape Model.escapeModel := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pat
    have h := compilePattern_match pat
    simp only [Model.allowedValidate, validate, Internal.validate, Model.validateModel,
      bind, Except.bind, pure, Except.pure, Except.map]
    cases hc : Internal.compilePattern pat with
    | error e =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact ⟨h, compilePattern_err_ne_empty hc⟩
      | ok ps2 => rw [hc, hm] at h; exact False.elim h
    | ok ps1 =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact False.elim h
      | ok ps2 => trivial
  · intro pat path
    have h := compilePattern_match pat
    simp only [Model.allowedIsMatch, isMatch, Internal.isMatch, Model.isMatchModel,
      splitOnChar_slash_eq_splitSlash, bind, Except.bind, pure, Except.pure, Except.map]
    cases hc : Internal.compilePattern pat with
    | error e =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact ⟨h, compilePattern_err_ne_empty hc⟩
      | ok ps2 => rw [hc, hm] at h; exact False.elim h
    | ok ps1 =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact False.elim h
      | ok ps2 => rw [hc, hm] at h; exact h (Model.splitSlash path.toList)
  · intro pat paths
    have h := compilePattern_match pat
    simp only [Model.allowedFilter, filter, Internal.filter, Internal.filterCompiled, Model.filterModel,
      splitOnChar_slash_eq_splitSlash, bind, Except.bind, pure, Except.pure, Except.map]
    cases hc : Internal.compilePattern pat with
    | error e =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact ⟨h, compilePattern_err_ne_empty hc⟩
      | ok ps2 => rw [hc, hm] at h; exact False.elim h
    | ok ps1 =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact False.elim h
      | ok ps2 =>
        rw [hc, hm] at h
        congr 1
        funext p
        exact h (Model.splitSlash p.toList)
  · intro pat paths
    have h := compilePattern_match pat
    simp only [Model.allowedCountMatches, countMatches, Internal.countMatches, Internal.filter,
      Internal.filterCompiled, Model.countMatchesModel, Model.filterModel,
      splitOnChar_slash_eq_splitSlash, bind, Except.bind, pure, Except.pure, Except.map]
    cases hc : Internal.compilePattern pat with
    | error e =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact ⟨h, compilePattern_err_ne_empty hc⟩
      | ok ps2 => rw [hc, hm] at h; exact False.elim h
    | ok ps1 =>
      cases hm : Model.parsePattern pat with
      | error k => rw [hc, hm] at h; exact False.elim h
      | ok ps2 =>
        rw [hc, hm] at h
        apply congrArg Array.size
        congr 1
        funext p
        exact h (Model.splitSlash p.toList)
  · intro literal
    simp [escape, Internal.escape, Model.escapeModel, escapeChars_eq_model]

end LeanSwe.Glob.Proofs
