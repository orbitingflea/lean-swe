import LeanSwe.Glob.Interface
import LeanSweProofs.Glob.Model

namespace LeanSwe.Glob.Proofs

/-- Map an `Internal.CharClassItem` to `Model.ClassItem`. -/
def toModelItem : Internal.CharClassItem → Model.ClassItem
  | .single c => .single c
  | .range lo hi => .range lo hi

/-- Map an `Internal.CharClass` to `Model.CharClass`. -/
def toModelClass (cc : Internal.CharClass) : Model.CharClass :=
  { negated := cc.negated, items := cc.items.map toModelItem }

/-- Map an `Internal.SegAtom` to `Model.Atom`. -/
def toModelAtom : Internal.SegAtom → Model.Atom
  | .lit c => .lit c
  | .anyChar => .any
  | .star => .star
  | .charClass cc => .charClass (toModelClass cc)

/-- Map an `Internal.SegmentPat` to `Model.Segment`. -/
def toModelSeg : Internal.SegmentPat → Model.Segment
  | .globStar => .globStar
  | .atoms xs => .atoms (xs.map toModelAtom)

/-- `Internal.splitOnChar '/'` equals `Model.splitSlash`. -/
theorem splitOnChar_slash_eq_splitSlash (cs : List Char) :
    Internal.splitOnChar '/' cs = Model.splitSlash cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [Internal.splitOnChar, Model.splitSlash, ih]
    split <;> rfl

/-- `Internal.escapeChars` equals `Model.escapeCharsModel`. -/
theorem escapeChars_eq_model (cs : List Char) :
    Internal.escapeChars cs = Model.escapeCharsModel cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [Internal.escapeChars, Model.escapeCharsModel, ih]

private theorem matchClassItems_eq_any (c : Char) (items : List Internal.CharClassItem) :
    Internal.matchClassItems c items = (items.map toModelItem).any (Model.classItemMatches c) := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    cases it <;> simp [Internal.matchClassItems, Model.classItemMatches, toModelItem, ih]

/-- `Internal.matchCharClass` agrees with `Model.charClassMatches` via `toModelClass`. -/
theorem matchCharClass_eq_model (cc : Internal.CharClass) (c : Char) :
    Internal.matchCharClass cc c = Model.charClassMatches (toModelClass cc) c := by
  simp [Internal.matchCharClass, Model.charClassMatches, toModelClass, matchClassItems_eq_any]

private theorem matchSegAtoms_star_eq (atoms : List Internal.SegAtom) (cs : List Char)
    (ih : ∀ cs', Internal.matchSegAtoms atoms cs' = Model.evalSeg (atoms.map toModelAtom) cs') :
    Internal.matchSegAtoms (.star :: atoms) cs =
      Model.evalSeg (.star :: atoms.map toModelAtom) cs := by
  induction cs with
  | nil =>
    simp only [Internal.matchSegAtoms, Model.evalSeg, Model.evalSegStar]
    exact ih []
  | cons c rest ihCs =>
    simp only [Internal.matchSegAtoms, Model.evalSeg, Model.evalSegStar] at ihCs ⊢
    rw [ih (c :: rest), ihCs]

/-- `Internal.matchSegAtoms` agrees with `Model.evalSeg` via `toModelAtom`. -/
theorem matchSegAtoms_eq_evalSeg (atoms : List Internal.SegAtom) (cs : List Char) :
    Internal.matchSegAtoms atoms cs = Model.evalSeg (atoms.map toModelAtom) cs := by
  induction atoms generalizing cs with
  | nil =>
    cases cs <;> simp [Internal.matchSegAtoms, Model.evalSeg]
  | cons a rest ih =>
    cases a with
    | lit p =>
      cases cs with
      | nil => simp [Internal.matchSegAtoms, Model.evalSeg, toModelAtom]
      | cons c tl => simp [Internal.matchSegAtoms, Model.evalSeg, toModelAtom, ih tl]
    | anyChar =>
      cases cs with
      | nil => simp [Internal.matchSegAtoms, Model.evalSeg, toModelAtom]
      | cons c tl => simp [Internal.matchSegAtoms, Model.evalSeg, toModelAtom, ih tl]
    | charClass cc =>
      cases cs with
      | nil => simp [Internal.matchSegAtoms, Model.evalSeg, toModelAtom]
      | cons c tl =>
        simp [Internal.matchSegAtoms, Model.evalSeg, toModelAtom, matchCharClass_eq_model, ih tl]
    | star =>
      exact matchSegAtoms_star_eq rest cs ih

private theorem evalSegStar_congr {f g : List Char → Bool} (hfg : ∀ cs, f cs = g cs) (cs : List Char) :
    Model.evalSegStar f cs = Model.evalSegStar g cs := by
  induction cs with
  | nil => exact hfg []
  | cons c rest ih => simp [Model.evalSegStar, hfg (c :: rest), ih]

/-- Congruence of `Model.evalSeg` under a leading `.star` wildcard. -/
theorem evalSeg_star_congr {a1 a2 : List Model.Atom}
    (ha : ∀ cs, Model.evalSeg a1 cs = Model.evalSeg a2 cs) (cs : List Char) :
    Model.evalSeg (.star :: a1) cs = Model.evalSeg (.star :: a2) cs := by
  simp only [Model.evalSeg]
  exact evalSegStar_congr ha cs

/-- Adjacent `.star` wildcards collapse under `Model.evalSeg`. -/
theorem evalSeg_star_star (xs : List Model.Atom) (cs : List Char) :
    Model.evalSeg (.star :: .star :: xs) cs = Model.evalSeg (.star :: xs) cs := by
  apply Bool.eq_iff_iff.mpr
  simp only [Model.evalSeg_eq_true_iff]
  constructor
  · intro h
    cases h with
    | star pre1 suf1 hs1 =>
      cases hs1 with
      | star pre2 suf2 hs2 =>
        simpa [List.append_assoc] using Model.MatchSeg.star (pre1 ++ pre2) suf2 hs2
  · intro h
    cases h with
    | star pre suf hs =>
      exact Model.MatchSeg.star [] (pre ++ suf) (Model.MatchSeg.star pre suf hs)

private theorem matchSegPats_globStar_eq (pats : List Internal.SegmentPat) (segs : List (List Char))
    (ih : ∀ segs', Internal.matchSegPats pats segs' = Model.evalPath (pats.map toModelSeg) segs') :
    Internal.matchSegPats (.globStar :: pats) segs =
      Model.evalPath (.globStar :: pats.map toModelSeg) segs := by
  induction segs with
  | nil =>
    simp only [Internal.matchSegPats, Model.evalPath, Model.evalPathGlobStar]
    exact ih []
  | cons s rest ihS =>
    simp only [Internal.matchSegPats, Model.evalPath, Model.evalPathGlobStar] at ihS ⊢
    rw [ih (s :: rest), ihS]

/-- `Internal.matchSegPats` agrees with `Model.evalPath` via `toModelSeg`. -/
theorem matchSegPats_eq_evalPath (pats : List Internal.SegmentPat) (segs : List (List Char)) :
    Internal.matchSegPats pats segs = Model.evalPath (pats.map toModelSeg) segs := by
  induction pats generalizing segs with
  | nil =>
    cases segs <;> simp [Internal.matchSegPats, Model.evalPath]
  | cons p rest ih =>
    cases p with
    | atoms a =>
      cases segs with
      | nil => simp [Internal.matchSegPats, Model.evalPath, toModelSeg]
      | cons s ss =>
        simp [Internal.matchSegPats, Model.evalPath, toModelSeg, matchSegAtoms_eq_evalSeg, ih ss]
    | globStar =>
      exact matchSegPats_globStar_eq rest segs ih

private theorem evalPathGlobStar_congr {f g : List (List Char) → Bool}
    (hfg : ∀ segs, f segs = g segs) (segs : List (List Char)) :
    Model.evalPathGlobStar f segs = Model.evalPathGlobStar g segs := by
  induction segs with
  | nil => exact hfg []
  | cons s rest ih => simp [Model.evalPathGlobStar, hfg (s :: rest), ih]

/-- Congruence of `Model.evalPath` under a leading `.globStar` segment. -/
theorem evalPath_globStar_congr {p1 p2 : List Model.Segment}
    (hp : ∀ segs, Model.evalPath p1 segs = Model.evalPath p2 segs) (segs : List (List Char)) :
    Model.evalPath (.globStar :: p1) segs = Model.evalPath (.globStar :: p2) segs := by
  simp only [Model.evalPath]
  exact evalPathGlobStar_congr hp segs

/-- Adjacent `.globStar` segments collapse under `Model.evalPath`. -/
theorem evalPath_globStar_globStar (xs : List Model.Segment) (segs : List (List Char)) :
    Model.evalPath (.globStar :: .globStar :: xs) segs = Model.evalPath (.globStar :: xs) segs := by
  apply Bool.eq_iff_iff.mpr
  simp only [Model.evalPath_eq_true_iff]
  constructor
  · intro h
    cases h with
    | globStar pre1 suf1 hs1 =>
      cases hs1 with
      | globStar pre2 suf2 hs2 =>
        simpa [List.append_assoc] using Model.MatchPath.globStar (pre1 ++ pre2) suf2 hs2
  · intro h
    cases h with
    | globStar pre suf hs =>
      exact Model.MatchPath.globStar [] (pre ++ suf) (Model.MatchPath.globStar pre suf hs)

private theorem model_parseClassAfter_nonDash (neg : Bool) (acc : List Model.ClassItem)
    (lo : Char) (cs : List Char) (hNotDash : ∀ tl, cs ≠ '-' :: tl) :
    Model.parseClassAfter neg acc lo cs = Model.parseClass neg (.single lo :: acc) cs := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    by_cases hcDash : c = '-'
    · exact absurd (hcDash ▸ rfl) (hNotDash rest)
    · by_cases hcRbr : c = ']'
      · subst hcRbr
        rfl
      · by_cases hcBs : c = '\\'
        · subst hcBs
          cases rest with
          | nil => rfl
          | cons lo2 tail => rfl
        · unfold Model.parseClassAfter Model.parseClass
          simp [hcBs]

private def ClassItemsMatch (neg : Bool) (acc : List Internal.CharClassItem)
    (cs : List Char) : Prop :=
  match Internal.parseClassItems cs acc with
  | .error e => Model.parseClass neg (acc.map toModelItem) cs = .error e.kind
  | .ok (items, ⟨r, _⟩) =>
    Model.parseClass neg (acc.map toModelItem) cs =
      (Model.parseAtoms r).map
        (Model.Atom.charClass { negated := neg, items := items.map toModelItem } :: ·)

private theorem parseClassItems_match_aux (n : Nat) :
    ∀ (cs : List Char), cs.length ≤ n → ∀ neg acc, ClassItemsMatch neg acc cs := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro cs hLen neg acc
    unfold ClassItemsMatch
    rw [Internal.parseClassItems.eq_def]
    cases cs with
    | nil =>
      simp [Internal.classUnclosedErr, Model.parseClass]
    | cons c rest =>
      by_cases hcRbr : c = ']'
      · subst hcRbr
        by_cases hEmpty : acc.isEmpty = true
        · simp [hEmpty, Internal.classEmptyErr, Model.parseClass]
        · have hEmpty' : acc.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
          have hAccNonEmpty : (acc.map toModelItem).isEmpty = false := by
            cases acc with
            | nil => simp at hEmpty
            | cons _ _ => rfl
          have hMapRev : (acc.map toModelItem).reverse = acc.reverse.map toModelItem :=
            (List.map_reverse (f := toModelItem) (l := acc)).symm
          simp only [hEmpty', hAccNonEmpty, Bool.false_eq_true, ↓reduceIte, Model.parseClass, hMapRev]
      · have hParseStep :
            Model.parseClass neg (acc.map toModelItem) (c :: rest) =
              match Internal.readClassAtom (c :: rest) with
              | .error e => .error e.kind
              | .ok (lo, ⟨afterLo, _⟩) => Model.parseClassAfter neg (acc.map toModelItem) lo afterLo := by
          by_cases hcBs : c = '\\'
          · subst hcBs
            cases rest with
            | nil => simp [Internal.readClassAtom, Internal.trailingEscapeErr, Model.parseClass]
            | cons lo tail => simp [Internal.readClassAtom, Model.parseClass]
          · unfold Internal.readClassAtom Model.parseClass
            simp [hcBs]
        cases hAtom : Internal.readClassAtom (c :: rest) with
        | error e =>
          simp only [bind, Except.bind, hAtom] at hParseStep ⊢
          exact hParseStep
        | ok p =>
          rcases p with ⟨lo, ⟨afterLo, hLo⟩⟩
          simp only [bind, Except.bind, hAtom] at hParseStep ⊢
          clear hAtom
          revert hLo hParseStep
          cases hAfter : afterLo with
          | nil =>
            intro hLo hParseStep
            rw [hParseStep]
            have hND : ∀ tl, ([] : List Char) ≠ '-' :: tl := by intro _ h; cases h
            rw [model_parseClassAfter_nonDash neg (acc.map toModelItem) lo [] hND]
            have hRec := ih 0 (by rw [List.length_cons] at hLen hLo; omega) [] (Nat.le_refl 0) neg (.single lo :: acc)
            unfold ClassItemsMatch at hRec
            simp only [pure, Except.pure, List.map_cons, toModelItem] at hRec ⊢
            cases hRes : Internal.parseClassItems [] (.single lo :: acc) with
            | error e => rw [hRes] at hRec; exact hRec
            | ok q => rw [hRes] at hRec; exact hRec
          | cons d afterRest =>
            intro hLo hParseStep
            have hStep : (d :: afterRest).length < n := by
              simp only [List.length_cons] at hLen hLo ⊢
              omega
            by_cases hdDash : d = '-'
            · subst hdDash
              cases afterRest with
              | nil =>
                rw [hParseStep]
                simp [Internal.readClassAtom, Internal.classUnclosedErr,
                  Model.parseClassAfter, Model.parseClassRange]
              | cons e afterRest2 =>
                by_cases heRbr : e = ']'
                · subst heRbr
                  rw [hParseStep]
                  have hItems :
                      (Model.ClassItem.single '-' :: Model.ClassItem.single lo :: acc.map toModelItem).reverse =
                        (Internal.CharClassItem.single '-' :: Internal.CharClassItem.single lo :: acc).reverse.map
                          toModelItem := by
                    simp [List.map_reverse, toModelItem]
                  simp only [Model.parseClassAfter, Model.parseClassRange, hItems]
                · have hRangeStep :
                      Model.parseClassAfter neg (acc.map toModelItem) lo ('-' :: e :: afterRest2) =
                        match Internal.readClassAtom (e :: afterRest2) with
                        | .error err => .error err.kind
                        | .ok (hi, ⟨afterHi, _⟩) =>
                          if lo ≤ hi then
                            Model.parseClass neg (.range lo hi :: acc.map toModelItem) afterHi
                          else
                            .error .invalidRange := by
                    by_cases heBs : e = '\\'
                    · subst heBs
                      cases afterRest2 with
                      | nil =>
                        simp [Internal.readClassAtom, Internal.trailingEscapeErr,
                          Model.parseClassAfter, Model.parseClassRange]
                      | cons hi tail =>
                        simp [Internal.readClassAtom, Model.parseClassAfter, Model.parseClassRange]
                    · unfold Internal.readClassAtom Model.parseClassAfter Model.parseClassRange
                      simp [heBs]
                  rw [hParseStep, hRangeStep]
                  split
                  · rename_i _ errRes heq
                    split at heq
                    · rename_i heq1
                      injection heq1 with _ h2
                      injection h2 with he
                      exact absurd he heRbr
                    · rename_i rest2 _ heqRest
                      injection heqRest with _ hRestEq
                      subst hRestEq
                      cases hHiAtom : Internal.readClassAtom (e :: afterRest2) with
                      | error err =>
                        rw [hHiAtom] at heq
                        injection heq with hErr
                        subst hErr
                        rfl
                      | ok q =>
                        rcases q with ⟨hi, ⟨afterHi, hHi⟩⟩
                        rw [hHiAtom] at heq
                        by_cases hRng : lo ≤ hi
                        · simp only [hRng, ↓reduceIte] at heq
                          have hSub : afterHi.length < n := by
                            simp only [List.length_cons] at hLo hHi hLen
                            omega
                          have hRec := ih afterHi.length hSub afterHi (Nat.le_refl _)
                            neg (.range lo hi :: acc)
                          unfold ClassItemsMatch at hRec
                          simp only [List.map_cons, toModelItem] at hRec
                          cases hRes : Internal.parseClassItems afterHi (.range lo hi :: acc) with
                          | error err2 =>
                            rw [hRes] at heq hRec
                            dsimp only [bind, Except.bind] at heq
                            injection heq with hErr
                            subst hErr
                            simpa [hRng] using hRec
                          | ok res =>
                            rw [hRes] at heq
                            dsimp only [bind, Except.bind, pure, Except.pure] at heq
                            cases heq
                        · simp only [hRng, ↓reduceIte] at heq
                          injection heq with hErr
                          subst hErr
                          simp [hRng, Internal.invalidRangeErr]
                    · rename_i hNotRange
                      exact absurd rfl (hNotRange (e :: afterRest2))
                  · rename_i _ items r hProp heq
                    split at heq
                    · rename_i heq1
                      injection heq1 with _ h2
                      injection h2 with he
                      exact absurd he heRbr
                    · rename_i rest2 _ heqRest
                      injection heqRest with _ hRestEq
                      subst hRestEq
                      cases hHiAtom : Internal.readClassAtom (e :: afterRest2) with
                      | error err => rw [hHiAtom] at heq; cases heq
                      | ok q =>
                        rcases q with ⟨hi, ⟨afterHi, hHi⟩⟩
                        rw [hHiAtom] at heq
                        by_cases hRng : lo ≤ hi
                        · simp only [hRng, ↓reduceIte] at heq
                          have hSub : afterHi.length < n := by
                            simp only [List.length_cons] at hLo hHi hLen
                            omega
                          have hRec := ih afterHi.length hSub afterHi (Nat.le_refl _)
                            neg (.range lo hi :: acc)
                          unfold ClassItemsMatch at hRec
                          simp only [List.map_cons, toModelItem] at hRec
                          cases hRes : Internal.parseClassItems afterHi (.range lo hi :: acc) with
                          | error err2 =>
                            rw [hRes] at heq
                            dsimp only [bind, Except.bind] at heq
                            cases heq
                          | ok res =>
                            rw [hRes] at heq hRec
                            dsimp only [bind, Except.bind, pure, Except.pure] at heq
                            injection heq with hPair
                            cases hPair
                            simpa [hRng] using hRec
                        · simp only [hRng, ↓reduceIte] at heq
                          cases heq
                    · rename_i hNotRange
                      exact absurd rfl (hNotRange (e :: afterRest2))
            · rw [hParseStep]
              have hND : ∀ tl, (d :: afterRest) ≠ '-' :: tl := by
                intro _ h; injection h with hd; exact hdDash hd
              rw [model_parseClassAfter_nonDash neg (acc.map toModelItem) lo (d :: afterRest) hND]
              have hRec := ih (d :: afterRest).length hStep (d :: afterRest) (Nat.le_refl _)
                neg (.single lo :: acc)
              unfold ClassItemsMatch at hRec
              simp only [pure, Except.pure, List.map_cons, toModelItem] at hRec ⊢
              split
              · rename_i _ errRes heq
                split at heq
                · rename_i heq1; injection heq1 with hd; exact absurd hd hdDash
                · rename_i heq1; injection heq1 with hd; exact absurd hd hdDash
                · cases hRes : Internal.parseClassItems (d :: afterRest) (.single lo :: acc) with
                  | error e =>
                    rw [hRes] at heq hRec
                    injection heq with hErr
                    subst hErr
                    exact hRec
                  | ok res =>
                    rw [hRes] at heq
                    cases heq
              · rename_i _ items r hProp heq
                split at heq
                · rename_i heq1; injection heq1 with hd; exact absurd hd hdDash
                · rename_i heq1; injection heq1 with hd; exact absurd hd hdDash
                · cases hRes : Internal.parseClassItems (d :: afterRest) (.single lo :: acc) with
                  | error e => rw [hRes] at heq; cases heq
                  | ok res =>
                    rw [hRes] at heq hRec
                    injection heq with hPair
                    cases hPair
                    exact hRec

private theorem parseClassItems_match (neg : Bool) (acc : List Internal.CharClassItem)
    (cs : List Char) : ClassItemsMatch neg acc cs :=
  parseClassItems_match_aux cs.length cs (Nat.le_refl _) neg acc

/-- Model character-class entry point dispatching optional leading `'!'` negation. -/
def modelParseClass (cs : List Char) : Except GlobErrorKind (List Model.Atom) :=
  match cs with
  | '!' :: tail => Model.parseClass true [] tail
  | other => Model.parseClass false [] other

/-- Equivalence invariant between `Internal.parseCharClass` and `modelParseClass`. -/
def CharClassMatch (cs : List Char) : Prop :=
  match Internal.parseCharClass cs with
  | .error e => modelParseClass cs = .error e.kind
  | .ok (cc, r) => modelParseClass cs = (Model.parseAtoms r.1).map (.charClass (toModelClass cc) :: ·)

private theorem internal_parseCharClass_nonBang (d : Char) (tail : List Char) (hd : d ≠ '!') :
    Internal.parseCharClass (d :: tail) =
      match Internal.parseClassItems (d :: tail) [] with
      | .error err => .error err
      | .ok (items, r) => .ok ({ negated := false, items }, r) := by
  unfold Internal.parseCharClass
  simp [hd]
  cases Internal.parseClassItems (d :: tail) [] <;> rfl

/-- `Internal.parseCharClass` matches `modelParseClass` on all inputs. -/
theorem parseCharClass_match (cs : List Char) : CharClassMatch cs := by
  unfold CharClassMatch modelParseClass
  cases cs with
  | nil =>
    unfold Internal.parseCharClass
    have h := parseClassItems_match false [] []
    unfold ClassItemsMatch at h
    simp only [List.map_nil, bind, Except.bind, pure, Except.pure] at h ⊢
    cases hRes : Internal.parseClassItems [] [] with
    | error e => simp only [hRes] at h ⊢; exact h
    | ok res => simp only [hRes, toModelClass] at h ⊢; exact h
  | cons d tail =>
    by_cases hdBang : d = '!'
    · subst hdBang
      unfold Internal.parseCharClass
      have h := parseClassItems_match true [] tail
      unfold ClassItemsMatch at h
      simp only [List.map_nil, bind, Except.bind, pure, Except.pure] at h ⊢
      cases hRes : Internal.parseClassItems tail [] with
      | error e => simp only [hRes] at h ⊢; exact h
      | ok res => simp only [hRes, toModelClass] at h ⊢; exact h
    · rw [internal_parseCharClass_nonBang d tail hdBang]
      have h := parseClassItems_match false [] (d :: tail)
      unfold ClassItemsMatch at h
      simp only [List.map_nil] at h
      have hModel :
          (match d :: tail with
          | '!' :: t => Model.parseClass true [] t
          | other => Model.parseClass false [] other) =
            Model.parseClass false [] (d :: tail) := by
        split
        · rename_i t heq
          injection heq with hd
          exact absurd hd hdBang
        · rfl
      rw [hModel]
      cases hRes : Internal.parseClassItems (d :: tail) [] with
      | error e => simp only [hRes] at h ⊢; exact h
      | ok res => simp only [hRes, toModelClass] at h ⊢; exact h

end LeanSwe.Glob.Proofs
