import LeanSwe.Glob.Interface
import LeanSwe.Glob.SpecTests

namespace LeanSwe.Glob.Proofs

open Core
open Core.NondetTest

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

private theorem compilePattern_err_ne_empty {pat : String} {err : GlobError}
    (h : Internal.compilePattern pat = .error err) : err.message ≠ "" :=
  parseSegList_nonEmptyErr _ err h

/-- Proof of `test_glob_onError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_glob_onError_returnsNonEmptyMessage :
    AllPass (test_glob_onError_returnsNonEmptyMessage defaultApi) := by
  intro pat path
  simp only [defaultApi, isMatch, Internal.isMatch, bind, Except.bind]
  cases hc : Internal.compilePattern pat with
  | ok _ => simp [pure, Except.pure, assume]
  | error e => exact ⟨compilePattern_err_ne_empty hc, trivial⟩

/-- Proof of `test_glob_isMatch_iff_validateOk` for `defaultApi`. -/
theorem proof_glob_isMatch_iff_validateOk :
    AllPass (test_glob_isMatch_iff_validateOk defaultApi) := by
  intro pat path
  simp only [defaultApi, validate, isMatch, Internal.validate, Internal.isMatch,
    bind, Except.bind, pure, Except.pure]
  cases hc : Internal.compilePattern pat with
  | error e => simp [assert]
  | ok _ => simp [assert]

/-- Proof of `test_glob_filter_preservesValidity` for `defaultApi`. -/
theorem proof_glob_filter_preservesValidity :
    AllPass (test_glob_filter_preservesValidity defaultApi) := by
  intro pat paths
  simp only [defaultApi, validate, filter, isMatch,
    Internal.validate, Internal.filter, Internal.isMatch, bind, Except.bind, pure, Except.pure]
  cases hc : Internal.compilePattern pat with
  | error _ => simp [assume]
  | ok pats =>
    simp only [assert]
    refine ⟨Array.size_filter_le, ?_⟩
    intro i hi
    have hPos : (Internal.filterCompiled pats paths)[i]! = (Internal.filterCompiled pats paths)[i] :=
      getElem!_pos _ i hi
    have hMem : (Internal.filterCompiled pats paths)[i] ∈ Internal.filterCompiled pats paths :=
      Array.getElem_mem hi
    unfold Internal.filterCompiled at hMem
    rw [Array.mem_filter] at hMem
    simp only [Internal.filterCompiled] at hPos ⊢
    rw [hPos]
    exact ⟨hMem.2, trivial⟩

/-- Proof of `test_glob_countMatches_eq_filterSize` for `defaultApi`. -/
theorem proof_glob_countMatches_eq_filterSize :
    AllPass (test_glob_countMatches_eq_filterSize defaultApi) := by
  intro pat paths
  simp only [defaultApi, filter, countMatches, Internal.filter, Internal.countMatches,
    bind, Except.bind, pure, Except.pure]
  cases hc : Internal.compilePattern pat with
  | error e => simp [assert]
  | ok _ => simp [assert]

private theorem matchSegPats_globStar (ss : List (List Char)) :
    Internal.matchSegPats [.globStar] ss = true := by
  induction ss with
  | nil => simp [Internal.matchSegPats]
  | cons s rest ih => simp [Internal.matchSegPats, ih]

private theorem compile_globStar :
    Internal.compilePattern "**" = .ok [.globStar] := by
  have h : "**".toList = ['*', '*'] := by decide
  simp [Internal.compilePattern, h, Internal.splitOnChar, Internal.parseSegList,
    Internal.parseSegment, bind, Except.bind, pure, Except.pure]

/-- Proof of `test_glob_globStar_matchesAll` for `defaultApi`. -/
theorem proof_glob_globStar_matchesAll :
    AllPass (test_glob_globStar_matchesAll defaultApi) := by
  intro path
  simp only [defaultApi, isMatch, Internal.isMatch, compile_globStar, bind, Except.bind, pure,
    Except.pure, assert]
  exact ⟨matchSegPats_globStar _, trivial⟩

private theorem splitOnChar_ne_nil (sep : Char) (cs : List Char) :
    Internal.splitOnChar sep cs ≠ [] := by
  induction cs with
  | nil => simp [Internal.splitOnChar]
  | cons c rest _ =>
    simp only [Internal.splitOnChar]
    split
    · simp
    · cases Internal.splitOnChar sep rest <;> simp

private theorem splitOnChar_cons_nonSep (sep c : Char) (hne : c ≠ sep) (cs : List Char) :
    Internal.splitOnChar sep (c :: cs) =
      match Internal.splitOnChar sep cs with
      | [] => [[c]]
      | seg :: rest => (c :: seg) :: rest := by
  have hb : (c == sep) = false := beq_false_of_ne hne
  simp only [Internal.splitOnChar, hb]
  rfl

private theorem splitOnChar_escapeChars (cs : List Char) :
    Internal.splitOnChar '/' (Internal.escapeChars cs) =
      (Internal.splitOnChar '/' cs).map Internal.escapeChars := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    by_cases hSep : c = '/'
    · subst hSep
      simp [Internal.escapeChars, Internal.splitOnChar, ih]
    · by_cases hMeta : c = '*' ∨ c = '?' ∨ c = '[' ∨ c = ']' ∨ c = '\\'
      · have hMetaB : (c == '*' || c == '?' || c == '[' || c == ']' || c == '\\') = true := by
          rcases hMeta with rfl | rfl | rfl | rfl | rfl <;> rfl
        have hEsc : Internal.escapeChars (c :: rest) = '\\' :: c :: Internal.escapeChars rest := by
          simp [Internal.escapeChars, hMetaB]
        rw [hEsc]
        have hBsNe : ('\\' : Char) ≠ '/' := by decide
        rw [splitOnChar_cons_nonSep '/' '\\' hBsNe, splitOnChar_cons_nonSep '/' c hSep,
          splitOnChar_cons_nonSep '/' c hSep, ih]
        cases hsp : Internal.splitOnChar '/' rest with
        | nil => exact absurd hsp (splitOnChar_ne_nil '/' rest)
        | cons seg tl => simp [Internal.escapeChars, hMetaB]
      · have hMetaB : (c == '*' || c == '?' || c == '[' || c == ']' || c == '\\') = false := by
          have hn1 : c ≠ '*' := fun h => hMeta (Or.inl h)
          have hn2 : c ≠ '?' := fun h => hMeta (Or.inr (Or.inl h))
          have hn3 : c ≠ '[' := fun h => hMeta (Or.inr (Or.inr (Or.inl h)))
          have hn4 : c ≠ ']' := fun h => hMeta (Or.inr (Or.inr (Or.inr (Or.inl h))))
          have hn5 : c ≠ '\\' := fun h => hMeta (Or.inr (Or.inr (Or.inr (Or.inr h))))
          simp [hn1, hn2, hn3, hn4, hn5]
        have hEsc : Internal.escapeChars (c :: rest) = c :: Internal.escapeChars rest := by
          simp [Internal.escapeChars, hMetaB]
        rw [hEsc, splitOnChar_cons_nonSep '/' c hSep, splitOnChar_cons_nonSep '/' c hSep, ih]
        cases hsp : Internal.splitOnChar '/' rest with
        | nil => exact absurd hsp (splitOnChar_ne_nil '/' rest)
        | cons seg tl => simp [Internal.escapeChars, hMetaB]

private theorem parseAtoms_escapeChars (cs : List Char) :
    Internal.parseAtoms (Internal.escapeChars cs) = .ok (cs.map Internal.SegAtom.lit) := by
  induction cs with
  | nil => simp [Internal.escapeChars, Internal.parseAtoms]
  | cons c rest ih =>
    by_cases hMeta : c = '*' ∨ c = '?' ∨ c = '[' ∨ c = ']' ∨ c = '\\'
    · have hMetaB : (c == '*' || c == '?' || c == '[' || c == ']' || c == '\\') = true := by
        rcases hMeta with rfl | rfl | rfl | rfl | rfl <;> rfl
      simp [Internal.escapeChars, hMetaB, Internal.parseAtoms, ih, bind, Except.bind, pure, Except.pure]
    · have hn1 : c ≠ '*' := fun h => hMeta (Or.inl h)
      have hn2 : c ≠ '?' := fun h => hMeta (Or.inr (Or.inl h))
      have hn3 : c ≠ '[' := fun h => hMeta (Or.inr (Or.inr (Or.inl h)))
      have hn4 : c ≠ ']' := fun h => hMeta (Or.inr (Or.inr (Or.inr (Or.inl h))))
      have hn5 : c ≠ '\\' := fun h => hMeta (Or.inr (Or.inr (Or.inr (Or.inr h))))
      have hMetaB : (c == '*' || c == '?' || c == '[' || c == ']' || c == '\\') = false := by
        simp [hn1, hn2, hn3, hn4, hn5]
      simp [Internal.escapeChars, hMetaB, Internal.parseAtoms, ih,
        hn5, bind, Except.bind, pure, Except.pure]

private theorem escapeChars_ne_globStar (cs : List Char) :
    Internal.escapeChars cs ≠ ['*', '*'] := by
  cases cs with
  | nil => simp [Internal.escapeChars]
  | cons c rest =>
    by_cases hMeta : c = '*' ∨ c = '?' ∨ c = '[' ∨ c = ']' ∨ c = '\\'
    · have hMetaB : (c == '*' || c == '?' || c == '[' || c == ']' || c == '\\') = true := by
        rcases hMeta with rfl | rfl | rfl | rfl | rfl <;> rfl
      simp [Internal.escapeChars, hMetaB]
    · have hn1 : c ≠ '*' := fun h => hMeta (Or.inl h)
      have hn2 : c ≠ '?' := fun h => hMeta (Or.inr (Or.inl h))
      have hn3 : c ≠ '[' := fun h => hMeta (Or.inr (Or.inr (Or.inl h)))
      have hn4 : c ≠ ']' := fun h => hMeta (Or.inr (Or.inr (Or.inr (Or.inl h))))
      have hn5 : c ≠ '\\' := fun h => hMeta (Or.inr (Or.inr (Or.inr (Or.inr h))))
      have hMetaB : (c == '*' || c == '?' || c == '[' || c == ']' || c == '\\') = false := by
        simp [hn1, hn2, hn3, hn4, hn5]
      simp [Internal.escapeChars, hMetaB, hn1]

private theorem parseSegList_map_escapeChars (segs : List (List Char)) :
    Internal.parseSegList (segs.map Internal.escapeChars) =
      .ok (segs.map fun s => .atoms (s.map Internal.SegAtom.lit)) := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
    have hSeg : Internal.parseSegment (Internal.escapeChars s) =
        .ok (.atoms (s.map Internal.SegAtom.lit)) := by
      simp [Internal.parseSegment, beq_false_of_ne (escapeChars_ne_globStar s),
        parseAtoms_escapeChars s, Except.map]
    simp [Internal.parseSegList, hSeg, ih, bind, Except.bind, pure, Except.pure]

private theorem matchSegAtoms_map_lit (cs : List Char) :
    Internal.matchSegAtoms (cs.map Internal.SegAtom.lit) cs = true := by
  induction cs with
  | nil => simp [Internal.matchSegAtoms]
  | cons c rest ih => simp [Internal.matchSegAtoms, ih]

private theorem matchSegPats_map_lits (segs : List (List Char)) :
    Internal.matchSegPats (segs.map fun s => .atoms (s.map Internal.SegAtom.lit)) segs = true := by
  induction segs with
  | nil => simp [Internal.matchSegPats]
  | cons s rest ih => simp [Internal.matchSegPats, matchSegAtoms_map_lit s, ih]

/-- Proof of `test_glob_escape_matchesSelf` for `defaultApi`. -/
theorem proof_glob_escape_matchesSelf :
    AllPass (test_glob_escape_matchesSelf defaultApi) := by
  intro path
  simp only [defaultApi, isMatch, escape, Internal.isMatch, Internal.escape,
    Internal.compilePattern, String.toList_ofList, splitOnChar_escapeChars,
    parseSegList_map_escapeChars, bind, Except.bind, pure, Except.pure, assert]
  exact ⟨matchSegPats_map_lits (Internal.splitOnChar '/' path.toList), trivial⟩

private theorem compile_lbracket :
    Internal.compilePattern "[" = .error Internal.classUnclosedErr := by
  have hl : "[".toList = ['['] := by decide
  simp [Internal.compilePattern, hl, Internal.splitOnChar, Internal.parseSegList,
    Internal.parseSegment, Internal.parseAtoms, Internal.parseCharClass, Internal.parseClassItems,
    bind, Except.bind, Except.map]

private theorem compile_star_lean :
    Internal.compilePattern "*.lean" =
      .ok [.atoms [.star, .lit '.', .lit 'l', .lit 'e', .lit 'a', .lit 'n']] := by
  have hs : "*.lean".toList = ['*', '.', 'l', 'e', 'a', 'n'] := by decide
  simp [Internal.compilePattern, hs, Internal.splitOnChar, Internal.parseSegList,
    Internal.parseSegment, Internal.parseAtoms, bind, Except.bind, pure, Except.pure, Except.map]

/-- Non-vacuity `CanReach` witness for `test_glob_onError_returnsNonEmptyMessage` on `defaultApi`. -/
theorem reach_glob_onError_returnsNonEmptyMessage :
    CanReach (test_glob_onError_returnsNonEmptyMessage defaultApi) := by
  refine ⟨"[", "a", ?_⟩
  simp [defaultApi, isMatch, Internal.isMatch, compile_lbracket, Internal.classUnclosedErr,
    bind, Except.bind, assert]

/-- Non-vacuity `CanReach` witness for `test_glob_isMatch_iff_validateOk` on `defaultApi`. -/
theorem reach_glob_isMatch_iff_validateOk :
    CanReach (test_glob_isMatch_iff_validateOk defaultApi) :=
  ⟨"*.lean", "Main.lean", proof_glob_isMatch_iff_validateOk "*.lean" "Main.lean"⟩

/-- Non-vacuity `CanReach` witness for `test_glob_filter_preservesValidity` on `defaultApi`. -/
theorem reach_glob_filter_preservesValidity :
    CanReach (test_glob_filter_preservesValidity defaultApi) := by
  refine ⟨"*.lean", #["a.lean"], ?_⟩
  have ha : "a.lean".toList = ['a', '.', 'l', 'e', 'a', 'n'] := by decide
  simp [defaultApi, validate, filter, isMatch, Internal.validate, Internal.filter, Internal.isMatch,
    Internal.filterCompiled, compile_star_lean, ha, Internal.splitOnChar, Internal.matchSegPats,
    Internal.matchSegAtoms, bind, Except.bind, pure, Except.pure, assert, assume]
  refine ⟨0, ?_⟩
  simp [ha, Internal.splitOnChar, Internal.matchSegPats, Internal.matchSegAtoms]

/-- Non-vacuity `CanReach` witness for `test_glob_countMatches_eq_filterSize` on `defaultApi`. -/
theorem reach_glob_countMatches_eq_filterSize :
    CanReach (test_glob_countMatches_eq_filterSize defaultApi) :=
  ⟨"*.lean", #["a.lean"], proof_glob_countMatches_eq_filterSize "*.lean" #["a.lean"]⟩

/-- Non-vacuity `CanReach` witness for `test_glob_globStar_matchesAll` on `defaultApi`. -/
theorem reach_glob_globStar_matchesAll :
    CanReach (test_glob_globStar_matchesAll defaultApi) :=
  ⟨"a/b/c", proof_glob_globStar_matchesAll "a/b/c"⟩

/-- Non-vacuity `CanReach` witness for `test_glob_escape_matchesSelf` on `defaultApi`. -/
theorem reach_glob_escape_matchesSelf :
    CanReach (test_glob_escape_matchesSelf defaultApi) :=
  ⟨"a/*/b", proof_glob_escape_matchesSelf "a/*/b"⟩

private def toModelItem : Internal.CharClassItem → Model.ClassItem
  | .single c => .single c
  | .range lo hi => .range lo hi

private def toModelClass (cc : Internal.CharClass) : Model.CharClass :=
  { negated := cc.negated, items := cc.items.map toModelItem }

private def toModelAtom : Internal.SegAtom → Model.Atom
  | .lit c => .lit c
  | .anyChar => .any
  | .star => .star
  | .charClass cc => .charClass (toModelClass cc)

private def toModelSeg : Internal.SegmentPat → Model.Segment
  | .globStar => .globStar
  | .atoms xs => .atoms (xs.map toModelAtom)

private theorem splitOnChar_slash_eq_splitSlash (cs : List Char) :
    Internal.splitOnChar '/' cs = Model.splitSlash cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [Internal.splitOnChar, Model.splitSlash, ih]
    split <;> rfl

private theorem escapeChars_eq_model (cs : List Char) :
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

private theorem matchCharClass_eq_model (cc : Internal.CharClass) (c : Char) :
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

private theorem matchSegAtoms_eq_evalSeg (atoms : List Internal.SegAtom) (cs : List Char) :
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

private theorem evalSeg_star_congr {a1 a2 : List Model.Atom}
    (ha : ∀ cs, Model.evalSeg a1 cs = Model.evalSeg a2 cs) (cs : List Char) :
    Model.evalSeg (.star :: a1) cs = Model.evalSeg (.star :: a2) cs := by
  simp only [Model.evalSeg]
  exact evalSegStar_congr ha cs

private theorem evalSeg_star_star (xs : List Model.Atom) (cs : List Char) :
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

private theorem matchSegPats_eq_evalPath (pats : List Internal.SegmentPat) (segs : List (List Char)) :
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

private theorem evalPath_globStar_congr {p1 p2 : List Model.Segment}
    (hp : ∀ segs, Model.evalPath p1 segs = Model.evalPath p2 segs) (segs : List (List Char)) :
    Model.evalPath (.globStar :: p1) segs = Model.evalPath (.globStar :: p2) segs := by
  simp only [Model.evalPath]
  exact evalPathGlobStar_congr hp segs

private theorem evalPath_globStar_globStar (xs : List Model.Segment) (segs : List (List Char)) :
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

private def modelParseClass (cs : List Char) : Except GlobErrorKind (List Model.Atom) :=
  match cs with
  | '!' :: tail => Model.parseClass true [] tail
  | other => Model.parseClass false [] other

private def CharClassMatch (cs : List Char) : Prop :=
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

private theorem parseCharClass_match (cs : List Char) : CharClassMatch cs := by
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

private theorem parseCharClass_len_le {cs : List Char} {cc : Internal.CharClass}
    {r : List Char} {hr : r.length ≤ cs.length}
    (_h : Internal.parseCharClass cs = .ok (cc, ⟨r, hr⟩)) :
    r.length ≤ cs.length := hr

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

/-- Proof of `test_glob_validate_matchesModel` for `defaultApi`. -/
theorem proof_glob_validate_matchesModel :
    AllPass (test_glob_validate_matchesModel defaultApi) := by
  intro pat
  have h := compilePattern_match pat
  simp only [defaultApi, validate, Internal.validate, Model.validateModel,
    bind, Except.bind, pure, Except.pure, Except.map]
  cases hc : Internal.compilePattern pat with
  | error e =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact ⟨⟨h, compilePattern_err_ne_empty hc⟩, trivial⟩
    | ok ps2 => rw [hc, hm] at h; exact False.elim h
  | ok ps1 =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact False.elim h
    | ok ps2 => exact ⟨trivial, trivial⟩

/-- Proof of `test_glob_isMatch_matchesModel` for `defaultApi`. -/
theorem proof_glob_isMatch_matchesModel :
    AllPass (test_glob_isMatch_matchesModel defaultApi) := by
  intro pat path
  have h := compilePattern_match pat
  simp only [defaultApi, isMatch, Internal.isMatch, Model.isMatchModel,
    splitOnChar_slash_eq_splitSlash, bind, Except.bind, pure, Except.pure, Except.map]
  cases hc : Internal.compilePattern pat with
  | error e =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact ⟨⟨h, compilePattern_err_ne_empty hc⟩, trivial⟩
    | ok ps2 => rw [hc, hm] at h; exact False.elim h
  | ok ps1 =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact False.elim h
    | ok ps2 => rw [hc, hm] at h; exact ⟨h (Model.splitSlash path.toList), trivial⟩

/-- Proof of `test_glob_filter_matchesModel` for `defaultApi`. -/
theorem proof_glob_filter_matchesModel :
    AllPass (test_glob_filter_matchesModel defaultApi) := by
  intro pat paths
  have h := compilePattern_match pat
  simp only [defaultApi, filter, Internal.filter, Internal.filterCompiled, Model.filterModel,
    splitOnChar_slash_eq_splitSlash, bind, Except.bind, pure, Except.pure, Except.map]
  cases hc : Internal.compilePattern pat with
  | error e =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact ⟨⟨h, compilePattern_err_ne_empty hc⟩, trivial⟩
    | ok ps2 => rw [hc, hm] at h; exact False.elim h
  | ok ps1 =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact False.elim h
    | ok ps2 =>
      rw [hc, hm] at h
      have hEq : (paths.filter fun p => Internal.matchSegPats ps1 (Model.splitSlash p.toList)) =
          (paths.filter fun p => Model.evalPath ps2 (Model.splitSlash p.toList)) := by
        congr 1
        funext p
        exact h (Model.splitSlash p.toList)
      exact ⟨hEq, trivial⟩

/-- Proof of `test_glob_countMatches_matchesModel` for `defaultApi`. -/
theorem proof_glob_countMatches_matchesModel :
    AllPass (test_glob_countMatches_matchesModel defaultApi) := by
  intro pat paths
  have h := compilePattern_match pat
  simp only [defaultApi, countMatches, Internal.countMatches, Internal.filter,
    Internal.filterCompiled, Model.countMatchesModel, Model.filterModel,
    splitOnChar_slash_eq_splitSlash, bind, Except.bind, pure, Except.pure, Except.map]
  cases hc : Internal.compilePattern pat with
  | error e =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact ⟨⟨h, compilePattern_err_ne_empty hc⟩, trivial⟩
    | ok ps2 => rw [hc, hm] at h; exact False.elim h
  | ok ps1 =>
    cases hm : Model.parsePattern pat with
    | error k => rw [hc, hm] at h; exact False.elim h
    | ok ps2 =>
      rw [hc, hm] at h
      have hEq : (paths.filter fun p => Internal.matchSegPats ps1 (Model.splitSlash p.toList)) =
          (paths.filter fun p => Model.evalPath ps2 (Model.splitSlash p.toList)) := by
        congr 1
        funext p
        exact h (Model.splitSlash p.toList)
      exact ⟨congrArg Array.size hEq, trivial⟩

/-- Proof of `test_glob_escape_matchesModel` for `defaultApi`. -/
theorem proof_glob_escape_matchesModel :
    AllPass (test_glob_escape_matchesModel defaultApi) := by
  intro literal
  simp [defaultApi, escape, Internal.escape, Model.escapeModel, escapeChars_eq_model, assert]

end LeanSwe.Glob.Proofs

