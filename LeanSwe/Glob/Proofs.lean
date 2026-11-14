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

end LeanSwe.Glob.Proofs
