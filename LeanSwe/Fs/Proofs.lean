import LeanSwe.Fs.Interface
import LeanSwe.Fs.SpecTests
import LeanSwe.Fs.Raw.Proofs

namespace LeanSwe.Fs.Proofs

open Core
open Core.NondetTest

/-- Proof of `test_fs_mapRawError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_fs_mapRawError_returnsNonEmptyMessage :
    AllPass (test_fs_mapRawError_returnsNonEmptyMessage defaultApi) := by
  intro raw
  simpa [defaultApi, Internal.mkApiM] using
    Fs.Raw.Proofs.proof_fsraw_mapRawError_returnsNonEmptyMessage raw

private theorem splitCharList_ne_nil (sep : Char) (cs : List Char) :
    Internal.splitCharList sep cs ≠ [] := by
  induction cs with
  | nil => simp [Internal.splitCharList]
  | cons c rest _ =>
    simp only [Internal.splitCharList]
    split
    · simp
    · cases Internal.splitCharList sep rest <;> simp

private theorem splitCharList_no_sep (sep : Char) (cs : List Char) :
    ∀ seg ∈ Internal.splitCharList sep cs, sep ∉ seg := by
  induction cs with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    simp only [Internal.splitCharList]
    split
    · intro seg hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp
      · exact ih seg hmem
    · next hne =>
      have hcne : c ≠ sep := fun h => hne (by subst h; exact beq_self_eq_true _)
      cases hsp : Internal.splitCharList sep rest with
      | nil => exact absurd hsp (splitCharList_ne_nil sep rest)
      | cons hd tl =>
        intro seg hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · intro hIn
          simp only [List.mem_cons] at hIn
          rcases hIn with hce | hIn
          · exact hcne hce.symm
          · exact ih hd (by rw [hsp]; simp) hIn
        · exact ih seg (by rw [hsp]; simp [hmem])

private theorem splitCharList_of_no_sep (sep : Char) (b : List Char) (hno : sep ∉ b) :
    Internal.splitCharList sep b = [b] := by
  induction b with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hcne : c ≠ sep := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [Internal.splitCharList, beq_false_of_ne hcne, ih']

private theorem splitCharList_append_slash (a b : List Char) (hno : '/' ∉ a) :
    Internal.splitCharList '/' (a ++ '/' :: b) = a :: Internal.splitCharList '/' b := by
  induction a with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hcne : c ≠ '/' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [List.cons_append, Internal.splitCharList, beq_false_of_ne hcne, ih']

private theorem splitCharList_append_tail_no_slash (a b : List Char) (hno : '/' ∉ b) :
    Internal.splitCharList '/' (a ++ '/' :: b) = Internal.splitCharList '/' a ++ [b] := by
  induction a with
  | nil =>
    simp only [List.nil_append, Internal.splitCharList, beq_self_eq_true, ↓reduceIte,
      splitCharList_of_no_sep '/' b hno, List.singleton_append]
  | cons c rest ih =>
    simp only [List.cons_append, Internal.splitCharList]
    split
    · simp [ih]
    · rw [ih]
      cases hsp : Internal.splitCharList '/' rest with
      | nil => exact absurd hsp (splitCharList_ne_nil '/' rest)
      | cons hd tl => simp

private theorem splitCharList_joinSlashChars (segs : List (List Char))
    (hne : segs ≠ []) (hno : ∀ s ∈ segs, '/' ∉ s) :
    Internal.splitCharList '/' (Internal.joinSlashChars segs) = segs := by
  induction segs with
  | nil => exact absurd rfl hne
  | cons s rest ih =>
    cases rest with
    | nil =>
      simp only [Internal.joinSlashChars]
      exact splitCharList_of_no_sep '/' s (hno s (by simp))
    | cons s2 tl =>
      have ih' := ih (by simp) (fun x hx => hno x (by simp [hx]))
      simp only [Internal.joinSlashChars]
      rw [splitCharList_append_slash s (Internal.joinSlashChars (s2 :: tl)) (hno s (by simp)), ih']

private theorem joinSlashChars_ne_nil {s : List Char} {tl : List (List Char)} (hs : s ≠ []) :
    Internal.joinSlashChars (s :: tl) ≠ [] := by
  cases tl with
  | nil => simp [Internal.joinSlashChars, hs]
  | cons _ _ =>
    simp only [Internal.joinSlashChars]
    cases s with
    | nil => exact absurd rfl hs
    | cons _ _ => simp

private theorem collapseChars_elems_valid (abs : Bool) (segs acc : List (List Char))
    (hAcc : ∀ s ∈ acc, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s)
    (hSegs : ∀ s ∈ segs, '/' ∉ s) :
    ∀ s ∈ Internal.collapseChars abs segs acc, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s := by
  induction segs generalizing acc with
  | nil =>
    intro s hs
    simp only [Internal.collapseChars, List.mem_reverse] at hs
    exact hAcc s hs
  | cons seg rest ih =>
    simp only [Internal.collapseChars]
    split
    · exact ih acc hAcc (fun x hx => hSegs x (by simp [hx]))
    · split
      · cases acc with
        | nil =>
          apply ih
          · intro s hs
            cases abs with
            | true => simp at hs
            | false => simp at hs; subst hs; decide
          · exact fun x hx => hSegs x (by simp [hx])
        | cons top tail =>
          simp only
          split
          · exact ih tail (fun x hx => hAcc x (by simp [hx])) (fun x hx => hSegs x (by simp [hx]))
          · apply ih
            · intro s hs
              cases abs with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hs
                rcases hs with rfl | hs
                · decide
                · exact hAcc s (List.mem_cons.mpr hs)
              | true => exact hAcc s (by simpa using hs)
            · exact fun x hx => hSegs x (by simp [hx])
      · apply ih
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · next h1 _ =>
            simp only [Bool.or_eq_true] at h1
            have hnEmpty : (!s.isEmpty) = true := by cases he : List.isEmpty s <;> simp_all
            have hnDot : (s != ['.']) = true := by cases hd : (s == ['.']) <;> simp_all
            exact ⟨hnEmpty, hnDot, hSegs s (by simp)⟩
          · exact hAcc s hs
        · exact fun x hx => hSegs x (by simp [hx])

/-- Proof of `test_fs_normPath_neverEmpty` for `defaultApi`. -/
theorem proof_fs_normPath_neverEmpty :
    AllPass (test_fs_normPath_neverEmpty defaultApi) := by
  intro path
  simp only [defaultApi, Internal.mkApiM, assert]
  refine ⟨?_, trivial⟩
  unfold Internal.normPath
  cases hAbs : Internal.isAbsChars path.toList
  · simp only [hAbs, Bool.false_eq_true, ↓reduceIte]
    cases hCol : Internal.collapseChars false (Internal.splitCharList '/' path.toList) [] with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte]
      decide
    | cons hd tl =>
      have hVal := collapseChars_elems_valid false (Internal.splitCharList '/' path.toList) []
        (fun _ h => by simp at h) (splitCharList_no_sep '/' path.toList) hd (by rw [hCol]; simp)
      have hhdNe : hd ≠ [] := by cases hd <;> simp_all
      have hjNe := joinSlashChars_ne_nil (tl := tl) hhdNe
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      intro h
      have hlen := congrArg String.toList h
      simp only [String.toList_ofList, show ("" : String).toList = [] from rfl] at hlen
      exact hjNe hlen
  · simp only [hAbs, ↓reduceIte]
    intro h
    have hlen := congrArg String.toList h
    simp [show ("" : String).toList = [] from rfl] at hlen

private def ValidStack (abs : Bool) : List (List Char) → Prop
  | [] => True
  | top :: tail =>
    !top.isEmpty ∧ top != ['.'] ∧ '/' ∉ top ∧ ValidStack abs tail ∧
      (top = ['.', '.'] → abs = false ∧ ∀ x ∈ tail, x = ['.', '.'])

private theorem validStack_tail {abs : Bool} {top : List Char} {tail : List (List Char)}
    (h : ValidStack abs (top :: tail)) : ValidStack abs tail :=
  h.2.2.2.1

private theorem validStack_push_nonDotDot {abs : Bool} {seg : List Char} {acc : List (List Char)}
    (h1 : !seg.isEmpty) (h2 : seg != ['.']) (h3 : '/' ∉ seg) (h4 : seg ≠ ['.', '.'])
    (hAcc : ValidStack abs acc) : ValidStack abs (seg :: acc) :=
  ⟨h1, h2, h3, hAcc, fun hm => absurd hm h4⟩

private theorem validStack_push_dotDot {acc : List (List Char)}
    (hAbs : ∀ x ∈ acc, x = ['.', '.']) (hAcc : ValidStack false acc) :
    ValidStack false (['.', '.'] :: acc) :=
  ⟨by decide, by decide, by decide, hAcc, fun _ => ⟨rfl, hAbs⟩⟩

private theorem collapseChars_validStack (abs : Bool) (segs acc : List (List Char))
    (hAcc : ValidStack abs acc) (hSegs : ∀ s ∈ segs, '/' ∉ s) :
    ValidStack abs (Internal.collapseChars abs segs acc).reverse := by
  induction segs generalizing acc with
  | nil => simpa [Internal.collapseChars] using hAcc
  | cons seg rest ih =>
    simp only [Internal.collapseChars]
    split
    · exact ih acc hAcc (fun x hx => hSegs x (by simp [hx]))
    · split
      · cases acc with
        | nil =>
          apply ih
          · cases abs
            · exact validStack_push_dotDot (fun _ h => by simp at h) trivial
            · trivial
          · exact fun x hx => hSegs x (by simp [hx])
        | cons top tail =>
          simp only
          split
          · exact ih tail (validStack_tail hAcc) (fun x hx => hSegs x (by simp [hx]))
          · next hNotNe =>
            have hTop : top = ['.', '.'] := by
              cases hb : (top == ['.', '.']) <;> simp_all [beq_iff_eq]
            have hTail := hAcc.2.2.2.2 hTop
            apply ih
            · cases abs
              · refine validStack_push_dotDot ?_ hAcc
                intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact hTop
                · exact hTail.2 x hx
              · exact absurd hTail.1 (by decide)
            · exact fun x hx => hSegs x (by simp [hx])
      · next h1 h2 =>
        simp only [Bool.or_eq_true] at h1
        have hnEmpty : (!seg.isEmpty) = true := by cases he : List.isEmpty seg <;> simp_all
        have hnDot : (seg != ['.']) = true := by cases hd : (seg == ['.']) <;> simp_all
        have hnDotDot : seg ≠ ['.', '.'] := fun h => h2 (by subst h; rfl)
        exact ih (seg :: acc)
          (validStack_push_nonDotDot hnEmpty hnDot (hSegs seg (by simp)) hnDotDot hAcc)
          (fun x hx => hSegs x (by simp [hx]))

private def NoDotDot (xs : List (List Char)) : Prop :=
  ∀ s ∈ xs, s ≠ ['.', '.']

private def ValidOrder : Bool → List (List Char) → Prop
  | true, xs => NoDotDot xs
  | false, xs => ∃ pre suf, xs = pre ++ suf ∧ (∀ x ∈ pre, x = ['.', '.']) ∧ NoDotDot suf

private theorem validStack_to_validOrder (abs : Bool) (acc : List (List Char))
    (h : ValidStack abs acc) : ValidOrder abs acc.reverse := by
  induction acc with
  | nil =>
    cases abs
    · exact ⟨[], [], rfl, fun _ hm => by simp at hm, fun _ hm => by simp at hm⟩
    · intro _ hm; simp at hm
  | cons top tail ih =>
    have ih' := ih (validStack_tail h)
    by_cases hTop : top = ['.', '.']
    · have hInfo := h.2.2.2.2 hTop
      cases abs
      · refine ⟨tail.reverse ++ [top], [], by simp, ?_, fun _ hm => by simp at hm⟩
        intro x hx
        simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hInfo.2 x hx
        · exact hTop
      · exact absurd hInfo.1 (by decide)
    · cases abs
      · rcases ih' with ⟨pre, suf, hEq, hPre, hSuf⟩
        refine ⟨pre, suf ++ [top], by simp [hEq], hPre, ?_⟩
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hSuf x hx
        · exact hTop
      · intro x hx
        simp only [List.mem_reverse, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hTop
        · exact ih' x (List.mem_reverse.mpr hx)

private theorem collapseChars_noop (abs : Bool) (rest acc : List (List Char))
    (hElem : ∀ s ∈ rest, !s.isEmpty ∧ s != ['.'])
    (hNoPop : NoDotDot rest ∨ (abs = false ∧ ValidOrder false rest ∧ ∀ x ∈ acc, x = ['.', '.'])) :
    Internal.collapseChars abs rest acc = acc.reverse ++ rest := by
  induction rest generalizing acc with
  | nil => simp [Internal.collapseChars]
  | cons seg rest ih =>
    have hS := hElem seg (by simp)
    have hnSkip : (seg.isEmpty || seg == ['.']) = false := by
      cases he : List.isEmpty seg <;> cases hd : (seg == ['.']) <;> simp_all
    simp only [Internal.collapseChars, hnSkip, Bool.false_eq_true, ↓reduceIte]
    by_cases hDotDot : seg = ['.', '.']
    · subst hDotDot
      rcases hNoPop with hNo | ⟨rfl, hOrd, hAccAll⟩
      · exact absurd rfl (hNo ['.', '.'] (by simp))
      · rcases hOrd with ⟨pre, suf, hEq, hPre, hSuf⟩
        have hOrdRest : ValidOrder false rest := by
          cases pre with
          | nil =>
            simp only [List.nil_append] at hEq
            have hFalse : (['.', '.'] : List Char) ≠ ['.', '.'] := hSuf ['.', '.'] (by rw [← hEq]; simp)
            exact absurd rfl hFalse
          | cons _ ptail =>
            simp only [List.cons_append, List.cons.injEq] at hEq
            exact ⟨ptail, suf, hEq.2, fun x hx => hPre x (by simp [hx]), hSuf⟩
        have hEqTrue : (['.', '.'] == ['.', '.']) = true := rfl
        simp only [hEqTrue, ↓reduceIte]
        cases acc with
        | nil =>
          rw [ih _ (fun x hx => hElem x (by simp [hx]))
            (Or.inr ⟨rfl, hOrdRest, fun x hx => by simp at hx; exact hx⟩)]
          simp
        | cons top tail =>
          have hTopDot : top = ['.', '.'] := hAccAll top (by simp)
          have hNotNe : (top != ['.', '.']) = false := by simp [hTopDot]
          simp only [hNotNe, Bool.false_eq_true, ↓reduceIte]
          rw [ih _ (fun x hx => hElem x (by simp [hx]))
            (Or.inr ⟨rfl, hOrdRest, fun x hx => by
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · rfl
              · exact hAccAll x (List.mem_cons.mpr hx)⟩)]
          simp
    · have hNeFalse : (seg == ['.', '.']) = false := beq_false_of_ne hDotDot
      simp only [hNeFalse, Bool.false_eq_true, ↓reduceIte]
      have hRestNoDot : NoDotDot rest := by
        rcases hNoPop with hNo | ⟨_, hOrd, _⟩
        · exact fun x hx => hNo x (by simp [hx])
        · rcases hOrd with ⟨pre, suf, hEq, hPre, hSuf⟩
          cases pre with
          | nil =>
            simp only [List.nil_append] at hEq
            exact fun x hx => hSuf x (by rw [← hEq]; simp [hx])
          | cons phd _ =>
            simp only [List.cons_append, List.cons.injEq] at hEq
            exact absurd hEq.1.symm (fun h => hDotDot (h ▸ hPre phd (by simp)))
      rw [ih (seg :: acc) (fun x hx => hElem x (by simp [hx])) (Or.inl hRestNoDot)]
      simp

private theorem isAbsChars_joinSlashChars_head {hd : List Char} {tl : List (List Char)}
    (hne : hd ≠ []) (hno : '/' ∉ hd) :
    Internal.isAbsChars (Internal.joinSlashChars (hd :: tl)) = false := by
  cases tl with
  | nil =>
    cases hd with
    | nil => exact absurd rfl hne
    | cons c cs =>
      have hcne : c ≠ '/' := fun h => hno (by subst h; simp)
      simp [Internal.joinSlashChars, Internal.isAbsChars, hcne]
  | cons s2 _ =>
    cases hd with
    | nil => exact absurd rfl hne
    | cons c cs =>
      have hcne : c ≠ '/' := fun h => hno (by subst h; simp)
      simp [Internal.joinSlashChars, Internal.isAbsChars, hcne]

/-- Proof of `test_fs_normPath_idempotent` for `defaultApi`. -/
theorem proof_fs_normPath_idempotent :
    AllPass (test_fs_normPath_idempotent defaultApi) := by
  intro path
  simp only [defaultApi, Internal.mkApiM, assert]
  refine ⟨?_, trivial⟩
  conv => rhs; unfold Internal.normPath
  cases hAbs : Internal.isAbsChars path.toList
  · have hElem : ∀ s ∈ Internal.collapseChars false (Internal.splitCharList '/' path.toList) [],
        !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s :=
      collapseChars_elems_valid false (Internal.splitCharList '/' path.toList) []
        (fun _ h => by simp at h) (splitCharList_no_sep '/' path.toList)
    have hStack : ValidStack false
        (Internal.collapseChars false (Internal.splitCharList '/' path.toList) []).reverse :=
      collapseChars_validStack false (Internal.splitCharList '/' path.toList) []
        trivial (splitCharList_no_sep '/' path.toList)
    have hOrd : ValidOrder false (Internal.collapseChars false (Internal.splitCharList '/' path.toList) []) := by
      simpa using validStack_to_validOrder false _ hStack
    simp only [Internal.normPath, hAbs, Bool.false_eq_true, ↓reduceIte]
    cases hParts : Internal.collapseChars false (Internal.splitCharList '/' path.toList) [] with
    | nil =>
      have hDot : ".".toList = ['.'] := by decide
      simp [hDot, Internal.isAbsChars, Internal.splitCharList, Internal.collapseChars]
    | cons hd tl =>
      have hHd := hElem hd (by rw [hParts]; simp)
      have hHdNe : hd ≠ [] := by cases hd <;> simp_all
      have hNotAbs : Internal.isAbsChars (Internal.joinSlashChars (hd :: tl)) = false :=
        isAbsChars_joinSlashChars_head hHdNe hHd.2.2
      have hSplit : Internal.splitCharList '/' (Internal.joinSlashChars (hd :: tl)) = hd :: tl :=
        splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hElem s (by rw [hParts]; exact hs)).2.2)
      have hOrd' : ValidOrder false (hd :: tl) := hParts ▸ hOrd
      have hNoop := collapseChars_noop false (hd :: tl) []
        (fun s hs => ⟨(hElem s (by rw [hParts]; exact hs)).1, (hElem s (by rw [hParts]; exact hs)).2.1⟩)
        (Or.inr ⟨rfl, hOrd', fun _ h => by simp at h⟩)
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        String.toList_ofList, hNotAbs, hSplit, hNoop, List.reverse_nil, List.nil_append]
  · have hElem : ∀ s ∈ Internal.collapseChars true (Internal.splitCharList '/' path.toList) [],
        !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s :=
      collapseChars_elems_valid true (Internal.splitCharList '/' path.toList) []
        (fun _ h => by simp at h) (splitCharList_no_sep '/' path.toList)
    have hStack : ValidStack true
        (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []).reverse :=
      collapseChars_validStack true (Internal.splitCharList '/' path.toList) []
        trivial (splitCharList_no_sep '/' path.toList)
    have hOrd : ValidOrder true (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []) := by
      simpa using validStack_to_validOrder true _ hStack
    simp only [Internal.normPath, hAbs, ↓reduceIte]
    have hAbs2 : Internal.isAbsChars ('/' :: Internal.joinSlashChars
        (Internal.collapseChars true (Internal.splitCharList '/' path.toList) [])) = true := rfl
    simp only [String.toList_ofList]
    simp only [hAbs2, ↓reduceIte]
    have hSplit : Internal.splitCharList '/' ('/' :: Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) [])) =
        [] :: Internal.splitCharList '/' (Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) [])) := by
      simp [Internal.splitCharList]
    have hStepNil : Internal.collapseChars true ([] :: Internal.splitCharList '/' (Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []))) [] =
        Internal.collapseChars true (Internal.splitCharList '/' (Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []))) [] := by
      simp [Internal.collapseChars]
    rw [hSplit, hStepNil]
    cases hParts : Internal.collapseChars true (Internal.splitCharList '/' path.toList) [] with
    | nil => simp [Internal.joinSlashChars, Internal.splitCharList, Internal.collapseChars]
    | cons hd tl =>
      have hSplitJ : Internal.splitCharList '/' (Internal.joinSlashChars (hd :: tl)) = hd :: tl :=
        splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hElem s (by rw [hParts]; exact hs)).2.2)
      have hOrd' : NoDotDot (hd :: tl) := hParts ▸ hOrd
      have hNoop := collapseChars_noop true (hd :: tl) []
        (fun s hs => ⟨(hElem s (by rw [hParts]; exact hs)).1, (hElem s (by rw [hParts]; exact hs)).2.1⟩)
        (Or.inl hOrd')
      rw [hSplitJ, hNoop]
      simp

private theorem join_absOverridesBase (base sub : String) :
    Internal.isAbsolute sub = true → Internal.join base sub = sub := by
  intro h
  simp [Internal.join, h]

/-- Proof of `test_fs_join_absOverridesBase` for `defaultApi`. -/
theorem proof_fs_join_absOverridesBase :
    AllPass (test_fs_join_absOverridesBase defaultApi) := by
  intro base sub
  simp only [defaultApi, Internal.mkApiM, assume, assert]
  intro h
  exact ⟨join_absOverridesBase base sub h, trivial⟩

private theorem splitLastAux_append_singleton {α : Type} (xs acc : List α) (last : α) :
    Internal.splitLastAux (xs ++ [last]) acc = some (acc.reverse ++ xs, last) := by
  induction xs generalizing acc with
  | nil => simp [Internal.splitLastAux]
  | cons x rest ih =>
    cases rest with
    | nil => simp [Internal.splitLastAux]
    | cons _ _ =>
      have ih' := ih (x :: acc)
      simp only [List.cons_append] at ih'
      simp only [List.cons_append, Internal.splitLastAux]
      rw [ih']
      simp

private theorem cleanCharSegments_joinParentName (par? : Option String) (newName : String)
    (hValid : Internal.validFileName newName = true) :
    ∃ front, (Internal.cleanCharSegments (Internal.joinParentName par? newName)).2 = front ++ [newName.toList] := by
  unfold Internal.validFileName at hValid
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hValid
  rcases hValid with ⟨⟨⟨hNeEmpty, hNoSlash⟩, hNeDot⟩, _⟩
  have hNotEmptyB : (!newName.toList.isEmpty) = true := by simp [hNeEmpty]
  have hNeDotB : (newName.toList != ['.']) = true := bne_iff_ne.mpr hNeDot
  have hKeep : (fun s => !s.isEmpty && s != ['.']) newName.toList = true := by
    simp [hNotEmptyB, hNeDotB]
  have hSplitNew : Internal.splitCharList '/' newName.toList = [newName.toList] :=
    splitCharList_of_no_sep '/' newName.toList hNoSlash
  cases par? with
  | none =>
    refine ⟨[], ?_⟩
    simp [Internal.joinParentName, Internal.cleanCharSegments, hSplitNew, hKeep]
  | some par =>
    by_cases hRoot : par = "/"
    · subst hRoot
      refine ⟨[], ?_⟩
      have hLst : ("/" ++ newName).toList = '/' :: newName.toList := by
        simp [String.toList_append, show "/".toList = ['/'] by decide]
      have hSp : Internal.splitCharList '/' ('/' :: newName.toList) = [] :: [newName.toList] := by
        simp [Internal.splitCharList, hSplitNew]
      simp [Internal.joinParentName, Internal.cleanCharSegments, hLst, hSp, hKeep]
    · simp only [Internal.joinParentName, Internal.cleanCharSegments]
      have hLst : (par ++ "/" ++ newName).toList = par.toList ++ '/' :: newName.toList := by
        simp [String.toList_append, show "/".toList = ['/'] by decide]
      rw [hLst, splitCharList_append_tail_no_slash par.toList newName.toList hNoSlash, List.filter_append]
      simp [hKeep]

/-- Proof of `test_fs_withName_updatesName` for `defaultApi`. -/
theorem proof_fs_withName_updatesName :
    AllPass (test_fs_withName_updatesName defaultApi) := by
  intro path newName
  simp only [defaultApi, Internal.mkApiM]
  unfold Internal.withName
  split
  · simp [assume]
  · have hValid : Internal.validFileName newName = true := by
      cases hv : Internal.validFileName newName <;> simp_all
    cases hPar : Internal.splitParentName path with
    | none => simp [assume]
    | some pair =>
      rcases pair with ⟨par?, oldName⟩
      simp only [assert]
      obtain ⟨front, hSegs⟩ := cleanCharSegments_joinParentName par? newName hValid
      refine ⟨?_, trivial⟩
      unfold Internal.name Internal.splitParentName
      dsimp only
      rw [hSegs, splitLastAux_append_singleton]
      cases front <;> simp

private theorem splitRevAtDot_append_noDot (revTail revStem : List Char) (hno : '.' ∉ revTail) :
    Internal.splitRevAtDot (revTail ++ '.' :: revStem) = some (revStem, revTail) := by
  induction revTail with
  | nil => simp [Internal.splitRevAtDot]
  | cons c rest ih =>
    have hcne : c ≠ '.' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    unfold Internal.splitRevAtDot
    split
    · next he => simp at he
    · next he =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 hcne
    · next _ _ he =>
      simp only [List.cons_append, List.cons.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      rw [ih']

/-- Proof of `test_fs_withSuffix_updatesSuffix` for `defaultApi`. -/
theorem proof_fs_withSuffix_updatesSuffix :
    AllPass (test_fs_withSuffix_updatesSuffix defaultApi) := by
  intro path ext
  simp only [defaultApi, Internal.mkApiM, assume]
  intro hHead hNoDotTail
  cases hSufCall : Internal.withSuffix path ext with
  | error _ => simp
  | ok updated =>
    simp only [assert]
    refine ⟨?_, trivial⟩
    unfold Internal.withSuffix at hSufCall
    have hValidSuf : Internal.validSuffix ext = true := by
      cases hv : Internal.validSuffix ext
      · simp [hv] at hSufCall
      · rfl
    simp only [hValidSuf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSufCall
    cases hPar : Internal.splitParentName path with
    | none => simp [hPar] at hSufCall
    | some pair =>
      rcases pair with ⟨par?, oldName⟩
      simp only [hPar] at hSufCall
      let stemPart := (Internal.splitNameSuffix oldName).1
      by_cases hStemBad : (stemPart.isEmpty || stemPart.toList.all (· == '.')) = true
      · simp [stemPart, hStemBad] at hSufCall
      · have hNotBad : (stemPart.isEmpty || stemPart.toList.all (· == '.')) = false :=
          Bool.eq_false_iff.mpr hStemBad
        simp only [stemPart, hNotBad, Bool.false_eq_true, ↓reduceIte] at hSufCall
        change Internal.withName path (stemPart ++ ext) = .ok updated at hSufCall
        have hStemNeEmpty : stemPart.toList ≠ [] := by
          intro h
          have hEmp : stemPart = "" := by rw [← String.ofList_toList (s := stemPart), h]
          have he : stemPart.isEmpty = true := by rw [hEmp]; rfl
          simp [he] at hNotBad
        have hNotAllDots : stemPart.toList.all (· == '.') = false := by
          cases hd : stemPart.toList.all (· == '.') <;> simp_all
        have hNameEq := proof_fs_withName_updatesName path (stemPart ++ ext)
        simp only [defaultApi, Internal.mkApiM, hSufCall, assert] at hNameEq
        unfold Internal.suffix
        rw [hNameEq.1]
        dsimp only
        cases hExt : ext.toList with
        | nil => simp [hExt] at hHead
        | cons d extTail =>
          have hdEq : d = '.' := by simp [hExt] at hHead; exact hHead
          subst hdEq
          have hNoDotTail' : '.' ∉ extTail := by simp [hExt] at hNoDotTail; exact hNoDotTail
          have hExtTailNe : extTail ≠ [] := by
            intro hEmpty
            subst hEmpty
            simp [Internal.validSuffix, hExt] at hValidSuf
          have hNoDotRev : '.' ∉ extTail.reverse := by simpa using hNoDotTail'
          unfold Internal.splitNameSuffix
          have hRev : (stemPart ++ ext).toList.reverse = extTail.reverse ++ '.' :: stemPart.toList.reverse := by
            simp [String.toList_append, hExt, List.reverse_append]
          rw [hRev, splitRevAtDot_append_noDot extTail.reverse stemPart.toList.reverse hNoDotRev]
          have hRevPrefNe : stemPart.toList.reverse.isEmpty = false := by
            cases h : stemPart.toList <;> simp_all
          have hRevSufNe : extTail.reverse.isEmpty = false := by
            cases h : extTail <;> simp_all
          have hRevAllDots : stemPart.toList.reverse.all (· == '.') = false := by
            simpa [List.all_reverse] using hNotAllDots
          simp only [hRevPrefNe, hRevSufNe, hRevAllDots, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            List.reverse_reverse]
          have hExtEq : ext = String.ofList ('.' :: extTail) := by
            rw [← hExt, String.ofList_toList]
          have hCatEq : "." ++ String.ofList extTail = String.ofList ('.' :: extTail) := by
            rw [← String.ofList_toList (s := "." ++ String.ofList extTail)]
            simp [String.toList_append, show ".".toList = ['.'] from rfl]
          rw [hExtEq, hCatEq]

/-- Non-vacuity `CanReach` witness for `test_fs_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_fs_mapRawError_returnsNonEmptyMessage :
    CanReach (test_fs_mapRawError_returnsNonEmptyMessage defaultApi) :=
  ⟨.userError "", proof_fs_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Non-vacuity `CanReach` witness for `test_fs_normPath_idempotent`. -/
theorem reach_fs_normPath_idempotent :
    CanReach (test_fs_normPath_idempotent defaultApi) :=
  ⟨"/a/b/../c", proof_fs_normPath_idempotent "/a/b/../c"⟩

/-- Non-vacuity `CanReach` witness for `test_fs_normPath_neverEmpty`. -/
theorem reach_fs_normPath_neverEmpty :
    CanReach (test_fs_normPath_neverEmpty defaultApi) :=
  ⟨"", proof_fs_normPath_neverEmpty ""⟩

/-- Non-vacuity `CanReach` witness for `test_fs_join_absOverridesBase`. -/
theorem reach_fs_join_absOverridesBase :
    CanReach (test_fs_join_absOverridesBase defaultApi) :=
  ⟨"/a", "/b", rfl, proof_fs_join_absOverridesBase "/a" "/b" rfl⟩

/-- Non-vacuity `CanReach` witness for `test_fs_withName_updatesName`. -/
theorem reach_fs_withName_updatesName :
    CanReach (test_fs_withName_updatesName defaultApi) := by
  refine ⟨"a/b.txt", "c.lean", ?_⟩
  have h := proof_fs_withName_updatesName "a/b.txt" "c.lean"
  have hw : Internal.withName "a/b.txt" "c.lean" = .ok "a/c.lean" := rfl
  simp [defaultApi, Internal.mkApiM, hw, assert] at h ⊢
  exact h

/-- Non-vacuity `CanReach` witness for `test_fs_withSuffix_updatesSuffix`. -/
theorem reach_fs_withSuffix_updatesSuffix :
    CanReach (test_fs_withSuffix_updatesSuffix defaultApi) := by
  refine ⟨"a/b.txt", ".lean", by decide, by decide, ?_⟩
  have h := proof_fs_withSuffix_updatesSuffix "a/b.txt" ".lean" (by decide) (by decide)
  have hs : Internal.withSuffix "a/b.txt" ".lean" = .ok "a/b.lean" := rfl
  simp [defaultApi, Internal.mkApiM, hs, assert] at h ⊢
  exact h

private theorem splitCharList_dot_concat (bs suf : List Char) (hno : '.' ∉ bs) :
    Internal.splitCharList '.' (bs ++ '.' :: suf) = bs :: Internal.splitCharList '.' suf := by
  induction bs with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hc : c ≠ '.' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [Internal.splitCharList, hc, ih']

/-- Proof of `test_fs_suffixes_doubleDot` for `defaultApi`. -/
theorem proof_fs_suffixes_doubleDot :
    AllPass (test_fs_suffixes_doubleDot defaultApi) := by
  intro base hNe hNoDot hNoSlash
  simp only [defaultApi, Internal.mkApiM, assert]
  refine ⟨?_, trivial⟩
  cases hBase : base.toList with
  | nil => exact absurd hBase hNe
  | cons c rest =>
    have hcDot : c ≠ '.' := fun h => hNoDot (by simp [hBase, h])
    have hBaseNoDot : '.' ∉ base.toList := hNoDot
    have hBaseNoSlash : '/' ∉ base.toList := hNoSlash
    have hFullNoSlash : '/' ∉ (base ++ "..ext").toList := by
      simp [String.toList_append, hBaseNoSlash, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
    have hFullNotEmpty : (!(base.toList ++ "..ext".toList).isEmpty) = true := by
      simp [hBase]
    have hFullNotDot : ((base.toList ++ "..ext".toList) != ['.']) = true := by
      refine bne_iff_ne.mpr fun heq => ?_
      have hLen := congrArg List.length heq
      simp [show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide] at hLen
    have hName : Internal.name (base ++ "..ext") = some (base ++ "..ext") := by
      unfold Internal.name Internal.splitParentName Internal.cleanCharSegments
      dsimp only
      rw [splitCharList_of_no_sep '/' (base ++ "..ext").toList hFullNoSlash]
      rw [String.toList_append]
      simp [hFullNotEmpty, hFullNotDot, Internal.splitLastAux]
    unfold Internal.suffixes
    rw [hName]
    dsimp only
    have hRev : (base ++ "..ext").toList.reverse =
        ['t', 'x', 'e', '.', '.'] ++ base.toList.reverse := by
      simp [String.toList_append, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
    rw [hRev]
    have hDrop : (base ++ "..ext").toList.dropWhile (· == '.') = base.toList ++ ['.', '.', 'e', 'x', 't'] := by
      have hList : (base ++ "..ext").toList = c :: (rest ++ ['.', '.', 'e', 'x', 't']) := by
        simp [String.toList_append, hBase, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
      rw [hList]
      simp [hcDot, hBase]
    rw [hDrop]
    have hDotEq : base.toList ++ ['.', '.', 'e', 'x', 't'] = base.toList ++ '.' :: ['.', 'e', 'x', 't'] := rfl
    rw [hDotEq, splitCharList_dot_concat base.toList ['.', 'e', 'x', 't'] hBaseNoDot]
    simp [Internal.splitCharList, show String.ofList [] = "" from rfl,
      show String.ofList ['e', 'x', 't'] = "ext" from rfl]

/-- Non-vacuity `CanReach` witness for `test_fs_suffixes_doubleDot`. -/
theorem reach_fs_suffixes_doubleDot :
    CanReach (test_fs_suffixes_doubleDot defaultApi) :=
  ⟨"a", by decide, by decide, by decide,
    proof_fs_suffixes_doubleDot "a" (by decide) (by decide) (by decide)⟩

/-- Node stored in the pure in-memory VFS model. -/
inductive VfsNode where
  /-- Regular file storing bytes and POSIX permission bits. -/
  | file (data : ByteArray) (mode : Nat)
  /-- Directory storing POSIX permission bits. -/
  | dir (mode : Nat)
  /-- Symbolic link storing target path and mode bits. -/
  | symlink (target : String) (mode : Nat)
  deriving BEq, DecidableEq

/-- Structural directory tree backing `VfsState` (makes orphan paths unrepresentable). -/
inductive VfsTree where
  /-- Regular file storing bytes and POSIX permission bits. -/
  | file (data : ByteArray) (mode : Nat)
  /-- Directory storing POSIX permission bits and child lookup. -/
  | dir (mode : Nat) (children : String → Option VfsTree)
  /-- Symbolic link storing target path and mode bits. -/
  | symlink (target : String) (mode : Nat)

private def vfsTreeTopNode : VfsTree → VfsNode
  | .file bs m => .file bs m
  | .dir m _ => .dir m
  | .symlink t m => .symlink t m

private def vfsEmptyDir (mode : Nat) : VfsTree :=
  .dir mode (fun _ => none)

private def vfsTreeGet (t : VfsTree) : List String → Option VfsTree
  | [] => some t
  | seg :: rest =>
    match t with
    | .dir _ ch =>
      match ch seg with
      | none => none
      | some sub => vfsTreeGet sub rest
    | _ => none

private def vfsTreeSet (t : VfsTree) (segs : List String) (v : Option VfsTree) : VfsTree :=
  match segs with
  | [] => v.getD t
  | [last] =>
    match t with
    | .dir m ch => .dir m (fun s => if s == last then v else ch s)
    | _ => t
  | seg :: rest =>
    match t with
    | .dir m ch =>
      .dir m (fun s =>
        if s == seg then
          match ch seg with
          | some sub => some (vfsTreeSet sub rest v)
          | none => none
        else ch s)
    | _ => t

/-- Pure in-memory VFS state used to discharge `SpecTests` over `StateM VfsState`. -/
structure VfsState where
  /-- Root directory tree of the VFS. -/
  tree : VfsTree
  /-- Canonical paths tracked for directory listing. -/
  keys : List String
  /-- Current working directory (normalized absolute path). -/
  cwd : String
  /-- Monotonic counter for temporary sibling filenames. -/
  nonce : Nat

private def vfsAbsNorm (cwd path : String) : String :=
  Internal.normPath (if Internal.isAbsolute path then path else Internal.join cwd path)

private def vfsSplitSegs (absNorm : String) : List String :=
  match absNorm.toList with
  | '/' :: rest =>
    (Internal.splitCharList '/' rest).filterMap fun cs =>
      if cs.isEmpty then none else some (String.ofList cs)
  | _ => []

private def isCanonPath (k : String) : Bool :=
  Internal.isAbsolute k && (Internal.normPath k == k)

private def vfsTreeNodes (t : VfsTree) (k : String) : Option VfsNode :=
  if isCanonPath k then (vfsTreeGet t (vfsSplitSegs k)).map vfsTreeTopNode else none

/-- Canonical path lookup view derived from `VfsState.tree`. -/
def VfsState.nodes (st : VfsState) : String → Option VfsNode :=
  vfsTreeNodes st.tree

private def vfsChildPath (cur seg : String) : String :=
  if cur == "/" then "/" ++ seg else cur ++ "/" ++ seg

private def vfsResolveSegs (nodes : String → Option VfsNode) (cur : String)
    (segs : List String) (followLast : Bool) : Nat → Except FsError (String × VfsNode)
  | 0 => .error { kind := .ioError, path := some cur, message := "too many levels of symbolic links" }
  | fuel + 1 =>
    match segs with
    | [] =>
      match nodes cur with
      | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
      | some (.symlink target m) =>
        if followLast then
          let par := (Internal.parent cur).getD "/"
          let nextAbs := Internal.normPath (if Internal.isAbsolute target then target else Internal.join par target)
          vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs) true fuel
        else
          .ok (cur, .symlink target m)
      | some node => .ok (cur, node)
    | seg :: rest =>
      match nodes cur with
      | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
      | some (.dir mode) =>
        if (mode / 64) % 2 == 0 then
          .error { kind := .permissionDenied, path := some cur, message := s!"permission denied: {cur}" }
        else
          vfsResolveSegs nodes (vfsChildPath cur seg) rest followLast fuel
      | some (.symlink target _) =>
        let par := (Internal.parent cur).getD "/"
        let nextAbs := Internal.normPath (if Internal.isAbsolute target then target else Internal.join par target)
        vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs ++ seg :: rest) followLast fuel
      | some (.file _ _) =>
        .error { kind := .notADirectory, path := some cur, message := s!"not a directory: {cur}" }

private def vfsToStat : VfsNode → FileStat
  | .file bs m =>
    { kind := .file, byteSize := bs.size, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .dir m =>
    { kind := .dir, byteSize := 0, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .symlink _ m =>
    { kind := .symlink, byteSize := 0, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }

private def vfsStatPure (st : VfsState) (follow : Bool) (path : String) : Except FsError FileStat :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) follow 1024 with
  | .error e => .error e
  | .ok (_, node) => .ok (vfsToStat node)

private def vfsRealPathPure (st : VfsState) (path : String) : Except FsError String :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) true 1024 with
  | .error e => .error e
  | .ok (canon, _) => .ok canon

private def vfsCreateDirPure (st : VfsState) (path : String) : Except FsError Unit × VfsState :=
  let abs := vfsAbsNorm st.cwd path
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
  | .ok _ => (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
  | .error e =>
    if e.kind != .notFound then
      (.error e, st)
    else
      match Internal.splitLastAux (vfsSplitSegs abs) [] with
      | none =>
        (.error { kind := .notFound, path := some path, message := s!"invalid path: {path}" }, st)
      | some (parSegs, lastSeg) =>
        match vfsResolveSegs st.nodes "/" parSegs true 512 with
        | .error pe => (.error pe, st)
        | .ok (parCanon, .dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
          else
            let newKey := vfsChildPath parCanon lastSeg
            match st.nodes newKey with
            | some _ => (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
            | none =>
              (.ok (), { st with
                tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (vfsEmptyDir 0o755))
                keys := newKey :: st.keys })
        | .ok (parCanon, _) =>
          (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

private def vfsReadDirPure (st : VfsState) (path : String) : Except FsError (Array String) :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) true 1024 with
  | .error e => .error e
  | .ok (canon, .dir mode) =>
    if (mode / 256) % 2 == 0 then
      .error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }
    else
      let prefixChars := (if canon == "/" then "/" else canon ++ "/").toList
      let children := st.keys.eraseDups.filterMap fun k =>
        if (st.nodes k).isSome then
          if k != canon && prefixChars.isPrefixOf k.toList then
            let restChars := k.toList.drop prefixChars.length
            if !restChars.isEmpty && !('/' ∈ restChars) then some (String.ofList restChars) else none
          else none
        else none
      .ok children.toArray
  | .ok (_, _) => .error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }

private def vfsWriteBytesPure (st : VfsState) (path : String) (bs : ByteArray) :
    Except FsError Unit × VfsState :=
  let abs := vfsAbsNorm st.cwd path
  match Internal.splitLastAux (vfsSplitSegs abs) [] with
  | none => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
  | some (parSegs, lastSeg) =>
    match vfsResolveSegs st.nodes "/" parSegs true 512 with
    | .error pe => (.error pe, st)
    | .ok (parCanon, .dir parMode) =>
      if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
      else
        let targetKey := vfsChildPath parCanon lastSeg
        match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
        | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
        | _ =>
          let finalKey := match st.nodes targetKey with
            | some (.symlink tgt _) => vfsAbsNorm parCanon tgt
            | _ => targetKey
          (.ok (), { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs finalKey) (some (.file bs 0o644))
            keys := finalKey :: st.keys })
    | .ok (parCanon, _) =>
      (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

/-- Pure single-step `RawFsOpsM (StateM VfsState)` backed by `VfsState`. -/
def vfsOps : RawFsOpsM (StateM VfsState) :=
  { mapRawError := Fs.Raw.Internal.mapRawError
    stat := fun follow path st => (vfsStatPure st follow path, st)
    readDir := fun path st => (vfsReadDirPure st path, st)
    createDir := fun path st => vfsCreateDirPure st path
    removeDir := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (canon, .dir _) =>
        if canon == "/" then (.error { kind := .permissionDenied, path := some path, message := "cannot remove root" }, st)
        else (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) none })
      | .ok (_, _) => (.error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }, st)
    unlinkFile := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | .ok (canon, _) => (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) none })
    readBytes := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .error e => (.error e, st)
      | .ok (_, .file bs _) => (.ok bs, st)
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | .ok (_, _) => (.error { kind := .notFound, path := some path, message := s!"not found: {path}" }, st)
    writeBytes := fun path bs st => vfsWriteBytesPure st path bs
    appendText := fun path s st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .ok (canon, .file bs m) =>
        (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) (some (.file (bs ++ s.toUTF8) m)) })
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | _ => vfsWriteBytesPure st path s.toUTF8
    rename := fun src dst st =>
      let srcAbs := vfsAbsNorm st.cwd src
      let dstAbs := vfsAbsNorm st.cwd dst
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs srcAbs) false 1024 with
      | .error e => (.error e, st)
      | .ok (srcCanon, _) =>
        let moved := vfsTreeGet st.tree (vfsSplitSegs srcCanon)
        let tr₁ := vfsTreeSet st.tree (vfsSplitSegs srcCanon) none
        (.ok (), { st with
          tree := vfsTreeSet tr₁ (vfsSplitSegs dstAbs) moved
          keys := dstAbs :: st.keys })
    chmod := fun path mode st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .error e => (.error e, st)
      | .ok (canon, _) =>
        let updated := match vfsTreeGet st.tree (vfsSplitSegs canon) with
          | some (.file bs _) => some (.file bs mode)
          | some (.dir _ ch) => some (.dir mode ch)
          | some (.symlink t _) => some (.symlink t mode)
          | none => none
        (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) updated })
    symlink := fun target linkPath st =>
      let abs := vfsAbsNorm st.cwd linkPath
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .ok _ => (.error { kind := .alreadyExists, path := some linkPath, message := s!"already exists: {linkPath}" }, st)
      | .error e =>
        if e.kind != .notFound then (.error e, st)
        else (.ok (), { st with
          tree := vfsTreeSet st.tree (vfsSplitSegs abs) (some (.symlink target 0o777))
          keys := abs :: st.keys })
    readLink := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (_, .symlink target _) => (.ok target, st)
      | .ok (_, _) => (.error { kind := .invalidInput, path := some path, message := s!"not a symlink: {path}" }, st)
    realPath := fun path st => (vfsRealPathPure st path, st)
    cwd := fun st => (.ok st.cwd, st)
    monotonicNonce := fun st => (st.nonce, { st with nonce := st.nonce + 1 }) }

/-- Generic `FsApiM (StateM VfsState)` built directly from `Internal.mkApiM vfsOps`. -/
def vfsApi : FsApiM (StateM VfsState) :=
  Internal.mkApiM vfsOps

private theorem vfsResolveSegs_insert_fresh (nodes : String → Option VfsNode) (p : String) (v : VfsNode)
    (hp : nodes p = none) :
    ∀ fuel cur segs follow res,
      vfsResolveSegs nodes cur segs follow fuel = .ok res →
      vfsResolveSegs (fun k => if k == p then some v else nodes k) cur segs follow fuel = .ok res := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs follow res hOk
    simp only [vfsResolveSegs] at hOk ⊢
    cases segs with
    | nil =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        have hNe : cur ≠ p := fun heq => by subst heq; simp [hp] at hNode
        have hBeq : (cur == p) = false := beq_false_of_ne hNe
        simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
        simp only [hNode] at hOk
        cases nd with
        | symlink target m =>
          cases follow
          · exact hOk
          · exact ih "/" _ true res hOk
        | file _ _ => exact hOk
        | dir _ => exact hOk
    | cons seg rest =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        have hNe : cur ≠ p := fun heq => by subst heq; simp [hp] at hNode
        have hBeq : (cur == p) = false := beq_false_of_ne hNe
        simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
        simp only [hNode] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir mode =>
          by_cases hExec : ((mode / 64) % 2 == 0) = true
          · simp [hExec] at hOk
          · have hExecFalse : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hExec
            simp only [hExecFalse, Bool.false_eq_true, ↓reduceIte]
            simp only [hExecFalse, Bool.false_eq_true, ↓reduceIte] at hOk
            exact ih (vfsChildPath cur seg) rest follow res hOk
        | symlink target _ =>
          exact ih "/" _ follow res hOk

private theorem vfsResolveSegs_fuel_mono (nodes : String → Option VfsNode) :
    ∀ fuel₁ fuel₂ cur segs follow res,
      fuel₁ ≤ fuel₂ →
      vfsResolveSegs nodes cur segs follow fuel₁ = .ok res →
      vfsResolveSegs nodes cur segs follow fuel₂ = .ok res := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro _ _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ f1 ih =>
    intro fuel₂ cur segs follow res hle hOk
    cases fuel₂ with
    | zero => omega
    | succ f2 =>
      have hle' : f1 ≤ f2 := Nat.le_of_succ_le_succ hle
      simp only [vfsResolveSegs] at hOk ⊢
      cases segs with
      | nil =>
        cases hNode : nodes cur with
        | none => simp [hNode] at hOk
        | some nd =>
          simp only [hNode] at hOk ⊢
          cases nd with
          | symlink target m =>
            cases follow
            · exact hOk
            · exact ih f2 "/" _ true res hle' hOk
          | file _ _ => exact hOk
          | dir _ => exact hOk
      | cons seg rest =>
        cases hNode : nodes cur with
        | none => simp [hNode] at hOk
        | some nd =>
          simp only [hNode] at hOk ⊢
          cases nd with
          | file _ _ => simp at hOk
          | dir mode =>
            by_cases hExec : ((mode / 64) % 2 == 0) = true
            · simp [hExec] at hOk
            · have hExecFalse : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hExec
              simp only [hExecFalse, Bool.false_eq_true, ↓reduceIte] at hOk ⊢
              exact ih f2 (vfsChildPath cur seg) rest follow res hle' hOk
          | symlink target _ =>
            exact ih f2 "/" _ follow res hle' hOk

private theorem splitLastAux_spec {α : Type} (xs acc : List α) (init : List α) (last : α) :
    Internal.splitLastAux xs acc = some (init, last) →
    acc.reverse ++ xs = init ++ [last] := by
  induction xs generalizing acc with
  | nil => simp [Internal.splitLastAux]
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [Internal.splitLastAux, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      simp
    | cons y ys =>
      intro h
      have ih' := ih (x :: acc) h
      simpa using ih'

private theorem vfsResolveSegs_dir_child (nodes : String → Option VfsNode)
    (lastSeg parCanon : String) (parMode : Nat) (hExec : ((parMode / 64) % 2 == 0) = false)
    (hChild : nodes (vfsChildPath parCanon lastSeg) = some (.dir 0o755)) :
    ∀ fuel cur parSegs,
      vfsResolveSegs nodes cur parSegs true fuel = .ok (parCanon, .dir parMode) →
      vfsResolveSegs nodes cur (parSegs ++ [lastSeg]) true (fuel + 1) =
        .ok (vfsChildPath parCanon lastSeg, .dir 0o755) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; simp [vfsResolveSegs] at h
  | succ f ih =>
    intro cur parSegs hOk
    simp only [vfsResolveSegs] at hOk
    cases parSegs with
    | nil =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        simp only [hNode] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir m =>
          simp only [Prod.mk.injEq, Except.ok.injEq, VfsNode.dir.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          simp only [List.nil_append, vfsResolveSegs, hNode, hExec, Bool.false_eq_true, ↓reduceIte, hChild]
        | symlink target m =>
          simp only [List.nil_append, vfsResolveSegs, hNode]
          exact ih "/" (vfsSplitSegs (Internal.normPath
            (if Internal.isAbsolute target then target else Internal.join ((Internal.parent cur).getD "/") target))) hOk
    | cons seg rest =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        simp only [hNode] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir m =>
          by_cases he : ((m / 64) % 2 == 0) = true
          · simp [he] at hOk
          · have hef : ((m / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr he
            simp only [hef, Bool.false_eq_true, ↓reduceIte] at hOk
            simp only [List.cons_append, vfsResolveSegs, hNode, hef, Bool.false_eq_true, ↓reduceIte]
            exact ih (vfsChildPath cur seg) rest hOk
        | symlink target m =>
          simp only [List.cons_append, vfsResolveSegs, hNode]
          have hAssoc : vfsSplitSegs (Internal.normPath
              (if Internal.isAbsolute target then target else Internal.join ((Internal.parent cur).getD "/") target)) ++
              seg :: (rest ++ [lastSeg]) =
            (vfsSplitSegs (Internal.normPath
              (if Internal.isAbsolute target then target else Internal.join ((Internal.parent cur).getD "/") target)) ++
              seg :: rest) ++ [lastSeg] := by
            simp [List.append_assoc]
          rw [hAssoc]
          exact ih "/" _ hOk

private theorem vfsSplitSegs_joinSlashChars_valid (parts : List (List Char))
    (hParts : ∀ s ∈ parts, !s.isEmpty ∧ '/' ∉ s) :
    vfsSplitSegs (String.ofList ('/' :: Internal.joinSlashChars parts)) = parts.map String.ofList := by
  unfold vfsSplitSegs
  simp only [String.toList_ofList]
  cases parts with
  | nil => simp [Internal.joinSlashChars, Internal.splitCharList]
  | cons hd tl =>
    have hSplit := splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hParts s hs).2)
    rw [hSplit]
    simp only [List.filterMap_cons, List.map_cons]
    have hMap : ∀ xs : List (List Char), (∀ s ∈ xs, !s.isEmpty) →
        List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) xs = xs.map String.ofList := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons x xt ihx =>
        rcases x with _ | ⟨c, cs⟩
        · have := hxs [] (by simp); simp at this
        · have hTail : List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) xt =
              xt.map String.ofList := ihx (fun y hy => hxs y (by simp [hy]))
          simpa using congrArg (String.ofList (c :: cs) :: ·) hTail
    rcases hd with _ | ⟨hc, hcs⟩
    · have := hParts [] (by simp); simp at this
    · have hTl : List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) tl =
          tl.map String.ofList := hMap tl (fun s hs => (hParts s (by simp [hs])).1)
      simpa using congrArg (String.ofList (hc :: hcs) :: ·) hTl

private theorem vfsSplitSegs_normPath_valid (p : String) :
    ∀ s ∈ vfsSplitSegs (Internal.normPath p), Internal.validFileName s = true := by
  by_cases hAbs : Internal.isAbsChars p.toList = true
  · have hElem := collapseChars_elems_valid true (Internal.splitCharList '/' p.toList) []
      (fun _ h => by simp at h) (splitCharList_no_sep '/' p.toList)
    have hStack := collapseChars_validStack true (Internal.splitCharList '/' p.toList) []
      trivial (splitCharList_no_sep '/' p.toList)
    have hOrd : ValidOrder true (Internal.collapseChars true (Internal.splitCharList '/' p.toList) []) := by
      simpa using validStack_to_validOrder true _ hStack
    have hSp : vfsSplitSegs (Internal.normPath p) =
        (Internal.collapseChars true (Internal.splitCharList '/' p.toList) []).map String.ofList := by
      simp only [Internal.normPath, hAbs, ↓reduceIte]
      exact vfsSplitSegs_joinSlashChars_valid _ (fun s hs => ⟨(hElem s hs).1, (hElem s hs).2.2⟩)
    rw [hSp]
    intro seg hMem
    simp only [List.mem_map] at hMem
    rcases hMem with ⟨cs, hCsMem, rfl⟩
    have he := hElem cs hCsMem
    have hnd := hOrd cs hCsMem
    have hNeNil : cs ≠ [] := by cases cs <;> simp_all
    have hNeDot : cs ≠ ['.'] := by
      have := he.2.1
      cases hd : (cs == ['.']) <;> simp_all [beq_iff_eq]
    have hSlash : '/' ∉ cs := he.2.2
    have hEmpF : (String.ofList cs).toList.isEmpty = false := by
      rcases cs with _ | ⟨c, cs'⟩
      · exact absurd rfl hNeNil
      · simp
    have hBneDot : (String.ofList cs != ".") = true := by
      apply bne_iff_ne.mpr
      intro hEq
      apply hNeDot
      simpa using congrArg String.toList hEq
    have hBneDotDot : (String.ofList cs != "..") = true := by
      apply bne_iff_ne.mpr
      intro hEq
      apply hnd
      simpa [show "..".toList = ['.', '.'] by decide] using congrArg String.toList hEq
    simp only [Internal.validFileName, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨hEmpF, by simp [hSlash]⟩, ?_⟩, ?_⟩
    · exact bne_iff_ne.mpr (by simpa using hNeDot)
    · exact bne_iff_ne.mpr (by simpa [show "..".toList = ['.', '.'] by decide] using hnd)
  · have hNotAbs : Internal.isAbsChars p.toList = false := Bool.eq_false_iff.mpr hAbs
    have hElem := collapseChars_elems_valid false (Internal.splitCharList '/' p.toList) []
      (fun _ h => by simp at h) (splitCharList_no_sep '/' p.toList)
    simp only [Internal.normPath, hNotAbs, Bool.false_eq_true, ↓reduceIte]
    cases hParts : Internal.collapseChars false (Internal.splitCharList '/' p.toList) [] with
    | nil =>
      intro s hs
      simp only [List.isEmpty_nil, ↓reduceIte] at hs
      have hDot : vfsSplitSegs "." = [] := by decide
      rw [hDot] at hs
      simp at hs
    | cons hd tl =>
      have hHd := hElem hd (by rw [hParts]; simp)
      have hHdNe : hd ≠ [] := by cases hd <;> simp_all
      have hNA : Internal.isAbsChars (Internal.joinSlashChars (hd :: tl)) = false :=
        isAbsChars_joinSlashChars_head hHdNe hHd.2.2
      intro s hs
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hs
      unfold vfsSplitSegs at hs
      cases hList : (String.ofList (Internal.joinSlashChars (hd :: tl))).toList with
      | nil => simp [hList] at hs
      | cons c cs =>
        by_cases hc : c = '/'
        · subst hc
          have : Internal.isAbsChars (Internal.joinSlashChars (hd :: tl)) = true := by
            simp only [String.toList_ofList] at hList
            simp [hList, Internal.isAbsChars]
          simp [hNA] at this
        · simp [hList, hc] at hs

private theorem isCanonPath_normPath_parts (k : String) (hk : isCanonPath k = true) :
    let parts := (vfsSplitSegs k).map String.toList
    k = String.ofList ('/' :: Internal.joinSlashChars parts) ∧
    (∀ s ∈ parts, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s ∧ s ≠ ['.', '.']) := by
  simp only [isCanonPath, Bool.and_eq_true, beq_iff_eq] at hk
  rcases hk with ⟨hAbs, hNorm⟩
  have hAbsChars : Internal.isAbsChars k.toList = true := hAbs
  have hElem := collapseChars_elems_valid true (Internal.splitCharList '/' k.toList) []
    (fun _ h => by simp at h) (splitCharList_no_sep '/' k.toList)
  have hStack := collapseChars_validStack true (Internal.splitCharList '/' k.toList) []
    trivial (splitCharList_no_sep '/' k.toList)
  have hOrd : ValidOrder true (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []) := by
    simpa using validStack_to_validOrder true _ hStack
  have hKEq : k = String.ofList ('/' :: Internal.joinSlashChars
      (Internal.collapseChars true (Internal.splitCharList '/' k.toList) [])) := by
    calc k = Internal.normPath k := hNorm.symm
      _ = String.ofList ('/' :: Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' k.toList) [])) := by
        simp only [Internal.normPath, hAbsChars, ↓reduceIte]
  have hSp : vfsSplitSegs k =
      (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []).map String.ofList := by
    calc vfsSplitSegs k
        = vfsSplitSegs (String.ofList ('/' :: Internal.joinSlashChars
            (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []))) := congrArg vfsSplitSegs hKEq
      _ = (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []).map String.ofList :=
        vfsSplitSegs_joinSlashChars_valid _ (fun s hs => ⟨(hElem s hs).1, (hElem s hs).2.2⟩)
  have hPartsEq : (vfsSplitSegs k).map String.toList =
      Internal.collapseChars true (Internal.splitCharList '/' k.toList) [] := by
    rw [hSp, List.map_map]
    simp [Function.comp_def]
  refine ⟨?_, ?_⟩
  · rw [hPartsEq]; exact hKEq
  · intro s hs
    rw [hPartsEq] at hs
    exact ⟨(hElem s hs).1, (hElem s hs).2.1, (hElem s hs).2.2, hOrd s hs⟩

private theorem isCanonPath_of_parts (parts : List (List Char))
    (hParts : ∀ s ∈ parts, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s ∧ s ≠ ['.', '.']) :
    isCanonPath (String.ofList ('/' :: Internal.joinSlashChars parts)) = true := by
  simp only [isCanonPath, Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [Internal.isAbsolute, Internal.isAbsChars], ?_⟩
  simp only [Internal.normPath, String.toList_ofList, Internal.isAbsChars, ↓reduceIte]
  have hSplitNil : Internal.splitCharList '/' ('/' :: Internal.joinSlashChars parts) =
      [] :: Internal.splitCharList '/' (Internal.joinSlashChars parts) := by
    simp [Internal.splitCharList]
  have hStepNil : Internal.collapseChars true ([] :: Internal.splitCharList '/' (Internal.joinSlashChars parts)) [] =
      Internal.collapseChars true (Internal.splitCharList '/' (Internal.joinSlashChars parts)) [] := by
    simp [Internal.collapseChars]
  rw [hSplitNil, hStepNil]
  cases parts with
  | nil => simp [Internal.joinSlashChars, Internal.splitCharList, Internal.collapseChars]
  | cons hd tl =>
    have hSp := splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hParts s hs).2.2.1)
    have hNoop := collapseChars_noop true (hd :: tl) []
      (fun s hs => ⟨(hParts s hs).1, (hParts s hs).2.1⟩)
      (Or.inl (fun s hs => (hParts s hs).2.2.2))
    rw [hSp, hNoop]
    simp

private theorem validFileName_charList (seg : String) (h : Internal.validFileName seg = true) :
    !seg.toList.isEmpty ∧ seg.toList != ['.'] ∧ '/' ∉ seg.toList ∧ seg.toList ≠ ['.', '.'] := by
  simp only [Internal.validFileName, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    decide_eq_false_iff_not] at h
  rcases h with ⟨⟨⟨hEmp, hSlash⟩, hDot⟩, hDotDot⟩
  have hNeNil : seg.toList ≠ [] := by
    intro hn
    rw [hn] at hEmp
    simp at hEmp
  have hNotEmp : (!seg.toList.isEmpty) = true := by cases htl : seg.toList <;> simp_all
  have hNotDotL : (seg.toList != ['.']) = true := by
    apply bne_iff_ne.mpr
    intro heq
    apply hDot
    rw [← String.ofList_toList (s := seg), heq]
    rfl
  have hNotDD : seg.toList ≠ ['.', '.'] := by
    intro heq
    apply hDotDot
    rw [← String.ofList_toList (s := seg), heq]
    rfl
  exact ⟨hNotEmp, hNotDotL, hSlash, hNotDD⟩

private theorem joinSlashChars_append_singleton (xs : List (List Char)) (hxs : xs ≠ []) (last : List Char) :
    Internal.joinSlashChars (xs ++ [last]) = Internal.joinSlashChars xs ++ '/' :: last := by
  induction xs with
  | nil => exact absurd rfl hxs
  | cons hd tl ih =>
    cases tl with
    | nil => simp [Internal.joinSlashChars]
    | cons b bs =>
      have hSub : b :: (bs ++ [last]) = (b :: bs) ++ [last] := rfl
      simp only [List.cons_append, Internal.joinSlashChars]
      rw [hSub, ih (by simp)]
      simp [List.append_assoc]

private theorem vfsChildPath_valid (cur seg : String)
    (hCur : isCanonPath cur = true) (hSeg : Internal.validFileName seg = true) :
    isCanonPath (vfsChildPath cur seg) = true ∧
    vfsSplitSegs (vfsChildPath cur seg) = vfsSplitSegs cur ++ [seg] := by
  obtain ⟨hCurEq, hParts⟩ := isCanonPath_normPath_parts cur hCur
  have hSegL := validFileName_charList seg hSeg
  have hNewParts : ∀ s ∈ (vfsSplitSegs cur).map String.toList ++ [seg.toList],
      !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s ∧ s ≠ ['.', '.'] := by
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hParts s hs
    · exact hSegL
  have hChildEq : vfsChildPath cur seg =
      String.ofList ('/' :: Internal.joinSlashChars ((vfsSplitSegs cur).map String.toList ++ [seg.toList])) := by
    cases hSp : vfsSplitSegs cur with
    | nil =>
      have hCurRoot : cur = "/" := by
        rw [hCurEq, hSp]
        rfl
      simp only [vfsChildPath, hCurRoot, beq_self_eq_true, ↓reduceIte, Internal.joinSlashChars, List.nil_append, List.map_nil]
      apply String.ext_iff.mpr
      simp [String.toList_append, show "/".toList = ['/'] by decide]
    | cons sh st =>
      have hCurNeRoot : cur ≠ "/" := by
        intro heq
        have : vfsSplitSegs cur = [] := by rw [heq]; decide
        simp [this] at hSp
      have hBeqF : (cur == "/") = false := beq_false_of_ne hCurNeRoot
      simp only [vfsChildPath, hBeqF, Bool.false_eq_true, ↓reduceIte]
      have hApp := joinSlashChars_append_singleton ((sh :: st).map String.toList) (by simp) seg.toList
      rw [hCurEq]
      simp only [hSp, List.map_cons] at hApp ⊢
      apply String.ext_iff.mpr
      simp only [String.toList_append, String.toList_ofList, show "/".toList = ['/'] by decide]
      rw [hApp]
      simp [List.append_assoc]
  refine ⟨?_, ?_⟩
  · rw [hChildEq]; exact isCanonPath_of_parts _ hNewParts
  · rw [hChildEq, vfsSplitSegs_joinSlashChars_valid _ (fun s hs => ⟨(hNewParts s hs).1, (hNewParts s hs).2.2.1⟩)]
    simp [List.map_append, List.map_map, Function.comp_def]

private theorem vfsResolveSegs_isCanon (nodes : String → Option VfsNode) :
    ∀ fuel cur segs follow res,
      isCanonPath cur = true →
      (∀ s ∈ segs, Internal.validFileName s = true) →
      vfsResolveSegs nodes cur segs follow fuel = .ok res →
      isCanonPath res.1 = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs follow res hCur hSegs hOk
    simp only [vfsResolveSegs] at hOk
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd =>
        simp only [hNd] at hOk
        cases nd with
        | file _ _ => simp only [Except.ok.injEq] at hOk; subst hOk; exact hCur
        | dir _ => simp only [Except.ok.injEq] at hOk; subst hOk; exact hCur
        | symlink target _ =>
          cases follow
          · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hOk; subst hOk; exact hCur
          · simp only [↓reduceIte] at hOk
            exact ih "/" _ true res (by decide) (vfsSplitSegs_normPath_valid _) hOk
    | cons seg rest =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd =>
        simp only [hNd] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir mode =>
          by_cases hm : ((mode / 64) % 2 == 0) = true
          · simp [hm] at hOk
          · have hmf : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hOk
            have hValidSeg := hSegs seg (by simp)
            exact ih (vfsChildPath cur seg) rest follow res
              (vfsChildPath_valid cur seg hCur hValidSeg).1
              (fun s hs => hSegs s (by simp [hs]))
              hOk
        | symlink target _ =>
          apply ih "/" _ follow res (by decide) _ hOk
          intro s hs
          simp only [List.mem_append] at hs
          rcases hs with hs | hs
          · exact vfsSplitSegs_normPath_valid _ s hs
          · exact hSegs s (by simp [hs])

private theorem vfsSplitSegs_inj_canon (k₁ k₂ : String)
    (h1 : isCanonPath k₁ = true) (h2 : isCanonPath k₂ = true)
    (hSp : vfsSplitSegs k₁ = vfsSplitSegs k₂) : k₁ = k₂ := by
  have hEq1 := (isCanonPath_normPath_parts k₁ h1).1
  have hEq2 := (isCanonPath_normPath_parts k₂ h2).1
  rw [hEq1, hEq2, hSp]

private theorem vfsTreeGet_set_emptyDir (m' : Nat) :
    ∀ (segs : List String) (lastSeg : String) (t : VfsTree) (q : List String),
      (∃ dm dch, vfsTreeGet t segs = some (.dir dm dch)) →
      vfsTreeGet t (segs ++ [lastSeg]) = none →
      (vfsTreeGet (vfsTreeSet t (segs ++ [lastSeg]) (some (vfsEmptyDir m'))) q).map vfsTreeTopNode =
        if q == (segs ++ [lastSeg]) then some (.dir m') else (vfsTreeGet t q).map vfsTreeTopNode := by
  intro segs
  induction segs with
  | nil =>
    intro lastSeg t q hDir hNone
    rcases hDir with ⟨dm, dch, hGet⟩
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir mode ch =>
      simp only [List.nil_append, vfsTreeSet]
      have hChNone : ch lastSeg = none := by
        cases hCl : ch lastSeg with
        | none => rfl
        | some sub => simp [vfsTreeGet, hCl] at hNone
      cases q with
      | nil => rfl
      | cons qh qt =>
        by_cases hEq : qh = lastSeg
        · subst hEq
          cases qt with
          | nil => simp [vfsTreeGet, vfsEmptyDir, vfsTreeTopNode]
          | cons rh rt =>
            simp only [vfsTreeGet, beq_self_eq_true, ↓reduceIte, vfsEmptyDir]
            simp [hChNone]
        · have hNe : (qh == lastSeg) = false := beq_false_of_ne hEq
          have hListNe : ((qh :: qt) == [lastSeg]) = false := by
            simp [hEq]
          simp [vfsTreeGet, hNe, hListNe]
  | cons seg rest ih =>
    intro lastSeg t q hDir hNone
    rcases hDir with ⟨dm, dch, hGet⟩
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir mode ch =>
      cases hCh : ch seg with
      | none => simp [vfsTreeGet, hCh] at hGet
      | some sub =>
        have hSubDir : ∃ dm dch, vfsTreeGet sub rest = some (.dir dm dch) := by
          refine ⟨dm, dch, ?_⟩
          simpa [vfsTreeGet, hCh] using hGet
        have hSubNone : vfsTreeGet sub (rest ++ [lastSeg]) = none := by
          simpa [vfsTreeGet, hCh] using hNone
        have hNonEmpty : rest ++ [lastSeg] ≠ [] := by simp
        cases hRest : rest ++ [lastSeg] with
        | nil => exact absurd hRest hNonEmpty
        | cons rhd rtl =>
          have hSetEq : vfsTreeSet (.dir mode ch) ((seg :: rest) ++ [lastSeg]) (some (vfsEmptyDir m')) =
              .dir mode (fun s => if s == seg then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (vfsEmptyDir m'))) else ch s) := by
            simp only [List.cons_append, vfsTreeSet, hRest, hCh]
          rw [hSetEq]
          cases q with
          | nil => rfl
          | cons qh qt =>
            by_cases hEq : qh = seg
            · subst hEq
              have hIh := ih lastSeg sub qt hSubDir hSubNone
              have hLhs :
                  (vfsTreeGet (.dir mode fun s =>
                    if s == qh then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (vfsEmptyDir m'))) else ch s) (qh :: qt)).map vfsTreeTopNode =
                  (vfsTreeGet (vfsTreeSet sub (rest ++ [lastSeg]) (some (vfsEmptyDir m'))) qt).map vfsTreeTopNode := by
                simp [vfsTreeGet]
              have hRhs :
                  (vfsTreeGet (.dir mode ch) (qh :: qt)).map vfsTreeTopNode =
                  (vfsTreeGet sub qt).map vfsTreeTopNode := by
                simp [vfsTreeGet, hCh]
              have hCond : ((qh :: qt) == ((qh :: rest) ++ [lastSeg])) = (qt == (rest ++ [lastSeg])) := by
                simp [List.cons_append]
              rw [hLhs, hRhs, hCond, hIh]
            · have hNe : (qh == seg) = false := beq_false_of_ne hEq
              unfold vfsTreeGet
              simp [hNe]

private theorem vfsTreeNodes_insert_dir (t : VfsTree) (parCanon lastSeg : String)
    (hParCanon : isCanonPath parCanon = true)
    (hLastValid : Internal.validFileName lastSeg = true)
    (hParDir : ∃ dm, vfsTreeNodes t parCanon = some (.dir dm))
    (hNewNone : vfsTreeNodes t (vfsChildPath parCanon lastSeg) = none) :
    vfsTreeNodes (vfsTreeSet t (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))) =
      fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else vfsTreeNodes t k := by
  have ⟨hChildCanon, hChildSp⟩ := vfsChildPath_valid parCanon lastSeg hParCanon hLastValid
  have hParTreeDir : ∃ dm dch, vfsTreeGet t (vfsSplitSegs parCanon) = some (.dir dm dch) := by
    rcases hParDir with ⟨dm, hPar⟩
    simp only [vfsTreeNodes, hParCanon, ↓reduceIte] at hPar
    cases hGet : vfsTreeGet t (vfsSplitSegs parCanon) with
    | none => simp [hGet] at hPar
    | some sub =>
      cases sub with
      | dir dm' dch => exact ⟨dm', dch, rfl⟩
      | file _ _ => simp [hGet, vfsTreeTopNode] at hPar
      | symlink _ _ => simp [hGet, vfsTreeTopNode] at hPar
  have hNewTreeNone : vfsTreeGet t (vfsSplitSegs parCanon ++ [lastSeg]) = none := by
    have hNn := hNewNone
    simp only [vfsTreeNodes, hChildCanon, ↓reduceIte, hChildSp] at hNn
    cases hGet : vfsTreeGet t (vfsSplitSegs parCanon ++ [lastSeg]) with
    | none => rfl
    | some _ => simp [hGet] at hNn
  funext k
  by_cases hKCanon : isCanonPath k = true
  · simp only [vfsTreeNodes, hKCanon, ↓reduceIte, hChildSp]
    rw [vfsTreeGet_set_emptyDir 0o755 (vfsSplitSegs parCanon) lastSeg t (vfsSplitSegs k) hParTreeDir hNewTreeNone]
    by_cases hEq : k = vfsChildPath parCanon lastSeg
    · subst hEq
      simp [hChildSp]
    · have hBeqF : (k == vfsChildPath parCanon lastSeg) = false := beq_false_of_ne hEq
      have hSpNe : vfsSplitSegs k ≠ vfsSplitSegs parCanon ++ [lastSeg] := by
        intro heq
        apply hEq
        exact vfsSplitSegs_inj_canon k (vfsChildPath parCanon lastSeg) hKCanon hChildCanon (by simpa [hChildSp] using heq)
      have hSpBeqF : (vfsSplitSegs k == vfsSplitSegs parCanon ++ [lastSeg]) = false := beq_false_of_ne hSpNe
      simp [hBeqF, hSpBeqF]
  · have hKCanonF : isCanonPath k = false := Bool.eq_false_iff.mpr hKCanon
    have hKNe : k ≠ vfsChildPath parCanon lastSeg := fun h => by subst h; simp [hChildCanon] at hKCanonF
    have hBeqF : (k == vfsChildPath parCanon lastSeg) = false := beq_false_of_ne hKNe
    simp [vfsTreeNodes, hKCanonF, hBeqF]

private theorem vfsTreeNodes_set_preserves_none (t : VfsTree) (segs : List String) (lastSeg : String) (m' : Nat)
    (hDir : ∃ dm dch, vfsTreeGet t segs = some (.dir dm dch))
    (hNone : vfsTreeGet t (segs ++ [lastSeg]) = none) (q : String) (hq : vfsTreeNodes t q = none)
    (hQCanon : isCanonPath q = true) (hNe : vfsSplitSegs q ≠ segs ++ [lastSeg]) :
    vfsTreeNodes (vfsTreeSet t (segs ++ [lastSeg]) (some (vfsEmptyDir m'))) q = none := by
  simp only [vfsTreeNodes, hQCanon, ↓reduceIte] at hq ⊢
  rw [vfsTreeGet_set_emptyDir m' segs lastSeg t (vfsSplitSegs q) hDir hNone]
  have hBeqF : (vfsSplitSegs q == segs ++ [lastSeg]) = false := beq_false_of_ne hNe
  simp [hBeqF, hq]

private theorem vfsTreeSet_emptyDir_nodes_root_child (t : VfsTree) (child : String)
    (hPar : ∃ dm, vfsTreeNodes t "/" = some (.dir dm))
    (hValid : Internal.validFileName child = true)
    (hNone : vfsTreeNodes t (vfsChildPath "/" child) = none) :
    vfsTreeNodes (vfsTreeSet t (vfsSplitSegs (vfsChildPath "/" child)) (some (vfsEmptyDir 0o755))) =
      fun k => if k == vfsChildPath "/" child then some (.dir 0o755) else vfsTreeNodes t k :=
  vfsTreeNodes_insert_dir t "/" child (by decide) hValid hPar hNone

private theorem vfsResolveSegs_ok_node (nodes : String → Option VfsNode) :
    ∀ fuel cur segs follow canon nd,
      vfsResolveSegs nodes cur segs follow fuel = .ok (canon, nd) →
      nodes canon = some nd := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs follow canon nd hOk
    simp only [vfsResolveSegs] at hOk
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd' =>
        simp only [hNd] at hOk
        cases nd' with
        | symlink _ _ =>
          cases follow
          · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hOk
            rcases hOk with ⟨rfl, rfl⟩
            exact hNd
          · simp only [↓reduceIte] at hOk
            exact ih "/" _ true canon nd hOk
        | file _ _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          exact hNd
        | dir _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          exact hNd
    | cons seg rest =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd' =>
        simp only [hNd] at hOk
        cases nd' with
        | file _ _ => simp at hOk
        | dir mode =>
          by_cases hm : ((mode / 64) % 2 == 0) = true
          · simp [hm] at hOk
          · have hmf : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hOk
            exact ih (vfsChildPath cur seg) rest follow canon nd hOk
        | symlink _ _ => exact ih "/" _ follow canon nd hOk

private theorem vfsCreateDir_sets_isDir (path : String) (s₀ s₁ : VfsState)
    (hCreate : (vfsOps.createDir path).run s₀ = (.ok (), s₁)) :
    ((vfsApi.isDir path).run s₁).1 = .ok true := by
  dsimp only [vfsOps, vfsCreateDirPure, StateT.run] at hCreate
  cases hPre : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p =>
    simp only [hPre] at hCreate
    cases (congrArg Prod.fst hCreate)
  | error e =>
    simp only [hPre] at hCreate
    by_cases hNf : (e.kind != .notFound) = true
    · simp only [hNf, ↓reduceIte] at hCreate
      cases (congrArg Prod.fst hCreate)
    · have hNfFalse : (e.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
      simp only [hNfFalse, Bool.false_eq_true, ↓reduceIte] at hCreate
      cases hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] with
      | none =>
        simp only [hSplit] at hCreate
        cases (congrArg Prod.fst hCreate)
      | some pair =>
        rcases pair with ⟨parSegs, lastSeg⟩
        simp only [hSplit] at hCreate
        cases hPar : vfsResolveSegs s₀.nodes "/" parSegs true 512 with
        | error pe =>
          simp only [hPar] at hCreate
          cases (congrArg Prod.fst hCreate)
        | ok parRes =>
          rcases parRes with ⟨parCanon, parNode⟩
          cases parNode with
          | file _ _ =>
            simp only [hPar] at hCreate
            cases (congrArg Prod.fst hCreate)
          | symlink _ _ =>
            simp only [hPar] at hCreate
            cases (congrArg Prod.fst hCreate)
          | dir parMode =>
            simp only [hPar] at hCreate
            by_cases hPerm : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = true
            · simp only [hPerm, ↓reduceIte] at hCreate
              cases (congrArg Prod.fst hCreate)
            · have hPermFalse : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = false :=
                Bool.eq_false_iff.mpr hPerm
              have hExec : ((parMode / 64) % 2 == 0) = false := by
                cases hx : (parMode / 64) % 2 == 0 <;> simp_all
              simp only [hPermFalse, Bool.false_eq_true, ↓reduceIte] at hCreate
              cases hExisting : s₀.nodes (vfsChildPath parCanon lastSeg) with
              | some _ =>
                simp only [hExisting] at hCreate
                cases (congrArg Prod.fst hCreate)
              | none =>
                simp only [hExisting] at hCreate
                have hsEq : s₁ = { s₀ with
                    tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))
                    keys := vfsChildPath parCanon lastSeg :: s₀.keys } := (congrArg Prod.snd hCreate).symm
                subst hsEq
                have hAllSegs : vfsSplitSegs (vfsAbsNorm s₀.cwd path) = parSegs ++ [lastSeg] := by
                  simpa using splitLastAux_spec (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] parSegs lastSeg hSplit
                have hAllValid := vfsSplitSegs_normPath_valid (if Internal.isAbsolute path then path else Internal.join s₀.cwd path)
                have hParValid : ∀ s ∈ parSegs, Internal.validFileName s = true := fun s hs =>
                  hAllValid s (by rw [← vfsAbsNorm, hAllSegs]; simp [hs])
                have hLastValid : Internal.validFileName lastSeg = true :=
                  hAllValid lastSeg (by rw [← vfsAbsNorm, hAllSegs]; simp)
                have hParCanon : isCanonPath parCanon = true :=
                  vfsResolveSegs_isCanon s₀.nodes 512 "/" parSegs true (parCanon, .dir parMode) (by decide) hParValid hPar
                have hParLookup : s₀.nodes parCanon = some (.dir parMode) :=
                  vfsResolveSegs_ok_node s₀.nodes 512 "/" parSegs true parCanon (.dir parMode) hPar
                have hNodesEq :
                    ({ s₀ with
                        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))
                        keys := vfsChildPath parCanon lastSeg :: s₀.keys } : VfsState).nodes =
                      fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k := by
                  change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (vfsEmptyDir 0o755))) = _
                  exact vfsTreeNodes_insert_dir s₀.tree parCanon lastSeg hParCanon hLastValid ⟨parMode, hParLookup⟩ hExisting
                have hParNew := vfsResolveSegs_insert_fresh s₀.nodes (vfsChildPath parCanon lastSeg)
                  (.dir 0o755) hExisting 512 "/" parSegs true (parCanon, .dir parMode) hPar
                have hChildNew :
                    (fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k)
                      (vfsChildPath parCanon lastSeg) = some (.dir 0o755) := by
                  simp
                have hChildStep := vfsResolveSegs_dir_child
                  (fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k)
                  lastSeg parCanon parMode hExec hChildNew 512 "/" parSegs hParNew
                have h1024 := vfsResolveSegs_fuel_mono
                  (fun k => if k == vfsChildPath parCanon lastSeg then some (.dir 0o755) else s₀.nodes k)
                  513 1024 "/" (parSegs ++ [lastSeg]) true (vfsChildPath parCanon lastSeg, .dir 0o755)
                  (by omega) hChildStep
                rw [← hAllSegs] at h1024
                dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run, bind, StateT.bind, pure, StateT.pure]
                rw [hNodesEq, h1024]
                rfl

/-- Proof of `test_fs_vfs_mkdir_existingFails` on `vfsApi`. -/
theorem proof_fs_vfs_mkdir_existingFails :
    AllPass (test_fs_vfs_mkdir_existingFails vfsApi) := by
  intro s₀ path parents hOk
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hOk
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes, Except.isOk, Except.toBool] at hOk
  | ok p =>
    rcases p with ⟨canon, nd⟩
    dsimp only [vfsApi, Internal.mkApiM, Internal.mkdirImplM, vfsOps, vfsStatPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure, assert]
    rw [hRes]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.pure]
    exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩

private theorem vfsResolveSegs_root_dir (m : Nat) :
    vfsResolveSegs (fun k => if k == "/" then some (.dir m) else none) "/" [] true 512 = .ok ("/", .dir m) := by
  unfold vfsResolveSegs
  rfl

private theorem vfsLstat_broken_symlink :
    let st : VfsState :=
      { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
        keys := ["/", "/broken"]
        cwd := "/"
        nonce := 0 }
    ((vfsApi.lstat "/broken").run st).1.isOk = true := by
  intro st
  have hAbs : vfsAbsNorm "/" "/broken" = "/broken" := by decide
  have hSegs : vfsSplitSegs "/broken" = ["broken"] := by decide
  have hChild : vfsChildPath "/" "broken" = "/broken" := by decide
  have hCwd : st.cwd = "/" := rfl
  have hRes : vfsResolveSegs st.nodes "/" ["broken"] false 1024 = .ok ("/broken", .symlink "/nope" 0o777) := by
    unfold vfsResolveSegs
    have hRoot : st.nodes "/" = some (.dir 0o755) := rfl
    have hExec : ((0o755 / 64) % 2 == 0) = false := by decide
    rw [hRoot]
    dsimp only
    rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hChild]
    unfold vfsResolveSegs
    have hBrk : st.nodes "/broken" = some (.symlink "/nope" 0o777) := rfl
    rw [hBrk]
    rfl
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
  rw [hCwd, hAbs, hSegs, hRes]
  rfl

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_mkdir_existingFails`. -/
theorem reach_fs_vfs_mkdir_existingFails :
    CanReach (test_fs_vfs_mkdir_existingFails vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  exact ⟨st, "/broken", true, vfsLstat_broken_symlink, proof_fs_vfs_mkdir_existingFails st "/broken" true vfsLstat_broken_symlink⟩

/-- Proof of `test_fs_vfs_touch_existingFails` on `vfsApi`. -/
theorem proof_fs_vfs_touch_existingFails :
    AllPass (test_fs_vfs_touch_existingFails vfsApi) := by
  intro s₀ path hOk
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hOk
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes, Except.isOk, Except.toBool] at hOk
  | ok p =>
    rcases p with ⟨canon, nd⟩
    dsimp only [vfsApi, Internal.mkApiM, Internal.touchImplM, vfsOps, vfsStatPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure, assert]
    rw [hRes]
    simp only [Bool.not_false, ↓reduceIte, StateT.pure]
    exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_touch_existingFails`. -/
theorem reach_fs_vfs_touch_existingFails :
    CanReach (test_fs_vfs_touch_existingFails vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  exact ⟨st, "/broken", vfsLstat_broken_symlink, proof_fs_vfs_touch_existingFails st "/broken" vfsLstat_broken_symlink⟩

/-- Proof of `test_fs_vfs_walk_preservesStatError` on `vfsApi`. -/
theorem proof_fs_vfs_walk_preservesStatError :
    AllPass (test_fs_vfs_walk_preservesStatError vfsApi) := by
  intro s₀ root
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd root)) true 1024 with
  | error err =>
    dsimp only [vfsApi, Internal.mkApiM, Internal.walkImplM, vfsOps, vfsStatPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure, assert]
    rw [hRes]
    simp [StateT.pure]
  | ok p =>
    rcases p with ⟨canon, nd⟩
    dsimp only
    by_cases hNotDir : ((vfsToStat nd).kind != .dir) = true
    · simp only [hNotDir, ↓reduceIte]
      dsimp only [vfsApi, Internal.mkApiM, Internal.walkImplM, vfsOps, vfsStatPure, StateT.run,
        bind, StateT.bind, pure, StateT.pure, assert]
      rw [hRes]
      simp only [hNotDir, ↓reduceIte, StateT.pure]
      exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
    · have hNotDirFalse : ((vfsToStat nd).kind != .dir) = false := Bool.eq_false_iff.mpr hNotDir
      simp only [hNotDirFalse, Bool.false_eq_true, ↓reduceIte]
      trivial

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_walk_preservesStatError` exercising `EACCES`. -/
theorem reach_fs_vfs_walk_preservesStatError :
    CanReach (test_fs_vfs_walk_preservesStatError vfsApi) := by
  let st : VfsState :=
    { tree := vfsEmptyDir 0o000
      keys := ["/"]
      cwd := "/"
      nonce := 0 }
  refine ⟨st, "/locked", ?_⟩
  exact proof_fs_vfs_walk_preservesStatError st "/locked"

private theorem mkdirImpl_parents_ok {S : Type} (ops : RawFsOpsM (StateM S)) (path : String) (s₀ : S)
    (hMk : ((Internal.mkdirImplM ops path true false).run s₀).1 = .ok ()) :
    ∃ s_mid,
      ((ops.createDir path).run s_mid).1 = .ok () ∧
      ((Internal.mkdirImplM ops path true false).run s₀).2 = ((ops.createDir path).run s_mid).2 := by
  dsimp only [Internal.mkdirImplM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hMk ⊢
  cases hPre : ops.stat false path s₀ with
  | mk resPre sPre =>
    rw [hPre] at hMk
    dsimp only at hMk ⊢
    cases resPre with
    | ok _ =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.pure] at hMk
      cases hMk
    | error e =>
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte, StateT.pure] at hMk
        cases hMk
      · have hNfFalse : (e.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfFalse, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hMk ⊢
        cases hAnc : Internal.ensureAncestorsM ops (Internal.ancestorChain path path.toList.length) sPre with
        | mk ancRes s_mid =>
          dsimp only [StateT.bind] at hMk ⊢
          rw [hAnc] at hMk ⊢
          cases ancRes with
          | error _ =>
            cases hMk
          | ok _ =>
            exact ⟨s_mid, hMk, rfl⟩

/-- Proof of `test_fs_vfs_mkdir_parentsCreatesDir` on `vfsApi`. -/
theorem proof_fs_vfs_mkdir_parentsCreatesDir :
    AllPass (test_fs_vfs_mkdir_parentsCreatesDir vfsApi) := by
  intro s₀ path hRes
  have hMk : ((Internal.mkdirImplM vfsOps path true false).run s₀).1 = .ok () := hRes
  rcases mkdirImpl_parents_ok vfsOps path s₀ hMk with ⟨s_mid, hCr, hSnd⟩
  dsimp only [assert]
  change ((vfsApi.isDir path).run ((Internal.mkdirImplM vfsOps path true false).run s₀).2).1 = .ok true ∧ True
  rw [hSnd]
  exact ⟨vfsCreateDir_sets_isDir path s_mid _ (Prod.ext hCr rfl), trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_mkdir_parentsCreatesDir`. -/
theorem reach_fs_vfs_mkdir_parentsCreatesDir :
    CanReach (test_fs_vfs_mkdir_parentsCreatesDir vfsApi) := by
  let st : VfsState :=
    { tree := vfsEmptyDir 0o755
      keys := ["/"]
      cwd := "/"
      nonce := 0 }
  let stA : VfsState :=
    { st with
      tree := vfsTreeSet st.tree (vfsSplitSegs "/a") (some (vfsEmptyDir 0o755))
      keys := "/a" :: st.keys }
  have hCwd : st.cwd = "/" := rfl
  have hPre : vfsStatPure st false "/a/b" =
      .error { kind := .notFound, path := some "/a", message := "no such file or directory: /a" } := by
    have hAbs : vfsAbsNorm "/" "/a/b" = "/a/b" := by decide
    have hSegs : vfsSplitSegs "/a/b" = ["a", "b"] := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    dsimp only [vfsStatPure]
    rw [hCwd, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
    unfold vfsResolveSegs; rw [show st.nodes "/a" = none from rfl]
    rfl
  have hStatA : vfsStatPure st true "/a" =
      .error { kind := .notFound, path := some "/a", message := "no such file or directory: /a" } := by
    have hAbs : vfsAbsNorm "/" "/a" = "/a" := by decide
    have hSegs : vfsSplitSegs "/a" = ["a"] := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    dsimp only [vfsStatPure]
    rw [hCwd, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
    unfold vfsResolveSegs; rw [show st.nodes "/a" = none from rfl]
    rfl
  have hCreA : vfsCreateDirPure st "/a" = (.ok (), stA) := by
    have hAbs : vfsAbsNorm "/" "/a" = "/a" := by decide
    have hSegs : vfsSplitSegs "/a" = ["a"] := by decide
    have hPar : Internal.splitLastAux ["a"] [] = some ([], "a") := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    have hPreA : vfsResolveSegs st.nodes "/" ["a"] false 1024 =
        .error { kind := .notFound, path := some "/a", message := "no such file or directory: /a" } := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
      unfold vfsResolveSegs; rw [show st.nodes "/a" = none from rfl]
      rfl
    have hRootA : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
    dsimp only [vfsCreateDirPure]
    rw [hCwd, hAbs, hSegs, hPreA]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]
    dsimp only
    rw [hRootA]
    dsimp only
    rw [hC1, show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show st.nodes "/a" = none from rfl]
  have hAnc : Internal.ensureAncestorsM vfsOps ["/a"] st = (.ok (), stA) := by
    dsimp only [Internal.ensureAncestorsM, Internal.ensureDirM, StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat true "/a" st = (vfsStatPure st true "/a", st) from rfl, hStatA]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.bind]
    rw [show vfsOps.createDir "/a" st = vfsCreateDirPure st "/a" from rfl, hCreA]
    rfl
  have hCreB : ((vfsOps.createDir "/a/b").run stA).1 = .ok () := by
    have hAbs : vfsAbsNorm "/" "/a/b" = "/a/b" := by decide
    have hSegs : vfsSplitSegs "/a/b" = ["a", "b"] := by decide
    have hPar : Internal.splitLastAux ["a", "b"] [] = some (["a"], "b") := by decide
    have hC1 : vfsChildPath "/" "a" = "/a" := by decide
    have hC2 : vfsChildPath "/a" "b" = "/a/b" := by decide
    have hCwdA : stA.cwd = "/" := rfl
    have hPreB : vfsResolveSegs stA.nodes "/" ["a", "b"] false 1024 =
        .error { kind := .notFound, path := some "/a/b", message := "no such file or directory: /a/b" } := by
      unfold vfsResolveSegs; rw [show stA.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
      unfold vfsResolveSegs; rw [show stA.nodes "/a" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC2]
      unfold vfsResolveSegs; rw [show stA.nodes "/a/b" = none from rfl]
      rfl
    have hParB : vfsResolveSegs stA.nodes "/" ["a"] true 512 = .ok ("/a", .dir 0o755) := by
      unfold vfsResolveSegs; rw [show stA.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hC1]
      unfold vfsResolveSegs; rw [show stA.nodes "/a" = some (.dir 0o755) from rfl]
    dsimp only [vfsOps, vfsCreateDirPure, StateT.run]
    rw [hCwdA, hAbs, hSegs, hPreB]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]
    dsimp only
    rw [hParB]
    dsimp only
    rw [hC2, show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show stA.nodes "/a/b" = none from rfl]
  have hChain : Internal.ancestorChain "/a/b" "/a/b".toList.length = ["/a"] := by decide
  have hMk : ((vfsApi.mkdir "/a/b" true false).run st).1 = .ok () := by
    change ((Internal.mkdirImplM vfsOps "/a/b" true false).run st).1 = .ok ()
    dsimp only [Internal.mkdirImplM, StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/a/b" st = (vfsStatPure st false "/a/b", st) from rfl, hPre]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rw [hChain, show StateT.bind (Internal.ensureAncestorsM vfsOps ["/a"]) = fun k s =>
      match Internal.ensureAncestorsM vfsOps ["/a"] s with | (a, s') => k a s' from rfl]
    dsimp only
    rw [hAnc]
    exact hCreB
  exact ⟨st, "/a/b", hMk, proof_fs_vfs_mkdir_parentsCreatesDir st "/a/b" hMk⟩

private theorem list_getLast?_append {α : Type} :
    ∀ xs ys : List α, ys ≠ [] → (xs ++ ys).getLast? = ys.getLast? := by
  intro xs ys hne
  induction xs with
  | nil => rfl
  | cons x xt ih =>
    rw [List.cons_append, List.getLast?_cons, ih]
    cases hY : ys with
    | nil => exact absurd hY hne
    | cons z zs => rw [List.getLast?_cons]; rfl

private theorem joinSlashChars_last_not_slash :
    ∀ xs : List (List Char), xs ≠ [] → (∀ s ∈ xs, !s.isEmpty ∧ '/' ∉ s) →
      ('/' :: Internal.joinSlashChars xs).getLast? ≠ some '/' := by
  intro xs hne hvalid
  induction xs with
  | nil => exact absurd rfl hne
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [Internal.joinSlashChars]
      rcases hHd : hd.reverse with _ | ⟨c, _⟩
      · have : hd = [] := by simpa using congrArg List.reverse hHd
        have hv := (hvalid hd (by simp)).1
        simp [this] at hv
      · have hC : c ∈ hd := by
          have : c ∈ hd.reverse := by rw [hHd]; simp
          exact List.mem_reverse.mp this
        have hNoSlash : '/' ∉ hd := (hvalid hd (by simp)).2
        have hLast : ('/' :: hd).getLast? = some c := by
          have hHdLast : hd.getLast? = some c := by
            rw [← List.head?_reverse, hHd]; rfl
          rw [List.getLast?_cons, hHdLast]
          rfl
        rw [hLast]
        intro heq
        cases heq
        exact hNoSlash hC
    | cons b bs =>
      have ih' := ih (by simp) (fun s hs => hvalid s (by simp [hs]))
      simp only [Internal.joinSlashChars]
      have hApp : ('/' :: (hd ++ '/' :: Internal.joinSlashChars (b :: bs))).getLast? =
          ('/' :: Internal.joinSlashChars (b :: bs)).getLast? := by
        change (('/' :: hd) ++ ('/' :: Internal.joinSlashChars (b :: bs))).getLast? =
          ('/' :: Internal.joinSlashChars (b :: bs)).getLast?
        exact list_getLast?_append ('/' :: hd) ('/' :: Internal.joinSlashChars (b :: bs)) (by simp)
      rw [hApp]
      exact ih'

private theorem join_vfsChildPath (c child : String)
    (hc : isCanonPath c = true) (hcNe : c ≠ "/") (hchild : Internal.validFileName child = true) :
    Internal.join c child = c ++ "/" ++ child := by
  obtain ⟨hCEq, hParts⟩ := isCanonPath_normPath_parts c hc
  have hChildL := validFileName_charList child hchild
  have hNotAbs : Internal.isAbsolute child = false := by
    unfold Internal.isAbsolute
    cases hList : child.toList with
    | nil => rfl
    | cons ch _ =>
      by_cases hSl : ch = '/'
      · subst hSl
        exfalso
        exact hChildL.2.2.1 (by rw [hList]; simp)
      · unfold Internal.isAbsChars; simp [hSl]
  have hPartsNe : (vfsSplitSegs c).map String.toList ≠ [] := by
    intro hEmp
    cases hSp : vfsSplitSegs c with
    | nil =>
      have : c = "/" := by rw [hCEq, hSp]; rfl
      exact hcNe this
    | cons _ _ => simp [hSp] at hEmp
  have hCNeEmpty : c ≠ "" := by
    intro h
    have hToL : c.toList = [] := by simp [h]
    rw [hCEq] at hToL
    simp at hToL
  have hCNotEmpty : c.isEmpty = false := by
    cases he : c.isEmpty
    · rfl
    · exfalso; exact hCNeEmpty (by simpa [String.isEmpty] using he)
  have hNotEnd : (c.toList.getLast? == some '/') = false := by
    have hGl := joinSlashChars_last_not_slash ((vfsSplitSegs c).map String.toList) hPartsNe
      (fun s hs => ⟨(hParts s hs).1, (hParts s hs).2.2.1⟩)
    rw [hCEq, String.toList_ofList]
    exact beq_false_of_ne hGl
  simp [Internal.join, hNotAbs, hCNotEmpty, hNotEnd]

private theorem parent_name_vfsChildPath (c child : String)
    (hc : isCanonPath c = true) (hcNe : c ≠ "/") (hchild : Internal.validFileName child = true) :
    Internal.parent (c ++ "/" ++ child) = some c ∧ Internal.name (c ++ "/" ++ child) = some child := by
  obtain ⟨hCEq, hParts⟩ := isCanonPath_normPath_parts c hc
  have hChildL := validFileName_charList child hchild
  have hBeqF : (c == "/") = false := beq_false_of_ne hcNe
  have hChildV : vfsChildPath c child = c ++ "/" ++ child := by
    simp [vfsChildPath, hBeqF]
  have ⟨hChildCanon, hChildSp⟩ := vfsChildPath_valid c child hc hchild
  rw [hChildV] at hChildCanon hChildSp
  obtain ⟨hDstEq, hDstParts⟩ := isCanonPath_normPath_parts (c ++ "/" ++ child) hChildCanon
  have hPartsNe : (vfsSplitSegs c).map String.toList ≠ [] := by
    intro hEmp
    cases hSp : vfsSplitSegs c with
    | nil =>
      have : c = "/" := by rw [hCEq, hSp]; rfl
      exact hcNe this
    | cons _ _ => simp [hSp] at hEmp
  have hNewParts : (vfsSplitSegs (c ++ "/" ++ child)).map String.toList =
      (vfsSplitSegs c).map String.toList ++ [child.toList] := by
    rw [hChildSp, List.map_append, List.map_singleton]
  rw [hNewParts] at hDstEq hDstParts
  have hSplitAll :
      Internal.splitCharList '/' ('/' :: Internal.joinSlashChars ((vfsSplitSegs c).map String.toList ++ [child.toList])) =
      [] :: ((vfsSplitSegs c).map String.toList ++ [child.toList]) := by
    unfold Internal.splitCharList
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [splitCharList_joinSlashChars _ (by simp [hPartsNe]) (fun s hs => (hDstParts s hs).2.2.1)]
  have hClean :
      Internal.cleanCharSegments (c ++ "/" ++ child) =
      (true, (vfsSplitSegs c).map String.toList ++ [child.toList]) := by
    have hCleEq : Internal.cleanCharSegments (c ++ "/" ++ child) =
        Internal.cleanCharSegments (String.ofList ('/' :: Internal.joinSlashChars
          ((vfsSplitSegs c).map String.toList ++ [child.toList]))) :=
      congrArg Internal.cleanCharSegments hDstEq
    rw [hCleEq]
    unfold Internal.cleanCharSegments Internal.isAbsChars
    simp only [String.toList_ofList, hSplitAll, List.filter_cons, List.isEmpty_nil,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, true_and]
    rw [List.filter_eq_self.mpr]
    intro s hs
    exact Bool.and_eq_true _ _ |>.mpr ⟨(hDstParts s hs).1, (hDstParts s hs).2.1⟩
  have hLast := splitLastAux_append_singleton ((vfsSplitSegs c).map String.toList) [] child.toList
  have hSpPar : Internal.splitParentName (c ++ "/" ++ child) = some (some c, child) := by
    unfold Internal.splitParentName
    rw [hClean]
    dsimp only
    rw [hLast]
    rcases hP : (vfsSplitSegs c).map String.toList with _ | ⟨hd, tl⟩
    · exact absurd hP hPartsNe
    · simp only [List.reverse_nil, List.nil_append, String.ofList_toList, Option.some.injEq,
        Prod.mk.injEq, and_true]
      rw [← hP]
      exact hCEq.symm
  simp [Internal.parent, Internal.name, hSpPar]

private theorem vfsAbsNorm_abs (cwd p : String) (hp : Internal.isAbsolute p = true) :
    vfsAbsNorm cwd p = Internal.normPath p := by
  simp [vfsAbsNorm, hp]

private theorem vfsResolveSegs_abs_root_realPath (s₀ : VfsState) (stRoot : FileStat)
    (hStat : ((vfsApi.stat "/").run s₀).1 = .ok stRoot)
    (hKind : stRoot.kind = .dir)
    (hRes : ((vfsApi.resolve "/").run s₀).1 = .ok "/") :
    s₀.nodes "/" = some (.dir stRoot.mode) := by
  have hAbs : vfsAbsNorm s₀.cwd "/" = "/" := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hSegs : vfsSplitSegs "/" = [] := by decide
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run] at hRes
  rw [hAbs, hSegs] at hRes
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hStat
  rw [hAbs, hSegs] at hStat
  cases hR : vfsResolveSegs s₀.nodes "/" [] true 1024 with
  | error _ => simp [hR] at hRes
  | ok p =>
    rcases p with ⟨canon, nd⟩
    simp only [hR, Except.ok.injEq] at hRes hStat
    subst hRes
    have hNode := vfsResolveSegs_ok_node s₀.nodes 1024 "/" [] true "/" nd hR
    cases nd with
    | dir m =>
      have : stRoot.mode = m := by rw [← hStat]; rfl
      subst this; exact hNode
    | file _ _ => rw [← hStat] at hKind; simp [vfsToStat] at hKind
    | symlink _ _ => rw [← hStat] at hKind; simp [vfsToStat] at hKind

private theorem vfsTree_noOrphan_child (t : VfsTree) (hNone : vfsTreeNodes t "/new_parent" = none) :
    vfsTreeNodes t "/new_parent/copy" = none := by
  have hC1 : isCanonPath "/new_parent" = true := by decide
  have hC2 : isCanonPath "/new_parent/copy" = true := by decide
  have hS1 : vfsSplitSegs "/new_parent" = ["new_parent"] := by decide
  have hS2 : vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] := by decide
  simp only [vfsTreeNodes, hC1, hC2, ↓reduceIte, hS1, hS2] at hNone ⊢
  cases t with
  | file _ _ => rfl
  | symlink _ _ => rfl
  | dir m ch =>
    simp only [vfsTreeGet] at hNone ⊢
    cases hCh : ch "new_parent" with
    | none => rfl
    | some _ => simp [hCh] at hNone

private theorem copyTree_selfCopyRejected_exec (s₀ : VfsState) (src dst : String)
    (st : FileStat) (hStat : ((vfsApi.stat src).run s₀).1 = .ok st) (hKind : st.kind = .dir)
    (c : String) (hResSrc : ((vfsApi.resolve src).run s₀).1 = .ok c)
    (hCAbs : vfsApi.isAbsolute c = true) (hCNeRoot : c ≠ "/")
    (hResC : ((vfsApi.resolve c).run s₀).1 = .ok c)
    (hDstCase : dst = c ∨ ∃ child, (!child.isEmpty) = true ∧ (!decide ('/' ∈ child.toList)) = true ∧
      (child != ".") = true ∧ (child != "..") = true ∧ dst = c ++ "/" ++ child ∧ ((vfsApi.resolve dst).run s₀).1.isOk = false) :
    ∃ e, (vfsApi.copyTree src dst false).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput := by
  have hAllValid := vfsSplitSegs_normPath_valid (if Internal.isAbsolute src then src else Internal.join s₀.cwd src)
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run] at hResSrc
  cases hRS : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd src)) true 1024 with
  | error _ => simp [hRS] at hResSrc
  | ok rp =>
    rcases rp with ⟨c', nd'⟩
    simp only [hRS, Except.ok.injEq] at hResSrc
    have hCCanon : isCanonPath c = true := by
      subst hResSrc
      exact vfsResolveSegs_isCanon s₀.nodes 1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd src)) true (c', nd')
        (by decide) hAllValid hRS
    have hCNorm : Internal.normPath c = c := by
      have hAnd : (Internal.isAbsolute c && (Internal.normPath c == c)) = true := hCCanon
      exact beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hAnd).2
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hStat
    dsimp only [vfsApi, Internal.mkApiM, Internal.copyTreeImplM, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true src s₀ = (vfsStatPure s₀ true src, s₀) from rfl]
    change (match (vfsStatPure s₀ true src, s₀) with | (a, s) => _)
    have hStatP : vfsStatPure s₀ true src = .ok st := hStat
    rw [hStatP]
    have hNotDirF : (st.kind != .dir) = false := by rw [hKind]; decide
    simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath src s₀ = (vfsRealPathPure s₀ src, s₀) from rfl]
    have hRpSrc : vfsRealPathPure s₀ src = .ok c := by
      dsimp only [vfsRealPathPure]
      rw [hRS, hResSrc]
    rw [hRpSrc]
    dsimp only
    cases hDstCase with
    | inl hEqDst =>
      subst hEqDst
      have hAbsC : Internal.isAbsolute dst = true := hCAbs
      simp only [hAbsC, ↓reduceIte, hCNorm]
      cases hL : dst.toList.length + 1 with
      | zero => omega
      | succ fuel =>
        unfold Internal.resolveApproxGoM
        dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
        rw [show vfsOps.realPath dst s₀ = (vfsRealPathPure s₀ dst, s₀) from rfl]
        have hRpC : vfsRealPathPure s₀ dst = .ok dst := hResC
        rw [hRpC]
        simp only [List.foldl_nil]
        dsimp only [StateT.pure, Pure.pure, pure]
        rw [show (dst == dst || dst == "/" || (dst.toList ++ ['/']).isPrefixOf dst.toList) = true from by simp]
        simp only [↓reduceIte]
        exact ⟨_, rfl, rfl⟩
    | inr hSub =>
      rcases hSub with ⟨child, hChNeEmpty, hChNoSlash, hChNeDot, hChNeDotDot, hDstEq, hResDstBad⟩
      subst hDstEq
      have hChNoSlashP : '/' ∉ child.toList := by simpa using hChNoSlash
      have hChListNe : (!child.toList.isEmpty) = true := by
        cases hcL : child.toList with
        | nil =>
          have hE : child = "" := by rw [← String.ofList_toList (s := child), hcL]
          rw [hE] at hChNeEmpty; cases hChNeEmpty
        | cons _ _ => rfl
      have hChListDot : (child.toList != ['.']) = true := bne_iff_ne.mpr fun heq => by
        have hE : child = "." := by rw [← String.ofList_toList (s := child), heq]
        rw [hE] at hChNeDot; cases hChNeDot
      have hChListDotDot : (child.toList != ['.', '.']) = true := bne_iff_ne.mpr fun heq => by
        have hE : child = ".." := by rw [← String.ofList_toList (s := child), heq]
        rw [hE] at hChNeDotDot; cases hChNeDotDot
      have hChValid : Internal.validFileName child = true := by
        simp only [Internal.validFileName, Bool.and_eq_true]
        exact ⟨⟨⟨hChListNe, by simpa using hChNoSlashP⟩, hChListDot⟩, hChListDotDot⟩
      have ⟨hParDst, hNameDst⟩ := parent_name_vfsChildPath c child hCCanon hCNeRoot hChValid
      have hBeqRootF : (c == "/") = false := beq_false_of_ne hCNeRoot
      have hChildV : vfsChildPath c child = c ++ "/" ++ child := by simp [vfsChildPath, hBeqRootF]
      have ⟨hDstCanon, _⟩ := hChildV ▸ vfsChildPath_valid c child hCCanon hChValid
      have hDstAnd : (Internal.isAbsolute (c ++ "/" ++ child) && (Internal.normPath (c ++ "/" ++ child) == (c ++ "/" ++ child))) = true := hDstCanon
      have hDstPair := Bool.and_eq_true _ _ |>.mp hDstAnd
      have hDstAbs : Internal.isAbsolute (c ++ "/" ++ child) = true := hDstPair.1
      have hDstNorm : Internal.normPath (c ++ "/" ++ child) = c ++ "/" ++ child := beq_iff_eq.mp hDstPair.2
      have hCLenPos : 0 < c.toList.length := by
        have hCAbs' : Internal.isAbsolute c = true := hCAbs
        cases hCl : c.toList with
        | nil => rw [Internal.isAbsolute] at hCAbs'; rw [hCl] at hCAbs'; cases hCAbs'
        | cons _ _ => simp
      have hChildLenPos : 0 < child.toList.length := by
        cases hCl : child.toList with
        | nil =>
          have hE : child = "" := by rw [← String.ofList_toList (s := child), hCl]
          rw [hE] at hChNeEmpty; cases hChNeEmpty
        | cons _ _ => simp
      have hFuel2 : ∃ k, (c ++ "/" ++ child).toList.length + 1 = k + 2 := by
        have hLen : (c ++ "/" ++ child).toList.length = c.toList.length + 1 + child.toList.length := by
          rw [String.toList_append, String.toList_append, List.length_append, List.length_append,
              show "/".toList = ['/'] by decide, List.length_singleton]
        exact ⟨c.toList.length + child.toList.length, by omega⟩
      rcases hFuel2 with ⟨k, hFuelEq⟩
      simp only [hDstAbs, ↓reduceIte, hDstNorm]
      dsimp only [Bind.bind, StateT.bind, StateT.pure]
      rw [hFuelEq]
      unfold Internal.resolveApproxGoM
      dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
      rw [show vfsOps.realPath (c ++ "/" ++ child) s₀ = (vfsRealPathPure s₀ (c ++ "/" ++ child), s₀) from rfl]
      have hErrDst : ∃ err, vfsRealPathPure s₀ (c ++ "/" ++ child) = .error err := by
        cases hRd : vfsRealPathPure s₀ (c ++ "/" ++ child) with
        | ok _ =>
          have : ((vfsApi.resolve (c ++ "/" ++ child)).run s₀).1.isOk = true := by
            change (vfsRealPathPure s₀ (c ++ "/" ++ child)).isOk = true
            rw [hRd]; rfl
          simp [this] at hResDstBad
        | error e => exact ⟨e, rfl⟩
      rcases hErrDst with ⟨err, hRd⟩
      rw [hRd]
      dsimp only
      rw [hParDst, hNameDst]
      dsimp only
      unfold Internal.resolveApproxGoM
      dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
      rw [show vfsOps.realPath c s₀ = (vfsRealPathPure s₀ c, s₀) from rfl]
      have hRpC : vfsRealPathPure s₀ c = .ok c := hResC
      rw [hRpC]
      simp only [List.foldl_cons, List.foldl_nil, join_vfsChildPath c child hCCanon hCNeRoot hChValid]
      have hPref : (c.toList ++ ['/']).isPrefixOf (c ++ "/" ++ child).toList = true := by
        apply List.isPrefixOf_iff_prefix.mpr
        refine ⟨child.toList, ?_⟩
        rw [String.toList_append, String.toList_append, show "/".toList = ['/'] by decide, List.append_assoc]
      have hCondTrue : (c ++ "/" ++ child == c || c == "/" || (c.toList ++ ['/']).isPrefixOf (c ++ "/" ++ child).toList) = true := by
        simp only [hPref, Bool.or_true]
      dsimp only [StateT.pure, Pure.pure, pure]
      rw [hCondTrue]
      simp only [↓reduceIte]
      exact ⟨_, rfl, rfl⟩

/-- Proof of `test_fs_vfs_copyTree_selfCopyRejected` on `vfsApi`. -/
theorem proof_fs_vfs_copyTree_selfCopyRejected :
    AllPass (test_fs_vfs_copyTree_selfCopyRejected vfsApi) := by
  intro s₀ src dst ⟨st, hStat, hKind⟩ ⟨c, hResSrc, hCAbs, hCNeRoot, hResC, hDstCase⟩
  rcases copyTree_selfCopyRejected_exec s₀ src dst st hStat hKind c hResSrc hCAbs hCNeRoot hResC hDstCase with ⟨e, hEq, hEk⟩
  rw [hEq]
  exact ⟨⟨⟨e, rfl, hEk⟩, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_copyTree_selfCopyRejected`. -/
theorem reach_fs_vfs_copyTree_selfCopyRejected :
    CanReach (test_fs_vfs_copyTree_selfCopyRejected vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    have hAbs : vfsAbsNorm "/" "/src" = "/src" := by decide
    have hSegs : vfsSplitSegs "/src" = ["src"] := by decide
    have hChild : vfsChildPath "/" "src" = "/src" := by decide
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hChild]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    have hAbs : vfsAbsNorm "/" "/src" = "/src" := by decide
    have hSegs : vfsSplitSegs "/src" = ["src"] := by decide
    have hChild : vfsChildPath "/" "src" = "/src" := by decide
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, hAbs, hSegs]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hChild]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  exact ⟨st, "/src", "/src",
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, hResSrc, Or.inl rfl⟩,
    proof_fs_vfs_copyTree_selfCopyRejected st "/src" "/src"
      ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
      ⟨"/src", hResSrc, by decide, by decide, hResSrc, Or.inl rfl⟩⟩

private theorem not_prefix_new_parent_copy (c : String)
    (hAbs : Internal.isAbsolute c = true) (hNe2 : c ≠ "/new_parent") :
    (c.toList ++ ['/']).isPrefixOf "/new_parent/copy".toList = false := by
  by_cases hPref : (c.toList ++ ['/']).isPrefixOf "/new_parent/copy".toList = true
  · exfalso
    have hP := List.isPrefixOf_iff_prefix.mp hPref
    rcases hP with ⟨tail, hEq⟩
    cases hCl : c.toList with
    | nil => simp [Internal.isAbsolute, Internal.isAbsChars, hCl] at hAbs
    | cons c0 cs =>
      have hC0 : c0 = '/' := by
        have hI : Internal.isAbsChars (c0 :: cs) = true := hCl ▸ hAbs
        cases hEqS : (c0 == '/') with
        | true => exact beq_iff_eq.mp hEqS
        | false =>
          exfalso
          have : Internal.isAbsChars (c0 :: cs) = false := by
            unfold Internal.isAbsChars
            split
            · next h => cases h; simp at hEqS
            · rfl
          simp [this] at hI
      subst hC0
      have hTarget : "/new_parent/copy".toList = '/' :: "new_parent/copy".toList := by decide
      rw [hCl, hTarget, List.append_assoc] at hEq
      simp only [List.cons_append, List.cons.injEq, true_and] at hEq
      have hLen : cs.length < 15 := by
        have hL := congrArg List.length hEq
        simp [show "new_parent/copy".toList.length = 15 by decide] at hL
        omega
      have hAt : ("new_parent/copy".toList[cs.length]! == '/') = true := by
        have hIdx : (cs ++ '/' :: tail)[cs.length]! = "new_parent/copy".toList[cs.length]! :=
          congrArg (fun l : List Char => l[cs.length]!) hEq
        have hSlash : (cs ++ '/' :: tail)[cs.length]! = '/' := by simp
        rw [← hIdx, hSlash]
        rfl
      have hOnly : ∀ i : Fin 15, ("new_parent/copy".toList[i.val]! == '/') = true → i.val = 10 := by decide
      have hCsLen : cs.length = 10 := hOnly ⟨cs.length, hLen⟩ hAt
      have hTake : (cs ++ '/' :: tail).take 10 = "new_parent/copy".toList.take 10 :=
        congrArg (List.take 10) hEq
      have hCsEq : cs = "new_parent".toList := by
        have hTakeL : (cs ++ '/' :: tail).take cs.length = cs := by simp
        have hTakeR : "new_parent/copy".toList.take 10 = "new_parent".toList := by decide
        rw [← hCsLen, hTakeL] at hTake
        rw [← hCsLen] at hTakeR
        exact hTake.trans hTakeR
      apply hNe2
      apply String.ext_iff.mpr
      rw [hCl, hCsEq]
      decide
  · exact Bool.eq_false_iff.mpr hPref

private theorem not_prefix_loop_dst (c : String)
    (hAbs : Internal.isAbsolute c = true) :
    (c.toList ++ ['/']).isPrefixOf "/loop_dst".toList = false := by
  by_cases hPref : (c.toList ++ ['/']).isPrefixOf "/loop_dst".toList = true
  · exfalso
    have hP := List.isPrefixOf_iff_prefix.mp hPref
    rcases hP with ⟨tail, hEq⟩
    cases hCl : c.toList with
    | nil => simp [Internal.isAbsolute, Internal.isAbsChars, hCl] at hAbs
    | cons c0 cs =>
      have hC0 : c0 = '/' := by
        have hI : Internal.isAbsChars (c0 :: cs) = true := hCl ▸ hAbs
        cases hEqS : (c0 == '/') with
        | true => exact beq_iff_eq.mp hEqS
        | false =>
          exfalso
          have : Internal.isAbsChars (c0 :: cs) = false := by
            unfold Internal.isAbsChars
            split
            · next h => cases h; simp at hEqS
            · rfl
          simp [this] at hI
      subst hC0
      have hTarget : "/loop_dst".toList = '/' :: "loop_dst".toList := by decide
      rw [hCl, hTarget, List.append_assoc] at hEq
      simp only [List.cons_append, List.cons.injEq, true_and] at hEq
      have hMem : '/' ∈ "loop_dst".toList := by
        rw [← hEq]; simp
      have hNotMem : '/' ∉ "loop_dst".toList := by decide
      exact hNotMem hMem
  · exact Bool.eq_false_iff.mpr hPref

private theorem lstat_root_child_none (s₀ : VfsState) (m : Nat) (seg : String)
    (hRoot : s₀.nodes "/" = some (.dir m))
    (hExec : ((m / 64) % 2 == 0) = false)
    (hSegs : vfsSplitSegs (vfsAbsNorm s₀.cwd ("/" ++ seg)) = [seg])
    (hChild : vfsChildPath "/" seg = "/" ++ seg)
    (hFail : ((vfsApi.lstat ("/" ++ seg)).run s₀).1.isOk = false) :
    s₀.nodes ("/" ++ seg) = none := by
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hFail
  rw [hSegs] at hFail
  cases hN : s₀.nodes ("/" ++ seg) with
  | none => rfl
  | some nd =>
    have hStep : vfsResolveSegs s₀.nodes "/" [seg] false 1024 = .ok ("/" ++ seg, nd) := by
      unfold vfsResolveSegs
      rw [hRoot]
      dsimp only
      rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, hChild]
      unfold vfsResolveSegs
      rw [hN]
      cases nd <;> rfl
    rw [hStep] at hFail
    simp [Except.isOk, Except.toBool] at hFail

private theorem copyTree_pre_checks_ok {S : Type} (ops : RawFsOpsM (StateM S))
    (src dst : String) (dirsExistOk : Bool) (s₀ : S) (stSrc : FileStat) (c dstCanon : String)
    (hStat : (ops.stat true src).run s₀ = (.ok stSrc, s₀))
    (hKind : stSrc.kind = .dir)
    (hRp : (ops.realPath src).run s₀ = (.ok c, s₀))
    (hAbsDst : Internal.isAbsolute dst = true)
    (hNormDst : Internal.normPath dst = dst)
    (hApprox : (Internal.resolveApproxGoM ops dst [] (dst.toList.length + 1)).run s₀ = (dstCanon, s₀))
    (hGuard : (dstCanon == c || c == "/" || (c.toList ++ ['/']).isPrefixOf dstCanon.toList) = false) :
    (Internal.copyTreeImplM ops src dst dirsExistOk).run s₀ =
      (Internal.copyTreeGoM ops src dst dirsExistOk [] 4096).run s₀ := by
  dsimp only [Internal.copyTreeImplM, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  rw [show ops.stat true src s₀ = (ops.stat true src).run s₀ from rfl, hStat]
  have hNotDirF : (stSrc.kind != .dir) = false := by rw [hKind]; decide
  simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
  dsimp only [Bind.bind, StateT.bind, StateT.pure]
  rw [show ops.realPath src s₀ = (ops.realPath src).run s₀ from rfl, hRp]
  simp only [hAbsDst, ↓reduceIte, hNormDst]
  dsimp only [Bind.bind, StateT.bind, StateT.pure]
  dsimp only [StateT.run] at hApprox
  rw [hApprox]
  simp [hGuard]
  dsimp only [Bind.bind, StateT.bind, StateT.pure]

/-- Proof of `test_fs_vfs_copyTree_createsMissingParents` on `vfsApi`. -/
theorem proof_fs_vfs_copyTree_createsMissingParents :
    AllPass (test_fs_vfs_copyTree_createsMissingParents vfsApi) := by
  intro s₀ src ⟨stRoot, hStatRoot, hRootKind, hRootW, hRootX, hResRoot⟩
    ⟨stSrc, hStatSrc, hSrcKind⟩ ⟨c, hResSrc, hCAbs, hCNeRoot, hCNeNP, hCNeCopy⟩
    hListSrc hLstatNP hStatNP hLstatCopy
  have hRootNode : s₀.nodes "/" = some (.dir stRoot.mode) :=
    vfsResolveSegs_abs_root_realPath s₀ stRoot hStatRoot hRootKind hResRoot
  have hExec : ((stRoot.mode / 64) % 2 == 0) = false := by
    have : (stRoot.mode / 64) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 64) % 2 == 0 <;> simp_all
  have hWrite : ((stRoot.mode / 128) % 2 == 0) = false := by
    have : (stRoot.mode / 128) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 128) % 2 == 0 <;> simp_all
  have hSegsNP : vfsSplitSegs (vfsAbsNorm s₀.cwd "/new_parent") = ["new_parent"] := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hNPNone : s₀.nodes "/new_parent" = none :=
    lstat_root_child_none s₀ stRoot.mode "new_parent" hRootNode hExec hSegsNP (by decide) hLstatNP
  have hCopyNone : s₀.nodes "/new_parent/copy" = none :=
    vfsTree_noOrphan_child s₀.tree hNPNone
  have hRpNPBad : vfsRealPathPure s₀ "/new_parent" =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsRealPathPure]
    rw [hSegsNP]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [hNPNone]; rfl
  have hSegsCopy : vfsSplitSegs (vfsAbsNorm s₀.cwd "/new_parent/copy") = ["new_parent", "copy"] := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hStatCopyBad : vfsStatPure s₀ false "/new_parent/copy" =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsStatPure]
    rw [hSegsCopy]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [hNPNone]; rfl
  have hRpCopyBad : vfsRealPathPure s₀ "/new_parent/copy" =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsRealPathPure]
    rw [hSegsCopy]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [hNPNone]; rfl
  have hParCopy : Internal.parent "/new_parent/copy" = some "/new_parent" := by decide
  have hNameCopy : Internal.name "/new_parent/copy" = some "copy" := by decide
  have hParNP : Internal.parent "/new_parent" = some "/" := by decide
  have hNameNP : Internal.name "/new_parent" = some "new_parent" := by decide
  have hApprox : (Internal.resolveApproxGoM vfsOps "/new_parent/copy" [] ("/new_parent/copy".toList.length + 1)).run s₀ =
      ("/new_parent/copy", s₀) := by
    rw [show ("/new_parent/copy".toList.length + 1) = 17 from by decide]
    unfold Internal.resolveApproxGoM
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.realPath "/new_parent/copy" s₀ = (vfsRealPathPure s₀ "/new_parent/copy", s₀) from rfl, hRpCopyBad]
    dsimp only; rw [hParCopy, hNameCopy]; dsimp only
    unfold Internal.resolveApproxGoM
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.realPath "/new_parent" s₀ = (vfsRealPathPure s₀ "/new_parent", s₀) from rfl, hRpNPBad]
    dsimp only; rw [hParNP, hNameNP]; dsimp only
    unfold Internal.resolveApproxGoM
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    have hRpR : vfsRealPathPure s₀ "/" = .ok "/" := hResRoot
    rw [show vfsOps.realPath "/" s₀ = (vfsRealPathPure s₀ "/", s₀) from rfl, hRpR]
    simp only [List.foldl_cons, List.foldl_nil]
    rfl
  have hGuard : ("/new_parent/copy" == c || c == "/" || (c.toList ++ ['/']).isPrefixOf "/new_parent/copy".toList) = false := by
    have h1 : ("/new_parent/copy" == c) = false := beq_false_of_ne (Ne.symm hCNeCopy)
    have h2 : (c == "/") = false := beq_false_of_ne hCNeRoot
    have h3 := not_prefix_new_parent_copy c hCAbs hCNeNP
    simp [h1, h2, h3]
  have hStatS0 : (vfsOps.stat true src).run s₀ = (.ok stSrc, s₀) := by
    change (vfsStatPure s₀ true src, s₀) = (.ok stSrc, s₀)
    rw [show vfsStatPure s₀ true src = .ok stSrc from hStatSrc]
  have hRpS0 : (vfsOps.realPath src).run s₀ = (.ok c, s₀) := by
    change (vfsRealPathPure s₀ src, s₀) = (.ok c, s₀)
    rw [show vfsRealPathPure s₀ src = .ok c from hResSrc]
  have hPre := copyTree_pre_checks_ok vfsOps src "/new_parent/copy" false s₀ stSrc c "/new_parent/copy"
    hStatS0 hSrcKind hRpS0 (by decide) (by decide) hApprox hGuard
  let st₁ : VfsState :=
    { s₀ with
      tree := vfsTreeSet s₀.tree ["new_parent"] (some (vfsEmptyDir 0o755))
      keys := "/new_parent" :: s₀.keys }
  let st₂ : VfsState :=
    { st₁ with
      tree := vfsTreeSet st₁.tree ["new_parent", "copy"] (some (vfsEmptyDir 0o755))
      keys := "/new_parent/copy" :: st₁.keys }
  have hSt1Nodes : st₁.nodes = fun k => if k == "/new_parent" then some (.dir 0o755) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath "/" "new_parent")) (some (vfsEmptyDir 0o755))) = _
    exact vfsTreeSet_emptyDir_nodes_root_child s₀.tree "new_parent" ⟨stRoot.mode, hRootNode⟩ (by decide) hNPNone
  have hSt1Root : st₁.nodes "/" = some (.dir stRoot.mode) := by
    rw [hSt1Nodes]; simp [hRootNode]
  have hSt1NP : st₁.nodes "/new_parent" = some (.dir 0o755) := by
    rw [hSt1Nodes]; simp
  have hSt1CopyNone : st₁.nodes "/new_parent/copy" = none := by
    rw [hSt1Nodes]; simp [hCopyNone]
  have hSt2Nodes : st₂.nodes = fun k => if k == "/new_parent/copy" then some (.dir 0o755) else st₁.nodes k := by
    change vfsTreeNodes (vfsTreeSet st₁.tree (vfsSplitSegs (vfsChildPath "/new_parent" "copy")) (some (vfsEmptyDir 0o755))) = _
    exact vfsTreeNodes_insert_dir st₁.tree "/new_parent" "copy" (by decide) (by decide) ⟨0o755, hSt1NP⟩ hSt1CopyNone
  have hCreNP : vfsCreateDirPure s₀ "/new_parent" = (.ok (), st₁) := by
    have hAbs : vfsAbsNorm s₀.cwd "/new_parent" = "/new_parent" := vfsAbsNorm_abs _ _ (by decide)
    have hPar : Internal.splitLastAux ["new_parent"] [] = some ([], "new_parent") := by decide
    have hPreNP : vfsResolveSegs s₀.nodes "/" ["new_parent"] false 1024 =
        .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
      unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hNPNone]; rfl
    have hParRoot : vfsResolveSegs s₀.nodes "/" [] true 512 = .ok ("/", .dir stRoot.mode) := by
      unfold vfsResolveSegs; rw [hRootNode]
    dsimp only [vfsCreateDirPure]
    rw [hAbs, show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide, hPreNP]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]; dsimp only; rw [hParRoot]; dsimp only
    rw [show (stRoot.mode / 128 % 2 == 0 || stRoot.mode / 64 % 2 == 0) = false from by simp [hWrite, hExec]]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    rw [hNPNone]
    simp [st₁, show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide]
  have hCreCopy : vfsCreateDirPure st₁ "/new_parent/copy" = (.ok (), st₂) := by
    have hAbs : vfsAbsNorm st₁.cwd "/new_parent/copy" = "/new_parent/copy" := vfsAbsNorm_abs _ _ (by decide)
    have hPar : Internal.splitLastAux ["new_parent", "copy"] [] = some (["new_parent"], "copy") := by decide
    have hPreC : vfsResolveSegs st₁.nodes "/" ["new_parent", "copy"] false 1024 =
        .error { kind := .notFound, path := some "/new_parent/copy", message := "no such file or directory: /new_parent/copy" } := by
      unfold vfsResolveSegs; rw [hSt1Root]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hSt1NP]; dsimp only
      rw [show (0o755 / 64 % 2 == 0) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/new_parent" "copy" = "/new_parent/copy" from by decide]
      unfold vfsResolveSegs; rw [hSt1CopyNone]; rfl
    have hParNP' : vfsResolveSegs st₁.nodes "/" ["new_parent"] true 512 = .ok ("/new_parent", .dir 0o755) := by
      unfold vfsResolveSegs; rw [hSt1Root]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hSt1NP]
    dsimp only [vfsCreateDirPure]
    rw [hAbs, show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide, hPreC]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]; dsimp only; rw [hParNP']; dsimp only
    rw [show (0o755 / 128 % 2 == 0 || 0o755 / 64 % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/new_parent" "copy" = "/new_parent/copy" from by decide]
    rw [hSt1CopyNone]
    simp [st₂, show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide]
  have hMkDst : Internal.mkdirImplM vfsOps "/new_parent/copy" true false s₀ = (.ok (), st₂) := by
    dsimp only [Internal.mkdirImplM, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/new_parent/copy" s₀ = (vfsStatPure s₀ false "/new_parent/copy", s₀) from rfl, hStatCopyBad]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rw [show Internal.ancestorChain "/new_parent/copy" "/new_parent/copy".toList.length = ["/new_parent"] from by decide]
    have hStatNPBad : vfsStatPure s₀ true "/new_parent" =
        .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
      dsimp only [vfsStatPure]
      rw [hSegsNP]
      unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hNPNone]; rfl
    have hAnc : Internal.ensureAncestorsM vfsOps ["/new_parent"] s₀ = (.ok (), st₁) := by
      dsimp only [Internal.ensureAncestorsM, Internal.ensureDirM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
      rw [show vfsOps.stat true "/new_parent" s₀ = (vfsStatPure s₀ true "/new_parent", s₀) from rfl, hStatNPBad]
      dsimp only
      rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, StateT.bind, StateT.pure]
      rw [show vfsOps.createDir "/new_parent" s₀ = vfsCreateDirPure s₀ "/new_parent" from rfl, hCreNP]
      rfl
    have hBindAnc :
        StateT.bind (Internal.ensureAncestorsM vfsOps ["/new_parent"])
          (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/new_parent/copy") s₀ =
        vfsOps.createDir "/new_parent/copy" st₁ := by
      dsimp only [Bind.bind, StateT.bind]
      rw [hAnc]
    change (StateT.bind (Internal.ensureAncestorsM vfsOps ["/new_parent"])
      (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/new_parent/copy") s₀) = (.ok (), st₂)
    rw [hBindAnc]
    exact hCreCopy
  have hCopyExec : (Internal.copyTreeImplM vfsOps src "/new_parent/copy" false).run s₀ = (.ok (), st₂) := by
    rw [hPre]
    unfold Internal.copyTreeGoM
    dsimp only [StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true src s₀ = (vfsStatPure s₀ true src, s₀) from rfl]
    have hVfsStatSrc : vfsStatPure s₀ true src = .ok stSrc := hStatSrc
    rw [hVfsStatSrc]
    have hNotDirF : (stSrc.kind != .dir) = false := by rw [hSrcKind]; decide
    simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath src s₀ = (vfsRealPathPure s₀ src, s₀) from rfl]
    have hVfsRpSrc : vfsRealPathPure s₀ src = .ok c := hResSrc
    rw [hVfsRpSrc]
    simp only [List.mem_nil_iff, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    have hListEq : Internal.listDirSortedM vfsOps src s₀ = (.ok #[], s₀) := by
      dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hListSrc ⊢
      cases hRd : vfsReadDirPure s₀ src with
      | error _ =>
        simp [hRd, StateT.pure] at hListSrc
      | ok arr =>
        simp only [hRd] at hListSrc
        dsimp only [StateT.pure, Pure.pure, pure] at hListSrc ⊢
        simp only [Except.ok.injEq] at hListSrc
        rw [hListSrc]
    rw [hListEq]
    dsimp only [StateT.bind]
    rw [hMkDst]
    dsimp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  have hIsDirNP : ((vfsApi.isDir "/new_parent").run st₂).1 = .ok true := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run, bind, StateT.bind, pure, StateT.pure]
    have hResNP : vfsResolveSegs st₂.nodes "/" (vfsSplitSegs (vfsAbsNorm st₂.cwd "/new_parent")) true 1024 =
        .ok ("/new_parent", .dir 0o755) := by
      have hSegs : vfsSplitSegs (vfsAbsNorm st₂.cwd "/new_parent") = ["new_parent"] := by
        rw [vfsAbsNorm_abs _ _ (by decide)]; decide
      rw [hSegs]
      unfold vfsResolveSegs
      have hSt2Root : st₂.nodes "/" = some (.dir stRoot.mode) := by
        rw [hSt2Nodes]; simp [hSt1Root]
      have hSt2NP : st₂.nodes "/new_parent" = some (.dir 0o755) := by
        rw [hSt2Nodes]; simp [hSt1NP]
      rw [hSt2Root]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
      unfold vfsResolveSegs; rw [hSt2NP]
    rw [hResNP]; rfl
  have hIsDirCopy : ((vfsApi.isDir "/new_parent/copy").run st₂).1 = .ok true := by
    change ((vfsApi.isDir "/new_parent/copy").run st₂).1 = .ok true
    exact vfsCreateDir_sets_isDir "/new_parent/copy" st₁ st₂ hCreCopy
  dsimp only [vfsApi, Internal.mkApiM]
  rw [hCopyExec]
  exact ⟨⟨rfl, hIsDirNP, hIsDirCopy⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_copyTree_createsMissingParents`. -/
theorem reach_fs_vfs_copyTree_createsMissingParents :
    CanReach (test_fs_vfs_copyTree_createsMissingParents vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hStatRoot : ((vfsApi.stat "/").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hResRoot : ((vfsApi.resolve "/").run st).1 = .ok "/" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hListSrc : ((vfsApi.listDir "/src").run st).1 = .ok #[] := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, Bool.true_and, Bool.false_and, List.mergeSort_nil]
  have hLstatNP : ((vfsApi.lstat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/new_parent" = "/new_parent" := by decide
    have hS : vfsSplitSegs "/new_parent" = ["new_parent"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hStatNP : ((vfsApi.stat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/new_parent" = "/new_parent" := by decide
    have hS : vfsSplitSegs "/new_parent" = ["new_parent"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hLstatCopy : ((vfsApi.lstat "/new_parent/copy").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/new_parent/copy" = "/new_parent/copy" := by decide
    have hS : vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  exact ⟨st, "/src",
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩,
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, by decide, by decide⟩,
    hListSrc, hLstatNP, hStatNP, hLstatCopy,
    proof_fs_vfs_copyTree_createsMissingParents st "/src"
      ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩
      ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
      ⟨"/src", hResSrc, by decide, by decide, by decide, by decide⟩
      hListSrc hLstatNP hStatNP hLstatCopy⟩

/-- Proof of `test_fs_vfs_copyTree_loopRejected` on `vfsApi`. -/
theorem proof_fs_vfs_copyTree_loopRejected :
    AllPass (test_fs_vfs_copyTree_loopRejected vfsApi) := by
  intro s₀ src ⟨stRoot, hStatRoot, hRootKind, hRootW, hRootX, hResRoot⟩
    ⟨stSrc, hStatSrc, hSrcKind⟩ ⟨c, hResSrc, hCAbs, hCNeRoot, hCNeLoop, hResSelf⟩
    hListSrc ⟨stSelf, hStatSelf, hSelfKind⟩ hLstatLoop
  have hRootNode : s₀.nodes "/" = some (.dir stRoot.mode) :=
    vfsResolveSegs_abs_root_realPath s₀ stRoot hStatRoot hRootKind hResRoot
  have hExec : ((stRoot.mode / 64) % 2 == 0) = false := by
    have : (stRoot.mode / 64) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 64) % 2 == 0 <;> simp_all
  have hWrite : ((stRoot.mode / 128) % 2 == 0) = false := by
    have : (stRoot.mode / 128) % 2 ≠ 0 := by omega
    cases hb : (stRoot.mode / 128) % 2 == 0 <;> simp_all
  have hSegsLoop : vfsSplitSegs (vfsAbsNorm s₀.cwd "/loop_dst") = ["loop_dst"] := by
    rw [vfsAbsNorm_abs _ _ (by decide)]; decide
  have hLoopNone : s₀.nodes "/loop_dst" = none :=
    lstat_root_child_none s₀ stRoot.mode "loop_dst" hRootNode hExec hSegsLoop (by decide) hLstatLoop
  have hRpLoopBad : vfsRealPathPure s₀ "/loop_dst" =
      .error { kind := .notFound, path := some "/loop_dst", message := "no such file or directory: /loop_dst" } := by
    dsimp only [vfsRealPathPure]
    rw [hSegsLoop]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    unfold vfsResolveSegs; rw [hLoopNone]; rfl
  have hStatLoopBad : vfsStatPure s₀ false "/loop_dst" =
      .error { kind := .notFound, path := some "/loop_dst", message := "no such file or directory: /loop_dst" } := by
    dsimp only [vfsStatPure]
    rw [hSegsLoop]
    unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    unfold vfsResolveSegs; rw [hLoopNone]; rfl
  have hApprox : (Internal.resolveApproxGoM vfsOps "/loop_dst" [] ("/loop_dst".toList.length + 1)).run s₀ =
      ("/loop_dst", s₀) := by
    rw [show ("/loop_dst".toList.length + 1) = 10 from by decide]
    unfold Internal.resolveApproxGoM
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.realPath "/loop_dst" s₀ = (vfsRealPathPure s₀ "/loop_dst", s₀) from rfl, hRpLoopBad]
    dsimp only
    rw [show Internal.parent "/loop_dst" = some "/" from by decide,
        show Internal.name "/loop_dst" = some "loop_dst" from by decide]
    dsimp only
    unfold Internal.resolveApproxGoM
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    have hRpR : vfsRealPathPure s₀ "/" = .ok "/" := hResRoot
    rw [show vfsOps.realPath "/" s₀ = (vfsRealPathPure s₀ "/", s₀) from rfl, hRpR]
    simp only [List.foldl_cons, List.foldl_nil]
    rfl
  have hGuard : ("/loop_dst" == c || c == "/" || (c.toList ++ ['/']).isPrefixOf "/loop_dst".toList) = false := by
    have h1 : ("/loop_dst" == c) = false := beq_false_of_ne (Ne.symm hCNeLoop)
    have h2 : (c == "/") = false := beq_false_of_ne hCNeRoot
    have h3 := not_prefix_loop_dst c hCAbs
    simp [h1, h2, h3]
  have hStatS0 : (vfsOps.stat true src).run s₀ = (.ok stSrc, s₀) := by
    change (vfsStatPure s₀ true src, s₀) = (.ok stSrc, s₀)
    rw [show vfsStatPure s₀ true src = .ok stSrc from hStatSrc]
  have hRpS0 : (vfsOps.realPath src).run s₀ = (.ok c, s₀) := by
    change (vfsRealPathPure s₀ src, s₀) = (.ok c, s₀)
    rw [show vfsRealPathPure s₀ src = .ok c from hResSrc]
  have hPre := copyTree_pre_checks_ok vfsOps src "/loop_dst" false s₀ stSrc c "/loop_dst"
    hStatS0 hSrcKind hRpS0 (by decide) (by decide) hApprox hGuard
  have hListEq : (Internal.listDirSortedM vfsOps src).run s₀ = (.ok #["self"], s₀) := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hListSrc ⊢
    cases hRd : vfsReadDirPure s₀ src with
    | error _ =>
      simp [hRd, StateT.pure] at hListSrc
    | ok arr =>
      simp only [hRd] at hListSrc
      dsimp only [StateT.pure, Pure.pure, pure] at hListSrc ⊢
      simp only [Except.ok.injEq] at hListSrc
      rw [hListSrc]
  dsimp only [StateT.run] at hListEq
  let st₁ : VfsState :=
    { s₀ with
      tree := vfsTreeSet s₀.tree ["loop_dst"] (some (vfsEmptyDir 0o755))
      keys := "/loop_dst" :: s₀.keys }
  have hSt1Nodes : st₁.nodes = fun k => if k == "/loop_dst" then some (.dir 0o755) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath "/" "loop_dst")) (some (vfsEmptyDir 0o755))) = _
    exact vfsTreeSet_emptyDir_nodes_root_child s₀.tree "loop_dst" ⟨stRoot.mode, hRootNode⟩ (by decide) hLoopNone
  have hCreLoop : vfsCreateDirPure s₀ "/loop_dst" = (.ok (), st₁) := by
    have hAbs : vfsAbsNorm s₀.cwd "/loop_dst" = "/loop_dst" := vfsAbsNorm_abs _ _ (by decide)
    have hPar : Internal.splitLastAux ["loop_dst"] [] = some ([], "loop_dst") := by decide
    have hPreL : vfsResolveSegs s₀.nodes "/" ["loop_dst"] false 1024 =
        .error { kind := .notFound, path := some "/loop_dst", message := "no such file or directory: /loop_dst" } := by
      unfold vfsResolveSegs; rw [hRootNode]; dsimp only; rw [hExec]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
      unfold vfsResolveSegs; rw [hLoopNone]; rfl
    have hParRoot : vfsResolveSegs s₀.nodes "/" [] true 512 = .ok ("/", .dir stRoot.mode) := by
      unfold vfsResolveSegs; rw [hRootNode]
    dsimp only [vfsCreateDirPure]
    rw [hAbs, show vfsSplitSegs "/loop_dst" = ["loop_dst"] from by decide, hPreL]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hPar]; dsimp only; rw [hParRoot]; dsimp only
    rw [show (stRoot.mode / 128 % 2 == 0 || stRoot.mode / 64 % 2 == 0) = false from by simp [hWrite, hExec]]
    simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    rw [hLoopNone]
    simp [st₁, show vfsSplitSegs "/loop_dst" = ["loop_dst"] from by decide]
  have hMkLoop : Internal.mkdirImplM vfsOps "/loop_dst" true false s₀ = (.ok (), st₁) := by
    dsimp only [Internal.mkdirImplM, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/loop_dst" s₀ = (vfsStatPure s₀ false "/loop_dst", s₀) from rfl, hStatLoopBad]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rw [show Internal.ancestorChain "/loop_dst" "/loop_dst".toList.length = [] from by decide]
    change StateT.bind (Internal.ensureAncestorsM vfsOps [])
      (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/loop_dst") s₀ = (.ok (), st₁)
    have hAncNil : Internal.ensureAncestorsM vfsOps [] s₀ = (.ok (), s₀) := rfl
    simp [StateT.bind, hAncNil]
    exact hCreLoop
  have hSelfStatSt1 : vfsStatPure st₁ true (Internal.join src "self") = .ok stSelf := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hStatSelf ⊢
    cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true 1024 with
    | error _ => simp [hR] at hStatSelf
    | ok p =>
      have hPres := vfsResolveSegs_insert_fresh s₀.nodes "/loop_dst" (.dir 0o755) hLoopNone
        1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true p hR
      dsimp only [st₁]
      rw [hSt1Nodes, hPres]
      simpa [hR] using hStatSelf
  have hSelfRpSt1 : vfsRealPathPure st₁ (Internal.join src "self") = .ok c := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run] at hResSelf ⊢
    cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true 1024 with
    | error _ => simp [hR] at hResSelf
    | ok p =>
      have hPres := vfsResolveSegs_insert_fresh s₀.nodes "/loop_dst" (.dir 0o755) hLoopNone
        1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd (Internal.join src "self"))) true p hR
      dsimp only [st₁]
      rw [hSt1Nodes, hPres]
      simpa [hR] using hResSelf
  have hCopyExec : (Internal.copyTreeImplM vfsOps src "/loop_dst" false).run s₀ =
      (.error { kind := .invalidInput, path := some (Internal.join src "self"), message := s!"symlink directory loop: {Internal.join src "self"}" }, st₁) := by
    rw [hPre]
    unfold Internal.copyTreeGoM
    dsimp only [StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true src s₀ = (vfsStatPure s₀ true src, s₀) from rfl]
    have hVfsStatSrc : vfsStatPure s₀ true src = .ok stSrc := hStatSrc
    rw [hVfsStatSrc]
    have hNotDirF : (stSrc.kind != .dir) = false := by rw [hSrcKind]; decide
    simp only [hNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath src s₀ = (vfsRealPathPure s₀ src, s₀) from rfl]
    have hVfsRpSrc : vfsRealPathPure s₀ src = .ok c := hResSrc
    rw [hVfsRpSrc]
    simp only [List.mem_nil_iff, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [hListEq]
    dsimp only [StateT.bind]
    rw [hMkLoop]
    dsimp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true (Internal.join src "self") st₁ = (vfsStatPure st₁ true (Internal.join src "self"), st₁) from rfl,
        hSelfStatSt1]
    dsimp only
    have hSelfNotDirF : (stSelf.kind != .dir) = false := by rw [hSelfKind]; decide
    rw [show (stSelf.kind == .dir) = true from by rw [hSelfKind]; decide]
    simp only [↓reduceIte]
    unfold Internal.copyTreeGoM
    dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true (Internal.join src "self") st₁ = (vfsStatPure st₁ true (Internal.join src "self"), st₁) from rfl,
        hSelfStatSt1]
    simp only [hSelfNotDirF, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath (Internal.join src "self") st₁ = (vfsRealPathPure st₁ (Internal.join src "self"), st₁) from rfl,
        hSelfRpSt1]
    simp only [List.mem_singleton, ↓reduceIte]
    rfl
  dsimp only [vfsApi, Internal.mkApiM]
  rw [hCopyExec]
  exact ⟨⟨_, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_copyTree_loopRejected`. -/
theorem reach_fs_vfs_copyTree_loopRejected :
    CanReach (test_fs_vfs_copyTree_loopRejected vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s =>
        if s == "src" then
          some (.dir 0o755 (fun s2 => if s2 == "self" then some (.symlink "/src" 0o777) else none))
        else none)
      keys := ["/", "/src", "/src/self"]
      cwd := "/"
      nonce := 0 }
  have hStatRoot : ((vfsApi.stat "/").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hResRoot : ((vfsApi.resolve "/").run st).1 = .ok "/" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/" = "/" := by decide
    have hS : vfsSplitSegs "/" = [] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hSelfResolve : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (vfsApi.join "/src" "self"))) true 1024 =
      .ok ("/src", .dir 0o755) := by
    have hJ : vfsApi.join "/src" "self" = "/src/self" := by decide
    have hA : vfsAbsNorm st.cwd "/src/self" = "/src/self" := by decide
    have hS : vfsSplitSegs "/src/self" = ["src", "self"] := by decide
    have hS_src : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hJ, hA, hS]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/src" "self" = "/src/self" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src/self" = some (.symlink "/src" 0o777) from rfl]; dsimp only
    rw [show ((Internal.parent "/src/self").getD "/") = "/src" from by decide,
        show Internal.isAbsolute "/src" = true from by decide]
    simp only [↓reduceIte, show Internal.normPath "/src" = "/src" from by decide, hS_src]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSelf : ((vfsApi.resolve (vfsApi.join "/src" "self")).run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    have hSelf : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (Internal.join "/src" "self"))) true 1024 =
        .ok ("/src", .dir 0o755) := hSelfResolve
    rw [hSelf]
  have hStatSelf : ((vfsApi.stat (vfsApi.join "/src" "self")).run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hSelf : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd (Internal.join "/src" "self"))) true 1024 =
        .ok ("/src", .dir 0o755) := hSelfResolve
    rw [hSelf]
  have hListSrc : ((vfsApi.listDir "/src").run st).1 = .ok #["self"] := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure]
    have hA : vfsAbsNorm st.cwd "/src" = "/src" := by decide
    have hS : vfsSplitSegs "/src" = ["src"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src", "/src/self"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hN2 : (st.nodes "/src/self").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    have hPre2 : "/src/".toList.isPrefixOf "/src/self".toList = true := by decide
    have hDrop2 : "/src/self".toList.drop "/src/".toList.length = "self".toList := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, hN2, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src/self" != "/src") = true from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, hPre2, hDrop2,
      show (!"self".toList.isEmpty && !('/' ∈ "self".toList)) = true from by decide,
      show String.ofList "self".toList = "self" from by decide,
      Bool.true_and, Bool.false_and, List.mergeSort_singleton]
  have hLstatLoop : ((vfsApi.lstat "/loop_dst").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    have hA : vfsAbsNorm st.cwd "/loop_dst" = "/loop_dst" := by decide
    have hS : vfsSplitSegs "/loop_dst" = ["loop_dst"] := by decide
    rw [hA, hS]; unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "loop_dst" = "/loop_dst" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/loop_dst" = none from rfl]; rfl
  exact ⟨st, "/src",
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩,
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, by decide, hResSelf⟩,
    hListSrc, ⟨vfsToStat (.dir 0o755), hStatSelf, rfl⟩, hLstatLoop,
    proof_fs_vfs_copyTree_loopRejected st "/src"
      ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩
      ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
      ⟨"/src", hResSrc, by decide, by decide, by decide, hResSelf⟩
      hListSrc ⟨vfsToStat (.dir 0o755), hStatSelf, rfl⟩ hLstatLoop⟩

private def buggyMkdirR1I01 (path : String) (parents existOk : Bool) : StateM VfsState (Except FsError Unit) := do
  if !parents then
    Internal.mkdirImplM vfsOps path parents existOk
  else
    let ancs := Internal.ancestorChain path path.toList.length
    match ← Internal.ensureAncestorsM vfsOps ancs with
    | .error ae => return .error ae
    | .ok () =>
      match ← vfsOps.createDir path with
      | .ok () => return .ok ()
      | .error e => if e.kind == .alreadyExists then return .ok () else return .error e

example : ¬ AllPass (test_fs_vfs_mkdir_existingFails { vfsApi with mkdir := buggyMkdirR1I01 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  have hFail := h st "/broken" true vfsLstat_broken_symlink
  dsimp only [buggyMkdirR1I01, bind, StateT.bind, pure, StateT.pure] at hFail
  have hChain : Internal.ancestorChain "/broken" "/broken".toList.length = [] := by decide
  rw [hChain] at hFail
  have hCre : vfsCreateDirPure st "/broken" =
      (.error { kind := .alreadyExists, path := some "/broken", message := "already exists: /broken" }, st) := by
    have hAbs : vfsAbsNorm "/" "/broken" = "/broken" := by decide
    have hSegs : vfsSplitSegs "/broken" = ["broken"] := by decide
    have hRes : vfsResolveSegs st.nodes "/" ["broken"] false 1024 = .ok ("/broken", .symlink "/nope" 0o777) := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show vfsChildPath "/" "broken" = "/broken" from by decide]
      unfold vfsResolveSegs; rw [show st.nodes "/broken" = some (.symlink "/nope" 0o777) from rfl]; rfl
    dsimp only [vfsCreateDirPure]
    rw [show st.cwd = "/" from rfl, hAbs, hSegs, hRes]
    rfl
  change (match ((do
    let x ← Internal.ensureAncestorsM vfsOps []
    match x with
    | .error ae => return .error ae
    | .ok () =>
      match ← vfsOps.createDir "/broken" with
      | .ok () => return .ok ()
      | .error (e : FsError) =>
        if e.kind == .alreadyExists then return .ok () else return .error e :
          StateM VfsState (Except FsError Unit)).run st) with
    | (res, _) => _) at hFail
  have hAnc : Internal.ensureAncestorsM vfsOps [] st = (.ok (), st) := rfl
  simp only [StateT.run, bind, StateT.bind, pure, hAnc,
    show vfsOps.createDir "/broken" st = vfsCreateDirPure st "/broken" from rfl, hCre, assert] at hFail
  rcases hFail with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

private def buggyCopyTreeR1I02 (src dst : String) (dirsExistOk : Bool) : StateM VfsState (Except FsError Unit) := do
  match ← vfsOps.stat true src with
  | .error e => return .error e
  | .ok st =>
    if st.kind != .dir then
      return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
    Internal.mkdirImplM vfsOps dst false dirsExistOk

example : ¬ AllPass (test_fs_vfs_copyTree_createsMissingParents { vfsApi with copyTree := buggyCopyTreeR1I02 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hStatRoot : ((vfsApi.stat "/").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/" = "/" from by decide,
        show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hResRoot : ((vfsApi.resolve "/").run st).1 = .ok "/" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/" = "/" from by decide,
        show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hListSrc : ((vfsApi.listDir "/src").run st).1 = .ok #[] := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run,
      bind, StateT.bind, pure, StateT.pure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, Bool.true_and, Bool.false_and, List.mergeSort_nil]
  have hLstatNP : ((vfsApi.lstat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent" = "/new_parent" from by decide,
        show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hStatNP : ((vfsApi.stat "/new_parent").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent" = "/new_parent" from by decide,
        show vfsSplitSegs "/new_parent" = ["new_parent"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hLstatCopy : ((vfsApi.lstat "/new_parent/copy").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent/copy" = "/new_parent/copy" from by decide,
        show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hFail := h st "/src"
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
    ⟨"/src", hResSrc, by decide, by decide, by decide, by decide⟩
    hListSrc hLstatNP hStatNP hLstatCopy
  have hPreCopy : vfsResolveSegs st.nodes "/" ["new_parent", "copy"] false 1024 =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hParNP : vfsResolveSegs st.nodes "/" ["new_parent"] true 512 =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new_parent" = "/new_parent" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new_parent" = none from rfl]; rfl
  have hCreFail : (vfsCreateDirPure st "/new_parent/copy").1 =
      .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
    dsimp only [vfsCreateDirPure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent/copy" = "/new_parent/copy" from by decide,
        show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide, hPreCopy]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show Internal.splitLastAux ["new_parent", "copy"] [] = some (["new_parent"], "copy") from by decide]
    dsimp only
    rw [hParNP]
  dsimp only [buggyCopyTreeR1I02, Internal.mkdirImplM, StateT.run, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hFail
  have hVS : vfsOps.stat true "/src" st = (.ok (vfsToStat (.dir 0o755)), st) := by
    change (vfsStatPure st true "/src", st) = _
    rw [show vfsStatPure st true "/src" = .ok (vfsToStat (.dir 0o755)) from hStatSrc]
  rw [hVS] at hFail
  dsimp only at hFail
  rw [show ((vfsToStat (.dir 0o755)).kind != .dir) = false from by decide] at hFail
  simp only [Bool.false_eq_true, ↓reduceIte] at hFail
  dsimp only [Bind.bind, StateT.bind, StateT.pure] at hFail
  have hStCopy : vfsOps.stat false "/new_parent/copy" st =
      (.error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" }, st) := by
    dsimp only [vfsOps, vfsStatPure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new_parent/copy" = "/new_parent/copy" from by decide,
        show vfsSplitSegs "/new_parent/copy" = ["new_parent", "copy"] from by decide, hPreCopy]
  rw [hStCopy] at hFail
  dsimp only at hFail
  rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide] at hFail
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hFail
  change (match (vfsCreateDirPure st "/new_parent/copy") with | (res, s₁) => _) at hFail
  dsimp only [vfsOps] at hFail
  cases hC : vfsCreateDirPure st "/new_parent/copy" with
  | mk res _ =>
    rw [hC] at hFail
    have hEq : res = .error { kind := .notFound, path := some "/new_parent", message := "no such file or directory: /new_parent" } := by
      simpa [hC] using hCreFail
    simp [hEq, assert] at hFail

private def buggyTouchR1I03 (path : String) (existOk : Bool) : StateM VfsState (Except FsError Unit) := do
  match ← vfsOps.stat true path with
  | .ok st =>
    if !existOk then
      return .error { kind := .alreadyExists, path := some path, message := s!"file already exists: {path}" }
    else if st.kind == .dir then
      return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    else
      vfsOps.appendText path ""
  | .error e =>
    if e.kind == .notFound then
      vfsOps.writeBytes path ByteArray.empty
    else
      return .error e

example : ¬ AllPass (test_fs_vfs_touch_existingFails { vfsApi with touch := buggyTouchR1I03 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "broken" then some (.symlink "/nope" 0o777) else none)
      keys := ["/", "/broken"]
      cwd := "/"
      nonce := 0 }
  have hFail := h st "/broken" vfsLstat_broken_symlink
  have hFollowRes : vfsResolveSegs st.nodes "/" ["broken"] true 1024 =
      .error { kind := .notFound, path := some "/nope", message := "no such file or directory: /nope" } := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "broken" = "/broken" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/broken" = some (.symlink "/nope" 0o777) from rfl]; dsimp only
    rw [show ((Internal.parent "/broken").getD "/") = "/" from by decide,
        show Internal.isAbsolute "/nope" = true from by decide]
    simp only [↓reduceIte, show Internal.normPath "/nope" = "/nope" from by decide,
      show vfsSplitSegs "/nope" = ["nope"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "nope" = "/nope" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/nope" = none from rfl]; rfl
  have hStatFollow : vfsStatPure st true "/broken" =
      .error { kind := .notFound, path := some "/nope", message := "no such file or directory: /nope" } := by
    dsimp only [vfsStatPure]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/broken" = "/broken" from by decide,
        show vfsSplitSegs "/broken" = ["broken"] from by decide,
        hFollowRes]
  have hWb : (vfsWriteBytesPure st "/broken" ByteArray.empty).1 = .ok () := by
    dsimp only [vfsWriteBytesPure]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/broken" = "/broken" from by decide,
        show vfsSplitSegs "/broken" = ["broken"] from by decide,
        show Internal.splitLastAux ["broken"] [] = some ([], "broken") from by decide]
    dsimp only
    have hRootR : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
    rw [hRootR]; dsimp only
    rw [show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte,
      show vfsChildPath "/" "broken" = "/broken" from by decide, hFollowRes]
  dsimp only [vfsApi, Internal.mkApiM, buggyTouchR1I03, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at hFail
  rw [show vfsOps.stat true "/broken" st = (vfsStatPure st true "/broken", st) from rfl, hStatFollow] at hFail
  dsimp only at hFail
  rw [show (Raw.FsErrorKind.notFound == Raw.FsErrorKind.notFound) = true from by decide] at hFail
  simp only [↓reduceIte] at hFail
  rw [show vfsOps.writeBytes "/broken" ByteArray.empty st = vfsWriteBytesPure st "/broken" ByteArray.empty from rfl] at hFail
  cases hW : vfsWriteBytesPure st "/broken" ByteArray.empty with
  | mk res _ =>
    rw [hW] at hFail
    have hOkW : res = .ok () := by simpa [hW] using hWb
    rcases hFail with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
    rw [hOkW] at he
    cases he

private def buggyCopyTreeGoNoLoopM (src dst : String) (dirsExistOk : Bool) : Nat → StateM VfsState (Except FsError Unit)
  | 0 => return .error { kind := .ioError, path := some src, message := s!"maximum directory depth exceeded: {src}" }
  | fuel + 1 => do
    match ← vfsOps.stat true src with
    | .error e => return .error e
    | .ok st =>
      if st.kind != .dir then
        return .error { kind := .notADirectory, path := some src, message := s!"not a directory: {src}" }
      match ← vfsOps.realPath src with
      | .error e => return .error e
      | .ok _ =>
        match ← Internal.listDirSortedM vfsOps src with
        | .error e => return .error e
        | .ok names =>
          match ← Internal.mkdirImplM vfsOps dst true dirsExistOk with
          | .error e => return .error e
          | .ok () =>
            Internal.forEachChildM (fun n => do
              let sChild := Internal.join src n
              let dChild := Internal.join dst n
              match ← vfsOps.stat true sChild with
              | .error e => return .error e
              | .ok childSt =>
                if childSt.kind == .dir then
                  buggyCopyTreeGoNoLoopM sChild dChild dirsExistOk fuel
                else
                  match ← vfsOps.readBytes sChild with
                  | .error e => return .error e
                  | .ok bs => vfsOps.writeBytes dChild bs) names.toList

private theorem vfsResolveSegs_never_invalidInput (nodes : String → Option VfsNode) :
    ∀ fuel cur segs follow e, vfsResolveSegs nodes cur segs follow fuel = .error e → e.kind ≠ .invalidInput := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ h; simp [vfsResolveSegs] at h; cases h; intro hk; cases hk
  | succ fuel ih =>
    intro cur segs follow e h
    simp only [vfsResolveSegs] at h
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at h; cases h; intro hk; cases hk
      | some nd =>
        simp only [hNd] at h
        cases nd with
        | file _ _ => simp at h
        | dir _ => simp at h
        | symlink _ _ => cases follow <;> simp at h; exact ih _ _ _ _ h
    | cons _ _ =>
      cases hNd : nodes cur with
      | none => simp [hNd] at h; cases h; intro hk; cases hk
      | some nd =>
        simp only [hNd] at h
        cases nd with
        | file _ _ => simp at h; cases h; intro hk; cases hk
        | symlink _ _ => exact ih _ _ _ _ h
        | dir mode =>
          by_cases hm : ((mode / 64) % 2 == 0) = true
          · simp [hm] at h; cases h; intro hk; cases hk
          · have hmf : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at h
            exact ih _ _ _ _ h

private theorem vfsOps_mkdir_never_invalidInput (path : String) (parents existOk : Bool) (st : VfsState) (e : FsError)
    (hErr : (Internal.mkdirImplM vfsOps path parents existOk st).1 = .error e) : e.kind ≠ .invalidInput := by
  have hStatNe : ∀ f p s err, (vfsOps.stat f p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro f p s err hs
    dsimp only [vfsOps, vfsStatPure] at hs
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) f 1024 with
    | ok _ => simp [hR] at hs
    | error err' => simp [hR] at hs; cases hs; exact vfsResolveSegs_never_invalidInput s.nodes 1024 _ _ _ _ hR
  have hCreNe : ∀ p s err, (vfsOps.createDir p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hc
    dsimp only [vfsOps, vfsCreateDirPure] at hc
    cases hPre : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) false 1024 with
    | ok _ => simp [hPre] at hc; cases hc; intro hk; cases hk
    | error e0 =>
      simp only [hPre] at hc
      by_cases hNf : (e0.kind != .notFound) = true
      · simp [hNf] at hc; cases hc; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hPre
      · have hNfF : (e0.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hc
        cases hSp : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s.cwd p)) [] with
        | none => simp [hSp] at hc; cases hc; intro hk; cases hk
        | some pair =>
          rcases pair with ⟨parSegs, lastSeg⟩
          simp only [hSp] at hc
          cases hPar : vfsResolveSegs s.nodes "/" parSegs true 512 with
          | error pe => simp [hPar] at hc; cases hc; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hPar
          | ok pNode =>
            rcases pNode with ⟨parCanon, nd⟩
            cases nd with
            | file _ _ => simp [hPar] at hc; cases hc; intro hk; cases hk
            | symlink _ _ => simp [hPar] at hc; cases hc; intro hk; cases hk
            | dir pm =>
              simp only [hPar] at hc
              by_cases hPm : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = true
              · simp [hPm] at hc; cases hc; intro hk; cases hk
              · have hPmF : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hPm
                simp only [hPmF, Bool.false_eq_true, ↓reduceIte] at hc
                cases hEx : s.nodes (vfsChildPath parCanon lastSeg) with
                | some _ => simp [hEx] at hc; cases hc; intro hk; cases hk
                | none => simp [hEx] at hc
  have hEnsureNe : ∀ p s err, (Internal.ensureDirM vfsOps p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hd
    dsimp only [Internal.ensureDirM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hd
    cases hSt : vfsOps.stat true p s with
    | mk res1 s1 =>
      rw [hSt] at hd
      cases res1 with
      | ok st1 =>
        simp only at hd
        by_cases hD : (st1.kind == .dir) = true
        · simp only [hD, ↓reduceIte] at hd
          dsimp only [StateT.pure, Pure.pure, pure] at hd
          cases hd
        · have hDF : (st1.kind == .dir) = false := Bool.eq_false_iff.mpr hD
          simp only [hDF, Bool.false_eq_true, ↓reduceIte] at hd
          dsimp only [StateT.pure, Pure.pure, pure] at hd
          simp only [Except.error.injEq] at hd; rw [← hd]; intro hk; cases hk
      | error e1 =>
        have hStE1 := hStatNe true p s e1 (congrArg Prod.fst hSt)
        simp only at hd
        by_cases hNf : (e1.kind != .notFound) = true
        · simp [hNf, StateT.pure] at hd; cases hd; exact hStE1
        · have hNfF : (e1.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
          simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hd
          dsimp only [Bind.bind, StateT.bind, StateT.pure] at hd
          cases hCre : vfsOps.createDir p s1 with
          | mk rc sc =>
            rw [hCre] at hd
            cases rc with
            | ok _ =>
              dsimp only [StateT.pure, Pure.pure, pure] at hd
              cases hd
            | error ce =>
              have hCreE := hCreNe p s1 ce (congrArg Prod.fst hCre)
              simp only at hd
              by_cases hAe : (ce.kind == .alreadyExists) = true
              · simp only [hAe, ↓reduceIte] at hd
                cases hSt2 : vfsOps.stat true p sc with
                | mk rs2 _ =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hd
                  rw [hSt2] at hd
                  cases rs2 with
                  | error _ =>
                    dsimp only at hd
                    cases hd; intro hk; cases hk
                  | ok st2 =>
                    dsimp only at hd
                    by_cases hD2 : (st2.kind == .dir) = true
                    · simp only [hD2, ↓reduceIte] at hd
                      dsimp only [StateT.pure, Pure.pure, pure] at hd
                      cases hd
                    · have hD2F : (st2.kind == .dir) = false := Bool.eq_false_iff.mpr hD2
                      simp only [hD2F, Bool.false_eq_true, ↓reduceIte] at hd
                      dsimp only [StateT.pure, Pure.pure, pure] at hd
                      simp only [Except.error.injEq] at hd; rw [← hd]; intro hk; cases hk
              · simp [hAe, StateT.pure] at hd; cases hd; exact hCreE
  have hAncNe : ∀ ancs s err, (Internal.ensureAncestorsM vfsOps ancs s).1 = .error err → err.kind ≠ .invalidInput := by
    intro ancs; induction ancs with
    | nil => intro _ _ h; simp [Internal.ensureAncestorsM, pure, StateT.pure] at h
    | cons a rest ih =>
      intro s err ha
      simp only [Internal.ensureAncestorsM, Bind.bind, bind, StateT.bind, Pure.pure, pure] at ha
      cases hE : Internal.ensureDirM vfsOps a s with
      | mk r s' =>
        rw [hE] at ha
        cases r with
        | error e' =>
          dsimp only [StateT.pure, Pure.pure, pure] at ha
          cases ha; exact hEnsureNe a s err (congrArg Prod.fst hE)
        | ok _ => exact ih s' err ha
  dsimp only [Internal.mkdirImplM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hErr
  cases hSt : vfsOps.stat false path st with
  | mk resPre sPre =>
    rw [hSt] at hErr
    cases resPre with
    | ok stPre =>
      simp only at hErr
      by_cases h1 : (existOk && stPre.kind == .dir) = true
      · simp [h1, StateT.pure] at hErr
      · have h1F : (existOk && stPre.kind == .dir) = false := Bool.eq_false_iff.mpr h1
        simp only [h1F, Bool.false_eq_true, ↓reduceIte] at hErr
        by_cases h2 : (existOk && stPre.kind == .symlink) = true
        · simp only [h2, ↓reduceIte] at hErr
          cases hSt2 : vfsOps.stat true path sPre with
          | mk r2 _ =>
            dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hErr
            rw [hSt2] at hErr
            cases r2 with
            | error _ =>
              dsimp only at hErr
              cases hErr; intro hk; cases hk
            | ok ts =>
              dsimp only at hErr
              by_cases hD : (ts.kind == .dir) = true
              · simp only [hD, ↓reduceIte] at hErr
                dsimp only [StateT.pure, Pure.pure, pure] at hErr
                cases hErr
              · have hDF : (ts.kind == .dir) = false := Bool.eq_false_iff.mpr hD
                simp only [hDF, Bool.false_eq_true, ↓reduceIte] at hErr
                dsimp only [StateT.pure, Pure.pure, pure] at hErr
                simp only [Except.error.injEq] at hErr; rw [← hErr]; intro hk; cases hk
        · simp [h2, StateT.pure] at hErr; cases hErr; intro hk; cases hk
    | error e0 =>
      have hStE0 := hStatNe false path st e0 (congrArg Prod.fst hSt)
      simp only at hErr
      by_cases hNf : (e0.kind != .notFound) = true
      · simp [hNf, StateT.pure] at hErr; cases hErr; exact hStE0
      · have hNfF : (e0.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hErr
        by_cases hP : (!parents) = true
        · simp [hP] at hErr; exact hCreNe path sPre e hErr
        · have hPF : (!parents) = false := Bool.eq_false_iff.mpr hP
          simp only [hPF, Bool.false_eq_true, ↓reduceIte] at hErr
          dsimp only [Bind.bind, StateT.bind, StateT.pure] at hErr
          cases hAnc : Internal.ensureAncestorsM vfsOps (Internal.ancestorChain path path.toList.length) sPre with
          | mk ra sa =>
            rw [hAnc] at hErr
            cases ra with
            | error ae =>
              dsimp only [StateT.pure, Pure.pure, pure] at hErr
              cases hErr; exact hAncNe _ sPre e (congrArg Prod.fst hAnc)
            | ok _ => exact hCreNe path sa e hErr

private theorem forEachChildM_never_invalidInput (f : String → StateM VfsState (Except FsError Unit))
    (hf : ∀ x st e, (f x st).1 = .error e → e.kind ≠ .invalidInput) :
    ∀ xs st e, (Internal.forEachChildM f xs st).1 = .error e → e.kind ≠ .invalidInput := by
  intro xs; induction xs with
  | nil => intro _ _ h; simp [Internal.forEachChildM, pure, StateT.pure] at h
  | cons x rest ih =>
    intro st e h
    simp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind] at h
    cases hx : f x st with
    | mk r s' =>
      rw [hx] at h
      cases r with
      | error e' =>
        dsimp only [StateT.pure, Pure.pure, pure] at h
        cases h; exact hf x st e (congrArg Prod.fst hx)
      | ok _ => exact ih s' e h

private theorem buggyCopyTreeGoNoLoopM_never_invalidInput :
    ∀ fuel src dst dirsExistOk st e,
      (buggyCopyTreeGoNoLoopM src dst dirsExistOk fuel st).1 = .error e → e.kind ≠ .invalidInput := by
  have hStatNe : ∀ f p s err, (vfsOps.stat f p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro f p s err hs; dsimp only [vfsOps, vfsStatPure] at hs
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) f 1024 with
    | ok _ => simp [hR] at hs
    | error err' => simp [hR] at hs; cases hs; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hR
  have hRpNe : ∀ p s err, (vfsOps.realPath p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hr; dsimp only [vfsOps, vfsRealPathPure] at hr
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) true 1024 with
    | ok _ => simp [hR] at hr
    | error err' => simp [hR] at hr; cases hr; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hR
  have hListNe : ∀ p s err, (Internal.listDirSortedM vfsOps p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hl
    dsimp only [Internal.listDirSortedM, vfsOps, vfsReadDirPure, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hl
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) true 1024 with
    | error err' => simp [hR] at hl; cases hl; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hR
    | ok pNode =>
      rcases pNode with ⟨_, nd⟩
      cases nd with
      | dir m =>
        by_cases hm : ((m / 256) % 2 == 0) = true
        · simp [hR, hm, StateT.pure] at hl; cases hl; intro hk; cases hk
        · have hmF : ((m / 256) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
          simp [hR, hmF, StateT.pure] at hl
      | file _ _ => simp [hR] at hl; cases hl; intro hk; cases hk
      | symlink _ _ => simp [hR] at hl; cases hl; intro hk; cases hk
  have hRbNe : ∀ p s err, (vfsOps.readBytes p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hr; dsimp only [vfsOps] at hr
    cases hR : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) true 1024 with
    | error err' => simp [hR] at hr; cases hr; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hR
    | ok pNode =>
      rcases pNode with ⟨_, nd⟩
      cases nd <;> simp [hR] at hr <;> (cases hr; intro hk; cases hk)
  have hWbNe : ∀ p bs s err, (vfsOps.writeBytes p bs s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p bs s err hw; dsimp only [vfsOps, vfsWriteBytesPure] at hw
    cases hSp : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s.cwd p)) [] with
    | none => simp [hSp] at hw; cases hw; intro hk; cases hk
    | some pair =>
      rcases pair with ⟨parSegs, lastSeg⟩
      simp only [hSp] at hw
      cases hPar : vfsResolveSegs s.nodes "/" parSegs true 512 with
      | error pe => simp [hPar] at hw; cases hw; exact vfsResolveSegs_never_invalidInput _ _ _ _ _ _ hPar
      | ok pNode =>
        rcases pNode with ⟨_, nd⟩
        cases nd with
        | file _ _ => simp [hPar] at hw; cases hw; intro hk; cases hk
        | symlink _ _ => simp [hPar] at hw; cases hw; intro hk; cases hk
        | dir pm =>
          simp only [hPar] at hw
          by_cases hPm : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = true
          · simp [hPm] at hw; cases hw; intro hk; cases hk
          · have hPmF : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hPm
            simp only [hPmF, Bool.false_eq_true, ↓reduceIte] at hw
            cases hR2 : vfsResolveSegs s.nodes "/" (vfsSplitSegs (vfsAbsNorm s.cwd p)) true 1024 with
            | error _ => simp [hR2] at hw
            | ok p2 => rcases p2 with ⟨_, nd2⟩; cases nd2 <;> simp [hR2] at hw; cases hw; intro hk; cases hk
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ _ h; simp [buggyCopyTreeGoNoLoopM, pure, StateT.pure] at h; cases h; intro hk; cases hk
  | succ fuel ih =>
    intro src dst dirsExistOk st e h
    simp only [buggyCopyTreeGoNoLoopM, Bind.bind, bind, StateT.bind, Pure.pure, pure] at h
    cases hSt : vfsOps.stat true src st with
    | mk rs s1 =>
      rw [hSt] at h
      cases rs with
      | error e1 =>
        cases h; exact hStatNe true src st e (congrArg Prod.fst hSt)
      | ok st1 =>
        simp only at h
        by_cases hND : (st1.kind != .dir) = true
        · simp only [hND, ↓reduceIte] at h
          dsimp only [StateT.pure, Pure.pure, pure] at h
          simp only [Except.error.injEq] at h; rw [← h]; intro hk; cases hk
        · have hNDF : (st1.kind != .dir) = false := Bool.eq_false_iff.mpr hND
          simp only [hNDF, Bool.false_eq_true, ↓reduceIte] at h
          dsimp only [Bind.bind, StateT.bind, StateT.pure] at h
          cases hRp : vfsOps.realPath src s1 with
          | mk rr s2 =>
            rw [hRp] at h
            cases rr with
            | error e2 =>
              cases h; exact hRpNe src s1 e (congrArg Prod.fst hRp)
            | ok _ =>
              dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at h
              cases hLs : Internal.listDirSortedM vfsOps src s2 with
              | mk rl s3 =>
                rw [hLs] at h
                cases rl with
                | error e3 =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at h
                  cases h; exact hListNe src s2 e (congrArg Prod.fst hLs)
                | ok names =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at h
                  cases hMk : Internal.mkdirImplM vfsOps dst true dirsExistOk s3 with
                  | mk rm s4 =>
                    rw [hMk] at h
                    cases rm with
                    | error e4 =>
                      dsimp only [StateT.pure, Pure.pure, pure] at h
                      cases h; exact vfsOps_mkdir_never_invalidInput dst true dirsExistOk s3 e (congrArg Prod.fst hMk)
                    | ok _ =>
                      apply forEachChildM_never_invalidInput _ _ names.toList s4 e h
                      intro n sChildSt eChild hf
                      dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hf
                      cases hSc : vfsOps.stat true (Internal.join src n) sChildSt with
                      | mk rsc sc2 =>
                        rw [hSc] at hf
                        cases rsc with
                        | error e5 =>
                          dsimp only [StateT.pure, Pure.pure, pure] at hf
                          cases hf; exact hStatNe true _ sChildSt eChild (congrArg Prod.fst hSc)
                        | ok cst =>
                          simp only at hf
                          by_cases hD : (cst.kind == .dir) = true
                          · simp only [hD, ↓reduceIte] at hf
                            exact ih _ _ dirsExistOk sc2 eChild hf
                          · have hDF : (cst.kind == .dir) = false := Bool.eq_false_iff.mpr hD
                            simp only [hDF, Bool.false_eq_true, ↓reduceIte] at hf
                            dsimp only [Bind.bind, bind, StateT.bind] at hf
                            cases hRb : vfsOps.readBytes (Internal.join src n) sc2 with
                            | mk rrb sc3 =>
                              rw [hRb] at hf
                              cases rrb with
                              | error e6 =>
                                dsimp only [StateT.pure, Pure.pure, pure] at hf
                                cases hf; exact hRbNe _ sc2 eChild (congrArg Prod.fst hRb)
                              | ok bs =>
                                dsimp only at hf
                                exact hWbNe _ bs sc3 eChild hf

example : ¬ AllPass (test_fs_vfs_copyTree_loopRejected
    { vfsApi with copyTree := fun src dst ok => buggyCopyTreeGoNoLoopM src dst ok 4096 }) := by
  intro h
  rcases reach_fs_vfs_copyTree_loopRejected with
    ⟨st, src, hRoot, hSrc, hCan, hList, hSelf, hLstat, _⟩
  have hFail := h st src hRoot hSrc hCan hList hSelf hLstat
  dsimp only [StateT.run, assert] at hFail
  rcases hFail with ⟨⟨e, hErr, hKind⟩, _⟩
  exact buggyCopyTreeGoNoLoopM_never_invalidInput 4096 src "/loop_dst" false st e hErr hKind

private def buggyWalkR2I01 (root : String) : StateM VfsState (Except FsError (Array WalkEntry)) := do
  match ← vfsOps.stat true root with
  | .ok _ => Internal.walkImplM vfsOps root
  | .error _ => return .error { kind := .notFound, path := some root, message := s!"not found: {root}" }

example : ¬ AllPass (test_fs_vfs_walk_preservesStatError { vfsApi with walk := buggyWalkR2I01 }) := by
  intro h
  let st : VfsState :=
    { tree := vfsEmptyDir 0o000
      keys := ["/"]
      cwd := "/"
      nonce := 0 }
  have hFail := h st "/locked"
  have hStatPerm : vfsStatPure st true "/locked" =
      .error { kind := .permissionDenied, path := some "/", message := "permission denied: /" } := by
    dsimp only [vfsStatPure]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/locked" = "/locked" from by decide,
        show vfsSplitSegs "/locked" = ["locked"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o000) from rfl]; rfl
  dsimp only [vfsApi, Internal.mkApiM, buggyWalkR2I01, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at hFail
  rw [show vfsOps.stat true "/locked" st = (vfsStatPure st true "/locked", st) from rfl, hStatPerm] at hFail
  simp only at hFail
  rcases hFail with ⟨⟨⟨e, he, hk⟩, _⟩, _⟩
  cases he
  simp at hk

private def buggySuffixesR3I01 (path : String) : Array String :=
  match Internal.name path with
  | none => #[]
  | some n =>
    match n.toList.reverse with
    | '.' :: _ => #[]
    | _ =>
      let stripped := n.toList.dropWhile (· == '.')
      match Internal.splitCharList '.' stripped with
      | [] | [_] => #[]
      | _ :: exts => ((exts.filter (!·.isEmpty)).map fun cs => "." ++ String.ofList cs).toArray

example : ¬ AllPass (test_fs_suffixes_doubleDot { defaultApi with suffixes := buggySuffixesR3I01 }) := by
  intro h
  have hFail := h "a" (by decide) (by decide) (by decide)
  have hVal : buggySuffixesR3I01 "a..ext" = #[".ext"] := by decide
  dsimp only [assert] at hFail
  have hCat : ("a" ++ "..ext") = "a..ext" := by decide
  rw [hCat, hVal] at hFail
  exact absurd hFail.1 (by decide)

private def buggyCopyTreeR3I02 (src dst : String) (dirsExistOk : Bool) : StateM VfsState (Except FsError Unit) :=
  Internal.copyTreeGoM vfsOps src dst dirsExistOk [] 4096

example : ¬ AllPass (test_fs_vfs_copyTree_selfCopyRejected { vfsApi with copyTree := buggyCopyTreeR3I02 }) := by
  intro h
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "src" then some (vfsEmptyDir 0o755) else none)
      keys := ["/", "/src"]
      cwd := "/"
      nonce := 0 }
  have hStatSrc : ((vfsApi.stat "/src").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResSrc : ((vfsApi.resolve "/src").run st).1 = .ok "/src" := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
  have hResDstBad : ((vfsApi.resolve "/src/sub").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsRealPathPure, StateT.run]
    rw [show st.cwd = "/" from rfl,
        show vfsAbsNorm "/" "/src/sub" = "/src/sub" from by decide,
        show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/src" "sub" = "/src/sub" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src/sub" = none from rfl]; rfl
  have hFail := h st "/src" "/src/sub"
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩
    ⟨"/src", hResSrc, by decide, by decide, hResSrc,
      Or.inr ⟨"sub", by decide, by decide, by decide, by decide, rfl, hResDstBad⟩⟩
  have hSubNone : st.nodes "/src/sub" = none := rfl
  have hListSrc : (Internal.listDirSortedM vfsOps "/src").run st = (.ok #[], st) := by
    dsimp only [Internal.listDirSortedM, vfsOps, vfsReadDirPure, StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src" = "/src" from by decide,
        show vfsSplitSegs "/src" = ["src"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "src" = "/src" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 256) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [StateT.pure, Pure.pure, pure]
    have hK : st.keys.eraseDups = ["/", "/src"] := rfl
    have hN0 : (st.nodes "/").isSome = true := rfl
    have hN1 : (st.nodes "/src").isSome = true := rfl
    have hPre0 : "/src/".toList.isPrefixOf "/".toList = false := by decide
    rw [hK]
    simp only [List.filterMap_cons, List.filterMap_nil, hN0, hN1, Bool.false_eq_true, ↓reduceIte,
      show ("/src" == "/") = false from by decide,
      show ("/" != "/src") = true from by decide,
      show ("/src" != "/src") = false from by decide,
      show ("/src" ++ "/").toList = "/src/".toList from by decide,
      hPre0, Bool.true_and, Bool.false_and, List.mergeSort_nil]
  let stSub : VfsState :=
    { st with
      tree := vfsTreeSet st.tree ["src", "sub"] (some (vfsEmptyDir 0o755))
      keys := "/src/sub" :: st.keys }
  have hMkSub : Internal.mkdirImplM vfsOps "/src/sub" true false st = (.ok (), stSub) := by
    have hPreSub : vfsStatPure st false "/src/sub" =
        .error { kind := .notFound, path := some "/src/sub", message := "no such file or directory: /src/sub" } := by
      dsimp only [vfsStatPure]
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/src/sub" = "/src/sub" from by decide,
          show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide]
      unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show vfsChildPath "/" "src" = "/src" from by decide]
      unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
      rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show vfsChildPath "/src" "sub" = "/src/sub" from by decide]
      unfold vfsResolveSegs; rw [hSubNone]; rfl
    have hStSrcOk : vfsStatPure st true "/src" = .ok (vfsToStat (.dir 0o755)) := hStatSrc
    have hAnc : Internal.ensureAncestorsM vfsOps ["/src"] st = (.ok (), st) := by
      dsimp only [Internal.ensureAncestorsM, Internal.ensureDirM, bind, StateT.bind, pure, StateT.pure]
      rw [show vfsOps.stat true "/src" st = (vfsStatPure st true "/src", st) from rfl, hStSrcOk]
      rfl
    have hCre : vfsCreateDirPure st "/src/sub" = (.ok (), stSub) := by
      have hParSub : Internal.splitLastAux ["src", "sub"] [] = some (["src"], "sub") := by decide
      have hParSrc : vfsResolveSegs st.nodes "/" ["src"] true 512 = .ok ("/src", .dir 0o755) := by
        unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
        rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show vfsChildPath "/" "src" = "/src" from by decide]
        unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]
      have hPreSub' : vfsResolveSegs st.nodes "/" ["src", "sub"] false 1024 =
          .error { kind := .notFound, path := some "/src/sub", message := "no such file or directory: /src/sub" } := by
        unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
        rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show vfsChildPath "/" "src" = "/src" from by decide]
        unfold vfsResolveSegs; rw [show st.nodes "/src" = some (.dir 0o755) from rfl]; dsimp only
        rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show vfsChildPath "/src" "sub" = "/src/sub" from by decide]
        unfold vfsResolveSegs; rw [hSubNone]; rfl
      dsimp only [vfsCreateDirPure]
      rw [show vfsAbsNorm st.cwd "/src/sub" = "/src/sub" from by decide,
          show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide, hPreSub']
      dsimp only
      rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte, hParSub]
      rw [hParSrc]; dsimp only
      rw [show ((0o755 / 128) % 2 == 0 || (0o755 / 64) % 2 == 0) = false from by decide]
      simp only [Bool.false_eq_true, ↓reduceIte, show vfsChildPath "/src" "sub" = "/src/sub" from by decide, hSubNone]
      simp [stSub, show vfsSplitSegs "/src/sub" = ["src", "sub"] from by decide]
    dsimp only [Internal.mkdirImplM, bind, StateT.bind, pure, StateT.pure]
    rw [show vfsOps.stat false "/src/sub" st = (vfsStatPure st false "/src/sub", st) from rfl, hPreSub]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true,
        show Internal.ancestorChain "/src/sub" "/src/sub".toList.length = ["/src"] from by decide]
    have hBindSub :
        StateT.bind (Internal.ensureAncestorsM vfsOps ["/src"])
          (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/src/sub") st =
        vfsOps.createDir "/src/sub" st := by
      dsimp only [Bind.bind, StateT.bind]
      rw [hAnc]
    change StateT.bind (Internal.ensureAncestorsM vfsOps ["/src"])
      (fun x => match x with | .error ae => pure (.error ae) | .ok () => vfsOps.createDir "/src/sub") st = (.ok (), stSub)
    rw [hBindSub]
    exact hCre
  have hBuggy : buggyCopyTreeR3I02 "/src" "/src/sub" false st = (.ok (), stSub) := by
    unfold buggyCopyTreeR3I02 Internal.copyTreeGoM
    dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
    rw [show vfsOps.stat true "/src" st = (vfsStatPure st true "/src", st) from rfl]
    have hStS : vfsStatPure st true "/src" = .ok (vfsToStat (.dir 0o755)) := hStatSrc
    rw [hStS]
    dsimp only
    rw [show ((vfsToStat (.dir 0o755)).kind != .dir) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    rw [show vfsOps.realPath "/src" st = (vfsRealPathPure st "/src", st) from rfl]
    have hRpS : vfsRealPathPure st "/src" = .ok "/src" := hResSrc
    rw [hRpS]
    simp only [List.mem_nil_iff, ↓reduceIte]
    dsimp only [Bind.bind, StateT.bind, StateT.pure]
    dsimp only [StateT.run] at hListSrc
    rw [hListSrc]
    dsimp only [StateT.bind]
    rw [hMkSub]
    simp [Internal.forEachChildM, pure]
    rfl
  dsimp only [StateT.run, assert] at hFail
  rw [hBuggy] at hFail
  rcases hFail with ⟨⟨⟨e, he, _⟩, _⟩, _⟩
  cases he

end LeanSwe.Fs.Proofs
