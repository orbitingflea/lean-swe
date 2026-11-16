import LeanSwe.Fs.Interface
import LeanSwe.Fs.SpecTests
import LeanSwe.Fs.Raw.Proofs
import LeanSwe.Fs.Proofs.RawDirOps
import LeanSwe.Fs.Proofs.SubtreeIsolation
import LeanSwe.Fs.Proofs.SubtreeModelSpecs
import LeanSwe.Fs.Proofs.SubtreeTests

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
    have hFullNotEmpty : (!(base.toList ++ ['.', '.', 'e', 'x', 't']).isEmpty) = true := by
      simp [hBase]
    have hFullNotDot : ((base.toList ++ ['.', '.', 'e', 'x', 't']) != ['.']) = true := by
      refine bne_iff_ne.mpr fun heq => ?_
      have hLen := congrArg List.length heq
      simp at hLen
    have hName : Internal.name (base ++ "..ext") = some (base ++ "..ext") := by
      unfold Internal.name Internal.splitParentName Internal.cleanCharSegments
      dsimp only
      rw [splitCharList_of_no_sep '/' (base ++ "..ext").toList hFullNoSlash]
      rw [String.toList_append, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
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
  /-- Active advisory locks `(handleId, canonicalPath, mode)`. -/
  locks : List (Nat × String × LockMode) := []
  /-- Monotonic counter for allocated lock handle IDs. -/
  nextLockId : Nat := 1

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

private def maxLockId : List (Nat × String × LockMode) → Nat
  | [] => 0
  | (i, _, _) :: rest => max i (maxLockId rest)

private def freshLockId (st : VfsState) : Nat :=
  max (maxLockId st.locks) st.nextLockId + 1

private def hasLockConflict (locks : List (Nat × String × LockMode)) (canon : String)
    (mode : LockMode) : Bool :=
  locks.any fun (_, p, m) => p == canon && (mode == .exclusive || m == .exclusive)

private def isValidLockPath (path : String) : Bool :=
  let chars := path.toList
  !chars.isEmpty && !(chars.length > 1 && chars.getLast? == some '/')

private def vfsAcquireLockPure (st : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (_nonBlocking : Bool) : Except FsError LockHandle × VfsState :=
  if !isValidLockPath path then
    (.error { kind := .invalidInput, path := some path, message := "invalid lock path" }, st)
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
    | .ok (canon, .file _ _) =>
      if hasLockConflict st.locks canon mode then
        (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, st)
      else
        let id := freshLockId st
        (.ok { handleId := id, path := path, mode := mode },
          { st with locks := (id, canon, mode) :: st.locks, nextLockId := id })
    | .ok (_, .dir _) =>
      (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
    | .ok (_, .symlink _ _) =>
      (.error { kind := .invalidInput, path := some path, message := s!"symlink rejected for lock: {path}" }, st)
    | .error e =>
      if e.kind != .notFound then
        (.error e, st)
      else if !createIfMissing then
        (.error e, st)
      else
        match Internal.splitLastAux (vfsSplitSegs abs) [] with
        | none =>
          (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
        | some (parSegs, lastSeg) =>
          match vfsResolveSegs st.nodes "/" parSegs true 512 with
          | .error pe => (.error pe, st)
          | .ok (parCanon, .dir parMode) =>
            if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
              (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
            else
              let newKey := vfsChildPath parCanon lastSeg
              if hasLockConflict st.locks newKey mode then
                (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, st)
              else
                let id := freshLockId st
                (.ok { handleId := id, path := path, mode := mode },
                  { st with
                    tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (.file ByteArray.empty 0o644))
                    keys := newKey :: st.keys
                    locks := (id, newKey, mode) :: st.locks
                    nextLockId := id })
          | .ok (parCanon, _) =>
            (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

private def vfsReleaseLockPure (st : VfsState) (handle : LockHandle) :
    Except FsError Unit × VfsState :=
  if handle.handleId == 0 then
    (.error { kind := .invalidInput, path := some handle.path, message := "invalid lock handle" }, st)
  else if st.locks.any (fun (id, _, _) => id == handle.handleId) then
    (.ok (), { st with locks := st.locks.filter (fun (id, _, _) => id != handle.handleId) })
  else
    (.error { kind := .invalidInput, path := some handle.path, message := "unknown lock handle" }, st)

private def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

private def vfsReadBytesPure (st : VfsState) (path : String) : Except FsError ByteArray :=
  if !isValidRawPath path then
    .error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
    | .error e => .error e
    | .ok (_, .file bs _) => .ok bs
    | .ok (_, .dir _) => .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    | .ok (_, _) => .error { kind := .notFound, path := some path, message := s!"not found: {path}" }

private def vfsCreateFileNewPure (st : VfsState) (path : String) (bs : ByteArray) :
    Except FsError Unit × VfsState :=
  if !isValidRawPath path then
    (.error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }, st)
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
    | .ok _ =>
      (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
    | .error e =>
      if e.kind != .notFound then
        (.error e, st)
      else
        match Internal.splitLastAux (vfsSplitSegs abs) [] with
        | none =>
          (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
        | some (parSegs, lastSeg) =>
          match vfsResolveSegs st.nodes "/" parSegs true 1024 with
          | .error pe => (.error pe, st)
          | .ok (parCanon, .dir parMode) =>
            if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
              (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
            else
              let newKey := vfsChildPath parCanon lastSeg
              (.ok (), { st with
                tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (.file bs 0o644))
                keys := newKey :: st.keys })
          | .ok (parCanon, _) =>
            (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)

private def vfsRenamePure (st : VfsState) (src dst : String) : Except FsError Unit × VfsState :=
  if !isValidRawPath src then
    (.error { kind := .invalidInput, path := some src, message := s!"invalid path: {src}" }, st)
  else if !isValidRawPath dst then
    (.error { kind := .invalidInput, path := some dst, message := s!"invalid path: {dst}" }, st)
  else
    let srcAbs := vfsAbsNorm st.cwd src
    let dstAbs := vfsAbsNorm st.cwd dst
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs srcAbs) false 1024 with
    | .error e => (.error e, st)
    | .ok (srcCanon, srcNode) =>
      match Internal.splitLastAux (vfsSplitSegs dstAbs) [] with
      | none => (.error { kind := .isADirectory, path := some dst, message := s!"is a directory: {dst}" }, st)
      | some (dstParSegs, dstLastSeg) =>
        match vfsResolveSegs st.nodes "/" dstParSegs true 512 with
        | .error pe => (.error pe, st)
        | .ok (dstParCanon, .dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some dst, message := s!"permission denied: {dst}" }, st)
          else
            let dstKey := vfsChildPath dstParCanon dstLastSeg
            let srcIsDir := match srcNode with | .dir _ => true | _ => false
            let dstIsDir := match st.nodes dstKey with | some (.dir _) => true | _ => false
            if dstIsDir && !srcIsDir then
              (.error { kind := .isADirectory, path := some dst, message := s!"is a directory: {dst}" }, st)
            else if srcCanon == dstKey then
              (.ok (), st)
            else
              let moved := vfsTreeGet st.tree (vfsSplitSegs srcCanon)
              let tr₁ := vfsTreeSet st.tree (vfsSplitSegs srcCanon) none
              (.ok (), { st with
                tree := vfsTreeSet tr₁ (vfsSplitSegs dstKey) moved
                keys := dstKey :: st.keys })
        | .ok (dstParCanon, _) =>
          (.error { kind := .notADirectory, path := some dstParCanon, message := s!"not a directory: {dstParCanon}" }, st)

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
    readBytes := fun path st => (vfsReadBytesPure st path, st)
    writeBytes := fun path bs st => vfsWriteBytesPure st path bs
    createFileNew := fun path bs st => vfsCreateFileNewPure st path bs
    appendText := fun path s st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .ok (canon, .file bs m) =>
        (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) (some (.file (bs ++ s.toUTF8) m)) })
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | _ => vfsWriteBytesPure st path s.toUTF8
    rename := fun src dst st => vfsRenamePure st src dst
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
    monotonicNonce := fun st => (st.nonce, { st with nonce := st.nonce + 1 })
    acquireLock := fun path mode createIfMissing nonBlocking st =>
      vfsAcquireLockPure st path mode createIfMissing nonBlocking
    releaseLock := fun handle st => vfsReleaseLockPure st handle }

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
      bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
    rw [hRes]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, StateT.pure]
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩

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
      bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
    rw [hRes]
    simp only [Bool.not_false, ↓reduceIte, StateT.pure]
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩

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
      bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
    rw [hRes]
    simp [Pure.pure, StateT.pure]
  | ok p =>
    rcases p with ⟨canon, nd⟩
    dsimp only
    by_cases hNotDir : ((vfsToStat nd).kind != .dir) = true
    · simp only [hNotDir, ↓reduceIte]
      dsimp only [vfsApi, Internal.mkApiM, Internal.walkImplM, vfsOps, vfsStatPure, StateT.run,
        bind, StateT.bind, pure, Pure.pure, StateT.pure, assert]
      rw [hRes]
      simp only [hNotDir, ↓reduceIte, StateT.pure]
      exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
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
      dsimp only [Bind.bind, StateT.bind, Pure.pure, pure, StateT.pure]
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
        simp at hL
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
  dsimp only [Bind.bind, StateT.bind, Pure.pure, pure, StateT.pure]
  dsimp only [StateT.run] at hApprox
  rw [hApprox]
  simp [hGuard]

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
    simp only [h1, h2, h3, Bool.or_false]
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
    simp only [h1, h2, h3, Bool.or_false]
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
  simp only [buggyMkdirR1I01, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind,
    pure, Pure.pure] at hFail
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
  have hCreExistNe : ∀ p s err, (Internal.createDirExistOkM vfsOps p s).1 = .error err → err.kind ≠ .invalidInput := by
    intro p s err hce
    dsimp only [Internal.createDirExistOkM, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hce
    cases hC : vfsOps.createDir p s with
    | mk rc sc =>
      rw [hC] at hce
      cases rc with
      | ok _ =>
        dsimp only [StateT.pure, Pure.pure, pure] at hce
        cases hce
      | error ce =>
        have hCeNe := hCreNe p s ce (congrArg Prod.fst hC)
        dsimp only at hce
        by_cases hAe : (ce.kind != .alreadyExists) = true
        · simp [hAe, StateT.pure] at hce; cases hce; exact hCeNe
        · have hAeF : (ce.kind != .alreadyExists) = false := Bool.eq_false_iff.mpr hAe
          simp only [hAeF, Bool.false_eq_true, ↓reduceIte] at hce
          dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure] at hce
          cases hSt2 : vfsOps.stat true p sc with
          | mk rs2 s2 =>
            rw [hSt2] at hce
            cases rs2 with
            | error _ => simp [StateT.pure] at hce; cases hce; exact hCeNe
            | ok st2 =>
              dsimp only at hce
              by_cases hD2 : (st2.kind == .dir) = true
              · simp [hD2, StateT.pure] at hce
              · simp [hD2, StateT.pure] at hce; cases hce; exact hCeNe
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
        · simp only [hP, ↓reduceIte] at hErr
          cases existOk with
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hErr; exact hCreNe path sPre e hErr
          | true => simp only [↓reduceIte] at hErr; exact hCreExistNe path sPre e hErr
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
            | ok _ =>
              dsimp only at hErr
              cases existOk with
              | false => simp only [Bool.false_eq_true, ↓reduceIte] at hErr; exact hCreNe path sa e hErr
              | true => simp only [↓reduceIte] at hErr; exact hCreExistNe path sa e hErr

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

private theorem forEachChildM_invariant (P : VfsState → Prop)
    (f : String → StateM VfsState (Except FsError Unit))
    (hf : ∀ x st, P st → P (f x st).2 ∧ (∀ e, (f x st).1 = .error e → e.kind ≠ .invalidInput)) :
    ∀ xs st, P st →
      P (Internal.forEachChildM f xs st).2 ∧
      (∀ e, (Internal.forEachChildM f xs st).1 = .error e → e.kind ≠ .invalidInput) := by
  intro xs; induction xs with
  | nil =>
    intro st hP
    simp only [Internal.forEachChildM, pure, StateT.pure]
    exact ⟨hP, fun _ h => by cases h⟩
  | cons x rest ih =>
    intro st hP
    simp only [Internal.forEachChildM, Bind.bind, bind, StateT.bind]
    cases hx : f x st with
    | mk r s' =>
      have hStep := hf x st hP
      rw [hx] at hStep
      cases r with
      | error e' =>
        dsimp only [StateT.pure, Pure.pure, pure]
        exact ⟨hStep.1, fun e h => by cases h; exact hStep.2 e' rfl⟩
      | ok _ => exact ih s' hStep.1

private def NoFileTree (t : VfsTree) : Prop :=
  ∀ segs bs m, vfsTreeGet t segs ≠ some (.file bs m)

private theorem vfsTreeNodes_noFile (t : VfsTree) (k : String) (bs : ByteArray) (m : Nat)
    (hc : vfsTreeNodes t k = some (.file bs m)) (ht : NoFileTree t) : False := by
  unfold vfsTreeNodes at hc
  by_cases hC : isCanonPath k = true
  · simp only [hC, ↓reduceIte] at hc
    cases hg : vfsTreeGet t (vfsSplitSegs k) with
    | none => simp [hg] at hc
    | some sub =>
      simp only [hg, Option.map_some, Option.some.injEq] at hc
      cases sub with
      | file _ _ => exact ht (vfsSplitSegs k) _ _ hg
      | dir _ _ => simp [vfsTreeTopNode] at hc
      | symlink _ _ => simp [vfsTreeTopNode] at hc
  · simp [hC] at hc

private theorem vfsResolveSegs_true_noFile_isDir (t : VfsTree) (ht : NoFileTree t) :
    ∀ fuel cur segs canon nd,
      vfsResolveSegs (vfsTreeNodes t) cur segs true fuel = .ok (canon, nd) →
      ∃ m, nd = .dir m := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs canon nd h
    cases segs with
    | nil =>
      simp only [vfsResolveSegs] at h
      cases hc : vfsTreeNodes t cur with
      | none => simp [hc] at h
      | some n0 =>
        cases n0 with
        | file bs m => exact (vfsTreeNodes_noFile t cur bs m hc ht).elim
        | dir m => simp [hc] at h; rcases h with ⟨_, rfl⟩; exact ⟨m, rfl⟩
        | symlink _ _ => simp [hc] at h; exact ih _ _ _ _ h
    | cons seg rest =>
      simp only [vfsResolveSegs] at h
      cases hc : vfsTreeNodes t cur with
      | none => simp [hc] at h
      | some n0 =>
        cases n0 with
        | file bs m => exact (vfsTreeNodes_noFile t cur bs m hc ht).elim
        | symlink _ _ => simp [hc] at h; exact ih _ _ _ _ h
        | dir m =>
          simp only [hc] at h
          by_cases hp : ((m / 64) % 2 == 0) = true
          · simp [hp] at h
          · simp [hp] at h; exact ih _ _ _ _ h

private theorem vfsTreeSet_emptyDir_noFileTree (m : Nat) :
    ∀ path t, NoFileTree t → NoFileTree (vfsTreeSet t path (some (vfsEmptyDir m))) := by
  intro path; induction path with
  | nil =>
    intro t _ segs bs m' h
    cases segs <;> simp [vfsTreeSet, vfsEmptyDir, vfsTreeGet] at h
  | cons seg rest ih =>
    intro t ht segs bs m' h
    cases rest with
    | nil =>
      cases t with
      | file _ _ => exact ht segs _ _ h
      | symlink _ _ => exact ht segs _ _ (by simpa [vfsTreeSet] using h)
      | dir dm ch =>
        cases segs with
        | nil => simp [vfsTreeSet, vfsTreeGet] at h
        | cons s srest =>
          simp only [vfsTreeSet, vfsTreeGet] at h
          by_cases hs : (s == seg) = true
          · simp only [hs, ↓reduceIte] at h
            cases srest <;> simp [vfsEmptyDir, vfsTreeGet] at h
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
            cases hc : ch s with
            | none => simp [hc] at h
            | some sub =>
              simp only [hc] at h
              exact ht (s :: srest) bs m' (by simp only [vfsTreeGet, hc]; exact h)
    | cons seg2 rest2 =>
      cases t with
      | file _ _ => exact ht segs _ _ h
      | symlink _ _ => exact ht segs _ _ (by simpa [vfsTreeSet] using h)
      | dir dm ch =>
        cases segs with
        | nil => simp [vfsTreeSet, vfsTreeGet] at h
        | cons s srest =>
          simp only [vfsTreeSet, vfsTreeGet] at h
          by_cases hs : (s == seg) = true
          · simp only [hs, ↓reduceIte] at h
            cases hc : ch seg with
            | none => simp [hc] at h
            | some sub =>
              have hsEq : s = seg := beq_iff_eq.mp hs
              subst hsEq
              simp only [hc] at h
              have htSub : NoFileTree sub := fun xs bs' m'' hx =>
                ht (s :: xs) bs' m'' (by simp only [vfsTreeGet, hc]; exact hx)
              exact ih sub htSub srest bs m' h
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
            cases hc : ch s with
            | none => simp [hc] at h
            | some sub =>
              simp only [hc] at h
              exact ht (s :: srest) bs m' (by simp only [vfsTreeGet, hc]; exact h)

private theorem vfsCreateDirPure_noFileTree (st : VfsState) (p : String) (ht : NoFileTree st.tree) :
    NoFileTree (vfsCreateDirPure st p).2.tree := by
  unfold vfsCreateDirPure
  dsimp only
  cases vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd p)) false 1024 with
  | ok _ => exact ht
  | error e =>
    dsimp only
    by_cases hNf : (e.kind != .notFound) = true
    · simp only [hNf, ↓reduceIte]; exact ht
    · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
      cases Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm st.cwd p)) [] with
      | none => exact ht
      | some pair =>
        rcases pair with ⟨parSegs, lastSeg⟩
        dsimp only
        cases vfsResolveSegs st.nodes "/" parSegs true 512 with
        | error _ => exact ht
        | ok pNode =>
          rcases pNode with ⟨parCanon, nd⟩
          cases nd with
          | file _ _ => exact ht
          | symlink _ _ => exact ht
          | dir pm =>
            dsimp only
            by_cases hPm : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = true
            · simp only [hPm, ↓reduceIte]; exact ht
            · simp only [hPm, Bool.false_eq_true, ↓reduceIte]
              cases st.nodes (vfsChildPath parCanon lastSeg) with
              | some _ => exact ht
              | none => exact vfsTreeSet_emptyDir_noFileTree 0o755 (vfsSplitSegs (vfsChildPath parCanon lastSeg)) st.tree ht

private theorem vfsEnsureDirM_noFileTree (anc : String) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.ensureDirM vfsOps anc st).2.tree := by
  unfold Internal.ensureDirM
  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  cases hSt : vfsOps.stat true anc st with
  | mk rSt s1 =>
    have hs1 : s1 = st := (congrArg Prod.snd hSt).symm
    cases rSt with
    | ok st0 =>
      dsimp only
      by_cases hD : (st0.kind == .dir) = true <;> simp only [hD, ↓reduceIte, Bool.false_eq_true] <;> subst hs1 <;> exact ht
    | error e =>
      dsimp only
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte]; subst hs1; exact ht
      · simp only [hNf, Bool.false_eq_true, ↓reduceIte, Bind.bind, bind, StateT.bind]
        cases hCr : vfsOps.createDir anc s1 with
        | mk rc s2 =>
          have ht2 : NoFileTree s2.tree := by
            have hS2Eq : s2 = (vfsCreateDirPure s1 anc).2 := (congrArg Prod.snd hCr).symm
            rw [hS2Eq]; exact vfsCreateDirPure_noFileTree s1 anc (by subst hs1; exact ht)
          cases rc with
          | ok _ => exact ht2
          | error ce =>
            dsimp only
            by_cases hAe : (ce.kind == .alreadyExists) = true
            · simp only [hAe, ↓reduceIte, Bind.bind, bind, StateT.bind]
              cases hSt2 : vfsOps.stat true anc s2 with
              | mk rSt2 s3 =>
                have hs3 : s3 = s2 := (congrArg Prod.snd hSt2).symm
                cases rSt2 with
                | error _ => subst hs3; exact ht2
                | ok st2 =>
                  dsimp only
                  by_cases hD2 : (st2.kind == .dir) = true <;>
                    simp only [hD2, ↓reduceIte, Bool.false_eq_true] <;> subst hs3 <;> exact ht2
            · simp only [hAe, Bool.false_eq_true, ↓reduceIte]; exact ht2

private theorem vfsEnsureAncestorsM_noFileTree (ps : List String) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.ensureAncestorsM vfsOps ps st).2.tree := by
  induction ps generalizing st with
  | nil => exact ht
  | cons p rest ih =>
    simp only [Internal.ensureAncestorsM, Bind.bind, bind, StateT.bind]
    cases hEd : Internal.ensureDirM vfsOps p st with
    | mk rd s1 =>
      have ht1 : NoFileTree s1.tree := by
        have hS1Eq : s1 = (Internal.ensureDirM vfsOps p st).2 := (congrArg Prod.snd hEd).symm
        rw [hS1Eq]; exact vfsEnsureDirM_noFileTree p st ht
      cases rd with
      | error _ => exact ht1
      | ok _ => exact ih s1 ht1

private theorem vfsCreateDirExistOkM_noFileTree (p : String) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.createDirExistOkM vfsOps p st).2.tree := by
  unfold Internal.createDirExistOkM
  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  cases hC : vfsOps.createDir p st with
  | mk rc sc =>
    have htc : NoFileTree sc.tree := by
      have hEq : sc = (vfsCreateDirPure st p).2 := (congrArg Prod.snd hC).symm
      rw [hEq]; exact vfsCreateDirPure_noFileTree st p ht
    cases rc with
    | ok _ => exact htc
    | error ce =>
      dsimp only
      by_cases hAe : (ce.kind != .alreadyExists) = true
      · simp only [hAe, ↓reduceIte]; exact htc
      · have hAeF : (ce.kind != .alreadyExists) = false := Bool.eq_false_iff.mpr hAe
        simp only [hAeF, Bool.false_eq_true, ↓reduceIte, Bind.bind, bind, StateT.bind]
        cases hSt2 : vfsOps.stat true p sc with
        | mk rs2 s2 =>
          have hs2 : s2 = sc := (congrArg Prod.snd hSt2).symm
          cases rs2 with
          | error _ => subst hs2; exact htc
          | ok st2 =>
            by_cases hD2 : (st2.kind == .dir) = true <;>
              simp only [hD2, ↓reduceIte, Bool.false_eq_true] <;> subst hs2 <;> exact htc

private theorem vfsMkdirImplM_noFileTree (p : String) (parents existOk : Bool) (st : VfsState) (ht : NoFileTree st.tree) :
    NoFileTree (Internal.mkdirImplM vfsOps p parents existOk st).2.tree := by
  unfold Internal.mkdirImplM
  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
  cases hSt : vfsOps.stat false p st with
  | mk rSt s1 =>
    have hs1 : s1 = st := (congrArg Prod.snd hSt).symm
    cases rSt with
    | ok ts =>
      dsimp only
      by_cases hD : (existOk && ts.kind == .dir) = true
      · simp only [hD, ↓reduceIte]; subst hs1; exact ht
      · simp only [hD, Bool.false_eq_true, ↓reduceIte]
        by_cases hS : (existOk && ts.kind == .symlink) = true
        · simp only [hS, ↓reduceIte, Bind.bind, bind, StateT.bind]
          cases hSt2 : vfsOps.stat true p s1 with
          | mk rSt2 s2 =>
            have hs2 : s2 = s1 := (congrArg Prod.snd hSt2).symm
            cases rSt2 with
            | error _ => subst hs2; subst hs1; exact ht
            | ok tgtSt =>
              dsimp only
              by_cases hTD : (tgtSt.kind == .dir) = true <;>
                simp only [hTD, ↓reduceIte, Bool.false_eq_true] <;> subst hs2 <;> subst hs1 <;> exact ht
        · simp only [hS, Bool.false_eq_true, ↓reduceIte]; subst hs1; exact ht
    | error e =>
      dsimp only
      by_cases hNf : (e.kind != .notFound) = true
      · simp only [hNf, ↓reduceIte]; subst hs1; exact ht
      · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
        by_cases hP : (!parents) = true
        · simp only [hP, ↓reduceIte]
          cases existOk with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact vfsCreateDirPure_noFileTree s1 p (by subst hs1; exact ht)
          | true =>
            simp only [↓reduceIte]
            exact vfsCreateDirExistOkM_noFileTree p s1 (by subst hs1; exact ht)
        · have hPF : (!parents) = false := Bool.eq_false_iff.mpr hP
          simp only [hPF, Bool.false_eq_true, ↓reduceIte, Bind.bind, bind, StateT.bind]
          cases hAnc : Internal.ensureAncestorsM vfsOps (Internal.ancestorChain p p.toList.length) s1 with
          | mk ra sa =>
            have hta : NoFileTree sa.tree := by
              have hSaEq : sa = (Internal.ensureAncestorsM vfsOps (Internal.ancestorChain p p.toList.length) s1).2 :=
                (congrArg Prod.snd hAnc).symm
              rw [hSaEq]; exact vfsEnsureAncestorsM_noFileTree (Internal.ancestorChain p p.toList.length) s1 (by subst hs1; exact ht)
            cases ra with
            | error _ => exact hta
            | ok _ =>
              cases existOk with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact vfsCreateDirPure_noFileTree sa p hta
              | true =>
                simp only [↓reduceIte]
                exact vfsCreateDirExistOkM_noFileTree p sa hta

private theorem buggyCopyTreeGoNoLoopM_never_invalidInput :
    ∀ fuel src dst dirsExistOk st, NoFileTree st.tree →
      NoFileTree (buggyCopyTreeGoNoLoopM src dst dirsExistOk fuel st).2.tree ∧
      (∀ e, (buggyCopyTreeGoNoLoopM src dst dirsExistOk fuel st).1 = .error e → e.kind ≠ .invalidInput) := by
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
  intro fuel; induction fuel with
  | zero =>
    intro _ _ _ st ht
    simp only [buggyCopyTreeGoNoLoopM, pure, StateT.pure]
    exact ⟨ht, fun _ h => by cases h; intro hk; cases hk⟩
  | succ fuel ih =>
    intro src dst dirsExistOk st ht
    simp only [buggyCopyTreeGoNoLoopM, Bind.bind, bind, StateT.bind, Pure.pure, pure]
    cases hSt : vfsOps.stat true src st with
    | mk rs s1 =>
      have hs1 : s1 = st := (congrArg Prod.snd hSt).symm
      cases rs with
      | error e1 =>
        dsimp only [StateT.pure]
        exact ⟨by subst hs1; exact ht, fun eOut h => by cases h; exact hStatNe true src st _ (congrArg Prod.fst hSt)⟩
      | ok st1 =>
        dsimp only
        by_cases hND : (st1.kind != .dir) = true
        · simp only [hND, ↓reduceIte, StateT.pure]
          exact ⟨by subst hs1; exact ht, fun eOut h => by cases h; intro hk; cases hk⟩
        · have hNDF : (st1.kind != .dir) = false := Bool.eq_false_iff.mpr hND
          simp only [hNDF, Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.bind]
          cases hRp : vfsOps.realPath src s1 with
          | mk rr s2 =>
            have hs2 : s2 = s1 := (congrArg Prod.snd hRp).symm
            cases rr with
            | error e2 =>
              exact ⟨by subst hs2; subst hs1; exact ht, fun eOut h => by cases h; exact hRpNe src s1 _ (congrArg Prod.fst hRp)⟩
            | ok _ =>
              dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
              cases hLs : Internal.listDirSortedM vfsOps src s2 with
              | mk rl s3 =>
                have hs3 : s3 = s2 := by
                  have hSnd : s3 = (Internal.listDirSortedM vfsOps src s2).2 := (congrArg Prod.snd hLs).symm
                  rw [hSnd]
                  dsimp only [Internal.listDirSortedM, vfsOps, Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                  cases vfsReadDirPure s2 src <;> rfl
                cases rl with
                | error e3 =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                  exact ⟨by subst hs3; subst hs2; subst hs1; exact ht, fun eOut h => by cases h; exact hListNe src s2 _ (congrArg Prod.fst hLs)⟩
                | ok names =>
                  dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                  cases hMk : Internal.mkdirImplM vfsOps dst true dirsExistOk s3 with
                  | mk rm s4 =>
                    have ht4 : NoFileTree s4.tree := by
                      have hEq : s4 = (Internal.mkdirImplM vfsOps dst true dirsExistOk s3).2 := (congrArg Prod.snd hMk).symm
                      rw [hEq]; apply vfsMkdirImplM_noFileTree
                      subst hs3; subst hs2; subst hs1; exact ht
                    cases rm with
                    | error e4 =>
                      dsimp only [StateT.pure, Pure.pure, pure]
                      exact ⟨ht4, fun eOut h => by cases h; exact vfsOps_mkdir_never_invalidInput dst true dirsExistOk s3 _ (congrArg Prod.fst hMk)⟩
                    | ok _ =>
                      apply forEachChildM_invariant (fun s => NoFileTree s.tree) _ _ names.toList s4 ht4
                      intro n sChildSt hChildHt
                      dsimp only [Bind.bind, bind, StateT.bind, Pure.pure, pure, StateT.pure]
                      cases hSc : vfsOps.stat true (Internal.join src n) sChildSt with
                      | mk rsc sc2 =>
                        have hsc2 : sc2 = sChildSt := (congrArg Prod.snd hSc).symm
                        cases rsc with
                        | error e5 =>
                          dsimp only [StateT.pure, Pure.pure, pure]
                          exact ⟨by subst hsc2; exact hChildHt, fun eOut h => by cases h; exact hStatNe true _ sChildSt _ (congrArg Prod.fst hSc)⟩
                        | ok cst =>
                          have hSc1 : vfsStatPure sChildSt true (Internal.join src n) = .ok cst := congrArg Prod.fst hSc
                          have hResTrue : ∃ nd, vfsResolveSegs sChildSt.nodes "/"
                              (vfsSplitSegs (vfsAbsNorm sChildSt.cwd (Internal.join src n))) true 1024 = .ok nd ∧
                              vfsToStat nd.2 = cst := by
                            unfold vfsStatPure at hSc1
                            cases hR : vfsResolveSegs sChildSt.nodes "/"
                                (vfsSplitSegs (vfsAbsNorm sChildSt.cwd (Internal.join src n))) true 1024 with
                            | error _ => simp [hR] at hSc1
                            | ok nd =>
                              simp only [hR, Except.ok.injEq] at hSc1
                              exact ⟨nd, rfl, hSc1⟩
                          rcases hResTrue with ⟨⟨_, nd⟩, hR, hStEq⟩
                          have ⟨m, hNd⟩ := vfsResolveSegs_true_noFile_isDir sChildSt.tree hChildHt 1024 "/" _ _ _ hR
                          subst hNd
                          have hCstDir : cst.kind = .dir := by rw [← hStEq]; rfl
                          have hD : (cst.kind == .dir) = true := by rw [hCstDir]; rfl
                          dsimp only
                          simp only [hD, ↓reduceIte]
                          exact ih _ _ dirsExistOk sc2 (by subst hsc2; exact hChildHt)

private theorem reach_fs_vfs_copyTree_loopRejected_noFile :
    ∃ (st : VfsState) (src : String), NoFileTree st.tree ∧
      (∃ stRoot, ((vfsApi.stat "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
        (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 ∧
        ((vfsApi.resolve "/").run st).1 = .ok "/") ∧
      (∃ stSrc, ((vfsApi.stat src).run st).1 = .ok stSrc ∧ stSrc.kind = .dir) ∧
      (∃ c, ((vfsApi.resolve src).run st).1 = .ok c ∧ vfsApi.isAbsolute c ∧ c ≠ "/" ∧
        c ≠ "/loop_dst" ∧ ((vfsApi.resolve (vfsApi.join src "self")).run st).1 = .ok c) ∧
      ((vfsApi.listDir src).run st).1 = .ok #["self"] ∧
      (∃ stSelf, ((vfsApi.stat (vfsApi.join src "self")).run st).1 = .ok stSelf ∧ stSelf.kind = .dir) ∧
      ((vfsApi.lstat "/loop_dst").run st).1.isOk = false := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s =>
        if s == "src" then
          some (.dir 0o755 (fun s2 => if s2 == "self" then some (.symlink "/src" 0o777) else none))
        else none)
      keys := ["/", "/src", "/src/self"]
      cwd := "/"
      nonce := 0 }
  have hNoFile : NoFileTree st.tree := by
    intro segs bs m hGet
    cases segs with
    | nil => simp [st, vfsTreeGet] at hGet
    | cons s rest =>
      simp only [st, vfsTreeGet] at hGet
      by_cases hS : (s == "src") = true
      · simp only [hS, ↓reduceIte] at hGet
        cases rest with
        | nil => simp [vfsTreeGet] at hGet
        | cons s2 rest2 =>
          simp only [vfsTreeGet] at hGet
          by_cases hS2 : (s2 == "self") = true
          · simp only [hS2, ↓reduceIte] at hGet
            cases rest2 <;> simp [vfsTreeGet] at hGet
          · simp [hS2] at hGet
      · simp [hS] at hGet
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
  exact ⟨st, "/src", hNoFile,
    ⟨vfsToStat (.dir 0o755), hStatRoot, rfl, by decide, by decide, hResRoot⟩,
    ⟨vfsToStat (.dir 0o755), hStatSrc, rfl⟩,
    ⟨"/src", hResSrc, by decide, by decide, by decide, hResSelf⟩,
    hListSrc, ⟨vfsToStat (.dir 0o755), hStatSelf, rfl⟩, hLstatLoop⟩

example : ¬ AllPass (test_fs_vfs_copyTree_loopRejected
    { vfsApi with copyTree := fun src dst ok => buggyCopyTreeGoNoLoopM src dst ok 4096 }) := by
  intro h
  rcases reach_fs_vfs_copyTree_loopRejected_noFile with
    ⟨st, src, hNoFile, hRoot, hSrc, hCan, hList, hSelf, hLstat⟩
  have hFail := h st src hRoot hSrc hCan hList hSelf hLstat
  dsimp only [StateT.run, assert] at hFail
  rcases hFail with ⟨⟨e, hErr, hKind⟩, _⟩
  exact (buggyCopyTreeGoNoLoopM_never_invalidInput 4096 src "/loop_dst" false st hNoFile).2 e hErr hKind

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

private theorem maxLockId_ge :
    ∀ (locks : List (Nat × String × LockMode)) (i : Nat) (p : String) (m : LockMode),
      (i, p, m) ∈ locks → i ≤ maxLockId locks
  | (hdId, _, _) :: rest, i, p, m, h => by
    simp only [List.mem_cons] at h
    rcases h with heq | hmem
    · cases heq
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (maxLockId_ge rest i p m hmem) (Nat.le_max_right _ _)

private theorem freshLockId_not_mem (st : VfsState) (p : String) (m : LockMode) :
    (freshLockId st, p, m) ∉ st.locks := by
  intro hmem
  have hle := maxLockId_ge st.locks (freshLockId st) p m hmem
  have hgt : maxLockId st.locks < freshLockId st := by
    unfold freshLockId
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  omega

private theorem filter_ne_fresh_eq :
    ∀ (l : List (Nat × String × LockMode)) (k : Nat),
      (∀ p m, (k, p, m) ∉ l) →
      l.filter (fun (id, _, _) => id != k) = l
  | [], _, _ => rfl
  | (i, p, m) :: rest, k, hk => by
    have hne : i ≠ k := fun heq => hk p m (heq ▸ List.mem_cons_self)
    have hbeq : (i != k) = true := bne_iff_ne.mpr hne
    have hrest : ∀ p' m', (k, p', m') ∉ rest := fun p' m' hm => hk p' m' (List.mem_cons_of_mem _ hm)
    simp [List.filter, hbeq, filter_ne_fresh_eq rest k hrest]

private theorem vfsTreeGet_set_file (bs : ByteArray) (m' : Nat) :
    ∀ (segs : List String) (lastSeg : String) (t : VfsTree) (q : List String),
      (∃ dm dch, vfsTreeGet t segs = some (.dir dm dch)) →
      vfsTreeGet t (segs ++ [lastSeg]) = none →
      (vfsTreeGet (vfsTreeSet t (segs ++ [lastSeg]) (some (.file bs m'))) q).map vfsTreeTopNode =
        if q == (segs ++ [lastSeg]) then some (.file bs m') else (vfsTreeGet t q).map vfsTreeTopNode := by
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
          | nil => simp [vfsTreeGet, vfsTreeTopNode]
          | cons rh rt =>
            simp only [vfsTreeGet, beq_self_eq_true, ↓reduceIte]
            simp [hChNone]
        · have hNe : (qh == lastSeg) = false := beq_false_of_ne hEq
          have hListNe : ((qh :: qt) == [lastSeg]) = false := by simp [hEq]
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
        have hSubDir : ∃ dm dch, vfsTreeGet sub rest = some (.dir dm dch) :=
          ⟨dm, dch, by simpa [vfsTreeGet, hCh] using hGet⟩
        have hSubNone : vfsTreeGet sub (rest ++ [lastSeg]) = none := by
          simpa [vfsTreeGet, hCh] using hNone
        have hNonEmpty : rest ++ [lastSeg] ≠ [] := by simp
        cases hRest : rest ++ [lastSeg] with
        | nil => exact absurd hRest hNonEmpty
        | cons rhd rtl =>
          have hSetEq : vfsTreeSet (.dir mode ch) ((seg :: rest) ++ [lastSeg]) (some (.file bs m')) =
              .dir mode (fun s => if s == seg then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (.file bs m'))) else ch s) := by
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
                    if s == qh then some (vfsTreeSet sub (rest ++ [lastSeg]) (some (.file bs m'))) else ch s) (qh :: qt)).map vfsTreeTopNode =
                  (vfsTreeGet (vfsTreeSet sub (rest ++ [lastSeg]) (some (.file bs m'))) qt).map vfsTreeTopNode := by
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

private theorem vfsTreeNodes_insert_file (t : VfsTree) (parCanon lastSeg : String)
    (bs : ByteArray) (m' : Nat)
    (hParCanon : isCanonPath parCanon = true)
    (hLastValid : Internal.validFileName lastSeg = true)
    (hParDir : ∃ dm, vfsTreeNodes t parCanon = some (.dir dm))
    (hNewNone : vfsTreeNodes t (vfsChildPath parCanon lastSeg) = none) :
    vfsTreeNodes (vfsTreeSet t (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file bs m'))) =
      fun k => if k == vfsChildPath parCanon lastSeg then some (.file bs m') else vfsTreeNodes t k := by
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
    rw [vfsTreeGet_set_file bs m' (vfsSplitSegs parCanon) lastSeg t (vfsSplitSegs k) hParTreeDir hNewTreeNone]
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

private theorem vfsResolveSegs_dir_child_nofollow (nodes : String → Option VfsNode)
    (lastSeg parCanon : String) (parMode : Nat) (hExec : ((parMode / 64) % 2 == 0) = false)
    (nd : VfsNode) (hChild : nodes (vfsChildPath parCanon lastSeg) = some nd) :
    ∀ fuel cur parSegs,
      vfsResolveSegs nodes cur parSegs true fuel = .ok (parCanon, .dir parMode) →
      vfsResolveSegs nodes cur (parSegs ++ [lastSeg]) false (fuel + 1) =
        .ok (vfsChildPath parCanon lastSeg, nd) := by
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
      | some nd' =>
        simp only [hNode] at hOk
        cases nd' with
        | file _ _ => simp at hOk
        | dir m =>
          simp only [Prod.mk.injEq, Except.ok.injEq, VfsNode.dir.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          simp only [List.nil_append, vfsResolveSegs, hNode, hExec, Bool.false_eq_true, ↓reduceIte, hChild]
          cases nd with
          | file _ _ => rfl
          | dir _ => rfl
          | symlink _ _ => rfl
        | symlink target m =>
          simp only [List.nil_append, vfsResolveSegs, hNode]
          exact ih "/" (vfsSplitSegs (Internal.normPath
            (if Internal.isAbsolute target then target else Internal.join ((Internal.parent cur).getD "/") target))) hOk
    | cons seg rest =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd' =>
        simp only [hNode] at hOk
        cases nd' with
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

private theorem vfsResolveSegs_true_ok_implies_false_ok (nodes : String → Option VfsNode) :
    ∀ fuel cur segs res,
      vfsResolveSegs nodes cur segs true fuel = .ok res →
      ∃ res', vfsResolveSegs nodes cur segs false fuel = .ok res' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [vfsResolveSegs] at h
  | succ f ih =>
    intro cur segs res hOk
    simp only [vfsResolveSegs] at hOk
    cases segs with
    | nil =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        cases nd with
        | file bs m => exact ⟨(cur, .file bs m), by simp [vfsResolveSegs, hNode]⟩
        | dir m => exact ⟨(cur, .dir m), by simp [vfsResolveSegs, hNode]⟩
        | symlink t m => exact ⟨(cur, .symlink t m), by simp [vfsResolveSegs, hNode]⟩
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
            rcases ih (vfsChildPath cur seg) rest res hOk with ⟨r', hr'⟩
            exact ⟨r', by simp [vfsResolveSegs, hNode, hef, hr']⟩
        | symlink target m =>
          rcases ih "/" _ res hOk with ⟨r', hr'⟩
          exact ⟨r', by simp [vfsResolveSegs, hNode, hr']⟩

private theorem hasLockConflict_exclusive_false (locks : List (Nat × String × LockMode))
    (canon : String) (mode : LockMode) :
    hasLockConflict locks canon .exclusive = false →
    hasLockConflict locks canon mode = false := by
  intro h
  simp only [hasLockConflict, List.any_eq_false] at h ⊢
  intro x hx hMatch
  apply h x hx
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hMatch ⊢
  exact ⟨hMatch.1, Or.inl rfl⟩

private theorem hasLockConflict_cons_self_mode (id : Nat) (canon : String)
    (outerMode innerMode : LockMode) (locks : List (Nat × String × LockMode))
    (hEx : outerMode = .exclusive ∨ innerMode = .exclusive) :
    hasLockConflict ((id, canon, outerMode) :: locks) canon innerMode = true := by
  have hSelf : (Raw.LockMode.exclusive == Raw.LockMode.exclusive) = true := rfl
  rcases hEx with rfl | rfl <;> simp [hasLockConflict, hSelf]

private theorem vfsReleaseLockPure_fresh (st st1 : VfsState) (key path : String) (mode : LockMode)
    (hTrees : st1 = { st with locks := (freshLockId st, key, mode) :: st.locks, nextLockId := freshLockId st } ∨
      ∃ newTree newKeys, st1 = { st with tree := newTree, keys := newKeys, locks := (freshLockId st, key, mode) :: st.locks, nextLockId := freshLockId st }) :
    vfsReleaseLockPure st1 { handleId := freshLockId st, path := path, mode := mode } =
      (.ok (), { st1 with locks := st.locks }) := by
  have hNeZero : (freshLockId st == 0) = false := beq_false_of_ne (Nat.succ_ne_zero _)
  have hFilter := filter_ne_fresh_eq st.locks (freshLockId st) (freshLockId_not_mem st)
  rcases hTrees with rfl | ⟨_, _, rfl⟩ <;>
    simp [vfsReleaseLockPure, hNeZero, hFilter]

private theorem vfsAcquireLock_ok_step (st : VfsState) (path : String) (mode : LockMode)
    (createIfMissing nb : Bool) (h : LockHandle) (st1 : VfsState)
    (hAcq : vfsAcquireLockPure st path mode createIfMissing nb = (.ok h, st1)) :
    (h = { handleId := freshLockId st, path := path, mode := mode }) ∧
    ((∃ canon,
        vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 = .ok (canon, .file ByteArray.empty 0) ∧ False) ∨
      (∃ canon bs m,
        vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 = .ok (canon, .file bs m) ∧
        hasLockConflict st.locks canon mode = false ∧
        st1 = { st with locks := (freshLockId st, canon, mode) :: st.locks, nextLockId := freshLockId st }) ∨
      (∃ parSegs lastSeg parCanon parMode e,
        createIfMissing = true ∧
        vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 = .error e ∧
        e.kind = .notFound ∧
        Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm st.cwd path)) [] = some (parSegs, lastSeg) ∧
        vfsResolveSegs st.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode) ∧
        ((parMode / 128) % 2 == 0) = false ∧
        ((parMode / 64) % 2 == 0) = false ∧
        st.nodes (vfsChildPath parCanon lastSeg) = none ∧
        hasLockConflict st.locks (vfsChildPath parCanon lastSeg) mode = false ∧
        st1 = { st with
          tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath parCanon lastSeg :: st.keys
          locks := (freshLockId st, vfsChildPath parCanon lastSeg, mode) :: st.locks
          nextLockId := freshLockId st })) := by
  unfold vfsAcquireLockPure at hAcq
  split at hAcq
  · simp at hAcq
  · cases hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 with
    | ok pair =>
      rcases pair with ⟨canon, nd⟩
      simp only [hRes] at hAcq
      cases nd with
      | dir _ => simp at hAcq
      | symlink _ _ => simp at hAcq
      | file bs m =>
        by_cases hConf : hasLockConflict st.locks canon mode = true
        · simp [hConf] at hAcq
        · have hConfF : hasLockConflict st.locks canon mode = false := Bool.eq_false_iff.mpr hConf
          simp only [hConfF, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hAcq
          rcases hAcq with ⟨rfl, rfl⟩
          exact ⟨rfl, Or.inr (Or.inl ⟨canon, bs, m, rfl, hConfF, rfl⟩)⟩
    | error e =>
      simp only [hRes] at hAcq
      by_cases hNf : (e.kind != .notFound) = true
      · simp [hNf] at hAcq
      · have hNfEq : e.kind = .notFound := by
          cases hk : e.kind <;> rw [hk] at hNf
          all_goals first | rfl | exact absurd hNf (by decide)
        have hNfF : (e.kind != .notFound) = false := Bool.eq_false_iff.mpr hNf
        simp only [hNfF, Bool.false_eq_true, ↓reduceIte] at hAcq
        cases hCre : createIfMissing
        · simp [hCre] at hAcq
        · simp only [hCre, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAcq
          cases hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm st.cwd path)) [] with
          | none => simp [hSplit] at hAcq
          | some sp =>
            rcases sp with ⟨parSegs, lastSeg⟩
            simp only [hSplit] at hAcq
            cases hPar : vfsResolveSegs st.nodes "/" parSegs true 512 with
            | error pe => simp [hPar] at hAcq
            | ok parPair =>
              rcases parPair with ⟨parCanon, parNd⟩
              simp only [hPar] at hAcq
              cases parNd with
              | file _ _ => simp at hAcq
              | symlink _ _ => simp at hAcq
              | dir parMode =>
                by_cases hPerm : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = true
                · simp [hPerm] at hAcq
                · have hPermF : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = false :=
                    Bool.eq_false_iff.mpr hPerm
                  have hW : ((parMode / 128) % 2 == 0) = false := by
                    cases h1 : ((parMode / 128) % 2 == 0) <;> simp_all
                  have hX : ((parMode / 64) % 2 == 0) = false := by
                    cases h2 : ((parMode / 64) % 2 == 0) <;> simp_all
                  simp only [hPermF, Bool.false_eq_true, ↓reduceIte] at hAcq
                  by_cases hConf : hasLockConflict st.locks (vfsChildPath parCanon lastSeg) mode = true
                  · simp [hConf] at hAcq
                  · have hConfF : hasLockConflict st.locks (vfsChildPath parCanon lastSeg) mode = false :=
                      Bool.eq_false_iff.mpr hConf
                    simp only [hConfF, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hAcq
                    rcases hAcq with ⟨rfl, rfl⟩
                    have hNone : st.nodes (vfsChildPath parCanon lastSeg) = none := by
                      cases hCur : st.nodes (vfsChildPath parCanon lastSeg) with
                      | none => rfl
                      | some nd =>
                        exfalso
                        have hAllSegs : vfsSplitSegs (vfsAbsNorm st.cwd path) = parSegs ++ [lastSeg] := by
                          simpa using splitLastAux_spec (vfsSplitSegs (vfsAbsNorm st.cwd path)) [] parSegs lastSeg hSplit
                        have hStep := vfsResolveSegs_dir_child_nofollow st.nodes lastSeg parCanon parMode hX nd hCur 512 "/" parSegs hPar
                        have h1024 := vfsResolveSegs_fuel_mono st.nodes 513 1024 "/" (parSegs ++ [lastSeg]) false
                          (vfsChildPath parCanon lastSeg, nd) (by omega) hStep
                        rw [← hAllSegs, hRes] at h1024
                        cases h1024
                    exact ⟨rfl, Or.inr (Or.inr ⟨parSegs, lastSeg, parCanon, parMode, e, rfl, rfl, hNfEq, rfl, hPar, hW, hX, hNone, hConfF, rfl⟩)⟩

private theorem vfsWithFileLock_action_step {α : Type} (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (action : StateM VfsState (Except FsError α)) :
    (vfsApi.withFileLock path mode createIfMissing action).run s₀ =
      match vfsAcquireLockPure s₀ path mode createIfMissing false with
      | (.error e, st') => (.error e, st')
      | (.ok h, st1) =>
        let (r, st2) := action.run st1
        let (relRes, s₁) := vfsReleaseLockPure st2 h
        match r with
        | .error e => (.error e, s₁)
        | .ok a =>
          match relRes with
          | .ok () => (.ok a, s₁)
          | .error re => (.error re, s₁) := by
  dsimp only [vfsApi, Internal.mkApiM, Internal.withFileLockImplM, Internal.bracketLockM,
    vfsOps, StateT.run, StateT.tryFinally, Id.finally,
    tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
  cases hA : vfsAcquireLockPure s₀ path mode createIfMissing false with
  | mk res st1 =>
    cases res with
    | error e => rfl
    | ok h =>
      dsimp only [StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      cases hAct : action.run st1 with
      | mk r st2 =>
        dsimp only [StateT.run] at hAct
        rw [hAct]
        dsimp only [StateT.bind, bind, StateT.pure, pure, Id.instMonad]
        cases vfsReleaseLockPure st2 h with
        | mk relRes s₁ =>
          cases r with
          | error e => rfl
          | ok a => cases relRes <;> rfl

private theorem vfsWithFileLock_pure_step {α : Type} (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (r : Except FsError α) :
    (vfsApi.withFileLock path mode createIfMissing (pure r)).run s₀ =
      match vfsAcquireLockPure s₀ path mode createIfMissing false with
      | (.error e, st') => (.error e, st')
      | (.ok h, st1) =>
        let (relRes, s₁) := vfsReleaseLockPure st1 h
        match r with
        | .error e => (.error e, s₁)
        | .ok a =>
          match relRes with
          | .ok () => (.ok a, s₁)
          | .error re => (.error re, s₁) :=
  vfsWithFileLock_action_step s₀ path mode createIfMissing (pure r)

private theorem vfsTryWithFileLock_pure_step {α : Type} (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (r : Except FsError α) :
    (vfsApi.tryWithFileLock path mode createIfMissing (pure r)).run s₀ =
      match vfsAcquireLockPure s₀ path mode createIfMissing true with
      | (.error e, st') =>
        if e.kind == .wouldBlock then (.ok none, st') else (.error e, st')
      | (.ok h, st1) =>
        let (relRes, s₁) := vfsReleaseLockPure st1 h
        match r with
        | .error e => (.error e, s₁)
        | .ok a =>
          match relRes with
          | .ok () => (.ok (some a), s₁)
          | .error re => (.error re, s₁) := by
  dsimp only [vfsApi, Internal.mkApiM, Internal.tryWithFileLockImplM, Internal.bracketLockM,
    vfsOps, StateT.run, StateT.tryFinally, Id.finally,
    tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
  cases hA : vfsAcquireLockPure s₀ path mode createIfMissing true with
  | mk res st1 =>
    cases res with
    | error e =>
      dsimp only
      by_cases hw : (e.kind == .wouldBlock) = true <;> simp [hw] <;> rfl
    | ok h =>
      dsimp only [StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      cases vfsReleaseLockPure st1 h with
      | mk relRes s₁ =>
        cases r with
        | error e => rfl
        | ok a => cases relRes <;> rfl

private theorem vfsAcquireLock_after_exclusive_probe (s₀ : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool)
    (hProbe : ((vfsApi.tryWithFileLock path .exclusive createIfMissing (pure (.ok ()))).run s₀).1 = .ok (some ())) :
    isValidLockPath path = true ∧
    ((∃ canon bs m,
        vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 = .ok (canon, .file bs m) ∧
        hasLockConflict s₀.locks canon .exclusive = false ∧
        (∀ nb, vfsAcquireLockPure s₀ path mode createIfMissing nb =
          (.ok { handleId := freshLockId s₀, path := path, mode := mode },
            { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }))) ∨
      (∃ parSegs lastSeg parCanon parMode,
        createIfMissing = true ∧
        Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] = some (parSegs, lastSeg) ∧
        vfsResolveSegs s₀.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode) ∧
        ((parMode / 128) % 2 == 0) = false ∧
        ((parMode / 64) % 2 == 0) = false ∧
        s₀.nodes (vfsChildPath parCanon lastSeg) = none ∧
        hasLockConflict s₀.locks (vfsChildPath parCanon lastSeg) .exclusive = false ∧
        (∀ nb, vfsAcquireLockPure s₀ path mode true nb =
          (.ok { handleId := freshLockId s₀, path := path, mode := mode },
            { s₀ with
              tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
              nextLockId := freshLockId s₀ })))) := by
  rw [vfsTryWithFileLock_pure_step] at hProbe
  cases hA : vfsAcquireLockPure s₀ path .exclusive createIfMissing true with
  | mk res st' =>
    rw [hA] at hProbe
    cases res with
    | error e =>
      by_cases hw : (e.kind == .wouldBlock) = true <;> simp [hw] at hProbe
    | ok hEx =>
      have ⟨rfl, hCases⟩ := vfsAcquireLock_ok_step s₀ path .exclusive createIfMissing true hEx st' hA
      have hValid : isValidLockPath path = true := by
        unfold vfsAcquireLockPure at hA
        cases hv : isValidLockPath path <;> simp_all
      refine ⟨hValid, ?_⟩
      rcases hCases with ⟨_, _, hFalse⟩ | ⟨canon, bs, m, hRes, hConfEx, _⟩ |
          ⟨parSegs, lastSeg, parCanon, parMode, e, hCre, hRes, hNf, hSplit, hPar, hW, hX, hNone, hConfEx, _⟩
      · exact hFalse.elim
      · refine Or.inl ⟨canon, bs, m, hRes, hConfEx, fun nb => ?_⟩
        have hConfMode := hasLockConflict_exclusive_false s₀.locks canon mode hConfEx
        simp [vfsAcquireLockPure, hValid, hRes, hConfMode]
      · refine Or.inr ⟨parSegs, lastSeg, parCanon, parMode, hCre, hSplit, hPar, hW, hX, hNone, hConfEx, fun nb => ?_⟩
        have hConfMode := hasLockConflict_exclusive_false s₀.locks (vfsChildPath parCanon lastSeg) mode hConfEx
        have hPermF : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = false := by simp [hW, hX]
        have hNfBool : (e.kind != .notFound) = false := by rw [hNf]; decide
        unfold vfsAcquireLockPure
        rw [hValid]
        dsimp only
        rw [hRes]
        dsimp only
        simp [hNfBool, hSplit, hPar, hPermF, hConfMode]

private theorem vfsResolveSegs_after_create (s₀ : VfsState) (path parCanon lastSeg : String)
    (parSegs : List String) (parMode : Nat)
    (hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] = some (parSegs, lastSeg))
    (hPar : vfsResolveSegs s₀.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode))
    (hX : ((parMode / 64) % 2 == 0) = false)
    (hNone : s₀.nodes (vfsChildPath parCanon lastSeg) = none) :
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
      .ok (vfsChildPath parCanon lastSeg, .file ByteArray.empty 0o644) := by
  intro s₁
  have hAllSegs : vfsSplitSegs (vfsAbsNorm s₀.cwd path) = parSegs ++ [lastSeg] := by
    simpa using splitLastAux_spec (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] parSegs lastSeg hSplit
  have hAllValid := vfsSplitSegs_normPath_valid
    (if Internal.isAbsolute path then path else Internal.join s₀.cwd path)
  have hParValid : ∀ s ∈ parSegs, Internal.validFileName s = true := fun s hs =>
    hAllValid s (by rw [← vfsAbsNorm, hAllSegs]; simp [hs])
  have hLastValid : Internal.validFileName lastSeg = true :=
    hAllValid lastSeg (by rw [← vfsAbsNorm, hAllSegs]; simp)
  have hParCanon : isCanonPath parCanon = true :=
    vfsResolveSegs_isCanon s₀.nodes 512 "/" parSegs true (parCanon, .dir parMode) (by decide) hParValid hPar
  have hParLookup : s₀.nodes parCanon = some (.dir parMode) :=
    vfsResolveSegs_ok_node s₀.nodes 512 "/" parSegs true parCanon (.dir parMode) hPar
  have hNodesEq :
      s₁.nodes = fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))) = _
    exact vfsTreeNodes_insert_file s₀.tree parCanon lastSeg ByteArray.empty 0o644 hParCanon hLastValid ⟨parMode, hParLookup⟩ hNone
  have hParNew := vfsResolveSegs_insert_fresh s₀.nodes (vfsChildPath parCanon lastSeg)
    (.file ByteArray.empty 0o644) hNone 512 "/" parSegs true (parCanon, .dir parMode) hPar
  have hChildNew :
      (fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k)
        (vfsChildPath parCanon lastSeg) = some (.file ByteArray.empty 0o644) := by simp
  have hStep := vfsResolveSegs_dir_child_nofollow
    (fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k)
    lastSeg parCanon parMode hX (.file ByteArray.empty 0o644) hChildNew 512 "/" parSegs hParNew
  have h1024 := vfsResolveSegs_fuel_mono
    (fun k => if k == vfsChildPath parCanon lastSeg then some (.file ByteArray.empty 0o644) else s₀.nodes k)
    513 1024 "/" (parSegs ++ [lastSeg]) false (vfsChildPath parCanon lastSeg, .file ByteArray.empty 0o644)
    (by omega) hStep
  rw [← hAllSegs] at h1024
  change vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 = _
  rw [hNodesEq, h1024]

private theorem vfsProbe_after_release_created (s₀ : VfsState) (path parCanon lastSeg : String)
    (parSegs : List String) (parMode : Nat)
    (hValid : isValidLockPath path = true)
    (hSplit : Internal.splitLastAux (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) [] = some (parSegs, lastSeg))
    (hPar : vfsResolveSegs s₀.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode))
    (hX : ((parMode / 64) % 2 == 0) = false)
    (hNone : s₀.nodes (vfsChildPath parCanon lastSeg) = none)
    (hConfEx : hasLockConflict s₀.locks (vfsChildPath parCanon lastSeg) .exclusive = false) :
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
      .ok (vfsChildPath parCanon lastSeg, .file ByteArray.empty 0o644) ∧
    ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
  intro s₁
  have hResS1 := vfsResolveSegs_after_create s₀ path parCanon lastSeg parSegs parMode hSplit hPar hX hNone
  refine ⟨hResS1, ?_⟩
  rw [vfsTryWithFileLock_pure_step]
  have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
      (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
        { s₁ with locks := (freshLockId s₁, vfsChildPath parCanon lastSeg, .exclusive) :: s₁.locks,
                  nextLockId := freshLockId s₁ }) := by
    simp [vfsAcquireLockPure, hValid, hResS1, s₁, hConfEx]
  rw [hAcqS1]
  have hRelS1 := vfsReleaseLockPure_fresh s₁
    { s₁ with locks := (freshLockId s₁, vfsChildPath parCanon lastSeg, .exclusive) :: s₁.locks,
              nextLockId := freshLockId s₁ }
    (vfsChildPath parCanon lastSeg) path .exclusive (Or.inl rfl)
  simp [hRelS1]

/-- Proof of `test_fs_vfs_withFileLock_releasesOnOk` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_releasesOnOk :
    AllPass (test_fs_vfs_withFileLock_releasesOnOk vfsApi) := by
  intro s₀ path mode createIfMissing val hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  dsimp only [assert]
  rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
      ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
  · let st1 : VfsState := { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
    let s₁ : VfsState := { st1 with locks := s₀.locks }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 canon path mode (Or.inl rfl)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode createIfMissing (pure (.ok val))).run s₀ = (.ok val, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hResS1 : vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
        .ok (canon, .file bs m) := hRes
    have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
        (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
          { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
      unfold vfsAcquireLockPure
      rw [hValid]
      dsimp only
      rw [hResS1]
      dsimp only
      simp [s₁, st1, hConfEx]
    have hRelS1 := vfsReleaseLockPure_fresh s₁
      { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
      canon path .exclusive (Or.inl rfl)
    have hP : ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
      rw [vfsTryWithFileLock_pure_step, hAcqS1]
      simp [hRelS1]
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩
  · let st1 : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
        nextLockId := freshLockId s₀ }
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode true (pure (.ok val))).run s₀ = (.ok val, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hP := (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_releasesOnOk` using a `0o444` read-only file with `createIfMissing = true`. -/
theorem reach_fs_vfs_withFileLock_releasesOnOk :
    CanReach (test_fs_vfs_withFileLock_releasesOnOk vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "ro.lock" then some (.file (ByteArray.mk #[42]) 0o444) else none)
      keys := ["/ro.lock"]
      cwd := "/"
      nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/ro.lock")) false 1024 =
      .ok ("/ro.lock", .file (ByteArray.mk #[42]) 0o444) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/ro.lock" = "/ro.lock" from by decide,
        show vfsSplitSegs "/ro.lock" = ["ro.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "ro.lock" = "/ro.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/ro.lock" = some (.file (ByteArray.mk #[42]) 0o444) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/ro.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/ro.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/ro.lock", mode := .exclusive },
          { st with locks := (freshLockId st, "/ro.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }) := by
      unfold vfsAcquireLockPure
      rw [show isValidLockPath "/ro.lock" = true from by decide]
      dsimp only
      rw [hRes]
      simp [st, hasLockConflict]
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with locks := (freshLockId st, "/ro.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }
      "/ro.lock" "/ro.lock" .exclusive (Or.inl rfl)
    simp [hRel]
  exact ⟨st, "/ro.lock", .shared, true, 7, hProbe,
    proof_fs_vfs_withFileLock_releasesOnOk st "/ro.lock" .shared true 7 hProbe⟩

/-- Proof of `test_fs_vfs_withFileLock_releasesOnError` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_releasesOnError :
    AllPass (test_fs_vfs_withFileLock_releasesOnError vfsApi) := by
  intro s₀ path mode createIfMissing err hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  dsimp only [assert]
  rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
      ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
  · let st1 : VfsState := { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
    let s₁ : VfsState := { st1 with locks := s₀.locks }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 canon path mode (Or.inl rfl)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode createIfMissing (pure (.error err : Except FsError Unit))).run s₀ =
        (.error err, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hResS1 : vfsResolveSegs s₁.nodes "/" (vfsSplitSegs (vfsAbsNorm s₁.cwd path)) false 1024 =
        .ok (canon, .file bs m) := hRes
    have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
        (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
          { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
      unfold vfsAcquireLockPure
      rw [hValid]
      dsimp only
      rw [hResS1]
      dsimp only
      simp [s₁, st1, hConfEx]
    have hRelS1 := vfsReleaseLockPure_fresh s₁
      { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
      canon path .exclusive (Or.inl rfl)
    have hP : ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
      rw [vfsTryWithFileLock_pure_step, hAcqS1]
      simp [hRelS1]
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩
  · let st1 : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
        nextLockId := freshLockId s₀ }
    let s₁ : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath parCanon lastSeg :: s₀.keys
        nextLockId := freshLockId s₀ }
    have hRel := vfsReleaseLockPure_fresh s₀ st1 (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
    dsimp only [st1] at hRel
    have hW : (vfsApi.withFileLock path mode true (pure (.error err : Except FsError Unit))).run s₀ =
        (.error err, s₁) := by
      rw [vfsWithFileLock_pure_step, hAcq false]
      dsimp only
      rw [hRel]
    have hP := (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
    exact ⟨⟨congrArg Prod.fst hW,
      (congrArg (fun st => ((vfsApi.tryWithFileLock path .exclusive false (pure (.ok ()))).run st).1)
        (congrArg Prod.snd hW)).trans hP⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_releasesOnError`. -/
theorem reach_fs_vfs_withFileLock_releasesOnError :
    CanReach (test_fs_vfs_withFileLock_releasesOnError vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  let err : FsError := { kind := .permissionDenied, message := "boom" }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/err.lock")) false 1024 =
      .error { kind := .notFound, path := some "/err.lock", message := "no such file or directory: /err.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/err.lock" = "/err.lock" from by decide,
        show vfsSplitSegs "/err.lock" = ["err.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "err.lock" = "/err.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/err.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/err.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/err.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/err.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "err.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "err.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "err.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      unfold vfsAcquireLockPure
      rw [show isValidLockPath "/err.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/err.lock" = "/err.lock" from by decide,
          show vfsSplitSegs "/err.lock" = ["err.lock"] from by decide,
          show Internal.splitLastAux ["err.lock"] [] = some ([], "err.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "err.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "err.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "err.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "err.lock") "/err.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/err.lock", .exclusive, true, err, hProbe,
    proof_fs_vfs_withFileLock_releasesOnError st "/err.lock" .exclusive true err hProbe⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_sharedCoexists` on `vfsApi`. -/
theorem proof_fs_vfs_tryWithFileLock_sharedCoexists :
    AllPass (test_fs_vfs_tryWithFileLock_sharedCoexists vfsApi) := by
  intro s₀ path val hIsOk
  change ((vfsApi.withFileLock path .shared true
      (vfsApi.tryWithFileLock path .shared false (pure (Except.ok val)))).run s₀).1.isOk = true at hIsOk
  change (((vfsApi.withFileLock path .shared true
      (vfsApi.tryWithFileLock path .shared false (pure (Except.ok val)))).run s₀).1 = .ok (some val)) ∧ True
  rw [vfsWithFileLock_action_step] at hIsOk ⊢
  cases hOuter : vfsAcquireLockPure s₀ path .shared true false with
  | mk rO stO =>
    cases rO with
    | error e => rw [hOuter] at hIsOk; cases hIsOk
    | ok hO =>
      dsimp only at hIsOk ⊢
      rcases vfsAcquireLock_ok_step s₀ path .shared true false hO stO hOuter with ⟨rfl, hCases⟩
      have hValid : isValidLockPath path = true := by
        unfold vfsAcquireLockPure at hOuter
        cases hv : isValidLockPath path <;> simp_all
      have hSharedNe : (Raw.LockMode.shared == Raw.LockMode.exclusive) = false := rfl
      have hInner : (vfsApi.tryWithFileLock path .shared false (pure (Except.ok val))).run stO =
          (.ok (some val), { stO with nextLockId := freshLockId stO }) := by
        rw [vfsTryWithFileLock_pure_step]
        rcases hCases with ⟨_, _, hF⟩ | ⟨canon, bs, m, hRes, hConf, rfl⟩ |
            ⟨parSegs, lastSeg, parCanon, parMode, _, _, hRes, _, hSplit, hPar, _, hX, hNone, hConf, rfl⟩
        · exact hF.elim
        · have hConfIn : hasLockConflict ((freshLockId s₀, canon, .shared) :: s₀.locks) canon .shared = false := by
            simp only [hasLockConflict, hSharedNe]
            simpa [hasLockConflict, hSharedNe] using hConf
          let stO' : VfsState := { s₀ with locks := (freshLockId s₀, canon, .shared) :: s₀.locks, nextLockId := freshLockId s₀ }
          have hAcqIn : vfsAcquireLockPure stO' path .shared false true =
              (.ok { handleId := freshLockId stO', path := path, mode := .shared },
                { stO' with locks := (freshLockId stO', canon, .shared) :: stO'.locks, nextLockId := freshLockId stO' }) := by
            unfold vfsAcquireLockPure
            rw [hValid]
            dsimp only
            rw [show stO'.nodes = s₀.nodes from rfl, show stO'.cwd = s₀.cwd from rfl, hRes]
            dsimp only
            simp [stO', hConfIn]
          rw [hAcqIn]
          have hRelIn := vfsReleaseLockPure_fresh stO'
            { stO' with locks := (freshLockId stO', canon, .shared) :: stO'.locks, nextLockId := freshLockId stO' }
            canon path .shared (Or.inl rfl)
          dsimp only [stO'] at hRelIn ⊢
          simp [hRelIn]
        · let newTree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          let stO' : VfsState :=
            { s₀ with
              tree := newTree
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, .shared) :: s₀.locks
              nextLockId := freshLockId s₀ }
          have hResStO' := vfsResolveSegs_after_create s₀ path parCanon lastSeg parSegs parMode hSplit hPar hX hNone
          have hConfIn : hasLockConflict stO'.locks (vfsChildPath parCanon lastSeg) .shared = false := by
            simp only [stO', hasLockConflict, hSharedNe]
            simpa [hasLockConflict, hSharedNe] using hConf
          have hAcqIn : vfsAcquireLockPure stO' path .shared false true =
              (.ok { handleId := freshLockId stO', path := path, mode := .shared },
                { stO' with
                  locks := (freshLockId stO', vfsChildPath parCanon lastSeg, .shared) :: stO'.locks
                  nextLockId := freshLockId stO' }) := by
            unfold vfsAcquireLockPure
            rw [hValid]
            dsimp only
            rw [show stO'.nodes = ({ s₀ with tree := newTree, keys := vfsChildPath parCanon lastSeg :: s₀.keys, nextLockId := freshLockId s₀ } : VfsState).nodes from rfl,
                show stO'.cwd = ({ s₀ with tree := newTree, keys := vfsChildPath parCanon lastSeg :: s₀.keys, nextLockId := freshLockId s₀ } : VfsState).cwd from rfl,
                hResStO']
            dsimp only
            simp [stO', hConfIn]
          rw [hAcqIn]
          have hRelIn := vfsReleaseLockPure_fresh stO'
            { stO' with
              locks := (freshLockId stO', vfsChildPath parCanon lastSeg, .shared) :: stO'.locks
              nextLockId := freshLockId stO' }
            (vfsChildPath parCanon lastSeg) path .shared (Or.inl rfl)
          dsimp only [stO', newTree] at hRelIn ⊢
          simp [hRelIn]
      rw [hInner]
      dsimp only [assert]
      rcases hCases with ⟨_, _, hF⟩ | ⟨canon, _, _, _, _, rfl⟩ |
          ⟨_, lastSeg, parCanon, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      · exact hF.elim
      · have hRelOk : (vfsReleaseLockPure
            { s₀ with
              locks := (freshLockId s₀, canon, .shared) :: s₀.locks
              nextLockId := freshLockId { s₀ with locks := (freshLockId s₀, canon, .shared) :: s₀.locks, nextLockId := freshLockId s₀ } }
            { handleId := freshLockId s₀, path := path, mode := .shared }).1 = .ok () := by
          simp [vfsReleaseLockPure, freshLockId]
        rw [hRelOk]
        exact ⟨rfl, trivial⟩
      · have hRelOk : (vfsReleaseLockPure
            { s₀ with
              tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, .shared) :: s₀.locks
              nextLockId := freshLockId { s₀ with
                tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
                keys := vfsChildPath parCanon lastSeg :: s₀.keys
                locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, .shared) :: s₀.locks
                nextLockId := freshLockId s₀ } }
            { handleId := freshLockId s₀, path := path, mode := .shared }).1 = .ok () := by
          simp [vfsReleaseLockPure, freshLockId]
        rw [hRelOk]
        exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_sharedCoexists`. -/
theorem reach_fs_vfs_tryWithFileLock_sharedCoexists :
    CanReach (test_fs_vfs_tryWithFileLock_sharedCoexists vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/sh.lock")) false 1024 =
      .error { kind := .notFound, path := some "/sh.lock", message := "no such file or directory: /sh.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/sh.lock" = "/sh.lock" from by decide,
        show vfsSplitSegs "/sh.lock" = ["sh.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "sh.lock" = "/sh.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/sh.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hOuter : ((vfsApi.withFileLock "/sh.lock" .shared true (vfsApi.tryWithFileLock "/sh.lock" .shared false (pure (Except.ok 42)))).run st).1.isOk = true := by
    rw [vfsWithFileLock_action_step]
    let stO :=
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "sh.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "sh.lock", .shared) :: st.locks
        nextLockId := freshLockId st }
    have hAcqO : vfsAcquireLockPure st "/sh.lock" .shared true false =
        (.ok { handleId := freshLockId st, path := "/sh.lock", mode := .shared }, stO) := by
      unfold vfsAcquireLockPure
      rw [show isValidLockPath "/sh.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/sh.lock" = "/sh.lock" from by decide,
          show vfsSplitSegs "/sh.lock" = ["sh.lock"] from by decide,
          show Internal.splitLastAux ["sh.lock"] [] = some ([], "sh.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict, stO]
      decide
    have hParNew := vfsResolveSegs_insert_fresh st.nodes (vfsChildPath "/" "sh.lock")
      (.file ByteArray.empty 0o644) (show st.nodes "/sh.lock" = none from rfl) 512 "/" [] true ("/", .dir 0o755) hPar
    have hNodesEq : stO.nodes = fun k =>
        if k == vfsChildPath "/" "sh.lock" then some (.file ByteArray.empty 0o644) else st.nodes k := by
      change vfsTreeNodes (vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))) = _
      exact vfsTreeNodes_insert_file st.tree "/" "sh.lock" ByteArray.empty 0o644 (by decide) (by decide)
        ⟨0o755, show st.nodes "/" = some (.dir 0o755) from rfl⟩ (show st.nodes "/sh.lock" = none from rfl)
    have hStep := vfsResolveSegs_dir_child_nofollow stO.nodes "sh.lock" "/" 0o755 (by decide)
      (.file ByteArray.empty 0o644) (by rw [hNodesEq]; simp) 512 "/" [] (by rw [hNodesEq]; exact hParNew)
    have hResO : vfsResolveSegs stO.nodes "/" (vfsSplitSegs (vfsAbsNorm stO.cwd "/sh.lock")) false 1024 =
        .ok ("/sh.lock", .file ByteArray.empty 0o644) := by
      change vfsResolveSegs stO.nodes "/" (vfsSplitSegs (vfsAbsNorm "/" "/sh.lock")) false 1024 = _
      rw [show vfsAbsNorm "/" "/sh.lock" = "/sh.lock" from by decide,
          show vfsSplitSegs "/sh.lock" = ["sh.lock"] from by decide]
      exact vfsResolveSegs_fuel_mono stO.nodes 513 1024 "/" ["sh.lock"] false _ (by omega) hStep
    have hConfO : hasLockConflict stO.locks "/sh.lock" .shared = false := by
      dsimp [stO, st, hasLockConflict]
      decide
    have hIn : (vfsApi.tryWithFileLock "/sh.lock" .shared false (pure (Except.ok 42))).run stO =
        (.ok (some 42), { stO with nextLockId := freshLockId stO }) := by
      rw [vfsTryWithFileLock_pure_step]
      have hAcqI : vfsAcquireLockPure stO "/sh.lock" .shared false true =
          (.ok { handleId := freshLockId stO, path := "/sh.lock", mode := .shared },
            { stO with locks := (freshLockId stO, "/sh.lock", .shared) :: stO.locks, nextLockId := freshLockId stO }) := by
        unfold vfsAcquireLockPure
        rw [show isValidLockPath "/sh.lock" = true from by decide]
        dsimp only
        rw [hResO]
        dsimp only
        simp [stO, hConfO]
      rw [hAcqI]
      have hRelI := vfsReleaseLockPure_fresh stO
        { stO with locks := (freshLockId stO, "/sh.lock", .shared) :: stO.locks, nextLockId := freshLockId stO }
        "/sh.lock" "/sh.lock" .shared (Or.inl rfl)
      simp [hRelI]
    have hRelO' : (vfsReleaseLockPure { stO with nextLockId := freshLockId stO }
        { handleId := freshLockId st, path := "/sh.lock", mode := .shared }).1 = .ok () := by
      dsimp [vfsReleaseLockPure, stO, st, freshLockId]
    dsimp only [stO] at hAcqO hIn hRelO'
    rw [hAcqO]
    dsimp only
    rw [hIn]
    dsimp only
    cases hRel : vfsReleaseLockPure
        { st with
          tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath "/" "sh.lock" :: st.keys
          locks := (freshLockId st, vfsChildPath "/" "sh.lock", .shared) :: st.locks
          nextLockId := freshLockId { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "sh.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "sh.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "sh.lock", .shared) :: st.locks
            nextLockId := freshLockId st } }
        { handleId := freshLockId st, path := "/sh.lock", mode := .shared } with
    | mk relRes sFinal =>
      have hRelEq : relRes = .ok () := by
        simpa [hRel] using hRelO'
      rw [hRelEq]
      rfl
  exact ⟨st, "/sh.lock", 42, hOuter,
    proof_fs_vfs_tryWithFileLock_sharedCoexists st "/sh.lock" 42 hOuter⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_exclusiveRejects` on `vfsApi`. -/
theorem proof_fs_vfs_tryWithFileLock_exclusiveRejects :
    AllPass (test_fs_vfs_tryWithFileLock_exclusiveRejects vfsApi) := by
  intro s₀ path markerPath outerMode innerMode hModes _ hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hMarkerNone
  rw [vfsWithFileLock_action_step]
  cases hOuter : vfsAcquireLockPure s₀ path outerMode false false with
  | mk rO stO =>
    cases rO with
    | error e =>
      dsimp only
      intro hFalse
      exact hFalse.elim
    | ok hO =>
      dsimp only
      rcases vfsAcquireLock_ok_step s₀ path outerMode false false hO stO hOuter with ⟨rfl, hCases⟩
      have hValid : isValidLockPath path = true := by
        unfold vfsAcquireLockPure at hOuter
        cases hv : isValidLockPath path <;> simp_all
      rcases hCases with ⟨_, _, hF⟩ | ⟨canon, bs, m, hRes, _, rfl⟩ | ⟨_, _, _, _, _, hCre, _⟩
      · exact hF.elim
      · have hConf1 := hasLockConflict_cons_self_mode (freshLockId s₀) canon outerMode innerMode s₀.locks hModes
        have hConf2 := hasLockConflict_cons_self_mode (freshLockId s₀) canon outerMode .exclusive s₀.locks (Or.inr rfl)
        let stO' : VfsState := { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ }
        have hAcq1 : vfsAcquireLockPure stO' path innerMode false true =
            (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, stO') := by
          unfold vfsAcquireLockPure
          rw [hValid]
          dsimp only
          rw [show stO'.nodes = s₀.nodes from rfl, show stO'.cwd = s₀.cwd from rfl, hRes]
          dsimp only
          simp [stO', hConf1]
        have hR1 :
            (vfsApi.tryWithFileLock path innerMode false (vfsApi.writeText markerPath "ran")).run stO' =
              (.ok none, stO') := by
          dsimp only [vfsApi, Internal.mkApiM, Internal.tryWithFileLockImplM, vfsOps, StateT.run, bind, StateT.bind, pure]
          rw [hAcq1]
          rfl
        have hAcq2 : vfsAcquireLockPure stO' path .exclusive false true =
            (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, stO') := by
          unfold vfsAcquireLockPure
          rw [hValid]
          dsimp only
          rw [show stO'.nodes = s₀.nodes from rfl, show stO'.cwd = s₀.cwd from rfl, hRes]
          dsimp only
          simp [stO', hConf2]
        have hR2 :
            (vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run stO' =
              (.ok none, stO') := by
          rw [vfsTryWithFileLock_pure_step, hAcq2]
          rfl
        have hMarkerFalse : ((vfsApi.lstat markerPath).run s₀).1.isOk = false := hMarkerNone
        have hRelO := vfsReleaseLockPure_fresh s₀ stO' canon path outerMode (Or.inl rfl)
        dsimp only [stO'] at hRelO hR1 hR2
        have hAct :
            (do
              let r1 ← vfsApi.tryWithFileLock path innerMode false (vfsApi.writeText markerPath "ran")
              let mAfter ← vfsApi.lstat markerPath
              let r2 ← vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))
              pure (Except.ok (r1, mAfter.isOk, r2)) :
                StateM VfsState (Except FsError (Except FsError (Option Unit) × Bool × Except FsError (Option Unit)))).run
              { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ } =
              (.ok (.ok none, false, .ok none),
                { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ }) := by
          dsimp only [StateT.run, StateT.bind, bind, StateT.pure, pure, Id.instMonad]
          change match (vfsApi.tryWithFileLock path innerMode false (vfsApi.writeText markerPath "ran")).run _ with
            | (r1, s1) =>
              match (vfsApi.lstat markerPath).run s1 with
              | (mAfter, s2) =>
                match (vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run s2 with
                | (r2, s3) => (Except.ok (r1, mAfter.isOk, r2), s3) = _
          rw [hR1]
          dsimp only
          have hLstatM :
              (vfsApi.lstat markerPath).run
                { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ } =
              (((vfsApi.lstat markerPath).run s₀).1,
                { s₀ with locks := (freshLockId s₀, canon, outerMode) :: s₀.locks, nextLockId := freshLockId s₀ }) := rfl
          rw [hLstatM]
          dsimp only
          rw [hR2]
          dsimp only
          rw [hMarkerFalse]
        rw [hAct]
        dsimp only
        rw [hRelO]
        dsimp only [assert]
        exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩
      · cases hCre

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_exclusiveRejects`. -/
theorem reach_fs_vfs_tryWithFileLock_exclusiveRejects :
    CanReach (test_fs_vfs_tryWithFileLock_exclusiveRejects vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "a.lock" then some (.file ByteArray.empty 0o644) else none)
      keys := ["/a.lock"]
      cwd := "/"
      nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/a.lock")) false 1024 =
      .ok ("/a.lock", .file ByteArray.empty 0o644) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/a.lock" = "/a.lock" from by decide,
        show vfsSplitSegs "/a.lock" = ["a.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "a.lock" = "/a.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/a.lock" = some (.file ByteArray.empty 0o644) from rfl]
  have hLstatA : ((vfsApi.lstat "/a.lock").run st).1.isOk = true := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [hRes]; rfl
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  let stO' : VfsState := { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }
  have hAcqO : vfsAcquireLockPure st "/a.lock" .exclusive false false =
      (.ok { handleId := freshLockId st, path := "/a.lock", mode := .exclusive }, stO') := by
    unfold vfsAcquireLockPure; rw [show isValidLockPath "/a.lock" = true from by decide]; dsimp only; rw [hRes]; dsimp only
    simp [st, hasLockConflict, stO']
  have hConf1 : hasLockConflict stO'.locks "/a.lock" .exclusive = true := by
    dsimp [stO', hasLockConflict]
    decide
  have hAcq1 : vfsAcquireLockPure stO' "/a.lock" .exclusive false true =
      (.error { kind := .wouldBlock, path := some "/a.lock", message := "resource temporarily unavailable" }, stO') := by
    unfold vfsAcquireLockPure; rw [show isValidLockPath "/a.lock" = true from by decide]; dsimp only
    rw [show stO'.nodes = st.nodes from rfl, show stO'.cwd = st.cwd from rfl, hRes]; dsimp only; simp [stO', hConf1]
  have hR1 : (vfsApi.tryWithFileLock "/a.lock" .exclusive false (vfsApi.writeText "/marker" "ran")).run stO' =
      (.ok none, stO') := by
    dsimp only [vfsApi, Internal.mkApiM, Internal.tryWithFileLockImplM, vfsOps, StateT.run, bind, StateT.bind, pure]
    rw [hAcq1]; rfl
  have hR2 : (vfsApi.tryWithFileLock "/a.lock" .exclusive false (pure (Except.ok ()))).run stO' =
      (.ok none, stO') := by
    rw [vfsTryWithFileLock_pure_step, hAcq1]; rfl
  have hRelO := vfsReleaseLockPure_fresh st stO' "/a.lock" "/a.lock" .exclusive (Or.inl rfl)
  dsimp only [stO'] at hAcqO hR1 hR2 hRelO
  refine ⟨st, "/a.lock", "/marker", .exclusive, .exclusive, Or.inl rfl, hLstatA, hMarker, ?_⟩
  dsimp only [test_fs_vfs_tryWithFileLock_exclusiveRejects]
  rw [vfsWithFileLock_action_step, hAcqO]
  dsimp only
  have hAct :
      (do
        let r1 ← vfsApi.tryWithFileLock "/a.lock" .exclusive false (vfsApi.writeText "/marker" "ran")
        let mAfter ← vfsApi.lstat "/marker"
        let r2 ← vfsApi.tryWithFileLock "/a.lock" .exclusive false (pure (Except.ok ()))
        pure (Except.ok (r1, mAfter.isOk, r2)) :
          StateM VfsState (Except FsError (Except FsError (Option Unit) × Bool × Except FsError (Option Unit)))).run
        { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st } =
        (.ok (.ok none, false, .ok none),
          { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }) := by
    dsimp only [StateT.run, StateT.bind, bind, StateT.pure, pure, Id.instMonad]
    change match (vfsApi.tryWithFileLock "/a.lock" .exclusive false (vfsApi.writeText "/marker" "ran")).run _ with
      | (r1, s1) =>
        match (vfsApi.lstat "/marker").run s1 with
        | (mAfter, s2) =>
          match (vfsApi.tryWithFileLock "/a.lock" .exclusive false (pure (Except.ok ()))).run s2 with
          | (r2, s3) => (Except.ok (r1, mAfter.isOk, r2), s3) = _
    rw [hR1]
    dsimp only
    have hLstatM :
        (vfsApi.lstat "/marker").run
          { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st } =
        (((vfsApi.lstat "/marker").run st).1,
          { st with locks := (freshLockId st, "/a.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }) := rfl
    rw [hLstatM]
    dsimp only
    rw [hR2]
    dsimp only
    rw [hMarker]
  rw [hAct]
  dsimp only
  rw [hRelO]
  dsimp only [assert]
  exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩

private theorem isValidLockPath_of_not_empty_no_trailing_slash (path : String)
    (hNeEmpty : path.toList ≠ [])
    (hNoSlash : path.toList.length = 1 ∨ path.toList.getLast? ≠ some '/') :
    isValidLockPath path = true := by
  unfold isValidLockPath
  cases hc : path.toList with
  | nil => exact absurd hc hNeEmpty
  | cons c rest =>
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and]
    rcases hNoSlash with hLen | hLast
    · have hLen1 : (c :: rest).length = 1 := by simpa [hc] using hLen
      simp [hLen1]
    · have hLast' : (c :: rest).getLast? ≠ some '/' := by simpa [hc] using hLast
      have hBeq : ((c :: rest).getLast? == some '/') = false := by
        cases hgl : (c :: rest).getLast? with
        | none => rfl
        | some ch =>
          simp only [hgl] at hLast'
          exact beq_false_of_ne (fun h => hLast' (by cases h; rfl))
      simp [hBeq]

/-- Proof of `test_fs_vfs_withFileLock_missingNotCreated` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_missingNotCreated :
    AllPass (test_fs_vfs_withFileLock_missingNotCreated vfsApi) := by
  intro s₀ path mode hNeEmpty hNoSlash hLstat
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hLstat
  rcases hLstat with ⟨e, hStat, hNf⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p => simp [hRes] at hStat
  | error e' =>
    simp only [hRes, Except.error.injEq] at hStat
    subst hStat
    have hAcq : vfsAcquireLockPure s₀ path mode false false = (.error e', s₀) := by
      unfold vfsAcquireLockPure
      rw [hValid]
      dsimp only
      rw [hRes]
      dsimp only
      simp [hNf]
    have hW : (vfsApi.withFileLock path mode false (pure (.ok ()))).run s₀ = (.error e', s₀) := by
      rw [vfsWithFileLock_pure_step, hAcq]
    dsimp only [assert]
    exact ⟨⟨⟨e', congrArg Prod.fst hW, hNf⟩, congrArg Prod.snd hW⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_missingNotCreated`. -/
theorem reach_fs_vfs_withFileLock_missingNotCreated :
    CanReach (test_fs_vfs_withFileLock_missingNotCreated vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hStat : ((vfsApi.lstat "/missing.lock").run st).1 =
      .error { kind := .notFound, path := some "/missing.lock", message := "no such file or directory: /missing.lock" } := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/missing.lock" = "/missing.lock" from by decide,
        show vfsSplitSegs "/missing.lock" = ["missing.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "missing.lock" = "/missing.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/missing.lock" = none from rfl]; rfl
  exact ⟨st, "/missing.lock", .exclusive, by decide, Or.inr (by decide),
    ⟨_, hStat, rfl⟩,
    proof_fs_vfs_withFileLock_missingNotCreated st "/missing.lock" .exclusive (by decide) (Or.inr (by decide)) ⟨_, hStat, rfl⟩⟩

/-- Proof of `test_fs_vfs_withFileLock_symlinkRejected` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_symlinkRejected :
    AllPass (test_fs_vfs_withFileLock_symlinkRejected vfsApi) := by
  intro s₀ path markerPath mode createIfMissing hNeEmpty hNoSlash hLstat hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run, assert] at hLstat hMarkerNone ⊢
  rcases hLstat with ⟨st, hStat, hSym⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes] at hStat
  | ok pair =>
    rcases pair with ⟨canon, nd⟩
    simp only [hRes, Except.ok.injEq] at hStat
    subst hStat
    cases nd with
    | file _ _ => simp [vfsToStat] at hSym
    | dir _ => simp [vfsToStat] at hSym
    | symlink tgt m =>
      dsimp only [Internal.withFileLockImplM, Internal.bracketLockM,
        StateT.tryFinally, Id.finally,
        tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .invalidInput, path := some path, message := s!"symlink rejected for lock: {path}" }, s₀) := by
        unfold vfsAcquireLockPure
        rw [hValid]
        dsimp only
        rw [hRes]
        rfl
      rw [hAcq]
      exact ⟨⟨⟨_, rfl, rfl⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_symlinkRejected`. -/
theorem reach_fs_vfs_withFileLock_symlinkRejected :
    CanReach (test_fs_vfs_withFileLock_symlinkRejected vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "sym.lock" then some (.symlink "/target" 0o777) else none)
      keys := ["/sym.lock"]
      cwd := "/"
      nonce := 0 }
  have hSym : ((vfsApi.lstat "/sym.lock").run st).1 = .ok (vfsToStat (.symlink "/target" 0o777)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/sym.lock" = "/sym.lock" from by decide,
        show vfsSplitSegs "/sym.lock" = ["sym.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "sym.lock" = "/sym.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/sym.lock" = some (.symlink "/target" 0o777) from rfl]; rfl
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "/sym.lock", "/marker", .exclusive, true, by decide, Or.inr (by decide),
    ⟨vfsToStat (.symlink "/target" 0o777), hSym, rfl⟩, hMarker,
    proof_fs_vfs_withFileLock_symlinkRejected st "/sym.lock" "/marker" .exclusive true (by decide) (Or.inr (by decide))
      ⟨vfsToStat (.symlink "/target" 0o777), hSym, rfl⟩ hMarker⟩

/-- Proof of `test_fs_vfs_withFileLock_dirRejected` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_dirRejected :
    AllPass (test_fs_vfs_withFileLock_dirRejected vfsApi) := by
  intro s₀ path markerPath mode createIfMissing hNeEmpty hNoSlash hLstat hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run, assert] at hLstat hMarkerNone ⊢
  rcases hLstat with ⟨st, hStat, hDir⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hRes] at hStat
  | ok pair =>
    rcases pair with ⟨canon, nd⟩
    simp only [hRes, Except.ok.injEq] at hStat
    subst hStat
    cases nd with
    | file _ _ => simp [vfsToStat] at hDir
    | symlink _ _ => simp [vfsToStat] at hDir
    | dir m =>
      dsimp only [Internal.withFileLockImplM, Internal.bracketLockM,
        StateT.tryFinally, Id.finally,
        tryFinally', MonadFinally.tryFinally', StateT.bind, bind, StateT.pure, pure, Id.instMonad]
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, s₀) := by
        unfold vfsAcquireLockPure
        rw [hValid]
        dsimp only
        rw [hRes]
        rfl
      rw [hAcq]
      exact ⟨⟨⟨_, rfl, rfl⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_dirRejected`. -/
theorem reach_fs_vfs_withFileLock_dirRejected :
    CanReach (test_fs_vfs_withFileLock_dirRejected vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "dir" then some (.dir 0o755 fun _ => none) else none)
      keys := ["/dir"]
      cwd := "/"
      nonce := 0 }
  have hDir : ((vfsApi.lstat "/dir").run st).1 = .ok (vfsToStat (.dir 0o755)) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/dir" = "/dir" from by decide,
        show vfsSplitSegs "/dir" = ["dir"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "dir" = "/dir" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/dir" = some (.dir 0o755) from rfl]
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "/dir", "/marker", .exclusive, true, by decide, Or.inr (by decide),
    ⟨vfsToStat (.dir 0o755), hDir, rfl⟩, hMarker,
    proof_fs_vfs_withFileLock_dirRejected st "/dir" "/marker" .exclusive true (by decide) (Or.inr (by decide))
      ⟨vfsToStat (.dir 0o755), hDir, rfl⟩ hMarker⟩

/-- Proof of `test_fs_vfs_withFileLock_createsMissingFile` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_createsMissingFile :
    AllPass (test_fs_vfs_withFileLock_createsMissingFile vfsApi) := by
  intro s₀ path mode hNeEmpty hNoSlash hLstat hResOk
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run] at hLstat
  rcases hLstat with ⟨e, hStat, hNf⟩
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p => simp [hRes] at hStat
  | error e' =>
    simp only [hRes, Except.error.injEq] at hStat
    subst hStat
    change ((vfsApi.withFileLock path mode true (pure (.ok ()))).run s₀).1 = .ok () at hResOk
    change (∃ st, ((vfsApi.lstat path).run ((vfsApi.withFileLock path mode true (pure (.ok ()))).run s₀).2).1 = .ok st ∧ st.kind = .file ∧ st.byteSize = 0) ∧ True
    rw [vfsWithFileLock_pure_step] at hResOk ⊢
    cases hA : vfsAcquireLockPure s₀ path mode true false with
    | mk r st1 =>
      rw [hA] at hResOk
      cases r with
      | error err => simp at hResOk
      | ok h =>
        have hValid : isValidLockPath path = true := by
          unfold vfsAcquireLockPure at hA
          cases hv : isValidLockPath path <;> simp_all
        rcases vfsAcquireLock_ok_step s₀ path mode true false h st1 hA with ⟨rfl, hCases⟩
        rcases hCases with ⟨_, _, hF⟩ | ⟨_, _, _, hResOk', _⟩ |
            ⟨parSegs, lastSeg, parCanon, parMode, _, _, hResErr, _, hSplit, hPar, _, hX, hNone, hConf, rfl⟩
        · exact hF.elim
        · rw [hRes] at hResOk'; cases hResOk'
        · have hRel := vfsReleaseLockPure_fresh s₀
            { s₀ with
              tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
              keys := vfsChildPath parCanon lastSeg :: s₀.keys
              locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
              nextLockId := freshLockId s₀ }
            (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
          have hCreated := vfsResolveSegs_after_create s₀ path parCanon lastSeg parSegs parMode hSplit hPar hX hNone
          dsimp only [vfsApi, Internal.mkApiM, vfsOps, StateT.run, assert]
          rw [hRel]
          dsimp only
          unfold vfsStatPure
          rw [hCreated]
          refine ⟨⟨vfsToStat (.file ByteArray.empty 0o644), rfl, rfl, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_createsMissingFile` using a missing path. -/
theorem reach_fs_vfs_withFileLock_createsMissingFile :
    CanReach (test_fs_vfs_withFileLock_createsMissingFile vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/new.lock")) false 1024 =
      .error { kind := .notFound, path := some "/new.lock", message := "no such file or directory: /new.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new.lock" = "/new.lock" from by decide,
        show vfsSplitSegs "/new.lock" = ["new.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "new.lock" = "/new.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/new.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hStat : ((vfsApi.lstat "/new.lock").run st).1 =
      .error { kind := .notFound, path := some "/new.lock", message := "no such file or directory: /new.lock" } := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [hRes]
  have hOk : ((vfsApi.withFileLock "/new.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok () := by
    rw [vfsWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/new.lock" .exclusive true false =
        (.ok { handleId := freshLockId st, path := "/new.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "new.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "new.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "new.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      unfold vfsAcquireLockPure
      rw [show isValidLockPath "/new.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/new.lock" = "/new.lock" from by decide,
          show vfsSplitSegs "/new.lock" = ["new.lock"] from by decide,
          show Internal.splitLastAux ["new.lock"] [] = some ([], "new.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "new.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "new.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "new.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "new.lock") "/new.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/new.lock", .exclusive, by decide, Or.inr (by decide), ⟨_, hStat, rfl⟩, hOk,
    proof_fs_vfs_withFileLock_createsMissingFile st "/new.lock" .exclusive (by decide) (Or.inr (by decide)) ⟨_, hStat, rfl⟩ hOk⟩

/-- Proof of `test_fs_vfs_withFileLock_preservesExistingBytes` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_preservesExistingBytes :
    AllPass (test_fs_vfs_withFileLock_preservesExistingBytes vfsApi) := by
  intro s₀ path mode createIfMissing hNeEmpty hNoSlash
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  dsimp only [test_fs_vfs_withFileLock_preservesExistingBytes]
  cases hRb : ((vfsApi.readBytes path).run s₀).1 with
  | error e => intro hF; exact hF.elim
  | ok bs₀ =>
    have ⟨hRaw, hRead⟩ : isValidRawPath path = true ∧
        ∃ canon m₀, vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) true 1024 =
          .ok (canon, .file bs₀ m₀) := by
      dsimp only [vfsApi, Internal.mkApiM, vfsOps, StateT.run, vfsReadBytesPure] at hRb
      by_cases hV : isValidRawPath path = true
      · simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRb
        cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) true 1024 with
        | error _ => simp [hR] at hRb
        | ok pair =>
          rcases pair with ⟨canon, nd⟩
          cases nd with
          | dir _ => simp [hR] at hRb
          | symlink _ _ => simp [hR] at hRb
          | file bs m₀ =>
            simp only [hR, Except.ok.injEq] at hRb
            subst hRb
            exact ⟨hV, canon, m₀, rfl⟩
      · have hVF : isValidRawPath path = false := Bool.eq_false_iff.mpr hV
        simp [hVF] at hRb
    rcases hRead with ⟨canon, m₀, hRead⟩
    dsimp only
    intro hResIsOk
    change ((vfsApi.withFileLock path mode createIfMissing (vfsApi.readBytes path)).run s₀).1.isOk = true at hResIsOk
    change (((vfsApi.withFileLock path mode createIfMissing (vfsApi.readBytes path)).run s₀).1 = .ok bs₀ ∧
      ((vfsApi.readBytes path).run ((vfsApi.withFileLock path mode createIfMissing (vfsApi.readBytes path)).run s₀).2).1 = .ok bs₀) ∧ True
    rw [vfsWithFileLock_action_step] at hResIsOk ⊢
    have ⟨res', hNoFollowOk⟩ :=
      vfsResolveSegs_true_ok_implies_false_ok s₀.nodes 1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) (canon, .file bs₀ m₀) hRead
    rcases res' with ⟨canon', nd'⟩
    cases nd' with
    | dir _ =>
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, s₀) := by
        unfold vfsAcquireLockPure
        rw [hValid]
        dsimp only
        rw [hNoFollowOk]
        rfl
      rw [hAcq] at hResIsOk
      cases hResIsOk
    | symlink _ _ =>
      have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
          (.error { kind := .invalidInput, path := some path, message := s!"symlink rejected for lock: {path}" }, s₀) := by
        unfold vfsAcquireLockPure
        rw [hValid]
        dsimp only
        rw [hNoFollowOk]
        rfl
      rw [hAcq] at hResIsOk
      cases hResIsOk
    | file bs' m' =>
      by_cases hConf : hasLockConflict s₀.locks canon' mode = true
      · have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
            (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, s₀) := by
          unfold vfsAcquireLockPure
          rw [hValid]
          dsimp only
          rw [hNoFollowOk]
          dsimp only
          simp [hConf]
        rw [hAcq] at hResIsOk
        cases hResIsOk
      · have hConfF : hasLockConflict s₀.locks canon' mode = false := Bool.eq_false_iff.mpr hConf
        let st1 : VfsState := { s₀ with locks := (freshLockId s₀, canon', mode) :: s₀.locks, nextLockId := freshLockId s₀ }
        have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
            (.ok { handleId := freshLockId s₀, path := path, mode := mode }, st1) := by
          unfold vfsAcquireLockPure
          rw [hValid]
          dsimp only
          rw [hNoFollowOk]
          dsimp only
          simp [hConfF, st1]
        rw [hAcq] at hResIsOk ⊢
        dsimp only [assert]
        have hReadSt1 : (vfsApi.readBytes path).run st1 = (.ok bs₀, st1) := by
          dsimp only [vfsApi, Internal.mkApiM, vfsOps, StateT.run]
          unfold vfsReadBytesPure
          simp only [hRaw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [show st1.nodes = s₀.nodes from rfl, show st1.cwd = s₀.cwd from rfl, hRead]
        rw [hReadSt1]
        dsimp only
        have hRel := vfsReleaseLockPure_fresh s₀ st1 canon' path mode (Or.inl rfl)
        dsimp only [st1] at hRel
        rw [hRel]
        dsimp only
        have hReadS2 : ((vfsApi.readBytes path).run { st1 with locks := s₀.locks }).1 = .ok bs₀ := by
          dsimp only [vfsApi, Internal.mkApiM, vfsOps, StateT.run]
          unfold vfsReadBytesPure
          simp only [hRaw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [show ({ st1 with locks := s₀.locks } : VfsState).nodes = s₀.nodes from rfl,
              show ({ st1 with locks := s₀.locks } : VfsState).cwd = s₀.cwd from rfl, hRead]
        exact ⟨⟨rfl, hReadS2⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_preservesExistingBytes` using a `0o444` read-only existing file. -/
theorem reach_fs_vfs_withFileLock_preservesExistingBytes :
    CanReach (test_fs_vfs_withFileLock_preservesExistingBytes vfsApi) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s => if s == "data.lock" then some (.file (ByteArray.mk #[1, 2, 3]) 0o444) else none)
      keys := ["/data.lock"]
      cwd := "/"
      nonce := 0 }
  have hResTrue : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/data.lock")) true 1024 =
      .ok ("/data.lock", .file (ByteArray.mk #[1, 2, 3]) 0o444) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/data.lock" = "/data.lock" from by decide,
        show vfsSplitSegs "/data.lock" = ["data.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "data.lock" = "/data.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/data.lock" = some (.file (ByteArray.mk #[1, 2, 3]) 0o444) from rfl]
  have hResFalse : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/data.lock")) false 1024 =
      .ok ("/data.lock", .file (ByteArray.mk #[1, 2, 3]) 0o444) := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/data.lock" = "/data.lock" from by decide,
        show vfsSplitSegs "/data.lock" = ["data.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "data.lock" = "/data.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/data.lock" = some (.file (ByteArray.mk #[1, 2, 3]) 0o444) from rfl]
  have hReadSt : ((vfsApi.readBytes "/data.lock").run st).1 = .ok (ByteArray.mk #[1, 2, 3]) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, StateT.run]
    unfold vfsReadBytesPure
    simp only [show isValidRawPath "/data.lock" = true from by decide, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hResTrue]
  let st1 : VfsState := { st with locks := (freshLockId st, "/data.lock", .exclusive) :: st.locks, nextLockId := freshLockId st }
  have hAcq : vfsAcquireLockPure st "/data.lock" .exclusive true false =
      (.ok { handleId := freshLockId st, path := "/data.lock", mode := .exclusive }, st1) := by
    unfold vfsAcquireLockPure
    rw [show isValidLockPath "/data.lock" = true from by decide]
    dsimp only
    rw [hResFalse]
    dsimp only
    simp [st, hasLockConflict, st1]
  have hReadSt1 : (vfsApi.readBytes "/data.lock").run st1 = (.ok (ByteArray.mk #[1, 2, 3]), st1) := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, StateT.run]
    unfold vfsReadBytesPure
    simp only [show isValidRawPath "/data.lock" = true from by decide, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show st1.cwd = "/" from rfl, show st1.nodes = st.nodes from rfl, hResTrue]
  have hRel := vfsReleaseLockPure_fresh st st1 "/data.lock" "/data.lock" .exclusive (Or.inl rfl)
  dsimp only [st1] at hAcq hReadSt1 hRel
  have hResOk : ((vfsApi.withFileLock "/data.lock" .exclusive true (vfsApi.readBytes "/data.lock")).run st).1.isOk = true := by
    rw [vfsWithFileLock_action_step, hAcq]
    dsimp only
    rw [hReadSt1]
    dsimp only
    rw [hRel]
    rfl
  have hAll := proof_fs_vfs_withFileLock_preservesExistingBytes st "/data.lock" .exclusive true (by decide) (Or.inr (by decide))
  rw [hReadSt] at hAll
  dsimp only at hAll
  refine ⟨st, "/data.lock", .exclusive, true, by decide, Or.inr (by decide), ?_⟩
  dsimp only [test_fs_vfs_withFileLock_preservesExistingBytes]
  rw [hReadSt]
  exact ⟨hResOk, hAll hResOk⟩

/-- Proof of `test_fs_vfs_withFileLock_invalidPathRejected` on `vfsApi`. -/
theorem proof_fs_vfs_withFileLock_invalidPathRejected :
    AllPass (test_fs_vfs_withFileLock_invalidPathRejected vfsApi) := by
  intro s₀ path markerPath mode createIfMissing hBadPath hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, Internal.withFileLockImplM, vfsOps, StateT.run, bind, StateT.bind,
    pure, StateT.pure, assert] at hMarkerNone ⊢
  have hInvalid : isValidLockPath path = false := by
    unfold isValidLockPath
    rcases hBadPath with hEmpty | ⟨hGt, hSlash⟩
    · simp [hEmpty]
    · cases hc : path.toList with
      | nil => simp
      | cons c rest =>
        have hGt' : (c :: rest).length > 1 := by simpa [hc] using hGt
        have hSlash' : (c :: rest).getLast? = some '/' := by simpa [hc] using hSlash
        have hPos : 0 < rest.length := by simp at hGt'; omega
        simp [hPos, hSlash']
  have hAcq : vfsAcquireLockPure s₀ path mode createIfMissing false =
      (.error { kind := .invalidInput, path := some path, message := "invalid lock path" }, s₀) := by
    unfold vfsAcquireLockPure
    rw [hInvalid]
    rfl
  rw [hAcq]
  exact ⟨⟨⟨_, rfl, rfl⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_withFileLock_invalidPathRejected`. -/
theorem reach_fs_vfs_withFileLock_invalidPathRejected :
    CanReach (test_fs_vfs_withFileLock_invalidPathRejected vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "", "/marker", .exclusive, true, Or.inl rfl, hMarker,
    proof_fs_vfs_withFileLock_invalidPathRejected st "" "/marker" .exclusive true (Or.inl rfl) hMarker⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_releasesOnOk` on `vfsApi`. -/
theorem proof_fs_vfs_tryWithFileLock_releasesOnOk :
    AllPass (test_fs_vfs_tryWithFileLock_releasesOnOk vfsApi) := by
  intro s₀ path mode createIfMissing val hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  have hBoth :
      ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.ok val))).run s₀).1 = .ok (some val) ∧
      ((vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run
        ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.ok val))).run s₀).2).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
        ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
        canon path mode (Or.inl rfl)
      simp only [hRel, true_and]
      rw [vfsTryWithFileLock_pure_step]
      let s₁ : VfsState := { s₀ with nextLockId := freshLockId s₀ }
      have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
          (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
            { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
        unfold vfsAcquireLockPure
        rw [hValid]
        dsimp only
        rw [show s₁.nodes = s₀.nodes from rfl, show s₁.cwd = s₀.cwd from rfl, hRes]
        dsimp only
        simp [s₁, hConfEx]
      rw [hAcqS1]
      have hRelS1 := vfsReleaseLockPure_fresh s₁
        { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
        canon path .exclusive (Or.inl rfl)
      simp [hRelS1]
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with
          tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath parCanon lastSeg :: s₀.keys
          locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
          nextLockId := freshLockId s₀ }
        (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
      simp only [hRel, true_and]
      exact (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
  dsimp only [assert]
  exact ⟨hBoth, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_releasesOnOk`. -/
theorem reach_fs_vfs_tryWithFileLock_releasesOnOk :
    CanReach (test_fs_vfs_tryWithFileLock_releasesOnOk vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/try.lock")) false 1024 =
      .error { kind := .notFound, path := some "/try.lock", message := "no such file or directory: /try.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/try.lock" = "/try.lock" from by decide,
        show vfsSplitSegs "/try.lock" = ["try.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "try.lock" = "/try.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/try.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/try.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/try.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/try.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "try.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "try.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "try.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      unfold vfsAcquireLockPure
      rw [show isValidLockPath "/try.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/try.lock" = "/try.lock" from by decide,
          show vfsSplitSegs "/try.lock" = ["try.lock"] from by decide,
          show Internal.splitLastAux ["try.lock"] [] = some ([], "try.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "try.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "try.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "try.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "try.lock") "/try.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/try.lock", .shared, true, 9, hProbe,
    proof_fs_vfs_tryWithFileLock_releasesOnOk st "/try.lock" .shared true 9 hProbe⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_missingNotSwallowed` on `vfsApi`. -/
theorem proof_fs_vfs_tryWithFileLock_missingNotSwallowed :
    AllPass (test_fs_vfs_tryWithFileLock_missingNotSwallowed vfsApi) := by
  intro s₀ path markerPath mode hNeEmpty hNoSlash hLstat hMarkerNone
  dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run, assert] at hLstat hMarkerNone ⊢
  rcases hLstat with ⟨e, hStat, hNf⟩
  have hValid := isValidLockPath_of_not_empty_no_trailing_slash path hNeEmpty hNoSlash
  cases hRes : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | ok p => simp [hRes] at hStat
  | error e' =>
    simp only [hRes, Except.error.injEq] at hStat
    subst hStat
    dsimp only [Internal.tryWithFileLockImplM, StateT.bind, bind, StateT.pure, pure, Id.instMonad]
    have hAcq : vfsAcquireLockPure s₀ path mode false true = (.error e', s₀) := by
      unfold vfsAcquireLockPure
      rw [hValid]
      dsimp only
      rw [hRes]
      dsimp only
      simp [hNf]
    rw [hAcq]
    have hNotWb : (e'.kind == .wouldBlock) = false := by rw [hNf]; decide
    simp only [hNotWb, Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨⟨_, rfl, hNf⟩, hMarkerNone, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_missingNotSwallowed`. -/
theorem reach_fs_vfs_tryWithFileLock_missingNotSwallowed :
    CanReach (test_fs_vfs_tryWithFileLock_missingNotSwallowed vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hStat : ((vfsApi.lstat "/missing.lock").run st).1 =
      .error { kind := .notFound, path := some "/missing.lock", message := "no such file or directory: /missing.lock" } := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/missing.lock" = "/missing.lock" from by decide,
        show vfsSplitSegs "/missing.lock" = ["missing.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "missing.lock" = "/missing.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/missing.lock" = none from rfl]; rfl
  have hMarker : ((vfsApi.lstat "/marker").run st).1.isOk = false := by
    dsimp only [vfsApi, Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/marker" = "/marker" from by decide,
        show vfsSplitSegs "/marker" = ["marker"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "marker" = "/marker" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/marker" = none from rfl]; rfl
  exact ⟨st, "/missing.lock", "/marker", .exclusive, by decide, Or.inr (by decide),
    ⟨_, hStat, rfl⟩, hMarker,
    proof_fs_vfs_tryWithFileLock_missingNotSwallowed st "/missing.lock" "/marker" .exclusive (by decide) (Or.inr (by decide))
      ⟨_, hStat, rfl⟩ hMarker⟩

/-- Proof of `test_fs_vfs_tryWithFileLock_releasesOnActionError` on `vfsApi`. -/
theorem proof_fs_vfs_tryWithFileLock_releasesOnActionError :
    AllPass (test_fs_vfs_tryWithFileLock_releasesOnActionError vfsApi) := by
  intro s₀ path mode createIfMissing err hProbe
  have ⟨hValid, hCases⟩ := vfsAcquireLock_after_exclusive_probe s₀ path mode createIfMissing hProbe
  have hBoth :
      ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.error err : Except FsError Unit))).run s₀).1 =
        .error err ∧
      ((vfsApi.tryWithFileLock path .exclusive false (pure (Except.ok ()))).run
        ((vfsApi.tryWithFileLock path mode createIfMissing (pure (Except.error err : Except FsError Unit))).run s₀).2).1 =
        .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    rcases hCases with ⟨canon, bs, m, hRes, hConfEx, hAcq⟩ |
        ⟨parSegs, lastSeg, parCanon, parMode, rfl, hSplit, hPar, _, hX, hNone, hConfEx, hAcq⟩
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with locks := (freshLockId s₀, canon, mode) :: s₀.locks, nextLockId := freshLockId s₀ }
        canon path mode (Or.inl rfl)
      simp only [hRel, true_and]
      rw [vfsTryWithFileLock_pure_step]
      let s₁ : VfsState := { s₀ with nextLockId := freshLockId s₀ }
      have hAcqS1 : vfsAcquireLockPure s₁ path .exclusive false true =
          (.ok { handleId := freshLockId s₁, path := path, mode := .exclusive },
            { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }) := by
        unfold vfsAcquireLockPure
        rw [hValid]
        dsimp only
        rw [show s₁.nodes = s₀.nodes from rfl, show s₁.cwd = s₀.cwd from rfl, hRes]
        dsimp only
        simp [s₁, hConfEx]
      rw [hAcqS1]
      have hRelS1 := vfsReleaseLockPure_fresh s₁
        { s₁ with locks := (freshLockId s₁, canon, .exclusive) :: s₁.locks, nextLockId := freshLockId s₁ }
        canon path .exclusive (Or.inl rfl)
      simp [hRelS1]
    · rw [hAcq true]
      have hRel := vfsReleaseLockPure_fresh s₀
        { s₀ with
          tree := vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath parCanon lastSeg)) (some (.file ByteArray.empty 0o644))
          keys := vfsChildPath parCanon lastSeg :: s₀.keys
          locks := (freshLockId s₀, vfsChildPath parCanon lastSeg, mode) :: s₀.locks
          nextLockId := freshLockId s₀ }
        (vfsChildPath parCanon lastSeg) path mode (Or.inr ⟨_, _, rfl⟩)
      simp only [hRel, true_and]
      exact (vfsProbe_after_release_created s₀ path parCanon lastSeg parSegs parMode hValid hSplit hPar hX hNone hConfEx).2
  dsimp only [assert]
  exact ⟨hBoth, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_tryWithFileLock_releasesOnActionError`. -/
theorem reach_fs_vfs_tryWithFileLock_releasesOnActionError :
    CanReach (test_fs_vfs_tryWithFileLock_releasesOnActionError vfsApi) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  let err : FsError := { kind := .permissionDenied, message := "boom" }
  have hRes : vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd "/tryerr.lock")) false 1024 =
      .error { kind := .notFound, path := some "/tryerr.lock", message := "no such file or directory: /tryerr.lock" } := by
    rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/tryerr.lock" = "/tryerr.lock" from by decide,
        show vfsSplitSegs "/tryerr.lock" = ["tryerr.lock"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "tryerr.lock" = "/tryerr.lock" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/tryerr.lock" = none from rfl]; rfl
  have hPar : vfsResolveSegs st.nodes "/" [] true 512 = .ok ("/", .dir 0o755) := by
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hProbe : ((vfsApi.tryWithFileLock "/tryerr.lock" .exclusive true (pure (.ok ()))).run st).1 = .ok (some ()) := by
    rw [vfsTryWithFileLock_pure_step]
    have hAcq : vfsAcquireLockPure st "/tryerr.lock" .exclusive true true =
        (.ok { handleId := freshLockId st, path := "/tryerr.lock", mode := .exclusive },
          { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "tryerr.lock")) (some (.file ByteArray.empty 0o644))
            keys := vfsChildPath "/" "tryerr.lock" :: st.keys
            locks := (freshLockId st, vfsChildPath "/" "tryerr.lock", .exclusive) :: st.locks
            nextLockId := freshLockId st }) := by
      unfold vfsAcquireLockPure
      rw [show isValidLockPath "/tryerr.lock" = true from by decide]
      dsimp only
      rw [hRes]
      dsimp only
      rw [show st.cwd = "/" from rfl, show vfsAbsNorm "/" "/tryerr.lock" = "/tryerr.lock" from by decide,
          show vfsSplitSegs "/tryerr.lock" = ["tryerr.lock"] from by decide,
          show Internal.splitLastAux ["tryerr.lock"] [] = some ([], "tryerr.lock") from by decide]
      dsimp only
      rw [hPar]
      simp [st, hasLockConflict]
      decide
    rw [hAcq]
    have hRel := vfsReleaseLockPure_fresh st
      { st with
        tree := vfsTreeSet st.tree (vfsSplitSegs (vfsChildPath "/" "tryerr.lock")) (some (.file ByteArray.empty 0o644))
        keys := vfsChildPath "/" "tryerr.lock" :: st.keys
        locks := (freshLockId st, vfsChildPath "/" "tryerr.lock", .exclusive) :: st.locks
        nextLockId := freshLockId st }
      (vfsChildPath "/" "tryerr.lock") "/tryerr.lock" .exclusive (Or.inr ⟨_, _, rfl⟩)
    simp [hRel]
  exact ⟨st, "/tryerr.lock", .shared, true, err, hProbe,
    proof_fs_vfs_tryWithFileLock_releasesOnActionError st "/tryerr.lock" .shared true err hProbe⟩

private theorem vfsTreeGet_set_leaf :
    ∀ (segs : List String) (lastSeg : String) (t : VfsTree) (v : Option VfsTree) (q : List String),
      (∃ dm dch, vfsTreeGet t segs = some (.dir dm dch)) →
      (∀ dm dch, vfsTreeGet t (segs ++ [lastSeg]) ≠ some (.dir dm dch)) →
      (∀ dm dch, v ≠ some (.dir dm dch)) →
      (vfsTreeGet (vfsTreeSet t (segs ++ [lastSeg]) v) q).map vfsTreeTopNode =
        if q == (segs ++ [lastSeg]) then v.map vfsTreeTopNode else (vfsTreeGet t q).map vfsTreeTopNode := by
  intro segs
  induction segs with
  | nil =>
    intro lastSeg t v q hDir hNotDir hNewNotDir
    rcases hDir with ⟨dm, dch, hGet⟩
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir mode ch =>
      simp only [List.nil_append, vfsTreeSet]
      have hChNotDir : ∀ dm' dch', ch lastSeg ≠ some (.dir dm' dch') := by
        intro dm' dch' hEq
        exact hNotDir dm' dch' (by simp [vfsTreeGet, hEq])
      cases q with
      | nil => rfl
      | cons qh qt =>
        by_cases hEq : qh = lastSeg
        · subst hEq
          cases qt with
          | nil => cases v <;> simp [vfsTreeGet]
          | cons rh rt =>
            have hListNe : ((qh :: rh :: rt) == [qh]) = false := by simp
            simp only [vfsTreeGet, beq_self_eq_true, ↓reduceIte, hListNe, Bool.false_eq_true]
            cases v with
            | none =>
              cases hCh : ch qh with
              | none => rfl
              | some sub =>
                cases sub with
                | file _ _ => rfl
                | symlink _ _ => rfl
                | dir dm' dch' => exact absurd hCh (hChNotDir dm' dch')
            | some vsub =>
              cases vsub with
              | dir dm' dch' => exact absurd rfl (hNewNotDir dm' dch')
              | file _ _ =>
                cases hCh : ch qh with
                | none => rfl
                | some sub =>
                  cases sub with
                  | file _ _ => rfl
                  | symlink _ _ => rfl
                  | dir dm' dch' => exact absurd hCh (hChNotDir dm' dch')
              | symlink _ _ =>
                cases hCh : ch qh with
                | none => rfl
                | some sub =>
                  cases sub with
                  | file _ _ => rfl
                  | symlink _ _ => rfl
                  | dir dm' dch' => exact absurd hCh (hChNotDir dm' dch')
        · have hNe : (qh == lastSeg) = false := beq_false_of_ne hEq
          have hListNe : ((qh :: qt) == [lastSeg]) = false := by simp [hEq]
          simp [vfsTreeGet, hNe, hListNe]
  | cons seg rest ih =>
    intro lastSeg t v q hDir hNotDir hNewNotDir
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
        have hSubNotDir : ∀ dm dch, vfsTreeGet sub (rest ++ [lastSeg]) ≠ some (.dir dm dch) := by
          intro dm' dch' hEq
          exact hNotDir dm' dch' (by simpa [vfsTreeGet, hCh] using hEq)
        have hNonEmpty : rest ++ [lastSeg] ≠ [] := by simp
        cases hRest : rest ++ [lastSeg] with
        | nil => exact absurd hRest hNonEmpty
        | cons rhd rtl =>
          have hSetEq : vfsTreeSet (.dir mode ch) ((seg :: rest) ++ [lastSeg]) v =
              .dir mode (fun s => if s == seg then some (vfsTreeSet sub (rest ++ [lastSeg]) v) else ch s) := by
            simp only [List.cons_append, vfsTreeSet, hRest, hCh]
          rw [hSetEq]
          cases q with
          | nil => rfl
          | cons qh qt =>
            by_cases hEq : qh = seg
            · subst hEq
              have hIh := ih lastSeg sub v qt hSubDir hSubNotDir hNewNotDir
              have hLhs :
                  (vfsTreeGet (.dir mode fun s =>
                    if s == qh then some (vfsTreeSet sub (rest ++ [lastSeg]) v) else ch s) (qh :: qt)).map vfsTreeTopNode =
                  (vfsTreeGet (vfsTreeSet sub (rest ++ [lastSeg]) v) qt).map vfsTreeTopNode := by
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

private theorem vfsTreeNodes_set_leaf (t : VfsTree) (parCanon lastSeg : String) (v : Option VfsTree)
    (hParCanon : isCanonPath parCanon = true)
    (hLastValid : Internal.validFileName lastSeg = true)
    (hParDir : ∃ dm, vfsTreeNodes t parCanon = some (.dir dm))
    (hNotDir : ∀ dm, vfsTreeNodes t (vfsChildPath parCanon lastSeg) ≠ some (.dir dm))
    (hNewNotDir : ∀ dm dch, v ≠ some (.dir dm dch)) :
    vfsTreeNodes (vfsTreeSet t (vfsSplitSegs (vfsChildPath parCanon lastSeg)) v) =
      fun k => if k == vfsChildPath parCanon lastSeg then v.map vfsTreeTopNode else vfsTreeNodes t k := by
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
  have hChildTreeNotDir : ∀ dm dch, vfsTreeGet t (vfsSplitSegs parCanon ++ [lastSeg]) ≠ some (.dir dm dch) := by
    intro dm dch hGet
    apply hNotDir dm
    simp only [vfsTreeNodes, hChildCanon, ↓reduceIte, hChildSp, hGet, Option.map_some, vfsTreeTopNode]
  funext k
  by_cases hKCanon : isCanonPath k = true
  · simp only [vfsTreeNodes, hKCanon, ↓reduceIte, hChildSp]
    rw [vfsTreeGet_set_leaf (vfsSplitSegs parCanon) lastSeg t v (vfsSplitSegs k) hParTreeDir hChildTreeNotDir hNewNotDir]
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

private theorem validFileName_of_singleParts (s : String)
    (hNe : (!s.toList.isEmpty) = true) (hNoSlash : decide ('/' ∈ s.toList) = false)
    (hNeDot : (s != ".") = true) (hNeDotDot : (s != "..") = true) :
    Internal.validFileName s = true := by
  have hNoSlBool : (!decide ('/' ∈ s.toList)) = true := by simp [hNoSlash]
  have hD1 : (s.toList != ['.']) = true := by
    cases hb : (s.toList == ['.']) with
    | false => simp [bne, hb]
    | true =>
      have hStr : s = "." := String.toList_inj.mp (beq_iff_eq.mp hb)
      subst hStr; simp at hNeDot
  have hD2 : (s.toList != ['.', '.']) = true := by
    cases hb : (s.toList == ['.', '.']) with
    | false => simp [bne, hb]
    | true =>
      have hStr : s = ".." := String.toList_inj.mp (beq_iff_eq.mp hb)
      subst hStr; simp at hNeDotDot
  simp [Internal.validFileName, hNe, hNoSlBool, hD1, hD2]

private theorem list_getLast?_not_mem {α : Type} (c : α) (xs : List α) (h : c ∉ xs) :
    xs.getLast? ≠ some c := by
  intro hEq
  cases xs with
  | nil => simp at hEq
  | cons hd tl =>
    have hMem : c ∈ hd :: tl := by
      have : some c = (hd :: tl).getLast? := hEq.symm
      rw [List.getLast?_eq_some_getLast (by simp)] at this
      cases this
      exact List.getLast_mem (by simp)
    exact h hMem

private theorem isValidRawPath_slash_child (c : String)
    (hNe : (!c.toList.isEmpty) = true) (hNoSlash : decide ('/' ∈ c.toList) = false)
    (hNoNul : decide (Char.ofNat 0 ∈ c.toList) = false) :
    isValidRawPath ("/" ++ c) = true := by
  have hEmpF : c.toList.isEmpty = false := by simpa using hNe
  have hNoSl : '/' ∉ c.toList := of_decide_eq_false hNoSlash
  have hNoNul' : Char.ofNat 0 ∉ c.toList := of_decide_eq_false hNoNul
  have hFull : ("/" ++ c).toList = '/' :: c.toList := by simp [String.toList_append]
  have hLast : ('/' :: c.toList).getLast? ≠ some '/' := by
    cases hCs : c.toList with
    | nil => simp [hCs] at hEmpF
    | cons x xs =>
      rw [List.getLast?_cons_cons]
      have hSub : '/' ∉ x :: xs := by rw [← hCs]; exact hNoSl
      exact list_getLast?_not_mem '/' (x :: xs) hSub
  have hNoNulFull : Char.ofNat 0 ∉ '/' :: c.toList := by
    intro hm
    cases hm with
    | tail _ hm' => exact hNoNul' hm'
  unfold isValidRawPath
  rw [hFull]
  simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨decide_eq_false hNoNulFull, ?_⟩
  cases hB : (('/' :: c.toList).length > 1 && ('/' :: c.toList).getLast? == some '/') with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hB
    exact absurd hB.2 hLast

private theorem isValidRawPath_of_single (c : String)
    (hNe : (!c.toList.isEmpty) = true) (hNoSlash : decide ('/' ∈ c.toList) = false)
    (hNoNul : decide (Char.ofNat 0 ∈ c.toList) = false) :
    isValidRawPath c = true := by
  have hNoSl : '/' ∉ c.toList := of_decide_eq_false hNoSlash
  have hNoNul' : Char.ofNat 0 ∉ c.toList := of_decide_eq_false hNoNul
  have hNe' : c.toList.isEmpty = false := by simpa using hNe
  unfold isValidRawPath
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨hNe', decide_eq_false hNoNul'⟩, ?_⟩
  have hLast : c.toList.getLast? ≠ some '/' := list_getLast?_not_mem '/' c.toList hNoSl
  cases hB : (c.toList.length > 1 && c.toList.getLast? == some '/') with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hB
    exact absurd hB.2 hLast

private theorem vfsAbsNorm_slash_child (cwd c : String) (hc : Internal.validFileName c = true) :
    vfsAbsNorm cwd ("/" ++ c) = "/" ++ c ∧
    vfsSplitSegs ("/" ++ c) = [c] ∧
    vfsChildPath "/" c = "/" ++ c := by
  have hChildEq : vfsChildPath "/" c = "/" ++ c := by simp [vfsChildPath]
  have ⟨hCanon, hSp⟩ := vfsChildPath_valid "/" c (by decide) hc
  rw [hChildEq] at hCanon hSp
  have hIsAbs : Internal.isAbsolute ("/" ++ c) = true := by
    simp [Internal.isAbsolute, Internal.isAbsChars, String.toList_append]
  have hNorm : Internal.normPath ("/" ++ c) = "/" ++ c := by
    unfold isCanonPath at hCanon
    simp only [Bool.and_eq_true, beq_iff_eq] at hCanon
    exact hCanon.2
  refine ⟨?_, hSp, hChildEq⟩
  rw [vfsAbsNorm_abs cwd ("/" ++ c) hIsAbs, hNorm]

private theorem vfsResolveSegs_true_never_symlink (nodes : String → Option VfsNode) :
    ∀ fuel cur segs canon tgt m,
      vfsResolveSegs nodes cur segs true fuel = .ok (canon, .symlink tgt m) → False := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs canon tgt m h
    cases segs with
    | nil =>
      simp only [vfsResolveSegs] at h
      cases hNd : nodes cur with
      | none => simp [hNd] at h
      | some nd =>
        cases nd with
        | file _ _ => simp [hNd] at h
        | dir _ => simp [hNd] at h
        | symlink _ _ => simp only [hNd, ↓reduceIte] at h; exact ih _ _ _ _ _ h
    | cons seg rest =>
      simp only [vfsResolveSegs] at h
      cases hNd : nodes cur with
      | none => simp [hNd] at h
      | some nd =>
        cases nd with
        | file _ _ => simp [hNd] at h
        | symlink _ _ => simp only [hNd] at h; exact ih _ _ _ _ _ h
        | dir dm =>
          simp only [hNd] at h
          by_cases hp : ((dm / 64) % 2 == 0) = true
          · simp [hp] at h
          · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h; exact ih _ _ _ _ _ h

private theorem vfsResolveSegs_false_error_notFound_implies_true (nodes : String → Option VfsNode) :
    ∀ fuel cur segs e,
      vfsResolveSegs nodes cur segs false fuel = .error e →
      e.kind = .notFound →
      vfsResolveSegs nodes cur segs true fuel = .error e := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h hk; simp [vfsResolveSegs] at h; subst h; simp at hk
  | succ fuel ih =>
    intro cur segs e h hk
    cases segs with
    | nil =>
      simp only [vfsResolveSegs] at h ⊢
      cases hNd : nodes cur with
      | none => simp only [hNd] at h ⊢; exact h
      | some nd =>
        cases nd with
        | file _ _ => simp [hNd] at h
        | dir _ => simp [hNd] at h
        | symlink _ _ => simp [hNd] at h
    | cons seg rest =>
      simp only [vfsResolveSegs] at h ⊢
      cases hNd : nodes cur with
      | none => simp only [hNd] at h ⊢; exact h
      | some nd =>
        cases nd with
        | file _ _ => simp [hNd] at h; subst h; simp at hk
        | symlink _ _ => simp only [hNd] at h; exact ih _ _ _ h hk
        | dir dm =>
          simp only [hNd] at h ⊢
          by_cases hp : ((dm / 64) % 2 == 0) = true
          · simp [hp] at h ⊢; exact h
          · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact ih _ _ _ h hk

private theorem vfsResolveSegs_prefix_false_notFound (nodes : String → Option VfsNode) :
    ∀ fuel cur xs ys fl2 e,
      vfsResolveSegs nodes cur xs false fuel = .error e →
      e.kind = .notFound →
      ∃ e2, vfsResolveSegs nodes cur (xs ++ ys) fl2 fuel = .error e2 ∧ e2.kind = .notFound := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h hk; simp [vfsResolveSegs] at h; subst h; simp at hk
  | succ fuel ih =>
    intro cur xs ys fl2 e h hk
    cases xs with
    | nil =>
      simp only [vfsResolveSegs] at h
      cases hNd : nodes cur with
      | none =>
        simp only [hNd, Except.error.injEq] at h
        subst h
        cases ys with
        | nil =>
          refine ⟨{ kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }, ?_, rfl⟩
          simp [vfsResolveSegs, hNd]
        | cons _ _ =>
          refine ⟨{ kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }, ?_, rfl⟩
          simp [vfsResolveSegs, hNd]
      | some nd =>
        cases nd with
        | file _ _ => simp [hNd] at h
        | dir _ => simp [hNd] at h
        | symlink _ _ => simp [hNd] at h
    | cons x xs' =>
      simp only [vfsResolveSegs, List.cons_append] at h ⊢
      cases hNd : nodes cur with
      | none =>
        simp only [hNd, Except.error.injEq] at h
        subst h
        exact ⟨_, rfl, rfl⟩
      | some nd =>
        cases nd with
        | file _ _ => simp [hNd] at h; subst h; simp at hk
        | symlink _ _ =>
          simp only [hNd] at h ⊢
          rw [← List.cons_append, ← List.append_assoc]
          exact ih "/" _ ys fl2 e h hk
        | dir dm =>
          simp only [hNd] at h ⊢
          by_cases hp : ((dm / 64) % 2 == 0) = true
          · simp [hp] at h; subst h; simp at hk
          · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact ih _ _ ys fl2 e h hk

private theorem vfsStat_root_dir_node (s₀ : VfsState) (stRoot : FileStat)
    (hStat : vfsStatPure s₀ false "/" = .ok stRoot) (hKind : stRoot.kind = .dir) :
    s₀.nodes "/" = some (.dir stRoot.mode) := by
  unfold vfsStatPure at hStat
  rw [show vfsAbsNorm s₀.cwd "/" = "/" from by rw [vfsAbsNorm_abs _ _ (by decide)]; decide,
      show vfsSplitSegs "/" = [] from by decide] at hStat
  unfold vfsResolveSegs at hStat
  cases hNd : s₀.nodes "/" with
  | none => simp [hNd] at hStat
  | some nd =>
    cases nd with
    | file _ _ => simp [hNd, vfsToStat] at hStat; subst hStat; simp at hKind
    | symlink _ _ => simp [hNd, vfsToStat] at hStat; subst hStat; simp at hKind
    | dir m => simp [hNd, vfsToStat] at hStat; subst hStat; rfl

/-- Proof of `test_fsraw_createFileNew_createsMissingWithExactBytes` on `vfsOps`. -/
theorem proof_fsraw_createFileNew_createsMissingWithExactBytes :
    AllPass (Raw.test_fsraw_createFileNew_createsMissingWithExactBytes vfsOps) := by
  intro s₀ child bytes hValid ⟨stRoot, hRootStat, hRootKind, hRootW, hRootX⟩ ⟨eNf, hStatNf, hKindNf⟩
  change ((!child.toList.isEmpty && !decide ('/' ∈ child.toList) &&
    !decide (Char.ofNat 0 ∈ child.toList) && (child != ".") && (child != "..")) = true) at hValid
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hValid
  rcases hValid with ⟨⟨⟨⟨hNe, hNoSl⟩, hNoNul⟩, hNeD⟩, hNeDD⟩
  have hNe' : (!child.toList.isEmpty) = true := by simp [hNe]
  have hChildValid := validFileName_of_singleParts child hNe' hNoSl hNeD hNeDD
  have hRawValid := isValidRawPath_slash_child child hNe' hNoSl hNoNul
  have ⟨hAbs, hSplit, hChild⟩ := vfsAbsNorm_slash_child s₀.cwd child hChildValid
  have hRootNode := vfsStat_root_dir_node s₀ stRoot hRootStat hRootKind
  have hW : ((stRoot.mode / 128) % 2 == 0) = false := by
    cases hb : (stRoot.mode / 128) % 2 == 0 <;> simp_all
  have hX : ((stRoot.mode / 64) % 2 == 0) = false := by
    cases hb : (stRoot.mode / 64) % 2 == 0 <;> simp_all
  have hChildNone : s₀.nodes ("/" ++ child) = none := by
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hStatNf
    rw [hAbs, hSplit] at hStatNf
    unfold vfsResolveSegs at hStatNf
    rw [hRootNode] at hStatNf
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hChild] at hStatNf
    unfold vfsResolveSegs at hStatNf
    cases hNd : s₀.nodes ("/" ++ child) with
    | none => rfl
    | some nd => cases nd <;> simp [hNd] at hStatNf
  have hResNf : vfsResolveSegs s₀.nodes "/" [child] false 1024 =
      .error { kind := .notFound, path := some ("/" ++ child), message := s!"no such file or directory: {"/" ++ child}" } := by
    unfold vfsResolveSegs
    rw [hRootNode]
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hChild]
    unfold vfsResolveSegs
    rw [hChildNone]
  have hParOk : vfsResolveSegs s₀.nodes "/" [] true 1024 = .ok ("/", .dir stRoot.mode) := by
    unfold vfsResolveSegs
    rw [hRootNode]
  let s₁ : VfsState :=
    { s₀ with
      tree := vfsTreeSet s₀.tree (vfsSplitSegs ("/" ++ child)) (some (.file bytes 0o644))
      keys := ("/" ++ child) :: s₀.keys }
  have hCreate : (vfsOps.createFileNew ("/" ++ child) bytes s₀) = (.ok (), s₁) := by
    dsimp only [vfsOps]
    unfold vfsCreateFileNewPure
    rw [hRawValid]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hAbs, hSplit, hResNf]
    rw [show Internal.splitLastAux [child] [] = some ([], child) from rfl]
    dsimp only
    rw [hParOk]
    simp only [hW, hX, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hChild]
    rfl
  have hNodes₁ : s₁.nodes = fun k => if k == ("/" ++ child) then some (.file bytes 0o644) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath "/" child)) (some (.file bytes 0o644))) = _
    rw [hChild]
    refine vfsTreeNodes_set_leaf s₀.tree "/" child (some (.file bytes 0o644)) (by decide) hChildValid
      ⟨stRoot.mode, hRootNode⟩
      (fun dm h => by rw [hChild] at h; change s₀.nodes ("/" ++ child) = some (.dir dm) at h; rw [hChildNone] at h; cases h)
      (fun _ _ h => by cases h)
  have hNeRoot : ("/" == "/" ++ child) = false := by
    apply beq_false_of_ne
    intro hEq
    have := congrArg (fun s => (vfsSplitSegs s).length) hEq
    rw [hSplit, show vfsSplitSegs "/" = [] from by decide] at this
    simp at this
  have hResolve₁False : vfsResolveSegs s₁.nodes "/" [child] false 1024 = .ok ("/" ++ child, .file bytes 0o644) := by
    unfold vfsResolveSegs
    rw [hNodes₁]
    simp only [hNeRoot, Bool.false_eq_true, ↓reduceIte, hRootNode, hX, hChild]
    unfold vfsResolveSegs
    simp
  have hResolve₁True : vfsResolveSegs s₁.nodes "/" [child] true 1024 = .ok ("/" ++ child, .file bytes 0o644) := by
    unfold vfsResolveSegs
    rw [hNodes₁]
    simp only [hNeRoot, Bool.false_eq_true, ↓reduceIte, hRootNode, hX, hChild]
    unfold vfsResolveSegs
    simp
  have hCwd₁ : s₁.cwd = s₀.cwd := rfl
  have ⟨hAbs₁, hSplit₁, _⟩ := vfsAbsNorm_slash_child s₁.cwd child hChildValid
  dsimp only [StateT.run, assert]
  rw [hCreate]
  refine ⟨rfl, ⟨vfsToStat (.file bytes 0o644), ?_, rfl, rfl⟩, ?_, trivial⟩
  · dsimp only [vfsOps, vfsStatPure]
    rw [hAbs₁, hSplit₁, hResolve₁False]
  · dsimp only [vfsOps, vfsReadBytesPure]
    simp only [hRawValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hAbs₁, hSplit₁, hResolve₁True]

/-- Non-vacuity `CanReach` witness for `test_fsraw_createFileNew_createsMissingWithExactBytes`. -/
theorem reach_fsraw_createFileNew_createsMissingWithExactBytes :
    CanReach (Raw.test_fsraw_createFileNew_createsMissingWithExactBytes vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 := by
    refine ⟨vfsToStat (.dir 0o755), ?_, rfl, by decide, by decide⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/" = "/" from by decide, show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hMissing : ∃ e, ((vfsOps.stat false "/a").run st).1 = .error e ∧ e.kind = .notFound := by
    refine ⟨{ kind := .notFound, path := some "/a", message := "no such file or directory: /a" }, ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/a" = "/a" from by decide, show vfsSplitSegs "/a" = ["a"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "a" = "/a" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/a" = none from rfl]; rfl
  exact ⟨st, "a", ByteArray.empty, by decide, hRoot, hMissing,
    proof_fsraw_createFileNew_createsMissingWithExactBytes st "a" ByteArray.empty (by decide) hRoot hMissing⟩

/-- Proof of `test_fsraw_createFileNew_existingRejected` on `vfsOps`. -/
theorem proof_fsraw_createFileNew_existingRejected :
    AllPass (Raw.test_fsraw_createFileNew_existingRejected vfsOps) := by
  intro s₀ path bytes hValid hExists
  change isValidRawPath path = true at hValid
  dsimp only [vfsOps, vfsStatPure, StateT.run] at hExists
  dsimp only [vfsOps, StateT.run, assert]
  unfold vfsCreateFileNewPure
  simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 with
  | error e => simp [hR, Except.isOk, Except.toBool] at hExists
  | ok res => exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_createFileNew_existingRejected`. -/
theorem reach_fsraw_createFileNew_existingRejected :
    CanReach (Raw.test_fsraw_createFileNew_existingRejected vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := ["/"], cwd := "/", nonce := 0 }
  have hEx : ((vfsOps.stat false "/").run st).1.isOk = true := by
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/" = "/" from by decide, show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; rfl
  exact ⟨st, "/", ByteArray.empty, by decide, hEx,
    proof_fsraw_createFileNew_existingRejected st "/" ByteArray.empty (by decide) hEx⟩

/-- Proof of `test_fsraw_createFileNew_invalidPathRejected` on `vfsOps`. -/
theorem proof_fsraw_createFileNew_invalidPathRejected :
    AllPass (Raw.test_fsraw_createFileNew_invalidPathRejected vfsOps) := by
  intro s₀ path bytes hInvalid
  change isValidRawPath path = false at hInvalid
  dsimp only [vfsOps, StateT.run, assert]
  unfold vfsCreateFileNewPure
  simp only [hInvalid, Bool.not_false, ↓reduceIte]
  exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_createFileNew_invalidPathRejected`. -/
theorem reach_fsraw_createFileNew_invalidPathRejected :
    CanReach (Raw.test_fsraw_createFileNew_invalidPathRejected vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  exact ⟨st, "", ByteArray.empty, by decide,
    proof_fsraw_createFileNew_invalidPathRejected st "" ByteArray.empty (by decide)⟩

/-- Proof of `test_fsraw_createFileNew_missingParentRejected` on `vfsOps`. -/
theorem proof_fsraw_createFileNew_missingParentRejected :
    AllPass (Raw.test_fsraw_createFileNew_missingParentRejected vfsOps) := by
  intro s₀ d f bytes ⟨hDv, hFv⟩ ⟨eNf, hStatNf, hKindNf⟩
  change ((!d.toList.isEmpty && !decide ('/' ∈ d.toList) &&
    !decide (Char.ofNat 0 ∈ d.toList) && (d != ".") && (d != "..")) = true) at hDv
  change ((!f.toList.isEmpty && !decide ('/' ∈ f.toList) &&
    !decide (Char.ofNat 0 ∈ f.toList) && (f != ".") && (f != "..")) = true) at hFv
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hDv hFv
  rcases hDv with ⟨⟨⟨⟨hDne, hDns⟩, hDnn⟩, hDnd1⟩, hDnd2⟩
  rcases hFv with ⟨⟨⟨⟨hFne, hFns⟩, hFnn⟩, hFnd1⟩, hFnd2⟩
  have hDne' : (!d.toList.isEmpty) = true := by simp [hDne]
  have hFne' : (!f.toList.isEmpty) = true := by simp [hFne]
  have hDv' := validFileName_of_singleParts d hDne' hDns hDnd1 hDnd2
  have hFv' := validFileName_of_singleParts f hFne' hFns hFnd1 hFnd2
  have hParRaw := isValidRawPath_slash_child d hDne' hDns hDnn
  have hDChild := vfsAbsNorm_slash_child s₀.cwd d hDv'
  have hFCanon := vfsChildPath_valid ("/" ++ d) f (vfsChildPath_valid "/" d (by decide) hDv').1 hFv'
  have hPathIsAbs : Internal.isAbsolute ("/" ++ d ++ "/" ++ f) = true := by
    simp [Internal.isAbsolute, Internal.isAbsChars, String.toList_append]
  have hChildEq : vfsChildPath ("/" ++ d) f = "/" ++ d ++ "/" ++ f := by
    have hNe : ("/" ++ d == "/") = false := by
      apply beq_false_of_ne
      intro hEq
      have := congrArg (fun s => (vfsSplitSegs s).length) hEq
      rw [hDChild.2.1, show vfsSplitSegs "/" = [] from by decide] at this
      simp at this
    simp [vfsChildPath, hNe, String.append_assoc]
  rw [hChildEq] at hFCanon
  have hPathNorm : Internal.normPath ("/" ++ d ++ "/" ++ f) = "/" ++ d ++ "/" ++ f := by
    have hc := hFCanon.1
    unfold isCanonPath at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.2
  have hPathAbsNorm : vfsAbsNorm s₀.cwd ("/" ++ d ++ "/" ++ f) = "/" ++ d ++ "/" ++ f := by
    rw [vfsAbsNorm_abs s₀.cwd _ hPathIsAbs, hPathNorm]
  have hPathSplit : vfsSplitSegs ("/" ++ d ++ "/" ++ f) = [d, f] := by
    rw [hFCanon.2, hDChild.2.1]; rfl
  have hPathRawValid : isValidRawPath ("/" ++ d ++ "/" ++ f) = true := by
    have hCs : ("/" ++ d ++ "/" ++ f).toList = '/' :: (d.toList ++ '/' :: f.toList) := by
      simp [String.toList_append, List.append_assoc]
    have hNoNul : Char.ofNat 0 ∉ ('/' :: (d.toList ++ '/' :: f.toList)) := by
      have hd0 : Char.ofNat 0 ∉ d.toList := of_decide_eq_false hDnn
      have hf0 : Char.ofNat 0 ∉ f.toList := of_decide_eq_false hFnn
      intro hm
      cases hm with
      | tail _ hm' =>
        rcases List.mem_append.mp hm' with h1 | h2
        · exact hd0 h1
        · cases h2 with
          | tail _ h3 => exact hf0 h3
    have hLast : ('/' :: (d.toList ++ '/' :: f.toList)).getLast? ≠ some '/' := by
      have hfEmpty : f.toList ≠ [] := by simpa using hFne
      have hfNoSl : '/' ∉ f.toList := of_decide_eq_false hFns
      have hTailNe : (d.toList ++ '/' :: f.toList).getLast? ≠ some '/' := by
        have hApp : ∀ (xs : List Char) (y : Char) (ys : List Char),
            ys ≠ [] → (xs ++ y :: ys).getLast? = ys.getLast? := by
          intro xs y ys hYne
          induction xs with
          | nil =>
            simp only [List.nil_append]
            cases ys with
            | nil => exact absurd rfl hYne
            | cons _ _ => simp [List.getLast?_cons_cons]
          | cons a as ih =>
            simp only [List.cons_append]
            have hTailNe : as ++ y :: ys ≠ [] := by simp
            cases hTail : as ++ y :: ys with
            | nil => exact absurd hTail hTailNe
            | cons b bs => rw [List.getLast?_cons_cons, ← hTail, ih]
        rw [hApp d.toList '/' f.toList hfEmpty]
        exact list_getLast?_not_mem '/' f.toList hfNoSl
      intro hEq
      have hSub : (d.toList ++ '/' :: f.toList).getLast? = some '/' := by
        cases hDs : d.toList with
        | nil => simp [hDs] at hEq; exact hEq
        | cons a as => simpa [hDs, List.getLast?_cons_cons] using hEq
      exact hTailNe hSub
    unfold isValidRawPath
    rw [hCs]
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨decide_eq_false hNoNul, ?_⟩
    cases hB : (('/' :: (d.toList ++ '/' :: f.toList)).length > 1 &&
        ('/' :: (d.toList ++ '/' :: f.toList)).getLast? == some '/') with
    | false => rfl
    | true =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hB
      exact absurd hB.2 hLast
  dsimp only [vfsOps, vfsStatPure, StateT.run] at hStatNf
  rw [hDChild.1, hDChild.2.1] at hStatNf
  have hResD : vfsResolveSegs s₀.nodes "/" [d] false 1024 = .error eNf := by
    cases hD : vfsResolveSegs s₀.nodes "/" [d] false 1024 with
    | ok _ => simp [hD] at hStatNf
    | error e' => simp [hD] at hStatNf; exact congrArg Except.error hStatNf
  have ⟨e2, hRes2, hKind2⟩ :=
    vfsResolveSegs_prefix_false_notFound s₀.nodes 1024 "/" [d] [f] false eNf hResD hKindNf
  have hParNf := vfsResolveSegs_false_error_notFound_implies_true s₀.nodes 1024 "/" [d] eNf hResD hKindNf
  dsimp only [vfsOps, StateT.run, assert]
  unfold vfsCreateFileNewPure
  rw [hPathRawValid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPathAbsNorm, hPathSplit]
  rw [show [d] ++ [f] = [d, f] from rfl] at hRes2
  rw [hRes2]
  have hNeNf : (e2.kind != .notFound) = false := by rw [hKind2]; decide
  simp only [hNeNf, Bool.false_eq_true, ↓reduceIte]
  rw [show Internal.splitLastAux [d, f] [] = some ([d], f) from rfl]
  dsimp only
  rw [hParNf]
  exact ⟨⟨⟨eNf, rfl, hKindNf⟩, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_createFileNew_missingParentRejected`. -/
theorem reach_fsraw_createFileNew_missingParentRejected :
    CanReach (Raw.test_fsraw_createFileNew_missingParentRejected vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hMissing : ∃ e, ((vfsOps.stat false "/d").run st).1 = .error e ∧ e.kind = .notFound := by
    refine ⟨{ kind := .notFound, path := some "/d", message := "no such file or directory: /d" }, ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/d" = "/d" from by decide, show vfsSplitSegs "/d" = ["d"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "d" = "/d" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/d" = none from rfl]; rfl
  exact ⟨st, "d", "f", ByteArray.empty, ⟨by decide, by decide⟩, hMissing,
    proof_fsraw_createFileNew_missingParentRejected st "d" "f" ByteArray.empty ⟨by decide, by decide⟩ hMissing⟩

/-- Proof of `test_fsraw_readBytes_followsSymlinkToRegularFile` on `vfsOps`. -/
theorem proof_fsraw_readBytes_followsSymlinkToRegularFile :
    AllPass (Raw.test_fsraw_readBytes_followsSymlinkToRegularFile vfsOps) := by
  intro s₀ path hValid _ ⟨stTgt, hStatTgt, hTgtFile⟩
  change isValidRawPath path = true at hValid
  dsimp only [vfsOps, vfsStatPure, StateT.run] at hStatTgt
  dsimp only [vfsOps, vfsReadBytesPure, StateT.run, assert]
  simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) true 1024 with
  | error _ => simp [hR] at hStatTgt
  | ok pair =>
    rcases pair with ⟨canon, nd⟩
    simp only [hR, Except.ok.injEq] at hStatTgt
    cases nd with
    | dir _ => subst hStatTgt; simp [vfsToStat] at hTgtFile
    | symlink tgt m => exact (vfsResolveSegs_true_never_symlink s₀.nodes 1024 "/" _ canon tgt m hR).elim
    | file bs m =>
      refine ⟨⟨⟨bs, rfl, stTgt, ?_, ?_⟩, trivial⟩, trivial⟩
      · dsimp only [vfsOps, vfsStatPure]
        rw [hR]; simp [hStatTgt]
      · subst hStatTgt; rfl

/-- Non-vacuity `CanReach` witness for `test_fsraw_readBytes_followsSymlinkToRegularFile`. -/
theorem reach_fsraw_readBytes_followsSymlinkToRegularFile :
    CanReach (Raw.test_fsraw_readBytes_followsSymlinkToRegularFile vfsOps) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun s =>
        if s == "f" then some (.file (ByteArray.mk #[1, 2]) 0o644)
        else if s == "l" then some (.symlink "/f" 0o777)
        else none)
      keys := ["/f", "/l"]
      cwd := "/"
      nonce := 0 }
  have hL : ∃ lst, ((vfsOps.stat false "/l").run st).1 = .ok lst ∧ lst.kind = .symlink := by
    refine ⟨vfsToStat (.symlink "/f" 0o777), ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/l" = "/l" from by decide, show vfsSplitSegs "/l" = ["l"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "l" = "/l" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/l" = some (.symlink "/f" 0o777) from rfl]; rfl
  have hF : ∃ ft, ((vfsOps.stat true "/l").run st).1 = .ok ft ∧ ft.kind = .file := by
    refine ⟨vfsToStat (.file (ByteArray.mk #[1, 2]) 0o644), ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/l" = "/l" from by decide, show vfsSplitSegs "/l" = ["l"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "l" = "/l" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/l" = some (.symlink "/f" 0o777) from rfl]; dsimp only
    rw [show Internal.isAbsolute "/f" = true from by decide]
    simp only [↓reduceIte]
    rw [show Internal.normPath "/f" = "/f" from by decide, show vfsSplitSegs "/f" = ["f"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "f" = "/f" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/f" = some (.file (ByteArray.mk #[1, 2]) 0o644) from rfl]
  exact ⟨st, "/l", by decide, hL, hF, proof_fsraw_readBytes_followsSymlinkToRegularFile st "/l" (by decide) hL hF⟩

/-- Proof of `test_fsraw_readBytes_roundTripsExactBytesThroughSymlink` on `vfsOps`. -/
theorem proof_fsraw_readBytes_roundTripsExactBytesThroughSymlink :
    AllPass (Raw.test_fsraw_readBytes_roundTripsExactBytesThroughSymlink vfsOps) := by
  intro s₀ tgtName symName bytes ⟨hTv, hSv, hNeName⟩
    ⟨stRoot, hRootStat, hRootKind, hRootW, hRootX⟩
    ⟨e1, hTgtNf, hTgtKind⟩ ⟨e2, hSymNf, hSymKind⟩
  change ((!tgtName.toList.isEmpty && !decide ('/' ∈ tgtName.toList) &&
    !decide (Char.ofNat 0 ∈ tgtName.toList) && (tgtName != ".") && (tgtName != "..")) = true) at hTv
  change ((!symName.toList.isEmpty && !decide ('/' ∈ symName.toList) &&
    !decide (Char.ofNat 0 ∈ symName.toList) && (symName != ".") && (symName != "..")) = true) at hSv
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hTv hSv
  rcases hTv with ⟨⟨⟨⟨hTne, hTns⟩, hTnn⟩, hTnd1⟩, hTnd2⟩
  rcases hSv with ⟨⟨⟨⟨hSne, hSns⟩, hSnn⟩, hSnd1⟩, hSnd2⟩
  have hTne' : (!tgtName.toList.isEmpty) = true := by simp [hTne]
  have hSne' : (!symName.toList.isEmpty) = true := by simp [hSne]
  have hTValid := validFileName_of_singleParts tgtName hTne' hTns hTnd1 hTnd2
  have hSValid := validFileName_of_singleParts symName hSne' hSns hSnd1 hSnd2
  have hTRaw := isValidRawPath_slash_child tgtName hTne' hTns hTnn
  have ⟨hTAbs, hTSplit, hTChild⟩ := vfsAbsNorm_slash_child s₀.cwd tgtName hTValid
  have hRootNode := vfsStat_root_dir_node s₀ stRoot hRootStat hRootKind
  have hW : ((stRoot.mode / 128) % 2 == 0) = false := by
    cases hb : (stRoot.mode / 128) % 2 == 0 <;> simp_all
  have hX : ((stRoot.mode / 64) % 2 == 0) = false := by
    cases hb : (stRoot.mode / 64) % 2 == 0 <;> simp_all
  have hTgtNone : s₀.nodes ("/" ++ tgtName) = none := by
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hTgtNf
    rw [hTAbs, hTSplit] at hTgtNf
    unfold vfsResolveSegs at hTgtNf
    rw [hRootNode] at hTgtNf
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hTChild] at hTgtNf
    unfold vfsResolveSegs at hTgtNf
    cases hNd : s₀.nodes ("/" ++ tgtName) with
    | none => rfl
    | some nd => cases nd <;> simp [hNd] at hTgtNf
  have hResTNf : vfsResolveSegs s₀.nodes "/" [tgtName] false 1024 =
      .error { kind := .notFound, path := some ("/" ++ tgtName), message := s!"no such file or directory: {"/" ++ tgtName}" } := by
    unfold vfsResolveSegs; rw [hRootNode]
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hTChild]
    unfold vfsResolveSegs; rw [hTgtNone]
  have hParOk : vfsResolveSegs s₀.nodes "/" [] true 1024 = .ok ("/", .dir stRoot.mode) := by
    unfold vfsResolveSegs; rw [hRootNode]
  let s₁ : VfsState :=
    { s₀ with
      tree := vfsTreeSet s₀.tree (vfsSplitSegs ("/" ++ tgtName)) (some (.file bytes 0o644))
      keys := ("/" ++ tgtName) :: s₀.keys }
  have hCreate : (vfsOps.createFileNew ("/" ++ tgtName) bytes s₀) = (.ok (), s₁) := by
    dsimp only [vfsOps]
    unfold vfsCreateFileNewPure
    rw [hTRaw]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hTAbs, hTSplit, hResTNf]
    rw [show Internal.splitLastAux [tgtName] [] = some ([], tgtName) from rfl]
    dsimp only; rw [hParOk]
    simp only [hW, hX, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hTChild]; rfl
  have hNodes₁ : s₁.nodes = fun k => if k == ("/" ++ tgtName) then some (.file bytes 0o644) else s₀.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₀.tree (vfsSplitSegs (vfsChildPath "/" tgtName)) (some (.file bytes 0o644))) = _
    rw [hTChild]
    refine vfsTreeNodes_set_leaf s₀.tree "/" tgtName (some (.file bytes 0o644)) (by decide) hTValid
      ⟨stRoot.mode, hRootNode⟩
      (fun dm h => by rw [hTChild] at h; change s₀.nodes ("/" ++ tgtName) = some (.dir dm) at h; rw [hTgtNone] at h; cases h)
      (fun _ _ h => by cases h)
  have ⟨hSAbs, hSSplit, hSChild⟩ := vfsAbsNorm_slash_child s₁.cwd symName hSValid
  have hSAbs₀ : vfsAbsNorm s₀.cwd ("/" ++ symName) = "/" ++ symName := by
    change vfsAbsNorm s₁.cwd ("/" ++ symName) = _; exact hSAbs
  have hSymNone : s₀.nodes ("/" ++ symName) = none := by
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hSymNf
    rw [hSAbs₀, hSSplit] at hSymNf
    unfold vfsResolveSegs at hSymNf
    rw [hRootNode] at hSymNf
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hSChild] at hSymNf
    unfold vfsResolveSegs at hSymNf
    cases hNd : s₀.nodes ("/" ++ symName) with
    | none => rfl
    | some nd => cases nd <;> simp [hNd] at hSymNf
  have hNeRootT : ("/" == "/" ++ tgtName) = false := by
    apply beq_false_of_ne
    intro hEq
    have := congrArg (fun s => (vfsSplitSegs s).length) hEq
    rw [hTSplit, show vfsSplitSegs "/" = [] from by decide] at this; simp at this
  have hNeSymTgt : ("/" ++ symName == "/" ++ tgtName) = false := by
    apply beq_false_of_ne
    intro hEq
    apply hNeName
    have hL := congrArg String.toList hEq
    rw [String.toList_append, String.toList_append] at hL
    simp only [show "/".toList = ['/'] from rfl, List.singleton_append, List.cons.injEq, true_and] at hL
    exact (String.toList_inj.mp hL).symm
  have hSymNone₁ : s₁.nodes ("/" ++ symName) = none := by
    rw [hNodes₁]; dsimp only; rw [hNeSymTgt]; exact hSymNone
  have hRootNode₁ : s₁.nodes "/" = some (.dir stRoot.mode) := by
    rw [hNodes₁]; dsimp only; rw [hNeRootT]; exact hRootNode
  have hResSNf₁ : vfsResolveSegs s₁.nodes "/" [symName] false 1024 =
      .error { kind := .notFound, path := some ("/" ++ symName), message := s!"no such file or directory: {"/" ++ symName}" } := by
    unfold vfsResolveSegs; rw [hRootNode₁]
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hSChild]
    unfold vfsResolveSegs; rw [hSymNone₁]
  let s₂ : VfsState :=
    { s₁ with
      tree := vfsTreeSet s₁.tree (vfsSplitSegs ("/" ++ symName)) (some (.symlink ("/" ++ tgtName) 0o777))
      keys := ("/" ++ symName) :: s₁.keys }
  have hSymLink : (vfsOps.symlink ("/" ++ tgtName) ("/" ++ symName) s₁) = (.ok (), s₂) := by
    dsimp only [vfsOps]
    rw [hSAbs, hSSplit, hResSNf₁]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, ← hSSplit]
    rfl
  have hNodes₂ : s₂.nodes = fun k =>
      if k == ("/" ++ symName) then some (.symlink ("/" ++ tgtName) 0o777) else s₁.nodes k := by
    change vfsTreeNodes (vfsTreeSet s₁.tree (vfsSplitSegs (vfsChildPath "/" symName))
        (some (.symlink ("/" ++ tgtName) 0o777))) = _
    rw [hSChild]
    refine vfsTreeNodes_set_leaf s₁.tree "/" symName (some (.symlink ("/" ++ tgtName) 0o777)) (by decide) hSValid
      ⟨stRoot.mode, hRootNode₁⟩
      (fun dm h => by rw [hSChild] at h; change s₁.nodes ("/" ++ symName) = some (.dir dm) at h; rw [hSymNone₁] at h; cases h)
      (fun _ _ h => by cases h)
  have hNeRootS : ("/" == "/" ++ symName) = false := by
    apply beq_false_of_ne
    intro hEq
    have := congrArg (fun s => (vfsSplitSegs s).length) hEq
    rw [hSSplit, show vfsSplitSegs "/" = [] from by decide] at this; simp at this
  have hNeTgtSym : ("/" ++ tgtName == "/" ++ symName) = false := by
    apply beq_false_of_ne
    intro hEq
    apply hNeName
    have hL := congrArg String.toList hEq
    rw [String.toList_append, String.toList_append] at hL
    simp only [show "/".toList = ['/'] from rfl, List.singleton_append, List.cons.injEq, true_and] at hL
    exact String.toList_inj.mp hL
  have hRootNode₂ : s₂.nodes "/" = some (.dir stRoot.mode) := by
    rw [hNodes₂]; dsimp only; rw [hNeRootS]; exact hRootNode₁
  have hSymNode₂ : s₂.nodes ("/" ++ symName) = some (.symlink ("/" ++ tgtName) 0o777) := by
    rw [hNodes₂]; dsimp only; rw [beq_self_eq_true]; rfl
  have hTgtNode₂ : s₂.nodes ("/" ++ tgtName) = some (.file bytes 0o644) := by
    rw [hNodes₂]; dsimp only; rw [hNeTgtSym, hNodes₁]; dsimp only; rw [beq_self_eq_true]; rfl
  have hParSym : Internal.parent ("/" ++ symName) = some "/" := by
    have hV := vfsChildPath_valid "/" symName (by decide) hSValid
    have hEqC : "/" ++ symName = vfsChildPath "/" symName := by simp [vfsChildPath]
    have hParts : (vfsSplitSegs ("/" ++ symName)).map String.toList = [symName.toList] := by
      rw [hSSplit]; rfl
    have hCanon := hV.1; rw [← hEqC] at hCanon
    obtain ⟨hDstEq, hDstParts⟩ := isCanonPath_normPath_parts ("/" ++ symName) hCanon
    rw [hParts] at hDstEq hDstParts
    have hSplitAll :
        Internal.splitCharList '/' ('/' :: Internal.joinSlashChars [symName.toList]) =
        [] :: [symName.toList] := by
      unfold Internal.splitCharList
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [splitCharList_joinSlashChars _ (by simp) (fun s hs => (hDstParts s hs).2.2.1)]
    have hClean : Internal.cleanCharSegments ("/" ++ symName) = (true, [symName.toList]) := by
      rw [congrArg Internal.cleanCharSegments hDstEq]
      unfold Internal.cleanCharSegments Internal.isAbsChars
      simp only [String.toList_ofList, hSplitAll, List.filter_cons, List.isEmpty_nil,
        Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, true_and]
      have hP := hDstParts symName.toList (by simp)
      simp [hP.1, hP.2.1]
    have hSpPar : Internal.splitParentName ("/" ++ symName) = some (some "/", symName) := by
      unfold Internal.splitParentName
      rw [hClean]
      simp [Internal.splitLastAux]
    simp [Internal.parent, hSpPar]
  have hSRaw := isValidRawPath_slash_child symName hSne' hSns hSnn
  have ⟨hSAbs₂, hSSplit₂, _⟩ := vfsAbsNorm_slash_child s₂.cwd symName hSValid
  have hTgtIsAbs : Internal.isAbsolute ("/" ++ tgtName) = true := by
    simp [Internal.isAbsolute, Internal.isAbsChars, String.toList_append]
  have hTgtNorm : Internal.normPath ("/" ++ tgtName) = "/" ++ tgtName := by
    have hc := (vfsChildPath_valid "/" tgtName (by decide) hTValid).1
    rw [hTChild] at hc
    unfold isCanonPath at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.2
  have hReadSym : vfsReadBytesPure s₂ ("/" ++ symName) = .ok bytes := by
    unfold vfsReadBytesPure
    rw [hSRaw]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hSAbs₂, hSSplit₂]
    unfold vfsResolveSegs; rw [hRootNode₂]
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hSChild]
    unfold vfsResolveSegs; rw [hSymNode₂]
    simp only [↓reduceIte, hTgtIsAbs, hTgtNorm, hTSplit]
    unfold vfsResolveSegs; rw [hRootNode₂]
    simp only [hX, Bool.false_eq_true, ↓reduceIte, hTChild]
    unfold vfsResolveSegs; rw [hTgtNode₂]
  dsimp only [StateT.run]
  rw [hCreate]
  intro hR1
  dsimp only
  rw [hSymLink]
  intro hR2
  dsimp only [vfsOps, assert]
  rw [hReadSym]
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_readBytes_roundTripsExactBytesThroughSymlink`. -/
theorem reach_fsraw_readBytes_roundTripsExactBytesThroughSymlink :
    CanReach (Raw.test_fsraw_readBytes_roundTripsExactBytesThroughSymlink vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 := by
    refine ⟨vfsToStat (.dir 0o755), ?_, rfl, by decide, by decide⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/" = "/" from by decide, show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  have hMissingT : ∃ e1, ((vfsOps.stat false "/t").run st).1 = .error e1 ∧ e1.kind = .notFound := by
    refine ⟨{ kind := .notFound, path := some "/t", message := "no such file or directory: /t" }, ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/t" = "/t" from by decide, show vfsSplitSegs "/t" = ["t"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "t" = "/t" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/t" = none from rfl]; rfl
  have hMissingS : ∃ e2, ((vfsOps.stat false "/s").run st).1 = .error e2 ∧ e2.kind = .notFound := by
    refine ⟨{ kind := .notFound, path := some "/s", message := "no such file or directory: /s" }, ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm st.cwd "/s" = "/s" from by decide, show vfsSplitSegs "/s" = ["s"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "s" = "/s" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/s" = none from rfl]; rfl
  have hCreate : ((vfsOps.createFileNew "/t" (ByteArray.mk #[7, 8])).run st).1 = .ok () := by
    dsimp only [vfsOps, StateT.run]; unfold vfsCreateFileNewPure
    simp only [show isValidRawPath "/t" = true from by decide, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show vfsAbsNorm st.cwd "/t" = "/t" from by decide, show vfsSplitSegs "/t" = ["t"] from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "t" = "/t" from by decide]
    unfold vfsResolveSegs; rw [show st.nodes "/t" = none from rfl]
    rw [show Internal.splitLastAux ["t"] [] = some ([], "t") from by decide]
    rfl
  let st₁ := (vfsOps.createFileNew "/t" (ByteArray.mk #[7, 8]) st).2
  have hSym : ((vfsOps.symlink "/t" "/s").run st₁).1 = .ok () := by
    have hNodesS : st₁.nodes "/s" = none := by decide
    have hNodesRoot : st₁.nodes "/" = some (.dir 0o755) := by decide
    dsimp only [vfsOps, StateT.run]
    rw [show vfsAbsNorm st₁.cwd "/s" = "/s" from by decide, show vfsSplitSegs "/s" = ["s"] from by decide]
    unfold vfsResolveSegs; rw [hNodesRoot]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show vfsChildPath "/" "s" = "/s" from by decide]
    unfold vfsResolveSegs; rw [hNodesS]; rfl
  exact ⟨st, "t", "s", ByteArray.mk #[7, 8], ⟨by decide, by decide, by decide⟩, hRoot, hMissingT, hMissingS,
    hCreate, hSym,
    proof_fsraw_readBytes_roundTripsExactBytesThroughSymlink st "t" "s" (ByteArray.mk #[7, 8])
      ⟨by decide, by decide, by decide⟩ hRoot hMissingT hMissingS hCreate hSym⟩

/-- Proof of `test_fsraw_readBytes_dirAndMissingRejected` on `vfsOps`. -/
theorem proof_fsraw_readBytes_dirAndMissingRejected :
    AllPass (Raw.test_fsraw_readBytes_dirAndMissingRejected vfsOps) := by
  intro s₀ path hValid
  change isValidRawPath path = true at hValid
  dsimp only [vfsOps, vfsStatPure, vfsReadBytesPure, StateT.run, assert]
  cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) true 1024 with
  | error err =>
    simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨⟨err, rfl, rfl⟩, trivial⟩, trivial⟩
  | ok pair =>
    rcases pair with ⟨canon, nd⟩
    cases nd with
    | dir m =>
      simp only [vfsToStat, hValid, Bool.not_true, Bool.false_eq_true]
      exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
    | file bs m =>
      dsimp only [vfsToStat]
      rw [show (Raw.EntryKind.file == Raw.EntryKind.dir) = false from rfl]
      simp
      trivial
    | symlink tgt m =>
      exact (vfsResolveSegs_true_never_symlink s₀.nodes 1024 "/" _ canon tgt m hR).elim

/-- Non-vacuity `CanReach` witness for `test_fsraw_readBytes_dirAndMissingRejected`. -/
theorem reach_fsraw_readBytes_dirAndMissingRejected :
    CanReach (Raw.test_fsraw_readBytes_dirAndMissingRejected vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  exact ⟨st, "/", by decide, proof_fsraw_readBytes_dirAndMissingRejected st "/" (by decide)⟩

/-- Proof of `test_fsraw_readBytes_invalidPathRejected` on `vfsOps`. -/
theorem proof_fsraw_readBytes_invalidPathRejected :
    AllPass (Raw.test_fsraw_readBytes_invalidPathRejected vfsOps) := by
  intro s₀ path hInvalid
  change isValidRawPath path = false at hInvalid
  dsimp only [vfsOps, vfsReadBytesPure, StateT.run, assert]
  simp only [hInvalid, Bool.not_false, ↓reduceIte]
  exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_readBytes_invalidPathRejected`. -/
theorem reach_fsraw_readBytes_invalidPathRejected :
    CanReach (Raw.test_fsraw_readBytes_invalidPathRejected vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  exact ⟨st, "", by decide, proof_fsraw_readBytes_invalidPathRejected st "" (by decide)⟩

private theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.toUTF8_eq_toByteArray, String.fromUTF8?, s.isValidUTF8]

private theorem isSingleValidName_validFileName (s : String) :
    (!s.toList.isEmpty && !('/' ∈ s.toList) && !(Char.ofNat 0 ∈ s.toList) && s != "." && s != "..") = true →
    Internal.validFileName s = true := by
  intro h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨h1, h2⟩, _⟩, h4⟩, h5⟩
  have h4L : (s.toList != ['.']) = true := bne_iff_ne.mpr fun he =>
    h4 (by rw [← String.ofList_toList (s := s), he])
  have h5L : (s.toList != ['.', '.']) = true := bne_iff_ne.mpr fun he =>
    h5 (by rw [← String.ofList_toList (s := s), he])
  simp only [Internal.validFileName, Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, h4L⟩, h5L⟩

private theorem toDigitsCore_mem_digit_or_acc :
    ∀ fuel base n acc c,
      base = 10 →
      c ∈ Nat.toDigitsCore base fuel n acc →
      c ∈ acc ∨ ∃ d < 10, c = Nat.digitChar d := by
  intro fuel
  induction fuel with
  | zero => intro _ _ acc c _ h; exact Or.inl h
  | succ f ih =>
    intro base n acc c hb h
    subst hb
    rw [Nat.toDigitsCore] at h
    by_cases hZero : n / 10 = 0
    · simp only [hZero, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hc
      · exact Or.inr ⟨n % 10, Nat.mod_lt _ (by decide), rfl⟩
      · exact Or.inl hc
    · simp only [hZero, ↓reduceIte] at h
      rcases ih 10 (n / 10) (Nat.digitChar (n % 10) :: acc) c rfl h with hc | hc
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | ha
        · exact Or.inr ⟨n % 10, Nat.mod_lt _ (by decide), rfl⟩
        · exact Or.inl ha
      · exact Or.inr hc

private theorem slash_not_mem_toString_nat (n : Nat) : '/' ∉ (toString n).toList := by
  intro h
  have hDig : '/' ∈ Nat.toDigits 10 n := by simpa [toString, Nat.repr] using h
  unfold Nat.toDigits at hDig
  rcases toDigitsCore_mem_digit_or_acc (n + 1) 10 n [] '/' rfl hDig with hc | ⟨d, hd, hEq⟩
  · simp at hc
  · rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
    all_goals first | (simp [Nat.digitChar] at hEq; done) | omega

private theorem validFileName_tmpSibling (child : String) (nonce : Nat)
    (hChild : Internal.validFileName child = true) :
    Internal.validFileName ("." ++ child ++ ".tmp." ++ toString nonce) = true := by
  have hChildL := validFileName_charList child hChild
  have hNeNil : ("." ++ child ++ ".tmp." ++ toString nonce).toList ≠ [] := by
    simp [String.toList_append]
  have hNotEmp : (!("." ++ child ++ ".tmp." ++ toString nonce).toList.isEmpty) = true := by
    cases hL : ("." ++ child ++ ".tmp." ++ toString nonce).toList with
    | nil => exact absurd hL hNeNil
    | cons _ _ => rfl
  have hNoSlash : '/' ∉ ("." ++ child ++ ".tmp." ++ toString nonce).toList := by
    simp only [String.toList_append, List.mem_append,
      show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide]
    rintro (((h | h) | h) | h)
    · simp at h
    · exact hChildL.2.2.1 h
    · simp at h
    · exact slash_not_mem_toString_nat nonce h
  have hLenGt2 : 2 < ("." ++ child ++ ".tmp." ++ toString nonce).toList.length := by
    simp only [String.toList_append, List.length_append,
      show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide,
      List.length_cons, List.length_nil]
    omega
  have hNeDot : (("." ++ child ++ ".tmp." ++ toString nonce).toList != ['.']) = true := by
    apply bne_iff_ne.mpr
    intro heq
    have hLen := congrArg List.length heq
    rw [List.length_cons, List.length_nil] at hLen
    omega
  have hNeDotDot : (("." ++ child ++ ".tmp." ++ toString nonce).toList != ['.', '.']) = true := by
    apply bne_iff_ne.mpr
    intro heq
    have hLen := congrArg List.length heq
    rw [List.length_cons, List.length_cons, List.length_nil] at hLen
    omega
  simp only [Internal.validFileName, Bool.and_eq_true]
  exact ⟨⟨⟨hNotEmp, by simpa using hNoSlash⟩, hNeDot⟩, hNeDotDot⟩

private theorem tmpSibling_ne_child (child : String) (nonce : Nat) :
    "." ++ child ++ ".tmp." ++ toString nonce ≠ child := by
  intro heq
  have := congrArg (fun s => s.toList.length) heq
  simp only [String.toList_append, List.length_append,
    show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide,
    List.length_cons, List.length_nil] at this
  omega

private theorem splitCharList_single_of_no_sep (cs : List Char) (hNe : cs ≠ []) (hNo : '/' ∉ cs) :
    Internal.splitCharList '/' cs = [cs] := by
  induction cs with
  | nil => exact absurd rfl hNe
  | cons c rest ih =>
    have hNeC : (c == '/') = false := beq_false_of_ne (fun h => hNo (by simp [h]))
    have hNoRest : '/' ∉ rest := fun h => hNo (by simp [h])
    cases rest with
    | nil => simp [Internal.splitCharList, hNeC]
    | cons r rs =>
      have ih' := ih (by simp) hNoRest
      unfold Internal.splitCharList
      simp only [hNeC, Bool.false_eq_true, ↓reduceIte]
      rw [ih']

private theorem parent_name_slash_child (child : String) (h : Internal.validFileName child = true) :
    Internal.parent ("/" ++ child) = some "/" ∧ Internal.name ("/" ++ child) = some child := by
  have hL := validFileName_charList child h
  have hNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
  have hSp : Internal.splitCharList '/' ('/' :: child.toList) = [[], child.toList] := by
    unfold Internal.splitCharList
    simp only [beq_self_eq_true, ↓reduceIte, splitCharList_single_of_no_sep child.toList hNeNil hL.2.2.1]
  have hClean : Internal.cleanCharSegments ("/" ++ child) = (true, [child.toList]) := by
    unfold Internal.cleanCharSegments Internal.isAbsChars
    dsimp only
    rw [String.toList_append, show "/".toList = ['/'] by decide, List.singleton_append, hSp]
    simp [hL.1, hL.2.1]
  have hSpn : Internal.splitParentName ("/" ++ child) = some (some "/", child) := by
    unfold Internal.splitParentName
    rw [hClean]
    simp [Internal.splitLastAux, String.ofList_toList]
  simp [Internal.parent, Internal.name, hSpn]

private theorem parent_name_bare_child (child : String) (h : Internal.validFileName child = true) :
    Internal.parent child = none ∧ Internal.name child = some child := by
  have hL := validFileName_charList child h
  have hNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
  have hHeadNe : Internal.isAbsChars child.toList = false := by
    cases hC : child.toList with
    | nil => exact absurd hC hNeNil
    | cons c cs =>
      have hSl : c ≠ '/' := fun he => hL.2.2.1 (by rw [hC, he]; simp)
      simp [Internal.isAbsChars, hSl]
  have hSp : Internal.splitCharList '/' child.toList = [child.toList] :=
    splitCharList_single_of_no_sep child.toList hNeNil hL.2.2.1
  have hClean : Internal.cleanCharSegments child = (false, [child.toList]) := by
    unfold Internal.cleanCharSegments
    dsimp only
    rw [hHeadNe, hSp]
    simp [hL.1, hL.2.1]
  have hSpn : Internal.splitParentName child = some (none, child) := by
    unfold Internal.splitParentName
    rw [hClean]
    simp [Internal.splitLastAux, String.ofList_toList]
  simp [Internal.parent, Internal.name, hSpn]

private theorem parent_name_dir_child (dir child : String)
    (h1 : Internal.validFileName dir = true) (h2 : Internal.validFileName child = true) :
    Internal.parent ("/" ++ dir ++ "/" ++ child) = some ("/" ++ dir) ∧
    Internal.name ("/" ++ dir ++ "/" ++ child) = some child := by
  have h1C := vfsChildPath_valid "/" dir (by decide) h1
  have hSlash : vfsChildPath "/" dir = "/" ++ dir := by simp [vfsChildPath]
  rw [hSlash] at h1C
  exact parent_name_vfsChildPath ("/" ++ dir) child h1C.1 (by
    intro heq
    have := congrArg vfsSplitSegs heq
    rw [h1C.2, show vfsSplitSegs "/" = [] by decide] at this
    simp at this) h2

private theorem join_slash_of_not_abs (s : String) (hNotAbs : Internal.isAbsolute s = false) :
    Internal.join "/" s = "/" ++ s := by
  simp [Internal.join, hNotAbs, show ("/" : String).isEmpty = false by decide]

private theorem join_dot_of_not_abs (s : String) (hNotAbs : Internal.isAbsolute s = false) :
    Internal.join "." s = "./" ++ s := by
  simp [Internal.join, hNotAbs, show ("." : String).isEmpty = false by decide]

private theorem isAbsolute_false_dotPrefix (s : String) :
    Internal.isAbsolute ("." ++ s) = false := by
  simp [Internal.isAbsolute, Internal.isAbsChars, String.toList_append, show ".".toList = ['.'] by decide]

private theorem normPath_slash_child (child : String) (h : Internal.validFileName child = true) :
    Internal.normPath ("/" ++ child) = "/" ++ child := by
  have ⟨hCanon, _⟩ := vfsChildPath_valid "/" child (by decide) h
  have hChild : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  rw [hChild] at hCanon
  exact beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hCanon).2

private theorem vfsAbsNorm_root_dot_child (s : String) (h : Internal.validFileName s = true) :
    vfsAbsNorm "/" ("./" ++ s) = "/" ++ s := by
  have hNotAbs : Internal.isAbsolute ("./" ++ s) = false := by
    simp [Internal.isAbsolute, Internal.isAbsChars, String.toList_append, show "./".toList = ['.', '/'] by decide]
  have hJoin : Internal.join "/" ("./" ++ s) = "/./" ++ s := by
    simp [Internal.join, hNotAbs, show ("/" : String).isEmpty = false by decide]
    rw [← String.append_assoc]
    rfl
  have hL := validFileName_charList s h
  have hNeNil : s.toList ≠ [] := by cases hC : s.toList <;> simp_all
  have hSp : Internal.splitCharList '/' ('/' :: '.' :: '/' :: s.toList) = [[], ['.'], s.toList] := by
    unfold Internal.splitCharList
    simp only [beq_self_eq_true, ↓reduceIte]
    unfold Internal.splitCharList
    simp only [show ('.' == '/') = false by decide, Bool.false_eq_true, ↓reduceIte]
    unfold Internal.splitCharList
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [splitCharList_single_of_no_sep s.toList hNeNil hL.2.2.1]
  have hNorm : Internal.normPath ("/./" ++ s) = "/" ++ s := by
    unfold Internal.normPath
    dsimp only
    rw [String.toList_append, show "/./".toList = ['/', '.', '/'] by decide]
    simp only [List.cons_append, List.nil_append, Internal.isAbsChars, ↓reduceIte, hSp]
    rw [Internal.collapseChars]
    simp only [List.isEmpty_nil, Bool.true_or, ↓reduceIte]
    rw [Internal.collapseChars]
    simp only [show (['.'].isEmpty || ['.'] == ['.']) = true from rfl, ↓reduceIte]
    rw [Internal.collapseChars]
    have hEmpF : s.toList.isEmpty = false := by cases hC : s.toList <;> simp_all
    have hNotDot : (s.toList == ['.']) = false := beq_false_of_ne (bne_iff_ne.mp hL.2.1)
    have hNotDD : (s.toList == ['.', '.']) = false := beq_false_of_ne hL.2.2.2
    rw [hEmpF, hNotDot, hNotDD]
    simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    rw [Internal.collapseChars]
    rw [List.reverse_cons, List.reverse_nil, List.nil_append, Internal.joinSlashChars]
    apply String.ext_iff.mpr
    simp [String.toList_append, show "/".toList = ['/'] by decide]
  simp [vfsAbsNorm, hNotAbs, hJoin, hNorm]

private theorem vfsAbsNorm_root_bare_child (s : String) (h : Internal.validFileName s = true) :
    vfsAbsNorm "/" s = "/" ++ s := by
  have hL := validFileName_charList s h
  have hNeNil : s.toList ≠ [] := by cases hC : s.toList <;> simp_all
  have hNotAbs : Internal.isAbsolute s = false := by
    cases hC : s.toList with
    | nil => exact absurd hC hNeNil
    | cons c cs =>
      have hc : c ≠ '/' := fun he => hL.2.2.1 (by rw [hC, he]; simp)
      simp [Internal.isAbsolute, Internal.isAbsChars, hC, hc]
  have hJoin : Internal.join "/" s = "/" ++ s := join_slash_of_not_abs s hNotAbs
  simp [vfsAbsNorm, hNotAbs, hJoin, normPath_slash_child s h]

private theorem isValidRawPath_of_singleValid (s : String)
    (h : (!s.toList.isEmpty && !('/' ∈ s.toList) && !(Char.ofNat 0 ∈ s.toList) && s != "." && s != "..") = true) :
    isValidRawPath ("/" ++ s) = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at h
  rcases h with ⟨⟨⟨⟨hEmp, hSlash⟩, hNul⟩, _⟩, _⟩
  have hNeNil : s.toList ≠ [] := by cases hC : s.toList <;> simp_all
  have hNoNul : Char.ofNat 0 ∉ ("/" ++ s).toList := by
    rw [String.toList_append, show "/".toList = ['/'] by decide]
    simp only [List.mem_append, List.mem_singleton]
    rintro (h | h)
    · cases h
    · exact hNul h
  have hLast : (("/" ++ s).toList.getLast? == some '/') = false := by
    rw [String.toList_append, show "/".toList = ['/'] by decide, list_getLast?_append ['/'] s.toList hNeNil]
    apply beq_false_of_ne
    intro heq
    have hMem : '/' ∈ s.toList := by
      have : s.toList.reverse.head? = some '/' := by simpa [List.head?_reverse] using heq
      cases hr : s.toList.reverse with
      | nil => simp [hr] at this
      | cons c cs =>
        rw [hr] at this; simp at this; subst this
        exact List.mem_reverse.mp (by rw [hr]; simp)
    exact hSlash hMem
  simp only [isValidRawPath, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  refine ⟨⟨?_, hNoNul⟩, ?_⟩
  · cases hC : ("/" ++ s).toList with
    | nil => simp [String.toList_append] at hC
    | cons _ _ => rfl
  · rw [hLast, Bool.and_false]

private theorem isValidRawPath_tmpSibling (child : String) (nonce : Nat)
    (h : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true) :
    isValidRawPath ("/." ++ child ++ ".tmp." ++ toString nonce) = true := by
  have hValid := validFileName_tmpSibling child nonce (isSingleValidName_validFileName child h)
  have hL := validFileName_charList _ hValid
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at h
  have hNulChild : Char.ofNat 0 ∉ child.toList := h.1.1.2
  have hNoNulNat : Char.ofNat 0 ∉ (toString nonce).toList := by
    intro hm
    have hDig : Char.ofNat 0 ∈ Nat.toDigits 10 nonce := by simpa [toString, Nat.repr] using hm
    unfold Nat.toDigits at hDig
    rcases toDigitsCore_mem_digit_or_acc (nonce + 1) 10 nonce [] (Char.ofNat 0) rfl hDig with hc | ⟨d, hd, hEq⟩
    · simp at hc
    · rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
      all_goals first | (simp [Nat.digitChar] at hEq; done) | omega
  have hEqStr : "/." ++ child ++ ".tmp." ++ toString nonce = "/" ++ ("." ++ child ++ ".tmp." ++ toString nonce) := by
    apply String.ext_iff.mpr
    simp [String.toList_append, List.append_assoc,
      show "/.".toList = ['/', '.'] by decide, show "/".toList = ['/'] by decide, show ".".toList = ['.'] by decide]
  rw [hEqStr]
  apply isValidRawPath_of_singleValid
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not]
  have hLenGt2 : 2 < ("." ++ child ++ ".tmp." ++ toString nonce).toList.length := by
    simp only [String.toList_append, List.length_append,
      show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide,
      List.length_cons, List.length_nil]
    omega
  refine ⟨⟨⟨⟨?_, hL.2.2.1⟩, ?_⟩, ?_⟩, ?_⟩
  · cases hC : ("." ++ child ++ ".tmp." ++ toString nonce).toList with
    | nil => simp [String.toList_append] at hC
    | cons _ _ => rfl
  · simp only [String.toList_append, List.mem_append,
      show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide]
    rintro (((hm | hm) | hm) | hm)
    · simp at hm
    · exact hNulChild hm
    · simp at hm
    · exact hNoNulNat hm
  · intro heq
    have hLen := congrArg (fun x : String => x.toList.length) heq
    rw [show ".".toList = ['.'] by decide, List.length_cons, List.length_nil] at hLen
    omega
  · intro heq
    have hLen := congrArg (fun x : String => x.toList.length) heq
    rw [show "..".toList = ['.', '.'] by decide, List.length_cons, List.length_cons, List.length_nil] at hLen
    omega

private theorem vfsResolveSegs_root_symlink_err (nodes : String → Option VfsNode)
    (tgt : String) (m : Nat) (hRoot : nodes "/" = some (.symlink tgt m)) :
    ∀ fuel segs follow, (segs ≠ [] ∨ follow = true) →
      ∃ e, vfsResolveSegs nodes "/" segs follow fuel = .error e ∧ e.kind = .ioError := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; exact ⟨_, rfl, rfl⟩
  | succ f ih =>
    intro segs follow hCond
    cases segs with
    | nil =>
      rcases hCond with h | h
      · exact absurd rfl h
      · subst h
        simpa [vfsResolveSegs, hRoot] using ih _ true (Or.inr rfl)
    | cons seg rest =>
      simpa [vfsResolveSegs, hRoot] using ih _ follow (by
        cases follow <;> simp_all)

private theorem vfsStat_root_dir_nodes (s₀ : VfsState) (stRoot : FileStat)
    (hStat : ((vfsOps.stat false "/").run s₀).1 = .ok stRoot)
    (hKind : stRoot.kind = .dir) :
    s₀.nodes "/" = some (.dir stRoot.mode) := by
  dsimp only [vfsOps, vfsStatPure, StateT.run] at hStat
  rw [vfsAbsNorm_abs _ _ (by decide), show Internal.normPath "/" = "/" by decide, show vfsSplitSegs "/" = [] by decide] at hStat
  unfold vfsResolveSegs at hStat
  cases hR : s₀.nodes "/" with
  | none => simp [hR] at hStat
  | some nd =>
    cases nd with
    | file _ _ => simp [hR] at hStat; subst hStat; simp [vfsToStat] at hKind
    | symlink _ _ => simp [hR] at hStat; subst hStat; simp [vfsToStat] at hKind
    | dir m =>
      simp only [hR, Except.ok.injEq] at hStat
      have : stRoot.mode = m := by rw [← hStat]; rfl
      rw [this]

private theorem vfsResolveSegs_true_not_dir_implies_false_not_dir (nodes : String → Option VfsNode) :
    ∀ fuel cur segs c nd,
      vfsResolveSegs nodes cur segs true fuel = .ok (c, nd) →
      (∀ dm, nd ≠ .dir dm) →
      ∃ c' nd', vfsResolveSegs nodes cur segs false fuel = .ok (c', nd') ∧ (∀ dm, nd' ≠ .dir dm) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ f ih =>
    intro cur segs c nd hOk hNotDir
    simp only [vfsResolveSegs] at hOk ⊢
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some node =>
        simp only [hNd] at hOk ⊢
        cases node with
        | file bs m => exact ⟨cur, .file bs m, rfl, fun _ h => by cases h⟩
        | symlink tgt m => exact ⟨cur, .symlink tgt m, rfl, fun _ h => by cases h⟩
        | dir m =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          exact absurd hOk.2.symm (hNotDir m)
    | cons seg rest =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some node =>
        simp only [hNd] at hOk ⊢
        cases node with
        | file _ _ => simp at hOk
        | symlink tgt m => exact ih "/" _ c nd hOk hNotDir
        | dir m =>
          by_cases he : ((m / 64) % 2 == 0) = true
          · simp [he] at hOk
          · have hef : ((m / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr he
            simp only [hef, Bool.false_eq_true, ↓reduceIte] at hOk ⊢
            exact ih (vfsChildPath cur seg) rest c nd hOk hNotDir

private theorem vfsReadBytes_not_none_or_dir (s₀ : VfsState) (path : String) (bs : ByteArray)
    (hRead : ((vfsOps.readBytes path).run s₀).1 = .ok bs) :
    ∃ canon nd, vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) false 1024 = .ok (canon, nd) ∧
      (∀ dm, nd ≠ .dir dm) ∧ isValidRawPath path = true := by
  dsimp only [vfsOps, StateT.run] at hRead
  unfold vfsReadBytesPure at hRead
  by_cases hV : isValidRawPath path = true
  · simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRead
    cases hR : vfsResolveSegs s₀.nodes "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) true 1024 with
    | error _ => simp [hR] at hRead
    | ok p =>
      rcases p with ⟨c, nd⟩
      cases nd with
      | dir _ => simp [hR] at hRead
      | symlink _ _ => simp [hR] at hRead
      | file bs' m' =>
        have ⟨canon', nd', hNoFollow, hNdNotDir⟩ :=
          vfsResolveSegs_true_not_dir_implies_false_not_dir s₀.nodes 1024 "/"
            (vfsSplitSegs (vfsAbsNorm s₀.cwd path)) c (.file bs' m') hR (fun _ h => by cases h)
        exact ⟨canon', nd', hNoFollow, hNdNotDir, hV⟩
  · have hVF : isValidRawPath path = false := Bool.eq_false_iff.mpr hV
    simp [hVF] at hRead

private theorem splitLastAux_append_singleton_str (xs : List String) (last : String) :
    Internal.splitLastAux (xs ++ [last]) [] = some (xs, last) := by
  simpa using splitLastAux_append_singleton xs [] last

private theorem atomicWriteBytes_step_ok {S : Type} (ops : RawFsOpsM (StateM S))
    (path : String) (bytes : ByteArray) (s₀ s₁ s₂ s₃ s₄ : S) (nonce : Nat)
    (hValid : Internal.isValidAtomicTargetPath path = true)
    (hNeRoot : path ≠ "/")
    (hStat : (∃ e, (ops.stat false path).run s₀ = (.error e, s₁) ∧ e.kind = .notFound) ∨
      (∃ st, (ops.stat false path).run s₀ = (.ok st, s₁) ∧ st.kind ≠ .dir))
    (hNonce : ops.monotonicNonce.run s₁ = (nonce, s₂))
    (tmpPath : String)
    (hTmpPath : tmpPath = Internal.join ((Internal.parent path).getD ".") s!".{((Internal.name path).getD "tmp")}.tmp.{nonce}")
    (hCreate : (ops.createFileNew tmpPath bytes).run s₂ = (.ok (), s₃))
    (hRename : (ops.rename tmpPath path).run s₃ = (.ok (), s₄)) :
    ((Internal.mkApiM ops).atomicWriteBytes path bytes).run s₀ = (.ok (), s₄) := by
  dsimp only [Internal.mkApiM, Internal.atomicWriteBytesImplM, StateT.run]
  rw [hValid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_false_of_ne hNeRoot]
  dsimp only [Bind.bind, StateT.bind]
  rcases hStat with ⟨e, hS, hK⟩ | ⟨st, hS, hD⟩
  · dsimp only [StateT.run] at hS hNonce hCreate hRename
    rw [hS]
    dsimp only [Internal.atomicWriteSiblingM, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [show (e.kind != .notFound) = false from by rw [hK]; decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [hNonce]
    dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [← hTmpPath, hCreate]
    dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [hRename]
    rfl
  · dsimp only [StateT.run] at hS hNonce hCreate hRename
    rw [hS]
    dsimp only [Internal.atomicWriteSiblingM, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [show (st.kind == .dir) = false from by cases hk : st.kind <;> first | exact absurd hk hD | rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [hNonce]
    dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [← hTmpPath, hCreate]
    dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [hRename]
    rfl

private theorem atomicWriteText_eq_atomicWriteBytes {S : Type} (ops : RawFsOpsM (StateM S))
    (path content : String) (s₀ : S) :
    ((Internal.mkApiM ops).atomicWriteText path content).run s₀ =
      ((Internal.mkApiM ops).atomicWriteBytes path content.toUTF8).run s₀ := rfl

private theorem atomicWriteBytes_vfs_step (s₀ : VfsState) (path : String) (bytes : ByteArray)
    (parDir lastSeg parCanon : String) (parSegs : List String) (parMode : Nat)
    (hValidTarget : Internal.isValidAtomicTargetPath path = true)
    (hNeRoot : path ≠ "/")
    (hStatTarget : (∃ e, vfsStatPure s₀ false path = .error e ∧ e.kind = .notFound) ∨
      (∃ st, vfsStatPure s₀ false path = .ok st ∧ st.kind ≠ .dir))
    (hParName : (Internal.parent path).getD "." = parDir ∧ (Internal.name path).getD "tmp" = lastSeg)
    (hLastValid : Internal.validFileName lastSeg = true)
    (hTmpRawValid : isValidRawPath (Internal.join parDir ("." ++ lastSeg ++ ".tmp." ++ toString s₀.nonce)) = true)
    (hPathRawValid : isValidRawPath path = true)
    (hParCanon : isCanonPath parCanon = true ∧ vfsSplitSegs parCanon = parSegs)
    (hAbsTmp : vfsAbsNorm s₀.cwd (Internal.join parDir ("." ++ lastSeg ++ ".tmp." ++ toString s₀.nonce)) =
      vfsChildPath parCanon ("." ++ lastSeg ++ ".tmp." ++ toString s₀.nonce))
    (hAbsDst : vfsAbsNorm s₀.cwd path = vfsChildPath parCanon lastSeg)
    (hParRes : vfsResolveSegs s₀.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode))
    (hPerm : ((parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0) = false)
    (hParSimple : (parSegs = [] ∧ parCanon = "/") ∨
      (∃ d rm, parSegs = [d] ∧ parCanon = "/" ++ d ∧
        s₀.nodes "/" = some (.dir rm) ∧ ((rm / 64) % 2 == 0) = false))
    (hTmpNone : s₀.nodes (vfsChildPath parCanon ("." ++ lastSeg ++ ".tmp." ++ toString s₀.nonce)) = none)
    (hDstNotDir : s₀.nodes (vfsChildPath parCanon lastSeg) = none ∨
      (∃ bs m, s₀.nodes (vfsChildPath parCanon lastSeg) = some (.file bs m)) ∨
      (∃ tgt m, s₀.nodes (vfsChildPath parCanon lastSeg) = some (.symlink tgt m))) :
    ∃ s₁, ((Internal.mkApiM vfsOps).atomicWriteBytes path bytes).run s₀ = (.ok (), s₁) ∧
      s₁.cwd = s₀.cwd ∧ s₁.nonce = s₀.nonce + 1 ∧
      s₁.nodes = fun k =>
        if k == vfsChildPath parCanon lastSeg then some (.file bytes 0o644)
        else if k == vfsChildPath parCanon ("." ++ lastSeg ++ ".tmp." ++ toString s₀.nonce) then none
        else s₀.nodes k := by
  let tmpName := "." ++ lastSeg ++ ".tmp." ++ toString s₀.nonce
  let tmpRaw := Internal.join parDir tmpName
  let tmpKey := vfsChildPath parCanon tmpName
  let dstKey := vfsChildPath parCanon lastSeg
  have hTmpValid : Internal.validFileName tmpName = true := by
    have hL := validFileName_charList lastSeg hLastValid
    have hNotEmp : (!tmpName.toList.isEmpty) = true := by
      cases hC : tmpName.toList with
      | nil => simp [tmpName, String.toList_append] at hC
      | cons _ _ => rfl
    have hNoSlash : '/' ∉ tmpName.toList := by
      simp only [tmpName, String.toList_append, List.mem_append,
        show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide]
      rintro (((hm | hm) | hm) | hm)
      · simp at hm
      · exact hL.2.2.1 hm
      · simp at hm
      · exact slash_not_mem_toString_nat s₀.nonce hm
    have hLenGt2 : 2 < tmpName.toList.length := by
      simp only [tmpName, String.toList_append, List.length_append,
        show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide,
        List.length_cons, List.length_nil]
      omega
    have hNeDot : (tmpName.toList != ['.']) = true := bne_iff_ne.mpr fun heq => by
      have := congrArg List.length heq; simp at this; omega
    have hNeDotDot : (tmpName.toList != ['.', '.']) = true := bne_iff_ne.mpr fun heq => by
      have := congrArg List.length heq; simp at this; omega
    simp only [Internal.validFileName, Bool.and_eq_true]
    exact ⟨⟨⟨hNotEmp, by simpa using hNoSlash⟩, hNeDot⟩, hNeDotDot⟩
  have hTmpNeDst : tmpKey ≠ dstKey := by
    intro heq
    have hSp := congrArg vfsSplitSegs heq
    rw [(vfsChildPath_valid parCanon tmpName hParCanon.1 hTmpValid).2,
        (vfsChildPath_valid parCanon lastSeg hParCanon.1 hLastValid).2] at hSp
    simp only [List.append_cancel_left_eq, List.cons.injEq, and_true] at hSp
    exact tmpSibling_ne_child lastSeg s₀.nonce hSp
  have hParNeTmp : parCanon ≠ tmpKey := by
    intro heq
    have hSp := congrArg vfsSplitSegs heq
    rw [(vfsChildPath_valid parCanon tmpName hParCanon.1 hTmpValid).2] at hSp
    have := congrArg List.length hSp
    simp at this
  have hParNeDst : parCanon ≠ dstKey := by
    intro heq
    have hSp := congrArg vfsSplitSegs heq
    rw [(vfsChildPath_valid parCanon lastSeg hParCanon.1 hLastValid).2] at hSp
    have := congrArg List.length hSp
    simp at this
  have hRootNeTmp : "/" ≠ tmpKey := by
    intro heq
    have hSp := congrArg vfsSplitSegs heq
    rw [show vfsSplitSegs "/" = [] by decide, (vfsChildPath_valid parCanon tmpName hParCanon.1 hTmpValid).2] at hSp
    simp at hSp
  have hRootNeDst : "/" ≠ dstKey := by
    intro heq
    have hSp := congrArg vfsSplitSegs heq
    rw [show vfsSplitSegs "/" = [] by decide, (vfsChildPath_valid parCanon lastSeg hParCanon.1 hLastValid).2] at hSp
    simp at hSp
  have hExec : ((parMode / 64) % 2 == 0) = false := by
    cases h1 : ((parMode / 128) % 2 == 0) <;> cases h2 : ((parMode / 64) % 2 == 0) <;> simp_all
  have hParNodeOk : s₀.nodes parCanon = some (.dir parMode) :=
    vfsResolveSegs_ok_node s₀.nodes 512 "/" parSegs true parCanon (.dir parMode) hParRes
  have hParTreeDir : ∃ dm, vfsTreeNodes s₀.tree parCanon = some (.dir dm) := ⟨parMode, hParNodeOk⟩
  have hPar1024 : vfsResolveSegs s₀.nodes "/" parSegs true 1024 = .ok (parCanon, .dir parMode) :=
    vfsResolveSegs_fuel_mono s₀.nodes 512 1024 "/" parSegs true (parCanon, .dir parMode) (by omega) hParRes
  have hTmpStatNf : vfsResolveSegs s₀.nodes "/" (parSegs ++ [tmpName]) false 1024 =
      .error { kind := .notFound, path := some tmpKey, message := s!"no such file or directory: {tmpKey}" } := by
    rcases hParSimple with ⟨rfl, rfl⟩ | ⟨d, rm, rfl, rfl, hRootD, hRootExec⟩
    · simp only [List.nil_append, vfsResolveSegs, hParNodeOk, hExec, Bool.false_eq_true, ↓reduceIte]
      change (match s₀.nodes tmpKey with
        | none => Except.error { kind := Raw.FsErrorKind.notFound, path := some tmpKey, message := s!"no such file or directory: {tmpKey}" }
        | some (.symlink t m) => Except.ok (tmpKey, VfsNode.symlink t m)
        | some n => Except.ok (tmpKey, n) : Except Raw.FsError (String × VfsNode)) = _
      rw [hTmpNone]
    · have hChildD : vfsChildPath "/" d = "/" ++ d := by simp [vfsChildPath]
      simp only [List.cons_append, List.nil_append, vfsResolveSegs, hRootD, hRootExec, Bool.false_eq_true, ↓reduceIte,
        hChildD, hParNodeOk, hExec]
      change (match s₀.nodes tmpKey with
        | none => Except.error { kind := Raw.FsErrorKind.notFound, path := some tmpKey, message := s!"no such file or directory: {tmpKey}" }
        | some (.symlink t m) => Except.ok (tmpKey, VfsNode.symlink t m)
        | some n => Except.ok (tmpKey, n) : Except Raw.FsError (String × VfsNode)) = _
      rw [hTmpNone]
  let sNonce : VfsState := { s₀ with nonce := s₀.nonce + 1 }
  let tr1 := vfsTreeSet s₀.tree (vfsSplitSegs tmpKey) (some (.file bytes 0o644))
  let sAfterCreate : VfsState := { sNonce with tree := tr1, keys := tmpKey :: s₀.keys }
  have hCreate : vfsCreateFileNewPure sNonce tmpRaw bytes = (.ok (), sAfterCreate) := by
    unfold vfsCreateFileNewPure
    rw [hTmpRawValid]
    dsimp only
    rw [show sNonce.cwd = s₀.cwd from rfl, show sNonce.nodes = s₀.nodes from rfl,
        hAbsTmp, (vfsChildPath_valid parCanon tmpName hParCanon.1 hTmpValid).2, hParCanon.2, hTmpStatNf]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte, splitLastAux_append_singleton_str]
    rw [hPar1024]
    dsimp only
    rw [hPerm]
    simp only [Bool.false_eq_true, ↓reduceIte, sAfterCreate, tr1, sNonce]
    rfl
  have hNodesAfterCreate : sAfterCreate.nodes =
      fun k => if k == tmpKey then some (.file bytes 0o644) else s₀.nodes k := by
    change vfsTreeNodes tr1 = _
    exact vfsTreeNodes_set_leaf s₀.tree parCanon tmpName (some (.file bytes 0o644))
      hParCanon.1 hTmpValid hParTreeDir
      (fun dm h => by change s₀.nodes tmpKey = _ at h; rw [hTmpNone] at h; cases h)
      (fun dm ch h => by cases h)
  have hResolveSimp :
      ∀ (newNodes : String → Option VfsNode)
        (hAgree : ∀ k, k ≠ tmpKey → k ≠ dstKey → newNodes k = s₀.nodes k)
        (lastN : String) (lastNd : VfsNode) (hLastNd : newNodes (vfsChildPath parCanon lastN) = some lastNd)
        (follow : Bool) (fuel : Nat),
        fuel ≥ 3 →
        (follow = false ∨ ∀ t m, lastNd ≠ .symlink t m) →
        vfsResolveSegs newNodes "/" (parSegs ++ [lastN]) follow fuel =
          .ok (vfsChildPath parCanon lastN, lastNd) := by
    intro newNodes hAgree lastN lastNd hLastNd follow fuel hFuel hFol
    have ⟨f0, hfEq⟩ : ∃ f0, fuel = f0 + 3 := ⟨fuel - 3, by omega⟩
    subst hfEq
    rcases hParSimple with ⟨rfl, rfl⟩ | ⟨d, rm, rfl, rfl, hRootD, hRootExec⟩
    · have hRootEq : newNodes "/" = s₀.nodes "/" := hAgree "/" hRootNeTmp hRootNeDst
      simp only [List.nil_append, vfsResolveSegs, hRootEq, hParNodeOk, hExec, Bool.false_eq_true, ↓reduceIte, hLastNd]
      cases lastNd with
      | file _ _ => rfl
      | dir _ => rfl
      | symlink t m =>
        cases follow
        · rfl
        · exfalso
          rcases hFol with hF | hN
          · cases hF
          · exact hN t m rfl
    · have hRootEq : newNodes "/" = s₀.nodes "/" := hAgree "/" hRootNeTmp hRootNeDst
      have hParEq : newNodes ("/" ++ d) = s₀.nodes ("/" ++ d) := hAgree ("/" ++ d) hParNeTmp hParNeDst
      have hChildD : vfsChildPath "/" d = "/" ++ d := by simp [vfsChildPath]
      simp only [List.cons_append, List.nil_append, vfsResolveSegs, hRootEq, hRootD, hRootExec,
        Bool.false_eq_true, ↓reduceIte, hChildD, hParEq, hParNodeOk, hExec, hLastNd]
      cases lastNd with
      | file _ _ => rfl
      | dir _ => rfl
      | symlink t m =>
        cases follow
        · rfl
        · exfalso
          rcases hFol with hF | hN
          · cases hF
          · exact hN t m rfl
  have hResolveParS1 : vfsResolveSegs sAfterCreate.nodes "/" parSegs true 512 = .ok (parCanon, .dir parMode) := by
    have hAgree : ∀ k, k ≠ tmpKey → k ≠ dstKey → sAfterCreate.nodes k = s₀.nodes k := by
      intro k h1 _
      rw [hNodesAfterCreate]
      simp [beq_false_of_ne h1]
    rcases hParSimple with ⟨rfl, rfl⟩ | ⟨d, rm, rfl, rfl, hRootD, hRootExec⟩
    · simp [vfsResolveSegs, hAgree "/" hRootNeTmp hRootNeDst, hParNodeOk]
    · have hChildD : vfsChildPath "/" d = "/" ++ d := by simp [vfsChildPath]
      simp [vfsResolveSegs, hAgree "/" hRootNeTmp hRootNeDst, hRootD, hRootExec, hChildD,
        hAgree ("/" ++ d) hParNeTmp hParNeDst, hParNodeOk]
  have hSrcAfterCreate : vfsResolveSegs sAfterCreate.nodes "/" (parSegs ++ [tmpName]) false 1024 =
      .ok (tmpKey, .file bytes 0o644) := by
    refine hResolveSimp sAfterCreate.nodes (fun k h1 _ => by rw [hNodesAfterCreate]; simp [beq_false_of_ne h1])
      tmpName (.file bytes 0o644) (by change sAfterCreate.nodes tmpKey = _; rw [hNodesAfterCreate]; simp)
      false 1024 (by omega) (Or.inl rfl)
  let moved := vfsTreeGet tr1 (vfsSplitSegs tmpKey)
  have hMovedEq : moved = some (.file bytes 0o644) := by
    have hTop : Option.map vfsTreeTopNode moved = some (.file bytes 0o644) := by
      have hNode : sAfterCreate.nodes tmpKey = some (.file bytes 0o644) := by
        rw [hNodesAfterCreate]; simp
      dsimp only [VfsState.nodes, vfsTreeNodes, sAfterCreate] at hNode
      rw [(vfsChildPath_valid parCanon tmpName hParCanon.1 hTmpValid).1] at hNode
      simpa [moved] using hNode
    cases hm : moved with
    | none => rw [hm] at hTop; cases hTop
    | some w =>
      rw [hm] at hTop
      cases w with
      | dir _ _ => simp [vfsTreeTopNode] at hTop
      | symlink _ _ => simp [vfsTreeTopNode] at hTop
      | file bs' m' =>
        simp [vfsTreeTopNode] at hTop
        rcases hTop with ⟨rfl, rfl⟩
        rfl
  let trRem := vfsTreeSet tr1 (vfsSplitSegs tmpKey) none
  let trFinal := vfsTreeSet trRem (vfsSplitSegs dstKey) moved
  let sFinal : VfsState := { sAfterCreate with tree := trFinal, keys := dstKey :: sAfterCreate.keys }
  have hNodesRem : vfsTreeNodes trRem = fun k => if k == tmpKey then none else s₀.nodes k := by
    have hParDir1 : ∃ dm, vfsTreeNodes tr1 parCanon = some (.dir dm) := by
      change ∃ dm, sAfterCreate.nodes parCanon = some (.dir dm)
      rw [hNodesAfterCreate]
      dsimp only
      rw [beq_false_of_ne hParNeTmp]
      exact hParTreeDir
    have hRemEq := vfsTreeNodes_set_leaf tr1 parCanon tmpName none
      hParCanon.1 hTmpValid hParDir1
      (fun dm h => by
        change sAfterCreate.nodes tmpKey = _ at h
        rw [hNodesAfterCreate] at h; simp at h)
      (fun dm ch h => by cases h)
    rw [hRemEq]
    funext k
    change (if k == tmpKey then none else sAfterCreate.nodes k) = _
    rw [hNodesAfterCreate]
    by_cases hk : k = tmpKey <;> simp [hk]
  have hNodesFinal : sFinal.nodes = fun k =>
      if k == dstKey then some (.file bytes 0o644)
      else if k == tmpKey then none
      else s₀.nodes k := by
    change vfsTreeNodes trFinal = _
    have hParDirRem : ∃ dm, vfsTreeNodes trRem parCanon = some (.dir dm) := by
      rw [hNodesRem]; simp [beq_false_of_ne hParNeTmp]; exact hParTreeDir
    have hDstNotDirRem : ∀ dm, vfsTreeNodes trRem dstKey ≠ some (.dir dm) := by
      intro dm h
      rw [hNodesRem] at h
      simp only [beq_false_of_ne hTmpNeDst.symm, Bool.false_eq_true, ↓reduceIte] at h
      rcases hDstNotDir with hN | ⟨bs, m, hF⟩ | ⟨tgt, m, hS⟩
      · rw [hN] at h; cases h
      · rw [hF] at h; cases h
      · rw [hS] at h; cases h
    have hFinEq := vfsTreeNodes_set_leaf trRem parCanon lastSeg moved
      hParCanon.1 hLastValid hParDirRem hDstNotDirRem (fun dm ch h => by
        rw [hMovedEq] at h; cases h)
    rw [hFinEq, hMovedEq, hNodesRem]
    rfl
  have hDstNotDir1 : (match sAfterCreate.nodes dstKey with | some (.dir _) => true | _ => false) = false := by
    rw [hNodesAfterCreate]
    dsimp only
    rw [beq_false_of_ne hTmpNeDst.symm]
    change (match s₀.nodes dstKey with | some (.dir _) => true | _ => false) = false
    rcases hDstNotDir with hN | ⟨bs, m, hF⟩ | ⟨tgt, m, hS⟩
    · dsimp only [dstKey]; simp [hN]
    · dsimp only [dstKey]; simp [hF]
    · dsimp only [dstKey]; simp [hS]
  have hRename : vfsRenamePure sAfterCreate tmpRaw path = (.ok (), sFinal) := by
    unfold vfsRenamePure
    rw [hTmpRawValid, hPathRawValid]
    dsimp only
    rw [show sAfterCreate.cwd = s₀.cwd from rfl, hAbsTmp, hAbsDst,
        (vfsChildPath_valid parCanon tmpName hParCanon.1 hTmpValid).2, hParCanon.2,
        (vfsChildPath_valid parCanon lastSeg hParCanon.1 hLastValid).2,
        hSrcAfterCreate]
    dsimp only
    rw [splitLastAux_append_singleton_str, hParCanon.2]
    dsimp only
    rw [hResolveParS1]
    dsimp only
    rw [hPerm, show (tmpKey == dstKey) = false from beq_false_of_ne hTmpNeDst, hDstNotDir1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  refine ⟨sFinal, ?_, rfl, rfl, hNodesFinal⟩
  refine atomicWriteBytes_step_ok vfsOps path bytes s₀ s₀ sNonce sAfterCreate sFinal s₀.nonce
    hValidTarget hNeRoot ?_ rfl tmpRaw (by dsimp [tmpRaw, tmpName]; rw [hParName.1, hParName.2]; rfl) hCreate hRename
  rcases hStatTarget with ⟨e, hStErr, hKind⟩ | ⟨st, hStOk, hKind⟩
  · exact Or.inl ⟨e, by simp [vfsOps, StateT.run, hStErr], hKind⟩
  · exact Or.inr ⟨st, by simp [vfsOps, StateT.run, hStOk], hKind⟩

private theorem vfsAbsNorm_canon (cwd path : String) (h : isCanonPath path = true) :
    vfsAbsNorm cwd path = path := by
  have hAbs : Internal.isAbsolute path = true := (Bool.and_eq_true _ _ |>.mp h).1
  have hNorm : Internal.normPath path = path := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp h).2
  simp [vfsAbsNorm, hAbs, hNorm]

private theorem isValidAtomicTargetPath_pfx_slash_single (pfx s : String)
    (hNulPfx : Char.ofNat 0 ∉ pfx.toList)
    (hs : (!s.toList.isEmpty && !('/' ∈ s.toList) && !(Char.ofNat 0 ∈ s.toList) && s != "." && s != "..") = true) :
    Internal.isValidAtomicTargetPath (pfx ++ "/" ++ s) = true := by
  have hsL := isSingleValidName_validFileName s hs
  have hsC := validFileName_charList s hsL
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hs
  have hsNul : Char.ofNat 0 ∉ s.toList := hs.1.1.2
  have hsNeNil : s.toList ≠ [] := by cases hC : s.toList <;> simp_all
  have hsSlash : '/' ∉ s.toList := hsC.2.2.1
  have hStr : (pfx ++ "/" ++ s).toList = pfx.toList ++ ('/' :: s.toList) := by
    simp [String.toList_append, List.append_assoc, show "/".toList = ['/'] by decide]
  have hNeNil : (pfx ++ "/" ++ s).toList ≠ [] := by
    rw [hStr]
    intro heq
    have hLen := congrArg List.length heq
    simp at hLen
  have hNoNul : Char.ofNat 0 ∉ (pfx ++ "/" ++ s).toList := by
    rw [hStr]
    simp only [List.mem_append, List.mem_cons]
    rintro (h | h | h)
    · exact hNulPfx h
    · cases h
    · exact hsNul h
  have hLastNotSlash : ((pfx ++ "/" ++ s).toList.getLast? == some '/') = false := by
    rw [hStr, list_getLast?_append pfx.toList ('/' :: s.toList) (by simp)]
    rw [show ('/' :: s.toList) = ['/'] ++ s.toList from rfl, list_getLast?_append ['/'] s.toList hsNeNil]
    apply beq_false_of_ne
    intro heq
    have hMem : '/' ∈ s.toList := by
      have : s.toList.reverse.head? = some '/' := by simpa [List.head?_reverse] using heq
      cases hr : s.toList.reverse with
      | nil => simp [hr] at this
      | cons c cs =>
        rw [hr] at this; simp at this; subst this
        exact List.mem_reverse.mp (by rw [hr]; simp)
    exact hsSlash hMem
  have hRaw : isValidRawPath (pfx ++ "/" ++ s) = true := by
    simp only [isValidRawPath, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨?_, decide_eq_false hNoNul⟩, ?_⟩
    · cases hC : (pfx ++ "/" ++ s).toList with
      | nil => exact absurd hC hNeNil
      | cons _ _ => rfl
    · rw [hLastNotSlash, Bool.and_false]
  have hNotDot : Internal.hasDotFinalSegment (pfx ++ "/" ++ s) = false := by
    unfold Internal.hasDotFinalSegment
    have hRev : (pfx ++ "/" ++ s).toList.reverse = s.toList.reverse ++ ('/' :: pfx.toList.reverse) := by
      rw [hStr, List.reverse_append, List.reverse_cons]
      simp [List.append_assoc]
    rw [hRev]
    cases hSr : s.toList.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp hSr) hsNeNil
    | cons c1 cs1 =>
      cases cs1 with
      | nil =>
        by_cases hc1 : c1 = '.'
        · subst hc1
          have hsEq : s.toList = ['.'] := by
            simpa using congrArg List.reverse hSr
          exact absurd hsEq (bne_iff_ne.mp hsC.2.1)
        · simp [hc1]
      | cons c2 cs2 =>
        cases cs2 with
        | nil =>
          by_cases hc2 : c2 = '/'
          · subst hc2
            have hMem : '/' ∈ s.toList := List.mem_reverse.mp (by rw [hSr]; simp)
            exact absurd hMem hsSlash
          · by_cases hc1 : c1 = '.'
            · by_cases hc2d : c2 = '.'
              · subst hc1 hc2d
                have hsEq : s.toList = ['.', '.'] := by
                  simpa using congrArg List.reverse hSr
                exact absurd hsEq hsC.2.2.2
              · subst hc1; simp [hc2, hc2d]
            · simp [hc1]
        | cons c3 cs3 =>
          by_cases hc1 : c1 = '.'
          · by_cases hc2 : c2 = '/'
            · subst hc2
              have hMem : '/' ∈ s.toList := List.mem_reverse.mp (by rw [hSr]; simp)
              exact absurd hMem hsSlash
            · by_cases hc2d : c2 = '.'
              · by_cases hc3 : c3 = '/'
                · subst hc3
                  have hMem : '/' ∈ s.toList := List.mem_reverse.mp (by rw [hSr]; simp)
                  exact absurd hMem hsSlash
                · subst hc1 hc2d; simp [hc2, hc3]
              · subst hc1; simp [hc2, hc2d]
          · simp [hc1]
  change (isValidRawPath (pfx ++ "/" ++ s) && !Internal.hasDotFinalSegment (pfx ++ "/" ++ s)) = true
  rw [hRaw, hNotDot]
  rfl

private theorem join_slash_dir_of_not_abs (dir s : String) (hDir : Internal.validFileName dir = true)
    (hNotAbs : Internal.isAbsolute s = false) :
    Internal.join ("/" ++ dir) s = "/" ++ dir ++ "/" ++ s := by
  have hL := validFileName_charList dir hDir
  have hNeNil : dir.toList ≠ [] := by cases hC : dir.toList <;> simp_all
  have hNotEmp : ("/" ++ dir).isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have heq : "/" ++ dir = "" := String.isEmpty_iff.mp he
    have hL' := congrArg String.toList heq
    simp [String.toList_append, show "/".toList = ['/'] by decide] at hL'
  have hLast : (('/' :: dir.toList).getLast? == some '/') = false := by
    rw [show ('/' :: dir.toList) = ['/'] ++ dir.toList from rfl, list_getLast?_append ['/'] dir.toList hNeNil]
    apply beq_false_of_ne
    intro heq
    have hMem : '/' ∈ dir.toList := by
      have : dir.toList.reverse.head? = some '/' := by simpa [List.head?_reverse] using heq
      cases hr : dir.toList.reverse with
      | nil => simp [hr] at this
      | cons c cs =>
        rw [hr] at this; simp at this; subst this
        exact List.mem_reverse.mp (by rw [hr]; simp)
    exact hL.2.2.1 hMem
  simp [Internal.join, hNotAbs, hNotEmp, hLast, String.append_assoc]

private theorem vfsChildPath_dir_child (dir child : String)
    (h1 : Internal.validFileName dir = true) (h2 : Internal.validFileName child = true) :
    vfsChildPath ("/" ++ dir) child = "/" ++ dir ++ "/" ++ child ∧
    isCanonPath ("/" ++ dir ++ "/" ++ child) = true ∧
    vfsSplitSegs ("/" ++ dir ++ "/" ++ child) = [dir, child] ∧
    (∀ cwd, vfsAbsNorm cwd ("/" ++ dir ++ "/" ++ child) = "/" ++ dir ++ "/" ++ child) := by
  have h1C := vfsChildPath_valid "/" dir (by decide) h1
  have hSlash : vfsChildPath "/" dir = "/" ++ dir := by simp [vfsChildPath]
  rw [hSlash] at h1C
  have hChild : vfsChildPath ("/" ++ dir) child = "/" ++ dir ++ "/" ++ child := by
    have hNe : "/" ++ dir ≠ "/" := by
      intro heq
      have := congrArg vfsSplitSegs heq
      rw [h1C.2, show vfsSplitSegs "/" = [] by decide] at this
      simp at this
    simp [vfsChildPath, hNe, String.append_assoc]
  have h2C := vfsChildPath_valid ("/" ++ dir) child h1C.1 h2
  rw [hChild, h1C.2] at h2C
  have hNorm : Internal.normPath ("/" ++ dir ++ "/" ++ child) = "/" ++ dir ++ "/" ++ child :=
    beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp h2C.1).2
  have hAbs : Internal.isAbsolute ("/" ++ dir ++ "/" ++ child) = true :=
    (Bool.and_eq_true _ _ |>.mp h2C.1).1
  refine ⟨hChild, h2C.1, h2C.2, fun cwd => ?_⟩
  simp [vfsAbsNorm, hAbs, hNorm]

private theorem isValidRawPath_dir_child (dir child : String)
    (hd : (!dir.toList.isEmpty && !('/' ∈ dir.toList) && !(Char.ofNat 0 ∈ dir.toList) && dir != "." && dir != "..") = true)
    (hc : Internal.validFileName child = true)
    (hNulC : Char.ofNat 0 ∉ child.toList) :
    isValidRawPath ("/" ++ dir ++ "/" ++ child) = true := by
  have hcL := validFileName_charList child hc
  have hcNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hd
  have hdNul : Char.ofNat 0 ∉ dir.toList := hd.1.1.2
  have hStr : ("/" ++ dir ++ "/" ++ child).toList = '/' :: dir.toList ++ ('/' :: child.toList) := by
    simp [String.toList_append, List.append_assoc, show "/".toList = ['/'] by decide]
  have hNoNul : Char.ofNat 0 ∉ ("/" ++ dir ++ "/" ++ child).toList := by
    rw [hStr]
    simp only [List.mem_append, List.mem_cons]
    rintro ((h | h) | (h | h))
    · cases h
    · exact hdNul h
    · cases h
    · exact hNulC h
  have hLast : (("/" ++ dir ++ "/" ++ child).toList.getLast? == some '/') = false := by
    rw [hStr, show ('/' :: dir.toList) ++ ('/' :: child.toList) = ['/' ] ++ dir.toList ++ ('/' :: child.toList) from rfl]
    rw [list_getLast?_append (['/' ] ++ dir.toList) ('/' :: child.toList) (by simp)]
    rw [show ('/' :: child.toList) = ['/'] ++ child.toList from rfl, list_getLast?_append ['/'] child.toList hcNeNil]
    apply beq_false_of_ne
    intro heq
    have hMem : '/' ∈ child.toList := by
      have : child.toList.reverse.head? = some '/' := by simpa [List.head?_reverse] using heq
      cases hr : child.toList.reverse with
      | nil => simp [hr] at this
      | cons c cs =>
        rw [hr] at this; simp at this; subst this
        exact List.mem_reverse.mp (by rw [hr]; simp)
    exact hcL.2.2.1 hMem
  simp only [isValidRawPath, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  refine ⟨⟨?_, hNoNul⟩, ?_⟩
  · cases hC : ("/" ++ dir ++ "/" ++ child).toList with
    | nil => simp [hStr] at hC
    | cons _ _ => rfl
  · rw [hLast, Bool.and_false]

private theorem vfsStat_root_child_ok_to_node (s₀ : VfsState) (child : String) (st : FileStat)
    (hValid : Internal.validFileName child = true)
    (hRoot : ∃ stRoot, ((vfsOps.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧ (stRoot.mode / 64) % 2 = 1)
    (hStat : ((vfsOps.stat false ("/" ++ child)).run s₀).1 = .ok st) :
    ∃ nd, s₀.nodes ("/" ++ child) = some nd ∧ vfsToStat nd = st := by
  rcases hRoot with ⟨stR, hRs, hRk, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hRexec : ((stR.mode / 64) % 2 == 0) = false := by simp [hRx]
  have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hValid
  have hChildEq : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  rw [hChildEq] at hCanonC hSplitC
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
  dsimp only [vfsOps, vfsStatPure, StateT.run] at hStat
  rw [vfsAbsNorm_canon s₀.cwd ("/" ++ child) hCanonC, hSplitC] at hStat
  unfold vfsResolveSegs at hStat
  rw [hRootNd] at hStat
  dsimp only at hStat
  rw [hRexec, hChildEq] at hStat
  simp only [Bool.false_eq_true, ↓reduceIte] at hStat
  unfold vfsResolveSegs at hStat
  cases hN : s₀.nodes ("/" ++ child) with
  | none => simp [hN] at hStat
  | some nd =>
    refine ⟨nd, rfl, ?_⟩
    cases nd with
    | file bs m => simp [hN] at hStat; exact hStat
    | dir m => simp [hN] at hStat; exact hStat
    | symlink tgt m => simp [hN] at hStat; exact hStat

private theorem vfsStat_root_child_isOk_false (s₀ : VfsState) (child : String)
    (hValid : Internal.validFileName child = true)
    (_hRaw : isValidRawPath ("/" ++ child) = true)
    (hRoot : ∃ stRoot, ((vfsOps.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧ (stRoot.mode / 64) % 2 = 1)
    (hNotOk : ((vfsOps.stat false ("/" ++ child)).run s₀).1.isOk = false) :
    s₀.nodes ("/" ++ child) = none := by
  rcases hRoot with ⟨stR, hRs, hRk, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hRexec : ((stR.mode / 64) % 2 == 0) = false := by simp [hRx]
  have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hValid
  have hChildEq : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  rw [hChildEq] at hCanonC hSplitC
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
  dsimp only [vfsOps, vfsStatPure, StateT.run] at hNotOk
  rw [vfsAbsNorm_canon s₀.cwd ("/" ++ child) hCanonC, hSplitC] at hNotOk
  unfold vfsResolveSegs at hNotOk
  rw [hRootNd] at hNotOk
  dsimp only at hNotOk
  rw [hRexec, hChildEq] at hNotOk
  simp only [Bool.false_eq_true, ↓reduceIte] at hNotOk
  unfold vfsResolveSegs at hNotOk
  cases hN : s₀.nodes ("/" ++ child) with
  | none => rfl
  | some nd =>
    exfalso
    rw [hN] at hNotOk
    cases nd <;> cases hNotOk

private theorem vfsStat_root_child_isOk_true (s₀ : VfsState) (child : String)
    (hValid : Internal.validFileName child = true)
    (_hRaw : isValidRawPath ("/" ++ child) = true)
    (hRoot : ∃ stRoot, ((vfsOps.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧ (stRoot.mode / 64) % 2 = 1)
    (hOk : ((vfsOps.stat false ("/" ++ child)).run s₀).1.isOk = true) :
    ∃ nd, s₀.nodes ("/" ++ child) = some nd := by
  rcases hRoot with ⟨stR, hRs, hRk, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hRexec : ((stR.mode / 64) % 2 == 0) = false := by simp [hRx]
  have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hValid
  have hChildEq : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  rw [hChildEq] at hCanonC hSplitC
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
  dsimp only [vfsOps, vfsStatPure, StateT.run] at hOk
  rw [vfsAbsNorm_canon s₀.cwd ("/" ++ child) hCanonC, hSplitC] at hOk
  unfold vfsResolveSegs at hOk
  rw [hRootNd] at hOk
  dsimp only at hOk
  rw [hRexec, hChildEq] at hOk
  simp only [Bool.false_eq_true, ↓reduceIte] at hOk
  unfold vfsResolveSegs at hOk
  cases hN : s₀.nodes ("/" ++ child) with
  | none => rw [hN] at hOk; cases hOk
  | some nd => exact ⟨nd, rfl⟩

private theorem atomicWriteBytes_root_child_ok (s₀ : VfsState) (child : String) (bytes : ByteArray)
    (hChild : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true)
    (hRoot : ∃ stRoot, ((vfsOps.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hTmpMissing : ((vfsOps.stat false ("/." ++ child ++ ".tmp." ++ toString s₀.nonce)).run s₀).1.isOk = false)
    (hTarget : (∃ e, ((vfsOps.stat false ("/" ++ child)).run s₀).1 = .error e ∧ e.kind = .notFound) ∨
      (∃ st, ((vfsOps.stat false ("/" ++ child)).run s₀).1 = .ok st ∧ st.kind ≠ .dir)) :
    ∃ s₁, ((Internal.mkApiM vfsOps).atomicWriteBytes ("/" ++ child) bytes).run s₀ = (.ok (), s₁) ∧
      s₁.cwd = s₀.cwd ∧ s₁.nonce = s₀.nonce + 1 ∧
      s₁.nodes = fun k =>
        if k == ("/" ++ child) then some (.file bytes 0o644)
        else if k == ("/." ++ child ++ ".tmp." ++ toString s₀.nonce) then none
        else s₀.nodes k := by
  have hChildValid := isSingleValidName_validFileName child hChild
  have hChS := hChild
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hChS
  have hNulChild : Char.ofNat 0 ∉ child.toList := hChS.1.1.2
  let tmpName := "." ++ child ++ ".tmp." ++ toString s₀.nonce
  have hTmpValid : Internal.validFileName tmpName = true := validFileName_tmpSibling child s₀.nonce hChildValid
  have hTmpNotAbs : Internal.isAbsolute tmpName = false :=
    isAbsolute_false_dotPrefix (child ++ ".tmp." ++ toString s₀.nonce)
  have hTmpEq : "/" ++ tmpName = "/." ++ child ++ ".tmp." ++ toString s₀.nonce := by
    apply String.ext_iff.mpr
    simp [tmpName, String.toList_append, List.append_assoc,
      show "/".toList = ['/'] by decide, show "/.".toList = ['/', '.'] by decide, show ".".toList = ['.'] by decide]
  have hTmpJoin : Internal.join "/" tmpName = "/." ++ child ++ ".tmp." ++ toString s₀.nonce := by
    rw [join_slash_of_not_abs tmpName hTmpNotAbs, hTmpEq]
  have hTmpRaw : isValidRawPath ("/." ++ child ++ ".tmp." ++ toString s₀.nonce) = true :=
    isValidRawPath_tmpSibling child s₀.nonce hChild
  have hPathRaw : isValidRawPath ("/" ++ child) = true := isValidRawPath_of_singleValid child hChild
  rcases hRoot with ⟨stR, hRs, hRk, hRw, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hTmpNone : s₀.nodes ("/." ++ child ++ ".tmp." ++ toString s₀.nonce) = none := by
    have hEq := vfsStat_root_child_isOk_false s₀ tmpName hTmpValid
      (by rw [hTmpEq]; exact hTmpRaw) ⟨stR, hRs, hRk, hRx⟩
      (by rw [hTmpEq]; exact hTmpMissing)
    rw [← hTmpEq]; exact hEq
  have hDstNotDir : s₀.nodes ("/" ++ child) = none ∨
      (∃ bs m, s₀.nodes ("/" ++ child) = some (.file bs m)) ∨
      (∃ tgt m, s₀.nodes ("/" ++ child) = some (.symlink tgt m)) := by
    rcases hTarget with ⟨e, hErr, _⟩ | ⟨st, hOk, hNd⟩
    · cases hN : s₀.nodes ("/" ++ child) with
      | none => exact Or.inl rfl
      | some nd =>
        exfalso
        have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hChildValid
        have hChildEq : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
        rw [hChildEq] at hCanonC hSplitC
        rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
        dsimp only [vfsOps, vfsStatPure, StateT.run] at hErr
        rw [vfsAbsNorm_canon s₀.cwd ("/" ++ child) hCanonC, hSplitC] at hErr
        unfold vfsResolveSegs at hErr
        rw [hRootNd] at hErr
        dsimp only at hErr
        rw [show ((stR.mode / 64) % 2 == 0) = false from by simp [hRx], hChildEq] at hErr
        simp only [Bool.false_eq_true, ↓reduceIte] at hErr
        unfold vfsResolveSegs at hErr
        cases nd <;> simp [hN] at hErr
    · have ⟨nd, hN, hTo⟩ := vfsStat_root_child_ok_to_node s₀ child st hChildValid ⟨stR, hRs, hRk, hRx⟩ hOk
      cases nd with
      | dir m => exfalso; subst hTo; simp [vfsToStat] at hNd
      | file bs m => exact Or.inr (Or.inl ⟨bs, m, hN⟩)
      | symlink tgt m => exact Or.inr (Or.inr ⟨tgt, m, hN⟩)
  have hValidTarget : Internal.isValidAtomicTargetPath ("/" ++ child) = true :=
    isValidAtomicTargetPath_pfx_slash_single "" child (by simp) hChild
  have hNeRoot : "/" ++ child ≠ "/" := by
    intro heq
    have hL := congrArg (fun x : String => x.toList.length) heq
    have hL1 := validFileName_charList child hChildValid
    have hNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
    rw [String.toList_append, show "/".toList = ['/'] by decide] at hL
    cases hC : child.toList with
    | nil => exact hNeNil hC
    | cons _ _ => simp [hC] at hL
  have hParName := parent_name_slash_child child hChildValid
  have hRootRes : vfsResolveSegs s₀.nodes "/" [] true 512 = .ok ("/", .dir stR.mode) := by
    simp [vfsResolveSegs, hRootNd]
  have hPerm : ((stR.mode / 128) % 2 == 0 || (stR.mode / 64) % 2 == 0) = false := by
    simp [hRw, hRx]
  have hStatStep : (∃ e, vfsStatPure s₀ false ("/" ++ child) = .error e ∧ e.kind = .notFound) ∨
      (∃ st, vfsStatPure s₀ false ("/" ++ child) = .ok st ∧ st.kind ≠ .dir) := by
    simpa [vfsOps, StateT.run] using hTarget
  have hCChild : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  have hCTmp : vfsChildPath "/" ("." ++ child ++ ".tmp." ++ toString s₀.nonce) =
      "/." ++ child ++ ".tmp." ++ toString s₀.nonce := by
    change vfsChildPath "/" tmpName = _; rw [show vfsChildPath "/" tmpName = "/" ++ tmpName from by simp [vfsChildPath], hTmpEq]
  have hTmpCanon : isCanonPath ("/." ++ child ++ ".tmp." ++ toString s₀.nonce) = true := by
    have ⟨hc, _⟩ := vfsChildPath_valid "/" tmpName (by decide) hTmpValid
    change isCanonPath (vfsChildPath "/" ("." ++ child ++ ".tmp." ++ toString s₀.nonce)) = true at hc
    rwa [hCTmp] at hc
  have hChildCanon : isCanonPath ("/" ++ child) = true := by
    have ⟨hc, _⟩ := vfsChildPath_valid "/" child (by decide) hChildValid
    rwa [hCChild] at hc
  have hStep := atomicWriteBytes_vfs_step s₀ ("/" ++ child) bytes "/" child "/" [] stR.mode
    hValidTarget hNeRoot hStatStep (by simp [hParName.1, hParName.2]) hChildValid
    (by rw [hTmpJoin]; exact hTmpRaw) hPathRaw ⟨by decide, by decide⟩
    (by rw [hTmpJoin, hCTmp]; exact vfsAbsNorm_canon s₀.cwd _ hTmpCanon)
    (by rw [hCChild]; exact vfsAbsNorm_canon s₀.cwd _ hChildCanon)
    hRootRes hPerm (Or.inl ⟨rfl, rfl⟩)
    (by rw [hCTmp]; exact hTmpNone)
    (by rw [hCChild]; exact hDstNotDir)
  rcases hStep with ⟨s₁, hs1, hcwd, hnonce, hnodes⟩
  rw [hCChild, hCTmp] at hnodes
  exact ⟨s₁, hs1, hcwd, hnonce, hnodes⟩

private theorem vfsReadBytes_root_child_ok (s : VfsState) (child : String) (bytes : ByteArray) (mRm mFile : Nat)
    (hValid : Internal.validFileName child = true)
    (hRaw : isValidRawPath ("/" ++ child) = true)
    (hRoot : s.nodes "/" = some (.dir mRm))
    (hExec : (mRm / 64) % 2 = 1)
    (hFile : s.nodes ("/" ++ child) = some (.file bytes mFile)) :
    ((vfsOps.readBytes ("/" ++ child)).run s).1 = .ok bytes := by
  have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hValid
  have hChildEq : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  rw [hChildEq] at hCanonC hSplitC
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
  dsimp only [vfsOps, vfsReadBytesPure, StateT.run]
  rw [hRaw, vfsAbsNorm_canon s.cwd ("/" ++ child) hCanonC, hSplitC]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold vfsResolveSegs
  rw [hRoot]
  dsimp only
  rw [show ((mRm / 64) % 2 == 0) = false from by simp [hExec], hChildEq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold vfsResolveSegs
  rw [hFile]

private theorem vfsOps_stat_dir755_root (s : VfsState) (hRoot : s.nodes "/" = some (.dir 0o755)) :
    ((vfsOps.stat false "/").run s).1 = .ok (vfsToStat (.dir 0o755)) := by
  dsimp only [vfsOps, vfsStatPure, StateT.run]
  rw [vfsAbsNorm_canon s.cwd "/" (by decide), show vfsSplitSegs "/" = [] from by decide]
  unfold vfsResolveSegs
  rw [hRoot]

private theorem vfsOps_stat_dir755_child_none (s : VfsState) (child : String)
    (hValid : Internal.validFileName child = true)
    (hRoot : s.nodes "/" = some (.dir 0o755))
    (hNone : s.nodes ("/" ++ child) = none) :
    ((vfsOps.stat false ("/" ++ child)).run s).1 =
      .error { kind := .notFound, path := some ("/" ++ child), message := s!"no such file or directory: /{child}" } := by
  have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hValid
  have hChildEq : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  rw [hChildEq] at hCanonC hSplitC
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
  dsimp only [vfsOps, vfsStatPure, StateT.run]
  rw [vfsAbsNorm_canon s.cwd ("/" ++ child) hCanonC, hSplitC]
  unfold vfsResolveSegs
  rw [hRoot]
  dsimp only
  rw [show ((0o755 / 64) % 2 == 0) = false from by decide, hChildEq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold vfsResolveSegs
  rw [hNone]
  rfl

private theorem vfsOps_stat_dir755_child_some (s : VfsState) (child : String) (nd : VfsNode)
    (hValid : Internal.validFileName child = true)
    (hRoot : s.nodes "/" = some (.dir 0o755))
    (hSome : s.nodes ("/" ++ child) = some nd) :
    ((vfsOps.stat false ("/" ++ child)).run s).1 = .ok (vfsToStat nd) := by
  have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hValid
  have hChildEq : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
  rw [hChildEq] at hCanonC hSplitC
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
  dsimp only [vfsOps, vfsStatPure, StateT.run]
  rw [vfsAbsNorm_canon s.cwd ("/" ++ child) hCanonC, hSplitC]
  unfold vfsResolveSegs
  rw [hRoot]
  dsimp only
  rw [show ((0o755 / 64) % 2 == 0) = false from by decide, hChildEq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold vfsResolveSegs
  rw [hSome]
  cases nd <;> rfl

/-- Proof of `test_fs_vfs_atomicWriteBytes_writesAtomically` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_writesAtomically :
    AllPass (test_fs_vfs_atomicWriteBytes_writesAtomically Internal.mkApiM vfsOps) := by
  intro s₀ child bytes hChild hRoot hTmpMissing hTarget
  rcases atomicWriteBytes_root_child_ok s₀ child bytes hChild hRoot hTmpMissing hTarget with
    ⟨s₁, hStep, _, _, hNodes₁⟩
  have hChildValid := isSingleValidName_validFileName child hChild
  have hChS : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true := hChild
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hChS
  have hNulChild : Char.ofNat 0 ∉ child.toList := hChS.1.1.2
  let tmpName := "." ++ child ++ ".tmp." ++ toString s₀.nonce
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString s₀.nonce
  have hTmpValid : Internal.validFileName tmpName = true := validFileName_tmpSibling child s₀.nonce hChildValid
  have hTmpRaw : isValidRawPath tmpPath = true := isValidRawPath_tmpSibling child s₀.nonce hChild
  have hPathRaw : isValidRawPath ("/" ++ child) = true := isValidRawPath_of_singleValid child hChild
  rcases hRoot with ⟨stR, hRs, hRk, hRw, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hTmpEq : "/" ++ tmpName = tmpPath := by
    apply String.ext_iff.mpr
    simp [tmpName, tmpPath, String.toList_append, List.append_assoc,
      show "/.".toList = ['/', '.'] by decide, show "/".toList = ['/'] by decide, show ".".toList = ['.'] by decide]
  have hRootNePath : "/" ≠ "/" ++ child := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" child (by decide) hChildValid).2
    have hC : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC] at hSp
    rw [hSp, show vfsSplitSegs "/" = [] by decide] at this
    simp at this
  have hRootNeTmp : "/" ≠ tmpPath := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" tmpName (by decide) hTmpValid).2
    have hC : vfsChildPath "/" tmpName = tmpPath := by simp [vfsChildPath, hTmpEq]
    rw [hC] at hSp
    rw [hSp, show vfsSplitSegs "/" = [] by decide] at this
    simp at this
  have hTmpNePath : tmpPath ≠ "/" ++ child := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp1 := (vfsChildPath_valid "/" tmpName (by decide) hTmpValid).2
    have hC1 : vfsChildPath "/" tmpName = tmpPath := by simp [vfsChildPath, hTmpEq]
    rw [hC1] at hSp1
    have hSp2 := (vfsChildPath_valid "/" child (by decide) hChildValid).2
    have hC2 : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC2] at hSp2
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSp1 hSp2
    rw [hSp1, hSp2] at this
    simp only [List.cons.injEq, and_true] at this
    exact tmpSibling_ne_child child s₀.nonce this
  have hRoot₁ : s₁.nodes "/" = some (.dir stR.mode) := by
    rw [hNodes₁]; dsimp only
    rw [beq_false_of_ne hRootNePath, beq_false_of_ne hRootNeTmp]
    exact hRootNd
  have hFile₁ : s₁.nodes ("/" ++ child) = some (.file bytes 0o644) := by
    rw [hNodes₁]; simp
  have hTmpNone₁ : s₁.nodes tmpPath = none := by
    rw [hNodes₁]; dsimp only
    rw [beq_false_of_ne hTmpNePath]
    simp [tmpPath]
  have hRead₁ : (((Internal.mkApiM vfsOps).readBytes ("/" ++ child)).run s₁).1 = .ok bytes := by
    change ((vfsOps.readBytes ("/" ++ child)).run s₁).1 = .ok bytes
    exact vfsReadBytes_root_child_ok s₁ child bytes stR.mode 0o644 hChildValid hPathRaw hRoot₁ hRx hFile₁
  have hLstat₁ : ∃ st, (((Internal.mkApiM vfsOps).lstat ("/" ++ child)).run s₁).1 = .ok st ∧
      st.kind = .file ∧ st.byteSize = bytes.size := by
    have ⟨hCanonC, hSplitC⟩ := vfsChildPath_valid "/" child (by decide) hChildValid
    have hC : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC] at hCanonC hSplitC
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC
    dsimp only [Internal.mkApiM, vfsOps, vfsStatPure, StateT.run]
    rw [vfsAbsNorm_canon s₁.cwd ("/" ++ child) hCanonC, hSplitC]
    unfold vfsResolveSegs
    rw [hRoot₁]
    dsimp only
    rw [show ((stR.mode / 64) % 2 == 0) = false from by simp [hRx], hC]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [hFile₁]
    exact ⟨vfsToStat (.file bytes 0o644), rfl, rfl, rfl⟩
  have hTmpNotOk₁ : ((vfsOps.stat false tmpPath).run s₁).1.isOk = false := by
    have ⟨hCanonT, hSplitT⟩ := vfsChildPath_valid "/" tmpName (by decide) hTmpValid
    have hC : vfsChildPath "/" tmpName = tmpPath := by simp [vfsChildPath, hTmpEq]
    rw [hC] at hCanonT hSplitT
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitT
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [vfsAbsNorm_canon s₁.cwd tmpPath hCanonT, hSplitT]
    unfold vfsResolveSegs
    rw [hRoot₁]
    dsimp only
    rw [show ((stR.mode / 64) % 2 == 0) = false from by simp [hRx], hC]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [hTmpNone₁]
    rfl
  dsimp only
  rw [hStep]
  dsimp only [assert]
  exact ⟨rfl, hRead₁, hLstat₁, hTmpNotOk₁, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_writesAtomically`. -/
theorem reach_fs_vfs_atomicWriteBytes_writesAtomically :
    CanReach (test_fs_vfs_atomicWriteBytes_writesAtomically Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hTmp : ((vfsOps.stat false ("/." ++ "f" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = false := by
    rw [show "/." ++ "f" ++ ".tmp." ++ toString st.nonce = "/" ++ ".f.tmp.0" from by decide]
    rw [vfsOps_stat_dir755_child_none st ".f.tmp.0" (by decide) rfl rfl]
    rfl
  have hMiss : ∃ e, ((vfsOps.stat false ("/" ++ "f")).run st).1 = .error e ∧ e.kind = .notFound :=
    ⟨_, vfsOps_stat_dir755_child_none st "f" (by decide) rfl rfl, rfl⟩
  exact ⟨st, "f", ByteArray.mk #[1, 2], by decide, hRoot, hTmp, Or.inl hMiss,
    proof_fs_vfs_atomicWriteBytes_writesAtomically st "f" (ByteArray.mk #[1, 2])
      (by decide) hRoot hTmp (Or.inl hMiss)⟩

/-- Proof of `test_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget :
    AllPass (test_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget Internal.mkApiM vfsOps) := by
  intro s₀ child victimPath newBytes origBytes victimBytes hChild hRoot hTmpExists hOrig hVictim
  have hChildValid := isSingleValidName_validFileName child hChild
  have hChS : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true := hChild
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hChS
  have hNulChild : Char.ofNat 0 ∉ child.toList := hChS.1.1.2
  let tmpName := "." ++ child ++ ".tmp." ++ toString s₀.nonce
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString s₀.nonce
  have hTmpValid : Internal.validFileName tmpName = true := validFileName_tmpSibling child s₀.nonce hChildValid
  have hTmpNotAbs : Internal.isAbsolute tmpName = false :=
    isAbsolute_false_dotPrefix (child ++ ".tmp." ++ toString s₀.nonce)
  have hTmpEq : "/" ++ tmpName = tmpPath := by
    apply String.ext_iff.mpr
    simp [tmpName, tmpPath, String.toList_append, List.append_assoc,
      show "/".toList = ['/'] by decide, show "/.".toList = ['/', '.'] by decide, show ".".toList = ['.'] by decide]
  have hTmpJoin : Internal.join "/" tmpName = tmpPath := by
    rw [join_slash_of_not_abs tmpName hTmpNotAbs, hTmpEq]
  have hTmpRaw : isValidRawPath tmpPath = true := isValidRawPath_tmpSibling child s₀.nonce hChild
  have hValidTarget : Internal.isValidAtomicTargetPath ("/" ++ child) = true :=
    isValidAtomicTargetPath_pfx_slash_single "" child (by simp) hChild
  have hNeRoot : "/" ++ child ≠ "/" := by
    intro heq
    have hL := congrArg (fun x : String => x.toList.length) heq
    have hL1 := validFileName_charList child hChildValid
    have hNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
    rw [String.toList_append, show "/".toList = ['/'] by decide] at hL
    cases hC : child.toList with
    | nil => exact hNeNil hC
    | cons _ _ => simp [hC] at hL
  rcases hRoot with ⟨stR, hRs, hRk, hRw, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have ⟨canonO, ndO, hResO, hNotDirO, hRawO⟩ := vfsReadBytes_not_none_or_dir s₀ ("/" ++ child) origBytes hOrig
  have hStatPath : (vfsOps.stat false ("/" ++ child)).run s₀ = (.ok (vfsToStat ndO), s₀) := by
    dsimp only [vfsOps, vfsStatPure, StateT.run]; rw [hResO]
  have hKindPath : (vfsToStat ndO).kind ≠ .dir := by
    cases ndO with
    | dir m => exact absurd rfl (hNotDirO m)
    | file _ _ => intro h; cases h
    | symlink _ _ => intro h; cases h
  have ⟨ndTmp, hTmpNd⟩ := vfsStat_root_child_isOk_true s₀ tmpName hTmpValid
    (by rw [hTmpEq]; exact hTmpRaw) ⟨stR, hRs, hRk, hRx⟩
    (by rw [hTmpEq]; exact hTmpExists)
  rw [hTmpEq] at hTmpNd
  let sNonce : VfsState := { s₀ with nonce := s₀.nonce + 1 }
  have hCreateErr : vfsCreateFileNewPure sNonce tmpPath newBytes =
      (.error { kind := .alreadyExists, path := some tmpPath, message := s!"already exists: {tmpPath}" }, sNonce) := by
    have ⟨hCanonT, hSplitT⟩ := vfsChildPath_valid "/" tmpName (by decide) hTmpValid
    have hC : vfsChildPath "/" tmpName = tmpPath := by
      rw [show vfsChildPath "/" tmpName = "/" ++ tmpName from by simp [vfsChildPath], hTmpEq]
    rw [hC] at hCanonT hSplitT
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitT
    unfold vfsCreateFileNewPure
    rw [show sNonce.nodes = s₀.nodes from rfl, show sNonce.cwd = s₀.cwd from rfl, hTmpRaw]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      vfsAbsNorm_canon s₀.cwd tmpPath hCanonT,
      hSplitT]
    unfold vfsResolveSegs
    rw [hRootNd]
    dsimp only
    rw [show ((stR.mode / 64) % 2 == 0) = false from by simp [hRx], hC]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [hTmpNd]
    cases ndTmp <;> rfl
  have hParName := parent_name_slash_child child hChildValid
  have hStep : ((Internal.mkApiM vfsOps).atomicWriteBytes ("/" ++ child) newBytes).run s₀ =
      (.error { kind := .alreadyExists, path := some tmpPath, message := s!"already exists: {tmpPath}" }, sNonce) := by
    dsimp only [Internal.mkApiM, Internal.atomicWriteBytesImplM, StateT.run]
    rw [hValidTarget]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_false_of_ne hNeRoot]
    dsimp only [Bind.bind, StateT.bind, StateT.run]
    rw [show (vfsOps.stat false ("/" ++ child) s₀) = (.ok (vfsToStat ndO), s₀) from hStatPath]
    dsimp only [Internal.atomicWriteSiblingM, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [show ((vfsToStat ndO).kind == .dir) = false from by cases hkk : (vfsToStat ndO).kind <;> first | exact absurd hkk hKindPath | rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold StateT.bind
    rw [show vfsOps.monotonicNonce s₀ = (s₀.nonce, sNonce) from rfl]
    rw [hParName.1, hParName.2]
    dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, Option.getD]
    rw [show "/" = ("/" : String) from rfl]
    rw [show Internal.join "/" (toString "." ++ toString child ++ toString ".tmp." ++ toString s₀.nonce) = tmpPath from hTmpJoin]
    rw [show (vfsOps.createFileNew tmpPath newBytes sNonce) = _ from hCreateErr]
    rfl
  have hTmpSNonce : ((vfsOps.stat false tmpPath).run sNonce).1.isOk = true := by
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hTmpExists ⊢
    exact hTmpExists
  dsimp only
  rw [hStep]
  dsimp only [assert]
  exact ⟨⟨_, rfl, rfl⟩, hOrig, hVictim, hTmpSNonce, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget`. -/
theorem reach_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget :
    CanReach (test_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget Internal.mkApiM vfsOps) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun k =>
        if k == "f" then some (.file (ByteArray.mk #[1]) 0o644)
        else if k == "v" then some (.file (ByteArray.mk #[2]) 0o644)
        else if k == ".f.tmp.0" then some (.symlink "/v" 0o777)
        else none)
      keys := ["/f", "/v", "/.f.tmp.0"], cwd := "/", nonce := 0 }
  have hTmpStat : ((vfsOps.stat false ("/." ++ "f" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = true := by
    have hEq := vfsOps_stat_dir755_child_some st ".f.tmp.0" (.symlink "/v" 0o777) (by decide) rfl rfl
    have hPath : ("/." ++ "f" ++ ".tmp." ++ toString st.nonce) = "/" ++ ".f.tmp.0" := by decide
    dsimp only [vfsOps, StateT.run] at hEq ⊢
    rw [hPath, hEq]
    rfl
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hF := vfsReadBytes_root_child_ok st "f" (ByteArray.mk #[1]) 0o755 0o644 (by decide) (by decide) rfl (by decide) rfl
  have hV := vfsReadBytes_root_child_ok st "v" (ByteArray.mk #[2]) 0o755 0o644 (by decide) (by decide) rfl (by decide) rfl
  exact ⟨st, "f", "/v", ByteArray.mk #[9], ByteArray.mk #[1], ByteArray.mk #[2],
    by decide, hRoot, hTmpStat, hF, hV,
    proof_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget st "f" "/v"
      (ByteArray.mk #[9]) (ByteArray.mk #[1]) (ByteArray.mk #[2])
      (by decide) hRoot hTmpStat hF hV⟩

/-- Proof of `test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget :
    AllPass (test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget Internal.mkApiM vfsOps) := by
  intro s₀ child newBytes origBytes renameErr hChild hRoot hTmpMissing hOrig
  have hChildValid := isSingleValidName_validFileName child hChild
  have hChS : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true := hChild
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hChS
  have hNulChild : Char.ofNat 0 ∉ child.toList := hChS.1.1.2
  let tmpName := "." ++ child ++ ".tmp." ++ toString s₀.nonce
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString s₀.nonce
  have hTmpValid : Internal.validFileName tmpName = true := validFileName_tmpSibling child s₀.nonce hChildValid
  have hTmpNotAbs : Internal.isAbsolute tmpName = false :=
    isAbsolute_false_dotPrefix (child ++ ".tmp." ++ toString s₀.nonce)
  have hTmpEq : "/" ++ tmpName = tmpPath := by
    apply String.ext_iff.mpr
    simp [tmpName, tmpPath, String.toList_append, List.append_assoc,
      show "/".toList = ['/'] by decide, show "/.".toList = ['/', '.'] by decide, show ".".toList = ['.'] by decide]
  have hTmpJoin : Internal.join "/" tmpName = tmpPath := by
    rw [join_slash_of_not_abs tmpName hTmpNotAbs, hTmpEq]
  have hTmpRaw : isValidRawPath tmpPath = true := isValidRawPath_tmpSibling child s₀.nonce hChild
  have hValidTarget : Internal.isValidAtomicTargetPath ("/" ++ child) = true :=
    isValidAtomicTargetPath_pfx_slash_single "" child (by simp) hChild
  have hNeRoot : "/" ++ child ≠ "/" := by
    intro heq
    have hL := congrArg (fun x : String => x.toList.length) heq
    have hL1 := validFileName_charList child hChildValid
    have hNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
    rw [String.toList_append, show "/".toList = ['/'] by decide] at hL
    cases hC : child.toList with
    | nil => exact hNeNil hC
    | cons _ _ => simp [hC] at hL
  rcases hRoot with ⟨stR, hRs, hRk, hRw, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hRexec : ((stR.mode / 64) % 2 == 0) = false := by simp [hRx]
  have ⟨canonO, ndO, hResO, hNotDirO, hRawO⟩ := vfsReadBytes_not_none_or_dir s₀ ("/" ++ child) origBytes hOrig
  have hStatPath : (vfsOps.stat false ("/" ++ child)).run s₀ = (.ok (vfsToStat ndO), s₀) := by
    dsimp only [vfsOps, vfsStatPure, StateT.run]; rw [hResO]
  have hKindPath : (vfsToStat ndO).kind ≠ .dir := by
    cases ndO with
    | dir m => exact absurd rfl (hNotDirO m)
    | file _ _ => intro h; cases h
    | symlink _ _ => intro h; cases h
  have hTmpNone : s₀.nodes tmpPath = none := by
    have hEq := vfsStat_root_child_isOk_false s₀ tmpName hTmpValid
      (by rw [hTmpEq]; exact hTmpRaw) ⟨stR, hRs, hRk, hRx⟩
      (by rw [hTmpEq]; exact hTmpMissing)
    rw [← hTmpEq]; exact hEq
  let sNonce : VfsState := { s₀ with nonce := s₀.nonce + 1 }
  let tr1 := vfsTreeSet s₀.tree (vfsSplitSegs tmpPath) (some (.file newBytes 0o644))
  let sAfterCreate : VfsState := { sNonce with tree := tr1, keys := tmpPath :: s₀.keys }
  have ⟨hCanonT, hSplitT⟩ := vfsChildPath_valid "/" tmpName (by decide) hTmpValid
  have hCT : vfsChildPath "/" tmpName = tmpPath := by
    rw [show vfsChildPath "/" tmpName = "/" ++ tmpName from by simp [vfsChildPath], hTmpEq]
  rw [hCT] at hCanonT hSplitT
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitT
  have hCreateOk : vfsCreateFileNewPure sNonce tmpPath newBytes = (.ok (), sAfterCreate) := by
    unfold vfsCreateFileNewPure
    rw [show sNonce.nodes = s₀.nodes from rfl, show sNonce.cwd = s₀.cwd from rfl, hTmpRaw]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      vfsAbsNorm_canon s₀.cwd tmpPath hCanonT,
      hSplitT]
    unfold vfsResolveSegs
    rw [hRootNd]; dsimp only; rw [hRexec, hCT]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [hTmpNone]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show Internal.splitLastAux [tmpName] [] = some ([], tmpName) from rfl]
    dsimp only
    rw [show ((stR.mode / 128) % 2 == 0 || (stR.mode / 64) % 2 == 0) = false from by simp [hRw, hRx]]
    simp only [Bool.false_eq_true, ↓reduceIte, tr1, sAfterCreate, sNonce]
    rfl
  have hNodes1 : sAfterCreate.nodes = fun k => if k == tmpPath then some (.file newBytes 0o644) else s₀.nodes k := by
    change vfsTreeNodes tr1 = _
    have hLeaf := vfsTreeNodes_set_leaf s₀.tree "/" tmpName (some (.file newBytes 0o644))
      (by decide) hTmpValid ⟨stR.mode, hRootNd⟩
      (fun dm h => by change s₀.nodes tmpPath = _ at h; rw [hTmpNone] at h; cases h)
      (fun dm ch h => by cases h)
    dsimp only [Option.map, vfsTreeTopNode] at hLeaf
    rw [hCT] at hLeaf
    exact hLeaf
  have hRootNeTmp : "/" ≠ tmpPath := by
    intro heq
    have := congrArg vfsSplitSegs heq
    rw [hSplitT, show vfsSplitSegs "/" = [] by decide] at this
    simp at this
  have hRoot1 : sAfterCreate.nodes "/" = some (.dir stR.mode) := by
    rw [hNodes1]; dsimp only; rw [beq_false_of_ne hRootNeTmp]; exact hRootNd
  let sFinal : VfsState := { sAfterCreate with tree := vfsTreeSet tr1 (vfsSplitSegs tmpPath) none }
  have hUnlink : (vfsOps.unlinkFile tmpPath).run sAfterCreate = (.ok (), sFinal) := by
    dsimp only [vfsOps, StateT.run]
    rw [vfsAbsNorm_canon sAfterCreate.cwd tmpPath hCanonT, hSplitT]
    unfold vfsResolveSegs
    rw [hRoot1]; dsimp only; rw [hRexec, hCT]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show sAfterCreate.nodes tmpPath = some (.file newBytes 0o644) from by rw [hNodes1]; simp]
  have hNodesFinal : sFinal.nodes = s₀.nodes := by
    have hUn : vfsTreeNodes (vfsTreeSet tr1 (vfsSplitSegs tmpPath) none) =
        fun k => if k == tmpPath then none else sAfterCreate.nodes k := by
      have hLeaf := vfsTreeNodes_set_leaf tr1 "/" tmpName none
        (by decide) hTmpValid ⟨stR.mode, by change sAfterCreate.nodes "/" = _; exact hRoot1⟩
        (fun dm h => by change sAfterCreate.nodes tmpPath = _ at h; rw [hNodes1] at h; simp at h)
        (fun dm ch h => by cases h)
      dsimp only [Option.map] at hLeaf
      rw [hCT] at hLeaf
      exact hLeaf
    change vfsTreeNodes (vfsTreeSet tr1 (vfsSplitSegs tmpPath) none) = s₀.nodes
    rw [hUn]
    funext k
    rw [hNodes1]
    by_cases hk : k = tmpPath
    · subst hk; simp [hTmpNone]
    · simp [beq_false_of_ne hk]
  have hParName := parent_name_slash_child child hChildValid
  have hStep : ((Internal.mkApiM { vfsOps with rename := fun _ _ => pure (.error renameErr) }).atomicWriteBytes ("/" ++ child) newBytes).run s₀ =
      (.error renameErr, sFinal) := by
    dsimp only [Internal.mkApiM, Internal.atomicWriteBytesImplM, StateT.run]
    rw [hValidTarget]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_false_of_ne hNeRoot]
    dsimp only [Bind.bind, StateT.bind, StateT.run]
    rw [show vfsOps.stat false ("/" ++ child) s₀ = (.ok (vfsToStat ndO), s₀) from hStatPath]
    dsimp only [Internal.atomicWriteSiblingM, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
    rw [show ((vfsToStat ndO).kind == .dir) = false from by cases hkk : (vfsToStat ndO).kind <;> first | exact absurd hkk hKindPath | rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold StateT.bind
    rw [show vfsOps.monotonicNonce s₀ = (s₀.nonce, sNonce) from rfl]
    rw [hParName.1, hParName.2]
    dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, Option.getD]
    rw [show Internal.join "/" (toString "." ++ toString child ++ toString ".tmp." ++ toString s₀.nonce) = tmpPath from hTmpJoin]
    rw [show vfsOps.createFileNew tmpPath newBytes sNonce = (.ok (), sAfterCreate) from hCreateOk]
    dsimp only
    rw [show (vfsOps.unlinkFile tmpPath sAfterCreate).snd = sFinal from congrArg Prod.snd hUnlink]
  have hTmpFinal : ((vfsOps.stat false tmpPath).run sFinal).1.isOk = false := by
    dsimp only [vfsOps, StateT.run] at hTmpMissing ⊢
    have hStatEq : vfsStatPure sFinal false tmpPath = vfsStatPure s₀ false tmpPath := by
      unfold vfsStatPure
      rw [show sFinal.cwd = s₀.cwd from rfl, hNodesFinal]
    rw [hStatEq]
    dsimp only [tmpPath]
    exact hTmpMissing
  have hOrigFinal : ((vfsOps.readBytes ("/" ++ child)).run sFinal).1 = .ok origBytes := by
    dsimp only [vfsOps, StateT.run] at hOrig ⊢
    have hReadEq : vfsReadBytesPure sFinal ("/" ++ child) = vfsReadBytesPure s₀ ("/" ++ child) := by
      unfold vfsReadBytesPure
      rw [show sFinal.cwd = s₀.cwd from rfl, hNodesFinal]
    rw [hReadEq]
    exact hOrig
  dsimp only
  rw [hStep]
  dsimp only [assert]
  exact ⟨rfl, hTmpFinal, hOrigFinal, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget`. -/
theorem reach_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget :
    CanReach (test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget Internal.mkApiM vfsOps) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun k => if k == "f" then some (.file (ByteArray.mk #[1]) 0o644) else none)
      keys := ["/f"], cwd := "/", nonce := 0 }
  let err : FsError := { kind := .ioError, path := some "/f", message := "rename failed" }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hTmp : ((vfsOps.stat false ("/." ++ "f" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = false := by
    have hEq := vfsOps_stat_dir755_child_none st ".f.tmp.0" (by decide) rfl rfl
    have hPath : ("/." ++ "f" ++ ".tmp." ++ toString st.nonce) = "/" ++ ".f.tmp.0" := by decide
    dsimp only [vfsOps, StateT.run] at hEq ⊢
    rw [hPath, hEq]
    rfl
  have hOrig := vfsReadBytes_root_child_ok st "f" (ByteArray.mk #[1]) 0o755 0o644 (by decide) (by decide) rfl (by decide) rfl
  exact ⟨st, "f", ByteArray.mk #[9], ByteArray.mk #[1], err,
    by decide, hRoot, hTmp, hOrig,
    proof_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget st "f"
      (ByteArray.mk #[9]) (ByteArray.mk #[1]) err
      (by decide) hRoot hTmp hOrig⟩

/-- Proof of `test_fs_vfs_atomicWriteText_writesAtomically` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteText_writesAtomically :
    AllPass (test_fs_vfs_atomicWriteText_writesAtomically Internal.mkApiM vfsOps) := by
  intro s₀ child content hChild hRoot hTmpMissing hTarget
  rcases atomicWriteBytes_root_child_ok s₀ child content.toUTF8 hChild hRoot hTmpMissing hTarget with
    ⟨s₁, hStep, _, _, hNodes₁⟩
  have hStepText : ((Internal.mkApiM vfsOps).atomicWriteText ("/" ++ child) content).run s₀ = (.ok (), s₁) := by
    rw [atomicWriteText_eq_atomicWriteBytes]; exact hStep
  have hChildValid := isSingleValidName_validFileName child hChild
  have hChS : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true := hChild
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hChS
  have hNulChild : Char.ofNat 0 ∉ child.toList := hChS.1.1.2
  let tmpName := "." ++ child ++ ".tmp." ++ toString s₀.nonce
  let tmpPath := "/." ++ child ++ ".tmp." ++ toString s₀.nonce
  have hTmpValid : Internal.validFileName tmpName = true := validFileName_tmpSibling child s₀.nonce hChildValid
  have hTmpRaw : isValidRawPath tmpPath = true := isValidRawPath_tmpSibling child s₀.nonce hChild
  have hPathRaw : isValidRawPath ("/" ++ child) = true := isValidRawPath_of_singleValid child hChild
  rcases hRoot with ⟨stR, hRs, hRk, hRw, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hTmpEq : "/" ++ tmpName = tmpPath := by
    apply String.ext_iff.mpr
    simp [tmpName, tmpPath, String.toList_append, List.append_assoc,
      show "/.".toList = ['/', '.'] by decide, show "/".toList = ['/'] by decide, show ".".toList = ['.'] by decide]
  have hRootNePath : "/" ≠ "/" ++ child := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" child (by decide) hChildValid).2
    have hC : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC] at hSp; rw [hSp, show vfsSplitSegs "/" = [] by decide] at this; simp at this
  have hRootNeTmp : "/" ≠ tmpPath := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" tmpName (by decide) hTmpValid).2
    have hC : vfsChildPath "/" tmpName = tmpPath := by simp [vfsChildPath, hTmpEq]
    rw [hC] at hSp; rw [hSp, show vfsSplitSegs "/" = [] by decide] at this; simp at this
  have hTmpNePath : tmpPath ≠ "/" ++ child := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp1 := (vfsChildPath_valid "/" tmpName (by decide) hTmpValid).2
    have hC1 : vfsChildPath "/" tmpName = tmpPath := by simp [vfsChildPath, hTmpEq]
    rw [hC1] at hSp1
    have hSp2 := (vfsChildPath_valid "/" child (by decide) hChildValid).2
    have hC2 : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC2] at hSp2
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSp1 hSp2
    rw [hSp1, hSp2] at this
    simp only [List.cons.injEq, and_true] at this
    exact tmpSibling_ne_child child s₀.nonce this
  have hRoot₁ : s₁.nodes "/" = some (.dir stR.mode) := by
    rw [hNodes₁]; dsimp only
    rw [beq_false_of_ne hRootNePath, beq_false_of_ne hRootNeTmp]; exact hRootNd
  have hFile₁ : s₁.nodes ("/" ++ child) = some (.file content.toUTF8 0o644) := by
    rw [hNodes₁]; simp
  have hTmpNone₁ : s₁.nodes tmpPath = none := by
    rw [hNodes₁]; dsimp only
    rw [beq_false_of_ne hTmpNePath]; simp [tmpPath]
  have hReadB₁ : (((Internal.mkApiM vfsOps).readBytes ("/" ++ child)).run s₁).1 = .ok content.toUTF8 := by
    change ((vfsOps.readBytes ("/" ++ child)).run s₁).1 = .ok content.toUTF8
    exact vfsReadBytes_root_child_ok s₁ child content.toUTF8 stR.mode 0o644 hChildValid hPathRaw hRoot₁ hRx hFile₁
  have hReadT₁ : (((Internal.mkApiM vfsOps).readText ("/" ++ child)).run s₁).1 = .ok content := by
    dsimp only [Internal.mkApiM, Internal.readTextImplM, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
    have hRb : vfsOps.readBytes ("/" ++ child) s₁ = (.ok content.toUTF8, s₁) := by
      dsimp only [vfsOps, StateT.run] at hReadB₁ ⊢
      exact Prod.ext hReadB₁ rfl
    rw [hRb]
    dsimp only
    rw [show String.fromUTF8? content.toUTF8 = some content from fromUTF8?_toUTF8 content]
    rfl
  have hTmpNotOk₁ : ((vfsOps.stat false tmpPath).run s₁).1.isOk = false := by
    have ⟨hCanonT, hSplitT⟩ := vfsChildPath_valid "/" tmpName (by decide) hTmpValid
    have hC : vfsChildPath "/" tmpName = tmpPath := by
      rw [show vfsChildPath "/" tmpName = "/" ++ tmpName from by simp [vfsChildPath], hTmpEq]
    rw [hC] at hCanonT hSplitT
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitT
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [vfsAbsNorm_canon s₁.cwd tmpPath hCanonT, hSplitT]
    unfold vfsResolveSegs
    rw [hRoot₁]; dsimp only
    rw [show ((stR.mode / 64) % 2 == 0) = false from by simp [hRx], hC]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [hTmpNone₁]; rfl
  dsimp only
  rw [hStepText]
  dsimp only [assert]
  exact ⟨rfl, hReadB₁, hReadT₁, hTmpNotOk₁, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteText_writesAtomically`. -/
theorem reach_fs_vfs_atomicWriteText_writesAtomically :
    CanReach (test_fs_vfs_atomicWriteText_writesAtomically Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hTmp : ((vfsOps.stat false ("/." ++ "hello.txt" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = false := by
    rw [show "/." ++ "hello.txt" ++ ".tmp." ++ toString st.nonce = "/" ++ ".hello.txt.tmp.0" from by decide]
    rw [vfsOps_stat_dir755_child_none st ".hello.txt.tmp.0" (by decide) rfl rfl]
    rfl
  have hMiss : ∃ e, ((vfsOps.stat false ("/" ++ "hello.txt")).run st).1 = .error e ∧ e.kind = .notFound :=
    ⟨_, vfsOps_stat_dir755_child_none st "hello.txt" (by decide) rfl rfl, rfl⟩
  exact ⟨st, "hello.txt", "world", by decide, hRoot, hTmp, Or.inl hMiss,
    proof_fs_vfs_atomicWriteText_writesAtomically st "hello.txt" "world"
      (by decide) hRoot hTmp (Or.inl hMiss)⟩

/-- Proof of `test_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget :
    AllPass (test_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget Internal.mkApiM vfsOps) := by
  intro s₀ child victimPath newText origBytes victimBytes hChild hRoot hTmpExists hOrig hVictim
  have hB := proof_fs_vfs_atomicWriteBytes_rejectsPrePlantedTmpAndPreservesTarget
    s₀ child victimPath newText.toUTF8 origBytes victimBytes hChild hRoot hTmpExists hOrig hVictim
  simpa [atomicWriteText_eq_atomicWriteBytes] using hB

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget`. -/
theorem reach_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget :
    CanReach (test_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget Internal.mkApiM vfsOps) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun k =>
        if k == "f" then some (.file (ByteArray.mk #[1]) 0o644)
        else if k == "v" then some (.file (ByteArray.mk #[2]) 0o644)
        else if k == ".f.tmp.0" then some (.symlink "/v" 0o777)
        else none)
      keys := ["/f", "/v", "/.f.tmp.0"], cwd := "/", nonce := 0 }
  have hTmpStat : ((vfsOps.stat false ("/." ++ "f" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = true := by
    have hEq := vfsOps_stat_dir755_child_some st ".f.tmp.0" (.symlink "/v" 0o777) (by decide) rfl rfl
    have hPath : ("/." ++ "f" ++ ".tmp." ++ toString st.nonce) = "/" ++ ".f.tmp.0" := by decide
    dsimp only [vfsOps, StateT.run] at hEq ⊢
    rw [hPath, hEq]
    rfl
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hF := vfsReadBytes_root_child_ok st "f" (ByteArray.mk #[1]) 0o755 0o644 (by decide) (by decide) rfl (by decide) rfl
  have hV := vfsReadBytes_root_child_ok st "v" (ByteArray.mk #[2]) 0o755 0o644 (by decide) (by decide) rfl (by decide) rfl
  exact ⟨st, "f", "/v", "new", ByteArray.mk #[1], ByteArray.mk #[2],
    by decide, hRoot, hTmpStat, hF, hV,
    proof_fs_vfs_atomicWriteText_rejectsPrePlantedTmpAndPreservesTarget st "f" "/v" "new"
      (ByteArray.mk #[1]) (ByteArray.mk #[2])
      (by decide) hRoot hTmpStat hF hV⟩

/-- Proof of `test_fs_vfs_atomicWriteBytes_invalidPathRejected` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_invalidPathRejected :
    AllPass (test_fs_vfs_atomicWriteBytes_invalidPathRejected Internal.mkApiM vfsOps) := by
  intro s₀ path bytes hInvalid
  have hInv : Internal.isValidAtomicTargetPath path = false := hInvalid
  dsimp only [Internal.mkApiM, Internal.atomicWriteBytesImplM, StateT.run, Pure.pure, StateT.pure]
  rw [hInv]
  exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_invalidPathRejected`. -/
theorem reach_fs_vfs_atomicWriteBytes_invalidPathRejected :
    CanReach (test_fs_vfs_atomicWriteBytes_invalidPathRejected Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  exact ⟨st, "/.", ByteArray.empty, by decide,
    proof_fs_vfs_atomicWriteBytes_invalidPathRejected st "/." ByteArray.empty (by decide)⟩

/-- Proof of `test_fs_vfs_atomicWriteText_invalidPathRejected` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteText_invalidPathRejected :
    AllPass (test_fs_vfs_atomicWriteText_invalidPathRejected Internal.mkApiM vfsOps) := by
  intro s₀ path content hInvalid
  simpa [atomicWriteText_eq_atomicWriteBytes] using
    proof_fs_vfs_atomicWriteBytes_invalidPathRejected s₀ path content.toUTF8 hInvalid

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteText_invalidPathRejected`. -/
theorem reach_fs_vfs_atomicWriteText_invalidPathRejected :
    CanReach (test_fs_vfs_atomicWriteText_invalidPathRejected Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  exact ⟨st, "..", "x", by decide,
    proof_fs_vfs_atomicWriteText_invalidPathRejected st ".." "x" (by decide)⟩

/-- Proof of `test_fs_vfs_atomicWriteBytes_dirRejected` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_dirRejected :
    AllPass (test_fs_vfs_atomicWriteBytes_dirRejected Internal.mkApiM vfsOps) := by
  intro s₀ path bytes hValid hDir
  have hV : Internal.isValidAtomicTargetPath path = true := hValid
  dsimp only [Internal.mkApiM, Internal.atomicWriteBytesImplM, StateT.run, Pure.pure, StateT.pure]
  rw [hV]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases hDir with rfl | ⟨st, hSt, hK⟩
  · rw [show ("/" == "/") = true from by decide]
    simp only [↓reduceIte]
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
  · by_cases hR : path = "/"
    · subst hR
      rw [show ("/" == "/") = true from by decide]
      simp only [↓reduceIte]
      exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
    · rw [beq_false_of_ne hR]
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      dsimp only [vfsOps, StateT.run] at hSt ⊢
      rw [hSt]
      dsimp only
      rw [hK, show (Raw.EntryKind.dir == .dir) = true from by decide]
      simp only [↓reduceIte]
      exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_dirRejected`. -/
theorem reach_fs_vfs_atomicWriteBytes_dirRejected :
    CanReach (test_fs_vfs_atomicWriteBytes_dirRejected Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  exact ⟨st, "/", ByteArray.empty, by decide, Or.inl rfl,
    proof_fs_vfs_atomicWriteBytes_dirRejected st "/" ByteArray.empty (by decide) (Or.inl rfl)⟩

/-- Proof of `test_fs_vfs_atomicWriteText_dirRejected` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteText_dirRejected :
    AllPass (test_fs_vfs_atomicWriteText_dirRejected Internal.mkApiM vfsOps) := by
  intro s₀ path content hValid hDir
  simpa [atomicWriteText_eq_atomicWriteBytes] using
    proof_fs_vfs_atomicWriteBytes_dirRejected s₀ path content.toUTF8 hValid hDir

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteText_dirRejected`. -/
theorem reach_fs_vfs_atomicWriteText_dirRejected :
    CanReach (test_fs_vfs_atomicWriteText_dirRejected Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  exact ⟨st, "/", "x", by decide, Or.inl rfl,
    proof_fs_vfs_atomicWriteText_dirRejected st "/" "x" (by decide) (Or.inl rfl)⟩

/-- Proof of `test_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated :
    AllPass (test_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated Internal.mkApiM vfsOps) := by
  intro s₀ path bytes ⟨hValid, hNeRoot⟩ ⟨stErr, hErr, hNotNf⟩
  have hV : Internal.isValidAtomicTargetPath path = true := hValid
  dsimp only [Internal.mkApiM, Internal.atomicWriteBytesImplM, StateT.run, Pure.pure, StateT.pure]
  rw [hV, beq_false_of_ne hNeRoot]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure]
  dsimp only [vfsOps, StateT.run] at hErr ⊢
  rw [hErr]
  dsimp only
  have hNeq : (stErr.kind != .notFound) = true := by
    cases hsk : stErr.kind <;> first | exact absurd hsk hNotNf | decide
  rw [hNeq]
  exact ⟨⟨⟨stErr, stErr, rfl, rfl, rfl⟩, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated`. -/
theorem reach_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated :
    CanReach (test_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o644 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hPerm : ∃ stErr, ((vfsOps.stat false "/missing").run st).1 = .error stErr ∧ stErr.kind ≠ .notFound := by
    refine ⟨{ kind := .permissionDenied, path := some "/", message := "permission denied: /" }, ?_, by decide⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [vfsAbsNorm_canon st.cwd "/missing" (by decide), show vfsSplitSegs "/missing" = ["missing"] from by decide]
    unfold vfsResolveSegs
    rw [show st.nodes "/" = some (.dir 0o644) from rfl]
    dsimp only
    rw [show ((0o644 / 64) % 2 == 0) = true from by decide]
    rfl
  exact ⟨st, "/missing", ByteArray.empty, ⟨by decide, by decide⟩, hPerm,
    proof_fs_vfs_atomicWriteBytes_upfrontStatErrorPropagated st "/missing" ByteArray.empty
      ⟨by decide, by decide⟩ hPerm⟩

/-- Proof of `test_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically :
    AllPass (test_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically Internal.mkApiM vfsOps) := by
  intro s₀ child bytes hChild hRoot hTmpMissing ⟨lst, hLstOk, hLstSym⟩
  have hSymNeDir : lst.kind ≠ .dir := by rw [hLstSym]; decide
  rcases proof_fs_vfs_atomicWriteBytes_writesAtomically s₀ child bytes hChild hRoot hTmpMissing
      (Or.inr ⟨lst, hLstOk, hSymNeDir⟩) with
    ⟨hRes, hRead, hLstat, hTmp, _⟩
  exact ⟨hRes, hLstat, hRead, hTmp, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically`. -/
theorem reach_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically :
    CanReach (test_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically Internal.mkApiM vfsOps) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun k => if k == "s" then some (.symlink "/tgt" 0o777) else none)
      keys := ["/s"], cwd := "/", nonce := 0 }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hTmp : ((vfsOps.stat false ("/." ++ "s" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = false := by
    rw [show "/." ++ "s" ++ ".tmp." ++ toString st.nonce = "/" ++ ".s.tmp.0" from by decide]
    rw [vfsOps_stat_dir755_child_none st ".s.tmp.0" (by decide) rfl rfl]
    rfl
  have hSym : ∃ lst, ((vfsOps.stat false ("/" ++ "s")).run st).1 = .ok lst ∧ lst.kind = .symlink :=
    ⟨vfsToStat (.symlink "/tgt" 0o777),
      vfsOps_stat_dir755_child_some st "s" (.symlink "/tgt" 0o777) (by decide) rfl rfl, rfl⟩
  exact ⟨st, "s", ByteArray.mk #[5, 6], by decide, hRoot, hTmp, hSym,
    proof_fs_vfs_atomicWriteBytes_replacesSymlinkAtomically st "s" (ByteArray.mk #[5, 6])
      (by decide) hRoot hTmp hSym⟩

private theorem nestedParentAndRelative_step0 (s₀ : VfsState) (dirName child : String) (bytes : ByteArray)
    (hCond : (!dirName.toList.isEmpty && !('/' ∈ dirName.toList) && !(Char.ofNat 0 ∈ dirName.toList) && dirName != "." && dirName != "..") = true ∧
      (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true)
    (hDirStat : ∃ stDir, ((vfsOps.stat false ("/" ++ dirName)).run s₀).1 = .ok stDir ∧ stDir.kind = .dir ∧
      (stDir.mode / 128) % 2 = 1 ∧ (stDir.mode / 64) % 2 = 1)
    (hTmp0Missing : ((vfsOps.stat false ("/" ++ dirName ++ "/." ++ child ++ ".tmp." ++ toString (vfsOps.monotonicNonce.run s₀).1)).run s₀).1.isOk = false)
    (hPath0Nf : ∃ e, ((vfsOps.stat false ("/" ++ dirName ++ "/" ++ child)).run s₀).1 = .error e ∧ e.kind = .notFound) :
    ∃ s₁,
      ((Internal.mkApiM vfsOps).atomicWriteBytes ("/" ++ dirName ++ "/" ++ child) bytes).run s₀ = (.ok (), s₁) ∧
      (((Internal.mkApiM vfsOps).readBytes ("/" ++ dirName ++ "/" ++ child)).run s₁).1 = .ok bytes ∧
      ((vfsOps.stat false ("/" ++ dirName ++ "/." ++ child ++ ".tmp." ++ toString s₀.nonce)).run s₁).1.isOk = false ∧
      s₁.cwd = s₀.cwd ∧ s₁.nonce = s₀.nonce + 1 ∧
      s₁.nodes = (fun k => if k == ("/" ++ dirName ++ "/" ++ child) then some (.file bytes 0o644)
        else if k == ("/" ++ dirName ++ "/." ++ child ++ ".tmp." ++ toString s₀.nonce) then none else s₀.nodes k) := by
  rcases hCond with ⟨hDirS, hChildS⟩
  have hDirValid := isSingleValidName_validFileName dirName hDirS
  have hChildValid := isSingleValidName_validFileName child hChildS
  have hDirS' : (!dirName.toList.isEmpty && !('/' ∈ dirName.toList) && !(Char.ofNat 0 ∈ dirName.toList) && dirName != "." && dirName != "..") = true := hDirS
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hDirS'
  have hNulDir : Char.ofNat 0 ∉ dirName.toList := hDirS'.1.1.2
  have hChildS' : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true := hChildS
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hChildS'
  have hNulChild : Char.ofNat 0 ∉ child.toList := hChildS'.1.1.2
  let parDir := "/" ++ dirName
  let nestedPath := "/" ++ dirName ++ "/" ++ child
  let tmp0Name := "." ++ child ++ ".tmp." ++ toString s₀.nonce
  let nestedTmp := "/" ++ dirName ++ "/." ++ child ++ ".tmp." ++ toString s₀.nonce
  have hTmp0Valid : Internal.validFileName tmp0Name = true := validFileName_tmpSibling child s₀.nonce hChildValid
  have hTmp0Nul : Char.ofNat 0 ∉ tmp0Name.toList := by
    have hNoNulNat : Char.ofNat 0 ∉ (toString s₀.nonce).toList := by
      intro hm
      have hDig : Char.ofNat 0 ∈ Nat.toDigits 10 s₀.nonce := by simpa [toString, Nat.repr] using hm
      unfold Nat.toDigits at hDig
      rcases toDigitsCore_mem_digit_or_acc (s₀.nonce + 1) 10 s₀.nonce [] (Char.ofNat 0) rfl hDig with hc | ⟨d, hd, hEq⟩
      · simp at hc
      · rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
        all_goals first | (simp [Nat.digitChar] at hEq; done) | omega
    simp only [tmp0Name, String.toList_append, List.mem_append,
      show ".".toList = ['.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide]
    rintro (((hm | hm) | hm) | hm)
    · simp at hm
    · exact hNulChild hm
    · simp at hm
    · exact hNoNulNat hm
  have hNestedValid : Internal.isValidAtomicTargetPath nestedPath = true := by
    have hPfxNul : Char.ofNat 0 ∉ ("/" ++ dirName).toList := by
      intro hm
      rw [String.toList_append, show "/".toList = ['/'] by decide, List.mem_append, List.mem_singleton] at hm
      rcases hm with h | h
      · cases h
      · exact hNulDir h
    simpa [nestedPath, parDir, String.append_assoc] using
      isValidAtomicTargetPath_pfx_slash_single ("/" ++ dirName) child hPfxNul hChildS
  have hNestedNeRoot : nestedPath ≠ "/" := by
    intro heq
    have ⟨_, _, hSp, _⟩ := vfsChildPath_dir_child dirName child hDirValid hChildValid
    have := congrArg vfsSplitSegs heq
    rw [hSp, show vfsSplitSegs "/" = [] by decide] at this
    simp at this
  have hParName0 := parent_name_dir_child dirName child hDirValid hChildValid
  have hTmp0Eq : "/" ++ dirName ++ "/" ++ tmp0Name = nestedTmp := by
    apply String.ext_iff.mpr
    simp [tmp0Name, nestedTmp, String.toList_append, List.append_assoc,
      show "/".toList = ['/'] by decide, show "/.".toList = ['/', '.'] by decide, show ".".toList = ['.'] by decide]
  have hJoin0 : Internal.join ("/" ++ dirName) tmp0Name = nestedTmp := by
    rw [join_slash_dir_of_not_abs dirName tmp0Name hDirValid
      (isAbsolute_false_dotPrefix (child ++ ".tmp." ++ toString s₀.nonce)), hTmp0Eq]
  have hTmp0Raw : isValidRawPath nestedTmp = true := by
    rw [← hTmp0Eq]
    exact isValidRawPath_dir_child dirName tmp0Name hDirS hTmp0Valid hTmp0Nul
  have hPath0Raw : isValidRawPath nestedPath = true := isValidRawPath_dir_child dirName child hDirS hChildValid hNulChild
  have ⟨hParCanon, hParSegs⟩ := vfsChildPath_valid "/" dirName (by decide) hDirValid
  have hSlashDir : vfsChildPath "/" dirName = "/" ++ dirName := by simp [vfsChildPath]
  rw [hSlashDir] at hParCanon hParSegs
  have ⟨hChild0, hCanon0, hSplit0, hAbs0⟩ := vfsChildPath_dir_child dirName child hDirValid hChildValid
  have ⟨hTmpChild0, hTmpCanon0, hTmpSplit0, hTmpAbs0⟩ := vfsChildPath_dir_child dirName tmp0Name hDirValid hTmp0Valid
  rcases hDirStat with ⟨stDir, hDirOk, hDirKind, hDirW, hDirX⟩
  have hDirRaw : isValidRawPath ("/" ++ dirName) = true := isValidRawPath_of_singleValid dirName hDirS
  have hDirResolved : ∃ rm, s₀.nodes "/" = some (.dir rm) ∧ ((rm / 64) % 2 == 0) = false ∧
      s₀.nodes ("/" ++ dirName) = some (.dir stDir.mode) := by
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hDirOk
    rw [vfsAbsNorm_canon s₀.cwd ("/" ++ dirName) hParCanon, hParSegs, show vfsSplitSegs "/" = [] by decide, List.nil_append] at hDirOk
    unfold vfsResolveSegs at hDirOk
    cases hR : s₀.nodes "/" with
    | none => simp [hR] at hDirOk
    | some rnd =>
      cases rnd with
      | file _ _ => simp [hR] at hDirOk
      | symlink tgt m =>
        obtain ⟨e, hErr, _⟩ := vfsResolveSegs_root_symlink_err s₀.nodes tgt m hR 1024 [dirName] false (Or.inl (by simp))
        unfold vfsResolveSegs at hErr
        simp only [hR] at hDirOk hErr
        rw [hErr] at hDirOk
        cases hDirOk
      | dir rm =>
        simp only [hR] at hDirOk
        by_cases he : ((rm / 64) % 2 == 0) = true
        · simp [he] at hDirOk
        · have hef : ((rm / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr he
          simp only [hef, Bool.false_eq_true, ↓reduceIte, hSlashDir] at hDirOk
          unfold vfsResolveSegs at hDirOk
          cases hD : s₀.nodes ("/" ++ dirName) with
          | none => simp [hD] at hDirOk
          | some dnd =>
            cases dnd with
            | file _ _ => simp [hD] at hDirOk; subst hDirOk; simp [vfsToStat] at hDirKind
            | symlink _ _ => simp [hD] at hDirOk; subst hDirOk; simp [vfsToStat] at hDirKind
            | dir dm =>
              simp only [hD, Except.ok.injEq] at hDirOk
              have : stDir.mode = dm := by rw [← hDirOk]; rfl
              exact ⟨rm, rfl, hef, by rw [this]⟩
  rcases hDirResolved with ⟨rm, hRootD, hRootExec, hDirNd⟩
  have hDirRes512 : vfsResolveSegs s₀.nodes "/" [dirName] true 512 = .ok ("/" ++ dirName, .dir stDir.mode) := by
    simp [vfsResolveSegs, hRootD, hRootExec, hSlashDir, hDirNd]
  have hDirExecF : ((stDir.mode / 64) % 2 == 0) = false := by simp [hDirX]
  have hTmp0None : s₀.nodes nestedTmp = none := by
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hTmp0Missing
    rw [show vfsAbsNorm s₀.cwd nestedTmp = nestedTmp from by rw [← hTmp0Eq]; exact hTmpAbs0 s₀.cwd] at hTmp0Missing
    rw [show vfsSplitSegs nestedTmp = [dirName, tmp0Name] from by rw [← hTmp0Eq]; exact hTmpSplit0] at hTmp0Missing
    unfold vfsResolveSegs at hTmp0Missing
    rw [hRootD] at hTmp0Missing; dsimp only at hTmp0Missing
    rw [hRootExec, hSlashDir] at hTmp0Missing; simp only [Bool.false_eq_true, ↓reduceIte] at hTmp0Missing
    unfold vfsResolveSegs at hTmp0Missing
    rw [hDirNd] at hTmp0Missing; dsimp only at hTmp0Missing
    rw [hDirExecF] at hTmp0Missing; simp only [Bool.false_eq_true, ↓reduceIte] at hTmp0Missing
    rw [show vfsChildPath ("/" ++ dirName) tmp0Name = nestedTmp from by rw [hTmpChild0, hTmp0Eq]] at hTmp0Missing
    unfold vfsResolveSegs at hTmp0Missing
    cases hN : s₀.nodes nestedTmp with
    | none => rfl
    | some nd => exfalso; cases nd <;> simp [hN, Except.isOk, Except.toBool] at hTmp0Missing
  have hPerm0 : ((stDir.mode / 128) % 2 == 0 || (stDir.mode / 64) % 2 == 0) = false := by simp [hDirW, hDirX]
  have hStatStep0 : (∃ e, vfsStatPure s₀ false nestedPath = .error e ∧ e.kind = .notFound) ∨
      (∃ st, vfsStatPure s₀ false nestedPath = .ok st ∧ st.kind ≠ .dir) :=
    Or.inl (by simpa [vfsOps, StateT.run] using hPath0Nf)
  have hTmpChild0Eq : vfsChildPath ("/" ++ dirName) tmp0Name = nestedTmp := by rw [hTmpChild0, hTmp0Eq]
  rcases atomicWriteBytes_vfs_step s₀ nestedPath bytes ("/" ++ dirName) child ("/" ++ dirName) [dirName] stDir.mode
      hNestedValid hNestedNeRoot hStatStep0 (by simp [nestedPath, hParName0.1, hParName0.2]) hChildValid
      (by rw [hJoin0]; exact hTmp0Raw) hPath0Raw
      ⟨hParCanon, by rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hParSegs; exact hParSegs⟩
      (by rw [hJoin0, hTmpChild0Eq, ← hTmp0Eq]; exact hTmpAbs0 s₀.cwd)
      (by rw [hChild0]; exact hAbs0 s₀.cwd)
      hDirRes512 hPerm0 (Or.inr ⟨dirName, rm, rfl, rfl, hRootD, hRootExec⟩)
      (by rw [hTmpChild0Eq]; exact hTmp0None)
      (by
        left
        rcases hPath0Nf with ⟨e0, hErr0, hKind0⟩
        dsimp only [vfsOps, vfsStatPure, StateT.run] at hErr0
        rw [hAbs0 s₀.cwd, hSplit0] at hErr0
        unfold vfsResolveSegs at hErr0
        rw [hRootD] at hErr0; dsimp only at hErr0
        rw [hRootExec, hSlashDir] at hErr0; simp only [Bool.false_eq_true, ↓reduceIte] at hErr0
        unfold vfsResolveSegs at hErr0
        rw [hDirNd] at hErr0; dsimp only at hErr0
        rw [hDirExecF, hChild0] at hErr0; simp only [Bool.false_eq_true, ↓reduceIte] at hErr0
        unfold vfsResolveSegs at hErr0
        rw [hChild0]
        cases hN : s₀.nodes ("/" ++ dirName ++ "/" ++ child) with
        | none => exact rfl
        | some nd =>
          exfalso
          cases nd with
          | file _ _ => simp [hN] at hErr0
          | symlink _ _ => simp [hN] at hErr0
          | dir dm => simp [hN] at hErr0) with
    ⟨s₁, hStep0, hCwd1, hNonce1, hNodes1⟩
  have hDirNeNested : "/" ++ dirName ≠ nestedPath := by
    intro heq
    have := congrArg vfsSplitSegs heq
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hParSegs
    rw [hParSegs, hSplit0] at this
    simp at this
  have hDirNeTmp0 : "/" ++ dirName ≠ nestedTmp := by
    intro heq
    have := congrArg vfsSplitSegs heq
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hParSegs
    rw [hParSegs, show vfsSplitSegs nestedTmp = [dirName, tmp0Name] from by rw [← hTmp0Eq]; exact hTmpSplit0] at this
    simp at this
  have hRootNeNested : "/" ≠ nestedPath := hNestedNeRoot.symm
  have hRootNeTmp0 : "/" ≠ nestedTmp := by
    intro heq
    have := congrArg vfsSplitSegs heq
    rw [show vfsSplitSegs "/" = [] by decide,
      show vfsSplitSegs nestedTmp = [dirName, tmp0Name] from by rw [← hTmp0Eq]; exact hTmpSplit0] at this
    simp at this
  have hTmp0NeNested : nestedTmp ≠ nestedPath := by
    intro heq
    have := congrArg vfsSplitSegs heq
    rw [show vfsSplitSegs nestedTmp = [dirName, tmp0Name] from by rw [← hTmp0Eq]; exact hTmpSplit0, hSplit0] at this
    simp only [List.cons.injEq, and_true] at this
    exact tmpSibling_ne_child child s₀.nonce this.2
  have hRoot₁ : s₁.nodes "/" = some (.dir rm) := by
    rw [hNodes1]; dsimp only
    rw [beq_false_of_ne (by rw [hChild0]; exact hRootNeNested),
      beq_false_of_ne (by rw [hTmpChild0Eq]; exact hRootNeTmp0)]
    exact hRootD
  have hDir₁ : s₁.nodes ("/" ++ dirName) = some (.dir stDir.mode) := by
    rw [hNodes1]; dsimp only
    rw [beq_false_of_ne (by rw [hChild0]; exact hDirNeNested),
      beq_false_of_ne (by rw [hTmpChild0Eq]; exact hDirNeTmp0)]
    exact hDirNd
  have hFile₁ : s₁.nodes nestedPath = some (.file bytes 0o644) := by
    rw [hNodes1]; dsimp only
    rw [hChild0]
    dsimp only [nestedPath]
    simp
  have hTmp0None₁ : s₁.nodes nestedTmp = none := by
    rw [hNodes1]; dsimp only
    rw [hTmpChild0Eq, hChild0, beq_false_of_ne (show nestedTmp ≠ "/" ++ dirName ++ "/" ++ child from hTmp0NeNested)]
    simp
  have hRead0 : (((Internal.mkApiM vfsOps).readBytes nestedPath).run s₁).1 = .ok bytes := by
    dsimp only [Internal.mkApiM, vfsOps, vfsReadBytesPure, StateT.run]
    rw [hPath0Raw]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show vfsAbsNorm s₁.cwd nestedPath = "/" ++ dirName ++ "/" ++ child from hAbs0 s₁.cwd, hSplit0]
    unfold vfsResolveSegs; rw [hRoot₁]; dsimp only; rw [hRootExec, hSlashDir]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hDir₁]; dsimp only; rw [hDirExecF, hChild0]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hFile₁]
  have hTmp0NotOk₁ : ((vfsOps.stat false nestedTmp).run s₁).1.isOk = false := by
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show vfsAbsNorm s₁.cwd nestedTmp = nestedTmp from by rw [← hTmp0Eq]; exact hTmpAbs0 s₁.cwd,
      show vfsSplitSegs nestedTmp = [dirName, tmp0Name] from by rw [← hTmp0Eq]; exact hTmpSplit0]
    unfold vfsResolveSegs; rw [hRoot₁]; dsimp only; rw [hRootExec, hSlashDir]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hDir₁]; dsimp only; rw [hDirExecF, hTmpChild0Eq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hTmp0None₁]; rfl
  rw [hChild0, hTmpChild0Eq] at hNodes1
  exact ⟨s₁, hStep0, hRead0, hTmp0NotOk₁, hCwd1, hNonce1, hNodes1⟩

private theorem nestedParentAndRelative_step1 (s₁ : VfsState) (child : String) (bytes : ByteArray)
    (hChildS : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true)
    (hCwdS1 : (vfsOps.cwd.run s₁).1 = .ok "/")
    (hRootS1 : ∃ stRoot, ((vfsOps.stat false "/").run s₁).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hRelTmpMissing : ((vfsOps.stat false ("./." ++ child ++ ".tmp." ++ toString (vfsOps.monotonicNonce.run s₁).1)).run s₁).1.isOk = false)
    (hRelNf : ∃ e, ((vfsOps.stat false child).run s₁).1 = .error e ∧ e.kind = .notFound) :
    ∃ s₂,
      ((Internal.mkApiM vfsOps).atomicWriteBytes child bytes).run s₁ = (.ok (), s₂) ∧
      (((Internal.mkApiM vfsOps).readBytes child).run s₂).1 = .ok bytes ∧
      ((vfsOps.stat false ("./." ++ child ++ ".tmp." ++ toString s₁.nonce)).run s₂).1.isOk = false := by
  have hChildValid := isSingleValidName_validFileName child hChildS
  have hChildS' : (!child.toList.isEmpty && !('/' ∈ child.toList) && !(Char.ofNat 0 ∈ child.toList) && child != "." && child != "..") = true := hChildS
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hChildS'
  have hNulChild : Char.ofNat 0 ∉ child.toList := hChildS'.1.1.2
  have hCwdVal : s₁.cwd = "/" := by
    simpa [vfsOps, StateT.run] using hCwdS1
  let tmp1Name := "." ++ child ++ ".tmp." ++ toString s₁.nonce
  let relTmp := "./." ++ child ++ ".tmp." ++ toString s₁.nonce
  have hTmp1Valid : Internal.validFileName tmp1Name = true := validFileName_tmpSibling child s₁.nonce hChildValid
  have hRelRaw : isValidRawPath child = true := by
    have hNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
    have hLastNotSlash : (child.toList.getLast? == some '/') = false := by
      apply beq_false_of_ne; intro heq
      have : child.toList.reverse.head? = some '/' := by simpa [List.head?_reverse] using heq
      cases hr : child.toList.reverse with
      | nil => simp [hr] at this
      | cons c cs =>
        rw [hr] at this; simp at this; subst this
        exact hChildValid |> validFileName_charList child |>.2.2.1 <| List.mem_reverse.mp (by rw [hr]; simp)
    simp only [isValidRawPath, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨⟨?_, hNulChild⟩, by rw [hLastNotSlash, Bool.and_false]⟩
    cases hC : child.toList with
    | nil => exact absurd hC hNeNil
    | cons _ _ => rfl
  have hRelValid : Internal.isValidAtomicTargetPath child = true := by
    have hNotDotRel : Internal.hasDotFinalSegment child = false := by
      unfold Internal.hasDotFinalSegment
      have hChL := validFileName_charList child hChildValid
      have hNeNil : child.toList ≠ [] := by cases hC : child.toList <;> simp_all
      cases hr : child.toList.reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp hr) hNeNil
      | cons c1 cs1 =>
        cases cs1 with
        | nil =>
          by_cases hc1 : c1 = '.'
          · subst hc1
            have hsEq : child.toList = ['.'] := by simpa using congrArg List.reverse hr
            simp [hsEq] at hChL
          · simp [hc1]
        | cons c2 cs2 =>
          by_cases hc2 : c2 = '/'
          · subst hc2
            exact absurd (List.mem_reverse.mp (by rw [hr]; simp)) hChL.2.2.1
          · by_cases hc1 : c1 = '.'
            · by_cases hc2d : c2 = '.'
              · cases cs2 with
                | nil =>
                  subst hc1 hc2d
                  have hsEq : child.toList = ['.', '.'] := by simpa using congrArg List.reverse hr
                  simp [hsEq] at hChL
                | cons c3 cs3 =>
                  by_cases hc3 : c3 = '/'
                  · subst hc3; exact absurd (List.mem_reverse.mp (by rw [hr]; simp)) hChL.2.2.1
                  · subst hc1 hc2d; simp [hc2, hc3]
              · subst hc1; simp [hc2, hc2d]
            · simp [hc1]
    unfold Internal.isValidAtomicTargetPath
    simp only [Bool.and_eq_true, hNotDotRel, Bool.not_false, and_true]
    exact hRelRaw
  have hRelNeRoot : child ≠ "/" := by
    intro heq
    have hChL := validFileName_charList child hChildValid
    exact hChL.2.2.1 (by rw [heq]; decide)
  have hRelTmpRaw : isValidRawPath relTmp = true := by
    have hNoNulNat : Char.ofNat 0 ∉ (toString s₁.nonce).toList := by
      intro hm
      have hDig : Char.ofNat 0 ∈ Nat.toDigits 10 s₁.nonce := by simpa [toString, Nat.repr] using hm
      unfold Nat.toDigits at hDig
      rcases toDigitsCore_mem_digit_or_acc (s₁.nonce + 1) 10 s₁.nonce [] (Char.ofNat 0) rfl hDig with hc | ⟨d, hd, hEq⟩
      · simp at hc
      · rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
        all_goals first | (simp [Nat.digitChar] at hEq; done) | omega
    have hLastNotSlash : (relTmp.toList.getLast? == some '/') = false := by
      have hApp : relTmp.toList = "./.".toList ++ child.toList ++ ".tmp.".toList ++ (toString s₁.nonce).toList := by
        simp [relTmp, String.toList_append, List.append_assoc]
      have hNatNe : (toString s₁.nonce).toList ≠ [] := by
        simp [toString, Nat.repr]
      have hNoSlNat : '/' ∉ (toString s₁.nonce).toList := slash_not_mem_toString_nat s₁.nonce
      rw [hApp, list_getLast?_append _ (toString s₁.nonce).toList hNatNe]
      apply beq_false_of_ne; intro heq
      have : (toString s₁.nonce).toList.reverse.head? = some '/' := by simpa [List.head?_reverse] using heq
      cases hr : (toString s₁.nonce).toList.reverse with
      | nil => rw [hr] at this; cases this
      | cons c cs =>
        rw [hr] at this; simp at this; subst this
        exact hNoSlNat (List.mem_reverse.mp (by rw [hr]; simp))
    have hNoNulRel : Char.ofNat 0 ∉ relTmp.toList := by
      simp only [relTmp, String.toList_append, List.mem_append,
        show "./.".toList = ['.', '/', '.'] by decide, show ".tmp.".toList = ['.', 't', 'm', 'p', '.'] by decide]
      rintro (((hm | hm) | hm) | hm)
      · simp at hm
      · exact hNulChild hm
      · simp at hm
      · exact hNoNulNat hm
    simp only [isValidRawPath, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨⟨?_, hNoNulRel⟩, by rw [hLastNotSlash, Bool.and_false]⟩
    cases hC : relTmp.toList with
    | nil => simp [relTmp, String.toList_append] at hC
    | cons _ _ => rfl
  have hRelTmpEq : "./" ++ tmp1Name = relTmp := by
    apply String.ext_iff.mpr
    simp [tmp1Name, relTmp, String.toList_append, List.append_assoc,
      show "./".toList = ['.', '/'] by decide, show "./.".toList = ['.', '/', '.'] by decide, show ".".toList = ['.'] by decide]
  have hParName1 := parent_name_bare_child child hChildValid
  have hJoin1 : Internal.join "." tmp1Name = relTmp := by
    rw [join_dot_of_not_abs tmp1Name (isAbsolute_false_dotPrefix (child ++ ".tmp." ++ toString s₁.nonce)), hRelTmpEq]
  rcases hRootS1 with ⟨stR1, hRs1, hRk1, hRw1, hRx1⟩
  have hRootNd1 := vfsStat_root_dir_nodes s₁ stR1 hRs1 hRk1
  have hRelTmpNone : s₁.nodes ("/" ++ tmp1Name) = none := by
    have ⟨_, hSplitT1⟩ := vfsChildPath_valid "/" tmp1Name (by decide) hTmp1Valid
    have hCT1 : vfsChildPath "/" tmp1Name = "/" ++ tmp1Name := by simp [vfsChildPath]
    rw [hCT1] at hSplitT1
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitT1
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hRelTmpMissing
    rw [show "./." ++ child ++ ".tmp." ++ toString s₁.nonce = relTmp from rfl, hCwdVal] at hRelTmpMissing
    rw [← hRelTmpEq, vfsAbsNorm_root_dot_child tmp1Name hTmp1Valid, hSplitT1] at hRelTmpMissing
    unfold vfsResolveSegs at hRelTmpMissing
    rw [hRootNd1] at hRelTmpMissing; dsimp only at hRelTmpMissing
    rw [show ((stR1.mode / 64) % 2 == 0) = false from by simp [hRx1], hCT1] at hRelTmpMissing
    simp only [Bool.false_eq_true, ↓reduceIte] at hRelTmpMissing
    unfold vfsResolveSegs at hRelTmpMissing
    cases hN : s₁.nodes ("/" ++ tmp1Name) with
    | none => rfl
    | some nd => exfalso; cases nd <;> simp [hN, Except.isOk, Except.toBool] at hRelTmpMissing
  have hRelRootRes : vfsResolveSegs s₁.nodes "/" [] true 512 = .ok ("/", .dir stR1.mode) := by
    simp [vfsResolveSegs, hRootNd1]
  have hPerm1 : ((stR1.mode / 128) % 2 == 0 || (stR1.mode / 64) % 2 == 0) = false := by simp [hRw1, hRx1]
  have hStatStep1 : (∃ e, vfsStatPure s₁ false child = .error e ∧ e.kind = .notFound) ∨
      (∃ st, vfsStatPure s₁ false child = .ok st ∧ st.kind ≠ .dir) :=
    Or.inl (by simpa [vfsOps, StateT.run] using hRelNf)
  rcases atomicWriteBytes_vfs_step s₁ child bytes "." child "/" [] stR1.mode
      hRelValid hRelNeRoot hStatStep1 (by simp [hParName1.1, hParName1.2]) hChildValid
      (by rw [hJoin1]; exact hRelTmpRaw) hRelRaw ⟨by decide, by decide⟩
      (by rw [hCwdVal, hJoin1, ← hRelTmpEq]; exact (vfsAbsNorm_root_dot_child tmp1Name hTmp1Valid).trans (by simp [vfsChildPath, tmp1Name]))
      (by rw [hCwdVal]; exact (vfsAbsNorm_root_bare_child child hChildValid).trans (by simp [vfsChildPath]))
      hRelRootRes hPerm1 (Or.inl ⟨rfl, rfl⟩)
      (by
        rw [show vfsChildPath "/" ("." ++ child ++ ".tmp." ++ toString s₁.nonce) = "/" ++ tmp1Name from by simp [vfsChildPath, tmp1Name]]
        exact hRelTmpNone)
      (by
        left
        rcases hRelNf with ⟨e1, hErr1, _⟩
        have ⟨_, hSplitC1⟩ := vfsChildPath_valid "/" child (by decide) hChildValid
        have hC1 : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
        rw [hC1] at hSplitC1
        rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC1
        dsimp only [vfsOps, vfsStatPure, StateT.run] at hErr1
        rw [hCwdVal, vfsAbsNorm_root_bare_child child hChildValid, hSplitC1] at hErr1
        unfold vfsResolveSegs at hErr1
        rw [hRootNd1] at hErr1; dsimp only at hErr1
        rw [show ((stR1.mode / 64) % 2 == 0) = false from by simp [hRx1], hC1] at hErr1
        simp only [Bool.false_eq_true, ↓reduceIte] at hErr1
        unfold vfsResolveSegs at hErr1
        rw [hC1]
        cases hN : s₁.nodes ("/" ++ child) with
        | none => exact rfl
        | some nd => exfalso; cases nd <;> simp [hN] at hErr1) with
    ⟨s₂, hStep1, hCwd2, _, hNodes2⟩
  have hCwd2Val : s₂.cwd = "/" := hCwd2.trans hCwdVal
  have hRootNeC : "/" ≠ "/" ++ child := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" child (by decide) hChildValid).2
    have hC : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC] at hSp; rw [hSp, show vfsSplitSegs "/" = [] by decide] at this; simp at this
  have hRootNeT1 : "/" ≠ "/" ++ tmp1Name := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" tmp1Name (by decide) hTmp1Valid).2
    have hC : vfsChildPath "/" tmp1Name = "/" ++ tmp1Name := by simp [vfsChildPath]
    rw [hC] at hSp; rw [hSp, show vfsSplitSegs "/" = [] by decide] at this; simp at this
  have hT1NeC : "/" ++ tmp1Name ≠ "/" ++ child := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp1 := (vfsChildPath_valid "/" tmp1Name (by decide) hTmp1Valid).2
    have hC1 : vfsChildPath "/" tmp1Name = "/" ++ tmp1Name := by simp [vfsChildPath]
    rw [hC1] at hSp1
    have hSp2 := (vfsChildPath_valid "/" child (by decide) hChildValid).2
    have hC2 : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC2] at hSp2
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSp1 hSp2
    rw [hSp1, hSp2] at this
    simp only [List.cons.injEq, and_true] at this
    exact tmpSibling_ne_child child s₁.nonce this
  have hRoot₂ : s₂.nodes "/" = some (.dir stR1.mode) := by
    rw [hNodes2]; dsimp only
    rw [beq_false_of_ne (by simpa [vfsChildPath] using hRootNeC),
      beq_false_of_ne (by simpa [vfsChildPath, tmp1Name] using hRootNeT1)]
    exact hRootNd1
  have hFile₂ : s₂.nodes ("/" ++ child) = some (.file bytes 0o644) := by
    rw [hNodes2]; simp [vfsChildPath]
  have hT1None₂ : s₂.nodes ("/" ++ tmp1Name) = none := by
    rw [hNodes2]; dsimp only
    simp only [vfsChildPath, show ("/" == "/") = true from rfl, ↓reduceIte]
    rw [beq_false_of_ne hT1NeC]
    simp [tmp1Name]
  have hReadRel : (((Internal.mkApiM vfsOps).readBytes child).run s₂).1 = .ok bytes := by
    have ⟨_, hSplitC1⟩ := vfsChildPath_valid "/" child (by decide) hChildValid
    have hC1 : vfsChildPath "/" child = "/" ++ child := by simp [vfsChildPath]
    rw [hC1] at hSplitC1
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitC1
    dsimp only [Internal.mkApiM, vfsOps, vfsReadBytesPure, StateT.run]
    rw [hRelRaw, hCwd2Val]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      vfsAbsNorm_root_bare_child child hChildValid, hSplitC1]
    unfold vfsResolveSegs; rw [hRoot₂]; dsimp only
    rw [show ((stR1.mode / 64) % 2 == 0) = false from by simp [hRx1], hC1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hFile₂]
  have hTmp1NotOk₂ : ((vfsOps.stat false relTmp).run s₂).1.isOk = false := by
    have ⟨_, hSplitT1⟩ := vfsChildPath_valid "/" tmp1Name (by decide) hTmp1Valid
    have hCT1 : vfsChildPath "/" tmp1Name = "/" ++ tmp1Name := by simp [vfsChildPath]
    rw [hCT1] at hSplitT1
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitT1
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [hCwd2Val, ← hRelTmpEq, vfsAbsNorm_root_dot_child tmp1Name hTmp1Valid, hSplitT1]
    unfold vfsResolveSegs; rw [hRoot₂]; dsimp only
    rw [show ((stR1.mode / 64) % 2 == 0) = false from by simp [hRx1], hCT1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hT1None₂]; rfl
  exact ⟨s₂, hStep1, hReadRel, hTmp1NotOk₂⟩

/-- Proof of `test_fs_vfs_atomicWriteBytes_nestedParentAndRelative` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_atomicWriteBytes_nestedParentAndRelative :
    AllPass (test_fs_vfs_atomicWriteBytes_nestedParentAndRelative Internal.mkApiM vfsOps) := by
  intro s₀ dirName child bytes hCond hDirStat hTmp0Missing hPath0Nf
  rcases nestedParentAndRelative_step0 s₀ dirName child bytes hCond hDirStat hTmp0Missing hPath0Nf with
    ⟨s₁, hStep0, hRead0, hTmp0NotOk₁, _, _, _⟩
  dsimp only
  rw [hStep0]
  dsimp only [assert, assume]
  refine ⟨⟨rfl, hRead0, hTmp0NotOk₁⟩, ?_⟩
  intro hCwdS1 hRootS1 hRelTmpMissing hRelNf
  rcases nestedParentAndRelative_step1 s₁ child bytes hCond.2 hCwdS1 hRootS1 hRelTmpMissing hRelNf with
    ⟨s₂, hStep1, hReadRel, hTmp1NotOk₂⟩
  rw [hStep1]
  dsimp only [assert]
  exact ⟨⟨rfl, hReadRel, hTmp1NotOk₂⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_atomicWriteBytes_nestedParentAndRelative`. -/
theorem reach_fs_vfs_atomicWriteBytes_nestedParentAndRelative :
    CanReach (test_fs_vfs_atomicWriteBytes_nestedParentAndRelative Internal.mkApiM vfsOps) := by
  let st : VfsState :=
    { tree := .dir 0o755 (fun k => if k == "d" then some (vfsEmptyDir 0o755) else none)
      keys := ["/d"], cwd := "/", nonce := 0 }
  have hDirD : ∃ stDir, ((vfsOps.stat false ("/" ++ "d")).run st).1 = .ok stDir ∧ stDir.kind = .dir ∧
      (stDir.mode / 128) % 2 = 1 ∧ (stDir.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_child_some st "d" (.dir 0o755) (by decide) rfl rfl,
      rfl, by decide, by decide⟩
  have hTmp0 : ((vfsOps.stat false ("/" ++ "d" ++ "/." ++ "f" ++ ".tmp." ++ toString (vfsOps.monotonicNonce.run st).1)).run st).1.isOk = false := by
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show ("/" ++ "d" ++ "/." ++ "f" ++ ".tmp." ++ toString st.nonce) = "/d/.f.tmp.0" from by decide]
    rw [vfsAbsNorm_canon st.cwd "/d/.f.tmp.0" (by decide), show vfsSplitSegs "/d/.f.tmp.0" = ["d", ".f.tmp.0"] from by decide]
    unfold vfsResolveSegs
    rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" "d" = "/d" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show st.nodes "/d" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/d" ".f.tmp.0" = "/d/.f.tmp.0" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show st.nodes "/d/.f.tmp.0" = none from rfl]
    rfl
  have hPath0 : ∃ e, ((vfsOps.stat false ("/" ++ "d" ++ "/" ++ "f")).run st).1 = .error e ∧ e.kind = .notFound := by
    refine ⟨{ kind := .notFound, path := some "/d/f", message := "no such file or directory: /d/f" }, ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [show ("/" ++ "d" ++ "/" ++ "f") = "/d/f" from by decide]
    rw [vfsAbsNorm_canon st.cwd "/d/f" (by decide), show vfsSplitSegs "/d/f" = ["d", "f"] from by decide]
    unfold vfsResolveSegs
    rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" "d" = "/d" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show st.nodes "/d" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/d" "f" = "/d/f" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show st.nodes "/d/f" = none from rfl]
    rfl
  rcases nestedParentAndRelative_step0 st "d" "f" (ByteArray.mk #[3, 4])
      ⟨by decide, by decide⟩ hDirD hTmp0 hPath0 with
    ⟨s₁, hStep0, hRead0, hTmp0NotOk₁, hCwd1, hNonce1, hNodes1⟩
  have hRootNd1 : s₁.nodes "/" = some (.dir 0o755) := by
    rw [hNodes1]; dsimp only
    rw [beq_false_of_ne (by decide), beq_false_of_ne (by decide)]; rfl
  have hCwdS1 : (vfsOps.cwd.run s₁).1 = .ok "/" := by
    dsimp only [vfsOps, StateT.run]; rw [hCwd1]
  have hRootS1 : ∃ stRoot, ((vfsOps.stat false "/").run s₁).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 := by
    refine ⟨vfsToStat (.dir 0o755), ?_, rfl, by decide, by decide⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [vfsAbsNorm_canon s₁.cwd "/" (by decide), show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs; rw [hRootNd1]
  have hRelTmpMissing : ((vfsOps.stat false ("./." ++ "f" ++ ".tmp." ++ toString (vfsOps.monotonicNonce.run s₁).1)).run s₁).1.isOk = false := by
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [hCwd1, hNonce1, show st.cwd = "/" from rfl, show st.nonce = 0 from rfl,
      show ("./." ++ "f" ++ ".tmp." ++ toString (0 + 1)) = "./" ++ ".f.tmp.1" from by decide,
      vfsAbsNorm_root_dot_child ".f.tmp.1" (by decide),
      show vfsSplitSegs ("/" ++ ".f.tmp.1") = [".f.tmp.1"] from by decide]
    unfold vfsResolveSegs; rw [hRootNd1]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" ".f.tmp.1" = "/.f.tmp.1" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    have hN : s₁.nodes "/.f.tmp.1" = none := by
      rw [hNodes1]; dsimp only; rw [beq_false_of_ne (by decide), beq_false_of_ne (by decide)]; rfl
    rw [hN]; rfl
  have hRelNf : ∃ e, ((vfsOps.stat false "f").run s₁).1 = .error e ∧ e.kind = .notFound := by
    refine ⟨{ kind := .notFound, path := some "/f", message := "no such file or directory: /f" }, ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [hCwd1, show st.cwd = "/" from rfl, vfsAbsNorm_root_bare_child "f" (by decide),
      show vfsSplitSegs ("/" ++ "f") = ["f"] from by decide]
    unfold vfsResolveSegs; rw [hRootNd1]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" "f" = "/f" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    have hN : s₁.nodes "/f" = none := by
      rw [hNodes1]; dsimp only; rw [beq_false_of_ne (by decide), beq_false_of_ne (by decide)]; rfl
    rw [hN]; rfl
  rcases nestedParentAndRelative_step1 s₁ "f" (ByteArray.mk #[3, 4]) (by decide)
      hCwdS1 hRootS1 hRelTmpMissing hRelNf with
    ⟨s₂, hStep1, hReadRel, hTmp1NotOk₂⟩
  refine ⟨st, "d", "f", ByteArray.mk #[3, 4], ⟨by decide, by decide⟩, hDirD, hTmp0, hPath0, ?_⟩
  dsimp only
  rw [hStep0]
  dsimp only [assert, assume]
  refine ⟨⟨rfl, hRead0, by dsimp only [vfsOps]; exact hTmp0NotOk₁⟩,
    hCwdS1, hRootS1, hRelTmpMissing, hRelNf, ?_⟩
  dsimp only
  rw [hStep1]
  dsimp only [assert]
  exact ⟨⟨rfl, hReadRel, hTmp1NotOk₂⟩, trivial⟩

/-- Proof of `test_fs_vfs_readBytes_followsSymlinkToRegularFile` on `vfsApi`. -/
theorem proof_fs_vfs_readBytes_followsSymlinkToRegularFile :
    AllPass (test_fs_vfs_readBytes_followsSymlinkToRegularFile vfsApi) := by
  intro s₀ path hV hLst hSt
  exact proof_fsraw_readBytes_followsSymlinkToRegularFile s₀ path hV hLst hSt

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_readBytes_followsSymlinkToRegularFile`. -/
theorem reach_fs_vfs_readBytes_followsSymlinkToRegularFile :
    CanReach (test_fs_vfs_readBytes_followsSymlinkToRegularFile vfsApi) :=
  reach_fsraw_readBytes_followsSymlinkToRegularFile

private theorem roundTripsExactBytesThroughSymlink_exec (s₀ : VfsState)
    (tgtName symName : String) (bytes : ByteArray)
    (hCond : (!tgtName.toList.isEmpty && !('/' ∈ tgtName.toList) && !(Char.ofNat 0 ∈ tgtName.toList) && tgtName != "." && tgtName != "..") = true ∧
      (!symName.toList.isEmpty && !('/' ∈ symName.toList) && !(Char.ofNat 0 ∈ symName.toList) && symName != "." && symName != "..") = true ∧
      tgtName ≠ symName)
    (hRoot : ∃ stRoot, ((vfsOps.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hTmpMissing : ((vfsOps.stat false ("/." ++ tgtName ++ ".tmp." ++ toString s₀.nonce)).run s₀).1.isOk = false)
    (hTgtNf : ∃ e1, ((vfsOps.stat false ("/" ++ tgtName)).run s₀).1 = .error e1 ∧ e1.kind = .notFound)
    (hSymNf : ∃ e2, ((vfsOps.stat false ("/" ++ symName)).run s₀).1 = .error e2 ∧ e2.kind = .notFound) :
    ∃ s₁ s₂,
      ((Internal.mkApiM vfsOps).atomicWriteBytes ("/" ++ tgtName) bytes).run s₀ = (.ok (), s₁) ∧
      ((Internal.mkApiM vfsOps).symlink ("/" ++ tgtName) ("/" ++ symName)).run s₁ = (.ok (), s₂) ∧
      ((Internal.mkApiM vfsOps).readBytes ("/" ++ symName)).run s₂ = (.ok bytes, s₂) := by
  rcases hCond with ⟨hTgtS, hSymS, hNe⟩
  rcases atomicWriteBytes_root_child_ok s₀ tgtName bytes hTgtS hRoot hTmpMissing (Or.inl hTgtNf) with
    ⟨s₁, hStep1, _, _, hNodes1⟩
  have hTgtValid := isSingleValidName_validFileName tgtName hTgtS
  have hSymValid := isSingleValidName_validFileName symName hSymS
  have hTgtS' : (!tgtName.toList.isEmpty && !('/' ∈ tgtName.toList) && !(Char.ofNat 0 ∈ tgtName.toList) && tgtName != "." && tgtName != "..") = true := hTgtS
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hTgtS'
  have hNulTgt : Char.ofNat 0 ∉ tgtName.toList := hTgtS'.1.1.2
  let tmpName := "." ++ tgtName ++ ".tmp." ++ toString s₀.nonce
  let tmpPath := "/." ++ tgtName ++ ".tmp." ++ toString s₀.nonce
  have hTmpValid : Internal.validFileName tmpName = true := validFileName_tmpSibling tgtName s₀.nonce hTgtValid
  have hTmpRaw : isValidRawPath tmpPath = true := isValidRawPath_tmpSibling tgtName s₀.nonce hTgtS
  have hTgtRaw : isValidRawPath ("/" ++ tgtName) = true := isValidRawPath_of_singleValid tgtName hTgtS
  have hSymRaw : isValidRawPath ("/" ++ symName) = true := isValidRawPath_of_singleValid symName hSymS
  rcases hRoot with ⟨stR, hRs, hRk, _, hRx⟩
  have hRootNd := vfsStat_root_dir_nodes s₀ stR hRs hRk
  have hRexec : ((stR.mode / 64) % 2 == 0) = false := by simp [hRx]
  have hTmpEq : "/" ++ tmpName = tmpPath := by
    apply String.ext_iff.mpr
    simp [tmpName, tmpPath, String.toList_append, List.append_assoc,
      show "/.".toList = ['/', '.'] by decide, show "/".toList = ['/'] by decide, show ".".toList = ['.'] by decide]
  have hRootNeTgt : "/" ≠ "/" ++ tgtName := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" tgtName (by decide) hTgtValid).2
    have hC : vfsChildPath "/" tgtName = "/" ++ tgtName := by simp [vfsChildPath]
    rw [hC] at hSp; rw [hSp, show vfsSplitSegs "/" = [] by decide] at this; simp at this
  have hRootNeSym : "/" ≠ "/" ++ symName := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" symName (by decide) hSymValid).2
    have hC : vfsChildPath "/" symName = "/" ++ symName := by simp [vfsChildPath]
    rw [hC] at hSp; rw [hSp, show vfsSplitSegs "/" = [] by decide] at this; simp at this
  have hRootNeTmp : "/" ≠ tmpPath := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp := (vfsChildPath_valid "/" tmpName (by decide) hTmpValid).2
    have hC : vfsChildPath "/" tmpName = tmpPath := by simp [vfsChildPath, hTmpEq]
    rw [hC] at hSp; rw [hSp, show vfsSplitSegs "/" = [] by decide] at this; simp at this
  have hSymNeTgt : "/" ++ symName ≠ "/" ++ tgtName := by
    intro heq
    have := congrArg vfsSplitSegs heq
    have hSp1 := (vfsChildPath_valid "/" symName (by decide) hSymValid).2
    have hC1 : vfsChildPath "/" symName = "/" ++ symName := by simp [vfsChildPath]
    rw [hC1] at hSp1
    have hSp2 := (vfsChildPath_valid "/" tgtName (by decide) hTgtValid).2
    have hC2 : vfsChildPath "/" tgtName = "/" ++ tgtName := by simp [vfsChildPath]
    rw [hC2] at hSp2
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSp1 hSp2
    rw [hSp1, hSp2] at this
    simp only [List.cons.injEq, and_true] at this
    exact hNe this.symm
  have hSymNone₀ : s₀.nodes ("/" ++ symName) = none := by
    rcases hSymNf with ⟨e2, hErr2, _⟩
    have ⟨hCanonS, hSplitS⟩ := vfsChildPath_valid "/" symName (by decide) hSymValid
    have hCS : vfsChildPath "/" symName = "/" ++ symName := by simp [vfsChildPath]
    rw [hCS] at hCanonS hSplitS
    rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitS
    dsimp only [vfsOps, vfsStatPure, StateT.run] at hErr2
    rw [vfsAbsNorm_canon s₀.cwd ("/" ++ symName) hCanonS, hSplitS] at hErr2
    unfold vfsResolveSegs at hErr2
    rw [hRootNd] at hErr2; dsimp only at hErr2
    rw [hRexec, hCS] at hErr2; simp only [Bool.false_eq_true, ↓reduceIte] at hErr2
    unfold vfsResolveSegs at hErr2
    cases hN : s₀.nodes ("/" ++ symName) with
    | none => exact rfl
    | some nd => exfalso; cases nd <;> simp [hN] at hErr2
  have hRoot₁ : s₁.nodes "/" = some (.dir stR.mode) := by
    rw [hNodes1]; dsimp only
    rw [beq_false_of_ne hRootNeTgt, beq_false_of_ne hRootNeTmp]; exact hRootNd
  have hSymNone₁ : s₁.nodes ("/" ++ symName) = none := by
    rw [hNodes1]; dsimp only
    rw [beq_false_of_ne hSymNeTgt]
    by_cases hEq : ("/" ++ symName) = tmpPath
    · simp [hEq, tmpPath]
    · simp [hSymNone₀]
  have ⟨hCanonS, hSplitS⟩ := vfsChildPath_valid "/" symName (by decide) hSymValid
  have hCS : vfsChildPath "/" symName = "/" ++ symName := by simp [vfsChildPath]
  rw [hCS] at hCanonS hSplitS
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitS
  let tr2 := vfsTreeSet s₁.tree (vfsSplitSegs ("/" ++ symName)) (some (.symlink ("/" ++ tgtName) 0o777))
  let s₂ : VfsState := { s₁ with tree := tr2, keys := ("/" ++ symName) :: s₁.keys }
  have hSymStep : ((Internal.mkApiM vfsOps).symlink ("/" ++ tgtName) ("/" ++ symName)).run s₁ = (.ok (), s₂) := by
    dsimp only [Internal.mkApiM, vfsOps, StateT.run]
    rw [vfsAbsNorm_canon s₁.cwd ("/" ++ symName) hCanonS, hSplitS]
    unfold vfsResolveSegs
    rw [hRoot₁]; dsimp only; rw [hRexec, hCS]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [hSymNone₁]
    dsimp only
    rw [show (Raw.FsErrorKind.notFound != Raw.FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [s₂, tr2]
    rw [hSplitS]
  have hNodes2 : s₂.nodes = fun k => if k == ("/" ++ symName) then some (.symlink ("/" ++ tgtName) 0o777) else s₁.nodes k := by
    change vfsTreeNodes tr2 = _
    have hLeaf := vfsTreeNodes_set_leaf s₁.tree "/" symName (some (.symlink ("/" ++ tgtName) 0o777))
      (by decide) hSymValid ⟨stR.mode, hRoot₁⟩
      (fun dm h => by change s₁.nodes ("/" ++ symName) = _ at h; rw [hSymNone₁] at h; cases h)
      (fun dm ch h => by cases h)
    dsimp only [Option.map, vfsTreeTopNode] at hLeaf
    rw [hCS] at hLeaf
    exact hLeaf
  have hRoot₂ : s₂.nodes "/" = some (.dir stR.mode) := by
    rw [hNodes2]; dsimp only
    rw [beq_false_of_ne hRootNeSym]; exact hRoot₁
  have hSym₂ : s₂.nodes ("/" ++ symName) = some (.symlink ("/" ++ tgtName) 0o777) := by
    rw [hNodes2]; simp
  have hTgt₂ : s₂.nodes ("/" ++ tgtName) = some (.file bytes 0o644) := by
    rw [hNodes2]; dsimp only
    rw [beq_false_of_ne hSymNeTgt.symm, hNodes1]; simp
  have ⟨hCanonTgt, hSplitTgt⟩ := vfsChildPath_valid "/" tgtName (by decide) hTgtValid
  have hCTgt : vfsChildPath "/" tgtName = "/" ++ tgtName := by simp [vfsChildPath]
  rw [hCTgt] at hCanonTgt hSplitTgt
  rw [show vfsSplitSegs "/" = [] by decide, List.nil_append] at hSplitTgt
  have hRead₂ : (((Internal.mkApiM vfsOps).readBytes ("/" ++ symName)).run s₂).1 = .ok bytes := by
    dsimp only [Internal.mkApiM, vfsOps, vfsReadBytesPure, StateT.run]
    rw [hSymRaw, vfsAbsNorm_canon s₂.cwd ("/" ++ symName) hCanonS, hSplitS]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hRoot₂]; dsimp only; rw [hRexec, hCS]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hSym₂]
    dsimp only
    rw [show Internal.isAbsolute ("/" ++ tgtName) = true from (Bool.and_eq_true _ _ |>.mp hCanonTgt).1]
    simp only [↓reduceIte]
    rw [show Internal.normPath ("/" ++ tgtName) = "/" ++ tgtName from beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hCanonTgt).2, hSplitTgt]
    unfold vfsResolveSegs; rw [hRoot₂]; dsimp only; rw [hRexec, hCTgt]; simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs; rw [hTgt₂]
  exact ⟨s₁, s₂, hStep1, hSymStep, Prod.ext hRead₂ rfl⟩

/-- Proof of `test_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink` on `Internal.mkApiM vfsOps`. -/
theorem proof_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink :
    AllPass (test_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink Internal.mkApiM vfsOps) := by
  intro s₀ tgtName symName bytes hCond hRoot hTmpMissing hTgtNf hSymNf
  rcases roundTripsExactBytesThroughSymlink_exec s₀ tgtName symName bytes hCond hRoot hTmpMissing hTgtNf hSymNf with
    ⟨s₁, s₂, hStep1, hSymStep, hRead₂⟩
  dsimp only
  rw [hStep1]
  intro _
  rw [hSymStep]
  intro _
  rw [hRead₂]
  dsimp only [assert]
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink`. -/
theorem reach_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink :
    CanReach (test_fs_vfs_readBytes_roundTripsExactBytesThroughSymlink Internal.mkApiM vfsOps) := by
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hTmp : ((vfsOps.stat false ("/." ++ "t" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = false := by
    rw [show "/." ++ "t" ++ ".tmp." ++ toString st.nonce = "/" ++ ".t.tmp.0" from by decide]
    rw [vfsOps_stat_dir755_child_none st ".t.tmp.0" (by decide) rfl rfl]
    rfl
  have hTgt : ∃ e1, ((vfsOps.stat false ("/" ++ "t")).run st).1 = .error e1 ∧ e1.kind = .notFound :=
    ⟨_, vfsOps_stat_dir755_child_none st "t" (by decide) rfl rfl, rfl⟩
  have hSym : ∃ e2, ((vfsOps.stat false ("/" ++ "s")).run st).1 = .error e2 ∧ e2.kind = .notFound :=
    ⟨_, vfsOps_stat_dir755_child_none st "s" (by decide) rfl rfl, rfl⟩
  rcases roundTripsExactBytesThroughSymlink_exec st "t" "s" (ByteArray.mk #[7, 8])
      ⟨by decide, by decide, by decide⟩ hRoot hTmp hTgt hSym with
    ⟨s₁, s₂, hStep1, hSymStep, hRead₂⟩
  refine ⟨st, "t", "s", ByteArray.mk #[7, 8], ⟨by decide, by decide, by decide⟩, hRoot, hTmp, hTgt, hSym, ?_⟩
  dsimp only
  rw [hStep1]
  dsimp only [assume]
  refine ⟨rfl, ?_⟩
  rw [hSymStep]
  dsimp only [assume]
  refine ⟨rfl, ?_⟩
  rw [hRead₂]
  dsimp only [assert]
  exact ⟨⟨rfl, rfl⟩, trivial⟩

/-- Proof of `test_fs_vfs_readBytes_dirAndMissingRejected` on `vfsApi`. -/
theorem proof_fs_vfs_readBytes_dirAndMissingRejected :
    AllPass (test_fs_vfs_readBytes_dirAndMissingRejected vfsApi) := by
  intro s₀ path hV
  exact proof_fsraw_readBytes_dirAndMissingRejected s₀ path hV

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_readBytes_dirAndMissingRejected`. -/
theorem reach_fs_vfs_readBytes_dirAndMissingRejected :
    CanReach (test_fs_vfs_readBytes_dirAndMissingRejected vfsApi) :=
  reach_fsraw_readBytes_dirAndMissingRejected

/-- Proof of `test_fs_vfs_readBytes_invalidPathRejected` on `vfsApi`. -/
theorem proof_fs_vfs_readBytes_invalidPathRejected :
    AllPass (test_fs_vfs_readBytes_invalidPathRejected vfsApi) := by
  intro s₀ path hInvalid
  exact proof_fsraw_readBytes_invalidPathRejected s₀ path hInvalid

/-- Non-vacuity `CanReach` witness for `test_fs_vfs_readBytes_invalidPathRejected`. -/
theorem reach_fs_vfs_readBytes_invalidPathRejected :
    CanReach (test_fs_vfs_readBytes_invalidPathRejected vfsApi) :=
  reach_fsraw_readBytes_invalidPathRejected

example : ¬ AllPass (test_fs_vfs_atomicWriteBytes_invalidPathRejected
    (fun ops =>
      { Internal.mkApiM ops with
        atomicWriteBytes := fun path bytes => do
          if !isValidRawPath path then
            return .error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }
          else if path == "/" then
            return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
          else
            match ← ops.stat false path with
            | .ok st =>
              if st.kind == .dir then
                return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
              else
                Internal.atomicWriteSiblingM ops path bytes
            | .error e =>
              if e.kind != .notFound then return .error e
              else Internal.atomicWriteSiblingM ops path bytes })
    vfsOps) := by
  intro hAll
  let st : VfsState := { tree := .dir 0o755 (fun _ => none), keys := [], cwd := "/", nonce := 0 }
  have hPass := hAll st "." ByteArray.empty (by decide)
  have hStatDot : vfsStatPure st false "." = .ok (vfsToStat (.dir 0o755)) := by
    unfold vfsStatPure
    rw [show vfsAbsNorm st.cwd "." = "/" from by decide, show vfsSplitSegs "/" = [] from by decide]
    unfold vfsResolveSegs
    rw [show st.nodes "/" = some (.dir 0o755) from rfl]
  dsimp only [StateT.run, Bind.bind, Pure.pure, StateT.bind, StateT.pure, vfsOps, assert] at hPass
  rw [show isValidRawPath "." = true from by decide, show ("." == "/") = false from by decide] at hPass
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPass
  unfold StateT.bind at hPass
  dsimp only at hPass
  rw [hStatDot] at hPass
  rcases hPass with ⟨⟨⟨e, hEq, hKind⟩, _⟩, _⟩
  cases hEq
  cases hKind

example : ¬ AllPass (test_fs_vfs_atomicWriteBytes_renameErrorCleansUpTmpAndPreservesTarget
    (fun ops =>
      { Internal.mkApiM ops with
        atomicWriteBytes := fun path bytes => do
          if !Internal.isValidAtomicTargetPath path then
            return .error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }
          else if path == "/" then
            return .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
          else
            let parentDir := (Internal.parent path).getD "."
            let baseName := (Internal.name path).getD "tmp"
            let nonce ← ops.monotonicNonce
            let tmpPath := Internal.join parentDir s!".{baseName}.tmp.{nonce}"
            match ← ops.createFileNew tmpPath bytes with
            | .error e => return .error e
            | .ok () =>
              match ← ops.rename tmpPath path with
              | .error e => return .error e
              | .ok () => return .ok () })
    vfsOps) := by
  intro hAll
  let st : VfsState :=
    { tree := .dir 0o755 (fun k => if k == "f" then some (VfsTree.file (ByteArray.mk #[1]) 0o644) else none)
      keys := ["/f"], cwd := "/", nonce := 0 }
  let err : FsError := { kind := .ioError, path := some "/f", message := "rename failed" }
  have hRoot : ∃ stRoot, ((vfsOps.stat false "/").run st).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
      (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨vfsToStat (.dir 0o755), vfsOps_stat_dir755_root st rfl, rfl, by decide, by decide⟩
  have hTmp : ((vfsOps.stat false ("/." ++ "f" ++ ".tmp." ++ toString st.nonce)).run st).1.isOk = false := by
    have hEq := vfsOps_stat_dir755_child_none st ".f.tmp.0" (by decide) rfl rfl
    have hPath : ("/." ++ "f" ++ ".tmp." ++ toString st.nonce) = "/" ++ ".f.tmp.0" := by decide
    dsimp only [vfsOps, StateT.run] at hEq ⊢
    rw [hPath, hEq]
    rfl
  have hOrig : ((vfsOps.readBytes ("/" ++ "f")).run st).1 = .ok (ByteArray.mk #[1]) :=
    vfsReadBytes_root_child_ok st "f" (ByteArray.mk #[1]) 0o755 0o644 (by decide) (by decide) rfl (by decide) rfl
  have hPass := hAll st "f" (ByteArray.mk #[9]) (ByteArray.mk #[1]) err (by decide) hRoot hTmp hOrig
  let sNonce : VfsState := { st with nonce := 1 }
  let tr1 := vfsTreeSet sNonce.tree (vfsSplitSegs "/.f.tmp.0") (some (.file (ByteArray.mk #[9]) 0o644))
  let sCreated : VfsState := { sNonce with tree := tr1, keys := "/.f.tmp.0" :: sNonce.keys }
  have hCreate : vfsCreateFileNewPure sNonce "/.f.tmp.0" (ByteArray.mk #[9]) = (.ok (), sCreated) := by
    unfold vfsCreateFileNewPure
    simp only [show isValidRawPath "/.f.tmp.0" = true from by decide, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [vfsAbsNorm_canon sNonce.cwd "/.f.tmp.0" (by decide), show vfsSplitSegs "/.f.tmp.0" = [".f.tmp.0"] from by decide]
    unfold vfsResolveSegs
    rw [show sNonce.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" ".f.tmp.0" = "/.f.tmp.0" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show sNonce.nodes "/.f.tmp.0" = none from rfl]
    rw [show Internal.splitLastAux [".f.tmp.0"] [] = some ([], ".f.tmp.0") from by decide]
    unfold vfsResolveSegs
    rw [show sNonce.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show (((0o755 / 128) % 2 == 0) || ((0o755 / 64) % 2 == 0)) = false from by decide,
      show vfsChildPath "/" ".f.tmp.0" = "/.f.tmp.0" from by decide]
    rfl
  dsimp only [Internal.mkApiM, StateT.run, Bind.bind, Pure.pure, StateT.bind, StateT.pure, vfsOps, assert] at hPass
  rw [show Internal.isValidAtomicTargetPath ("/" ++ "f") = true from by decide,
    show ("/" ++ "f" == "/") = false from by decide] at hPass
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPass
  unfold StateT.bind at hPass
  dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure] at hPass
  rw [show (Internal.parent ("/" ++ "f")).getD "." = "/" from by decide,
    show (Internal.name ("/" ++ "f")).getD "tmp" = "f" from by decide,
    show Internal.join "/" (toString "." ++ toString "f" ++ toString ".tmp." ++ toString 0) = "/.f.tmp.0" from by decide] at hPass
  rw [hCreate] at hPass
  dsimp only at hPass
  have hFalse : false = true := by
    have hTmpStillOk : ((vfsOps.stat false "/.f.tmp.0").run sCreated).1.isOk = true := by
      have hEq := vfsOps_stat_dir755_child_some sCreated ".f.tmp.0" (.file (ByteArray.mk #[9]) 0o644) (by decide) rfl rfl
      have hPath : "/.f.tmp.0" = "/" ++ ".f.tmp.0" := rfl
      dsimp only [vfsOps, StateT.run] at hEq ⊢
      rw [hPath, hEq]
      rfl
    have hTmpBad := hPass.2.1
    rw [show "/." ++ "f" ++ ".tmp." ++ toString 0 = "/.f.tmp.0" from by decide] at hTmpBad
    dsimp only [vfsOps, StateT.run] at hTmpStillOk
    rw [hTmpStillOk] at hTmpBad
    exact hTmpBad.symm
  cases hFalse

example : ¬ AllPass (test_fs_vfs_readBytes_followsSymlinkToRegularFile
    { vfsApi with
      readBytes := fun path => fun st =>
        if !isValidRawPath path then
          (.error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }, st)
        else
          match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) false 1024 with
          | .ok (_, .file bs _) => (.ok bs, st)
          | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"dir: {path}" }, st)
          | .ok (_, .symlink _ _) => (.error { kind := .invalidInput, path := some path, message := s!"symlink: {path}" }, st)
          | .error e => (.error e, st) }) := by
  intro hAll
  let st : VfsState :=
    { tree := .dir 0o755 (fun k =>
        if k == "t" then some (.file (ByteArray.mk #[7]) 0o644)
        else if k == "s" then some (.symlink "/t" 0o777)
        else none)
      keys := ["/t", "/s"], cwd := "/", nonce := 0 }
  have hLstat : ∃ lst, ((vfsOps.stat false "/s").run st).1 = .ok lst ∧ lst.kind = .symlink :=
    ⟨vfsToStat (.symlink "/t" 0o777), vfsOps_stat_dir755_child_some st "s" (.symlink "/t" 0o777) (by decide) rfl rfl, rfl⟩
  have hStat : ∃ fst, ((vfsOps.stat true "/s").run st).1 = .ok fst ∧ fst.kind = .file := by
    refine ⟨vfsToStat (.file (ByteArray.mk #[7]) 0o644), ?_, rfl⟩
    dsimp only [vfsOps, vfsStatPure, StateT.run]
    rw [vfsAbsNorm_canon st.cwd "/s" (by decide), show vfsSplitSegs "/s" = ["s"] from by decide]
    unfold vfsResolveSegs
    rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" "s" = "/s" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show st.nodes "/s" = some (.symlink "/t" 0o777) from rfl]; dsimp only
    rw [show Internal.isAbsolute "/t" = true from by decide]
    simp only [↓reduceIte]
    rw [show Internal.normPath "/t" = "/t" from by decide, show vfsSplitSegs "/t" = ["t"] from by decide]
    unfold vfsResolveSegs
    rw [show st.nodes "/" = some (.dir 0o755) from rfl]; dsimp only
    rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" "t" = "/t" from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold vfsResolveSegs
    rw [show st.nodes "/t" = some (.file (ByteArray.mk #[7]) 0o644) from rfl]
  have hPass := hAll st "/s" (by decide) hLstat hStat
  dsimp only [vfsApi, StateT.run, assert] at hPass
  rw [show isValidRawPath "/s" = true from by decide, vfsAbsNorm_canon st.cwd "/s" (by decide),
    show vfsSplitSegs "/s" = ["s"] from by decide] at hPass
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hPass
  unfold vfsResolveSegs at hPass
  rw [show st.nodes "/" = some (.dir 0o755) from rfl] at hPass
  dsimp only at hPass
  rw [show ((0o755 / 64) % 2 == 0) = false from by decide, show vfsChildPath "/" "s" = "/s" from by decide] at hPass
  simp only [Bool.false_eq_true, ↓reduceIte] at hPass
  unfold vfsResolveSegs at hPass
  rw [show st.nodes "/s" = some (.symlink "/t" 0o777) from rfl] at hPass
  rcases hPass with ⟨⟨⟨bs, hEq, _⟩, _⟩, _⟩
  cases hEq

end LeanSwe.Fs.Proofs
