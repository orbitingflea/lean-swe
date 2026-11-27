import LeanSwe.Fs.Interface

open LeanSwe.Fs

namespace LeanSwe.Fs.ProofsInternal

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem splitCharList_ne_nil (sep : Char) (cs : List Char) :
    Internal.splitCharList sep cs ≠ [] := by
  induction cs with
  | nil => simp [Internal.splitCharList]
  | cons c rest _ =>
    simp only [Internal.splitCharList]
    split
    · simp
    · cases Internal.splitCharList sep rest <;> simp

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem splitCharList_no_sep (sep : Char) (cs : List Char) :
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

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem splitCharList_of_no_sep (sep : Char) (b : List Char) (hno : sep ∉ b) :
    Internal.splitCharList sep b = [b] := by
  induction b with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hcne : c ≠ sep := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [Internal.splitCharList, beq_false_of_ne hcne, ih']

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem splitCharList_append_slash (a b : List Char) (hno : '/' ∉ a) :
    Internal.splitCharList '/' (a ++ '/' :: b) = a :: Internal.splitCharList '/' b := by
  induction a with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hcne : c ≠ '/' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [List.cons_append, Internal.splitCharList, beq_false_of_ne hcne, ih']

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem splitCharList_joinSlashChars (segs : List (List Char))
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

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem collapseChars_elems_valid (abs : Bool) (segs acc : List (List Char))
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
          · exact ih tail (fun x hx => hAcc x (by simp [hx])) (fun x hx => hSegs x (by simp [hx]) )
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

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def ValidStack (abs : Bool) : List (List Char) → Prop
  | [] => True
  | top :: tail =>
    !top.isEmpty ∧ top != ['.'] ∧ '/' ∉ top ∧ ValidStack abs tail ∧
      (top = ['.', '.'] → abs = false ∧ ∀ x ∈ tail, x = ['.', '.'])

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem validStack_tail {abs : Bool} {top : List Char} {tail : List (List Char)}
    (h : ValidStack abs (top :: tail)) : ValidStack abs tail :=
  h.2.2.2.1

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem validStack_push_nonDotDot {abs : Bool} {seg : List Char} {acc : List (List Char)}
    (h1 : !seg.isEmpty) (h2 : seg != ['.']) (h3 : '/' ∉ seg) (h4 : seg ≠ ['.', '.'])
    (hAcc : ValidStack abs acc) : ValidStack abs (seg :: acc) :=
  ⟨h1, h2, h3, hAcc, fun hm => absurd hm h4⟩

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem validStack_push_dotDot {acc : List (List Char)}
    (hAbs : ∀ x ∈ acc, x = ['.', '.']) (hAcc : ValidStack false acc) :
    ValidStack false (['.', '.'] :: acc) :=
  ⟨by decide, by decide, by decide, hAcc, fun _ => ⟨rfl, hAbs⟩⟩

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem collapseChars_validStack (abs : Bool) (segs acc : List (List Char))
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

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def NoDotDot (xs : List (List Char)) : Prop :=
  ∀ s ∈ xs, s ≠ ['.', '.']

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def ValidOrder : Bool → List (List Char) → Prop
  | true, xs => NoDotDot xs
  | false, xs => ∃ pre suf, xs = pre ++ suf ∧ (∀ x ∈ pre, x = ['.', '.']) ∧ NoDotDot suf

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem validStack_to_validOrder (abs : Bool) (acc : List (List Char))
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

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem collapseChars_noop (abs : Bool) (rest acc : List (List Char))
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

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem isAbsChars_joinSlashChars_head {hd : List Char} {tl : List (List Char)}
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

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem splitLastAux_append_singleton {α : Type} (xs acc : List α) (last : α) :
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

end LeanSwe.Fs.ProofsInternal
