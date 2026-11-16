import LeanSwe.Fs.Proofs.PurePathProofs
import LeanSwe.Fs.Proofs.VfsShared

namespace LeanSwe.Fs.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs
open LeanSwe.Fs.ProofsInternal

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
    dsimp only [dstKey] at hDstNotDir1
    rw [hPerm, show (tmpKey == dstKey) = false from beq_false_of_ne hTmpNeDst]
    have hD1 : ∀ m, sAfterCreate.nodes (vfsChildPath parCanon lastSeg) ≠ some (.dir m) := by
      intro m hDir
      rw [hDir] at hDstNotDir1
      cases hDstNotDir1
    cases hNd : sAfterCreate.nodes (vfsChildPath parCanon lastSeg) with
    | none =>
      simp only [Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
      rfl
    | some nd =>
      cases nd with
      | dir m => exact absurd hNd (hD1 m)
      | file _ _ | symlink _ _ =>
        simp only [Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
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
