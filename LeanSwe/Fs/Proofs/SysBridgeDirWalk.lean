import LeanSwe.Fs.Proofs.SysBridgeDirOps2

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Lexicographical `mergeSort` on `String` produces a `List.Pairwise (· ≤ ·)` list. -/
theorem list_mergeSort_str_le (xs : List String) :
    List.Pairwise (· ≤ ·) (xs.mergeSort (fun a b => decide (a ≤ b))) :=
  (List.pairwise_mergeSort (le := fun a b : String => decide (a ≤ b))
    (fun _ _ _ hab hbc => decide_eq_true (Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun _ _ => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Std.le_total) xs).imp of_decide_eq_true

/-- `Internal.sortEntryNames` produces a `List.Pairwise (fun a b => a.val ≤ b.val)` list. -/
theorem sortEntryNames_pairwise (xs : Array EntryName) :
    List.Pairwise (fun a b => a.val ≤ b.val) (Internal.sortEntryNames xs) :=
  (List.pairwise_mergeSort (le := fun a b : EntryName => decide (a.val ≤ b.val))
    (fun _ _ _ hab hbc => decide_eq_true (Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun _ _ => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Std.le_total) xs.toList).imp of_decide_eq_true

/-- `Internal.sortEntryNames` preserves the number of entries. -/
theorem sortEntryNames_length (xs : Array EntryName) :
    (Internal.sortEntryNames xs).length = xs.size := by
  simp [Internal.sortEntryNames]

/-- Evaluation law for `Internal.bracketCloseDirM` in `StateM W`. -/
theorem sysBracketCloseDirM_run {W α dirH lockH : Type}
    (ops : RawDirOpsM (StateM W) dirH lockH) (dh : dirH) (act : StateM W α) (s : W) :
    (Internal.bracketCloseDirM ops dh act).run s =
      ((act.run s).1, ((ops.closeDir dh).run (act.run s).2).2) := by
  unfold Internal.bracketCloseDirM
  cases hA : act s with
  | mk a s1 =>
    cases hC : ops.closeDir dh s1 with
    | mk c s2 =>
      change (match act s with
        | (x, s') => match ops.closeDir dh s' with | (_, s'') => (x, s'')) = _
      simp only [StateT.run, hA, hC]

/-- Evaluation law for `Internal.bracketDirLockM` on a pure action in `StateM W`. -/
theorem bracketDirLockM_pure_run {W α dirH lockH : Type}
    (ops : RawDirOpsM (StateM W) dirH lockH) (h : lockH) (actRes : Except FsError α) (s : W) :
    (Internal.bracketDirLockM ops h (pure actRes)).run s =
      let r := (ops.releaseLock h).run s
      (match actRes with
       | .error e => .error e
       | .ok a => match r.1 with | .ok () => .ok a | .error re => .error re, r.2) := by
  unfold Internal.bracketDirLockM
  cases hRel : ops.releaseLock h s with
  | mk r1 s1 =>
    cases actRes with
    | error e =>
      change (match ops.releaseLock h s with | (_, s') => (Except.error e, s')) = _
      simp only [StateT.run, hRel]
    | ok a =>
      change (match ops.releaseLock h s with
        | (relRes, s') => (match relRes with
          | Except.ok () => StateT.pure (Except.ok a)
          | Except.error re => StateT.pure (Except.error re)) s') = _
      simp only [StateT.run, hRel]
      cases r1 with
      | ok u => cases u; rfl
      | error re => rfl

/-- Helper stating a `WalkEntry`'s `dirs` and `files` arrays are sorted ascending. -/
def WalkEntrySorted (e : WalkEntry) : Prop :=
  List.Pairwise (· ≤ ·) e.dirs.toList ∧ List.Pairwise (· ≤ ·) e.files.toList

private theorem pairwise_reverse_append_cons {α : Type} {R : α → α → Prop}
    {acc rest : List α} {x : α}
    (hAcc : List.Pairwise R acc.reverse)
    (hCross : ∀ a ∈ acc, ∀ b ∈ x :: rest, R a b)
    (hTail : List.Pairwise R (x :: rest)) :
    List.Pairwise R (x :: acc).reverse ∧
    (∀ a ∈ x :: acc, ∀ b ∈ rest, R a b) ∧
    List.Pairwise R rest := by
  rw [List.pairwise_cons] at hTail
  refine ⟨?_, ?_, hTail.2⟩
  · simp only [List.reverse_cons]
    rw [List.pairwise_append]
    refine ⟨hAcc, List.pairwise_singleton R x, ?_⟩
    intro a ha b hb
    rw [List.mem_reverse] at ha
    rw [List.mem_singleton] at hb
    subst hb
    exact hCross a ha b (by simp)
  · intro a ha b hb
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha'
    · exact hTail.1 b hb
    · exact hCross a ha' b (List.mem_cons_of_mem _ hb)

/-- Confined trace and sortedness specification for `Internal.classifyChildrenM`. -/
theorem classifyChildrenM_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dirDh : HandleId) (held : List HandleId)
    (items : List EntryName) (dirsAcc : List EntryName) (filesAcc : List String)
    (hItems : List.Pairwise (fun a b => a.val ≤ b.val) items)
    (hDirsAcc : List.Pairwise (· ≤ ·) (dirsAcc.reverse.map (·.val)))
    (hFilesAcc : List.Pairwise (· ≤ ·) filesAcc.reverse)
    (hCrossD : ∀ d ∈ dirsAcc, ∀ x ∈ items, d.val ≤ x.val)
    (hCrossF : ∀ f ∈ filesAcc, ∀ x ∈ items, f ≤ x.val)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (Internal.classifyChildrenM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dirDh items dirsAcc filesAcc).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok (dirs, files) =>
        List.Pairwise (· ≤ ·) (dirs.map (·.val)) ∧ List.Pairwise (· ≤ ·) files
      | .error e => nonLockErrOk e := by
  induction items generalizing dirsAcc filesAcc s with
  | nil =>
    unfold Internal.classifyChildrenM
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, hDirsAcc, hFilesAcc⟩
  | cons n rest ih =>
    unfold Internal.classifyChildrenM
    have hLs := dirOps_lstatAt_trace hCap dirDh n held hWf
    cases hR : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt dirDh n s) with
    | mk res s1 =>
      rw [StateT.run] at hLs; rw [hR] at hLs; dsimp only at hLs
      obtain ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, hOut1⟩ := hLs
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      cases res with
      | error e =>
        simp only [Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, hOut1.1⟩
      | ok info =>
        have hSplit := List.pairwise_cons.mp hItems
        by_cases hDir : (info.kind == .dir) = true
        · simp only [hDir, ↓reduceIte]
          have hStep := pairwise_reverse_append_cons (R := fun a b : EntryName => a.val ≤ b.val)
            (List.pairwise_map.mp hDirsAcc) hCrossD hItems
          have hDirsAcc' : List.Pairwise (· ≤ ·) ((n :: dirsAcc).reverse.map (·.val)) :=
            List.pairwise_map.mpr hStep.1
          have hCrossF' : ∀ f ∈ filesAcc, ∀ x ∈ rest, f ≤ x.val :=
            fun f hf x hx => hCrossF f hf x (List.mem_cons_of_mem _ hx)
          have hIh := ih (n :: dirsAcc) filesAcc hSplit.2 hDirsAcc' hFilesAcc hStep.2.1 hCrossF' hWf1
          cases hO : (Internal.classifyChildrenM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dirDh rest (n :: dirsAcc) filesAcc s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hO] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hIh
            exact ⟨hWf2, hTmp2.trans hTmp1, tr1 ++ tr2, healthyFilesSteps_append hSt1 hSt2,
              traceFds_append hFd1 hFd2, confined_append hConf1 hConf2, hOut2⟩
        · simp only [hDir, Bool.false_eq_true, ↓reduceIte]
          have hItemsStr : List.Pairwise (· ≤ ·) (n.val :: rest.map (·.val)) :=
            List.pairwise_map.mpr hItems
          have hCrossFStr : ∀ f ∈ filesAcc, ∀ y ∈ n.val :: rest.map (·.val), f ≤ y := by
            intro f hf y hy
            rw [List.mem_cons] at hy
            rcases hy with rfl | hy'
            · exact hCrossF f hf n (by simp)
            · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy'
              exact hCrossF f hf x (List.mem_cons_of_mem _ hx)
          have hStep := pairwise_reverse_append_cons hFilesAcc hCrossFStr hItemsStr
          have hCrossD' : ∀ d ∈ dirsAcc, ∀ x ∈ rest, d.val ≤ x.val :=
            fun d hd x hx => hCrossD d hd x (List.mem_cons_of_mem _ hx)
          have hCrossF' : ∀ f ∈ n.val :: filesAcc, ∀ x ∈ rest, f ≤ x.val :=
            fun f hf x hx => hStep.2.1 f hf x.val (List.mem_map_of_mem hx)
          have hIh := ih dirsAcc (n.val :: filesAcc) hSplit.2 hDirsAcc hStep.1 hCrossD' hCrossF' hWf1
          cases hO : (Internal.classifyChildrenM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dirDh rest dirsAcc (n.val :: filesAcc) s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hO] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hIh
            exact ⟨hWf2, hTmp2.trans hTmp1, tr1 ++ tr2, healthyFilesSteps_append hSt1 hSt2,
              traceFds_append hFd1 hFd2, confined_append hConf1 hConf2, hOut2⟩

/-- General confined trace specification for `Internal.walkDescendAuxM`, supporting both normal ops (`outFd = none`) and lock acquisition (`outFd = some`). -/
theorem walkDescendAuxM_trace {W α : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (outFd : α → Option HandleId)
    (post : HandleId → α → List KernelStep → Prop)
    (errPred : FsError → List KernelStep → Prop)
    (hErrMono : ∀ e sub tr, Subtrace sub tr → errPred e sub → errPred e tr)
    (hOpenErr : ∀ e tr, nonLockErrOk e → (e.kind = .notFound → ∃ r, (r, .err Errno.ENOENT) ∈ tr) → errPred e tr)
    (act : HandleId → StateM W (Except FsError α))
    (hAct : ∀ (dirDh : HandleId) (held : List HandleId) {s : W}, fsWorldWf (proj s) = true →
      let p := (act dirDh).run s
      fsWorldWf (proj p.2) = true ∧
      (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
      ∃ tr,
        HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        match p.1 with
        | .ok a =>
          TraceFds held tr (match outFd a with | none => held | some h => h :: held) ∧
          post dirDh a tr
        | .error e => TraceFds held tr held ∧ errPred e tr)
    (isRoot : Bool) (cur : HandleId) (tailHeld : List HandleId) (segs : List EntryName)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let held0 := if isRoot then tailHeld else cur :: tailHeld
    let p := (Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) isRoot cur segs act).run s
    fsWorldWf (proj p.2) = true ∧
    (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok a =>
        TraceFds held0 tr (match outFd a with | none => tailHeld | some h => h :: tailHeld) ∧
        ∃ d sub, Subtrace sub tr ∧ post d a sub
      | .error e => TraceFds held0 tr tailHeld ∧ errPred e tr := by
  induction segs generalizing isRoot cur s with
  | nil =>
    unfold Internal.walkDescendAuxM
    cases isRoot with
    | true =>
      simp only [↓reduceIte]
      have hA := hAct cur tailHeld hWf
      cases hRa : act cur s with
      | mk res s1 =>
        simp only [StateT.run, hRa] at hA ⊢
        obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hA
        refine ⟨hWf1, hTmp1, tr, hSt, hConf, ?_⟩
        cases res with
        | ok a => exact ⟨hOut.1, cur, tr, subtrace_refl tr, hOut.2⟩
        | error e => exact hOut
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sysBracketCloseDirM_run]
      have hA := hAct cur (cur :: tailHeld) hWf
      cases hRa : act cur s with
      | mk res s1 =>
        rw [StateT.run] at hA; rw [hRa] at hA; dsimp only at hA
        obtain ⟨hWf1, hTmp1, trA, hStA, hConfA, hOutA⟩ := hA
        have hCc := closeCheck_trace hCap cur none tailHeld hWf1
        cases hRc : (SysBridge.closeCheck cap.files cur none s1) with
        | mk cRes s2 =>
          rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
          obtain ⟨hWf2, hTmp2, _, co, hStC, hFdC, _⟩ := hCc
          have hCloseEq : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).closeDir cur s1 = (cRes, s2) := hRc
          simp only [StateT.run, hRa, hCloseEq]
          refine ⟨hWf2, by omega, trA ++ [(.close cur, co)],
            healthyFilesSteps_append hStA hStC, confined_append hConfA (confined_single (s := (.close cur, co)) trivial), ?_⟩
          cases res with
          | error e =>
            exact ⟨traceFds_append hOutA.1 hFdC, hErrMono e trA _ (subtrace_append_left _ (subtrace_refl trA)) hOutA.2⟩
          | ok a =>
            dsimp only at hOutA
            refine ⟨?_, cur, trA, subtrace_append_left _ (subtrace_refl trA), hOutA.2⟩
            cases hOf : outFd a with
            | none =>
              rw [hOf] at hOutA
              exact traceFds_append hOutA.1 hFdC
            | some x =>
              rw [hOf] at hOutA
              exact traceFds_append hOutA.1 traceFds_close_second
  | cons seg rest ih =>
    unfold Internal.walkDescendAuxM
    cases isRoot with
    | true =>
      simp only [↓reduceIte]
      have hOp := openDirAtPure_trace hCap cur seg tailHeld DEFAULT_EINTR_FUEL hWf
      cases hRo : (SysBridge.openDirAtPure cap.files cur seg DEFAULT_EINTR_FUEL s) with
      | mk oRes s1 =>
        rw [StateT.run] at hOp; rw [hRo] at hOp; dsimp only at hOp
        obtain ⟨hWf1, hTmp1, trO, hStO, hConfO, hOutO⟩ := hOp
        have hRo' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg s = (oRes, s1) := hRo
        simp only [Bind.bind, StateT.bind, StateT.run, hRo']
        cases oRes with
        | error e =>
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf1, by omega, trO, hStO, hConfO, hOutO.1, hOpenErr e trO hOutO.2.1 hOutO.2.2⟩
        | ok nextDh =>
          have hIh := ih false nextDh hWf1
          cases hRec : (Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest act s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hRec, Bool.false_eq_true, ↓reduceIte] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hSt2, hConf2, hOut2⟩ := hIh
            refine ⟨hWf2, by omega, trO ++ tr2, healthyFilesSteps_append hStO hSt2,
              confined_append hConfO hConf2, ?_⟩
            cases r2 with
            | error e =>
              exact ⟨traceFds_append hOutO hOut2.1, hErrMono e tr2 _ (subtrace_append_right trO (subtrace_refl tr2)) hOut2.2⟩
            | ok a =>
              obtain ⟨hFd2, d, sub, hSub, hPost⟩ := hOut2
              exact ⟨traceFds_append hOutO hFd2, d, sub, subtrace_append_right trO hSub, hPost⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hOp := openDirAtPure_trace hCap cur seg (cur :: tailHeld) DEFAULT_EINTR_FUEL hWf
      cases hRo : (SysBridge.openDirAtPure cap.files cur seg DEFAULT_EINTR_FUEL s) with
      | mk oRes s1 =>
        rw [StateT.run] at hOp; rw [hRo] at hOp; dsimp only at hOp
        obtain ⟨hWf1, hTmp1, trO, hStO, hConfO, hOutO⟩ := hOp
        have hCc := closeCheck_trace hCap cur none tailHeld hWf1
        cases hRc : (SysBridge.closeCheck cap.files cur none s1) with
        | mk cRes s2 =>
          rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
          obtain ⟨hWf2, hTmp2, _, co, hStC, hFdC, _⟩ := hCc
          have hBr : (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) cur
              ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg)) s = (oRes, s2) := by
            have h1 := sysBracketCloseDirM_run (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) cur
              ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg) s
            have hRo' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg s = (oRes, s1) := hRo
            have hRc' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).closeDir cur s1 = (cRes, s2) := hRc
            simp only [StateT.run, hRo', hRc'] at h1
            exact h1
          simp only [Bind.bind, StateT.bind, StateT.run, hBr]
          have hStOC := healthyFilesSteps_append hStO hStC
          have hConfOC := confined_append hConfO (confined_single (s := (.close cur, co)) trivial)
          cases oRes with
          | error e =>
            simp only [Pure.pure, StateT.pure]
            exact ⟨hWf2, by omega, trO ++ [(.close cur, co)], hStOC, hConfOC,
              traceFds_append hOutO.1 hFdC,
              hErrMono e trO _ (subtrace_append_left _ (subtrace_refl trO)) (hOpenErr e trO hOutO.2.1 hOutO.2.2)⟩
          | ok nextDh =>
            have hFdOC : TraceFds (cur :: tailHeld) (trO ++ [(.close cur, co)]) (nextDh :: tailHeld) :=
              traceFds_append hOutO traceFds_close_second
            have hIh := ih false nextDh hWf2
            cases hRec : (Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest act s2) with
            | mk r3 s3 =>
              simp only [StateT.run, hRec, Bool.false_eq_true, ↓reduceIte] at hIh ⊢
              obtain ⟨hWf3, hTmp3, tr3, hSt3, hConf3, hOut3⟩ := hIh
              refine ⟨hWf3, by omega, (trO ++ [(.close cur, co)]) ++ tr3,
                healthyFilesSteps_append hStOC hSt3, confined_append hConfOC hConf3, ?_⟩
              cases r3 with
              | error e =>
                exact ⟨traceFds_append hFdOC hOut3.1, hErrMono e tr3 _ (subtrace_append_right _ (subtrace_refl tr3)) hOut3.2⟩
              | ok a =>
                obtain ⟨hFd3, d, sub, hSub, hPost⟩ := hOut3
                exact ⟨traceFds_append hFdOC hFd3, d, sub, subtrace_append_right _ hSub, hPost⟩

/-- Confined trace specification for `Internal.mkdirWalkM`. -/
theorem mkdirWalkM_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (post : HandleId → List KernelStep → Prop)
    (leafAct : HandleId → StateM W (Except FsError Unit))
    (hLeaf : ∀ (dirDh : HandleId) (held : List HandleId) {s : W}, fsWorldWf (proj s) = true →
      let p := (leafAct dirDh).run s
      fsWorldWf (proj p.2) = true ∧
      (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
      ∃ tr,
        HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
        TraceFds held tr held ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        match p.1 with
        | .ok () => post dirDh tr
        | .error e => nonLockErrOk e)
    (isRoot : Bool) (cur : HandleId) (tailHeld : List HandleId) (segs : List EntryName)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let held0 := if isRoot then tailHeld else cur :: tailHeld
    let p := (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) isRoot cur segs leafAct).run s
    fsWorldWf (proj p.2) = true ∧
    (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held0 tr tailHeld ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => ∃ d sub, Subtrace sub tr ∧ post d sub
      | .error e => nonLockErrOk e := by
  induction segs generalizing isRoot cur s with
  | nil =>
    unfold Internal.mkdirWalkM
    cases isRoot with
    | true =>
      simp only [↓reduceIte]
      have hL := hLeaf cur tailHeld hWf
      cases hRl : leafAct cur s with
      | mk res s1 =>
        simp only [StateT.run, hRl] at hL ⊢
        obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hL
        refine ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, ?_⟩
        cases res with
        | ok u => cases u; exact ⟨cur, tr, subtrace_refl tr, hOut⟩
        | error e => exact hOut
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sysBracketCloseDirM_run]
      have hL := hLeaf cur (cur :: tailHeld) hWf
      cases hRl : leafAct cur s with
      | mk res s1 =>
        rw [StateT.run] at hL; rw [hRl] at hL; dsimp only at hL
        obtain ⟨hWf1, hTmp1, trL, hStL, hFdL, hConfL, hOutL⟩ := hL
        have hCc := closeCheck_trace hCap cur none tailHeld hWf1
        cases hRc : (SysBridge.closeCheck cap.files cur none s1) with
        | mk cRes s2 =>
          rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
          obtain ⟨hWf2, hTmp2, _, co, hStC, hFdC, _⟩ := hCc
          have hCloseEq : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).closeDir cur s1 = (cRes, s2) := hRc
          simp only [StateT.run, hRl, hCloseEq]
          refine ⟨hWf2, by omega, trL ++ [(.close cur, co)],
            healthyFilesSteps_append hStL hStC, traceFds_append hFdL hFdC,
            confined_append hConfL (confined_single (s := (.close cur, co)) trivial), ?_⟩
          cases res with
          | ok u => cases u; exact ⟨cur, trL, subtrace_append_left _ (subtrace_refl trL), hOutL⟩
          | error e => exact hOutL
  | cons seg rest ih =>
    let stepM : StateM W (Except FsError HandleId) := do
      match ← (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg with
      | .ok nextDh => pure (.ok nextDh)
      | .error e =>
        if e.kind == .notFound then
          match ← (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt cur seg with
          | .ok () => (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg
          | .error ce =>
            if ce.kind == .alreadyExists then (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg
            else pure (.error ce)
        else
          pure (.error e)
    have hStepSpec : ∀ (hld : List HandleId),
        let q := stepM.run s
        fsWorldWf (proj q.2) = true ∧
        (proj q.2).tempSeq = (proj s).tempSeq ∧
        ∃ tr,
          HealthyFilesSteps (proj s).env tr (proj q.2).env ∧
          (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
          match q.1 with
          | .ok nextDh => TraceFds hld tr (nextDh :: hld)
          | .error e => TraceFds hld tr hld ∧ nonLockErrOk e := by
      intro hld
      dsimp only [stepM]
      have hOp1 := openDirAtPure_trace hCap cur seg hld DEFAULT_EINTR_FUEL hWf
      cases hR1 : (SysBridge.openDirAtPure cap.files cur seg DEFAULT_EINTR_FUEL s) with
      | mk r1 s1 =>
        rw [StateT.run] at hOp1; rw [hR1] at hOp1; dsimp only at hOp1
        obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hOp1
        have hR1' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg s = (r1, s1) := hR1
        simp only [Bind.bind, StateT.bind, StateT.run, hR1']
        cases r1 with
        | ok nextDh =>
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩
        | error e =>
          by_cases hNf : (e.kind == .notFound) = true
          · simp only [hNf, ↓reduceIte]
            have hCr := dirOps_createDirAt_trace hCap cur seg hld hWf1
            cases hRc : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt cur seg s1) with
            | mk crRes s2 =>
              rw [StateT.run] at hCr; rw [hRc] at hCr; dsimp only at hCr
              obtain ⟨hWf2, hTmp2, trC, hStC, hFdC, hConfC, hOutC⟩ := hCr
              simp only [Bind.bind, StateT.bind, hRc]
              cases crRes with
              | ok u =>
                cases u
                dsimp only
                have hOp2 := openDirAtPure_trace hCap cur seg hld DEFAULT_EINTR_FUEL hWf2
                cases hR2 : (SysBridge.openDirAtPure cap.files cur seg DEFAULT_EINTR_FUEL s2) with
                | mk r2 s3 =>
                  rw [StateT.run] at hOp2; rw [hR2] at hOp2; dsimp only at hOp2
                  obtain ⟨hWf3, hTmp3, tr2, hSt2, hConf2, hOut2⟩ := hOp2
                  have hR2' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg s2 = (r2, s3) := hR2
                  rw [hR2']; dsimp only
                  refine ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), (tr1 ++ trC) ++ tr2,
                    healthyFilesSteps_append (healthyFilesSteps_append hSt1 hStC) hSt2,
                    confined_append (confined_append hConf1 hConfC) hConf2, ?_⟩
                  cases r2 with
                  | ok nextDh => exact traceFds_append (traceFds_append hOut1.1 hFdC) hOut2
                  | error e2 => exact ⟨traceFds_append (traceFds_append hOut1.1 hFdC) hOut2.1, hOut2.2.1⟩
              | error ce =>
                dsimp only
                by_cases hEx : (ce.kind == .alreadyExists) = true
                · simp only [hEx, ↓reduceIte]
                  have hOp2 := openDirAtPure_trace hCap cur seg hld DEFAULT_EINTR_FUEL hWf2
                  cases hR2 : (SysBridge.openDirAtPure cap.files cur seg DEFAULT_EINTR_FUEL s2) with
                  | mk r2 s3 =>
                    rw [StateT.run] at hOp2; rw [hR2] at hOp2; dsimp only at hOp2
                    obtain ⟨hWf3, hTmp3, tr2, hSt2, hConf2, hOut2⟩ := hOp2
                    have hR2' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg s2 = (r2, s3) := hR2
                    rw [hR2']; dsimp only
                    refine ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), (tr1 ++ trC) ++ tr2,
                      healthyFilesSteps_append (healthyFilesSteps_append hSt1 hStC) hSt2,
                      confined_append (confined_append hConf1 hConfC) hConf2, ?_⟩
                    cases r2 with
                    | ok nextDh => exact traceFds_append (traceFds_append hOut1.1 hFdC) hOut2
                    | error e2 => exact ⟨traceFds_append (traceFds_append hOut1.1 hFdC) hOut2.1, hOut2.2.1⟩
                · simp only [hEx, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                  exact ⟨hWf2, hTmp2.trans hTmp1, tr1 ++ trC, healthyFilesSteps_append hSt1 hStC,
                    confined_append hConf1 hConfC, traceFds_append hOut1.1 hFdC, hOutC⟩
          · simp only [hNf, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1.1, hOut1.2.1⟩
    cases isRoot with
    | true =>
      have hSt := hStepSpec tailHeld
      cases hRs : stepM s with
      | mk rNext s1 =>
        rw [StateT.run] at hSt; rw [hRs] at hSt; dsimp only at hSt
        obtain ⟨hWf1, hTmp1, trS, hStS, hConfS, hOutS⟩ := hSt
        have hEq : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true cur (seg :: rest) leafAct).run s =
            (match rNext with
             | .error e => (Except.error e, s1)
             | .ok nextDh => (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest leafAct).run s1) := by
          conv => lhs; unfold Internal.mkdirWalkM
          simp only [↓reduceIte]
          refine Eq.trans ?_ (show (stepM >>= fun r => match r with
            | .error e => pure (Except.error e)
            | .ok nextDh => Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest leafAct).run s = _ from by
            simp only [Bind.bind, StateT.bind, StateT.run, hRs]; cases rNext <;> rfl)
          have hF : ∀ (a b : StateM W (Except FsError HandleId))
              (g1 g2 : Except FsError HandleId → StateM W (Except FsError Unit)),
              a = b → g1 = g2 → (a >>= g1).run s = (b >>= g2).run s := by rintro _ _ _ _ rfl rfl; rfl
          refine hF _ _ _ _ (funext fun s0 => ?_) (funext fun r => by cases r <;> rfl)
          simp only [stepM, Bind.bind, StateT.bind]
          cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg s0 with
          | mk r0 sA =>
            cases r0 with
            | ok _ => rfl
            | error e =>
              by_cases hNf : (e.kind == .notFound) = true
              · simp only [hNf, ↓reduceIte]
                cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt cur seg sA with
                | mk rC _ => cases rC with | ok u => cases u; rfl | error _ => rfl
              · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
        dsimp only; rw [hEq]
        cases rNext with
        | error e =>
          dsimp only
          exact ⟨hWf1, by omega, trS, hStS, hOutS.1, hConfS, hOutS.2⟩
        | ok nextDh =>
          have hIh := ih false nextDh hWf1
          cases hRec : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest leafAct s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hRec, Bool.false_eq_true, ↓reduceIte] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hIh
            refine ⟨hWf2, by omega, trS ++ tr2, healthyFilesSteps_append hStS hSt2,
              traceFds_append hOutS hFd2, confined_append hConfS hConf2, ?_⟩
            cases r2 with
            | error e => exact hOut2
            | ok u => cases u; obtain ⟨d, sub, hSub, hPost⟩ := hOut2; exact ⟨d, sub, subtrace_append_right trS hSub, hPost⟩
    | false =>
      have hSt := hStepSpec (cur :: tailHeld)
      cases hRs : stepM s with
      | mk rNext s1 =>
        rw [StateT.run] at hSt; rw [hRs] at hSt; dsimp only at hSt
        obtain ⟨hWf1, hTmp1, trS, hStS, hConfS, hOutS⟩ := hSt
        have hCc := closeCheck_trace hCap cur none tailHeld hWf1
        cases hRc : (SysBridge.closeCheck cap.files cur none s1) with
        | mk cRes s2 =>
          rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
          obtain ⟨hWf2, hTmp2, _, co, hStC, hFdC, _⟩ := hCc
          have hBr : (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) cur stepM) s = (rNext, s2) := by
            have h1 := sysBracketCloseDirM_run (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) cur stepM s
            have hRc' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).closeDir cur s1 = (cRes, s2) := hRc
            simp only [StateT.run, hRs, hRc'] at h1; exact h1
          have hEq : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false cur (seg :: rest) leafAct).run s =
              (match rNext with
               | .error e => (Except.error e, s2)
               | .ok nextDh => (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest leafAct).run s2) := by
            conv => lhs; unfold Internal.mkdirWalkM
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine Eq.trans ?_ (show ((Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) cur stepM) >>= fun r =>
              match r with
              | .error e => pure (Except.error e)
              | .ok nextDh => Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest leafAct).run s = _ from by
              simp only [Bind.bind, StateT.bind, StateT.run, hBr]; cases rNext <;> rfl)
            have hF : ∀ (a b : StateM W (Except FsError HandleId))
                (g1 g2 : Except FsError HandleId → StateM W (Except FsError Unit)),
                a = b → g1 = g2 →
                ((Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) cur a) >>= g1).run s =
                ((Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) cur b) >>= g2).run s := by
              rintro _ _ _ _ rfl rfl; rfl
            refine hF _ _ _ _ (funext fun s0 => ?_) (funext fun r => by cases r <;> rfl)
            simp only [stepM, Bind.bind, StateT.bind]
            cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDirAt cur seg s0 with
            | mk r0 sA =>
              cases r0 with
              | ok _ => rfl
              | error e =>
                by_cases hNf : (e.kind == .notFound) = true
                · simp only [hNf, ↓reduceIte]
                  cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt cur seg sA with
                  | mk rC _ => cases rC with | ok u => cases u; rfl | error _ => rfl
                · simp only [hNf, Bool.false_eq_true, ↓reduceIte]
          dsimp only; rw [hEq]
          have hStSC := healthyFilesSteps_append hStS hStC
          have hConfSC := confined_append hConfS (confined_single (s := (.close cur, co)) trivial)
          cases rNext with
          | error e =>
            dsimp only
            exact ⟨hWf2, by omega, trS ++ [(.close cur, co)], hStSC,
              traceFds_append hOutS.1 hFdC, hConfSC, hOutS.2⟩
          | ok nextDh =>
            have hFdSC : TraceFds (cur :: tailHeld) (trS ++ [(.close cur, co)]) (nextDh :: tailHeld) :=
              traceFds_append hOutS traceFds_close_second
            have hIh := ih false nextDh hWf2
            cases hRec : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) false nextDh rest leafAct s2) with
            | mk r3 s3 =>
              simp only [StateT.run, hRec, Bool.false_eq_true, ↓reduceIte] at hIh ⊢
              obtain ⟨hWf3, hTmp3, tr3, hSt3, hFd3, hConf3, hOut3⟩ := hIh
              refine ⟨hWf3, by omega, (trS ++ [(.close cur, co)]) ++ tr3,
                healthyFilesSteps_append hStSC hSt3, traceFds_append hFdSC hFd3,
                confined_append hConfSC hConf3, ?_⟩
              cases r3 with
              | error e => exact hOut3
              | ok u => cases u; obtain ⟨d, sub, hSub, hPost⟩ := hOut3; exact ⟨d, sub, subtrace_append_right _ hSub, hPost⟩

end LeanSwe.Fs.Proofs
