import LeanSwe.Fs.Interface
import LeanSwe.Fs.Proofs.SysBridgeDirTree

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall LeanSwe.LinuxSyscall.Files LeanSwe.Fs LeanSwe.Fs.Model

/-- Named `Except` outcome matcher so congruence substitution unifies cleanly across `match` helpers. -/
def exceptPred {α : Type} (r : Except FsError α) (okP : α → Prop) (errP : FsError → Prop) : Prop :=
  match r with | .ok a => okP a | .error e => errP e

/-- Substitute an equal `(result, state)` pair in a `withSubtreeM_trace` action obligation. -/
theorem subAct_subst {W α : Type} {proj : W → FsWorld} {dh : HandleId} {s0 : W}
    {okP : α → List KernelStep → Prop} {errP : FsError → List KernelStep → Prop}
    {r1 r2 : Except FsError α} {s1 s2 : W} (hEq : (r1, s1) = (r2, s2))
    (h : fsWorldWf (proj s2) = true ∧ (proj s0).tempSeq ≤ (proj s2).tempSeq ∧
      ∃ tr, HealthyFilesSteps (proj s0).env tr (proj s2).env ∧ TraceFds [dh] tr [dh] ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧ exceptPred r2 (fun a => okP a tr) (fun e => errP e tr)) :
    fsWorldWf (proj s1) = true ∧ (proj s0).tempSeq ≤ (proj s1).tempSeq ∧
    ∃ tr, HealthyFilesSteps (proj s0).env tr (proj s1).env ∧ TraceFds [dh] tr [dh] ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧ exceptPred r1 (fun a => okP a tr) (fun e => errP e tr) := by
  cases hEq; exact h

/-- General confined trace specification for `Internal.withSubtreeM`. -/
theorem withSubtreeM_trace {W α : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (rootPath : String)
    (okPred : α → HandleId → List KernelStep → Prop)
    (errPred : FsError → HandleId → List KernelStep → Prop)
    (hOkMono : ∀ a dh tr1 tr2, okPred a dh tr2 → okPred a dh (tr1 ++ tr2))
    (hErrMono : ∀ e dh tr1 tr2, errPred e dh tr2 → errPred e dh (tr1 ++ tr2))
    (action : SubtreeM (StateM W) → StateM W (Except FsError α))
    (hAct : ∀ (dh : HandleId) {s : W}, fsWorldWf (proj s) = true →
      let q := (action (Internal.subtreeOpsM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh)).run s
      fsWorldWf (proj q.2) = true ∧
      (proj s).tempSeq ≤ (proj q.2).tempSeq ∧
      ∃ tr,
        HealthyFilesSteps (proj s).env tr (proj q.2).env ∧
        TraceFds [dh] tr [dh] ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        exceptPred q.1 (fun a => okPred a dh tr) (fun e => errPred e dh tr))
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (Internal.withSubtreeM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) rootPath action).run s
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok a => SubtreeConfinedTrace rootPath tr (fun rootDh trInner => okPred a rootDh trInner)
      | .error e =>
        SubtreeErrTrace rootPath e tr ∨
        SubtreeConfinedTrace rootPath tr (fun rootDh trInner => errPred e rootDh trInner) := by
  unfold Internal.withSubtreeM
  have hOp := openDirPure_trace hCap rootPath DEFAULT_EINTR_FUEL hWf
  cases hRo : (SysBridge.openDirPure cap.files rootPath DEFAULT_EINTR_FUEL s) with
  | mk oRes s1 =>
    rw [StateT.run] at hOp; rw [hRo] at hOp; dsimp only at hOp
    obtain ⟨hWf1, hTmp1, trO, hStO, hAllO, hOutO⟩ := hOp
    have hRo' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).openDir rootPath s = (oRes, s1) := hRo
    simp only [Bind.bind, StateT.bind, StateT.run, hRo']
    cases oRes with
    | error e =>
      simp only [Pure.pure, StateT.pure]
      obtain ⟨hFdO, hNlO, hCaseO⟩ := hOutO
      refine ⟨trO, ⟨hWf1, hStO, hFdO, by omega⟩, Or.inl ⟨hNlO, ?_⟩⟩
      rcases hCaseO with hInv | hNe
      · exact Or.inl hInv
      · exact Or.inr (Or.inl ⟨hNe, hAllO⟩)
    | ok dh =>
      dsimp only
      obtain ⟨hFdO, hMemO⟩ := hOutO
      let bodyM : StateM W (Except FsError α) := do
        match ← (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).fstatDir dh with
        | .error e => pure (.error e)
        | .ok info =>
          if info.kind != .dir then
            pure (.error { kind := .notADirectory, path := some rootPath, message := s!"not a directory: {rootPath}" })
          else if (info.mode / 256) % 2 == 0 || (info.mode / 64) % 2 == 0 then
            pure (.error { kind := .permissionDenied, path := some rootPath, message := s!"permission denied: {rootPath}" })
          else
            action (Internal.subtreeOpsM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh)
      have hBrEq : (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh bodyM).run s1 =
          ((bodyM.run s1).1, (((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).closeDir dh).run (bodyM.run s1).2).2) :=
        sysBracketCloseDirM_run (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh bodyM s1
      have hFs := dirOps_fstatDir_trace hCap dh [dh] hWf1
      cases hRf : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).fstatDir dh s1) with
      | mk fRes s2 =>
        rw [StateT.run] at hFs; rw [hRf] at hFs; dsimp only at hFs
        obtain ⟨hWf2, hTmp2, trF, hStF, hFdF, hConfF, hOutF⟩ := hFs
        have hBodyRun : bodyM s1 =
            (match fRes with
             | .error e => (Except.error e, s2)
             | .ok info =>
               if info.kind != .dir then
                 (Except.error { kind := .notADirectory, path := some rootPath, message := s!"not a directory: {rootPath}" }, s2)
               else if (info.mode / 256) % 2 == 0 || (info.mode / 64) % 2 == 0 then
                 (Except.error { kind := .permissionDenied, path := some rootPath, message := s!"permission denied: {rootPath}" }, s2)
               else
                 action (Internal.subtreeOpsM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh) s2) := by
          simp only [bodyM, Bind.bind, StateT.bind, hRf]
          cases fRes with
          | error e => rfl
          | ok info =>
            by_cases hNd : (info.kind != .dir) = true
            · simp [hNd, Pure.pure, StateT.pure]
            · by_cases hPm : ((info.mode / 256) % 2 == 0 || (info.mode / 64) % 2 == 0) = true <;>
                simp [hNd, hPm, Pure.pure, StateT.pure]
        have hCloseWrap : ∀ {rVal : Except FsError α} {sEnd : W} {trIn : List KernelStep},
            bodyM s1 = (rVal, sEnd) →
            fsWorldWf (proj sEnd) = true →
            (proj s).tempSeq ≤ (proj sEnd).tempSeq →
            HealthyFilesSteps (proj s1).env trIn (proj sEnd).env →
            TraceFds [dh] trIn [dh] →
            (∀ step ∈ trIn, SubtreeConfinedReq step.1) →
            (match rVal with
             | .ok a => okPred a dh trIn
             | .error e => nonLockErrOk e ∨ errPred e dh trIn) →
            let p := (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh bodyM) s1
            ∃ tr,
              FsWorldTrace (proj s) tr (proj p.2) ∧
              match p.1 with
              | .ok a => SubtreeConfinedTrace rootPath tr (fun rootDh trInner => okPred a rootDh trInner)
              | .error e =>
                SubtreeErrTrace rootPath e tr ∨
                SubtreeConfinedTrace rootPath tr (fun rootDh trInner => errPred e rootDh trInner) := by
          intro rVal sEnd trIn hB hWfE hSeqE hStIn hFdIn hConfIn hPostIn
          have hCc := closeCheck_trace hCap dh none [] hWfE
          cases hRc : (SysBridge.closeCheck cap.files dh none sEnd) with
          | mk cRes s3 =>
            rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
            obtain ⟨hWf3, hTmp3, _, co, hStC, hFdC, _⟩ := hCc
            have hRc' : (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).closeDir dh sEnd = (cRes, s3) := hRc
            have hBrVal : (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh bodyM) s1 = (rVal, s3) := by
              rw [show (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh bodyM) s1 =
                  (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh bodyM).run s1 from rfl, hBrEq]
              simp only [StateT.run, hB, hRc']
            dsimp only; rw [hBrVal]; dsimp only
            have hTrAll : FsWorldTrace (proj s) (trO ++ trIn ++ [(.close dh, co)]) (proj s3) :=
              ⟨hWf3, healthyFilesSteps_append (healthyFilesSteps_append hStO hStIn) hStC,
               traceFds_append (traceFds_append hFdO hFdIn) hFdC, by omega⟩
            cases rVal with
            | ok a =>
              exact ⟨_, hTrAll, dh, trO, trIn, [(.close dh, co)], rfl, hMemO, hAllO, hFdIn, hConfIn, ⟨co, rfl⟩, hPostIn⟩
            | error e =>
              rcases hPostIn with hNl | hEp
              · exact ⟨_, hTrAll, Or.inl ⟨hNl, Or.inr (Or.inr ⟨dh, trO, trIn, [(.close dh, co)], rfl, hMemO, hAllO, hFdIn, hConfIn, ⟨co, rfl⟩, trivial⟩)⟩⟩
              · exact ⟨_, hTrAll, Or.inr ⟨dh, trO, trIn, [(.close dh, co)], rfl, hMemO, hAllO, hFdIn, hConfIn, ⟨co, rfl⟩, hEp⟩⟩
        have hF : ∀ (a b : StateM W (Except FsError α)), a = b →
            (let p := (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh b) s1
             ∃ tr, FsWorldTrace (proj s) tr (proj p.2) ∧
               match p.1 with
               | .ok x => SubtreeConfinedTrace rootPath tr (fun rootDh trInner => okPred x rootDh trInner)
               | .error e => SubtreeErrTrace rootPath e tr ∨ SubtreeConfinedTrace rootPath tr (fun rootDh trInner => errPred e rootDh trInner)) →
            (let p := (Internal.bracketCloseDirM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh a) s1
             ∃ tr, FsWorldTrace (proj s) tr (proj p.2) ∧
               match p.1 with
               | .ok x => SubtreeConfinedTrace rootPath tr (fun rootDh trInner => okPred x rootDh trInner)
               | .error e => SubtreeErrTrace rootPath e tr ∨ SubtreeConfinedTrace rootPath tr (fun rootDh trInner => errPred e rootDh trInner)) := by
          rintro _ _ rfl h; exact h
        refine hF _ bodyM (funext fun s0 => ?_) ?_
        · simp only [bodyM, Bind.bind, StateT.bind]
          cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).fstatDir dh s0 with
          | mk r0 _ =>
            cases r0 with
            | error _ => rfl
            | ok info =>
              by_cases hNd : (info.kind != .dir) = true
              · simp [hNd]
              · simp only [hNd, Bool.false_eq_true, ↓reduceIte]
        cases fRes with
        | error fe =>
          exact hCloseWrap hBodyRun hWf2 (by omega) hStF hFdF hConfF (Or.inl hOutF)
        | ok info =>
          by_cases hNd : (info.kind != .dir) = true
          · simp only [hNd, ↓reduceIte] at hBodyRun
            exact hCloseWrap hBodyRun hWf2 (by omega) hStF hFdF hConfF
              (Or.inl ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩)
          · by_cases hPm : ((info.mode / 256) % 2 == 0 || (info.mode / 64) % 2 == 0) = true
            · simp only [hNd, Bool.false_eq_true, ↓reduceIte, hPm] at hBodyRun
              exact hCloseWrap hBodyRun hWf2 (by omega) hStF hFdF hConfF
                (Or.inl ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩)
            · simp only [hNd, Bool.false_eq_true, ↓reduceIte, hPm] at hBodyRun
              have hA := hAct dh hWf2
              cases hRa : (action (Internal.subtreeOpsM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh) s2) with
              | mk aRes sEnd =>
                rw [StateT.run] at hA; rw [hRa] at hA; dsimp only at hA
                obtain ⟨hWfE, hSeqE, trA, hStA, hFdA, hConfA, hOutA⟩ := hA
                rw [hRa] at hBodyRun
                refine hCloseWrap hBodyRun hWfE (by omega) (healthyFilesSteps_append hStF hStA)
                  (traceFds_append hFdF hFdA) (confined_append hConfF hConfA) ?_
                cases aRes with
                | ok a => exact hOkMono a dh trF trA hOutA
                | error e => exact Or.inr (hErrMono e dh trF trA hOutA)

/-- Lift a confined `nonLockErrOk` witness to `SubtreeErrTrace`. -/
theorem nonLockErr_to_subtreeErr {rootPath : String} {e : FsError} {tr : List KernelStep}
    (h : SubtreeErrTrace rootPath e tr ∨ SubtreeConfinedTrace rootPath tr (fun _ _ => nonLockErrOk e)) :
    SubtreeErrTrace rootPath e tr := by
  rcases h with h1 | h2
  · exact h1
  · obtain ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hNl⟩ := h2
    exact ⟨hNl, Or.inr (Or.inr ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, trivial⟩)⟩

/-- Confined step refinement for `SubtreeOpReq.lstat`. -/
theorem subtree_lstat_step {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (rootPath : String) (rel : RelPath) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerFromHealthyFilesM cap) ⟨rootPath, .lstat rel⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .lstat rel⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerFromHealthyFilesM, Internal.mkSubtreeOpenerM,
    Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun st rootDh trInner =>
      match splitLastAux rel.segments [] with
      | none => FstatTrace rootDh st trInner
      | some (_, leaf) => ∃ d, StatTrace (some d) leaf.val.toUTF8 false st trInner)
    (fun e _ _ => nonLockErrOk e)
    (fun st dh tr1 tr2 h => by
      cases hSp : splitLastAux rel.segments [] with
      | none => rw [hSp] at h; obtain ⟨rawSt, hm, heq⟩ := h; exact ⟨rawSt, List.mem_append_right _ hm, heq⟩
      | some pair => rw [hSp] at h; obtain ⟨d, rawSt, hm, heq⟩ := h; exact ⟨d, rawSt, List.mem_append_right _ hm, heq⟩)
    (fun _ _ _ _ h => h) (·.lstat rel)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        have hFs := dirOps_fstatDir_trace hCap dh [dh] hW0
        cases hR : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).fstatDir dh s0) with
        | mk res s1 =>
          simp only [StateT.run, hR] at hFs ⊢
          obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hFs
          exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, by cases res <;> exact hOut⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun _ => none)
          (fun parDh st tr => StatTrace (some parDh) pair.2.val.toUTF8 false st tr)
          (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
          (fun parDh => (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2)
          (fun parDh held sX hWX => by
            have hL := dirOps_lstatAt_trace hCap parDh pair.2 held hWX
            cases hRl : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2 sX) with
            | mk rL sY =>
              simp only [StateT.run, hRl] at hL ⊢
              obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hL
              exact ⟨hWfY, by omega, tr, hSt, hConf, by cases rL with | ok st => exact ⟨hFd, hOut⟩ | error e => exact ⟨hFd, hOut.1⟩⟩)
          true dh [dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh pair.1
            (fun parDh => (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2) s0) with
        | mk res s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2) s0 = (res, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hD
          simp only [StateT.run, hRd]
          refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
          cases res with
          | error e => exact hOut.2
          | ok st =>
            obtain ⟨_, d, sub, ⟨pre, post, rfl⟩, rawSt, hm, heq⟩ := hOut
            exact ⟨d, rawSt, by simpa using List.mem_append_left post (List.mem_append_right pre hm), heq⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) rootPath (·.lstat rel) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok st => exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

/-- Confined step refinement for `SubtreeOpReq.readRegular`. -/
theorem subtree_readRegular_step {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (rootPath : String) (rel : RelPath) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerFromHealthyFilesM cap) ⟨rootPath, .readRegular rel⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .readRegular rel⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerFromHealthyFilesM, Internal.mkSubtreeOpenerM,
    Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun bs _ trInner =>
      ∃ pre leaf d sub, splitLastAux rel.segments [] = some (pre, leaf) ∧
        Subtrace sub trInner ∧ ReadRegularTrace (some d) leaf.val.toUTF8 readAtOpenFlags bs sub)
    (fun e _ _ => nonLockErrOk e)
    (fun bs _ tr1 tr2 ⟨pre, leaf, d, sub, hSp, hSub, hR⟩ =>
      ⟨pre, leaf, d, sub, hSp, subtrace_append_right tr1 hSub, hR⟩)
    (fun _ _ _ _ h => h) (·.readRegular rel)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        have hFs := dirOps_fstatDir_trace hCap dh [dh] hW0
        cases hR : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).fstatDir dh s0) with
        | mk res s1 =>
          rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
          obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hFs
          simp only [Bind.bind, StateT.bind, StateT.run, hR]
          cases res with
          | error e => simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, hOut⟩
          | ok info =>
            by_cases hDir : (info.kind == .dir) = true
            · simp only [hDir, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, ⟨by simp, by intro h; cases h⟩⟩
            · simp only [hDir, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun _ => none)
          (fun parDh bs tr => ReadRegularTrace (some parDh) pair.2.val.toUTF8 readAtOpenFlags bs tr)
          (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
          (fun parDh => (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).readRegularAt parDh pair.2)
          (fun parDh held sX hWX => by
            have hRr := readRegularAtPure_trace hCap parDh pair.2 held DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL hWX
            cases hRo : (SysBridge.readRegularAtPure cap.files parDh pair.2 DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL sX) with
            | mk rL sY =>
              simp only [SysBridge.mkRawDirOpsM, StateT.run, hRo] at hRr ⊢
              obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hRr
              exact ⟨hWfY, by omega, tr, hSt, hConf, by cases rL <;> exact ⟨hFd, hOut⟩⟩)
          true dh [dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh pair.1
            (fun parDh => (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).readRegularAt parDh pair.2) s0) with
        | mk res s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).readRegularAt parDh pair.2) s0 = (res, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hD
          simp only [StateT.run, hRd]
          refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
          cases res with
          | error e => exact hOut.2
          | ok bs =>
            obtain ⟨_, d, sub, hSub, hRead⟩ := hOut
            exact ⟨pair.1, pair.2, d, sub, rfl, hSub, hRead⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) rootPath (·.readRegular rel) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok bs => exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

/-- Confined step refinement for `SubtreeOpReq.atomicWriteBytes`. -/
theorem subtree_atomicWriteBytes_step {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (rootPath : String) (rel : RelPath) (data : ByteArray) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerFromHealthyFilesM cap) ⟨rootPath, .atomicWriteBytes rel data⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .atomicWriteBytes rel data⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerFromHealthyFilesM, Internal.mkSubtreeOpenerM,
    Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun _ _ trInner =>
      ∃ pre leaf d, ∃ tmp : EntryName, ∃ sub1 sub2,
        splitLastAux rel.segments [] = some (pre, leaf) ∧
        Subtrace (sub1 ++ sub2) trInner ∧
        WriteFileTrace (some d) tmp.val.toUTF8 createNewOpenFlags 0o644 data sub1 ∧
        RenameTrace (some d) tmp.val.toUTF8 (some d) leaf.val.toUTF8 sub2)
    (fun e _ _ => nonLockErrOk e)
    (fun _ _ tr1 tr2 ⟨pre, leaf, d, tmp, sub1, sub2, hSp, hSub, hWr, hRn⟩ =>
      ⟨pre, leaf, d, tmp, sub1, sub2, hSp, subtrace_append_right tr1 hSub, hWr, hRn⟩)
    (fun _ _ _ _ h => h) (·.atomicWriteBytes rel data)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun _ => none)
          (fun parDh _ tr =>
            ∃ tmp : EntryName, ∃ sub1 sub2, Subtrace (sub1 ++ sub2) tr ∧
              WriteFileTrace (some parDh) tmp.val.toUTF8 createNewOpenFlags 0o644 data sub1 ∧
              RenameTrace (some parDh) tmp.val.toUTF8 (some parDh) pair.2.val.toUTF8 sub2)
          (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
          (fun parDh => Internal.atomicWriteAtAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) parDh pair.2 data 16)
          (fun parDh held sX hWX => by
            have hA := atomicWriteAtAuxM_trace hCap parDh pair.2 data held 16 hWX
            cases hRa : (Internal.atomicWriteAtAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) parDh pair.2 data 16 sX) with
            | mk rA sY =>
              simp only [StateT.run, hRa] at hA ⊢
              obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hA
              exact ⟨hWfY, hTmpY, tr, hSt, hConf, by cases rA with | ok u => cases u; exact ⟨hFd, hOut⟩ | error e => exact ⟨hFd, hOut⟩⟩)
          true dh [dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh pair.1
            (fun parDh => Internal.atomicWriteAtAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) parDh pair.2 data 16) s0) with
        | mk res s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1
              (fun parDh => Internal.atomicWriteAtAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) parDh pair.2 data 16) s0 = (res, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hD
          simp only [StateT.run, hRd]
          refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
          cases res with
          | error e => exact hOut.2
          | ok u =>
            cases u
            obtain ⟨_, d, sub, hSub, tmp, sub1, sub2, hSub12, hWr, hRn⟩ := hOut
            exact ⟨pair.1, pair.2, d, tmp, sub1, sub2, rfl, subtrace_trans hSub12 hSub, hWr, hRn⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) rootPath (·.atomicWriteBytes rel data) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok u => cases u; exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

/-- Confined step refinement for `SubtreeOpReq.mkdir`. -/
theorem subtree_mkdir_step {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (rootPath : String) (rel : RelPath) (parents existOk : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerFromHealthyFilesM cap) ⟨rootPath, .mkdir rel parents existOk⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .mkdir rel parents existOk⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerFromHealthyFilesM, Internal.mkSubtreeOpenerM,
    Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun _ rootDh trInner =>
      match splitLastAux rel.segments [] with
      | none => existOk = true ∧ ∃ rawSt, (.fstat rootDh, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir
      | some (_, leaf) =>
        ∃ d, MkdirTrace (some d) leaf.val.toUTF8 0o755 trInner ∨
          (existOk = true ∧ ∃ rawSt, (.fstatat (some d) leaf.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir))
    (fun e _ _ => nonLockErrOk e)
    (fun _ dh tr1 tr2 h => by
      cases hSp : splitLastAux rel.segments [] with
      | none => rw [hSp] at h; exact ⟨h.1, let ⟨rawSt, hm, hd⟩ := h.2; ⟨rawSt, List.mem_append_right _ hm, hd⟩⟩
      | some pair =>
        rw [hSp] at h; obtain ⟨d, hCase⟩ := h; refine ⟨d, ?_⟩
        rcases hCase with hMk | ⟨hEx, rawSt, hm, hd⟩
        · exact Or.inl (List.mem_append_right _ hMk)
        · exact Or.inr ⟨hEx, rawSt, List.mem_append_right _ hm, hd⟩)
    (fun _ _ _ _ h => h) (·.mkdir rel parents existOk)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        have hFs := dirOps_fstatDir_trace hCap dh [dh] hW0
        cases hR : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).fstatDir dh s0) with
        | mk res s1 =>
          rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
          obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hFs
          simp only [Bind.bind, StateT.bind, StateT.run, hR]
          cases res with
          | error e => simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, hOut⟩
          | ok info =>
            by_cases hNd : (info.kind != .dir) = true
            · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, ⟨by simp, by intro h; cases h⟩⟩
            · cases existOk with
              | false => simp only [hNd, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, ⟨by simp, by intro h; cases h⟩⟩
              | true =>
                simp only [hNd, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                obtain ⟨rawSt, hm, hEqSt⟩ := hOut
                have hKindDir : rawSt.kind = .dir := by
                  have hK : info.kind = .dir := by cases hIk : info.kind <;> rw [hIk] at hNd <;> first | rfl | exact absurd (by decide) hNd
                  rw [hEqSt] at hK; dsimp only [toFileStat] at hK
                  cases hRk : rawSt.kind <;> rw [hRk] at hK <;> first | rfl | cases hK
                exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, trivial, rawSt, hm, hKindDir⟩
      | some pair =>
        let leafAct : HandleId → StateM W (Except FsError Unit) := fun parDh => do
          match ← (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt parDh pair.2 with
          | .ok () => pure (.ok ())
          | .error e =>
            if existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
              match ← (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2 with
              | .error _ => pure (.error e)
              | .ok info =>
                if info.kind == .dir then pure (.ok ())
                else if e.kind == .alreadyExists then pure (.error e)
                else pure (.error { kind := .alreadyExists, path := some pair.2.val, message := s!"already exists: {pair.2.val}" })
            else pure (.error e)
        have hLeaf : ∀ (parDh : HandleId) (held : List HandleId) {sX : W}, fsWorldWf (proj sX) = true →
            let q := (leafAct parDh).run sX
            fsWorldWf (proj q.2) = true ∧ (proj sX).tempSeq ≤ (proj q.2).tempSeq ∧
            ∃ tr, HealthyFilesSteps (proj sX).env tr (proj q.2).env ∧ TraceFds held tr held ∧
              (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
              match q.1 with
              | .ok () =>
                MkdirTrace (some parDh) pair.2.val.toUTF8 0o755 tr ∨
                (existOk = true ∧ ∃ rawSt, (.fstatat (some parDh) pair.2.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir)
              | .error e => nonLockErrOk e := by
          intro parDh held sX hWX
          dsimp only [leafAct]
          have hCr := dirOps_createDirAt_trace hCap parDh pair.2 held hWX
          cases hRc : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt parDh pair.2 sX) with
          | mk cRes s1 =>
            rw [StateT.run] at hCr; rw [hRc] at hCr; dsimp only at hCr
            obtain ⟨hWf1, hTmp1, trC, hStC, hFdC, hConfC, hOutC⟩ := hCr
            simp only [Bind.bind, StateT.bind, StateT.run, hRc]
            cases cRes with
            | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, trC, hStC, hFdC, hConfC, Or.inl hOutC⟩
            | error e =>
              by_cases hEx : (existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied)) = true
              · have hExT : existOk = true := (Bool.and_eq_true _ _).mp hEx |>.1
                simp only [hEx, ↓reduceIte]
                have hLs := dirOps_lstatAt_trace hCap parDh pair.2 held hWf1
                cases hRl : ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2 s1) with
                | mk lRes s2 =>
                  rw [StateT.run] at hLs; rw [hRl] at hLs; dsimp only at hLs
                  obtain ⟨hWf2, hTmp2, trL, hStL, hFdL, hConfL, hOutL⟩ := hLs
                  simp only [Bind.bind, StateT.bind, hRl]
                  have hStCL := healthyFilesSteps_append hStC hStL
                  have hFdCL := traceFds_append hFdC hFdL
                  have hConfCL := confined_append hConfC hConfL
                  cases lRes with
                  | error _ => simp only [Pure.pure, StateT.pure]; exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, hOutC⟩
                  | ok info =>
                    by_cases hDir : (info.kind == .dir) = true
                    · simp only [hDir, ↓reduceIte, Pure.pure, StateT.pure]
                      obtain ⟨rawSt, hm, hEqSt⟩ := hOutL
                      have hKindDir : rawSt.kind = .dir := by
                        have hK : info.kind = .dir := by cases hIk : info.kind <;> rw [hIk] at hDir <;> first | rfl | exact absurd hDir (by decide)
                        rw [hEqSt] at hK; dsimp only [toFileStat] at hK
                        cases hRk : rawSt.kind <;> rw [hRk] at hK <;> first | rfl | cases hK
                      exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, Or.inr ⟨hExT, rawSt, List.mem_append_right _ hm, hKindDir⟩⟩
                    · by_cases hAe : (e.kind == .alreadyExists) = true
                      · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hAe, Pure.pure, StateT.pure]
                        exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, hOutC⟩
                      · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hAe, Pure.pure, StateT.pure]
                        exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩⟩
              · simp only [hEx, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf1, by omega, trC, hStC, hFdC, hConfC, hOutC⟩
        cases parents with
        | true =>
          simp only [↓reduceIte]
          refine subAct_subst
            (r2 := ((Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1 leafAct).run s0).1)
            (s2 := ((Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1 leafAct).run s0).2) ?_ ?_
          · exact congrArg (fun f => (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1 f).run s0)
              (funext fun parDh => funext fun sX => by
                simp only [leafAct, Bind.bind, StateT.bind]
                cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt parDh pair.2 sX with
                | mk r0 sA =>
                  cases r0 with
                  | ok u => cases u; rfl
                  | error e =>
                    by_cases hEx : (existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied)) = true
                    · simp only [hEx, ↓reduceIte]
                      cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2 sA with
                      | mk r1 _ => cases r1 with | error _ => rfl | ok _ => rfl
                    · simp only [hEx, Bool.false_eq_true, ↓reduceIte])
          · have hMw := mkdirWalkM_trace hCap
              (fun parDh tr => MkdirTrace (some parDh) pair.2.val.toUTF8 0o755 tr ∨
                (existOk = true ∧ ∃ rawSt, (.fstatat (some parDh) pair.2.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir))
              leafAct hLeaf true dh [dh] pair.1 hW0
            cases hRm : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1 leafAct s0) with
            | mk res s1 =>
              simp only [StateT.run, hRm, ↓reduceIte] at hMw ⊢
              obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hMw
              refine ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, ?_⟩
              cases res with
              | error e => exact hOut
              | ok u =>
                cases u; obtain ⟨d, sub, ⟨pre, post, rfl⟩, hCase⟩ := hOut; refine ⟨d, ?_⟩
                rcases hCase with hMk | ⟨hEx, rawSt, hm, hd⟩
                · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ hMk))
                · exact Or.inr ⟨hEx, rawSt, List.mem_append_left _ (List.mem_append_right _ hm), hd⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine subAct_subst
            (r2 := ((Internal.walkDescendM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh pair.1 leafAct).run s0).1)
            (s2 := ((Internal.walkDescendM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh pair.1 leafAct).run s0).2) ?_ ?_
          · exact congrArg (fun f => (Internal.walkDescendM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh pair.1 f).run s0)
              (funext fun parDh => funext fun sX => by
                simp only [leafAct, Bind.bind, StateT.bind]
                cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt parDh pair.2 sX with
                | mk r0 sA =>
                  cases r0 with
                  | ok u => cases u; rfl
                  | error e =>
                    by_cases hEx : (existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied)) = true
                    · simp only [hEx, ↓reduceIte]
                      cases (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt parDh pair.2 sA with
                      | mk r1 _ => cases r1 with | error _ => rfl | ok _ => rfl
                    · simp only [hEx, Bool.false_eq_true, ↓reduceIte])
          · have hWd := walkDescendAuxM_trace hCap (fun _ => none)
              (fun parDh _ tr => MkdirTrace (some parDh) pair.2.val.toUTF8 0o755 tr ∨
                (existOk = true ∧ ∃ rawSt, (.fstatat (some parDh) pair.2.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir))
              (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h) leafAct
              (fun parDh held sX hWX => by
                have hL := hLeaf parDh held hWX
                cases hRl : leafAct parDh sX with
                | mk rL sY =>
                  simp only [StateT.run, hRl] at hL ⊢
                  obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hL
                  exact ⟨hWfY, hTmpY, tr, hSt, hConf, by cases rL with | ok u => cases u; exact ⟨hFd, hOut⟩ | error e => exact ⟨hFd, hOut⟩⟩)
              true dh [dh] pair.1 hW0
            cases hRw : (Internal.walkDescendM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) dh pair.1 leafAct s0) with
            | mk res s1 =>
              have hRw' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) true dh pair.1 leafAct s0 = (res, s1) := hRw
              rw [StateT.run] at hWd; rw [hRw'] at hWd; simp only [↓reduceIte] at hWd
              obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hWd
              simp only [StateT.run, hRw]
              refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
              cases res with
              | error e => exact hOut.2
              | ok u =>
                cases u; obtain ⟨_, d, sub, ⟨pre, post, rfl⟩, hCase⟩ := hOut; refine ⟨d, ?_⟩
                rcases hCase with hMk | ⟨hEx, rawSt, hm, hd⟩
                · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ hMk))
                · exact Or.inr ⟨hEx, rawSt, List.mem_append_left _ (List.mem_append_right _ hm), hd⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq) rootPath (·.mkdir rel parents existOk) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok u => cases u; exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

end LeanSwe.Fs.Proofs
