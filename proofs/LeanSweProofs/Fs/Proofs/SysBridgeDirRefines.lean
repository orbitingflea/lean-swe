import LeanSweProofs.Fs.Proofs.SysBridgeDirSub2

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Confined step refinement for `SubtreeOpReq.withFileLock`. -/
theorem subtree_withFileLock_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) (mode : LockMode) (createIfMissing : Bool)
    (actRes : Except FsError Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .withFileLock rel mode createIfMissing actRes⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .withFileLock rel mode createIfMissing actRes⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun v _ trInner =>
      actRes = .ok v ∧
      ∃ pre leaf d sub, splitLastAux rel.segments [] = some (pre, leaf) ∧
        Subtrace sub trInner ∧ FileLockTrace (some d) leaf.val.toUTF8 mode false true sub)
    (fun e _ trInner =>
      nonLockErrOk e ∨
      (actRes = .error e ∧
        ∃ pre leaf d sub, splitLastAux rel.segments [] = some (pre, leaf) ∧
          Subtrace sub trInner ∧ FileLockTrace (some d) leaf.val.toUTF8 mode false false sub))
    (fun v _ tr1 tr2 ⟨hEq, pre, leaf, d, sub, hSp, hSub, hFl⟩ =>
      ⟨hEq, pre, leaf, d, sub, hSp, subtrace_append_right tr1 hSub, hFl⟩)
    (fun e _ tr1 tr2 h => match h with
      | Or.inl hNl => Or.inl hNl
      | Or.inr ⟨hEq, pre, leaf, d, sub, hSp, hSub, hFl⟩ =>
        Or.inr ⟨hEq, pre, leaf, d, sub, hSp, subtrace_append_right tr1 hSub, hFl⟩)
    (·.withFileLock rel mode createIfMissing (pure actRes))
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM, internal_splitLastAux_eq_model]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, Or.inl ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun h => some h)
          (fun parDh h tr =>
            ∃ rawSt fl modeArg trO trL,
              tr = trO ++ trL ∧ fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
              (.openat (some parDh) pair.2.val.toUTF8 fl modeArg, .opened (hidOf h)) ∈ trO ∧
              (.fstat (hidOf h), .statted rawSt) ∈ trL ∧ rawSt.kind = .reg ∧
              (.flock (hidOf h) (lockModeToFlockOp mode false), .unit) ∈ trL)
          (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
          (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).acquireLockAt parDh pair.2 mode createIfMissing false)
          (fun parDh held sX hWX => by
            have hA := acquireLockAtPure_trace hCap parDh pair.2 mode createIfMissing false held DEFAULT_EINTR_FUEL hWX
            cases hRa : (SysBridge.acquireLockAtPure files parDh pair.2 mode createIfMissing false DEFAULT_EINTR_FUEL sX) with
            | mk rA sY =>
              simp only [SysBridge.mkRawDirOpsM, StateT.run, hRa] at hA ⊢
              obtain ⟨hWfY, hTmpY, hOut⟩ := hA
              cases rA with
              | ok h =>
                obtain ⟨rawSt, fl, modeArg, trO, trL, hSt, hFdO, hFdL, hConf, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩ := hOut
                exact ⟨hWfY, by omega, trO ++ trL, hSt, hConf, traceFds_append hFdO hFdL,
                  rawSt, fl, modeArg, trO, trL, rfl, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩
              | error e =>
                obtain ⟨tr, hSt, hFd, hConf, hCase⟩ := hOut
                rcases hCase with hNl | ⟨_, hF, _⟩
                · exact ⟨hWfY, by omega, tr, hSt, hConf, hFd, hNl⟩
                · cases hF)
          true dh [hidOf dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1
            (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).acquireLockAt parDh pair.2 mode createIfMissing false) s0) with
        | mk rLock s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).acquireLockAt parDh pair.2 mode createIfMissing false) s0 = (rLock, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hD
          simp only [Bind.bind, StateT.bind, StateT.run, hRd]
          cases rLock with
          | error e =>
            simp only [Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, tr1, hSt1, hOut1.1, hConf1, Or.inl hOut1.2⟩
          | ok lockH =>
            dsimp only
            obtain ⟨hFd1, d, sub, hSub, rawSt, fl, modeArg, trO, trL, hSubEq, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩ := hOut1
            have hBr := bracketDirLockM_pure_run (SysBridge.mkRawDirOpsM files nextNonce) lockH actRes s1
            have hRel := releaseLockPure_trace hCap lockH [hidOf dh] DEFAULT_EINTR_FUEL hWf1
            cases hRr : (SysBridge.releaseLockPure files lockH DEFAULT_EINTR_FUEL s1) with
            | mk rRes s2 =>
              rw [StateT.run] at hRel; rw [hRr] at hRel; dsimp only at hRel
              obtain ⟨hWf2, hTmp2, trRel, hStR, hFdR, hConfR, ⟨uo, hMemU, hUOk⟩, ⟨co, hMemC⟩, hErrR⟩ := hRel
              have hRelEq : ((SysBridge.mkRawDirOpsM files nextNonce).releaseLock lockH).run s1 = (rRes, s2) := hRr
              rw [hRelEq] at hBr; simp only [StateT.run] at hBr
              rw [hBr]; dsimp only
              obtain ⟨pre, post, hTr1Eq⟩ := hSub
              have hStAll := healthyFilesSteps_append hSt1 hStR
              have hFdAll := traceFds_append hFd1 hFdR
              have hConfAll := confined_append hConf1 hConfR
              cases actRes with
              | error ae =>
                have hSubFL : Subtrace (trO ++ trL ++ (post ++ trRel)) (tr1 ++ trRel) :=
                  ⟨pre, [], by rw [hTr1Eq, hSubEq]; simp [List.append_assoc]⟩
                exact ⟨hWf2, by omega, tr1 ++ trRel, hStAll, hFdAll, hConfAll,
                  Or.inr ⟨rfl, pair.1, pair.2, d, trO ++ trL ++ (post ++ trRel), rfl, hSubFL,
                    hidOf lockH, rawSt, fl, modeArg, trO, trL, post ++ trRel, rfl, hAcc, hNf, hCl, hNb,
                    hMemO, hMemFs, hReg, hMemFl, ⟨uo, by simp [hMemU], fun hc => by cases hc⟩, co, by simp [hMemC]⟩⟩
              | ok v =>
                cases rRes with
                | error re => exact ⟨hWf2, by omega, tr1 ++ trRel, hStAll, hFdAll, hConfAll, Or.inl hErrR⟩
                | ok u =>
                  cases u
                  have hSubFL : Subtrace (trO ++ trL ++ (post ++ trRel)) (tr1 ++ trRel) :=
                    ⟨pre, [], by rw [hTr1Eq, hSubEq]; simp [List.append_assoc]⟩
                  exact ⟨hWf2, by omega, tr1 ++ trRel, hStAll, hFdAll, hConfAll,
                    rfl, pair.1, pair.2, d, trO ++ trL ++ (post ++ trRel), rfl, hSubFL,
                    hidOf lockH, rawSt, fl, modeArg, trO, trL, post ++ trRel, rfl, hAcc, hNf, hCl, hNb,
                    hMemO, hMemFs, hReg, hMemFl, ⟨uo, by simp [hMemU], fun _ => hUOk rfl⟩, co, by simp [hMemC]⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath
      (·.withFileLock rel mode createIfMissing (pure actRes)) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    cases res with
    | ok v =>
      obtain ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hActEq, hBody⟩ := hOut
      exact ⟨tr, hTr, hActEq, dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hBody⟩
    | error e =>
      rcases hOut with hErr | ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hCase⟩
      · exact ⟨tr, hTr, Or.inl hErr⟩
      · rcases hCase with hNl | ⟨hActEq, hBody⟩
        · exact ⟨tr, hTr, Or.inl ⟨hNl, Or.inr (Or.inr ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, trivial⟩)⟩⟩
        · exact ⟨tr, hTr, Or.inr ⟨hActEq, dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hBody⟩⟩

/-- Confined step refinement for `SubtreeOpReq.tryWithFileLock`. -/
theorem subtree_tryWithFileLock_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) (mode : LockMode) (createIfMissing : Bool)
    (actRes : Except FsError Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .tryWithFileLock rel mode createIfMissing actRes⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .tryWithFileLock rel mode createIfMissing actRes⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun opt _ trInner =>
      match opt with
      | none =>
        ∃ pre leaf d sub, splitLastAux rel.segments [] = some (pre, leaf) ∧
          Subtrace sub trInner ∧ TryLockContendedTrace (some d) leaf.val.toUTF8 mode sub
      | some v =>
        actRes = .ok v ∧
        ∃ pre leaf d sub, splitLastAux rel.segments [] = some (pre, leaf) ∧
          Subtrace sub trInner ∧ FileLockTrace (some d) leaf.val.toUTF8 mode true true sub)
    (fun e _ trInner =>
      nonLockErrOk e ∨
      (actRes = .error e ∧
        ∃ pre leaf d sub, splitLastAux rel.segments [] = some (pre, leaf) ∧
          Subtrace sub trInner ∧ FileLockTrace (some d) leaf.val.toUTF8 mode true false sub))
    (fun opt _ tr1 tr2 h => by
      cases opt with
      | none => obtain ⟨pre, leaf, d, sub, hSp, hSub, hCt⟩ := h; exact ⟨pre, leaf, d, sub, hSp, subtrace_append_right tr1 hSub, hCt⟩
      | some v => obtain ⟨hEq, pre, leaf, d, sub, hSp, hSub, hFl⟩ := h; exact ⟨hEq, pre, leaf, d, sub, hSp, subtrace_append_right tr1 hSub, hFl⟩)
    (fun e _ tr1 tr2 h => match h with
      | Or.inl hNl => Or.inl hNl
      | Or.inr ⟨hEq, pre, leaf, d, sub, hSp, hSub, hFl⟩ =>
        Or.inr ⟨hEq, pre, leaf, d, sub, hSp, subtrace_append_right tr1 hSub, hFl⟩)
    (·.tryWithFileLock rel mode createIfMissing (pure actRes))
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM, internal_splitLastAux_eq_model]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, Or.inl ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun h => some h)
          (fun parDh h tr =>
            ∃ rawSt fl modeArg trO trL,
              tr = trO ++ trL ∧ fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
              (.openat (some parDh) pair.2.val.toUTF8 fl modeArg, .opened (hidOf h)) ∈ trO ∧
              (.fstat (hidOf h), .statted rawSt) ∈ trL ∧ rawSt.kind = .reg ∧
              (.flock (hidOf h) (lockModeToFlockOp mode true), .unit) ∈ trL)
          (fun e tr => nonLockErrOk e ∨
            (e.kind = .wouldBlock ∧ ∃ d sub, Subtrace sub tr ∧ TryLockContendedTrace (some d) pair.2.val.toUTF8 mode sub))
          (fun _ _ _ hSub h => match h with
            | Or.inl hNl => Or.inl hNl
            | Or.inr ⟨hWb, d, sub, hS, hCt⟩ => Or.inr ⟨hWb, d, sub, subtrace_trans hS hSub, hCt⟩)
          (fun _ _ hNl _ => Or.inl hNl)
          (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).acquireLockAt parDh pair.2 mode createIfMissing true)
          (fun parDh held sX hWX => by
            have hA := acquireLockAtPure_trace hCap parDh pair.2 mode createIfMissing true held DEFAULT_EINTR_FUEL hWX
            cases hRa : (SysBridge.acquireLockAtPure files parDh pair.2 mode createIfMissing true DEFAULT_EINTR_FUEL sX) with
            | mk rA sY =>
              simp only [SysBridge.mkRawDirOpsM, StateT.run, hRa] at hA ⊢
              obtain ⟨hWfY, hTmpY, hOut⟩ := hA
              cases rA with
              | ok h =>
                obtain ⟨rawSt, fl, modeArg, trO, trL, hSt, hFdO, hFdL, hConf, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩ := hOut
                exact ⟨hWfY, by omega, trO ++ trL, hSt, hConf, traceFds_append hFdO hFdL,
                  rawSt, fl, modeArg, trO, trL, rfl, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩
              | error e =>
                obtain ⟨tr, hSt, hFd, hConf, hCase⟩ := hOut
                rcases hCase with hNl | ⟨hWb, _, hCt⟩
                · exact ⟨hWfY, by omega, tr, hSt, hConf, hFd, Or.inl hNl⟩
                · exact ⟨hWfY, by omega, tr, hSt, hConf, hFd, Or.inr ⟨hWb, hidOf parDh, tr, subtrace_refl tr, hCt⟩⟩)
          true dh [hidOf dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1
            (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).acquireLockAt parDh pair.2 mode createIfMissing true) s0) with
        | mk rLock s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).acquireLockAt parDh pair.2 mode createIfMissing true) s0 = (rLock, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hD
          simp only [Bind.bind, StateT.bind, StateT.run, hRd]
          cases rLock with
          | error e =>
            obtain ⟨hFd1, hErrCase⟩ := hOut1
            by_cases hWb : (e.kind == .wouldBlock) = true
            · simp only [hWb, ↓reduceIte, Pure.pure, StateT.pure]
              rcases hErrCase with hNl | ⟨_, d, sub, hSub, hCt⟩
              · exact False.elim (hNl.2 ((fsErrorKind_beq_iff_eq _ _).mp hWb))
              · exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, pair.1, pair.2, d, sub, rfl, hSub, hCt⟩
            · simp only [hWb, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
              rcases hErrCase with hNl | ⟨hWbEq, _⟩
              · exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, Or.inl hNl⟩
              · exact False.elim (hWb ((fsErrorKind_beq_iff_eq _ _).mpr hWbEq))
          | ok lockH =>
            dsimp only
            obtain ⟨hFd1, d, sub, hSub, rawSt, fl, modeArg, trO, trL, hSubEq, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩ := hOut1
            let mappedRes : Except FsError (Option Nat) := match actRes with | .ok a => .ok (some a) | .error e => .error e
            have hBr := bracketDirLockM_pure_run (SysBridge.mkRawDirOpsM files nextNonce) lockH mappedRes s1
            have hRel := releaseLockPure_trace hCap lockH [hidOf dh] DEFAULT_EINTR_FUEL hWf1
            cases hRr : (SysBridge.releaseLockPure files lockH DEFAULT_EINTR_FUEL s1) with
            | mk rRes s2 =>
              rw [StateT.run] at hRel; rw [hRr] at hRel; dsimp only at hRel
              obtain ⟨hWf2, hTmp2, trRel, hStR, hFdR, hConfR, ⟨uo, hMemU, hUOk⟩, ⟨co, hMemC⟩, hErrR⟩ := hRel
              have hRelEq : ((SysBridge.mkRawDirOpsM files nextNonce).releaseLock lockH).run s1 = (rRes, s2) := hRr
              rw [hRelEq] at hBr; simp only [StateT.run] at hBr
              refine subAct_subst
                (r2 := (Internal.bracketDirLockM (SysBridge.mkRawDirOpsM files nextNonce) lockH (pure mappedRes) s1).1)
                (s2 := (Internal.bracketDirLockM (SysBridge.mkRawDirOpsM files nextNonce) lockH (pure mappedRes) s1).2) ?_ ?_
              · exact congrArg (a₂ := pure mappedRes)
                  (fun m => Internal.bracketDirLockM (SysBridge.mkRawDirOpsM files nextNonce) lockH m s1)
                  (funext fun sX => by cases actRes <;> rfl)
              · rw [hBr]; dsimp only
                obtain ⟨pre, post, hTr1Eq⟩ := hSub
                have hStAll := healthyFilesSteps_append hSt1 hStR
                have hFdAll := traceFds_append hFd1 hFdR
                have hConfAll := confined_append hConf1 hConfR
                cases actRes with
                | error ae =>
                  have hSubFL : Subtrace (trO ++ trL ++ (post ++ trRel)) (tr1 ++ trRel) :=
                    ⟨pre, [], by rw [hTr1Eq, hSubEq]; simp [List.append_assoc]⟩
                  exact ⟨hWf2, by omega, tr1 ++ trRel, hStAll, hFdAll, hConfAll,
                    Or.inr ⟨rfl, pair.1, pair.2, d, trO ++ trL ++ (post ++ trRel), rfl, hSubFL,
                      hidOf lockH, rawSt, fl, modeArg, trO, trL, post ++ trRel, rfl, hAcc, hNf, hCl, hNb,
                      hMemO, hMemFs, hReg, hMemFl, ⟨uo, List.mem_append_right _ hMemU, fun hc => by cases hc⟩, co, List.mem_append_right _ hMemC⟩⟩
                | ok v =>
                  cases rRes with
                  | error re => exact ⟨hWf2, by omega, tr1 ++ trRel, hStAll, hFdAll, hConfAll, Or.inl hErrR⟩
                  | ok u =>
                    cases u
                    have hSubFL : Subtrace (trO ++ trL ++ (post ++ trRel)) (tr1 ++ trRel) :=
                      ⟨pre, [], by rw [hTr1Eq, hSubEq]; simp [List.append_assoc]⟩
                    exact ⟨hWf2, by omega, tr1 ++ trRel, hStAll, hFdAll, hConfAll,
                      rfl, pair.1, pair.2, d, trO ++ trL ++ (post ++ trRel), rfl, hSubFL,
                      hidOf lockH, rawSt, fl, modeArg, trO, trL, post ++ trRel, rfl, hAcc, hNf, hCl, hNb,
                      hMemO, hMemFs, hReg, hMemFl, ⟨uo, List.mem_append_right _ hMemU, fun _ => hUOk rfl⟩, co, List.mem_append_right _ hMemC⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath
      (·.tryWithFileLock rel mode createIfMissing (pure actRes)) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    cases res with
    | ok opt =>
      cases opt with
      | none => exact ⟨tr, hTr, hOut⟩
      | some v =>
        obtain ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hActEq, hBody⟩ := hOut
        exact ⟨tr, hTr, hActEq, dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hBody⟩
    | error e =>
      rcases hOut with hErr | ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hCase⟩
      · exact ⟨tr, hTr, Or.inl hErr⟩
      · rcases hCase with hNl | ⟨hActEq, hBody⟩
        · exact ⟨tr, hTr, Or.inl ⟨hNl, Or.inr (Or.inr ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, trivial⟩)⟩⟩
        · exact ⟨tr, hTr, Or.inr ⟨hActEq, dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hBody⟩⟩

/-- End-to-end descriptor-confined refinement of `Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)` against `allowedSubtreeStep` directly over `RefinesFsFilesFixed`. -/
theorem refinesSubtree_of_refinesFilesFixed
    {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce) :
    Core.ObeysStep proj Model.fsWorldWf
      (Model.execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)))
      Model.allowedSubtreeStep := by
  intro s req hWf
  rcases req with ⟨rootPath, op⟩
  cases op with
  | lstat rel => exact subtree_lstat_step hCap rootPath rel hWf
  | readRegular rel => exact subtree_readRegular_step hCap rootPath rel hWf
  | atomicWriteBytes rel data => exact subtree_atomicWriteBytes_step hCap rootPath rel data hWf
  | mkdir rel parents existOk => exact subtree_mkdir_step hCap rootPath rel parents existOk hWf
  | unlink rel missingOk => exact subtree_unlink_step hCap rootPath rel missingOk hWf
  | rmdir rel => exact subtree_rmdir_step hCap rootPath rel hWf
  | rmtree rel ignoreMissing => exact subtree_rmtree_step hCap rootPath rel ignoreMissing hWf
  | symlink target rel => exact subtree_symlink_step hCap rootPath target rel hWf
  | listDir rel => exact subtree_listDir_step hCap rootPath rel hWf
  | walk rel => exact subtree_walk_step hCap rootPath rel hWf
  | withFileLock rel mode createIfMissing actRes =>
    exact subtree_withFileLock_step hCap rootPath rel mode createIfMissing actRes hWf
  | tryWithFileLock rel mode createIfMissing actRes =>
    exact subtree_tryWithFileLock_step hCap rootPath rel mode createIfMissing actRes hWf

end LeanSwe.Fs.Proofs
