import LeanSweProofs.Process.Proofs.SysBridge.WaitAndReap

/-!
`spawnOsPhase` and `spawnPure` behavioral, process-slot conservation, and `openFds`
descriptor conservation laws for `LeanSwe.Process.Proofs.SysBridge`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

theorem spawnOsPhase_laws {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd)
    (hDeps : RefinesHealthySysDeps getTbl setTbl openFds deps)
    (eintrFuel : Nat) (s₀ : S) (req : ExecRequest) :
    let sp := (SysBridge.spawnOsPhase deps eintrFuel req).run s₀
    (∀ err, sp.1 = .error err →
      getTbl sp.2 = getTbl s₀ ∧
      openFds sp.2 = openFds s₀ ∧
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) ∧
    (∀ slot, sp.1 = .ok slot →
      getTbl sp.2 = getTbl s₀ ∧
      0 < slot.pid.toNat ∧ 0 < slot.pgid.toNat ∧
      ∃ errR outR inW,
        errR ≠ outR ∧ errR ≠ inW ∧ outR ≠ inW ∧
        slot.stdinFd? = optFdOf inW true ∧
        slot.stdoutFd? = optFdOf outR true ∧
        slot.stderrFd? = optFdOf errR true ∧
        openFds sp.2 = pipePrefix errR outR inW true true true (openFds s₀)) := by
  dsimp only
  let proj := fun s : S => (getTbl s, openFds s)
  have hCloseT : ∀ s h, getTbl ((deps.files.close h).run s).2 = getTbl s :=
    fun s h => (hDeps.close_frame s h).1
  have hCloseO : ∀ s h, openFds ((deps.files.close h).run s).2 = (openFds s).erase h :=
    fun s h => (hDeps.close_frame s h).2.1
  have hCloseSome : ∀ (x : fd) (st : S),
      let r := (Files.closeOpt deps.files (some x)).run st
      getTbl r.2 = getTbl st ∧ openFds r.2 = (openFds st).erase x := by
    intro x st
    unfold Files.closeOpt
    rw [stateT_bind_eq]
    exact ⟨hCloseT st x, hCloseO st x⟩
  have hStatP : ∀ s dir p fl, proj ((deps.files.fstatat dir p fl).run s).2 = proj s :=
    fun s dir p fl => Prod.ext (hDeps.fstatat_frame s dir p fl).1 (hDeps.fstatat_frame s dir p fl).2.1
  have hAccP : ∀ s dir p m fl, proj ((deps.files.faccessat dir p m fl).run s).2 = proj s :=
    fun s dir p m fl => Prod.ext (hDeps.faccessat_frame s dir p m fl).1 (hDeps.faccessat_frame s dir p m fl).2.1
  have hPipeRetry : ∀ s,
      let r := (LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s
      getTbl r.2 = getTbl s ∧
      (∀ e, r.1 = .error e → openFds r.2 = openFds s) ∧
      (∀ rf wf, r.1 = .ok (rf, wf) →
        rf ≠ wf ∧ rf ∉ openFds s ∧ wf ∉ openFds s ∧ openFds r.2 = wf :: rf :: openFds s) := by
    intro s
    exact retryEintr_pipe2_spec getTbl openFds (deps.proc.pipe2 { cloexec := true })
      (fun st =>
        let hp := hDeps.pipe2_frame st { cloexec := true }
        ⟨hp.1, fun e he => (hp.2.1 e he).1, hp.2.2⟩)
      eintrFuel s
  unfold SysBridge.spawnOsPhase
  by_cases hInv : SysBridge.isInvalidSpawnRequest req = true
  · rw [ite_eq_left hInv]
    dsimp only [pure, StateT.pure, StateT.run]
    refine ⟨?_, (by intro _ h; cases h)⟩
    intro err hEq; injection hEq with hE; rw [← hE]
    refine ⟨rfl, rfl, mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
  · rw [ite_eq_right hInv]
    rw [stateT_bind_eq]
    obtain ⟨hFcwdP, hEcwd⟩ := validateWorkingDir_spec proj deps.files hStatP hAccP req.cwd eintrFuel s₀
    let s0c := ((SysBridge.validateWorkingDir deps.files req.cwd eintrFuel).run s₀).2
    have hFs0c : getTbl s0c = getTbl s₀ := congrArg Prod.fst hFcwdP
    have hOs0c : openFds s0c = openFds s₀ := congrArg Prod.snd hFcwdP
    cases hCwdRes : ((SysBridge.validateWorkingDir deps.files req.cwd eintrFuel).run s₀).1 with
    | error cwdErr =>
      dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨?_, (by intro _ h; cases h)⟩
      intro err hEq; injection hEq with hE; rw [← hE]
      exact ⟨hFs0c, hOs0c, hEcwd cwdErr hCwdRes⟩
    | ok _ =>
      dsimp only
      have hEnvStep :
          ∃ baseRes s1,
            (SysBridge.readBaseEnv deps req.inheritEnv).run s0c = (baseRes, s1) ∧
            getTbl s1 = getTbl s₀ ∧
            openFds s1 = openFds s₀ ∧
            (∀ e, baseRes = .error e →
              e.kind ≠ .timedOut ∧ e.kind ≠ .outputLimitExceeded ∧ e.kind ≠ .terminatedBySignal) := by
        unfold SysBridge.readBaseEnv
        cases req.inheritEnv
        · exact ⟨.ok #[], s0c, rfl, hFs0c, hOs0c, (by intro _ h; cases h)⟩
        · obtain ⟨hFeT, hFeO, hKe⟩ := hDeps.listAmbientEnv_frame s0c
          exact ⟨_, _, rfl, hFeT.trans hFs0c, hFeO.trans hOs0c, hKe⟩
      rcases hEnvStep with ⟨baseRes, s1, hRunEnv, hFs1, hOs1, hErrEnv⟩
      rw [stateT_bind_eq, hRunEnv]
      cases baseRes with
      | error envErr =>
        dsimp only [pure, StateT.pure, StateT.run]
        refine ⟨?_, (by intro _ h; cases h)⟩
        intro err hEq; injection hEq with hE; rw [← hE]
        obtain ⟨hk1, hk2, hk3⟩ := hErrEnv envErr rfl
        have hkEq : (SysBridge.ensureNonEmptyMsg "failed to read environment" envErr).kind = envErr.kind := by
          unfold SysBridge.ensureNonEmptyMsg; split <;> rfl
        refine ⟨hFs1, hOs1, ensureNonEmptyMsg_ne_empty _ _ (by decide), ?_, ?_, ?_⟩ <;> rw [hkEq]
        · exact hk1
        · exact hk2
        · exact hk3
      | ok baseEnv =>
        dsimp only
        rw [stateT_bind_eq]
        let envBytes := SysBridge.mergeRawEnvOverrides baseEnv req.env
        obtain ⟨hFresP, hEres⟩ := resolveExecutablePath_spec proj deps.files hStatP hAccP
          req.program req.cwd envBytes eintrFuel s1
        let s2 := ((SysBridge.resolveExecutablePath deps.files req.program req.cwd envBytes eintrFuel).run s1).2
        have hFs2 : getTbl s2 = getTbl s₀ := (congrArg Prod.fst hFresP).trans hFs1
        have hOs2 : openFds s2 = openFds s₀ := (congrArg Prod.snd hFresP).trans hOs1
        cases hResP : ((SysBridge.resolveExecutablePath deps.files req.program req.cwd envBytes eintrFuel).run s1).1 with
        | error resErr =>
          dsimp only [pure, StateT.pure, StateT.run]
          refine ⟨?_, (by intro _ h; cases h)⟩
          intro err hEq; injection hEq with hE; rw [← hE]
          exact ⟨hFs2, hOs2, hEres resErr hResP⟩
        | ok resolvedPath =>
          dsimp only
          split
          · dsimp only [pure, StateT.pure, StateT.run]
            refine ⟨?_, (by intro _ h; cases h)⟩
            intro err hEq; injection hEq with hE; subst hE
            refine ⟨hFs2, hOs2, mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
          · rw [stateT_bind_eq]
            obtain ⟨hTp1, hEp1, hOkp1⟩ := hPipeRetry s2
            let s3 := ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s2).2
            have hFs3 : getTbl s3 = getTbl s₀ := hTp1.trans hFs2
            cases hP1 : ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s2).1 with
            | error e1 =>
              dsimp only [pure, StateT.pure, StateT.run]
              refine ⟨?_, (by intro _ h; cases h)⟩
              intro err hEq; injection hEq with hE; subst hE
              exact ⟨hFs3, (hEp1 e1 hP1).trans hOs2, mapErrno_kind_and_msg (some req.program) "pipe2" e1⟩
            | ok p1 =>
              rcases p1 with ⟨inR, inW⟩
              obtain ⟨hNe1, _, _, hOp1⟩ := hOkp1 inR inW hP1
              rw [hOs2] at hOp1
              dsimp only
              rw [stateT_bind_eq]
              obtain ⟨hTp2, hEp2, hOkp2⟩ := hPipeRetry s3
              let s4 := ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s3).2
              have hFs4 : getTbl s4 = getTbl s₀ := hTp2.trans hFs3
              cases hP2 : ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s3).1 with
              | error e2 =>
                dsimp only
                rw [stateT_bind_eq, stateT_bind_eq]
                dsimp only [pure, StateT.pure, StateT.run]
                have hOs4 : openFds s4 = inW :: inR :: openFds s₀ := (hEp2 e2 hP2).trans hOp1
                obtain ⟨hTc1, hOc1⟩ := hCloseSome inR s4
                obtain ⟨hTc2, hOc2⟩ := hCloseSome inW _
                have hOEnd : openFds ((Files.closeOpt deps.files (some inW)).run
                    ((Files.closeOpt deps.files (some inR)).run s4).2).2 = openFds s₀ := by
                  rw [hOc2, hOc1, hOs4, erase_two_fresh hNe1]
                refine ⟨?_, (by intro _ h; cases h)⟩
                intro err hEq; injection hEq with hE; subst hE
                exact ⟨hTc2.trans (hTc1.trans hFs4), hOEnd, mapErrno_kind_and_msg (some req.program) "pipe2" e2⟩
              | ok p2 =>
                rcases p2 with ⟨outR, outW⟩
                obtain ⟨hNe2, hNr2, hNw2, hOp2⟩ := hOkp2 outR outW hP2
                rw [hOp1] at hNr2 hNw2 hOp2
                dsimp only
                rw [stateT_bind_eq]
                obtain ⟨hTp3, hEp3, hOkp3⟩ := hPipeRetry s4
                let s5 := ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s4).2
                have hFs5 : getTbl s5 = getTbl s₀ := hTp3.trans hFs4
                cases hP3 : ((LinuxSyscall.retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel).run s4).1 with
                | error e3 =>
                  dsimp only
                  rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                  dsimp only [pure, StateT.pure, StateT.run]
                  have hOs5 : openFds s5 = outW :: outR :: inW :: inR :: openFds s₀ := (hEp3 e3 hP3).trans hOp2
                  obtain ⟨hTc1, hOc1⟩ := hCloseSome inR s5
                  obtain ⟨hTc2, hOc2⟩ := hCloseSome inW _
                  obtain ⟨hTc3, hOc3⟩ := hCloseSome outR _
                  obtain ⟨hTc4, hOc4⟩ := hCloseSome outW _
                  have hOEnd : openFds ((Files.closeOpt deps.files (some outW)).run
                      ((Files.closeOpt deps.files (some outR)).run
                        ((Files.closeOpt deps.files (some inW)).run
                          ((Files.closeOpt deps.files (some inR)).run s5).2).2).2).2 = openFds s₀ := by
                    rw [hOc4, hOc3, hOc2, hOc1, hOs5, erase_four_fresh hNe1 hNe2 hNr2 hNw2]
                  refine ⟨?_, (by intro _ h; cases h)⟩
                  intro err hEq; injection hEq with hE; subst hE
                  exact ⟨hTc4.trans (hTc3.trans (hTc2.trans (hTc1.trans hFs5))),
                    hOEnd, mapErrno_kind_and_msg (some req.program) "pipe2" e3⟩
                | ok p3 =>
                  rcases p3 with ⟨errR, errW⟩
                  obtain ⟨hNe3, hNr3, hNw3, hOp3⟩ := hOkp3 errR errW hP3
                  rw [hOp2] at hNr3 hNw3 hOp3
                  dsimp only
                  rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                  let childSpec : PostFork.ChildSpecM fd :=
                    { path := resolvedPath
                      argv := #[PostFork.ArgToken.lit req.program] ++ req.args.map PostFork.ArgToken.lit
                      cwd := req.cwd
                      env := #[]
                      rawEnv := envBytes
                      stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
                      fdPolicy := .inheritNonCloexec #[]
                      closeFds := #[.handle inW, .handle outR, .handle errR]
                      processGroup := .newGroup
                      sigpipe := .resetDefault
                      forkMode := .direct }
                  obtain ⟨hFpfT, hFpfO⟩ := hDeps.postFork_frame s5 childSpec
                  let spf := (deps.postFork.spawn childSpec).run s5
                  obtain ⟨hTcC1, hOcC1⟩ := hCloseSome inR spf.2
                  obtain ⟨hTcC2, hOcC2⟩ := hCloseSome outW _
                  obtain ⟨hTcC3, hOcC3⟩ := hCloseSome errW _
                  let s6 := ((Files.closeOpt deps.files (some errW)).run
                    ((Files.closeOpt deps.files (some outW)).run
                      ((Files.closeOpt deps.files (some inR)).run spf.2).2).2).2
                  have hFcChild : getTbl s6 = getTbl s₀ :=
                    hTcC3.trans (hTcC2.trans (hTcC1.trans (hFpfT.trans hFs5)))
                  obtain ⟨hChildErase, hEO, hEI, hOI⟩ :=
                    erase_child_ends_six hNe1 hNe2 hNe3 hNr2 hNw2 hNr3 hNw3
                  have hOcChild : openFds s6 = errR :: outR :: inW :: openFds s₀ := by
                    dsimp only [s6]
                    rw [hOcC3, hOcC2, hOcC1, hFpfO, hOp3, hChildErase]
                  cases hPfRes : spf.1 with
                  | error pfErr =>
                    dsimp only
                    rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                    dsimp only [pure, StateT.pure, StateT.run]
                    obtain ⟨hTcP1, hOcP1⟩ := hCloseSome inW s6
                    obtain ⟨hTcP2, hOcP2⟩ := hCloseSome outR _
                    obtain ⟨hTcP3, hOcP3⟩ := hCloseSome errR _
                    have hOPar : openFds ((Files.closeOpt deps.files (some errR)).run
                        ((Files.closeOpt deps.files (some outR)).run
                          ((Files.closeOpt deps.files (some inW)).run s6).2).2).2 = openFds s₀ := by
                      rw [hOcP3, hOcP2, hOcP1, hOcChild, erase_parent_ends_three hEO hEI hOI]
                    refine ⟨?_, (by intro _ h; cases h)⟩
                    intro err hEq; injection hEq with hE; subst hE
                    exact ⟨hTcP3.trans (hTcP2.trans (hTcP1.trans hFcChild)),
                      hOPar, mapPostForkError_kind_and_msg req pfErr⟩
                  | ok child =>
                    dsimp only
                    let rawPgid := child.pgid.getD child.pid
                    by_cases hBadPid : (child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID || rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID) = true
                    · rw [ite_eq_left hBadPid]
                      rw [stateT_bind_eq, stateT_bind_eq, stateT_bind_eq]
                      dsimp only [pure, StateT.pure, StateT.run]
                      obtain ⟨hTcP1, hOcP1⟩ := hCloseSome inW s6
                      obtain ⟨hTcP2, hOcP2⟩ := hCloseSome outR _
                      obtain ⟨hTcP3, hOcP3⟩ := hCloseSome errR _
                      have hOPar : openFds ((Files.closeOpt deps.files (some errR)).run
                          ((Files.closeOpt deps.files (some outR)).run
                            ((Files.closeOpt deps.files (some inW)).run s6).2).2).2 = openFds s₀ := by
                        rw [hOcP3, hOcP2, hOcP1, hOcChild, erase_parent_ends_three hEO hEI hOI]
                      refine ⟨?_, (by intro _ h; cases h)⟩
                      intro err hEq; injection hEq with hE; rw [← hE]
                      refine ⟨hTcP3.trans (hTcP2.trans (hTcP1.trans hFcChild)),
                        hOPar, mapRawError_message_ne_empty _, ?_, ?_, ?_⟩ <;> simp [SysBridge.mapRawError]
                    · rw [ite_eq_right hBadPid]
                      dsimp only [pure, StateT.pure, StateT.run]
                      refine ⟨(by intro _ h; cases h), ?_⟩
                      intro slot hEq
                      injection hEq with hSub
                      rw [← hSub]
                      dsimp only
                      have hPidNe0 : child.pid ≠ 0 := fun hz => hBadPid (by simp [hz])
                      have hPgidNe0 : rawPgid ≠ 0 := fun hz => hBadPid (by simp [hz])
                      have hPidPos : 0 < child.pid.toNat :=
                        Nat.pos_of_ne_zero fun hz =>
                          hPidNe0 (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hz))
                      have hPgidPos : 0 < rawPgid.toNat :=
                        Nat.pos_of_ne_zero fun hz =>
                          hPgidNe0 (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hz))
                      exact ⟨hFcChild, hPidPos, hPgidPos, errR, outR, inW, hEO, hEI, hOI,
                        rfl, rfl, rfl, hOcChild⟩

theorem spawnPure_laws {S fd : Type} [DecidableEq fd]
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S)
    (openFds : S → List fd)
    (deps : SysDepsM (StateM S) fd)
    (hDeps : RefinesHealthySysDeps getTbl setTbl openFds deps)
    (eintrFuel : Nat) (s₀ : S) (req : ExecRequest) :
    let sp := (SysBridge.spawnPure deps (SysBridge.stateProcTableOps getTbl setTbl) eintrFuel req).run s₀
    (∀ err, sp.1 = .error err →
      getTbl sp.2 = getTbl s₀ ∧
      openFds sp.2 = openFds s₀ ∧
      err.message ≠ "" ∧
      err.kind ≠ .timedOut ∧ err.kind ≠ .outputLimitExceeded ∧ err.kind ≠ .terminatedBySignal) ∧
    (∀ h, sp.1 = .ok h →
      h.pid > 0 ∧ h.pgid > 0 ∧
      ∃ errR outR inW slot,
        errR ≠ outR ∧ errR ≠ inW ∧ outR ≠ inW ∧
        slot.stdinFd? = optFdOf inW true ∧
        slot.stdoutFd? = optFdOf outR true ∧
        slot.stderrFd? = optFdOf errR true ∧
        openFds sp.2 = pipePrefix errR outR inW true true true (openFds s₀) ∧
        getTbl sp.2 = { nextId := h.handleId + 1, slots := (h.handleId, slot) :: (getTbl s₀).slots }) := by
  dsimp only
  have hOs := spawnOsPhase_laws getTbl setTbl openFds deps hDeps eintrFuel s₀ req
  unfold SysBridge.spawnPure
  rw [stateT_bind_eq]
  cases hOsRun : (SysBridge.spawnOsPhase deps eintrFuel req).run s₀ with
  | mk osRes s6 =>
    rw [hOsRun] at hOs
    cases osRes with
    | error err =>
      dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨?_, (by intro _ h; cases h)⟩
      intro err' hEq
      injection hEq with hE
      rw [← hE]
      exact hOs.1 err rfl
    | ok newSlot =>
      dsimp only
      obtain ⟨hFcChild, hPidPos, hPgidPos, errR, outR, inW, hEO, hEI, hOI, hIn, hOut, hErr, hOcChild⟩ :=
        hOs.2 newSlot rfl
      rw [stateT_bind_eq]
      have hIns : ((SysBridge.stateProcTableOps getTbl setTbl).insertSlot newSlot).run s6 =
          ((getTbl s₀).nextId, setTbl s6 (SysBridge.insertSlotPure (getTbl s₀) newSlot).2) := by
        dsimp only [SysBridge.stateProcTableOps, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, StateT.run]
        rw [hFcChild]
        rfl
      rw [hIns]
      dsimp only [pure, StateT.pure, StateT.run]
      refine ⟨(by intro _ h; cases h), ?_⟩
      intro hOutH hEq
      injection hEq with hSub
      rw [← hSub]
      dsimp only
      refine ⟨Int.ofNat_lt.mpr hPidPos, Int.ofNat_lt.mpr hPgidPos,
        errR, outR, inW, newSlot, hEO, hEI, hOI, hIn, hOut, hErr, ?_, ?_⟩
      · rw [hDeps.openFds_set, hOcChild]
      · rw [hDeps.get_set]; rfl

end LeanSwe.Process.Proofs
