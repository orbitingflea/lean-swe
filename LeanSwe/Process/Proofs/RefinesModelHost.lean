import LeanSwe.Process.Proofs.RefinesModelHostSpawn
import LeanSwe.Process.Proofs.RefinesModelHostLoops
import LeanSwe.Process.Proofs.RefinesModelHostWaitLoops

/-!
End-to-end `Impl + SysBridge` capability refinement over `Model.HealthyHostCapsM`
(`refinesStepFrom_mkApiFromHostCapsM`).
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

private theorem awaitOutputPure_refines_host {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (h : ProcessHandle)
    (stdin : ByteArray) (timeoutMs? maxOutputBytes? : Option Nat) :
    let r := (SysBridge.awaitOutputPure (hostDepsOf cap) cap.table
      DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL h stdin timeoutMs? maxOutputBytes?).run w
    Model.hostWorldWf (proj r.2) = true ∧
    Model.allowedAwaitCore (Model.hostWorldToProcessState (proj w)) h timeoutMs? maxOutputBytes?
      r.1 (Model.hostWorldToProcessState (proj r.2)) := by
  unfold SysBridge.awaitOutputPure
  dsimp only [hostDepsOf]
  rw [hostStateT_bind_run]
  have hTk := capTbl_takeSlotIo_step proj cap hCap w hWf h.handleId
  cases hTkRun : (cap.table.takeSlotIo h.handleId).run w with
  | mk tkRes w1 =>
    rw [hTkRun] at hTk
    obtain ⟨hWf1, hNext1, hMap1, hFilt1, hMem1⟩ := hTk
    cases tkRes with
    | none =>
      rw [hostStateT_pure_run]
      exact ⟨hWf1, hostWorldWf_implies_processStateWf hWf1, hNext1, hMap1, hFilt1,
        mapRawError_userError_isNonOutcome _⟩
    | some tup =>
      rcases tup with ⟨pid, inFd0?, outFd0?, errFd0?⟩
      have hMem := hMem1 _ rfl
      dsimp only
      rw [hostStateT_bind_run]
      have hSetup : let r := (SysBridge.setupStdinPipe cap.files stdin inFd0?).run w1
          Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w1).tbl := by
        unfold SysBridge.setupStdinPipe
        split
        · rw [hostStateT_bind_run, hostStateT_pure_run]
          exact hostCloseOpt_frame proj cap hCap inFd0? w1 hWf1
        · cases inFd0? with
          | none => rw [hostStateT_pure_run]; exact ⟨hWf1, rfl⟩
          | some inFd =>
            rw [hostStateT_bind_run, hostStateT_pure_run]
            exact execFiles_fcntl_frame proj cap hCap w1 hWf1 inFd (.setFl true false)
      cases hSetRun : (SysBridge.setupStdinPipe cap.files stdin inFd0?).run w1 with
      | mk inFd? w2 =>
        rw [hSetRun] at hSetup
        dsimp only
        rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run]
        have hNb1 := hostSetNonblockingOpt_frame proj cap hCap outFd0? w2 hSetup.1
        have hNb2 := hostSetNonblockingOpt_frame proj cap hCap errFd0?
          (Files.setNonblockingOpt cap.files outFd0? |>.run w2).2 hNb1.1
        let w3 := (Files.setNonblockingOpt cap.files errFd0? |>.run
          (Files.setNonblockingOpt cap.files outFd0? |>.run w2).2).2
        have hStart : let r := (SysBridge.readStartMsOpt cap.timeRand timeoutMs?).run w3
            Model.hostWorldWf (proj r.2) = true ∧ (proj r.2).tbl = (proj w3).tbl ∧
            (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
          unfold SysBridge.readStartMsOpt
          cases timeoutMs? with
          | none => rw [hostStateT_pure_run]; exact ⟨hNb2.1, rfl, fun _ h => by cases h⟩
          | some _ =>
            rw [hostStateT_bind_run]
            have hM := hostMonoNowMs_frame proj cap hCap w3 hNb2.1
            cases hMRun : (TimeRand.monoNowMs cap.timeRand).run w3 with
            | mk mRes wm =>
              rw [hMRun] at hM
              cases mRes with
              | ok _ => rw [hostStateT_pure_run]; exact ⟨hM.1, hM.2, fun _ h => by cases h⟩
              | error _ => rw [hostStateT_pure_run]; exact ⟨hM.1, hM.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
        cases hStRun : (SysBridge.readStartMsOpt cap.timeRand timeoutMs?).run w3 with
        | mk stRes w4 =>
          rw [hStRun] at hStart
          have hTbl4 : (proj w4).tbl = (proj w1).tbl :=
            hStart.2.1.trans (hNb2.2.trans (hNb1.2.trans hSetup.2))
          cases stRes with
          | error err =>
            dsimp only
            rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
            have hc1 := hostCloseOpt_frame proj cap hCap inFd? w4 hStart.1
            have hc2 := hostCloseOpt_frame proj cap hCap outFd0? (Files.closeOpt cap.files inFd? |>.run w4).2 hc1.1
            have hc3 := hostCloseOpt_frame proj cap hCap errFd0?
              (Files.closeOpt cap.files outFd0? |>.run (Files.closeOpt cap.files inFd? |>.run w4).2).2 hc2.1
            have hTblEnd : (proj (Files.closeOpt cap.files errFd0? |>.run
                (Files.closeOpt cap.files outFd0? |>.run (Files.closeOpt cap.files inFd? |>.run w4).2).2).2).tbl = (proj w1).tbl :=
              hc3.2.trans (hc2.2.trans (hc1.2.trans hTbl4))
            have hStEq := tblEq_to_stateEq hTblEnd
            exact ⟨hc3.1, hostWorldWf_implies_processStateWf hc3.1,
              (congrArg Model.ProcessModelState.nextHandleId hStEq).trans hNext1,
              (by rw [hStEq]; exact hMap1),
              (by rw [hStEq]; exact hFilt1),
              hStart.2.2 _ rfl⟩
          | ok startMs =>
            dsimp only
            rw [hostStateT_bind_run]
            let initSt : SysBridge.StreamLoopState Files.HandleId :=
              { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? }
            have hZeroB : ∀ lim, maxOutputBytes? = some lim → initSt.outLen + initSt.errLen ≤ lim :=
              fun _ _ => Nat.zero_le _
            have hLp := hostStreamPipesLoop_spec proj cap hCap stdin startMs timeoutMs? maxOutputBytes?
              DEFAULT_EINTR_FUEL initSt DEFAULT_IO_FUEL w4 hStart.1 rfl rfl hZeroB
            cases hLpRun : (SysBridge.streamPipesLoop cap.files cap.poll cap.timeRand stdin startMs
                timeoutMs? maxOutputBytes? DEFAULT_EINTR_FUEL initSt DEFAULT_IO_FUEL).run w4 with
            | mk lpRes w5 =>
              rw [hLpRun] at hLp
              have hTbl5 : (proj w5).tbl = (proj w1).tbl := hLp.2.1.trans hTbl4
              have hSt5 := tblEq_to_stateEq hTbl5
              cases lpRes with
              | error err =>
                rw [hostStateT_pure_run]
                exact ⟨hLp.1, hostWorldWf_implies_processStateWf hLp.1,
                  (congrArg Model.ProcessModelState.nextHandleId hSt5).trans hNext1,
                  (by rw [hSt5]; exact hMap1),
                  (by rw [hSt5]; exact hFilt1),
                  hLp.2.2⟩
              | ok phase =>
                have markHelper : ∀ (wk : W) (wf : Bool) (outc : ExecOutcome),
                    Model.hostWorldWf (proj wk) = true →
                    (proj wk).tbl = (proj w1).tbl →
                    Model.allowedAwaitOutcome timeoutMs? maxOutputBytes? outc →
                    let r := (do let ok ← cap.table.markWaited h.handleId wf; if !ok then return .error (SysBridge.mapRawError (.userError "process handle vanished")) else return .ok outc : StateM W (Except ProcessError ExecOutcome)).run wk
                    Model.hostWorldWf (proj r.2) = true ∧
                    Model.allowedAwaitCore (Model.hostWorldToProcessState (proj w)) h timeoutMs? maxOutputBytes?
                      r.1 (Model.hostWorldToProcessState (proj r.2)) := by
                  intro wk wf outc hWfk hTblK hOutc
                  dsimp only
                  rw [hostStateT_bind_run]
                  have hMk := capTbl_markWaited_step proj cap hCap wk hWfk h.handleId wf
                  cases hMkRun : (cap.table.markWaited h.handleId wf).run wk with
                  | mk mkOk wm =>
                    rw [hMkRun] at hMk
                    obtain ⟨hWfm, hNextM, hMapM, hFiltM, _⟩ := hMk
                    have hStK := tblEq_to_stateEq hTblK
                    have hNextM' := hNextM.trans ((congrArg Model.ProcessModelState.nextHandleId hStK).trans hNext1)
                    have hMapM' : (Model.hostWorldToProcessState (proj (mkOk, wm).2)).activeHandles.map (·.handleId) =
                        (Model.hostWorldToProcessState (proj w)).activeHandles.map (·.handleId) :=
                      hMapM.trans (by rw [hStK]; exact hMap1)
                    have hFiltM' : (Model.hostWorldToProcessState (proj (mkOk, wm).2)).activeHandles.filter (·.handleId != h.handleId) =
                        (Model.hostWorldToProcessState (proj w)).activeHandles.filter (·.handleId != h.handleId) :=
                      hFiltM.trans (by rw [hStK]; exact hFilt1)
                    dsimp only
                    cases mkOk with
                    | false =>
                      simp only [Bool.not_false, ↓reduceIte, hostStateT_pure_run]
                      exact ⟨hWfm, hostWorldWf_implies_processStateWf hWfm, hNextM', hMapM', hFiltM',
                        mapRawError_userError_isNonOutcome _⟩
                    | true =>
                      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hostStateT_pure_run]
                      exact ⟨hWfm, hostWorldWf_implies_processStateWf hWfm, hNextM', hMapM', hFiltM', hMem, hOutc⟩
                cases phase with
                | timedOut out err =>
                  exact markHelper w5 false (.timedOut out err) hLp.1 hTbl5 hLp.2.2
                | limitExceeded out err =>
                  exact markHelper w5 false (.outputLimitExceeded out err) hLp.1 hTbl5 hLp.2.2
                | eof out err =>
                  dsimp only
                  cases timeoutMs? with
                  | none =>
                    rw [hostStateT_bind_run]
                    have hWb := hostWaitBlockingLoop_spec proj cap hCap pid.toInt32 out err DEFAULT_EINTR_FUEL w5 hLp.1
                    cases hWbRun : (SysBridge.waitBlockingLoop cap.proc pid.toInt32 out err DEFAULT_EINTR_FUEL).run w5 with
                    | mk wbRes w6 =>
                      rw [hWbRun] at hWb
                      cases wbRes with
                      | error err =>
                        rw [hostStateT_pure_run]
                        have hSt6 := tblEq_to_stateEq (hWb.2.1.trans hTbl5)
                        exact ⟨hWb.1, hostWorldWf_implies_processStateWf hWb.1,
                          (congrArg Model.ProcessModelState.nextHandleId hSt6).trans hNext1,
                          (by rw [hSt6]; exact hMap1),
                          (by rw [hSt6]; exact hFilt1),
                          hWb.2.2⟩
                      | ok outc =>
                        have hOutc : Model.allowedAwaitOutcome none maxOutputBytes? outc := by
                          cases outc with
                          | exited res =>
                            intro lim hLim; obtain ⟨ho, he⟩ := hWb.2.2; rw [ho, he]; exact hLp.2.2 lim hLim
                          | signaled _ _ _ => trivial
                          | timedOut _ _ => exact absurd hWb.2.2 False.elim
                          | outputLimitExceeded _ _ => exact absurd hWb.2.2 False.elim
                        exact markHelper w6 true outc hWb.1 (hWb.2.1.trans hTbl5) hOutc
                  | some timeoutMs =>
                    rw [hostStateT_bind_run]
                    have hWt := hostWaitTimedLoop_spec proj cap hCap pid.toInt32 startMs timeoutMs out err
                      DEFAULT_IO_FUEL w5 hLp.1
                    cases hWtRun : (SysBridge.waitTimedLoop cap.proc cap.timeRand pid.toInt32 startMs timeoutMs out err
                        DEFAULT_IO_FUEL).run w5 with
                    | mk wtRes w6 =>
                      rw [hWtRun] at hWt
                      cases wtRes with
                      | error err =>
                        rw [hostStateT_pure_run]
                        have hSt6 := tblEq_to_stateEq (hWt.2.1.trans hTbl5)
                        exact ⟨hWt.1, hostWorldWf_implies_processStateWf hWt.1,
                          (congrArg Model.ProcessModelState.nextHandleId hSt6).trans hNext1,
                          (by rw [hSt6]; exact hMap1),
                          (by rw [hSt6]; exact hFilt1),
                          hWt.2.2⟩
                      | ok wtPair =>
                        rcases wtPair with ⟨waitedFlag, outc⟩
                        have hOutc : Model.allowedAwaitOutcome (some timeoutMs) maxOutputBytes? outc := by
                          cases outc with
                          | exited res =>
                            intro lim hLim; obtain ⟨ho, he⟩ := hWt.2.2; rw [ho, he]; exact hLp.2.2 lim hLim
                          | signaled _ _ _ => trivial
                          | timedOut _ _ => rfl
                          | outputLimitExceeded _ _ => exact absurd hWt.2.2 False.elim
                        exact markHelper w6 waitedFlag outc hWt.1 (hWt.2.1.trans hTbl5) hOutc

private theorem killProcessGroupPure_refines_host {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (h : ProcessHandle) :
    let r := (SysBridge.killProcessGroupPure (hostDepsOf cap) cap.table DEFAULT_EINTR_FUEL h).run w
    Model.hostWorldWf (proj r.2) = true ∧
    Model.allowedKillGroup (Model.hostWorldToProcessState (proj w)) r.1 (Model.hostWorldToProcessState (proj r.2)) := by
  unfold SysBridge.killProcessGroupPure
  dsimp only [hostDepsOf]
  rw [hostStateT_bind_run]
  have hLk := capTbl_lookupPgid_step proj cap hCap w hWf h.handleId
  cases hLkRun : (cap.table.lookupPgid h.handleId).run w with
  | mk pg? w1 =>
    rw [hLkRun] at hLk
    cases pg? with
    | none =>
      rw [hostStateT_pure_run]
      exact ⟨hLk.1, tblEq_to_stateEq hLk.2, trivial⟩
    | some pgid =>
      dsimp only
      split
      · rw [hostStateT_pure_run]
        exact ⟨hLk.1, tblEq_to_stateEq hLk.2, trivial⟩
      · rw [hostStateT_bind_run]
        let target := LinuxSyscall.Process.killTargetOfPgid pgid
        have hK1 := hostRetryEintr_frame proj (cap.proc.kill target .sigterm)
          (fun x hx => execProc_kill_frame proj cap hCap x hx target .sigterm)
          DEFAULT_EINTR_FUEL w1 hLk.1
        cases hK1Run : (LinuxSyscall.retryEintr (cap.proc.kill target .sigterm) DEFAULT_EINTR_FUEL).run w1 with
        | mk k1 w2 =>
          rw [hK1Run] at hK1
          cases k1 with
          | error e =>
            dsimp only
            split <;> rw [hostStateT_pure_run]
            · exact ⟨hK1.1, tblEq_to_stateEq (hK1.2.trans hLk.2), trivial⟩
            · exact ⟨hK1.1, tblEq_to_stateEq (hK1.2.trans hLk.2), mapErrno_isNonOutcome _ _ _⟩
          | ok _ =>
            dsimp only
            rw [hostStateT_bind_run]
            have hGp := hostKillGraceProbeLoop_frame proj cap hCap target 5 w2 hK1.1
            cases hGpRun : (SysBridge.killGraceProbeLoop cap.proc cap.timeRand target 5).run w2 with
            | mk vanished w3 =>
              rw [hGpRun] at hGp
              dsimp only
              split
              · rw [hostStateT_pure_run]
                exact ⟨hGp.1, tblEq_to_stateEq (hGp.2.trans (hK1.2.trans hLk.2)), trivial⟩
              · rw [hostStateT_bind_run]
                have hK2 := hostRetryEintr_frame proj (cap.proc.kill target .sigkill)
                  (fun x hx => execProc_kill_frame proj cap hCap x hx target .sigkill)
                  DEFAULT_EINTR_FUEL w3 hGp.1
                cases hK2Run : (LinuxSyscall.retryEintr (cap.proc.kill target .sigkill) DEFAULT_EINTR_FUEL).run w3 with
                | mk k2 w4 =>
                  rw [hK2Run] at hK2
                  cases k2 with
                  | ok _ =>
                    rw [hostStateT_pure_run]
                    exact ⟨hK2.1, tblEq_to_stateEq (hK2.2.trans (hGp.2.trans (hK1.2.trans hLk.2))), trivial⟩
                  | error e =>
                    dsimp only
                    split <;> rw [hostStateT_pure_run]
                    · exact ⟨hK2.1, tblEq_to_stateEq (hK2.2.trans (hGp.2.trans (hK1.2.trans hLk.2))), trivial⟩
                    · exact ⟨hK2.1, tblEq_to_stateEq (hK2.2.trans (hGp.2.trans (hK1.2.trans hLk.2))),
                        mapErrno_isNonOutcome _ _ _⟩

private theorem reapPure_refines_host {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (hWf : Model.hostWorldWf (proj w) = true) (h : ProcessHandle) :
    let r := (SysBridge.reapPure (hostDepsOf cap) cap.table DEFAULT_EINTR_FUEL h).run w
    Model.hostWorldWf (proj r.2) = true ∧
    Model.allowedReap (Model.hostWorldToProcessState (proj w)) h r.1 (Model.hostWorldToProcessState (proj r.2)) := by
  unfold SysBridge.reapPure
  dsimp only [hostDepsOf]
  rw [hostStateT_bind_run]
  have hDet := capTbl_detachSlot_step proj cap hCap w hWf h.handleId
  cases hDetRun : (cap.table.detachSlot h.handleId).run w with
  | mk det w1 =>
    rw [hDetRun] at hDet
    obtain ⟨hWf1, hNext1, hAct1⟩ := hDet
    cases det with
    | none =>
      rw [hostStateT_pure_run]
      exact ⟨hWf1, hNext1, hAct1, trivial⟩
    | some slot =>
      dsimp only
      rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run]
      have hc1 := hostCloseOpt_frame proj cap hCap slot.stdinFd? w1 hWf1
      have hc2 := hostCloseOpt_frame proj cap hCap slot.stdoutFd?
        (Files.closeOpt cap.files slot.stdinFd? |>.run w1).2 hc1.1
      have hc3 := hostCloseOpt_frame proj cap hCap slot.stderrFd?
        (Files.closeOpt cap.files slot.stdoutFd? |>.run (Files.closeOpt cap.files slot.stdinFd? |>.run w1).2).2 hc2.1
      let w4 := (Files.closeOpt cap.files slot.stderrFd? |>.run
        (Files.closeOpt cap.files slot.stdoutFd? |>.run (Files.closeOpt cap.files slot.stdinFd? |>.run w1).2).2).2
      have hTbl4 : (proj w4).tbl = (proj w1).tbl := hc3.2.trans (hc2.2.trans hc1.2)
      have hSt4 := tblEq_to_stateEq hTbl4
      split
      · rw [hostStateT_bind_run]
        have hRp := hostWaitpidReapLoop_frame proj cap hCap slot.pid.toInt32 DEFAULT_EINTR_FUEL w4 hc3.1
        cases hRpRun : (LinuxSyscall.Process.waitpidReapLoop cap.proc slot.pid.toInt32 DEFAULT_EINTR_FUEL).run w4 with
        | mk rp w5 =>
          rw [hRpRun] at hRp
          have hSt5 := tblEq_to_stateEq (hRp.2.trans hTbl4)
          have hNext5 := (congrArg Model.ProcessModelState.nextHandleId hSt5).trans hNext1
          have hAct5 := (congrArg Model.ProcessModelState.activeHandles hSt5).trans hAct1
          cases rp with
          | ok _ => rw [hostStateT_pure_run]; exact ⟨hRp.1, hNext5, hAct5, trivial⟩
          | error errOpt =>
            cases errOpt with
            | none => rw [hostStateT_pure_run]; exact ⟨hRp.1, hNext5, hAct5, mapRawError_userError_isNonOutcome _⟩
            | some e => rw [hostStateT_pure_run]; exact ⟨hRp.1, hNext5, hAct5, mapErrno_isNonOutcome _ _ _⟩
      · rw [hostStateT_pure_run]
        exact ⟨hc3.1, (congrArg Model.ProcessModelState.nextHandleId hSt4).trans hNext1,
          (congrArg Model.ProcessModelState.activeHandles hSt4).trans hAct1, trivial⟩

/-- End-to-end `SysBridge.mkRawOpsM` refinement over `Model.HealthyHostCapsM`. -/
theorem sysBridge_mkRawOpsM_refines_host {W : Type} (proj : W → Model.ProcessHostWorld)
    (cap : Model.HealthyHostCapsM (StateM W))
    (hCap : Core.ObeysStep proj Model.hostWorldWf (Model.execHostCapStep cap) Model.allowedHostCapStep)
    (w : W) (req : Model.RawStepReq) (hWf : Model.hostWorldWf (proj w) = true) :
    let (out, w') := (Model.execRawStep (SysBridge.mkRawOpsM (hostDepsOf cap) cap.table) req).run w
    Model.hostWorldWf (proj w') = true ∧
    Model.allowedRawStep (Model.hostWorldToProcessState (proj w)) req out (Model.hostWorldToProcessState (proj w')) := by
  have hS := hostWorldWf_implies_processStateWf hWf
  cases req with
  | mapRawError err =>
    dsimp only [Model.execRawStep, SysBridge.mkRawOpsM, Model.allowedRawStep]
    rw [hostStateT_pure_run]
    exact ⟨hWf, hS, hS, rfl, (refinesPure_mapRawError err).symm⟩
  | spawn sreq =>
    dsimp only [Model.execRawStep, SysBridge.mkRawOpsM, Model.allowedRawStep]
    rw [hostStateT_map_run]
    have hSp := spawnPure_refines_host proj cap hCap w hWf sreq
    cases hSpRun : (SysBridge.spawnPure (hostDepsOf cap) cap.table DEFAULT_EINTR_FUEL sreq).run w with
    | mk res w' =>
      rw [hSpRun] at hSp
      exact ⟨hSp.1, hS, hostWorldWf_implies_processStateWf hSp.1, hSp.2⟩
  | awaitOutput h stdin to? max? =>
    dsimp only [Model.execRawStep, SysBridge.mkRawOpsM, Model.allowedRawStep]
    rw [hostStateT_map_run]
    have hAw := awaitOutputPure_refines_host proj cap hCap w hWf h stdin to? max?
    cases hAwRun : (SysBridge.awaitOutputPure (hostDepsOf cap) cap.table
        DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL h stdin to? max?).run w with
    | mk res w' =>
      rw [hAwRun] at hAw
      exact ⟨hAw.1, hS, hostWorldWf_implies_processStateWf hAw.1, hAw.2⟩
  | killProcessGroup h =>
    dsimp only [Model.execRawStep, SysBridge.mkRawOpsM, Model.allowedRawStep]
    rw [hostStateT_map_run]
    have hKl := killProcessGroupPure_refines_host proj cap hCap w hWf h
    cases hKlRun : (SysBridge.killProcessGroupPure (hostDepsOf cap) cap.table DEFAULT_EINTR_FUEL h).run w with
    | mk res w' =>
      rw [hKlRun] at hKl
      exact ⟨hKl.1, hS, hostWorldWf_implies_processStateWf hKl.1, hKl.2⟩
  | reap h =>
    dsimp only [Model.execRawStep, SysBridge.mkRawOpsM, Model.allowedRawStep]
    rw [hostStateT_map_run]
    have hRp := reapPure_refines_host proj cap hCap w hWf h
    cases hRpRun : (SysBridge.reapPure (hostDepsOf cap) cap.table DEFAULT_EINTR_FUEL h).run w with
    | mk res w' =>
      rw [hRpRun] at hRp
      exact ⟨hRp.1, hS, hostWorldWf_implies_processStateWf hRp.1, hRp.2⟩
  | activeProcessCount =>
    dsimp only [Model.execRawStep, SysBridge.mkRawOpsM, Model.allowedRawStep]
    rw [hostStateT_map_run]
    have hCnt := capTbl_activeCount_step proj cap hCap w hWf
    cases hCntRun : cap.table.activeCount.run w with
    | mk n w' =>
      rw [hCntRun] at hCnt
      exact ⟨hCnt.1, hS, hostWorldWf_implies_processStateWf hCnt.1, hCnt.2.1, hCnt.2.2⟩

/-- End-to-end `Impl + SysBridge` capability refinement over `Model.HealthyHostCapsM` (`LinuxSyscall.{Process,Files,Poll,TimeRand}`, `PostFork`, `EnvVars.Raw`, and handle table). -/
theorem refinesStepFrom_mkApiFromHostCapsM :
    Core.ObeysStepFrom id Model.hostWorldWf
      Model.execHostCapStep Model.allowedHostCapStep
      Model.hostWorldWf Internal.mkApiFromHostCapsM
      Model.execPkgStep Model.allowedPkgHostStep := by
  intro W proj cap hCap w req hWf
  have hApi := mkApiM_refines_of_rawWf (fun x => Model.hostWorldWf (proj x))
    (fun x => Model.hostWorldToProcessState (proj x))
    (SysBridge.mkRawOpsM (hostDepsOf cap) cap.table)
    (fun x hx => hostWorldWf_implies_processStateWf hx)
    (sysBridge_mkRawOpsM_refines_host proj cap hCap)
    w req hWf
  change let (out, w') := (Model.execPkgStep (Internal.mkApiM (SysBridge.mkRawOpsM (hostDepsOf cap) cap.table)) req).run w
    Model.allowedPkgHostStep (proj w) req out (proj w')
  dsimp only [Model.allowedPkgHostStep]
  exact ⟨hWf, hApi.1, hApi.2⟩

end LeanSwe.Process.Proofs
