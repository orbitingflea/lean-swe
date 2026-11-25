import LeanSwe.Process.Proofs.FullObeysLoops

/-!
OS-phase specifications (`spawnOsPhase`, `awaitOsPhase`, `killGroupOsPhase`, `reapOsPhase`)
over `SysPreservesFrame` for `Core.ObeysStepFromConcCell`.
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process

/-- OS-phase specification for `SysBridge.spawnOsPhase` under `SysPreservesFrame`. -/
theorem spawnOsPhase_full_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (req : ExecRequest) (w : W) (hWf : inv w) :
    let r := (SysBridge.spawnOsPhase (SysBridge.sysDepsOfCaps sys) DEFAULT_EINTR_FUEL req).run w
    inv r.2 ∧ frame w r.2 ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok slot =>
      Model.procSlotWf slot = true ∧ slot.stdinFd?.isNone = false ∧ slot.waited = false := by
  unfold SysBridge.spawnOsPhase; dsimp only [SysBridge.sysDepsOfCaps]
  split
  · rw [hostStateT_pure_run]; exact ⟨hWf, hrefl w, mapRawError_invalidArg_isNonOutcome _ _ _⟩
  · rw [hostStateT_bind_run]
    have hWd := fullValidateWorkingDir_spec hrefl htrans hSys req.cwd DEFAULT_EINTR_FUEL w hWf
    cases hWdRun : (SysBridge.validateWorkingDir sys.files req.cwd DEFAULT_EINTR_FUEL).run w with
    | mk wdRes w1 =>
      rw [hWdRun] at hWd
      cases wdRes with
      | error _ => rw [hostStateT_pure_run]; exact ⟨hWd.1, hWd.2.1, hWd.2.2 _ rfl⟩
      | ok _ =>
        dsimp only; rw [hostStateT_bind_run]
        have hEnv : let r := (SysBridge.readBaseEnv
            { proc := sys.proc, files := sys.files, poll := sys.poll, timeRand := sys.timeRand,
              postFork := sys.postFork, listAmbientEnv := Except.ok <$> sys.envRaw.listEnvironBytes } req.inheritEnv).run w1
            inv r.2 ∧ frame w1 r.2 ∧ (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
          unfold SysBridge.readBaseEnv
          cases req.inheritEnv with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [hostStateT_pure_run]; exact ⟨hWd.1, hrefl w1, fun _ h => by cases h⟩
          | true =>
            simp only [↓reduceIte]; rw [hostStateT_map_run]
            have hA := hSys.listEnvironBytes w1 hWd.1
            exact ⟨hA.1, hA.2, fun _ h => by cases h⟩
        cases hEnvRun : (SysBridge.readBaseEnv
            { proc := sys.proc, files := sys.files, poll := sys.poll, timeRand := sys.timeRand,
              postFork := sys.postFork, listAmbientEnv := Except.ok <$> sys.envRaw.listEnvironBytes } req.inheritEnv).run w1 with
        | mk envRes w2 =>
          rw [hEnvRun] at hEnv
          have hf2 : frame w w2 := htrans _ _ _ hWd.2.1 hEnv.2.1
          cases envRes with
          | error _ =>
            rw [hostStateT_pure_run]
            exact ⟨hEnv.1, hf2, ensureNonEmpty_host_isNonOutcome _ _ (by decide) (hEnv.2.2 _ rfl)⟩
          | ok baseEnv =>
            dsimp only; rw [hostStateT_bind_run]
            let envBytes := SysBridge.mergeRawEnvOverrides baseEnv req.env
            have hRes := fullResolveExecutablePath_spec hrefl htrans hSys req.program req.cwd envBytes DEFAULT_EINTR_FUEL w2 hEnv.1
            cases hResRun : (SysBridge.resolveExecutablePath sys.files req.program req.cwd envBytes DEFAULT_EINTR_FUEL).run w2 with
            | mk pathRes w3 =>
              rw [hResRun] at hRes
              have hf3 : frame w w3 := htrans _ _ _ hf2 hRes.2.1
              cases pathRes with
              | error _ => rw [hostStateT_pure_run]; exact ⟨hRes.1, hf3, hRes.2.2 _ rfl⟩
              | ok resolvedPath =>
                dsimp only; split
                · rw [hostStateT_pure_run]; exact ⟨hRes.1, hf3, mapRawError_invalidArg_isNonOutcome _ _ _⟩
                · rw [hostStateT_bind_run]
                  have hP1 := fullRetryEintr_frame htrans (sys.proc.pipe2 { cloexec := true })
                    (hSys.pipe2 { cloexec := true }) DEFAULT_EINTR_FUEL w3 hRes.1
                  cases hP1Run : (LinuxSyscall.retryEintr (sys.proc.pipe2 { cloexec := true }) DEFAULT_EINTR_FUEL).run w3 with
                  | mk p1Res w4 =>
                    rw [hP1Run] at hP1
                    have hf4 : frame w w4 := htrans _ _ _ hf3 hP1.2
                    cases p1Res with
                    | error _ => rw [hostStateT_pure_run]; exact ⟨hP1.1, hf4, mapErrno_isNonOutcome _ _ _⟩
                    | ok p1 =>
                      rcases p1 with ⟨inR, inW⟩; dsimp only; rw [hostStateT_bind_run]
                      have hP2 := fullRetryEintr_frame htrans (sys.proc.pipe2 { cloexec := true })
                        (hSys.pipe2 { cloexec := true }) DEFAULT_EINTR_FUEL w4 hP1.1
                      cases hP2Run : (LinuxSyscall.retryEintr (sys.proc.pipe2 { cloexec := true }) DEFAULT_EINTR_FUEL).run w4 with
                      | mk p2Res w5 =>
                        rw [hP2Run] at hP2
                        have hf5 : frame w w5 := htrans _ _ _ hf4 hP2.2
                        cases p2Res with
                        | error _ =>
                          dsimp only; rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                          have hc1 := fullCloseOpt_frame hrefl hSys (some inR) w5 hP2.1
                          have hc2 := fullCloseOpt_frame hrefl hSys (some inW) (Files.closeOpt sys.files (some inR) |>.run w5).2 hc1.1
                          exact ⟨hc2.1, htrans _ _ _ hf5 (htrans _ _ _ hc1.2 hc2.2), mapErrno_isNonOutcome _ _ _⟩
                        | ok p2 =>
                          rcases p2 with ⟨outR, outW⟩; dsimp only; rw [hostStateT_bind_run]
                          have hP3 := fullRetryEintr_frame htrans (sys.proc.pipe2 { cloexec := true })
                            (hSys.pipe2 { cloexec := true }) DEFAULT_EINTR_FUEL w5 hP2.1
                          cases hP3Run : (LinuxSyscall.retryEintr (sys.proc.pipe2 { cloexec := true }) DEFAULT_EINTR_FUEL).run w5 with
                          | mk p3Res w6 =>
                            rw [hP3Run] at hP3
                            have hf6 : frame w w6 := htrans _ _ _ hf5 hP3.2
                            cases p3Res with
                            | error _ =>
                              dsimp only; rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                              have hc1 := fullCloseOpt_frame hrefl hSys (some inR) w6 hP3.1
                              have hc2 := fullCloseOpt_frame hrefl hSys (some inW) (Files.closeOpt sys.files (some inR) |>.run w6).2 hc1.1
                              have hc3 := fullCloseOpt_frame hrefl hSys (some outR)
                                (Files.closeOpt sys.files (some inW) |>.run (Files.closeOpt sys.files (some inR) |>.run w6).2).2 hc2.1
                              have hc4 := fullCloseOpt_frame hrefl hSys (some outW)
                                (Files.closeOpt sys.files (some outR) |>.run
                                  (Files.closeOpt sys.files (some inW) |>.run (Files.closeOpt sys.files (some inR) |>.run w6).2).2).2 hc3.1
                              exact ⟨hc4.1, htrans _ _ _ hf6 (htrans _ _ _ hc1.2 (htrans _ _ _ hc2.2 (htrans _ _ _ hc3.2 hc4.2))),
                                mapErrno_isNonOutcome _ _ _⟩
                            | ok p3 =>
                              rcases p3 with ⟨errR, errW⟩; dsimp only; rw [hostStateT_bind_run]
                              let spec : PostFork.ChildSpecM RawFd :=
                                { path := resolvedPath
                                  argv := #[PostFork.ArgToken.lit req.program] ++ req.args.map PostFork.ArgToken.lit
                                  cwd := req.cwd, env := #[], rawEnv := envBytes
                                  stdio := .redirect (.handle inR) (.handle outW) (.handle errW) true
                                  fdPolicy := .inheritNonCloexec #[]
                                  closeFds := #[.handle inW, .handle outR, .handle errR]
                                  processGroup := .newGroup, sigpipe := .resetDefault, forkMode := .direct }
                              have hPf := hSys.postFork spec w6 hP3.1
                              cases hPfRun : (sys.postFork.spawn spec).run w6 with
                              | mk pfRes w7 =>
                                rw [hPfRun] at hPf; dsimp only
                                rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run]
                                have hc1 := fullCloseOpt_frame hrefl hSys (some inR) w7 hPf.1
                                have hc2 := fullCloseOpt_frame hrefl hSys (some outW) (Files.closeOpt sys.files (some inR) |>.run w7).2 hc1.1
                                have hc3 := fullCloseOpt_frame hrefl hSys (some errW)
                                  (Files.closeOpt sys.files (some outW) |>.run (Files.closeOpt sys.files (some inR) |>.run w7).2).2 hc2.1
                                let w8 := (Files.closeOpt sys.files (some errW) |>.run
                                  (Files.closeOpt sys.files (some outW) |>.run (Files.closeOpt sys.files (some inR) |>.run w7).2).2).2
                                have hf8 : frame w w8 :=
                                  htrans _ _ _ hf6 (htrans _ _ _ hPf.2 (htrans _ _ _ hc1.2 (htrans _ _ _ hc2.2 hc3.2)))
                                cases pfRes with
                                | error _ =>
                                  dsimp only; rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                  have hc4 := fullCloseOpt_frame hrefl hSys (some inW) w8 hc3.1
                                  have hc5 := fullCloseOpt_frame hrefl hSys (some outR) (Files.closeOpt sys.files (some inW) |>.run w8).2 hc4.1
                                  have hc6 := fullCloseOpt_frame hrefl hSys (some errR)
                                    (Files.closeOpt sys.files (some outR) |>.run (Files.closeOpt sys.files (some inW) |>.run w8).2).2 hc5.1
                                  exact ⟨hc6.1, htrans _ _ _ hf8 (htrans _ _ _ hc4.2 (htrans _ _ _ hc5.2 hc6.2)),
                                    mapPostForkError_isNonOutcome _ _⟩
                                | ok child =>
                                  dsimp only
                                  let rawPgid := child.pgid.getD child.pid
                                  by_cases hBadPid : (child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID ||
                                      rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID) = true
                                  · rw [ite_eq_left hBadPid, hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
                                    have hc4 := fullCloseOpt_frame hrefl hSys (some inW) w8 hc3.1
                                    have hc5 := fullCloseOpt_frame hrefl hSys (some outR) (Files.closeOpt sys.files (some inW) |>.run w8).2 hc4.1
                                    have hc6 := fullCloseOpt_frame hrefl hSys (some errR)
                                      (Files.closeOpt sys.files (some outR) |>.run (Files.closeOpt sys.files (some inW) |>.run w8).2).2 hc5.1
                                    exact ⟨hc6.1, htrans _ _ _ hf8 (htrans _ _ _ hc4.2 (htrans _ _ _ hc5.2 hc6.2)),
                                      mapRawError_userError_isNonOutcome _⟩
                                  · rw [ite_eq_right hBadPid, hostStateT_pure_run]
                                    have hOkPid : (child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID ||
                                        rawPgid == 0 || rawPgid > LinuxSyscall.Process.MAX_LINUX_PID) = false :=
                                      Bool.eq_false_iff.mpr hBadPid
                                    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not,
                                      UInt32.lt_iff_toNat_lt] at hOkPid
                                    have hPidNe : child.pid.toNat ≠ 0 := fun hz => hOkPid.1.1.1 (UInt32.toNat_inj.mp hz)
                                    have hPgidNe : rawPgid.toNat ≠ 0 := fun hz => hOkPid.1.2 (UInt32.toNat_inj.mp hz)
                                    have hMaxNat : LinuxSyscall.Process.MAX_LINUX_PID.toNat ≤ Model.maxLinuxPidModel.toNat := by decide
                                    have hP1Ge : (1 : UInt32) ≤ child.pid := by rw [UInt32.le_iff_toNat_le]; change 1 ≤ child.pid.toNat; omega
                                    have hPMax : child.pid ≤ Model.maxLinuxPidModel := by rw [UInt32.le_iff_toNat_le]; omega
                                    have hPg1Ge : (1 : UInt32) ≤ rawPgid := by rw [UInt32.le_iff_toNat_le]; change 1 ≤ rawPgid.toNat; omega
                                    have hPgMax : rawPgid ≤ Model.maxLinuxPidModel := by rw [UInt32.le_iff_toNat_le]; omega
                                    refine ⟨hc3.1, hf8, ?_, rfl, rfl⟩
                                    unfold Model.procSlotWf
                                    exact decide_eq_true ⟨hP1Ge, hPMax, hPg1Ge, hPgMax⟩

/-- OS-phase specification for `SysBridge.awaitOsPhase` under `SysPreservesFrame`. -/
theorem awaitOsPhase_full_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (pid : UInt32) (inFd0? outFd0? errFd0? : Option RawFd)
    (stdin : ByteArray) (timeoutMs? maxOutputBytes? : Option Nat) (w : W) (hWf : inv w) :
    let r := (SysBridge.awaitOsPhase (SysBridge.sysDepsOfCaps sys) DEFAULT_EINTR_FUEL DEFAULT_IO_FUEL
      pid inFd0? outFd0? errFd0? stdin timeoutMs? maxOutputBytes?).run w
    inv r.2 ∧ frame w r.2 ∧
    match r.1 with
    | .error err => Model.isNonOutcomeError err
    | .ok (_, outcome) => Model.allowedAwaitOutcome timeoutMs? maxOutputBytes? outcome := by
  unfold SysBridge.awaitOsPhase; dsimp only [SysBridge.sysDepsOfCaps]
  rw [hostStateT_bind_run]
  have hSetup : let r := (SysBridge.setupStdinPipe sys.files stdin inFd0?).run w
      inv r.2 ∧ frame w r.2 := by
    unfold SysBridge.setupStdinPipe; split
    · rw [hostStateT_bind_run, hostStateT_pure_run]; exact fullCloseOpt_frame hrefl hSys inFd0? w hWf
    · cases inFd0? with
      | none => rw [hostStateT_pure_run]; exact ⟨hWf, hrefl w⟩
      | some inFd => rw [hostStateT_bind_run, hostStateT_pure_run]; exact hSys.fcntl inFd (.setFl true false) w hWf
  cases hSetRun : (SysBridge.setupStdinPipe sys.files stdin inFd0?).run w with
  | mk inFd? w1 =>
    rw [hSetRun] at hSetup; dsimp only
    rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run]
    have hNb1 := fullSetNonblockingOpt_frame hrefl hSys outFd0? w1 hSetup.1
    have hNb2 := fullSetNonblockingOpt_frame hrefl hSys errFd0? (Files.setNonblockingOpt sys.files outFd0? |>.run w1).2 hNb1.1
    let w2 := (Files.setNonblockingOpt sys.files errFd0? |>.run (Files.setNonblockingOpt sys.files outFd0? |>.run w1).2).2
    have hf2 : frame w w2 := htrans _ _ _ hSetup.2 (htrans _ _ _ hNb1.2 hNb2.2)
    have hStart : let r := (SysBridge.readStartMsOpt sys.timeRand timeoutMs?).run w2
        inv r.2 ∧ frame w2 r.2 ∧ (∀ err, r.1 = .error err → Model.isNonOutcomeError err) := by
      unfold SysBridge.readStartMsOpt
      cases timeoutMs? with
      | none => rw [hostStateT_pure_run]; exact ⟨hNb2.1, hrefl w2, fun _ h => by cases h⟩
      | some _ =>
        rw [hostStateT_bind_run]
        have hM := fullMonoNowMs_frame hSys w2 hNb2.1
        cases hMRun : (TimeRand.monoNowMs sys.timeRand).run w2 with
        | mk mRes _ =>
          rw [hMRun] at hM
          cases mRes with
          | ok _ => rw [hostStateT_pure_run]; exact ⟨hM.1, hM.2, fun _ h => by cases h⟩
          | error _ => rw [hostStateT_pure_run]; exact ⟨hM.1, hM.2, fun _ h => by injection h with he; subst he; exact mapErrno_isNonOutcome _ _ _⟩
    cases hStRun : (SysBridge.readStartMsOpt sys.timeRand timeoutMs?).run w2 with
    | mk stRes w3 =>
      rw [hStRun] at hStart
      have hf3 : frame w w3 := htrans _ _ _ hf2 hStart.2.1
      cases stRes with
      | error _ =>
        dsimp only; rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run, hostStateT_pure_run]
        have hc1 := fullCloseOpt_frame hrefl hSys inFd? w3 hStart.1
        have hc2 := fullCloseOpt_frame hrefl hSys outFd0? (Files.closeOpt sys.files inFd? |>.run w3).2 hc1.1
        have hc3 := fullCloseOpt_frame hrefl hSys errFd0?
          (Files.closeOpt sys.files outFd0? |>.run (Files.closeOpt sys.files inFd? |>.run w3).2).2 hc2.1
        exact ⟨hc3.1, htrans _ _ _ hf3 (htrans _ _ _ hc1.2 (htrans _ _ _ hc2.2 hc3.2)), hStart.2.2 _ rfl⟩
      | ok startMs =>
        dsimp only; rw [hostStateT_bind_run]
        let initSt : SysBridge.StreamLoopState RawFd := { inFd? := inFd?, outFd? := outFd0?, errFd? := errFd0? }
        have hLp := fullStreamPipesLoop_spec hrefl htrans hSys stdin startMs timeoutMs? maxOutputBytes?
          DEFAULT_EINTR_FUEL initSt DEFAULT_IO_FUEL w3 hStart.1 rfl rfl (fun _ _ => Nat.zero_le _)
        cases hLpRun : (SysBridge.streamPipesLoop sys.files sys.poll sys.timeRand stdin startMs
            timeoutMs? maxOutputBytes? DEFAULT_EINTR_FUEL initSt DEFAULT_IO_FUEL).run w3 with
        | mk lpRes w4 =>
          rw [hLpRun] at hLp
          have hf4 : frame w w4 := htrans _ _ _ hf3 hLp.2.1
          cases lpRes with
          | error _ => rw [hostStateT_pure_run]; exact ⟨hLp.1, hf4, hLp.2.2⟩
          | ok phase =>
            cases phase with
            | timedOut _ _ => rw [hostStateT_pure_run]; exact ⟨hLp.1, hf4, hLp.2.2⟩
            | limitExceeded _ _ => rw [hostStateT_pure_run]; exact ⟨hLp.1, hf4, hLp.2.2⟩
            | eof out err =>
              dsimp only
              cases timeoutMs? with
              | none =>
                rw [hostStateT_bind_run]
                have hWb := fullWaitBlockingLoop_spec hrefl htrans hSys pid.toInt32 out err DEFAULT_EINTR_FUEL w4 hLp.1
                cases hWbRun : (SysBridge.waitBlockingLoop sys.proc pid.toInt32 out err DEFAULT_EINTR_FUEL).run w4 with
                | mk wbRes w5 =>
                  rw [hWbRun] at hWb
                  cases wbRes with
                  | error _ => rw [hostStateT_pure_run]; exact ⟨hWb.1, htrans _ _ _ hf4 hWb.2.1, hWb.2.2⟩
                  | ok outc =>
                    rw [hostStateT_pure_run]
                    refine ⟨hWb.1, htrans _ _ _ hf4 hWb.2.1, ?_⟩
                    cases outc with
                    | exited res => intro lim hLim; obtain ⟨ho, he⟩ := hWb.2.2; rw [ho, he]; exact hLp.2.2 lim hLim
                    | signaled _ _ _ => trivial
                    | timedOut _ _ | outputLimitExceeded _ _ => exact False.elim hWb.2.2
              | some timeoutMs =>
                have hWt := fullWaitTimedLoop_spec hrefl htrans hSys pid.toInt32 startMs timeoutMs out err DEFAULT_IO_FUEL w4 hLp.1
                cases hWtRun : (SysBridge.waitTimedLoop sys.proc sys.timeRand pid.toInt32 startMs timeoutMs out err DEFAULT_IO_FUEL).run w4 with
                | mk wtRes w5 =>
                  rw [hWtRun] at hWt
                  cases wtRes with
                  | error _ => exact ⟨hWt.1, htrans _ _ _ hf4 hWt.2.1, hWt.2.2⟩
                  | ok wtPair =>
                    rcases wtPair with ⟨_, outc⟩
                    refine ⟨hWt.1, htrans _ _ _ hf4 hWt.2.1, ?_⟩
                    cases outc with
                    | exited res => intro lim hLim; obtain ⟨ho, he⟩ := hWt.2.2; rw [ho, he]; exact hLp.2.2 lim hLim
                    | signaled _ _ _ => trivial
                    | timedOut _ _ => rfl
                    | outputLimitExceeded _ _ => exact False.elim hWt.2.2

/-- OS-phase specification for `SysBridge.killGroupOsPhase` under `SysPreservesFrame`. -/
theorem killGroupOsPhase_full_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (pgid : UInt32) (w : W) (hWf : inv w) :
    let r := (SysBridge.killGroupOsPhase (SysBridge.sysDepsOfCaps sys) DEFAULT_EINTR_FUEL pgid).run w
    inv r.2 ∧ frame w r.2 ∧
    match r.1 with
    | .ok () => True
    | .error err => Model.isNonOutcomeError err := by
  unfold SysBridge.killGroupOsPhase; dsimp only [SysBridge.sysDepsOfCaps]
  split
  · rw [hostStateT_pure_run]; exact ⟨hWf, hrefl w, trivial⟩
  · rw [hostStateT_bind_run]
    let target := LinuxSyscall.Process.killTargetOfPgid pgid
    have hK1 := fullRetryEintr_frame htrans (sys.proc.kill target .sigterm)
      (hSys.kill target .sigterm) DEFAULT_EINTR_FUEL w hWf
    cases hK1Run : (LinuxSyscall.retryEintr (sys.proc.kill target .sigterm) DEFAULT_EINTR_FUEL).run w with
    | mk k1 w1 =>
      rw [hK1Run] at hK1
      cases k1 with
      | error _ =>
        dsimp only; split <;> rw [hostStateT_pure_run]
        · exact ⟨hK1.1, hK1.2, trivial⟩
        · exact ⟨hK1.1, hK1.2, mapErrno_isNonOutcome _ _ _⟩
      | ok _ =>
        dsimp only; rw [hostStateT_bind_run]
        have hGp := fullKillGraceProbeLoop_frame hrefl htrans hSys target 5 w1 hK1.1
        cases hGpRun : (SysBridge.killGraceProbeLoop sys.proc sys.timeRand target 5).run w1 with
        | mk _ w2 =>
          rw [hGpRun] at hGp; dsimp only; split
          · rw [hostStateT_pure_run]; exact ⟨hGp.1, htrans _ _ _ hK1.2 hGp.2, trivial⟩
          · rw [hostStateT_bind_run]
            have hK2 := fullRetryEintr_frame htrans (sys.proc.kill target .sigkill)
              (hSys.kill target .sigkill) DEFAULT_EINTR_FUEL w2 hGp.1
            cases hK2Run : (LinuxSyscall.retryEintr (sys.proc.kill target .sigkill) DEFAULT_EINTR_FUEL).run w2 with
            | mk k2 w3 =>
              rw [hK2Run] at hK2
              have hf3 : frame w w3 := htrans _ _ _ hK1.2 (htrans _ _ _ hGp.2 hK2.2)
              cases k2 with
              | ok _ => rw [hostStateT_pure_run]; exact ⟨hK2.1, hf3, trivial⟩
              | error _ =>
                dsimp only; split <;> rw [hostStateT_pure_run]
                · exact ⟨hK2.1, hf3, trivial⟩
                · exact ⟨hK2.1, hf3, mapErrno_isNonOutcome _ _ _⟩

/-- OS-phase specification for `SysBridge.reapOsPhase` under `SysPreservesFrame`. -/
theorem reapOsPhase_full_spec {W : Type} {inv : W → Prop} {frame : W → W → Prop}
    (hrefl : ∀ w, frame w w)
    (htrans : ∀ w₁ w₂ w₃, frame w₁ w₂ → frame w₂ w₃ → frame w₁ w₃)
    {sys : Internal.ProcessSysCapsM (StateM W)} (hSys : SysPreservesFrame inv frame sys)
    (slot : Internal.ProcSlotM RawFd) (w : W) (hWf : inv w) :
    let r := (SysBridge.reapOsPhase (SysBridge.sysDepsOfCaps sys) DEFAULT_EINTR_FUEL slot).run w
    inv r.2 ∧ frame w r.2 ∧
    match r.1 with
    | .ok () => True
    | .error err => Model.isNonOutcomeError err := by
  unfold SysBridge.reapOsPhase; dsimp only [SysBridge.sysDepsOfCaps]
  rw [hostStateT_bind_run, hostStateT_bind_run, hostStateT_bind_run]
  have hc1 := fullCloseOpt_frame hrefl hSys slot.stdinFd? w hWf
  have hc2 := fullCloseOpt_frame hrefl hSys slot.stdoutFd? (Files.closeOpt sys.files slot.stdinFd? |>.run w).2 hc1.1
  have hc3 := fullCloseOpt_frame hrefl hSys slot.stderrFd?
    (Files.closeOpt sys.files slot.stdoutFd? |>.run (Files.closeOpt sys.files slot.stdinFd? |>.run w).2).2 hc2.1
  let w3 := (Files.closeOpt sys.files slot.stderrFd? |>.run
    (Files.closeOpt sys.files slot.stdoutFd? |>.run (Files.closeOpt sys.files slot.stdinFd? |>.run w).2).2).2
  have hf3 : frame w w3 := htrans _ _ _ hc1.2 (htrans _ _ _ hc2.2 hc3.2)
  split
  · rw [hostStateT_bind_run]
    have hRp := fullWaitpidReapLoop_frame hrefl htrans hSys slot.pid.toInt32 DEFAULT_EINTR_FUEL w3 hc3.1
    cases hRpRun : (LinuxSyscall.Process.waitpidReapLoop sys.proc slot.pid.toInt32 DEFAULT_EINTR_FUEL).run w3 with
    | mk rp w4 =>
      rw [hRpRun] at hRp
      have hf4 : frame w w4 := htrans _ _ _ hf3 hRp.2
      cases rp with
      | ok _ => rw [hostStateT_pure_run]; exact ⟨hRp.1, hf4, trivial⟩
      | error errOpt =>
        cases errOpt with
        | none => rw [hostStateT_pure_run]; exact ⟨hRp.1, hf4, mapRawError_userError_isNonOutcome _⟩
        | some _ => rw [hostStateT_pure_run]; exact ⟨hRp.1, hf4, mapErrno_isNonOutcome _ _ _⟩
  · rw [hostStateT_pure_run]; exact ⟨hc3.1, hf3, trivial⟩

end LeanSwe.Process.Proofs
