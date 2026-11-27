import LeanSweProofs.LinuxSyscall.Process.Proofs.ObeysRaw
import LeanSweProofs.LinuxSyscall.Process.Proofs.ModelSoundnessReq

/-!
# Healthy-World Non-Vacuity & Combinator Proofs for `LeanSwe.LinuxSyscall.Process`

Proves `healthyModelOps_obeysSingleStep`, `rawHealthyModelOps_obeysStep`, and
`waitpidReapLoop_obeysStepFrom` for `LeanSwe.LinuxSyscall.Process.Proofs`.
-/

namespace LeanSwe.LinuxSyscall.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Process

private theorem evalKillProcessGroup_err_safe (s : ProcessSysState) (pgid : UInt32) (sig : Signal)
    {e : Errno} (h : evalKillProcessGroup s pgid sig = .error e) :
    isCriticalFault (.err e) = false ∧ isEintrOutcome (.err e) = false := by
  unfold evalKillProcessGroup at h
  repeat (first | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩) | split at h | (dsimp only at h) | cases h)

private theorem deliverSignalToTarget_err_safe (s : ProcessSysState) (pid : UInt32) (sig : Signal)
    (ts : Bool) {e : Errno} (h : deliverSignalToTarget s pid sig ts = .error e) :
    isCriticalFault (.err e) = false ∧ isEintrOutcome (.err e) = false := by
  unfold deliverSignalToTarget at h
  repeat (first | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩) | split at h | (dsimp only at h) | cases h)

private theorem evalKill_err_safe (s : ProcessSysState) (p : Int32) (sig : Signal)
    {e : Errno} (h : evalKill s p sig = .error e) :
    isCriticalFault (.err e) = false ∧ isEintrOutcome (.err e) = false := by
  unfold evalKill at h
  repeat (first
    | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩)
    | exact deliverSignalToTarget_err_safe _ _ _ _ h
    | exact evalKillProcessGroup_err_safe _ _ _ h
    | split at h
    | (dsimp only at h)
    | cases h)

private theorem checkPidfdOpenTarget_err_safe (s : ProcessSysState) (pid : UInt32)
    (flags : PidfdOpenFlags) {e : Errno} (h : checkPidfdOpenTarget s pid flags = .error e) :
    isCriticalFault (.err e) = false ∧ isEintrOutcome (.err e) = false := by
  unfold checkPidfdOpenTarget at h
  repeat (first | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩) | split at h | (dsimp only at h) | cases h)

private theorem evalPidfdSendSignal_err_safe (s : ProcessSysState) (hid : HandleId) (sig : Signal)
    (flags : PidfdSignalFlags) {e : Errno} (h : evalPidfdSendSignal s hid sig flags = .error e) :
    isCriticalFault (.err e) = false ∧ isEintrOutcome (.err e) = false := by
  unfold evalPidfdSendSignal at h
  repeat (first
    | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩)
    | exact evalKillProcessGroup_err_safe _ _ _ h
    | exact deliverSignalToTarget_err_safe _ _ _ _ h
    | split at h
    | (dsimp only at h)
    | cases h)

private theorem validateReqBeforeKernel_safe (s : ProcessSysState) (req : ProcessReq) {e : Errno}
    (h : validateReqBeforeKernel s req = some e) :
    isCriticalFault (.err e) = false ∧ isEintrOutcome (.err e) = false := by
  unfold validateReqBeforeKernel at h
  cases req <;> simp only at h
  all_goals
    repeat (first | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩) | split at h | (dsimp only at h) | cases h)

private theorem modelOps_nonWait_safe (s : ProcessSysState) (req : ProcessReq)
    (hNw : ∀ pid fl, req ≠ .waitpid pid fl) :
    let out := ((execProcessReq modelOps req).run s).1
    isCriticalFault out = false ∧ isEintrOutcome out = false := by
  cases req with
  | waitpid pid fl => exact absurd rfl (hNw pid fl)
  | getpid => exact ⟨rfl, rfl⟩
  | getuid => exact ⟨rfl, rfl⟩
  | pipe2 flags =>
    by_cases h1 : (!flags.isValid) = true
    · simp only [execProcessReq, modelOps, StateT.run, stateT_bind_eq, stateT_pure_eq,
        Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, StateT.get, set,
        h1, ↓reduceIte, outcomeOfPiped]
      exact ⟨by decide, by decide⟩
    · by_cases h2 : (flags.notificationPipe && !s.watchQueueSupported) = true
      · simp only [execProcessReq, modelOps, StateT.run, stateT_bind_eq, stateT_pure_eq,
          Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, StateT.get, set,
          h1, Bool.false_eq_true, ↓reduceIte, h2, outcomeOfPiped]
        exact ⟨by decide, by decide⟩
      · simp only [execProcessReq, modelOps, StateT.run, stateT_bind_eq, stateT_pure_eq,
          Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
          h1, h2, Bool.false_eq_true, ↓reduceIte, outcomeOfPiped]
        exact ⟨rfl, rfl⟩
  | kill pid sig =>
    dsimp only [execProcessReq, modelOps, StateT.run, stateT_bind_eq, stateT_pure_eq,
      Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]
    cases hPre : validateReqBeforeKernel s (.kill pid sig) with
    | some e => exact validateReqBeforeKernel_safe s (.kill pid sig) hPre
    | none =>
      dsimp only
      cases hEv : evalKill s pid sig with
      | ok _ => exact ⟨rfl, rfl⟩
      | error e => exact evalKill_err_safe s pid sig hEv
  | pidfd_open pid flags =>
    dsimp only [execProcessReq, modelOps, StateT.run, stateT_bind_eq, stateT_pure_eq,
      Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]
    cases hChk : checkPidfdOpenTarget s pid flags with
    | ok _ => exact ⟨rfl, rfl⟩
    | error e => exact checkPidfdOpenTarget_err_safe s pid flags hChk
  | pidfd_send_signal hid sig flags =>
    dsimp only [execProcessReq, modelOps, StateT.run, stateT_bind_eq, stateT_pure_eq,
      Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]
    cases hPre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) with
    | some e => exact validateReqBeforeKernel_safe s (.pidfd_send_signal hid sig flags) hPre
    | none =>
      dsimp only
      cases hEv : evalPidfdSendSignal s hid sig flags with
      | ok _ => exact ⟨rfl, rfl⟩
      | error e => exact evalPidfdSendSignal_err_safe s hid sig flags hEv

private theorem healthyStep_waitpid_enospc {env : HealthyEnv} (pid : Int32) (flags : WaitFlags)
    (hWf : env.wf = true) :
    healthyStep env (.waitpid pid flags) (.err Errno.ENOSPC) = some env := by
  rcases env with ⟨s, budget⟩
  have hNoCrit : isCriticalFault (.err Errno.ENOSPC) = false := by decide
  have hNoEi : isEintrOutcome (.err Errno.ENOSPC) = false := by decide
  have hTr : isKernelNonFdTransient Errno.ENOSPC = true := by decide
  have hAl : allowedStep s (.waitpid pid flags) (.err Errno.ENOSPC) = some s := by
    unfold allowedStep validateReqBeforeKernel allowedStepWaitpid
    dsimp only
    split
    · simp [hTr]
    · split
      · simp [hTr]
      · split
        · simp [hTr]
        · simp
  unfold healthyStep
  simp [hWf, hNoCrit, hNoEi, hAl]

/-- `Model.healthyModelOps` satisfies `Model.allowedSingleStep` from every well-formed `HealthyEnv`. -/
theorem healthyModelOps_obeysSingleStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execSingleStep Model.healthyModelOps) Model.allowedSingleStep := by
  intro env req hWf
  dsimp only [id, Model.allowedSingleStep] at hWf ⊢
  cases req with
  | waitpid pid flags =>
    simp only [Model.execSingleStep, execProcessReq, Model.healthyModelOps, Model.runHealthyWaitpid,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq]
    have hFb := healthyStep_waitpid_enospc pid flags hWf
    rcases hAct : modelOps.waitpid pid flags env.state with ⟨candRes, s'⟩
    dsimp only
    cases hFits : Model.waitResFitsRaw candRes with
    | false => simpa [outcomeOfWaited] using hFb
    | true =>
      simp only [↓reduceIte]
      cases hSt : healthyStep env (.waitpid pid flags) (outcomeOfWaited candRes) with
      | none => simpa [outcomeOfWaited] using hFb
      | some env' =>
        dsimp only
        cases hWf' : env'.wf with
        | false => simpa [outcomeOfWaited] using hFb
        | true => simp [hSt]
  | pipe2 flags =>
    have hSound := modelOps_execProcessReq_sound env.state (.pipe2 flags)
    obtain ⟨hNoCrit, hNoEi⟩ := modelOps_nonWait_safe env.state (.pipe2 flags) (fun _ _ h => by cases h)
    have hTight := allowedStep_healthy_tight hSound hWf hNoCrit (by simp [hNoEi])
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    simp only [execProcessReq, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq] at hTight
    simp only [Model.execSingleStep, execProcessReq, Model.healthyModelOps, Model.liftHealthyProcessOp,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq]
    rcases hAct : modelOps.pipe2 flags env.state with ⟨res, s'⟩
    try rw [hAct] at hTight
    exact hTight
  | kill pid sig =>
    have hSound := modelOps_execProcessReq_sound env.state (.kill pid sig)
    obtain ⟨hNoCrit, hNoEi⟩ := modelOps_nonWait_safe env.state (.kill pid sig) (fun _ _ h => by cases h)
    have hTight := allowedStep_healthy_tight hSound hWf hNoCrit (by simp [hNoEi])
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    simp only [execProcessReq, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq] at hTight
    simp only [Model.execSingleStep, execProcessReq, Model.healthyModelOps, Model.liftHealthyProcessOp,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq]
    rcases hAct : modelOps.kill pid sig env.state with ⟨res, s'⟩
    try rw [hAct] at hTight
    exact hTight
  | pidfd_open pid flags =>
    have hSound := modelOps_execProcessReq_sound env.state (.pidfd_open pid flags)
    obtain ⟨hNoCrit, hNoEi⟩ := modelOps_nonWait_safe env.state (.pidfd_open pid flags) (fun _ _ h => by cases h)
    have hTight := allowedStep_healthy_tight hSound hWf hNoCrit (by simp [hNoEi])
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    simp only [execProcessReq, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq] at hTight
    simp only [Model.execSingleStep, execProcessReq, Model.healthyModelOps, Model.liftHealthyProcessOp,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq]
    rcases hAct : modelOps.pidfd_open pid flags env.state with ⟨res, s'⟩
    try rw [hAct] at hTight
    exact hTight
  | pidfd_send_signal hid sig flags =>
    have hSound := modelOps_execProcessReq_sound env.state (.pidfd_send_signal hid sig flags)
    obtain ⟨hNoCrit, hNoEi⟩ := modelOps_nonWait_safe env.state (.pidfd_send_signal hid sig flags) (fun _ _ h => by cases h)
    have hTight := allowedStep_healthy_tight hSound hWf hNoCrit (by simp [hNoEi])
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    simp only [execProcessReq, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq] at hTight
    simp only [Model.execSingleStep, execProcessReq, Model.healthyModelOps, Model.liftHealthyProcessOp,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq]
    rcases hAct : modelOps.pidfd_send_signal hid sig flags env.state with ⟨res, s'⟩
    try rw [hAct] at hTight
    exact hTight
  | getpid =>
    have hSound := modelOps_execProcessReq_sound env.state .getpid
    obtain ⟨hNoCrit, hNoEi⟩ := modelOps_nonWait_safe env.state .getpid (fun _ _ h => by cases h)
    have hTight := allowedStep_healthy_tight hSound hWf hNoCrit (by simp [hNoEi])
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    simp only [execProcessReq, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq] at hTight
    simp only [Model.execSingleStep, execProcessReq, Model.healthyModelOps, Model.liftHealthyProcessOp,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq]
    rcases hAct : modelOps.getpid env.state with ⟨res, s'⟩
    try rw [hAct] at hTight
    exact hTight
  | getuid =>
    have hSound := modelOps_execProcessReq_sound env.state .getuid
    obtain ⟨hNoCrit, hNoEi⟩ := modelOps_nonWait_safe env.state .getuid (fun _ _ h => by cases h)
    have hTight := allowedStep_healthy_tight hSound hWf hNoCrit (by simp [hNoEi])
    simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
    simp only [execProcessReq, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq] at hTight
    simp only [Model.execSingleStep, execProcessReq, Model.healthyModelOps, Model.liftHealthyProcessOp,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq]
    rcases hAct : modelOps.getuid env.state with ⟨res, s'⟩
    try rw [hAct] at hTight
    exact hTight

private theorem runHealthyWaitpid_ok_roundtrip {env env' : HealthyEnv}
    {pid : Int32} {flags : WaitFlags} {wr : WaitResult}
    (h : Model.runHealthyWaitpid pid flags env = (.ok wr, env')) :
    WaitResult.ofRawWait4 (Model.encodeRawWait4 wr) = wr := by
  unfold Model.runHealthyWaitpid at h
  dsimp only [StateT.run] at h
  rcases hAct : modelOps.waitpid pid flags env.state with ⟨candRes, s'⟩
  rw [hAct] at h
  dsimp only at h
  cases hFits : Model.waitResFitsRaw candRes with
  | false =>
    rw [hFits] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    injection h with h1 _
    cases h1
  | true =>
    rw [hFits] at h
    simp only [↓reduceIte] at h
    cases hSt : healthyStep env (.waitpid pid flags) (outcomeOfWaited candRes) with
    | none =>
      rw [hSt] at h
      dsimp only at h
      injection h with h1 _
      cases h1
    | some env1 =>
      rw [hSt] at h
      dsimp only at h
      cases hWf1 : env1.wf with
      | false =>
        rw [hWf1] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        injection h with h1 _
        cases h1
      | true =>
        rw [hWf1] at h
        simp only [↓reduceIte] at h
        injection h with h1 _
        rw [h1] at hFits
        exact of_decide_eq_true hFits

/-- `Model.rawHealthyModelOps` satisfies `Model.allowedRawStep` from every well-formed `HealthyEnv`. -/
theorem rawHealthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  cases req with
  | pipe2 flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hDec : Model.decodeRawPipeFlags? flBits with
    | none => simp [Model.outcomeOfRawPiped]
    | some fl =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysSingleStep env (.pipe2 fl) hWf
      simp only [id, Model.execSingleStep, execProcessReq, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq, Model.allowedSingleStep] at hStep
      rcases hCall : Model.healthyModelOps.pipe2 fl env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res with
      | ok p => rcases p with ⟨r, wr⟩; simpa [Model.outcomeOfRawPiped, Model.toModelOutcome, outcomeOfPiped] using hStep
      | error e => simpa [Model.outcomeOfRawPiped, Model.toModelOutcome, outcomeOfPiped] using hStep
  | waitpid pid flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.rawHealthyModelOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_map_eq]
    cases hDec : Model.decodeRawWaitFlags? flBits with
    | none => simp [Model.outcomeOfRawWaited]
    | some fl =>
      dsimp only [Option.map]
      simp only [stateT_bind_eq]
      have hStep := healthyModelOps_obeysSingleStep env (.waitpid pid fl) hWf
      simp only [id, Model.execSingleStep, execProcessReq, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq, Model.allowedSingleStep] at hStep
      rcases hCall : Model.healthyModelOps.waitpid pid fl env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res with
      | error e =>
        simpa [Model.outcomeOfRawWaited, Model.toModelOutcome, outcomeOfWaited] using hStep
      | ok wr =>
        have hRt := runHealthyWaitpid_ok_roundtrip hCall
        simpa [Model.outcomeOfRawWaited, Model.toModelOutcome, outcomeOfWaited, hRt] using hStep
  | kill pid tg ag =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hDec : Model.decodeRawSignal? tg ag with
    | none => simp [Model.outcomeOfRawUnit]
    | some sig =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysSingleStep env (.kill pid sig) hWf
      simp only [id, Model.execSingleStep, execProcessReq, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq, Model.allowedSingleStep] at hStep
      rcases hCall : Model.healthyModelOps.kill pid sig env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | pidfd_open pid flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hDec : Model.decodeRawPidfdOpenFlags? flBits with
    | none => simp [Model.outcomeOfRawOpened]
    | some fl =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysSingleStep env (.pidfd_open pid fl) hWf
      simp only [id, Model.execSingleStep, execProcessReq, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq, Model.allowedSingleStep] at hStep
      rcases hCall : Model.healthyModelOps.pidfd_open pid fl env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | pidfd_send_signal h tg ag flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hSig : Model.decodeRawSignal? tg ag with
    | none => simp [Model.outcomeOfRawUnit]
    | some sig =>
      cases hFl : Model.decodeRawPidfdSignalFlags? flBits with
      | none => simp [Model.outcomeOfRawUnit]
      | some fl =>
        dsimp only
        have hStep := healthyModelOps_obeysSingleStep env (.pidfd_send_signal h sig fl) hWf
        simp only [id, Model.execSingleStep, execProcessReq, Bind.bind, Pure.pure,
          StateT.run, stateT_bind_eq, stateT_pure_eq, Model.allowedSingleStep] at hStep
        rcases hCall : Model.healthyModelOps.pidfd_send_signal h sig fl env with ⟨res, env'⟩
        try rw [hCall] at hStep
        cases res <;>
          simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getpid =>
    have hStep := healthyModelOps_obeysSingleStep env .getpid hWf
    simp only [id, Model.execSingleStep, execProcessReq, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, Model.allowedSingleStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.getpid env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | getuid =>
    have hStep := healthyModelOps_obeysSingleStep env .getuid hWf
    simp only [id, Model.execSingleStep, execProcessReq, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, Model.allowedSingleStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.getuid env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep

private theorem healthyStep_waitpid_eintr_wf {env env' : HealthyEnv} {pid : Int32}
    (h : healthyStep env (.waitpid pid {}) (.err Errno.EINTR) = some env') :
    env'.wf = true := by
  rcases healthyStep_implies_allowedStep h with ⟨hAl, hWf, _, _, _, _, _⟩
  have hTr : isKernelNonFdTransient Errno.EINTR = true := by decide
  unfold allowedStep validateReqBeforeKernel allowedStepWaitpid at hAl
  dsimp only at hAl
  have hSt : env'.state = env.state := by
    split at hAl
    · simp [hTr] at hAl; exact hAl.symm
    · split at hAl
      · simp [hTr] at hAl; exact hAl.symm
      · split at hAl
        · simp [hTr] at hAl; exact hAl.symm
        · simp at hAl; exact hAl.symm
  unfold HealthyEnv.wf at hWf ⊢
  rw [hSt]
  exact hWf

/-- `Process.waitpidReapLoop` obeys `Model.allowedWaitpidReapLoop` over any `ProcessOpsM` obeying `Model.allowedSingleStep`. -/
theorem waitpidReapLoop_obeysStepFrom :
    Core.ObeysStepFrom (PkgApi := Model.WaitpidReapLoopFn)
      id HealthyEnv.wf Model.execSingleStep Model.allowedSingleStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.Process.waitpidReapLoop
      Model.execWaitpidReapLoop Model.allowedWaitpidReapLoop := by
  intro W proj ops hOps w req hWf
  rcases req with ⟨pid, fuel⟩
  dsimp only [Function.comp, id, Model.execWaitpidReapLoop, Model.allowedWaitpidReapLoop] at hWf ⊢
  induction fuel generalizing w with
  | zero =>
    simp [LeanSwe.LinuxSyscall.Process.waitpidReapLoop,
      Model.allowedWaitpidReapLoopAux, Pure.pure, StateT.run, stateT_pure_eq, hWf]
  | succ fuel ih =>
    have hStep := hOps w (.waitpid pid {}) hWf
    simp only [Model.execSingleStep, execProcessReq, Model.allowedSingleStep,
      Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq] at hStep
    simp only [LeanSwe.LinuxSyscall.Process.waitpidReapLoop,
      Model.allowedWaitpidReapLoopAux, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq]
    rcases hCall : ops.waitpid pid {} w with ⟨res, wMid⟩
    try rw [hCall] at hStep
    cases res with
    | ok wr =>
      dsimp only [stateT_pure_eq]
      exact Or.inl ⟨wr, rfl, hStep⟩
    | error e =>
      dsimp only at hStep ⊢
      by_cases hEi : e = Errno.EINTR
      · subst hEi
        simp only [beq_self_eq_true, ↓reduceIte]
        have hWfMid : (proj wMid).wf = true := healthyStep_waitpid_eintr_wf hStep
        exact Or.inr (Or.inr (Or.inr ⟨proj wMid, hStep, ih wMid hWfMid⟩))
      · have hEiF : (e == Errno.EINTR) = false := beq_false_of_ne hEi
        simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
        by_cases hEc : e = Errno.ECHILD
        · subst hEc
          simp only [beq_self_eq_true, ↓reduceIte]
          dsimp only [stateT_pure_eq]
          exact Or.inr (Or.inl ⟨rfl, hStep⟩)
        · have hEcF : (e == Errno.ECHILD) = false := beq_false_of_ne hEc
          simp only [hEcF, Bool.false_eq_true, ↓reduceIte]
          dsimp only [stateT_pure_eq]
          exact Or.inr (Or.inr (Or.inl ⟨e, hEi, hEc, rfl, hStep⟩))

private theorem execReapLoop_eq {W : Type} (ops : Model.HandleProcessOpsM (StateM W))
    (pid : Int32) :
    ∀ fuel : Nat,
      Model.execReapLoop ops pid fuel =
        LeanSwe.LinuxSyscall.Process.waitpidReapLoop ops pid fuel := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext w
    simp only [Model.execReapLoop, LeanSwe.LinuxSyscall.Process.waitpidReapLoop,
      Bind.bind, Pure.pure, stateT_bind_eq]
    rcases ops.waitpid pid {} w with ⟨res, w1⟩
    cases res with
    | ok _ => rfl
    | error e =>
      dsimp only
      by_cases h1 : (e == Errno.EINTR) = true
      · simp only [h1, ↓reduceIte, ih]
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]

/-- `Internal.mkProcessOps` lifts any raw C-ABI bundle obeying `Model.allowedRawStep` to `Model.allowedPkgStep`. -/
theorem mkProcessOps_obeysStepFrom :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkProcessOps Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases req with
  | syscall sreq =>
    exact mkProcessOps_obeysSingleStep proj raw hRaw w sreq hWf
  | reapLoop pid fuel =>
    have hSingle := mkProcessOps_obeysSingleStep proj raw hRaw
    have hReap := waitpidReapLoop_obeysStepFrom proj (Internal.mkProcessOps raw)
      hSingle w (pid, fuel) hWf
    dsimp only [Function.comp, id, Model.execWaitpidReapLoop,
      Model.allowedWaitpidReapLoop, StateT.run] at hReap
    dsimp only [Model.execPkgStep, Model.allowedPkgStep, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq]
    rw [execReapLoop_eq]
    exact hReap

/-- `Model.healthyModelOps` satisfies `Model.allowedPkgStep` from every well-formed `HealthyEnv`. -/
theorem healthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep Model.healthyModelOps) Model.allowedPkgStep := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  cases req with
  | syscall sreq =>
    exact healthyModelOps_obeysSingleStep env sreq hWf
  | reapLoop pid fuel =>
    have hReap := waitpidReapLoop_obeysStepFrom id Model.healthyModelOps
      healthyModelOps_obeysSingleStep env (pid, fuel) hWf
    dsimp only [Function.comp, id, Model.execWaitpidReapLoop,
      Model.allowedWaitpidReapLoop, StateT.run] at hReap
    dsimp only [Model.execPkgStep, Model.allowedPkgStep, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq]
    rw [execReapLoop_eq]
    exact hReap

end LeanSwe.LinuxSyscall.Process.Proofs
