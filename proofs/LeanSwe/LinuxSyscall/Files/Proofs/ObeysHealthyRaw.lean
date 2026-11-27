import LeanSwe.LinuxSyscall.Files.Proofs.ObeysHealthyPkg

/-!
# Raw Healthy Witness & Combinator Proofs for `LeanSwe.LinuxSyscall.Files`

Proves `rawHealthyModelOps_obeysStep`, `closeOpt_obeysStepFrom`, and
`setNonblockingOpt_obeysStepFrom` for `LeanSwe.LinuxSyscall.Files.Proofs`.
-/

namespace LeanSwe.LinuxSyscall.Files.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files

private theorem runHealthyStatOp_ok_roundtrip
    {req : FilesReq} {env env' : HealthyEnv} {st : StatInfo}
    (h : Model.runHealthyFilesOp req outcomeOfStatted
      (fun | .statted s => some (.ok s) | .err e => some (.error e) | _ => none)
      Model.statResFitsRaw env = (.ok st, env')) :
    StatInfo.ofRawTuple (Model.encodeRawStatTuple st) = st := by
  unfold Model.runHealthyFilesOp at h
  dsimp only at h
  let fbErr := Model.fallbackFilesErrno env.state req
  have hNotFb :
      (match healthyStep env req (.err fbErr) with
       | some envFb => (Except.error fbErr, envFb)
       | none => (Except.error fbErr, env)) ≠ (.ok st, env') := by
    cases healthyStep env req (.err fbErr) <;> simp
  rcases hEm : evalModel env.state req with ⟨candOut, _⟩
  rw [hEm] at h
  dsimp only at h
  cases hUnp : (match candOut with
    | .statted s => some (Except.ok s)
    | .err e => some (Except.error e)
    | _ => none) with
  | none => rw [hUnp] at h; exact absurd h hNotFb
  | some candRes =>
    rw [hUnp] at h
    dsimp only at h
    cases hFit : Model.statResFitsRaw candRes with
    | false =>
      rw [hFit] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h hNotFb
    | true =>
      rw [hFit] at h
      simp only [↓reduceIte] at h
      cases hSt : healthyStep env req (outcomeOfStatted candRes) with
      | none => rw [hSt] at h; exact absurd h hNotFb
      | some env1 =>
        rw [hSt] at h
        dsimp only at h
        cases hWf1 : env1.wf with
        | false =>
          rw [hWf1] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact absurd h hNotFb
        | true =>
          rw [hWf1] at h
          simp only [↓reduceIte] at h
          injection h with h1 _
          rw [h1] at hFit
          exact of_decide_eq_true hFit

/-- `Model.rawHealthyModelOps` satisfies `Model.allowedRawStep` from every well-formed `HealthyEnv`. -/
theorem rawHealthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  cases req with
  | openat d p flBits md =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hFl : Model.decodeRawOpenFlags? flBits with
    | none => simp [Model.outcomeOfRawOpened]
    | some fl =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.openat d p fl md) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.openat d p fl md env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | openat2 d p flBits md resBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hFl : Model.decodeRawOpenFlags? flBits with
    | none => simp [Model.outcomeOfRawOpened]
    | some fl =>
      cases hRs : Model.decodeRawResolveFlags? resBits with
      | none => simp [Model.outcomeOfRawOpened]
      | some rs =>
        dsimp only
        have hStep := healthyModelOps_obeysStep env (.openat2 d p { flags := fl, mode := md, resolve := rs }) hWf
        simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
        rcases hCall : Model.healthyModelOps.openat2 d p { flags := fl, mode := md, resolve := rs } env with ⟨res, env'⟩
        rw [hCall] at hStep
        cases res <;> simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | close h =>
    have hStep := healthyModelOps_obeysStep env (.close h) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.close h env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | read h n =>
    have hStep := healthyModelOps_obeysStep env (.read h n) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.read h n env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | write h bs =>
    have hStep := healthyModelOps_obeysStep env (.write h bs) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.write h bs env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | fstat h =>
    have hStep := healthyModelOps_obeysStep env (.fstat h) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.fstat h env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res with
    | error e => simpa [Model.outcomeOfRawStat, Model.toModelOutcome, outcomeOfStatted] using hStep
    | ok st =>
      have hRt := runHealthyStatOp_ok_roundtrip hCall
      simpa [Model.outcomeOfRawStat, Model.toModelOutcome, outcomeOfStatted, hRt] using hStep
  | fstatat d p flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_map_eq]
    cases hFl : Model.decodeRawAtFlags? flBits with
    | none => simp [Model.outcomeOfRawStat]
    | some fl =>
      dsimp only [Option.map]
      simp only [stateT_bind_eq]
      have hStep := healthyModelOps_obeysStep env (.fstatat d p fl) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.fstatat d p fl env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res with
      | error e => simpa [Model.outcomeOfRawStat, Model.toModelOutcome, outcomeOfStatted] using hStep
      | ok st =>
        have hRt := runHealthyStatOp_ok_roundtrip hCall
        simpa [Model.outcomeOfRawStat, Model.toModelOutcome, outcomeOfStatted, hRt] using hStep
  | faccessat d p mkBits flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hMk : Model.decodeRawAccessModeMask? mkBits with
    | none => simp [Model.outcomeOfRawUnit]
    | some mk =>
      cases hFl : Model.decodeRawAtFlags? flBits with
      | none => simp [Model.outcomeOfRawUnit]
      | some fl =>
        dsimp only
        have hStep := healthyModelOps_obeysStep env (.faccessat d p mk fl) hWf
        simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
        rcases hCall : Model.healthyModelOps.faccessat d p mk fl env with ⟨res, env'⟩
        rw [hCall] at hStep
        cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | mkdirat d p md =>
    have hStep := healthyModelOps_obeysStep env (.mkdirat d p md) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.mkdirat d p md env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | unlinkat d p rmByte =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hRm : Model.decodeRawUnlinkDir? rmByte with
    | none => simp [Model.outcomeOfRawUnit]
    | some rm =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.unlinkat d p rm) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.unlinkat d p rm env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | renameat2 od op nd np flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hFl : Model.decodeRawRenameFlags? flBits with
    | none => simp [Model.outcomeOfRawUnit]
    | some fl =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.renameat2 od op nd np fl) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.renameat2 od op nd np fl env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | symlinkat t d lp =>
    have hStep := healthyModelOps_obeysStep env (.symlinkat t d lp) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.symlinkat t d lp env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | readlinkat d p c =>
    have hStep := healthyModelOps_obeysStep env (.readlinkat d p c) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.readlinkat d p c env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | getdents64 h c =>
    have hStep := healthyModelOps_obeysStep env (.getdents64 h c) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.getdents64 h c env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | fchmodat d p md =>
    have hStep := healthyModelOps_obeysStep env (.fchmodat d p md) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.fchmodat d p md env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | fchmod h md =>
    have hStep := healthyModelOps_obeysStep env (.fchmod h md) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.fchmod h md env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | flock h opBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hOp : Model.decodeRawFlockOp? opBits with
    | none => simp [Model.outcomeOfRawUnit]
    | some op =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.flock h op) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.flock h op env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | fcntl h tg ag =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hCmd : Model.decodeRawFcntlCmd? tg ag with
    | none => simp [Model.outcomeOfRawU32]
    | some cmd =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.fcntl h cmd) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.fcntl h cmd env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | fsync h =>
    have hStep := healthyModelOps_obeysStep env (.fsync h) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.fsync h env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getcwd c =>
    have hStep := healthyModelOps_obeysStep env (.getcwd c) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.getcwd c env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | lseek h off whRaw =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hWh : Model.decodeRawSeekWhence? whRaw with
    | none => simp [Model.outcomeOfRawU64]
    | some wh =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.lseek h off wh) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.lseek h off wh env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawU64, Model.toModelOutcome, outcomeOfU64] using hStep
  | reopenReadOnly h =>
    have hStep := healthyModelOps_obeysStep env (.reopenReadOnly h) hWf
    simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.reopenReadOnly h env with ⟨res, env'⟩
    rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | dupStdio slRaw =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hSl : Model.decodeRawStdioFd? slRaw with
    | none => simp [Model.outcomeOfRawOpened]
    | some sl =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.dupStdio sl) hWf
      simp only [id, execPkgStep_eq, execFilesReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.dupStdio sl env with ⟨res, env'⟩
      rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep

/-- `Files.closeOpt` obeys `Model.allowedCloseOpt` over any `FilesOpsM` obeying `Model.allowedPkgStep`. -/
theorem closeOpt_obeysStepFrom :
    Core.ObeysStepFrom (PkgApi := Model.CloseOptFn)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.Files.closeOpt
      Model.execCloseOpt Model.allowedCloseOpt := by
  intro W proj ops hOps w optFd hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases optFd with
  | none =>
    simp [Model.execCloseOpt, LeanSwe.LinuxSyscall.Files.closeOpt,
      Model.allowedCloseOpt, Pure.pure, StateT.run, stateT_pure_eq, hWf]
  | some h =>
    have hStep := hOps w (.close h) hWf
    simp only [execPkgStep_eq, execFilesReq, Model.allowedPkgStep,
      Model.execCloseOpt, LeanSwe.LinuxSyscall.Files.closeOpt, Model.allowedCloseOpt,
      Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq,
      stateT_map_eq] at hStep ⊢
    rcases hCall : ops.close h w with ⟨res, w'⟩
    try rw [hCall] at hStep
    exact ⟨res, hStep⟩

/-- `Files.setNonblockingOpt` obeys `Model.allowedSetNonblockingOpt` over any `FilesOpsM` obeying `Model.allowedPkgStep`. -/
theorem setNonblockingOpt_obeysStepFrom :
    Core.ObeysStepFrom (PkgApi := Model.SetNonblockingOptFn)
      id HealthyEnv.wf Model.execPkgStep Model.allowedPkgStep
      HealthyEnv.wf LeanSwe.LinuxSyscall.Files.setNonblockingOpt
      Model.execSetNonblockingOpt Model.allowedSetNonblockingOpt := by
  intro W proj ops hOps w optFd hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases optFd with
  | none =>
    simp [Model.execSetNonblockingOpt, LeanSwe.LinuxSyscall.Files.setNonblockingOpt,
      Model.allowedSetNonblockingOpt, Pure.pure, StateT.run, stateT_pure_eq, hWf]
  | some h =>
    have hStep := hOps w (.fcntl h (.setFl true false)) hWf
    simp only [execPkgStep_eq, execFilesReq, Model.allowedPkgStep,
      Model.execSetNonblockingOpt, LeanSwe.LinuxSyscall.Files.setNonblockingOpt,
      Model.allowedSetNonblockingOpt, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq] at hStep ⊢
    rcases hCall : ops.fcntl h (.setFl true false) w with ⟨res, w'⟩
    try rw [hCall] at hStep
    exact ⟨res, hStep⟩

end LeanSwe.LinuxSyscall.Files.Proofs
