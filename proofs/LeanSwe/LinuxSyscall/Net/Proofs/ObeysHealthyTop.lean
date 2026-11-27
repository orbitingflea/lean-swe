import LeanSwe.LinuxSyscall.Net.Proofs.ObeysHealthyIo

/-!
# Healthy-World Non-Vacuity Proofs for `LeanSwe.LinuxSyscall.Net`

Proves `healthyModelOps_obeysStep` and `rawHealthyModelOps_obeysStep` for
`LeanSwe.LinuxSyscall.Net.Proofs`.
-/

namespace LeanSwe.LinuxSyscall.Net.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net

private theorem fallbackNetErrno_healthy (env : HealthyEnv) (req : NetReq)
    (hWf : env.wf = true) :
    ∃ env', healthyStep env req (.err (Model.fallbackNetErrno env.state req)) = some env' ∧
      env'.wf = true := by
  have hCore :
      Errno.isCriticalOsErrno (Model.fallbackNetErrno env.state req) = false ∧
      (Model.fallbackNetErrno env.state req == Errno.EINTR) = false ∧
      ∃ s', stepNetCore env.state req (some (.err (Model.fallbackNetErrno env.state req))) =
        some (.err (Model.fallbackNetErrno env.state req), s') ∧
        s'.ambientSeccomp = env.state.ambientSeccomp := by
    unfold Model.fallbackNetErrno stepNetCore
    cases hPre : preCheckNet req with
    | some preErr =>
      dsimp only
      obtain ⟨hCrit, hEi⟩ := preCheckNet_safe req preErr hPre
      exact ⟨hCrit, hEi, env.state, emitErr_self_eq env.state preErr false, rfl⟩
    | none =>
      dsimp only
      cases req <;> dsimp only
      · exact ⟨by decide, by decide, env.state, rfl, rfl⟩
      · exact ⟨by decide, by decide, env.state, rfl, rfl⟩
      · rename_i hid addr
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepBind withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepBind withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepBind_spc env.state hid fid d addr _ hFid hSock hSpc⟩
      · rename_i hid bl
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepListen withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepListen withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepListen_spc env.state hid fid d bl _ hFid hSock hSpc⟩
      · rename_i hid fl
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepAccept4 withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepAccept4 withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepAccept4_spc env.state hid fid d fl _ hFid hSock hSpc⟩
      · rename_i hid addr
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepConnect withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepConnect withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepConnect_spc env.state hid fid d addr _ hFid hSock hSpc hNe⟩
      · rename_i hid opt
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepGetsockopt withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepGetsockopt withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepGetsockopt_spc env.state hid fid d opt _ hFid hSock hSpc⟩
      · rename_i hid opt val
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepSetsockopt withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepSetsockopt withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepSetsockopt_spc env.state hid fid d opt val _ hFid hSock hSpc⟩
      · rename_i hid
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepGetsockname withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepGetsockname withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepGetsockname_spc env.state hid fid d _ hFid hSock hSpc⟩
      · rename_i hid maxBytes fl
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepRecvfrom withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepRecvfrom withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepRecvfrom_spc env.state hid fid d maxBytes fl _ hFid hSock hSpc hNe⟩
      · rename_i hid data fl
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepSendto withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepSendto withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepSendto_spc env.state hid fid d data fl _ hFid hSock hSpc hNe⟩
      · rename_i hid how
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepShutdown withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepShutdown withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepShutdown_spc env.state hid fid d how _ hFid hSock hSpc⟩
      · rename_i hid fds
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepSendmsg; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          by_cases hLive : (!fds.toList.all (isLiveHandle env.state)) = true
          · simp only [hLive, ↓reduceIte]
            exact ⟨by decide, by decide, env.state,
              by unfold stepSendmsg; rw [hFid]; simp only [hLive, ↓reduceIte]; exact emitErr_self_eq _ _ false, rfl⟩
          · have hLiveF : (!fds.toList.all (isLiveHandle env.state)) = false := Bool.eq_false_iff.mpr hLive
            simp only [hLiveF, Bool.false_eq_true, ↓reduceIte]
            cases hSock : lookupFileSocket env.state fid with
            | error fdErr =>
              dsimp only
              rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
                exact ⟨by decide, by decide, env.state,
                  by unfold stepSendmsg; rw [hFid]; simp only [hLiveF, Bool.false_eq_true, ↓reduceIte]; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
            | ok d =>
              dsimp only
              obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
              exact ⟨hCrit, hEi, stepSendmsg_spc env.state hid fid d fds _ hFid hLiveF hSock hSpc hNe⟩
      · rename_i hid maxFds
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepRecvmsg withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepRecvmsg withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepRecvmsg_spc env.state hid fid d maxFds _ hFid hSock hSpc hNe⟩
      · rename_i hid op ifn
        cases hFid : lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold stepIoctl; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold stepIoctl; rw [hFid]; dsimp only; rw [hSock]; rfl, rfl⟩
          | ok d =>
            dsimp only
            exact ⟨by decide, by decide, stepIoctl_spc env.state hid fid d op ifn hFid hSock⟩
  rcases hCore with ⟨hCrit, hEi, s', hStep, hSec⟩
  have hNotWf : (!env.wf) = false := by simp [hWf]
  refine ⟨{ state := s', eintrBudget := env.eintrBudget }, ?_, ?_⟩
  · simp [healthyStep, hNotWf, isCriticalFault, hCrit, allowedStep, hStep,
      isEintrOutcome, hEi]
  · unfold HealthyEnv.wf at hWf ⊢
    rw [hSec]; exact hWf

private theorem runHealthyNetOp_obeys {α : Type}
    {req : NetReq}
    {pack : Except Errno α → NetOutcome}
    {unpack : NetOutcome → Option (Except Errno α)}
    {env : HealthyEnv}
    (hWf : env.wf = true)
    (hPackErr : ∀ e, pack (.error e) = .err e) :
    healthyStep env req (pack (Model.runHealthyNetOp req pack unpack env).1) =
      some (Model.runHealthyNetOp req pack unpack env).2 := by
  obtain ⟨envFb, hFbStep, _⟩ := fallbackNetErrno_healthy env req hWf
  unfold Model.runHealthyNetOp
  let fbPair : Except Errno α × HealthyEnv :=
    match healthyStep env req (.err (Model.fallbackNetErrno env.state req)) with
    | some ef => (.error (Model.fallbackNetErrno env.state req), ef)
    | none => (.error (Model.fallbackNetErrno env.state req), env)
  have hFbBranch : healthyStep env req (pack fbPair.1) = some fbPair.2 := by
    dsimp only [fbPair]
    rw [hFbStep]
    dsimp only
    rw [hPackErr]
    exact hFbStep
  cases stepNetCore env.state req none with
  | none => exact hFbBranch
  | some pair =>
    dsimp only
    cases unpack pair.1 with
    | none => exact hFbBranch
    | some candRes =>
      dsimp only
      cases hStep : healthyStep env req (pack candRes) with
      | none => exact hFbBranch
      | some env' =>
        dsimp only
        cases env'.wf with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hFbBranch
        | true => simp only [↓reduceIte]; exact hStep

/-- `Model.healthyModelOps` satisfies `Model.allowedPkgStep` from every well-formed `HealthyEnv`. -/
theorem healthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep Model.healthyModelOps) Model.allowedPkgStep := by
  intro env req hWf
  dsimp only [id] at hWf
  cases req <;>
  · dsimp only [id, Model.execPkgStep, execNetReq, Model.healthyModelOps,
      Model.allowedPkgStep, Functor.map, StateT.run, stateT_map_eq]
    apply runHealthyNetOp_obeys hWf
    intro _
    rfl

/-- `Model.rawHealthyModelOps` satisfies `Model.allowedRawStep` from every well-formed `HealthyEnv`. -/
theorem rawHealthyModelOps_obeysStep :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep := by
  intro env req hWf
  dsimp only [id] at hWf ⊢
  cases req with
  | socket domTag stTag flBits proto =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hDom : Model.decodeRawSockDomain? domTag with
    | none => simp [Model.outcomeOfRawOpened]
    | some dom =>
      cases hSt : Model.decodeRawSockType? stTag with
      | none => simp [Model.outcomeOfRawOpened]
      | some st =>
        cases hFl : Model.decodeRawSockFlags? flBits with
        | none => simp [Model.outcomeOfRawOpened]
        | some fl =>
          dsimp only
          have hStep := healthyModelOps_obeysStep env (.socket dom st fl proto) hWf
          simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
          rcases hCall : Model.healthyModelOps.socket dom st fl proto env with ⟨res, env'⟩
          try rw [hCall] at hStep
          cases res <;> simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | socketpair domTag stTag flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hDom : Model.decodeRawSockDomain? domTag with
    | none => simp [Model.outcomeOfRawPair]
    | some dom =>
      cases hSt : Model.decodeRawSockType? stTag with
      | none => simp [Model.outcomeOfRawPair]
      | some st =>
        cases hFl : Model.decodeRawSockFlags? flBits with
        | none => simp [Model.outcomeOfRawPair]
        | some fl =>
          dsimp only
          have hStep := healthyModelOps_obeysStep env (.socketpair dom st fl) hWf
          simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
          rcases hCall : Model.healthyModelOps.socketpair dom st fl env with ⟨res, env'⟩
          try rw [hCall] at hStep
          cases res with
          | ok p => rcases p with ⟨a, b⟩; simpa [Model.outcomeOfRawPair, Model.toModelOutcome, outcomeOfPair] using hStep
          | error e => simpa [Model.outcomeOfRawPair, Model.toModelOutcome, outcomeOfPair] using hStep
  | bind h rawSa =>
    have hStep := healthyModelOps_obeysStep env (.bind h (SockAddr.ofRawTuple rawSa)) hWf
    simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.bind h (SockAddr.ofRawTuple rawSa) env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | listen h bl =>
    have hStep := healthyModelOps_obeysStep env (.listen h bl) hWf
    simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.listen h bl env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | accept4 h flBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Bind.bind, Pure.pure, StateT.run, stateT_map_eq]
    cases hFl : Model.decodeRawSockFlags? flBits with
    | none => simp [Model.outcomeOfRawAccepted]
    | some fl =>
      dsimp only [Option.map]
      simp only [stateT_bind_eq]
      have hStep := healthyModelOps_obeysStep env (.accept4 h fl) hWf
      simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.accept4 h fl env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res with
      | ok p =>
        rcases p with ⟨cfd, sa⟩
        simpa [Model.outcomeOfRawAccepted, Model.toModelOutcome, outcomeOfAccepted,
          sockAddr_ofRawTuple_toRawTuple] using hStep
      | error e =>
        simpa [Model.outcomeOfRawAccepted, Model.toModelOutcome, outcomeOfAccepted] using hStep
  | connect h rawSa =>
    have hStep := healthyModelOps_obeysStep env (.connect h (SockAddr.ofRawTuple rawSa)) hWf
    simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.connect h (SockAddr.ofRawTuple rawSa) env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getsockopt h optTag =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hOpt : Model.decodeRawSockOpt? optTag with
    | none => simp [Model.outcomeOfRawU32]
    | some opt =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.getsockopt h opt) hWf
      simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.getsockopt h opt env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | setsockopt h optTag val =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hOpt : Model.decodeRawSetSockOpt? optTag with
    | none => simp [Model.outcomeOfRawUnit]
    | some opt =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.setsockopt h opt val) hWf
      simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.setsockopt h opt val env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getsockname h =>
    have hStep := healthyModelOps_obeysStep env (.getsockname h) hWf
    simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.getsockname h env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawAddr, Model.toModelOutcome, outcomeOfAddr,
        sockAddr_ofRawTuple_toRawTuple] using hStep
  | recvfrom h maxBytes mfBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hMf : Model.decodeRawMsgFlags? mfBits with
    | none => simp [Model.outcomeOfRawBytes]
    | some mf =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.recvfrom h maxBytes mf) hWf
      simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.recvfrom h maxBytes mf env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | sendto h data mfBits =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hMf : Model.decodeRawMsgFlags? mfBits with
    | none => simp [Model.outcomeOfRawU32]
    | some mf =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.sendto h data mf) hWf
      simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.sendto h data mf env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | shutdown h howTag =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hHow : Model.decodeRawShutHow? howTag with
    | none => simp [Model.outcomeOfRawUnit]
    | some how =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.shutdown h how) hWf
      simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.shutdown h how env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | sendmsg h fds =>
    have hStep := healthyModelOps_obeysStep env (.sendmsg h fds) hWf
    simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.sendmsg h fds env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | recvmsg h maxFds =>
    have hStep := healthyModelOps_obeysStep env (.recvmsg h maxFds) hWf
    simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, StateT.run, stateT_map_eq]
    rcases hCall : Model.healthyModelOps.recvmsg h maxFds env with ⟨res, env'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawFds, Model.toModelOutcome, outcomeOfFds] using hStep
  | ioctl h opTag arg ifn =>
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.rawHealthyModelOps, Functor.map, Pure.pure, StateT.run, stateT_map_eq]
    cases hOp : Model.decodeRawNetIoctlOp? opTag arg with
    | none => simp [Model.outcomeOfRawU32]
    | some op =>
      dsimp only [Option.map]
      have hStep := healthyModelOps_obeysStep env (.ioctl h op ifn) hWf
      simp only [id, Model.execPkgStep, execNetReq, Functor.map, StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep
      rcases hCall : Model.healthyModelOps.ioctl h op ifn env with ⟨res, env'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep

end LeanSwe.LinuxSyscall.Net.Proofs
