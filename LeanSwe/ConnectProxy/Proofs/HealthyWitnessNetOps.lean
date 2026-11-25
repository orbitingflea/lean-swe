import LeanSwe.ConnectProxy.Proofs.HealthyWitnessNetSend

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys

private theorem fallbackNetErrno_healthy (env : Net.HealthyEnv) (req : Net.NetReq)
    (hWf : env.wf = true) :
    ∃ env', Net.healthyStep env req (.err (fallbackNetErrno env.state req)) = some env' ∧
      env'.wf = true := by
  have hCore :
      Errno.isCriticalOsErrno (fallbackNetErrno env.state req) = false ∧
      (fallbackNetErrno env.state req == Errno.EINTR) = false ∧
      ∃ s', Net.stepNetCore env.state req (some (.err (fallbackNetErrno env.state req))) =
        some (.err (fallbackNetErrno env.state req), s') ∧
        s'.ambientSeccomp = env.state.ambientSeccomp := by
    unfold fallbackNetErrno Net.stepNetCore
    cases hPre : Net.preCheckNet req with
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
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepBind Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepBind Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepBind_spc env.state hid fid d addr _ hFid hSock hSpc⟩
      · rename_i hid bl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepListen Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepListen Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepListen_spc env.state hid fid d bl _ hFid hSock hSpc⟩
      · rename_i hid fl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepAccept4 Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepAccept4 Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepAccept4_spc env.state hid fid d fl _ hFid hSock hSpc⟩
      · rename_i hid addr
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepConnect Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepConnect Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepConnect_spc env.state hid fid d addr _ hFid hSock hSpc hNe⟩
      · rename_i hid opt
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepGetsockopt Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepGetsockopt Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepGetsockopt_spc env.state hid fid d opt _ hFid hSock hSpc⟩
      · rename_i hid opt val
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepSetsockopt Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepSetsockopt Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepSetsockopt_spc env.state hid fid d opt val _ hFid hSock hSpc⟩
      · rename_i hid
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepGetsockname Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepGetsockname Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepGetsockname_spc env.state hid fid d _ hFid hSock hSpc⟩
      · rename_i hid maxBytes fl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepRecvfrom Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepRecvfrom Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepRecvfrom_spc env.state hid fid d maxBytes fl _ hFid hSock hSpc hNe⟩
      · rename_i hid data fl
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepSendto Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepSendto Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepSendto_spc env.state hid fid d data fl _ hFid hSock hSpc hNe⟩
      · rename_i hid how
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepShutdown Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepShutdown Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, _, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepShutdown_spc env.state hid fid d how _ hFid hSock hSpc⟩
      · rename_i hid fds
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepSendmsg; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          by_cases hLive : (!fds.toList.all (Net.isLiveHandle env.state)) = true
          · simp only [hLive, ↓reduceIte]
            exact ⟨by decide, by decide, env.state,
              by unfold Net.stepSendmsg; rw [hFid]; simp only [hLive, ↓reduceIte]; exact emitErr_self_eq _ _ false, rfl⟩
          · have hLiveF : (!fds.toList.all (Net.isLiveHandle env.state)) = false := Bool.eq_false_iff.mpr hLive
            simp only [hLiveF, Bool.false_eq_true, ↓reduceIte]
            cases hSock : Net.lookupFileSocket env.state fid with
            | error fdErr =>
              dsimp only
              rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
                exact ⟨by decide, by decide, env.state,
                  by unfold Net.stepSendmsg; rw [hFid]; simp only [hLiveF, Bool.false_eq_true, ↓reduceIte]; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
            | ok d =>
              dsimp only
              obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
              exact ⟨hCrit, hEi, stepSendmsg_spc env.state hid fid d fds _ hFid hLiveF hSock hSpc hNe⟩
      · rename_i hid maxFds
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepRecvmsg Net.withSock; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepRecvmsg Net.withSock; rw [hFid]; dsimp only; rw [hSock]; exact emitErr_self_eq _ _ _, rfl⟩
          | ok d =>
            dsimp only
            obtain ⟨hSpc, hNe, hCrit, hEi⟩ := chosen_cases d.soError
            exact ⟨hCrit, hEi, stepRecvmsg_spc env.state hid fid d maxFds _ hFid hSock hSpc hNe⟩
      · rename_i hid op ifn
        cases hFid : Net.lookupHandleFileId env.state hid with
        | none =>
          dsimp only
          exact ⟨by decide, by decide, env.state,
            by unfold Net.stepIoctl; rw [hFid]; exact emitErr_self_eq _ _ false, rfl⟩
        | some fid =>
          dsimp only
          cases hSock : Net.lookupFileSocket env.state fid with
          | error fdErr =>
            dsimp only
            rcases lookupFileSocket_err_safe env.state fid fdErr hSock with rfl | rfl <;>
              exact ⟨by decide, by decide, env.state,
                by unfold Net.stepIoctl; rw [hFid]; dsimp only; rw [hSock]; rfl, rfl⟩
          | ok d =>
            dsimp only
            exact ⟨by decide, by decide, stepIoctl_spc env.state hid fid d op ifn hFid hSock⟩
  rcases hCore with ⟨hCrit, hEi, s', hStep, hSec⟩
  have hNotWf : (!env.wf) = false := by simp [hWf]
  refine ⟨{ state := s', eintrBudget := env.eintrBudget }, ?_, ?_⟩
  · simp [Net.healthyStep, hNotWf, Net.isCriticalFault, hCrit, Net.allowedStep, hStep,
      Net.isEintrOutcome, hEi]
  · unfold Net.HealthyEnv.wf at hWf ⊢
    rw [hSec]; exact hWf

/-- Internal ConnectProxy proof helper `runSampleNetOp`. -/
def runSampleNetOp {α : Type}
    (req : Net.NetReq)
    (pack : Except Errno α → Net.NetOutcome)
    (unpack : Net.NetOutcome → Option (Except Errno α)) :
    StateM HealthySysWorld (Except Errno α) := fun w =>
  let env := w.netEnv
  let fbErr := fallbackNetErrno env.state req
  let runFb (_ : Unit) : Except Errno α × HealthySysWorld :=
    match Net.healthyStep env req (.err fbErr) with
    | some envFb => (.error fbErr, { w with netEnv := envFb })
    | none => (.error fbErr, w)
  match Net.stepNetCore env.state req none with
  | some (candOut, _) =>
    match unpack candOut with
    | some candRes =>
      match Net.healthyStep env req (pack candRes) with
      | some env' =>
        if env'.wf then (candRes, { w with netEnv := env' })
        else runFb ()
      | none => runFb ()
    | none => runFb ()
  | none => runFb ()

/-- Internal ConnectProxy proof helper `runSampleNetOp_healthy`. -/
theorem runSampleNetOp_healthy {α : Type}
    (req : Net.NetReq)
    (pack : Except Errno α → Net.NetOutcome)
    (unpack : Net.NetOutcome → Option (Except Errno α))
    (hPackErr : ∀ e, pack (.error e) = .err e)
    (w : HealthySysWorld)
    (hWf : w.netEnv.wf = true) :
    Net.healthyStep w.netEnv req (pack ((runSampleNetOp req pack unpack).run w).1) =
      some ((runSampleNetOp req pack unpack).run w).2.netEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.netEnv.wf = true ∧
    ((runSampleNetOp req pack unpack).run w).2.filesEnv = w.filesEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.pollEnv = w.pollEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.dnsEnv = w.dnsEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.timeEnv = w.timeEnv ∧
    ((runSampleNetOp req pack unpack).run w).2.proxyTable = w.proxyTable := by
  obtain ⟨envFb, hFbStep, hFbWf⟩ := fallbackNetErrno_healthy w.netEnv req hWf
  unfold runSampleNetOp
  dsimp only [StateT.run, Id.run]
  let fbPair : Except Errno α × HealthySysWorld :=
    match Net.healthyStep w.netEnv req (.err (fallbackNetErrno w.netEnv.state req)) with
    | some ef => (.error (fallbackNetErrno w.netEnv.state req), { w with netEnv := ef })
    | none => (.error (fallbackNetErrno w.netEnv.state req), w)
  have hFbBranch :
      Net.healthyStep w.netEnv req (pack fbPair.1) = some fbPair.2.netEnv ∧
      fbPair.2.netEnv.wf = true ∧
      fbPair.2.filesEnv = w.filesEnv ∧
      fbPair.2.pollEnv = w.pollEnv ∧
      fbPair.2.dnsEnv = w.dnsEnv ∧
      fbPair.2.timeEnv = w.timeEnv ∧
      fbPair.2.proxyTable = w.proxyTable := by
    dsimp only [fbPair]
    rw [hFbStep]
    dsimp only
    rw [hPackErr]
    exact ⟨hFbStep, hFbWf, rfl, rfl, rfl, rfl, rfl⟩
  cases Net.stepNetCore w.netEnv.state req none with
  | none => exact hFbBranch
  | some pair =>
    dsimp only
    cases unpack pair.1 with
    | none => exact hFbBranch
    | some candRes =>
      dsimp only
      cases hStep : Net.healthyStep w.netEnv req (pack candRes) with
      | none => exact hFbBranch
      | some env' =>
        dsimp only
        by_cases hNextWf : env'.wf = true
        · have hIf : (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair) =
              (candRes, { w with netEnv := env' }) := by simp [hNextWf]
          change Net.healthyStep w.netEnv req (pack (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair).1) = _ ∧ _
          rw [hIf]; dsimp only
          exact ⟨hStep, hNextWf, rfl, rfl, rfl, rfl, rfl⟩
        · have hNextWfF : env'.wf = false := Bool.eq_false_iff.mpr hNextWf
          have hIf : (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair) = fbPair := by
            simp [hNextWfF]
          change Net.healthyStep w.netEnv req (pack (if env'.wf = true then (candRes, { w with netEnv := env' }) else fbPair).1) = _ ∧ _
          rw [hIf]
          exact hFbBranch

/-- Sample `NetOpsM` executing `Net.stepNetCore` with verified healthy fallback. -/
def sampleHealthyNetOps : Net.NetOpsM (StateM HealthySysWorld) Nat :=
  { socket := fun dom st fl p =>
      runSampleNetOp (.socket dom st fl p) Net.outcomeOfOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none)
    socketpair := fun dom st fl =>
      runSampleNetOp (.socketpair dom st fl) Net.outcomeOfPair
        (fun | .pair a b => some (.ok (a, b)) | .err e => some (.error e) | _ => none)
    bind := fun h sa =>
      runSampleNetOp (.bind h sa) Net.outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    listen := fun h bl =>
      runSampleNetOp (.listen h bl) Net.outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    accept4 := fun h fl =>
      runSampleNetOp (.accept4 h fl) Net.outcomeOfAccepted
        (fun | .accepted c sa => some (.ok (c, sa)) | .err e => some (.error e) | _ => none)
    connect := fun h sa =>
      runSampleNetOp (.connect h sa) Net.outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    getsockopt := fun h opt =>
      runSampleNetOp (.getsockopt h opt) Net.outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    setsockopt := fun h opt val =>
      runSampleNetOp (.setsockopt h opt val) Net.outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    getsockname := fun h =>
      runSampleNetOp (.getsockname h) Net.outcomeOfAddr
        (fun | .addr sa => some (.ok sa) | .err e => some (.error e) | _ => none)
    recvfrom := fun h n fl =>
      runSampleNetOp (.recvfrom h n fl) Net.outcomeOfBytes
        (fun | .bytes bs => some (.ok bs) | .err e => some (.error e) | _ => none)
    sendto := fun h bs fl =>
      runSampleNetOp (.sendto h bs fl) Net.outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none)
    shutdown := fun h how =>
      runSampleNetOp (.shutdown h how) Net.outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    sendmsg := fun h fds =>
      runSampleNetOp (.sendmsg h fds) Net.outcomeOfUnit
        (fun | .unit => some (.ok ()) | .err e => some (.error e) | _ => none)
    recvmsg := fun h mf =>
      runSampleNetOp (.recvmsg h mf) Net.outcomeOfFds
        (fun | .fds fs => some (.ok fs) | .err e => some (.error e) | _ => none)
    ioctl := fun h op ifn =>
      runSampleNetOp (.ioctl h op ifn) Net.outcomeOfU32
        (fun | .u32 v => some (.ok v) | .err e => some (.error e) | _ => none) }


end LeanSwe.ConnectProxy.Proofs
