import LeanSwe.ConnectProxy.Proofs.SysBridgeTeardown

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge


private theorem closeSysFdAux_openedFds_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (d : Nat) :
    ∀ (fuel : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      ((closeSysFdAux (instrumentSysOps sys) d fuel).run (w, tr)).2.2.openedFds = tr.openedFds
  | 0, w, tr => by
    unfold closeSysFdAux
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    rw [inst_files_close]
    rcases sys.files.close d w with ⟨_, _⟩
    rfl
  | fuel + 1, w, tr => by
    unfold closeSysFdAux
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    rw [inst_files_close]
    rcases sys.files.close d w with ⟨r, w1⟩
    dsimp only
    cases r with
    | ok _ => rfl
    | error e =>
      by_cases hB : (e == Errno.EBUSY) = true
      · simp only [hB, ↓reduceIte]
        dsimp only [StateT.run, bind, StateT.bind, Id.run]
        rw [inst_time_nanosleep]
        rcases sys.timeRand.clock_nanosleep .monotonic false { sec := 0, nsec := 100000 } w1 with ⟨_, w2⟩
        exact closeSysFdAux_openedFds_eq sys d fuel w2 _
      · have hBF := Bool.eq_false_iff.mpr hB
        simp only [hBF, Bool.false_eq_true, ↓reduceIte]
        rfl

private theorem closeFd_openedFds_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (d : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    (((instrumentSysOps sys).closeFd d).run (w, tr)).2.2.openedFds = tr.openedFds :=
  closeSysFdAux_openedFds_eq sys d 64 w tr

private theorem closeOptFd_openedFds_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (optFd : Option Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    ((NetRelay.closeOptFd (instrumentSysOps sys).closeFd optFd).run (w, tr)).2.2.openedFds = tr.openedFds := by
  cases optFd with
  | none => rfl
  | some d => exact closeFd_openedFds_eq sys d w tr

private theorem teardownSlot_openedFds_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) :
    ((teardownSlot (instrumentSysOps sys) (fun _ => pure ()) slot events).run (w, tr)).2.2.openedFds = tr.openedFds := by
  unfold teardownSlot
  cases slot.phase with
  | handshake cfd _ _ =>
    dsimp only; rw [stateT_bind_run]
    have h1 := closeFd_openedFds_eq sys cfd w tr
    rcases hR1 : ((instrumentSysOps sys).closeFd cfd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1; dsimp only [stateT_pure_run] at h1 ⊢; exact h1
  | dns cfd _ _ _ =>
    dsimp only; rw [stateT_bind_run, stateT_pure_run]; dsimp only; rw [stateT_bind_run]
    have h1 := closeFd_openedFds_eq sys cfd w tr
    rcases hR1 : ((instrumentSysOps sys).closeFd cfd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1; dsimp only [stateT_pure_run] at h1 ⊢; exact h1
  | connecting cfd ufd _ _ _ _ _ _ =>
    dsimp only; rw [stateT_bind_run]
    have h1 := closeFd_openedFds_eq sys ufd w tr
    rcases hR1 : ((instrumentSysOps sys).closeFd ufd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1; dsimp only at h1 ⊢; rw [stateT_bind_run]
    have h2 := closeFd_openedFds_eq sys cfd w1 tr1
    rcases hR2 : ((instrumentSysOps sys).closeFd cfd).run (w1, tr1) with ⟨_, w2, tr2⟩
    rw [hR2] at h2; dsimp only [stateT_pure_run] at h2 ⊢; exact h2.trans h1
  | relay st =>
    unfold Relay.closeRelayBoth
    dsimp only; rw [stateT_bind_run, stateT_bind_run]
    have h1 := closeOptFd_openedFds_eq sys st.clientFd? w tr
    rcases hR1 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd st.clientFd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1; dsimp only at h1 ⊢; rw [stateT_bind_run]
    have h2 := closeOptFd_openedFds_eq sys st.upstreamFd? w1 tr1
    rcases hR2 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd st.upstreamFd?).run (w1, tr1) with ⟨_, w2, tr2⟩
    rw [hR2] at h2; dsimp only [stateT_pure_run] at h2 ⊢; exact h2.trans h1
  | closingReply cfd? _ _ _ _ _ =>
    dsimp only; rw [stateT_bind_run]
    have h1 := closeOptFd_openedFds_eq sys cfd? w tr
    rcases hR1 : (NetRelay.closeOptFd (instrumentSysOps sys).closeFd cfd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1; dsimp only [stateT_pure_run] at h1 ⊢; exact h1
  | done => rfl

/-- Internal ConnectProxy proof helper `teardownAllSlotsList_openedFds_eq`. -/
theorem teardownAllSlotsList_openedFds_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat) :
    ∀ (slots : List (ClientSlot Nat Unit)) (events : Array ConnectEvent)
      (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      ((teardownAllSlotsList (instrumentSysOps sys) (fun _ => pure ()) slots events).run (w, tr)).2.2.openedFds = tr.openedFds
  | [], _, _, _ => rfl
  | slot :: rest, events, w, tr => by
    unfold teardownAllSlotsList
    rw [stateT_bind_run]
    have h1 := teardownSlot_openedFds_eq sys slot events w tr
    rcases hR1 : (teardownSlot (instrumentSysOps sys) (fun _ => pure ()) slot events).run (w, tr) with ⟨ev1, w1, tr1⟩
    rw [hR1] at h1
    dsimp only at h1 ⊢
    exact (teardownAllSlotsList_openedFds_eq sys rest ev1 w1 tr1).trans h1

private theorem closeLfdAndReturnErr_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (w₀ w w₁ : HealthySysWorld) (tr₀ tr tr₁ : SysAuditTrace Nat)
    (reqPort : UInt16) (lfd : Nat) (err : ProxyError)
    (res : Except ProxyError (Nat × Nat × Nat × UInt16))
    (hWf : w.wf = true)
    (hTbl : w.proxyTable = w₀.proxyTable)
    (hNd : (w₀.filesEnv.state.fds.map Prod.fst).Nodup → (w.filesEnv.state.fds.map Prod.fst).Nodup)
    (hDq : tr.dnsQueries = tr₀.dnsQueries)
    (hDa : tr.dialedAddrs = tr₀.dialedAddrs)
    (hBa : ∀ sa ∈ tr.boundAddrs.toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = .ipv4 Net.INADDR_LOOPBACK reqPort)
    (hOp : tr.openedFds = tr₀.openedFds.push lfd)
    (hMsg : err.message ≠ "" ∧ (w₀.netEnv.eintrBudget ≤ MAX_EINTR_RETRIES → err.errnoCode ≠ some Errno.EINTR))
    (hRun : StateT.run (do (instrumentSysOps sys).closeFd lfd; pure (Except.error err)) (w, tr) = (res, (w₁, tr₁))) :
    w₁.wf = true ∧
    w₁.proxyTable = w₀.proxyTable ∧
    tr₁.dnsQueries = tr₀.dnsQueries ∧
    tr₁.dialedAddrs = tr₀.dialedAddrs ∧
    (∀ sa ∈ tr₁.boundAddrs.toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = .ipv4 Net.INADDR_LOOPBACK reqPort) ∧
    ((w₀.filesEnv.state.fds.map Prod.fst).Nodup → (w₁.filesEnv.state.fds.map Prod.fst).Nodup) ∧
    res = .error err ∧
    (err.message ≠ "" ∧ (w₀.netEnv.eintrBudget ≤ MAX_EINTR_RETRIES → err.errnoCode ≠ some Errno.EINTR)) ∧
    ((w₀.filesEnv.state.fds.map Prod.fst).Nodup →
      ∀ fd ∈ tr₁.openedFds.toList,
        fd ∈ tr₀.openedFds.toList ∨
        (fd ∈ tr₁.closedFds.toList ∧ Files.assocGet w₁.filesEnv.state.fds fd = none)) := by
  obtain ⟨u, wC, trC, hC, hRun⟩ := stateT_bind_eq hRun
  dsimp only [stateT_pure_run] at hRun
  injection hRun with hr hwt; injection hwt with hwe hte
  subst hr; subst hwe; subst hte
  have hCl := healthy_closeFd_instrumented_laws sys hRef w tr lfd hWf
  have hC' : ((instrumentSysOps sys).closeFd lfd).run (w, tr) = (u, (wC, trC)) := hC
  rw [hC'] at hCl; clear hC hC'
  dsimp only at hCl ⊢
  rcases hCl with ⟨hWf₁, hTbl₁, hTr₁, _, hNdCl⟩
  rw [hTr₁]
  refine ⟨hWf₁, hTbl₁.trans hTbl, hDq, hDa, hBa, fun hNd₀ => (hNdCl (hNd hNd₀)).1, rfl, hMsg, fun hNd₀ fd hMem => ?_⟩
  rw [hOp, Array.toList_push, List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hOld | rfl
  · exact Or.inl hOld
  · refine Or.inr ⟨?_, (hNdCl (hNd hNd₀)).2⟩
    simp [Array.toList_push]

private theorem errnoToProxyError_not_eintr {α : Type} (port : UInt16) (e : Errno) (hNe : Except.error e ≠ (Except.error Errno.EINTR : Except Errno α)) :
    (errnoToProxyError port e).errnoCode ≠ some Errno.EINTR := by
  rw [(errnoToProxyError_laws port e).2.1]
  intro hc
  injection hc with he
  exact hNe (congrArg Except.error he)

/-- `createListener` over ANY `sys` refining `RefinesHealthyCProxySys`: binds strictly to `127.0.0.1` (`INADDR_LOOPBACK`), makes zero DNS or `connect` calls, preserves `wf`, `Nodup`, and `proxyTable`, resolves `boundPort ≠ 0` (`listenPort = 0` or `boundPort = listenPort`) on `.ok` (opening exact `#[lfd, wakeR, wakeW]`), never surfaces `EINTR` when `eintrBudget ≤ MAX_EINTR_RETRIES`, and deterministically closes + erases every opened socket on `.error`! -/
theorem healthy_createListener_instrumented_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (vcfg : ValidProxyConfig)
    (w₀ : HealthySysWorld) (tr₀ : SysAuditTrace Nat)
    (hWf₀ : w₀.wf = true) :
    let (res, (w₁, tr₁)) := (createListener (instrumentSysOps sys) vcfg).run (w₀, tr₀)
    w₁.wf = true ∧
    w₁.proxyTable = w₀.proxyTable ∧
    tr₁.dnsQueries = tr₀.dnsQueries ∧
    tr₁.dialedAddrs = tr₀.dialedAddrs ∧
    (∀ sa ∈ tr₁.boundAddrs.toList,
      sa ∈ tr₀.boundAddrs.toList ∨ sa = .ipv4 Net.INADDR_LOOPBACK vcfg.config.listenPort) ∧
    ((w₀.filesEnv.state.fds.map Prod.fst).Nodup → (w₁.filesEnv.state.fds.map Prod.fst).Nodup) ∧
    match res with
    | .ok (lfd, wakeR, wakeW, boundPort) =>
      boundPort ≠ 0 ∧
      (vcfg.config.listenPort = 0 ∨ boundPort = vcfg.config.listenPort) ∧
      tr₁.openedFds = ((tr₀.openedFds.push lfd).push wakeR).push wakeW
    | .error err =>
      (err.message ≠ "" ∧ (w₀.netEnv.eintrBudget ≤ MAX_EINTR_RETRIES → err.errnoCode ≠ some Errno.EINTR)) ∧
      ((w₀.filesEnv.state.fds.map Prod.fst).Nodup →
        ∀ fd ∈ tr₁.openedFds.toList,
          fd ∈ tr₀.openedFds.toList ∨
          (fd ∈ tr₁.closedFds.toList ∧ Files.assocGet w₁.filesEnv.state.fds fd = none)) := by
  let fdsNd (w : HealthySysWorld) : Prop := (w.filesEnv.state.fds.map Prod.fst).Nodup
  rcases hTop : (createListener (instrumentSysOps sys) vcfg).run (w₀, tr₀) with ⟨res, w₁, tr₁⟩
  have hRun : StateT.run (createListener (instrumentSysOps sys) vcfg) (w₀, tr₀) = (res, (w₁, tr₁)) := hTop
  clear hTop
  dsimp only
  unfold createListener at hRun
  cases hVal : validateStartLimits vcfg with
  | error err =>
    rw [hVal] at hRun
    dsimp only [stateT_pure_run] at hRun
    injection hRun with hr hwt; injection hwt with hwe hte
    subst hr; subst hwe; subst hte
    have hMsg : err.message ≠ "" ∧ err.errnoCode = none := by
      unfold validateStartLimits at hVal
      dsimp only at hVal
      split at hVal
      · injection hVal with he; subst he; exact ⟨by decide, rfl⟩
      · cases hVal
    exact ⟨hWf₀, rfl, rfl, rfl, fun _ h => Or.inl h, id,
      ⟨hMsg.1, fun _ hc => by rw [hMsg.2] at hc; nomatch hc⟩, fun _ _ hm => Or.inl hm⟩
  | ok _ =>
    rw [hVal] at hRun
    dsimp only at hRun
    let reqPort := vcfg.config.listenPort
    let bindAddr := Net.SockAddr.ipv4 Net.INADDR_LOOPBACK reqPort
    have hEinvalMsg : (Model.mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port")).message ≠ "" ∧
        (w₀.netEnv.eintrBudget ≤ MAX_EINTR_RETRIES →
          (Model.mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port")).errnoCode ≠ some Errno.EINTR) := by
      have hm := mapRawErrorPure_laws (.otherError Errno.EINVAL "getsockname returned invalid loopback port")
      exact ⟨hm.1, fun _ hc => by rw [hm.2.2] at hc; revert hc; decide⟩
    obtain ⟨r1, w1, tr1, hR1, hRun⟩ := stateT_bind_eq hRun
    have hSock := retryEintr_budget_laws
      (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.netEnv.eintrBudget)
      (fun wt =>
        wt.1.wf = true ∧ wt.1.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wt.1) ∧
        wt.2.dnsQueries = tr₀.dnsQueries ∧ wt.2.dialedAddrs = tr₀.dialedAddrs ∧
        wt.2.boundAddrs = tr₀.boundAddrs ∧ wt.2.openedFds = tr₀.openedFds)
      (fun r wt =>
        wt.1.wf = true ∧ wt.1.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wt.1) ∧
        wt.2.dnsQueries = tr₀.dnsQueries ∧ wt.2.dialedAddrs = tr₀.dialedAddrs ∧
        wt.2.boundAddrs = tr₀.boundAddrs ∧
        match r with
        | .error _ => wt.2.openedFds = tr₀.openedFds
        | .ok lfd => wt.2.openedFds = tr₀.openedFds.push lfd)
      ((instrumentSysOps sys).net.socket .inet .stream { nonblock := true, cloexec := true } 0)
      (fun ⟨wx, trx⟩ ⟨hwx, htbl, hnd, hdq, hda, hba, hop⟩ => by
        have hn := hRef.2.1 wx (.socket .inet .stream { nonblock := true, cloexec := true } 0) ((wf_iff_parts wx).mp hwx)
        dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
          pure, Pure.pure, StateT.pure, Id.run] at hn
        dsimp only [StateT.run]
        rw [inst_net_socket]
        rcases hS : sys.net.socket .inet .stream { nonblock := true, cloexec := true } 0 wx with ⟨sr, wx'⟩
        rw [hS] at hn
        dsimp only at hn ⊢
        have hwx' : wx'.wf = true := (wf_iff_parts wx').mpr hn.2.1
        have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.socket .inet .stream { nonblock := true, cloexec := true } 0) (Net.outcomeOfOpened sr) hn.1
        cases sr with
        | error e =>
          dsimp only
          refine ⟨fun hEi => ?_, fun hNe => ?_, ⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, hop⟩⟩
          · injection hEi with he; subst he
            exact ⟨⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, hop⟩, hBud.1 rfl⟩
          · have hNeOut : Net.outcomeOfOpened (.error e) ≠ .err Errno.EINTR := fun hc => by injection hc with he; exact hNe (congrArg Except.error he)
            exact Nat.le_of_eq (hBud.2 hNeOut)
        | ok lfd =>
          dsimp only
          exact ⟨(fun hBad => nomatch hBad), fun _ => Nat.le_of_eq (hBud.2 (fun hc => nomatch hc)),
                 ⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, by rw [hop]⟩⟩)
      MAX_EINTR_RETRIES (w₀, tr₀) ⟨hWf₀, rfl, id, rfl, rfl, rfl, rfl⟩
    have hR1' : (retryEintr
      ((instrumentSysOps sys).net.socket .inet .stream { nonblock := true, cloexec := true } 0)
      MAX_EINTR_RETRIES).run (w₀, tr₀) = (r1, (w1, tr1)) := hR1
    rw [hR1'] at hSock; clear hR1 hR1'
    dsimp only at hSock
    rcases hSock with ⟨⟨hWf1, hTbl1, hNd1, hDq1, hDa1, hBa1, hOp1⟩, hBudLe1, hNoEi1⟩
    cases r1 with
    | error e =>
      dsimp only [stateT_pure_run] at hRun
      injection hRun with hr hwt; injection hwt with hwe hte
      subst hr; subst hwe; subst hte
      exact ⟨hWf1, hTbl1, hDq1, hDa1, fun sa hm => Or.inl (hBa1 ▸ hm), hNd1,
        ⟨(errnoToProxyError_laws reqPort e).1, fun hB => errnoToProxyError_not_eintr reqPort e (hNoEi1 hB)⟩,
        fun _ fd hm => Or.inl (hOp1 ▸ hm)⟩
    | ok lfd =>
      dsimp only at hOp1 hRun
      obtain ⟨r2, w2, tr2, hR2, hRun⟩ := stateT_bind_eq hRun
      have hSetOpt := retryEintr_budget_laws
        (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.netEnv.eintrBudget)
        (fun (w, tr) => w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧ tr = tr1)
        (fun _ (w, tr) => w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧ tr = tr1)
        ((instrumentSysOps sys).net.setsockopt lfd .reuseAddr 1)
        (fun ⟨wx, trx⟩ ⟨hwx, htbl, hnd, htr⟩ => by
          have hn := hRef.2.1 wx (.setsockopt lfd .reuseAddr 1) ((wf_iff_parts wx).mp hwx)
          dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
            pure, Pure.pure, StateT.pure, Id.run] at hn
          dsimp only [StateT.run]
          rw [inst_net_setsockopt]
          rcases hS : sys.net.setsockopt lfd .reuseAddr 1 wx with ⟨sr, wx'⟩
          rw [hS] at hn
          dsimp only at hn ⊢
          have hP : wx'.wf = true ∧ wx'.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wx') ∧ trx = tr1 :=
            ⟨(wf_iff_parts wx').mpr hn.2.1, hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), htr⟩
          have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.setsockopt lfd .reuseAddr 1) (Net.outcomeOfUnit sr) hn.1
          refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
          · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
          · cases sr with
            | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
            | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he)))
        )
        MAX_EINTR_RETRIES (w1, tr1) ⟨hWf1, hTbl1, hNd1, rfl⟩
      have hR2' : (retryEintr ((instrumentSysOps sys).net.setsockopt lfd .reuseAddr 1) MAX_EINTR_RETRIES).run (w1, tr1) = (r2, (w2, tr2)) := hR2
      rw [hR2'] at hSetOpt; clear hR2 hR2'
      dsimp only at hSetOpt
      rcases hSetOpt with ⟨⟨hWf2, hTbl2, hNd2, hTr2⟩, hBudLe2, hNoEi2⟩
      rw [hTr2] at hRun
      cases r2 with
      | error e =>
        dsimp only at hRun
        obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
          closeLfdAndReturnErr_of_eq sys hRef w₀ w2 w₁ tr₀ tr1 tr₁ reqPort lfd (errnoToProxyError reqPort e) res
            hWf2 hTbl2 hNd2 hDq1 hDa1 (fun sa hm => Or.inl (hBa1 ▸ hm)) hOp1
            ⟨(errnoToProxyError_laws reqPort e).1, fun hB => errnoToProxyError_not_eintr reqPort e (hNoEi2 (Nat.le_trans hBudLe1 hB))⟩ hRun
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      | ok _ =>
        dsimp only at hRun
        obtain ⟨r3, w3, tr3, hR3, hRun⟩ := stateT_bind_eq hRun
        have hBind := retryEintr_budget_laws
          (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.netEnv.eintrBudget)
          (fun (w, tr) =>
            w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧
            tr.dnsQueries = tr₀.dnsQueries ∧ tr.dialedAddrs = tr₀.dialedAddrs ∧
            (∀ sa ∈ tr.boundAddrs.toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = bindAddr) ∧
            tr.openedFds = tr₀.openedFds.push lfd)
          (fun _ (w, tr) =>
            w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧
            tr.dnsQueries = tr₀.dnsQueries ∧ tr.dialedAddrs = tr₀.dialedAddrs ∧
            (∀ sa ∈ tr.boundAddrs.toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = bindAddr) ∧
            tr.openedFds = tr₀.openedFds.push lfd)
          ((instrumentSysOps sys).net.bind lfd bindAddr)
          (fun ⟨wx, trx⟩ ⟨hwx, htbl, hnd, hdq, hda, hba, hop⟩ => by
            have hn := hRef.2.1 wx (.bind lfd bindAddr) ((wf_iff_parts wx).mp hwx)
            dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
              pure, Pure.pure, StateT.pure, Id.run] at hn
            dsimp only [StateT.run]
            rw [inst_net_bind]
            rcases hS : sys.net.bind lfd bindAddr wx with ⟨sr, wx'⟩
            rw [hS] at hn
            dsimp only at hn ⊢
            have hBaNext : ∀ sa ∈ (trx.boundAddrs.push bindAddr).toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = bindAddr := by
              intro sa hm
              rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
              rcases hm with hPrev | rfl
              · exact hba sa hPrev
              · exact Or.inr rfl
            have hP : wx'.wf = true ∧ wx'.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wx') ∧
                trx.dnsQueries = tr₀.dnsQueries ∧ trx.dialedAddrs = tr₀.dialedAddrs ∧
                (∀ sa ∈ (trx.boundAddrs.push bindAddr).toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = bindAddr) ∧
                trx.openedFds = tr₀.openedFds.push lfd :=
              ⟨(wf_iff_parts wx').mpr hn.2.1, hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0),
                hdq, hda, hBaNext, hop⟩
            have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.bind lfd bindAddr) (Net.outcomeOfUnit sr) hn.1
            refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
            · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
            · cases sr with
              | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
              | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he))))
          MAX_EINTR_RETRIES (w2, tr1) ⟨hWf2, hTbl2, hNd2, hDq1, hDa1, fun sa hm => Or.inl (hBa1 ▸ hm), hOp1⟩
        have hR3' : (retryEintr ((instrumentSysOps sys).net.bind lfd bindAddr) MAX_EINTR_RETRIES).run (w2, tr1) = (r3, (w3, tr3)) := hR3
        rw [hR3'] at hBind; clear hR3 hR3'
        dsimp only at hBind
        rcases hBind with ⟨⟨hWf3, hTbl3, hNd3, hDq3, hDa3, hBa3, hOp3⟩, hBudLe3, hNoEi3⟩
        cases r3 with
        | error e =>
          dsimp only at hRun
          obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
            closeLfdAndReturnErr_of_eq sys hRef w₀ w3 w₁ tr₀ tr3 tr₁ reqPort lfd (errnoToProxyError reqPort e) res
              hWf3 hTbl3 hNd3 hDq3 hDa3 hBa3 hOp3
              ⟨(errnoToProxyError_laws reqPort e).1, fun hB => errnoToProxyError_not_eintr reqPort e (hNoEi3 (Nat.le_trans hBudLe2 (Nat.le_trans hBudLe1 hB)))⟩ hRun
          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
        | ok _ =>
          dsimp only at hRun
          obtain ⟨r4, w4, tr4, hR4, hRun⟩ := stateT_bind_eq hRun
          have hListen := retryEintr_budget_laws
            (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.netEnv.eintrBudget)
            (fun (w, tr) => w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧ tr = tr3)
            (fun _ (w, tr) => w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧ tr = tr3)
            ((instrumentSysOps sys).net.listen lfd 128)
            (fun ⟨wx, trx⟩ ⟨hwx, htbl, hnd, htr⟩ => by
              have hn := hRef.2.1 wx (.listen lfd 128) ((wf_iff_parts wx).mp hwx)
              dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
                pure, Pure.pure, StateT.pure, Id.run] at hn
              dsimp only [StateT.run]
              rw [inst_net_listen]
              rcases hS : sys.net.listen lfd 128 wx with ⟨sr, wx'⟩
              rw [hS] at hn
              dsimp only at hn ⊢
              have hP : wx'.wf = true ∧ wx'.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wx') ∧ trx = tr3 :=
                ⟨(wf_iff_parts wx').mpr hn.2.1, hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), htr⟩
              have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.listen lfd 128) (Net.outcomeOfUnit sr) hn.1
              refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
              · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
              · cases sr with
                | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
                | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he))))
            MAX_EINTR_RETRIES (w3, tr3) ⟨hWf3, hTbl3, hNd3, rfl⟩
          have hR4' : (retryEintr ((instrumentSysOps sys).net.listen lfd 128) MAX_EINTR_RETRIES).run (w3, tr3) = (r4, (w4, tr4)) := hR4
          rw [hR4'] at hListen; clear hR4 hR4'
          dsimp only at hListen
          rcases hListen with ⟨⟨hWf4, hTbl4, hNd4, hTr4⟩, hBudLe4, hNoEi4⟩
          rw [hTr4] at hRun
          cases r4 with
          | error e =>
            dsimp only at hRun
            obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
              closeLfdAndReturnErr_of_eq sys hRef w₀ w4 w₁ tr₀ tr3 tr₁ reqPort lfd (errnoToProxyError reqPort e) res
                hWf4 hTbl4 hNd4 hDq3 hDa3 hBa3 hOp3
                ⟨(errnoToProxyError_laws reqPort e).1, fun hB => errnoToProxyError_not_eintr reqPort e (hNoEi4 (by omega))⟩ hRun
            exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
          | ok _ =>
            dsimp only at hRun
            obtain ⟨r5, w5, tr5, hR5, hRun⟩ := stateT_bind_eq hRun
            have hGs := retryEintr_budget_laws
              (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.netEnv.eintrBudget)
              (fun (w, tr) => w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧ tr = tr3)
              (fun _ (w, tr) => w.wf = true ∧ w.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd w) ∧ tr = tr3)
              ((instrumentSysOps sys).net.getsockname lfd)
              (fun ⟨wx, trx⟩ ⟨hwx, htbl, hnd, htr⟩ => by
                have hn := hRef.2.1 wx (.getsockname lfd) ((wf_iff_parts wx).mp hwx)
                dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
                  pure, Pure.pure, StateT.pure, Id.run] at hn
                dsimp only [StateT.run]
                rw [inst_net_getsockname]
                rcases hS : sys.net.getsockname lfd wx with ⟨sr, wx'⟩
                rw [hS] at hn
                dsimp only at hn ⊢
                have hP : wx'.wf = true ∧ wx'.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wx') ∧ trx = tr3 :=
                  ⟨(wf_iff_parts wx').mpr hn.2.1, hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), htr⟩
                have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.getsockname lfd) (Net.outcomeOfAddr sr) hn.1
                refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
                · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
                · cases sr with
                  | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
                  | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he))))
              MAX_EINTR_RETRIES (w4, tr3) ⟨hWf4, hTbl4, hNd4, rfl⟩
            have hR5' : (retryEintr ((instrumentSysOps sys).net.getsockname lfd) MAX_EINTR_RETRIES).run (w4, tr3) = (r5, (w5, tr5)) := hR5
            rw [hR5'] at hGs; clear hR5 hR5'
            dsimp only at hGs
            rcases hGs with ⟨⟨hWf5, hTbl5, hNd5, hTr5⟩, hBudLe5, hNoEi5⟩
            rw [hTr5] at hRun
            cases r5 with
            | error e =>
              dsimp only at hRun
              obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
                closeLfdAndReturnErr_of_eq sys hRef w₀ w5 w₁ tr₀ tr3 tr₁ reqPort lfd (errnoToProxyError reqPort e) res
                  hWf5 hTbl5 hNd5 hDq3 hDa3 hBa3 hOp3
                  ⟨(errnoToProxyError_laws reqPort e).1, fun hB => errnoToProxyError_not_eintr reqPort e (hNoEi5 (by omega))⟩ hRun
              exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
            | ok boundSa =>
              dsimp only at hRun
              cases boundSa with
              | unix _ =>
                dsimp only at hRun
                obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
                  closeLfdAndReturnErr_of_eq sys hRef w₀ w5 w₁ tr₀ tr3 tr₁ reqPort lfd
                    (Model.mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port")) res
                    hWf5 hTbl5 hNd5 hDq3 hDa3 hBa3 hOp3 hEinvalMsg hRun
                exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
              | ipv6 _ _ _ _ _ =>
                dsimp only at hRun
                obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
                  closeLfdAndReturnErr_of_eq sys hRef w₀ w5 w₁ tr₀ tr3 tr₁ reqPort lfd
                    (Model.mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port")) res
                    hWf5 hTbl5 hNd5 hDq3 hDa3 hBa3 hOp3 hEinvalMsg hRun
                exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
              | ipv4 ip boundPort =>
                dsimp only at hRun
                by_cases hCond : (ip == Net.INADDR_LOOPBACK && boundPort != 0 && (vcfg.config.listenPort == 0 || boundPort == vcfg.config.listenPort)) = true
                · simp only [hCond, ↓reduceIte] at hRun
                  have hCond' := hCond
                  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hCond'
                  have hBpNe : boundPort ≠ 0 := hCond'.1.2
                  have hBpMatch : reqPort = 0 ∨ boundPort = reqPort := hCond'.2
                  obtain ⟨r6, w6, tr6, hR6, hRun⟩ := stateT_bind_eq hRun
                  have hPair := retryEintr_budget_laws
                    (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.netEnv.eintrBudget)
                    (fun wt =>
                      wt.1.wf = true ∧ wt.1.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wt.1) ∧
                      wt.2.dnsQueries = tr₀.dnsQueries ∧ wt.2.dialedAddrs = tr₀.dialedAddrs ∧
                      (∀ sa ∈ wt.2.boundAddrs.toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = bindAddr) ∧
                      wt.2.openedFds = tr₀.openedFds.push lfd)
                    (fun r wt =>
                      wt.1.wf = true ∧ wt.1.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wt.1) ∧
                      wt.2.dnsQueries = tr₀.dnsQueries ∧ wt.2.dialedAddrs = tr₀.dialedAddrs ∧
                      (∀ sa ∈ wt.2.boundAddrs.toList, sa ∈ tr₀.boundAddrs.toList ∨ sa = bindAddr) ∧
                      match r with
                      | .error _ => wt.2.openedFds = tr₀.openedFds.push lfd
                      | .ok (wakeR, wakeW) => wt.2.openedFds = ((tr₀.openedFds.push lfd).push wakeR).push wakeW)
                    ((instrumentSysOps sys).net.socketpair .unix .stream { nonblock := true, cloexec := true })
                    (fun ⟨wx, trx⟩ ⟨hwx, htbl, hnd, hdq, hda, hba, hop⟩ => by
                      have hn := hRef.2.1 wx (.socketpair .unix .stream { nonblock := true, cloexec := true }) ((wf_iff_parts wx).mp hwx)
                      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
                        pure, Pure.pure, StateT.pure, Id.run] at hn
                      dsimp only [StateT.run]
                      rw [inst_net_socketpair]
                      rcases hS : sys.net.socketpair .unix .stream { nonblock := true, cloexec := true } wx with ⟨sr, wx'⟩
                      rw [hS] at hn
                      dsimp only at hn ⊢
                      have hwx' : wx'.wf = true := (wf_iff_parts wx').mpr hn.2.1
                      have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.socketpair .unix .stream { nonblock := true, cloexec := true }) (Net.outcomeOfPair sr) hn.1
                      cases sr with
                      | error e =>
                        dsimp only
                        refine ⟨fun hEi => ?_, fun hNe => ?_, ⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, hop⟩⟩
                        · injection hEi with he; subst he
                          exact ⟨⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, hop⟩, hBud.1 rfl⟩
                        · exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he)))
                      | ok pair =>
                        rcases pair with ⟨wakeR, wakeW⟩
                        dsimp only
                        exact ⟨(fun hBad => nomatch hBad), fun _ => Nat.le_of_eq (hBud.2 (fun hc => nomatch hc)),
                               ⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, by rw [hop]⟩⟩)
                    MAX_EINTR_RETRIES (w5, tr3) ⟨hWf5, hTbl5, hNd5, hDq3, hDa3, hBa3, hOp3⟩
                  have hR6' : (retryEintr
                    ((instrumentSysOps sys).net.socketpair .unix .stream { nonblock := true, cloexec := true })
                    MAX_EINTR_RETRIES).run (w5, tr3) = (r6, (w6, tr6)) := hR6
                  rw [hR6'] at hPair; clear hR6 hR6'
                  dsimp only at hPair
                  rcases hPair with ⟨⟨hWf6, hTbl6, hNd6, hDq6, hDa6, hBa6, hOp6⟩, _, hNoEi6⟩
                  cases r6 with
                  | error e =>
                    dsimp only at hRun
                    obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
                      closeLfdAndReturnErr_of_eq sys hRef w₀ w6 w₁ tr₀ tr6 tr₁ reqPort lfd (errnoToProxyError reqPort e) res
                        hWf6 hTbl6 hNd6 hDq6 hDa6 hBa6 hOp6
                        ⟨(errnoToProxyError_laws reqPort e).1, fun hB => errnoToProxyError_not_eintr reqPort e (hNoEi6 (by omega))⟩ hRun
                    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
                  | ok pair =>
                    rcases pair with ⟨wakeR, wakeW⟩
                    dsimp only [stateT_pure_run] at hRun hOp6
                    injection hRun with hr hwt; injection hwt with hwe hte
                    subst hr; subst hwe; subst hte
                    exact ⟨hWf6, hTbl6, hDq6, hDa6, hBa6, hNd6, hBpNe, hBpMatch, hOp6⟩
                · have hCondF : (ip == Net.INADDR_LOOPBACK && boundPort != 0 && (vcfg.config.listenPort == 0 || boundPort == vcfg.config.listenPort)) = false :=
                    Bool.eq_false_iff.mpr hCond
                  simp only [hCondF, Bool.false_eq_true, ↓reduceIte] at hRun
                  obtain ⟨h1, h2, h3, h4, h5, h6, rfl, h7, h8⟩ :=
                    closeLfdAndReturnErr_of_eq sys hRef w₀ w5 w₁ tr₀ tr3 tr₁ reqPort lfd
                      (Model.mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port")) res
                      hWf5 hTbl5 hNd5 hDq3 hDa3 hBa3 hOp3 hEinvalMsg hRun
                  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩


end LeanSwe.ConnectProxy.Proofs
