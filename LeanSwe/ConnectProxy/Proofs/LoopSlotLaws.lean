import LeanSwe.ConnectProxy.Proofs.LoopRelayLaws

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge


/-- Internal ConnectProxy proof helper `drainWakeSocket_laws`. -/
theorem drainWakeSocket_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (wakeR : Nat) :
    ∀ (fuel : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      ((drainWakeSocket (instrumentSysOps sys).net wakeR fuel).run (w, tr)).2.1.wf = true ∧
      ((drainWakeSocket (instrumentSysOps sys).net wakeR fuel).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, w, _, hWf => ⟨hWf, rfl⟩
  | fuel + 1, w, tr, hWf => by
    unfold drainWakeSocket
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    have hNet := hRef.2.1 w (.recvfrom wakeR 256 { dontwait := true }) ((wf_iff_parts w).mp hWf)
    dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
    rw [inst_net_recvfrom]
    rcases hRun : sys.net.recvfrom wakeR 256 { dontwait := true } w with ⟨r, w1⟩
    rw [hRun] at hNet
    dsimp only at hNet ⊢
    have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
    cases r with
    | ok bs =>
      by_cases h0 : (bs.size == 0) = true
      · simp only [h0, ↓reduceIte]; exact ⟨hWf1, rfl⟩
      · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte]
        exact drainWakeSocket_laws sys hRef wakeR fuel w1 _ hWf1
    | error e =>
      by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        exact drainWakeSocket_laws sys hRef wakeR fuel w1 tr hWf1
      · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hWf1, rfl⟩

private theorem drainClosingClient_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfd : Nat) :
    ∀ (fuel drained : Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      let (_, (w', tr')) := (drainClosingClient (instrumentSysOps sys).net cfd fuel drained).run (w, tr)
      w'.wf = true ∧
      tr'.pollOutcomes = tr.pollOutcomes ∧
      tr'.closedFds = tr.closedFds ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup)
  | 0, _, w, _, hWf => ⟨hWf, rfl, rfl, id⟩
  | fuel + 1, drained, w, tr, hWf => by
    unfold drainClosingClient
    dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
    have hNet := hRef.2.1 w (.recvfrom cfd 1024 { dontwait := true }) ((wf_iff_parts w).mp hWf)
    dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
    rw [inst_net_recvfrom]
    rcases hRun : sys.net.recvfrom cfd 1024 { dontwait := true } w with ⟨r, w1⟩
    rw [hRun] at hNet
    dsimp only at hNet ⊢
    have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
    have hNd1 := hNet.2.2.2
    cases r with
    | ok bs =>
      by_cases h0 : (bs.size == 0) = true
      · simp only [h0, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩
      · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte]
        by_cases hMax : drained + bs.size ≥ CLOSING_DRAIN_MAX
        · simp only [hMax, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩
        · simp only [hMax, ↓reduceIte]
          let k := Nat.min bs.size (1024 : UInt32).toNat
          let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
          let tr1 : SysAuditTrace Nat := { tr with recvBytes := tr.recvBytes ++ accepted }
          have hSub := drainClosingClient_laws sys hRef cfd fuel (drained + bs.size) w1 tr1 hWf1
          dsimp only [StateT.run, tr1, accepted, k] at hSub ⊢
          rcases hRec : drainClosingClient (instrumentSysOps sys).net cfd fuel (drained + bs.size)
            (w1, { tr with recvBytes := tr.recvBytes ++ if (Nat.min bs.size (1024 : UInt32).toNat) == bs.size then bs.data else (bs.extract 0 (Nat.min bs.size (1024 : UInt32).toNat)).data }) with ⟨r2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          rw [hRec] at hSub
          exact ⟨hSub.1, hSub.2.1, hSub.2.2.1, fun h0 => hSub.2.2.2 (hNd1 h0)⟩
    | error e =>
      by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        have hSub := drainClosingClient_laws sys hRef cfd fuel drained w1 tr hWf1
        dsimp only [StateT.run] at hSub ⊢
        rcases hRec : drainClosingClient (instrumentSysOps sys).net cfd fuel drained (w1, tr) with ⟨r2, wt2⟩
        rcases wt2 with ⟨w2, tr2⟩
        rw [hRec] at hSub
        exact ⟨hSub.1, hSub.2.1, hSub.2.2.1, fun h0 => hSub.2.2.2 (hNd1 h0)⟩
      · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]
        by_cases hAg : (e == Errno.EAGAIN) = true
        · simp only [hAg, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩
        · simp only [Bool.eq_false_iff.mpr hAg, Bool.false_eq_true, ↓reduceIte]; exact ⟨hWf1, rfl, rfl, hNd1⟩

private theorem closingSendStep_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfd : Nat) (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool) (cRev : Poll.PollEvents)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) := (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup) := by
  rcases hTop : (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev).run (w, tr) with ⟨res, w', tr'⟩
  have hRun : StateT.run (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev) (w, tr) = (res, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold closingSendStep at hRun
  split at hRun
  · split at hRun
    · dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl, id⟩
    · split at hRun
      · obtain ⟨flRes, w1a, tr1a, hFl, hRun⟩ := stateT_bind_app hRun
        have hL := flushBytesNonblock_instrumented_laws sys hRef cfd replyBytes MAX_CLOSING_STEPS replyOff w tr hWf
        have hPo := flushBytesNonblock_pollOutcomes_eq sys cfd replyBytes MAX_CLOSING_STEPS replyOff w tr
        have hFl' : (NetRelay.flushBytesNonblock (instrumentSysOps sys).net cfd replyBytes MAX_CLOSING_STEPS replyOff).run (w, tr) = (flRes, (w1a, tr1a)) := hFl
        rw [hFl'] at hL hPo; dsimp only at hL hPo
        cases flRes with
        | none =>
          dsimp only [stateT_pure_run] at hRun
          injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
          exact ⟨hL.1, hPo, hL.2.2.2.2.1⟩
        | some nextOff =>
          dsimp only at hRun
          split at hRun
          · obtain ⟨okS, w1b, tr1b, hSh, hRun⟩ := stateT_bind_eq hRun
            have hShL := shutdownWrClean_instrumented_laws sys hRef cfd 16 w1a tr1a hL.1
            have hSh' : (NetRelay.shutdownWrClean (instrumentSysOps sys).net cfd 16).run (w1a, tr1a) = (okS, (w1b, tr1b)) := hSh
            rw [hSh'] at hShL; dsimp only at hShL
            cases okS
            · simp only [Bool.false_eq_true, ↓reduceIte, stateT_pure_run] at hRun
              injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
              exact ⟨hShL.1, (congrArg SysAuditTrace.pollOutcomes hShL.2.1).trans hPo, fun h0 => hShL.2.2 (hL.2.2.2.2.1 h0)⟩
            · simp only [↓reduceIte, stateT_pure_run] at hRun
              injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
              exact ⟨hShL.1, (congrArg SysAuditTrace.pollOutcomes hShL.2.1).trans hPo, fun h0 => hShL.2.2 (hL.2.2.2.2.1 h0)⟩
          · dsimp only [stateT_pure_run] at hRun
            injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
            exact ⟨hL.1, hPo, hL.2.2.2.2.1⟩
      · dsimp only [stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
        exact ⟨hWf, rfl, id⟩
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl, id⟩

private theorem closingDrainStep_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfd : Nat) (shut1 : Bool) (drained : Nat) (cRev : Poll.PollEvents)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) := (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup → (w'.filesEnv.state.fds.map Prod.fst).Nodup) := by
  rcases hTop : (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev).run (w, tr) with ⟨res, w', tr'⟩
  have hRun : StateT.run (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev) (w, tr) = (res, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold closingDrainStep at hRun
  split at hRun
  · have hDr := drainClosingClient_laws sys hRef cfd MAX_CLOSING_STEPS drained w tr hWf
    have hRun' : (drainClosingClient (instrumentSysOps sys).net cfd MAX_CLOSING_STEPS drained).run (w, tr) = (res, (w', tr')) := hRun
    rw [hRun'] at hDr
    exact ⟨hDr.1, hDr.2.1, hDr.2.2.2⟩
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl, id⟩

/-- Relational laws for `stepClosingReply` (and `stepSlotSync` on `.closingReply`). -/
theorem healthy_stepClosingReply_laws {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (slot : ClientSlot Nat dnsJob)
    (cfd? : Option Nat)
    (replyBytes : ByteArray) (replyOff : Nat) (shutWr : Bool) (drained deadlineMs : Nat)
    (cRev : Poll.PollEvents) (nowMs : Nat)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (slot', (w', tr')) :=
      (stepClosingReply (instrumentSysOps sys) slot cfd? replyBytes replyOff shutWr drained deadlineMs cRev nowMs).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    (∀ d, cfd? = some d →
      (nowMs ≥ deadlineMs → slot'.phase = .done) ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup → slot'.phase = .done →
        d ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds d = none)) := by
  rcases hTop : (stepClosingReply (instrumentSysOps sys) slot cfd? replyBytes replyOff shutWr drained deadlineMs cRev nowMs).run (w, tr) with ⟨slot', w', tr'⟩
  have hRun : StateT.run (stepClosingReply (instrumentSysOps sys) slot cfd? replyBytes replyOff shutWr drained deadlineMs cRev nowMs) (w, tr) = (slot', (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold stepClosingReply at hRun
  cases cfd? with
  | none =>
    dsimp only [stateT_pure_run] at hRun
    injection hRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
    exact ⟨hWf, rfl, fun _ hc => nomatch hc⟩
  | some cfd =>
    have hCloseDone : ∀ wx trx,
        wx.wf = true →
        trx.pollOutcomes = tr.pollOutcomes →
        ((w.filesEnv.state.fds.map Prod.fst).Nodup → (wx.filesEnv.state.fds.map Prod.fst).Nodup) →
        StateT.run (do (instrumentSysOps sys).closeFd cfd; pure { slot with phase := SlotPhase.done }) (wx, trx) = (slot', (w', tr')) →
        w'.wf = true ∧
        tr'.pollOutcomes = tr.pollOutcomes ∧
        (∀ d, some cfd = some d →
          (nowMs ≥ deadlineMs → slot'.phase = SlotPhase.done) ∧
          ((w.filesEnv.state.fds.map Prod.fst).Nodup → slot'.phase = SlotPhase.done →
            d ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds d = none)) := by
      intro wx trx hWfx hPox hNdx hCRun
      obtain ⟨u, wc, trc, hCl, hCRun⟩ := stateT_bind_eq hCRun
      dsimp only [stateT_pure_run] at hCRun
      injection hCRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
      have hc := healthy_closeFd_instrumented_laws sys hRef wx trx cfd hWfx
      have hCl' : ((instrumentSysOps sys).closeFd cfd).run (wx, trx) = (u, (wc, trc)) := hCl
      rw [hCl'] at hc; dsimp only at hc
      refine ⟨hc.1, (by rw [hc.2.2.1] : trc.pollOutcomes = trx.pollOutcomes).trans hPox, fun d hd => ?_⟩
      injection hd with heq; subst heq
      refine ⟨fun _ => rfl, fun hNd0 _ => ⟨?_, (hc.2.2.2.2 (hNdx hNd0)).2⟩⟩
      rw [hc.2.2.1]; simp [Array.toList_push]
    dsimp only at hRun
    obtain ⟨sendRes, w1, tr1, hR1, hRun⟩ := stateT_bind_eq hRun
    have hS1 := closingSendStep_laws sys hRef cfd replyBytes replyOff shutWr cRev w tr hWf
    have hR1' : (closingSendStep (instrumentSysOps sys).net cfd replyBytes replyOff shutWr cRev).run (w, tr) = (sendRes, (w1, tr1)) := hR1
    rw [hR1'] at hS1; dsimp only at hS1
    cases sendRes with
    | none => exact hCloseDone w1 tr1 hS1.1 hS1.2.1 hS1.2.2 hRun
    | some pair =>
      rcases pair with ⟨off1, shut1⟩
      dsimp only at hRun
      obtain ⟨drainRes, w2, tr2, hR2, hRun⟩ := stateT_bind_eq hRun
      have hS2 := closingDrainStep_laws sys hRef cfd shut1 drained cRev w1 tr1 hS1.1
      have hR2' : (closingDrainStep (instrumentSysOps sys).net cfd shut1 drained cRev).run (w1, tr1) = (drainRes, (w2, tr2)) := hR2
      rw [hR2'] at hS2; dsimp only at hS2
      cases drainRes with
      | none =>
        exact hCloseDone w2 tr2 hS2.1 (hS2.2.1.trans hS1.2.1) (fun h0 => hS2.2.2 (hS1.2.2 h0)) hRun
      | some drained1 =>
        dsimp only at hRun
        by_cases hTo : nowMs ≥ deadlineMs
        · simp only [hTo, ↓reduceIte] at hRun
          exact hCloseDone w2 tr2 hS2.1 (hS2.2.1.trans hS1.2.1) (fun h0 => hS2.2.2 (hS1.2.2 h0)) hRun
        · simp only [hTo, ↓reduceIte, stateT_pure_run] at hRun
          injection hRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
          exact ⟨hS2.1, hS2.2.1.trans hS1.2.1, fun _ _ => ⟨fun hGe => absurd hGe hTo, fun _ hDone => nomatch hDone⟩⟩

private theorem enterClosingReply_wf_poll_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    {limits : ProxyLimits} {slot slot' : ClientSlot Nat dnsJob}
    {cfd code : Nat}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run (enterClosingReply (instrumentSysOps sys) limits slot cfd code) (w, tr) = (slot', (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  have hWfOut := (enterClosingReply_laws_of_eq sys hRef limits slot cfd code w tr hWf slot' w' tr' hRun).1
  unfold enterClosingReply at hRun
  dsimp only at hRun
  obtain ⟨now, w1, tr1, hM, hRun⟩ := stateT_bind_eq hRun
  obtain ⟨hWf1, hTr1⟩ := monoNowMs_of_eq sys hRef w w1 tr tr1 now hWf hM; clear hM
  obtain ⟨flRes, w2, tr2, hF, hRun⟩ := stateT_bind_eq hRun
  have hPo2 := flushBytesNonblock_pollOutcomes_eq sys cfd (if code == 403 then Relay.reply403Bytes else if code == 503 then Relay.reply503Bytes else Relay.reply502Bytes) MAX_CLOSING_STEPS 0 w1 tr1
  have hFl2 := flushBytesNonblock_of_eq sys hRef cfd _ MAX_CLOSING_STEPS 0 w1 w2 tr1 tr2 flRes hWf1 hF
  have hF' : (NetRelay.flushBytesNonblock (instrumentSysOps sys).net cfd (if code == 403 then Relay.reply403Bytes else if code == 503 then Relay.reply503Bytes else Relay.reply502Bytes) MAX_CLOSING_STEPS 0).run (w1, tr1) = (flRes, (w2, tr2)) := hF
  rw [hF'] at hPo2; dsimp only at hPo2; clear hF hF'
  have hPo20 : tr2.pollOutcomes = tr.pollOutcomes := hPo2.trans (congrArg _ hTr1)
  refine ⟨hWfOut, ?_⟩
  cases flRes with
  | none =>
    dsimp only at hRun
    obtain ⟨u, w3, tr3, hC, hRun⟩ := stateT_bind_eq hRun
    have hc := healthy_closeFd_instrumented_laws sys hRef w2 tr2 cfd hFl2.1
    have hC' : ((instrumentSysOps sys).closeFd cfd).run (w2, tr2) = (u, (w3, tr3)) := hC
    rw [hC'] at hc; dsimp only at hc
    dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with _ ht; subst ht
    exact (by rw [hc.2.2.1] : tr3.pollOutcomes = tr2.pollOutcomes).trans hPo20
  | some sentOff =>
    dsimp only at hRun
    by_cases hSent : sentOff ≥ (if code == 403 then Relay.reply403Bytes else if code == 503 then Relay.reply503Bytes else Relay.reply502Bytes).size
    · simp only [hSent, ↓reduceIte] at hRun
      obtain ⟨okS, w3, tr3, hS, hRun⟩ := stateT_bind_eq hRun
      obtain ⟨hWf3, hTr3⟩ := shutdownWrClean_of_eq sys hRef cfd 16 w2 w3 tr2 tr3 okS hFl2.1 hS; clear hS
      cases okS with
      | true =>
        simp only [↓reduceIte, stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with _ ht; subst ht
        rw [hTr3]
        exact hPo20
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hRun
        obtain ⟨u, w4, tr4, hC, hRun⟩ := stateT_bind_eq hRun
        have hc := healthy_closeFd_instrumented_laws sys hRef w3 tr3 cfd hWf3
        have hC' : ((instrumentSysOps sys).closeFd cfd).run (w3, tr3) = (u, (w4, tr4)) := hC
        rw [hC'] at hc; dsimp only at hc
        dsimp only [stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with _ ht; subst ht
        exact (by rw [hc.2.2.1] : tr4.pollOutcomes = tr3.pollOutcomes).trans
          ((congrArg SysAuditTrace.pollOutcomes hTr3).trans hPo20)
    · simp only [hSent, ↓reduceIte, stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with _ ht; subst ht
      exact hPo20

/-- Internal ConnectProxy proof helper `emitAndClosingReply_wf_poll_of_eq`. -/
theorem emitAndClosingReply_wf_poll_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    {limits : ProxyLimits} {slot1 : ClientSlot Nat dnsJob} {events1 : Array ConnectEvent}
    {slot' : ClientSlot Nat dnsJob} {evs' : Array ConnectEvent}
    {cfd code : Nat}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run
      (do
        let s2 ← enterClosingReply (instrumentSysOps sys) limits slot1 cfd code
        pure (s2, events1))
      (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  obtain ⟨s2, w1, tr1, hCr, hRun⟩ := stateT_bind_eq hRun
  dsimp only [stateT_pure_run] at hRun
  injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
  exact enterClosingReply_wf_poll_of_eq sys hRef hWf hCr

/-- Internal ConnectProxy proof helper `startNextConnectAux_pollOutcomes_of_eq`. -/
theorem startNextConnectAux_pollOutcomes_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits) (slot : ClientSlot Nat dnsJob) (events : Array ConnectEvent)
    (cfd : Nat) (host : String) (port : UInt16) (candidates : Array IpAddr) :
    ∀ (fuel candIdx : Nat) (lastErr? : Option Errno)
      {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat}
      {slot' : ClientSlot Nat dnsJob} {evs' : Array ConnectEvent},
      w.wf = true →
      StateT.run (startNextConnectAux (instrumentSysOps sys) limits slot events cfd host port candidates fuel candIdx lastErr?)
        (w, tr) = ((slot', evs'), (w', tr')) →
      tr'.pollOutcomes = tr.pollOutcomes
  | 0, _, lastErr?, _, _, _, _, _, _, hWf, hRun => by
    unfold startNextConnectAux at hRun
    exact (emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun).2
  | fuel + 1, candIdx, lastErr?, w, w', tr, tr', slot', evs', hWf, hRun => by
    unfold startNextConnectAux at hRun
    by_cases hLt : candIdx < candidates.size
    · simp only [hLt, ↓reduceDIte] at hRun
      let sa := ipAddrToDialSockAddr (candidates[candIdx]'hLt) port
      obtain ⟨rSock, w1, tr1, hSR, hRun⟩ := stateT_bind_app hRun
      have hSock := retryEintr_preserves
        (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.wf = true ∧ wt.2.pollOutcomes = tr.pollOutcomes)
        (fun _ _ => True)
        ((instrumentSysOps sys).net.socket sa.domain .stream { nonblock := true, cloexec := true } 0)
        (fun (wx, trx) ⟨hwx, hpo⟩ => by
          have hn := hRef.2.1 wx (.socket sa.domain .stream { nonblock := true, cloexec := true } 0) ((wf_iff_parts wx).mp hwx)
          dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
          dsimp only [StateT.run]; rw [inst_net_socket]
          rcases hS : sys.net.socket sa.domain .stream { nonblock := true, cloexec := true } 0 wx with ⟨sr, wx'⟩
          rw [hS] at hn; cases sr <;> exact ⟨⟨(wf_iff_parts wx').mpr hn.2.1, hpo⟩, Or.inr trivial⟩)
        MAX_EINTR_RETRIES (w, tr) ⟨hWf, rfl⟩
      dsimp only [sa] at hSock
      have hSR' : (retryEintr ((instrumentSysOps sys).net.socket
        (ipAddrToDialSockAddr (candidates[candIdx]'hLt) port).domain .stream { nonblock := true, cloexec := true } 0)
        MAX_EINTR_RETRIES).run (w, tr) = (rSock, (w1, tr1)) := hSR
      rw [hSR'] at hSock; dsimp only at hSock
      cases rSock with
      | error e =>
        exact (startNextConnectAux_pollOutcomes_of_eq sys hRef limits slot events cfd host port candidates fuel (candIdx + 1) (some e) hSock.1.1 hRun).trans hSock.1.2
      | ok ufd =>
        dsimp only at hRun
        obtain ⟨rc, w2, tr2, hCR, hRun⟩ := stateT_bind_eq hRun
        have hn := hRef.2.1 w1 (.connect ufd sa) ((wf_iff_parts w1).mp hSock.1.1)
        dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
        have hCR' : (instrumentSysOps sys).net.connect ufd sa (w1, tr1) = (rc, (w2, tr2)) := hCR
        rw [inst_net_connect] at hCR'
        rcases hSysC : sys.net.connect ufd sa w1 with ⟨rcSys, w2Sys⟩
        rw [hSysC] at hn hCR'; dsimp only at hn hCR'
        injection hCR' with hrc hwt; injection hwt with hw2 ht2
        subst hrc; subst hw2; subst ht2
        have hWf2 : w2Sys.wf = true := (wf_iff_parts w2Sys).mpr hn.2.1
        let trDial : SysAuditTrace Nat := { tr1 with dialedAddrs := tr1.dialedAddrs.push sa }
        cases rcSys with
        | ok _ =>
          dsimp only [stateT_pure_run] at hRun
          injection hRun with _ hwt; injection hwt with _ ht; subst ht
          exact hSock.1.2
        | error e =>
          dsimp only at hRun
          split at hRun
          · obtain ⟨now, w3, tr3, hM, hRun⟩ := stateT_bind_eq hRun
            obtain ⟨_, hTr3⟩ := monoNowMs_of_eq sys hRef w2Sys w3 trDial tr3 now hWf2 hM
            dsimp only [stateT_pure_run] at hRun
            injection hRun with _ hwt; injection hwt with _ ht; subst ht
            rw [hTr3]; exact hSock.1.2
          · obtain ⟨u, w3, tr3, hC, hRun⟩ := stateT_bind_eq hRun
            have hc := healthy_closeFd_instrumented_laws sys hRef w2Sys trDial ufd hWf2
            have hC' : ((instrumentSysOps sys).closeFd ufd).run (w2Sys, trDial) = (u, (w3, tr3)) := hC
            rw [hC'] at hc; dsimp only at hc
            exact (startNextConnectAux_pollOutcomes_of_eq sys hRef limits slot events cfd host port candidates fuel (candIdx + 1) (some e) hc.1 hRun).trans
              ((by rw [hc.2.2.1] : tr3.pollOutcomes = tr1.pollOutcomes).trans hSock.1.2)
    · simp only [hLt, ↓reduceDIte] at hRun
      exact startNextConnectAux_pollOutcomes_of_eq sys hRef limits slot events cfd host port candidates 0 candIdx lastErr? hWf hRun

/-- Relational laws for `stepConnecting` (and `stepSlotSync` on `.connecting`). -/
theorem healthy_stepConnecting_laws {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat dnsJob)
    (events : Array ConnectEvent)
    (cfd ufd : Nat) (host : String) (port : UInt16)
    (candidates : Array IpAddr) (candIdx : Nat) (lastErr? : Option Errno) (dlMs : Nat)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat)
    (w₀ : HealthySysWorld) (tr₀ : SysAuditTrace Nat)
    (hWf₀ : w₀.wf = true) :
    let ((slot', evs'), (wC, trC)) :=
      (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port candidates candIdx lastErr? dlMs cRev uRev nowMs).run (w₀, tr₀)
    wC.wf = true ∧
    trC.pollOutcomes = tr₀.pollOutcomes ∧
    trC.dnsQueries = tr₀.dnsQueries ∧
    ((∀ ip ∈ candidates.toList, Model.allowsIp cfg.ipPolicy ip = true) →
      ∀ sa ∈ trC.dialedAddrs.toList,
        sa ∈ tr₀.dialedAddrs.toList ∨
        ∃ ip ∈ candidates.toList,
          sa = ipAddrToDialSockAddr ip port ∧
          Model.allowsIp cfg.ipPolicy ip = true ∧
          Model.isBannedByPrefixes cfg.ipPolicy.extraBans (effectiveDialIp ip) = false) ∧
    (∀ st, slot'.phase = .relay st →
      (slot.phase ≠ .relay st) →
      st.pendingPrefix = slot.pipelined ∧ st.pendingOff = 0 ∧
      st.u2c.toList = Relay.reply200Bytes.data.toList ∧
      evs'.size = events.size + (if slot.eventEmitted then 0 else 1)) ∧
    ((cRev.pollerr || cRev.pollhup || cRev.pollnval) = true →
      (w₀.filesEnv.state.fds.map Prod.fst).Nodup →
      ufd ∈ trC.closedFds.toList ∧ cfd ∈ trC.closedFds.toList ∧
      Files.assocGet wC.filesEnv.state.fds ufd = none ∧
      Files.assocGet wC.filesEnv.state.fds cfd = none) ∧
    ((cRev.pollerr || cRev.pollhup || cRev.pollnval) = false ∧
        (uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval) = false ∧
        nowMs ≥ dlMs →
      ufd ∈ trC.closedFds.toList) := by
  rcases hTop : (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port candidates candIdx lastErr? dlMs cRev uRev nowMs).run (w₀, tr₀) with ⟨⟨slot', evs'⟩, wC, trC⟩
  have hRun : StateT.run (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port candidates candIdx lastErr? dlMs cRev uRev nowMs) (w₀, tr₀) = ((slot', evs'), (wC, trC)) := hTop
  clear hTop
  dsimp only
  unfold stepConnecting at hRun
  by_cases hCErr : (cRev.pollerr || cRev.pollhup || cRev.pollnval) = true
  · simp only [hCErr, ↓reduceIte] at hRun
    obtain ⟨u1, w1, tr1, hC1, hRun⟩ := stateT_bind_app hRun
    obtain ⟨u2, w2, tr2, hC2, hRun⟩ := stateT_bind_eq hRun
    dsimp only [stateT_pure_run] at hRun
    injection hRun with hp hwt; injection hp with hs he; injection hwt with hw ht
    subst hs; subst he; subst hw; subst ht
    have hc1 := healthy_closeFd_instrumented_laws sys hRef w₀ tr₀ ufd hWf₀
    have hC1' : ((instrumentSysOps sys).closeFd ufd).run (w₀, tr₀) = (u1, (w1, tr1)) := hC1
    rw [hC1'] at hc1; dsimp only at hc1
    have hc2 := healthy_closeFd_instrumented_laws sys hRef w1 tr1 cfd hc1.1
    have hC2' : ((instrumentSysOps sys).closeFd cfd).run (w1, tr1) = (u2, (w2, tr2)) := hC2
    rw [hC2'] at hc2; dsimp only at hc2
    refine ⟨hc2.1,
      by rw [hc2.2.2.1, hc1.2.2.1],
      by rw [hc2.2.2.1, hc1.2.2.1],
      fun _ sa hm => Or.inl (by rw [hc2.2.2.1, hc1.2.2.1] at hm; exact hm),
      ?_, ?_,
      fun ⟨hCF, _⟩ => by rw [hCErr] at hCF; cases hCF⟩
    · intro _ hRel _; cases hRel
    · intro _ hNd₀
      obtain ⟨hNd1, hNoneU⟩ := hc1.2.2.2.2 hNd₀
      obtain ⟨_, hNoneC⟩ := hc2.2.2.2.2 hNd1
      refine ⟨?_, ?_, hc2.2.2.2.1 ufd hNoneU, hNoneC⟩
      · rw [hc2.2.2.1, hc1.2.2.1]; simp [Array.toList_push]
      · rw [hc2.2.2.1]; simp [Array.toList_push]
  · have hCErrF : (cRev.pollerr || cRev.pollhup || cRev.pollnval) = false := Bool.eq_false_iff.mpr hCErr
    simp only [hCErrF, Bool.false_eq_true, ↓reduceIte] at hRun
    by_cases hUEv : (uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval) = true
    · simp only [hUEv, ↓reduceIte] at hRun
      obtain ⟨gRes, w1, tr1, hGR, hRun⟩ := stateT_bind_app hRun
      have hGs := retryEintr_preserves
        (fun (wt : HealthySysWorld × SysAuditTrace Nat) => wt.1.wf = true ∧ wt.2 = tr₀)
        (fun _ _ => True)
        ((instrumentSysOps sys).net.getsockopt ufd .error)
        (fun (wx, trx) ⟨hwx, htrx⟩ => by
          have hn := hRef.2.1 wx (.getsockopt ufd .error) ((wf_iff_parts wx).mp hwx)
          dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
          dsimp only [StateT.run]; rw [inst_net_getsockopt]
          rcases hG : sys.net.getsockopt ufd .error wx with ⟨gr, wx'⟩
          rw [hG] at hn; exact ⟨⟨(wf_iff_parts wx').mpr hn.2.1, htrx⟩, Or.inr trivial⟩)
        MAX_EINTR_RETRIES (w₀, tr₀) ⟨hWf₀, rfl⟩
      have hGR' : (retryEintr ((instrumentSysOps sys).net.getsockopt ufd .error) MAX_EINTR_RETRIES).run (w₀, tr₀) = (gRes, (w1, tr1)) := hGR
      rw [hGR'] at hGs; dsimp only at hGs
      rcases hGs.1 with ⟨hWf1, hTr1Eq⟩
      rw [hTr1Eq] at hRun
      let soErr : Errno := match gRes with | .ok code => code | .error e => e
      have hSoNorm : StateT.run
          (if soErr == 0 && uRev.pollout && !uRev.pollerr && !uRev.pollnval then
            pure (enterRelay slot events cfd ufd host port)
          else do
            let recErr := if soErr != 0 then soErr else Errno.ECONNREFUSED
            (instrumentSysOps sys).closeFd ufd
            startNextConnect (instrumentSysOps sys) cfg.limits slot events cfd host port candidates candIdx (some recErr))
          (w1, tr₀) = ((slot', evs'), (wC, trC)) := by
        cases gRes <;> simpa [soErr, StateT.run, bind, StateT.bind, pure, StateT.pure] using hRun
      by_cases hOkConn : (soErr == 0 && uRev.pollout && !uRev.pollerr && !uRev.pollnval) = true
      · simp only [hOkConn, ↓reduceIte, stateT_pure_run] at hSoNorm
        injection hSoNorm with hp hwt; injection hp with hs he; injection hwt with hw ht
        subst hs; subst he; subst hw; subst ht
        refine ⟨hWf1, rfl, rfl, fun _ sa hm => Or.inl hm, fun st hRel _ => ?_,
          fun hBad => absurd hBad hCErr, fun ⟨_, hUF, _⟩ => by rw [hUEv] at hUF; cases hUF⟩
        dsimp only [enterRelay] at hRel
        injection hRel with hStEq
        subst hStEq
        exact ⟨emitSlotEvent_fst_pipelined slot events _, rfl, reply200_init_u2c_toList, emitSlotEvent_snd_size slot events _⟩
      · simp only [Bool.eq_false_iff.mpr hOkConn, Bool.false_eq_true, ↓reduceIte] at hSoNorm
        obtain ⟨u, w2, tr2, hC, hSnc⟩ := stateT_bind_app hSoNorm
        have hc := healthy_closeFd_instrumented_laws sys hRef w1 tr₀ ufd hWf1
        have hC' : ((instrumentSysOps sys).closeFd ufd).run (w1, tr₀) = (u, (w2, tr2)) := hC
        rw [hC'] at hc; dsimp only [startNextConnect] at hc hSnc
        have hPo := startNextConnectAux_pollOutcomes_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx _ hc.1 hSnc
        have hSub := startNextConnectAux_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx _ w2 wC tr2 trC slot' evs' hc.1 hSnc
        refine ⟨hSub.1,
          hPo.trans (by rw [hc.2.2.1]),
          hSub.2.1.trans (by rw [hc.2.2.1]),
          fun hCands sa hm => ?_,
          fun st hRel _ => hSub.2.2.2.2.2.2.1 st hRel,
          fun hBad => absurd hBad hCErr,
          fun ⟨_, hUF, _⟩ => by rw [hUEv] at hUF; cases hUF⟩
        rcases hSub.2.2.2.2.1 sa hm with hIn2 | ⟨ip, hMem, rfl⟩
        · rw [hc.2.2.1] at hIn2; exact Or.inl hIn2
        · have hAl := hCands ip hMem
          exact Or.inr ⟨ip, hMem, rfl, hAl, (dialSockAddr_never_banned cfg.ipPolicy ip hAl).1⟩
    · have hUEvF : (uRev.pollout || uRev.pollerr || uRev.pollhup || uRev.pollnval) = false := Bool.eq_false_iff.mpr hUEv
      simp only [hUEvF, Bool.false_eq_true, ↓reduceIte] at hRun
      by_cases hTo : nowMs ≥ dlMs
      · simp only [hTo, ↓reduceIte] at hRun
        obtain ⟨u, w1, tr1, hC, hSnc⟩ := stateT_bind_app hRun
        have hc := healthy_closeFd_instrumented_laws sys hRef w₀ tr₀ ufd hWf₀
        have hC' : ((instrumentSysOps sys).closeFd ufd).run (w₀, tr₀) = (u, (w1, tr1)) := hC
        rw [hC'] at hc; dsimp only [startNextConnect] at hc hSnc
        have hPo := startNextConnectAux_pollOutcomes_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx (some Errno.ETIMEDOUT) hc.1 hSnc
        have hSub := startNextConnectAux_of_eq sys hRef cfg.limits slot events cfd host port candidates (candidates.size - candIdx) candIdx (some Errno.ETIMEDOUT) w1 wC tr1 trC slot' evs' hc.1 hSnc
        refine ⟨hSub.1,
          hPo.trans (by rw [hc.2.2.1]),
          hSub.2.1.trans (by rw [hc.2.2.1]),
          fun hCands sa hm => ?_,
          fun st hRel _ => hSub.2.2.2.2.2.2.1 st hRel,
          fun hBad => absurd hBad hCErr,
          fun _ => hSub.2.2.2.1 ufd (by rw [hc.2.2.1]; simp [Array.toList_push])⟩
        rcases hSub.2.2.2.2.1 sa hm with hIn1 | ⟨ip, hMem, rfl⟩
        · rw [hc.2.2.1] at hIn1; exact Or.inl hIn1
        · have hAl := hCands ip hMem
          exact Or.inr ⟨ip, hMem, rfl, hAl, (dialSockAddr_never_banned cfg.ipPolicy ip hAl).1⟩
      · simp only [hTo, ↓reduceIte, stateT_pure_run] at hRun
        injection hRun with hp hwt; injection hp with hs he; injection hwt with hw ht
        subst hs; subst he; subst hw; subst ht
        exact ⟨hWf₀, rfl, rfl, fun _ sa hm => Or.inl hm,
          fun st hRel hNe => absurd hRel hNe,
          fun hBad => absurd hBad hCErr,
          fun ⟨_, _, hGe⟩ => absurd hGe hTo⟩


end LeanSwe.ConnectProxy.Proofs
