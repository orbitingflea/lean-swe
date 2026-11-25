import LeanSwe.ConnectProxy.Proofs.LoopSlotLaws

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge


private theorem handleResolveDecision_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) {slot slot' : ClientSlot Nat Unit} {events evs' : Array ConnectEvent}
    {cfd : Nat} {host : String} {port : UInt16} {ips : Array IpAddr}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run (handleResolveDecision (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy) slot events cfd host port ips) (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  unfold handleResolveDecision at hRun
  cases hDec : Model.decideResolvedIps cfg.ipPolicy host port ips with
  | deny r =>
    rw [hDec] at hRun; dsimp only at hRun
    exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
  | dial primary fallbacks =>
    rw [hDec] at hRun; dsimp only [startNextConnect] at hRun
    have hPo := startNextConnectAux_pollOutcomes_of_eq sys hRef cfg.limits slot events cfd host port (#[primary] ++ fallbacks) ((#[primary] ++ fallbacks).size - 0) 0 none hWf hRun
    have hSub := startNextConnectAux_of_eq sys hRef cfg.limits slot events cfd host port (#[primary] ++ fallbacks) ((#[primary] ++ fallbacks).size - 0) 0 none w w' tr tr' slot' evs' hWf hRun
    exact ⟨hSub.1, hPo⟩

private theorem handleCompleteHead_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) {slot slot' : ClientSlot Nat Unit} {events evs' : Array ConnectEvent}
    {cfd : Nat} {headBytes pipelined : ByteArray}
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat} (hWf : w.wf = true)
    (hRun : StateT.run
      (handleCompleteHead (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events cfd headBytes pipelined)
      (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  unfold handleCompleteHead at hRun
  dsimp only at hRun
  cases hDec : Model.decideConnectHead cfg headBytes with
  | deny h? p? reason =>
    rw [hDec] at hRun; dsimp only at hRun
    exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
  | needResolve host port litIp? =>
    rw [hDec] at hRun; dsimp only at hRun
    cases litIp? with
    | some litIp =>
      exact handleResolveDecision_wf_poll_of_eq sys hRef cfg hWf hRun
    | none =>
      dsimp only [startDnsSync] at hRun
      obtain ⟨dnsRes, w1, tr1, hD, hRun⟩ := stateT_bind_eq hRun
      have hDns := hRef.2.2.2.1 w { host := host, hints := { family := .any, sockType := .stream } } ((wf_iff_parts w).mp hWf)
      dsimp only [Dns.execDnsReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hDns
      have hD' : (instrumentSysOps sys).dns.getaddrinfo host { family := .any, sockType := .stream } (w, tr) = (dnsRes, (w1, tr1)) := hD
      rw [inst_dns_getaddrinfo] at hD'
      rcases hSysD : sys.dns.getaddrinfo host { family := .any, sockType := .stream } w with ⟨dSys, w1Sys⟩
      rw [hSysD] at hDns hD'; dsimp only at hDns hD'
      injection hD' with hd hwt; injection hwt with hw1 ht1
      subst hd; subst hw1; subst ht1
      have hWf1 : w1Sys.wf = true := (wf_iff_parts w1Sys).mpr hDns.2.1
      cases dSys with
      | error _ =>
        dsimp only at hRun
        have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
        exact ⟨hSub.1, hSub.2⟩
      | ok addrs =>
        dsimp only at hRun
        have hSub := handleResolveDecision_wf_poll_of_eq sys hRef cfg hWf1 hRun
        exact ⟨hSub.1, hSub.2⟩

private theorem stepHandshakeReadAux_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (cfd deadlineMs : Nat) :
    ∀ (fuel : Nat) (headBuf : ByteArray)
      {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat}
      {slot' : ClientSlot Nat Unit} {evs' : Array ConnectEvent},
      w.wf = true →
      StateT.run
        (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
          (Model.decideResolvedIps cfg.ipPolicy)
          (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
          slot events cfd deadlineMs fuel headBuf)
        (w, tr) = ((slot', evs'), (w', tr')) →
      w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes
  | 0, _, _, _, _, _, _, _, hWf, hRun => by
    unfold stepHandshakeReadAux at hRun
    dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl⟩
  | fuel + 1, headBuf, w, w', tr, tr', slot', evs', hWf, hRun => by
    unfold stepHandshakeReadAux at hRun
    by_cases hMax : headBuf.size ≥ cfg.limits.maxHeaderBytes
    · simp only [hMax, ↓reduceIte] at hRun
      exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
    · simp only [hMax, ↓reduceIte] at hRun
      let want := UInt32.ofNat (Nat.min (cfg.limits.maxHeaderBytes - headBuf.size) HANDSHAKE_CHUNK_MAX)
      obtain ⟨recvRes, w1, tr1, hR, hRun⟩ := stateT_bind_app hRun
      have hR' : (instrumentSysOps sys).net.recvfrom cfd want { dontwait := true } (w, tr) = (recvRes, (w1, tr1)) := hR
      clear hR
      rw [inst_net_recvfrom sys cfd want { dontwait := true } w tr] at hR'
      have hNet := hRef.2.1 w (.recvfrom cfd want { dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hNet
      rcases hRNet : sys.net.recvfrom cfd want { dontwait := true } w with ⟨rSys, w1Sys⟩
      rw [hRNet] at hNet hR'; dsimp only at hNet hR'
      injection hR' with hrr hwt; injection hwt with hw1 ht1
      subst hrr; subst hw1; subst ht1
      have hWf1 : w1Sys.wf = true := (wf_iff_parts w1Sys).mpr hNet.2.1
      cases rSys with
      | error e =>
        dsimp only at hRun
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte] at hRun
          exact stepHandshakeReadAux_wf_poll_of_eq sys hRef cfg slot events cfd deadlineMs fuel headBuf hWf1 hRun
        · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte] at hRun
          by_cases hAg : (e == Errno.EAGAIN) = true
          · simp only [hAg, ↓reduceIte, stateT_pure_run] at hRun
            injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
            exact ⟨hWf1, rfl⟩
          · simp only [Bool.eq_false_iff.mpr hAg, Bool.false_eq_true, ↓reduceIte] at hRun
            have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
            exact ⟨hSub.1, hSub.2⟩
      | ok chunk =>
        dsimp only at hRun
        by_cases h0 : (chunk.size == 0) = true
        · simp only [h0, ↓reduceIte] at hRun
          have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
          exact ⟨hSub.1, hSub.2⟩
        · simp only [Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte] at hRun
          let takeN := Nat.min chunk.size want.toNat
          let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
          let nextBuf := if headBuf.size == 0 then part else headBuf ++ part
          cases hScan : findCrlfCrlf nextBuf (headBuf.size - 3) with
          | some pos =>
            rw [hScan] at hRun; dsimp only at hRun
            have hSub := handleCompleteHead_wf_poll_of_eq sys hRef cfg hWf1 hRun
            exact ⟨hSub.1, hSub.2⟩
          | none =>
            rw [hScan] at hRun; dsimp only at hRun
            by_cases hNextGe : nextBuf.size ≥ cfg.limits.maxHeaderBytes
            · have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              have hSub := emitAndClosingReply_wf_poll_of_eq sys hRef hWf1 hRun
              exact ⟨hSub.1, hSub.2⟩
            · have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              have hSub := stepHandshakeReadAux_wf_poll_of_eq sys hRef cfg slot events cfd deadlineMs fuel _ hWf1 hRun
              exact ⟨hSub.1, hSub.2⟩

private theorem stepHandshake_wf_poll_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig) (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (cfd : Nat) (headBuf : ByteArray) (dl nowMs : Nat) (cRev : Poll.PollEvents)
    {w w' : HealthySysWorld} {tr tr' : SysAuditTrace Nat}
    {slot' : ClientSlot Nat Unit} {evs' : Array ConnectEvent}
    (hWf : w.wf = true)
    (hRun : StateT.run
      (stepHandshake (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events cfd headBuf dl cRev nowMs)
      (w, tr) = ((slot', evs'), (w', tr'))) :
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  unfold stepHandshake at hRun
  dsimp only at hRun
  by_cases hEv : (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = true
  · simp only [hEv, ↓reduceIte] at hRun
    obtain ⟨⟨s1, e1⟩, w1, tr1, hFirst, hRun⟩ := stateT_bind_app hRun
    dsimp only at hRun
    have hRd := stepHandshakeReadAux_wf_poll_of_eq sys hRef cfg slot events cfd dl MAX_HANDSHAKE_STEPS headBuf hWf hFirst
    cases hPh : s1.phase with
    | handshake cfd1 _ dl1 =>
      rw [hPh] at hRun; dsimp only at hRun
      by_cases hGe : nowMs ≥ dl1
      · simp only [hGe, ↓reduceIte] at hRun
        have hCr := emitAndClosingReply_wf_poll_of_eq sys hRef hRd.1 hRun
        exact ⟨hCr.1, hCr.2.trans hRd.2⟩
      · simp only [hGe, ↓reduceIte, stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
        exact hRd
    | dns _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | connecting _ _ _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | relay _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | closingReply _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
    | done =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact hRd
  · simp only [Bool.eq_false_iff.mpr hEv, Bool.false_eq_true, ↓reduceIte] at hRun
    obtain ⟨⟨s1, e1⟩, w1, tr1, hFirst, hRun⟩ := stateT_bind_app hRun
    dsimp only [stateT_pure_run] at hFirst
    injection hFirst with hp hwt; injection hp with hs he; injection hwt with hw ht
    subst hs; subst he; subst hw; subst ht
    dsimp only at hRun
    cases hPh : slot.phase with
    | handshake cfd1 _ dl1 =>
      rw [hPh] at hRun; dsimp only at hRun
      by_cases hGe : nowMs ≥ dl1
      · simp only [hGe, ↓reduceIte] at hRun
        exact emitAndClosingReply_wf_poll_of_eq sys hRef hWf hRun
      · simp only [hGe, ↓reduceIte, stateT_pure_run] at hRun
        injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
        exact ⟨hWf, rfl⟩
    | dns _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | connecting _ _ _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | relay _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | closingReply _ _ _ _ _ _ =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩
    | done =>
      rw [hPh] at hRun; dsimp only [stateT_pure_run] at hRun
      injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
      exact ⟨hWf, rfl⟩

private theorem stepSlotTick_wf_poll
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) :=
      (stepSlotM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        (fun () => pure none) (fun () => pure ()) slot events cRev uRev nowMs).run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  suffices hPres : PreservesWfPoll tr
      (stepSlotM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
        (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        (fun () => pure none) (fun () => pure ()) slot events cRev uRev nowMs) from
    hPres w tr hWf rfl
  unfold stepSlotM
  cases slot.phase with
  | handshake cfd headBuf dl =>
    intro wx trx hwx hpox
    rcases hR : (stepHandshake (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      slot events cfd headBuf dl cRev nowMs).run (wx, trx) with ⟨⟨s', e'⟩, w1, tr1⟩
    have hHs := stepHandshake_wf_poll_of_eq sys hRef cfg slot events cfd headBuf dl nowMs cRev hwx hR
    exact ⟨hHs.1, hHs.2.trans hpox⟩
  | dns cfd host port job =>
    dsimp only; split
    · exact pres_bind (pres_pure ()) (fun _ => pres_bind (pres_closeFd sys hRef tr cfd) (fun _ => pres_pure _))
    · intro wx trx hwx hpox
      exact ⟨hwx, hpox⟩
  | connecting cfd ufd host port cands idx lastErr? dl =>
    intro wx trx hwx hpox
    have hConn := healthy_stepConnecting_laws sys hRef cfg slot events cfd ufd host port cands idx lastErr? dl cRev uRev nowMs wx trx hwx
    rcases hR : (stepConnecting (instrumentSysOps sys) cfg.limits slot events cfd ufd host port cands idx lastErr? dl cRev uRev nowMs).run (wx, trx) with ⟨_, w1, tr1⟩
    rw [hR] at hConn
    exact ⟨hConn.1, hConn.2.1.trans hpox⟩
  | relay st =>
    dsimp only
    refine pres_bind ?_ (fun _ => by split <;> exact pres_pure _)
    intro wx trx hwx hpox
    have hRel := healthy_stepBidirectionalRelay_wf sys hRef st cRev uRev wx trx hwx
    rcases hR : (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd st cRev uRev).run (wx, trx) with ⟨_, w1, tr1⟩
    rw [hR] at hRel
    exact ⟨hRel.1, hRel.2.trans hpox⟩
  | closingReply cfd? rb roff sw dr dl =>
    dsimp only
    refine pres_bind ?_ (fun _ => pres_pure _)
    intro wx trx hwx hpox
    have hCl := healthy_stepClosingReply_laws sys hRef slot cfd? rb roff sw dr dl cRev nowMs wx trx hwx
    rcases hR : (stepClosingReply (instrumentSysOps sys) slot cfd? rb roff sw dr dl cRev nowMs).run (wx, trx) with ⟨_, w1, tr1⟩
    rw [hR] at hCl
    exact ⟨hCl.1, hCl.2.1.trans hpox⟩
  | done => exact pres_pure _

/-- Internal ConnectProxy proof helper `stepSlotsListM_laws`. -/
theorem stepSlotsListM_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (indices : Array (Option Nat × Option Nat))
    (revents : Array Poll.PollEvents)
    (nowMs : Nat) :
    ∀ (idx : Nat) (slots : List (ClientSlot Nat Unit))
      (accSlots : Array (ClientSlot Nat Unit)) (accEvents : Array ConnectEvent)
      (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      (∀ s ∈ accSlots.toList, s.isFinished = false) →
      let ((outSlots, _), (w', tr')) :=
        (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
          (Model.decideResolvedIps cfg.ipPolicy)
          (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
          (fun () => pure none) (fun () => pure ()) indices revents nowMs
          idx slots accSlots accEvents).run (w, tr)
      w'.wf = true ∧
      tr'.pollOutcomes = tr.pollOutcomes ∧
      outSlots.size ≤ accSlots.size + slots.length ∧
      (∀ s ∈ outSlots.toList, s.isFinished = false)
  | _, [], accSlots, _, w, _, hWf, hFin =>
    ⟨hWf, rfl, by simp, hFin⟩
  | idx, slot :: rest, accSlots, accEvents, w, tr, hWf, hFin => by
    rcases hTop : (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) indices revents nowMs
      idx (slot :: rest) accSlots accEvents).run (w, tr) with ⟨⟨outSlots, outEvs⟩, w2, tr2⟩
    have hRun : StateT.run (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) indices revents nowMs
      idx (slot :: rest) accSlots accEvents) (w, tr) = ((outSlots, outEvs), (w2, tr2)) := hTop
    clear hTop
    dsimp only
    unfold stepSlotsListM at hRun
    rcases hIdx : indices[idx]?.getD (none, none) with ⟨cIdx?, uIdx?⟩
    rw [hIdx] at hRun
    dsimp only at hRun
    obtain ⟨⟨slot', evs'⟩, w1, tr1, hSRun, hRun⟩ := stateT_bind_eq hRun
    let cRev := match cIdx? with | some ci => revents[ci]?.getD {} | none => {}
    let uRev := match uIdx? with | some ui => revents[ui]?.getD {} | none => {}
    have hStep := stepSlotTick_wf_poll sys hRef cfg slot accEvents cRev uRev nowMs w tr hWf
    have hSRun' : (stepSlotM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) slot accEvents cRev uRev nowMs).run (w, tr) = ((slot', evs'), (w1, tr1)) := hSRun
    rw [hSRun'] at hStep; dsimp only at hStep
    let accSlots' := if !slot'.isFinished then accSlots.push slot' else accSlots
    have hAccFin : ∀ s ∈ accSlots'.toList, s.isFinished = false := by
      dsimp only [accSlots']
      cases hF : slot'.isFinished
      · simp only [Bool.not_false, ↓reduceIte, Array.toList_push, List.mem_append, List.mem_singleton]
        rintro s (hOld | rfl)
        · exact hFin s hOld
        · exact hF
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hFin
    have hAccSz : accSlots'.size ≤ accSlots.size + 1 := by
      dsimp only [accSlots']
      split <;> simp [Array.size_push] <;> omega
    have hSub := stepSlotsListM_laws sys hRef cfg indices revents nowMs (idx + 1) rest accSlots' evs' w1 tr1 hStep.1 hAccFin
    have hRun' : (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
      (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      (fun () => pure none) (fun () => pure ()) indices revents nowMs
      (idx + 1) rest accSlots' evs').run (w1, tr1) = ((outSlots, outEvs), (w2, tr2)) := hRun
    rw [hRun'] at hSub; dsimp only at hSub
    have hLen : (slot :: rest).length = rest.length + 1 := rfl
    have hOutSz := hSub.2.2.1
    exact ⟨hSub.1, hSub.2.1.trans hStep.2, by omega, hSub.2.2.2⟩


end LeanSwe.ConnectProxy.Proofs
