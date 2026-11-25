import LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

/-- Internal SysBridge helper lemma `emitAndClosingReply_of_eq`. -/
theorem emitAndClosingReply_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits) (slot : ClientSlot Nat dnsJob)
    (events : Array ConnectEvent) (ev : ConnectEvent) (cfd code : Nat)
    (w w' : HealthySysWorld) (tr tr' : SysAuditTrace Nat)
    (slot' : ClientSlot Nat dnsJob) (ev' : Array ConnectEvent)
    (hWf : w.wf = true)
    (hRun : StateT.run
      (do
        let s2 ← enterClosingReply (instrumentSysOps sys) limits (emitSlotEvent slot events ev).1 cfd code
        pure (s2, (emitSlotEvent slot events ev).2))
      (w, tr) = ((slot', ev'), (w', tr'))) :
    w'.wf = true ∧
    tr'.dnsQueries = tr.dnsQueries ∧
    tr'.dialedAddrs = tr.dialedAddrs ∧
    (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
    (∀ x ∈ tr.closedFds.toList, x ∈ tr'.closedFds.toList) ∧
    (∀ c b dl, slot'.phase ≠ .handshake c b dl) ∧
    (∀ st, slot'.phase ≠ .relay st) ∧
    (∀ c u h p cs ci le dl, slot'.phase ≠ .connecting c u h p cs ci le dl) ∧
    ev'.size = events.size + (if slot.eventEmitted then 0 else 1) := by
  obtain ⟨s2, w2, tr2, hCr, hRun⟩ := stateT_bind_eq hRun
  dsimp only [stateT_pure_run] at hRun
  injection hRun with hP hW; injection hP with hS hE; injection hW with hw ht
  subst hS; subst hE; subst hw; subst ht
  obtain ⟨hwf, hq, hd, hne, hcf, hph, hrel, hconn⟩ := enterClosingReply_laws_of_eq sys hRef limits _ cfd code w tr hWf s2 w2 tr2 hCr
  exact ⟨hwf, hq, hd, hne, hcf, hph, hrel, hconn, emitSlotEvent_snd_size slot events ev⟩

/-- Internal SysBridge helper lemma `startNextConnectAux_of_eq`. -/
theorem startNextConnectAux_of_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits)
    (slot : ClientSlot Nat dnsJob)
    (events : Array ConnectEvent)
    (cfd : Nat)
    (host : String) (port : UInt16)
    (candidates : Array IpAddr) :
    ∀ (fuel candIdx : Nat) (lastErr? : Option Errno)
      (w w' : HealthySysWorld) (tr tr' : SysAuditTrace Nat)
      (slot' : ClientSlot Nat dnsJob) (ev' : Array ConnectEvent),
      w.wf = true →
      StateT.run (startNextConnectAux (instrumentSysOps sys) limits slot events cfd host port candidates fuel candIdx lastErr?) (w, tr) =
        ((slot', ev'), (w', tr')) →
      w'.wf = true ∧
      tr'.dnsQueries = tr.dnsQueries ∧
      (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
      (∀ x ∈ tr.closedFds.toList, x ∈ tr'.closedFds.toList) ∧
      (∀ sa ∈ tr'.dialedAddrs.toList,
        sa ∈ tr.dialedAddrs.toList ∨ ∃ ip ∈ candidates.toList, sa = ipAddrToDialSockAddr ip port) ∧
      (∀ c b dl, slot'.phase ≠ .handshake c b dl) ∧
      (∀ st, slot'.phase = .relay st →
        st.pendingPrefix = slot.pipelined ∧ st.pendingOff = 0 ∧
        st.u2c.toList = Relay.reply200Bytes.data.toList ∧
        ev'.size = events.size + (if slot.eventEmitted then 0 else 1)) ∧
      (∀ c u h p cs ci le dl, slot'.phase = .connecting c u h p cs ci le dl →
        slot'.pipelined = slot.pipelined) ∧
      ((∃ c u h p cs ci le dl, slot'.phase = .connecting c u h p cs ci le dl) ∨
        ev'.size = events.size + (if slot.eventEmitted then 0 else 1))
  | 0, _, lastErr?, w, w', tr, tr', slot', ev', hWf, hRun => by
    unfold startNextConnectAux at hRun
    dsimp only at hRun
    obtain ⟨hw, hq, hd, hne, hcf, hph, hrel, hconn, hev⟩ := emitAndClosingReply_of_eq sys hRef limits slot events _ cfd 502 w w' tr tr' slot' ev' hWf hRun
    exact ⟨hw, hq, hne, hcf, fun sa hMem => Or.inl (hd ▸ hMem), hph,
      fun st h => absurd h (hrel st),
      fun c u h p cs ci le dl hc => absurd hc (hconn c u h p cs ci le dl),
      Or.inr hev⟩
  | fuel + 1, candIdx, lastErr?, w, w', tr, tr', slot', ev', hWf, hRun => by
    unfold startNextConnectAux at hRun
    by_cases hLt : candIdx < candidates.size
    · simp only [hLt, ↓reduceDIte] at hRun
      let ip := candidates[candIdx]'hLt
      let sa := ipAddrToDialSockAddr ip port
      have hIpMem : ip ∈ candidates.toList := Array.getElem_mem_toList hLt
      obtain ⟨rSock, w1, tr1, hSRun, hRun⟩ := stateT_bind_eq hRun
      have hSock := retryEintr_preserves
        (fun (wt : HealthySysWorld × SysAuditTrace Nat) =>
          wt.1.wf = true ∧ wt.2.dnsQueries = tr.dnsQueries ∧ wt.2.dialedAddrs = tr.dialedAddrs ∧
          wt.2.netErrs = tr.netErrs ∧ wt.2.closedFds = tr.closedFds)
        (fun _ _ => True)
        ((instrumentSysOps sys).net.socket sa.domain .stream { nonblock := true, cloexec := true } 0)
        (fun (wx, trx) ⟨hwx, hdq, hda, hne, hcf⟩ => by
          have hn := hRef.2.1 wx (.socket sa.domain .stream { nonblock := true, cloexec := true } 0) ((wf_iff_parts wx).mp hwx)
          dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
          dsimp only [StateT.run]
          rw [inst_net_socket]
          rcases hS : sys.net.socket sa.domain .stream { nonblock := true, cloexec := true } 0 wx with ⟨sr, wx'⟩
          rw [hS] at hn
          dsimp only at hn ⊢
          cases sr <;> exact ⟨⟨(wf_iff_parts wx').mpr hn.2.1, hdq, hda, hne, hcf⟩, Or.inr trivial⟩)
        MAX_EINTR_RETRIES (w, tr) ⟨hWf, rfl, rfl, rfl, rfl⟩
      have hSRun' : (retryEintr
        ((instrumentSysOps sys).net.socket sa.domain .stream { nonblock := true, cloexec := true } 0)
        MAX_EINTR_RETRIES).run (w, tr) = (rSock, (w1, tr1)) := hSRun
      rw [hSRun'] at hSock; clear hSRun hSRun'
      dsimp only at hSock
      rcases hSock.1 with ⟨hWf1, hDq1, hDa1, hNe1, hCf1⟩
      cases rSock with
      | error e =>
        dsimp only at hRun
        have hSub := startNextConnectAux_of_eq sys hRef limits slot events cfd host port candidates fuel (candIdx + 1) (some e) w1 w' tr1 tr' slot' ev' hWf1 hRun
        refine ⟨hSub.1, hSub.2.1.trans hDq1,
          fun x hx => hSub.2.2.1 x (hNe1.symm ▸ hx),
          fun x hx => hSub.2.2.2.1 x (hCf1.symm ▸ hx),
          fun x hx => ?_, hSub.2.2.2.2.2.1, hSub.2.2.2.2.2.2.1, hSub.2.2.2.2.2.2.2.1, hSub.2.2.2.2.2.2.2.2⟩
        rcases hSub.2.2.2.2.1 x hx with hIn1 | hCand
        · rw [hDa1] at hIn1; exact Or.inl hIn1
        · exact Or.inr hCand
      | ok ufd =>
        dsimp only at hRun
        obtain ⟨rConn, w2, tr2, hConnRun, hRun⟩ := stateT_bind_eq hRun
        have hConnRun' : (instrumentSysOps sys).net.connect ufd sa (w1, tr1) = (rConn, (w2, tr2)) := hConnRun
        clear hConnRun
        rw [inst_net_connect sys ufd sa w1 tr1] at hConnRun'
        have hConn := hRef.2.1 w1 (.connect ufd sa) ((wf_iff_parts w1).mp hWf1)
        dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hConn
        rcases hCRun : sys.net.connect ufd sa w1 with ⟨rConn0, w20⟩
        rw [hCRun] at hConn hConnRun'
        dsimp only at hConn hConnRun'
        injection hConnRun' with hr hw2; injection hw2 with hw2eq htr2eq
        subst hr; subst hw2eq; subst htr2eq
        have hWf2 : w20.wf = true := (wf_iff_parts w20).mpr hConn.2.1
        have hTr2Dial : ∀ x ∈ (tr1.dialedAddrs.push sa).toList,
            x ∈ tr.dialedAddrs.toList ∨ ∃ ip' ∈ candidates.toList, x = ipAddrToDialSockAddr ip' port := by
          intro x hx
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
          rcases hx with hOld | rfl
          · rw [hDa1] at hOld; exact Or.inl hOld
          · exact Or.inr ⟨ip, hIpMem, rfl⟩
        cases rConn0 with
        | ok _ =>
          dsimp only [stateT_pure_run] at hRun
          injection hRun with hp hw; injection hp with hs he; injection hw with hwe hte
          subst hs; subst he; subst hwe; subst hte
          refine ⟨hWf2, hDq1, fun x hx => hNe1.symm ▸ hx, fun x hx => hCf1.symm ▸ hx,
            hTr2Dial, ?_, ?_, ?_,
            Or.inr (emitSlotEvent_snd_size slot events _)⟩
          · intro _ _ _ h; cases h
          · intro st hRel
            dsimp only [enterRelay] at hRel
            injection hRel with hStEq
            subst hStEq
            exact ⟨emitSlotEvent_fst_pipelined slot events _, rfl, reply200_init_u2c_toList, emitSlotEvent_snd_size slot events _⟩
          · intro _ _ _ _ _ _ _ _ h; cases h
        | error e =>
          dsimp only at hRun
          by_cases hProg : (e == Errno.EINPROGRESS || e == Errno.EINTR) = true
          · simp only [hProg, ↓reduceIte] at hRun
            obtain ⟨now, w3, tr3, hM, hRun⟩ := stateT_bind_eq hRun
            obtain ⟨hWf3, hTr3⟩ := monoNowMs_of_eq sys hRef w20 w3 _ tr3 now hWf2 hM; clear hM
            dsimp only [stateT_pure_run] at hRun
            injection hRun with hp hw; injection hp with hs he; injection hw with hwe hte
            subst hs; subst he; subst hwe; subst hte
            rw [hTr3]
            refine ⟨hWf3, hDq1, fun x hx => hNe1.symm ▸ hx, fun x hx => hCf1.symm ▸ hx,
              hTr2Dial, ?_, ?_, fun _ _ _ _ _ _ _ _ _ => rfl, ?_⟩
            · intro _ _ _ h; cases h
            · intro _ h; cases h
            · exact Or.inl ⟨cfd, ufd, host, port, candidates, candIdx + 1, lastErr?, now + limits.connectTimeoutMs, rfl⟩
          · have hProgF : (e == Errno.EINPROGRESS || e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hProg
            simp only [hProgF, Bool.false_eq_true, ↓reduceIte] at hRun
            obtain ⟨u, w3, tr3, hC, hRun⟩ := stateT_bind_eq hRun
            obtain ⟨hWf3, hDq3, hDa3, hNe3, hCf3, _⟩ := closeFd_of_eq sys hRef w20 w3 _ tr3 ufd u hWf2 hC; clear hC
            have hSub := startNextConnectAux_of_eq sys hRef limits slot events cfd host port candidates fuel (candIdx + 1) (some e) w3 w' tr3 tr' slot' ev' hWf3 hRun
            refine ⟨hSub.1, ?_, ?_, ?_, ?_, hSub.2.2.2.2.2.1, hSub.2.2.2.2.2.2.1, hSub.2.2.2.2.2.2.2.1, hSub.2.2.2.2.2.2.2.2⟩
            · rw [hSub.2.1, hDq3]; exact hDq1
            · intro x hx; exact hSub.2.2.1 x (hNe3.symm ▸ hNe1.symm ▸ hx)
            · intro x hx; exact hSub.2.2.2.1 x (hCf3 x (hCf1.symm ▸ hx))
            · intro x hx
              rcases hSub.2.2.2.2.1 x hx with hIn3 | hCand
              · rw [hDa3] at hIn3; exact hTr2Dial x hIn3
              · exact Or.inr hCand
    · simp only [hLt, ↓reduceDIte] at hRun
      obtain ⟨hw, hq, hd, hne, hcf, hph, hrel, hconn, hev⟩ := emitAndClosingReply_of_eq sys hRef limits slot events _ cfd 502 w w' tr tr' slot' ev' hWf hRun
      exact ⟨hw, hq, hne, hcf, fun sa hMem => Or.inl (hd ▸ hMem), hph,
        fun st h => absurd h (hrel st),
        fun c u h p cs ci le dl hc => absurd hc (hconn c u h p cs ci le dl),
        Or.inr hev⟩

/-- Internal ConnectProxy proof helper `healthy_handleCompleteHeadSync_of_eq`. -/
theorem healthy_handleCompleteHeadSync_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (cfd : Nat)
    (headBytes pipelined : ByteArray)
    (w₀ w₁ : HealthySysWorld) (tr₀ tr₁ : SysAuditTrace Nat)
    (slot₁ : ClientSlot Nat Unit) (events₁ : Array ConnectEvent)
    (hWf₀ : w₀.wf = true)
    (hRun : StateT.run (handleCompleteHead (instrumentSysOps sys) cfg.limits
      (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
      (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
      slot events cfd headBytes pipelined) (w₀, tr₀) = ((slot₁, events₁), (w₁, tr₁))) :
    w₁.wf = true ∧
    (∀ e ∈ tr₀.netErrs.toList, e ∈ tr₁.netErrs.toList) ∧
    (∀ c b dl, slot₁.phase ≠ .handshake c b dl) ∧
    (∀ st, slot₁.phase = .relay st →
      st.pendingPrefix = pipelined ∧ st.pendingOff = 0 ∧ st.u2c.toList = Relay.reply200Bytes.data.toList) ∧
    (∀ c u h p cs ci le dl, slot₁.phase = .connecting c u h p cs ci le dl →
      slot₁.pipelined = pipelined) ∧
    ((∃ c u h p cs ci le dl, slot₁.phase = .connecting c u h p cs ci le dl) ∨
      events₁.size = events.size + (if slot.eventEmitted then 0 else 1)) ∧
    match Model.decideConnectHead cfg headBytes with
    | .deny _ _ _ =>
      tr₁.dnsQueries = tr₀.dnsQueries ∧
      tr₁.dialedAddrs = tr₀.dialedAddrs ∧
      events₁.size = events.size + (if slot.eventEmitted then 0 else 1)
    | .needResolve _ port (some litIp) =>
      tr₁.dnsQueries = tr₀.dnsQueries ∧
      (∀ sa ∈ tr₁.dialedAddrs.toList,
        sa ∈ tr₀.dialedAddrs.toList ∨
        (sa = ipAddrToDialSockAddr litIp port ∧
         Model.allowsIp cfg.ipPolicy litIp = true ∧
         Model.isBannedByPrefixes cfg.ipPolicy.extraBans (effectiveDialIp litIp) = false))
    | .needResolve host port none =>
      tr₁.dnsQueries = tr₀.dnsQueries.push host ∧
      let (dnsRes, _) := (sys.dns.getaddrinfo host { family := .any, sockType := .stream }).run w₀
      match dnsRes with
      | .error _ => tr₁.dialedAddrs = tr₀.dialedAddrs
      | .ok addrs =>
        ∀ sa ∈ tr₁.dialedAddrs.toList,
          sa ∈ tr₀.dialedAddrs.toList ∨
          ∃ ip, sa = ipAddrToDialSockAddr ip port ∧
            Model.allowsIp cfg.ipPolicy ip = true ∧
            Model.isBannedByPrefixes cfg.ipPolicy.extraBans (effectiveDialIp ip) = false ∧
            ∃ a ∈ addrs, a.scopeId = 0 ∧ dnsAddrToIpAddr? a = some ip := by
  unfold handleCompleteHead at hRun
  dsimp only at hRun
  cases hHead : Model.decideConnectHead cfg headBytes with
  | deny h? p? reason =>
    rw [hHead] at hRun
    dsimp only at hRun
    obtain ⟨hw, hq, hd, hne, _, hph, hrel, hconn, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits { slot with pipelined := pipelined } events _ cfd 403 w₀ w₁ tr₀ tr₁ slot₁ events₁ hWf₀ hRun
    exact ⟨hw, hne, hph, fun st h => absurd h (hrel st),
      fun c u h p cs ci le dl hc => absurd hc (hconn c u h p cs ci le dl),
      Or.inr hev, hq, hd, hev⟩
  | needResolve host port litIp? =>
    rw [hHead] at hRun
    let slotTgt : ClientSlot Nat Unit := { slot with pipelined := pipelined, target? := some (host, port) }
    cases litIp? with
    | some litIp =>
      dsimp only [handleResolveDecision] at hRun
      cases hDec : Model.decideResolvedIps cfg.ipPolicy host port #[litIp] with
      | deny r =>
        rw [hDec] at hRun
        dsimp only at hRun
        obtain ⟨hw, hq, hd, hne, _, hph, hrel, hconn, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slotTgt events _ cfd 403 w₀ w₁ tr₀ tr₁ slot₁ events₁ hWf₀ hRun
        exact ⟨hw, hne, hph, fun st h => absurd h (hrel st),
          fun c u h p cs ci le dl hc => absurd hc (hconn c u h p cs ci le dl),
          Or.inr hev, hq, fun sa hm => Or.inl (hd ▸ hm)⟩
      | dial primary fallbacks =>
        rw [hDec] at hRun
        dsimp only [startNextConnect] at hRun
        have hPrimEq : primary = litIp ∧ fallbacks = #[] ∧ Model.allowsIp cfg.ipPolicy litIp = true := by
          unfold Model.decideResolvedIps at hDec
          cases hAl : Model.allowsIp cfg.ipPolicy litIp with
          | false => simp [List.filter, hAl] at hDec
          | true =>
            dsimp only [List.filter] at hDec
            rw [hAl] at hDec
            dsimp only at hDec
            injection hDec with hp hf
            exact ⟨hp.symm, hf.symm, rfl⟩
        rcases hPrimEq with ⟨rfl, rfl, hAllow⟩
        have hNotBan := (dialSockAddr_never_banned cfg.ipPolicy primary hAllow).1
        have hDial := startNextConnectAux_of_eq sys hRef cfg.limits slotTgt events cfd host port (#[primary] ++ #[]) ((#[primary] ++ (#[] : Array IpAddr)).size - 0) 0 none w₀ w₁ tr₀ tr₁ slot₁ events₁ hWf₀ hRun
        refine ⟨hDial.1, hDial.2.2.1, hDial.2.2.2.2.2.1,
          fun st hr => ⟨(hDial.2.2.2.2.2.2.1 st hr).1, (hDial.2.2.2.2.2.2.1 st hr).2.1, (hDial.2.2.2.2.2.2.1 st hr).2.2.1⟩,
          hDial.2.2.2.2.2.2.2.1, hDial.2.2.2.2.2.2.2.2,
          hDial.2.1, fun sa hm => ?_⟩
        rcases hDial.2.2.2.2.1 sa hm with hOld | ⟨ip, hIpMem, rfl⟩
        · exact Or.inl hOld
        · have hEq : ip = primary := by simpa using hIpMem
          subst hEq
          exact Or.inr ⟨rfl, hAllow, hNotBan⟩
    | none =>
      dsimp only [startDnsSync] at hRun
      obtain ⟨dnsRes0, wDns, trDns0, hDnsRun, hRun⟩ := stateT_bind_eq hRun
      have hDnsRun' : (instrumentSysOps sys).dns.getaddrinfo host { family := .any, sockType := .stream } (w₀, tr₀) = (dnsRes0, (wDns, trDns0)) := hDnsRun
      clear hDnsRun
      rw [inst_dns_getaddrinfo sys host { family := .any, sockType := .stream } w₀ tr₀] at hDnsRun'
      have hDns := hRef.2.2.2.1 w₀ { host := host, hints := { family := .any, sockType := .stream } }
        ((wf_iff_parts w₀).mp hWf₀)
      dsimp only [Dns.execDnsReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
        pure, Pure.pure, StateT.pure, Id.run] at hDns
      rcases hDRun : (sys.dns.getaddrinfo host { family := .any, sockType := .stream }).run w₀ with ⟨dnsRes, wDns0⟩
      have hDRun' : sys.dns.getaddrinfo host { family := .any, sockType := .stream } w₀ = (dnsRes, wDns0) := hDRun
      dsimp only
      rw [hDRun]
      rw [hDRun'] at hDns hDnsRun'
      dsimp only at hDns hDnsRun' ⊢
      injection hDnsRun' with hdr hwd; injection hwd with hwde htde
      subst hdr; subst hwde; subst htde
      have hWfDns : wDns0.wf = true := (wf_iff_parts wDns0).mpr hDns.2.1
      let trDns := { tr₀ with dnsQueries := tr₀.dnsQueries.push host }
      cases dnsRes with
      | error dnsErr =>
        dsimp only at hRun ⊢
        obtain ⟨hw, hq, hd, hne, _, hph, hrel, hconn, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slotTgt events _ cfd 502 wDns0 w₁ trDns tr₁ slot₁ events₁ hWfDns hRun
        exact ⟨hw, hne, hph, fun st h => absurd h (hrel st),
          fun c u h p cs ci le dl hc => absurd hc (hconn c u h p cs ci le dl),
          Or.inr hev, hq, hd⟩
      | ok addrs =>
        dsimp only [handleResolveDecision] at hRun ⊢
        cases hDec : Model.decideResolvedIps cfg.ipPolicy host port (filterUnscopedDnsAddrs addrs) with
        | deny r =>
          rw [hDec] at hRun
          dsimp only at hRun
          obtain ⟨hw, hq, hd, hne, _, hph, hrel, hconn, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slotTgt events _ cfd 403 wDns0 w₁ trDns tr₁ slot₁ events₁ hWfDns hRun
          exact ⟨hw, hne, hph, fun st h => absurd h (hrel st),
            fun c u h p cs ci le dl hc => absurd hc (hconn c u h p cs ci le dl),
            Or.inr hev, hq, fun sa hm => Or.inl (hd ▸ hm)⟩
        | dial primary fallbacks =>
          rw [hDec] at hRun
          dsimp only [startNextConnect] at hRun
          have hCandProps : ∀ ip ∈ (#[primary] ++ fallbacks).toList,
              Model.allowsIp cfg.ipPolicy ip = true ∧
              Model.isBannedByPrefixes cfg.ipPolicy.extraBans (effectiveDialIp ip) = false ∧
              ∃ a ∈ addrs, a.scopeId = 0 ∧ dnsAddrToIpAddr? a = some ip := by
            unfold Model.decideResolvedIps at hDec
            cases hFilt : (filterUnscopedDnsAddrs addrs).toList.filter (Model.allowsIp cfg.ipPolicy) with
            | nil => rw [hFilt] at hDec; cases hDec
            | cons p rest =>
              rw [hFilt] at hDec
              dsimp only at hDec
              injection hDec with hp hf
              subst hp; subst hf
              intro ip hMem
              have hInFilt : ip ∈ (filterUnscopedDnsAddrs addrs).toList.filter (Model.allowsIp cfg.ipPolicy) := by
                rw [hFilt]
                simpa using hMem
              obtain ⟨hInUnsc, hAllow⟩ := List.mem_filter.mp hInFilt
              exact ⟨hAllow, (dialSockAddr_never_banned cfg.ipPolicy ip hAllow).1,
                filterUnscopedDnsAddrs_all_unscoped addrs ip hInUnsc⟩
          have hDial := startNextConnectAux_of_eq sys hRef cfg.limits slotTgt events cfd host port (#[primary] ++ fallbacks) ((#[primary] ++ fallbacks).size - 0) 0 none wDns0 w₁ trDns tr₁ slot₁ events₁ hWfDns hRun
          refine ⟨hDial.1, hDial.2.2.1, hDial.2.2.2.2.2.1,
            fun st hr => ⟨(hDial.2.2.2.2.2.2.1 st hr).1, (hDial.2.2.2.2.2.2.1 st hr).2.1, (hDial.2.2.2.2.2.2.1 st hr).2.2.1⟩,
            hDial.2.2.2.2.2.2.2.1, hDial.2.2.2.2.2.2.2.2,
            hDial.2.1, fun sa hm => ?_⟩
          rcases hDial.2.2.2.2.1 sa hm with hOld | ⟨ip, hIpMem, rfl⟩
          · exact Or.inl hOld
          · obtain ⟨hAl, hNb, hUnsc⟩ := hCandProps ip hIpMem
            exact Or.inr ⟨ip, rfl, hAl, hNb, hUnsc⟩

/-- End-to-end Stage-1 + Stage-2 authorization, DNS, `connect`, and pipelined-prefix laws over ANY `sys` refining `RefinesHealthyCProxySys`. -/
theorem healthy_handleCompleteHeadSync_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (cfd : Nat)
    (headBytes pipelined : ByteArray)
    (w₀ : HealthySysWorld) (tr₀ : SysAuditTrace Nat)
    (hWf₀ : w₀.wf = true) :
    let ((slot₁, events₁), (w₁, tr₁)) :=
      (handleCompleteHead (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events cfd headBytes pipelined).run (w₀, tr₀)
    w₁.wf = true ∧
    (∀ c b dl, slot₁.phase ≠ .handshake c b dl) ∧
    (∀ st, slot₁.phase = .relay st →
      st.pendingPrefix = pipelined ∧ st.pendingOff = 0 ∧ st.u2c.toList = Relay.reply200Bytes.data.toList) ∧
    (∀ c u h p cs ci le dl, slot₁.phase = .connecting c u h p cs ci le dl →
      slot₁.pipelined = pipelined) ∧
    match Model.decideConnectHead cfg headBytes with
    | .deny _ _ _ =>
      tr₁.dnsQueries = tr₀.dnsQueries ∧
      tr₁.dialedAddrs = tr₀.dialedAddrs ∧
      events₁.size = events.size + (if slot.eventEmitted then 0 else 1)
    | .needResolve _ port (some litIp) =>
      tr₁.dnsQueries = tr₀.dnsQueries ∧
      (∀ sa ∈ tr₁.dialedAddrs.toList,
        sa ∈ tr₀.dialedAddrs.toList ∨
        (sa = ipAddrToDialSockAddr litIp port ∧
         Model.allowsIp cfg.ipPolicy litIp = true ∧
         Model.isBannedByPrefixes cfg.ipPolicy.extraBans (effectiveDialIp litIp) = false))
    | .needResolve host port none =>
      tr₁.dnsQueries = tr₀.dnsQueries.push host ∧
      let (dnsRes, _) := (sys.dns.getaddrinfo host { family := .any, sockType := .stream }).run w₀
      match dnsRes with
      | .error _ => tr₁.dialedAddrs = tr₀.dialedAddrs
      | .ok addrs =>
        ∀ sa ∈ tr₁.dialedAddrs.toList,
          sa ∈ tr₀.dialedAddrs.toList ∨
          ∃ ip, sa = ipAddrToDialSockAddr ip port ∧
            Model.allowsIp cfg.ipPolicy ip = true ∧
            Model.isBannedByPrefixes cfg.ipPolicy.extraBans (effectiveDialIp ip) = false ∧
            ∃ a ∈ addrs, a.scopeId = 0 ∧ dnsAddrToIpAddr? a = some ip := by
  rcases hRun : (handleCompleteHead (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    slot events cfd headBytes pipelined).run (w₀, tr₀) with ⟨⟨slot₁, events₁⟩, w₁, tr₁⟩
  have h := healthy_handleCompleteHeadSync_of_eq sys hRef cfg slot events cfd headBytes pipelined w₀ w₁ tr₀ tr₁ slot₁ events₁ hWf₀ hRun
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- `acceptNewClientsAux` over ANY `sys` refining `RefinesHealthyCProxySys` preserves `wf`, enforces `slots.size ≤ maxConcurrentTunnels`, yields non-finished new slots, and retries `EINTR` until reaching `maxConcurrentTunnels` or recording a non-`EINTR` `accept4` error. -/
theorem healthy_acceptNewClientsAux_laws {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits)
    (listenFd : Nat)
    (nowMs : Nat) :
    ∀ (fuel : Nat) (slots : Array (ClientSlot Nat dnsJob)) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      slots.size ≤ limits.maxConcurrentTunnels →
      let (slots', (w', tr')) := (acceptNewClientsAux (instrumentSysOps sys) limits listenFd nowMs fuel slots).run (w, tr)
      w'.wf = true ∧
      slots'.size ≤ limits.maxConcurrentTunnels ∧
      (∀ s ∈ slots'.toList, s ∈ slots.toList ∨ s.isFinished = false) ∧
      (w.netEnv.eintrBudget + (limits.maxConcurrentTunnels - slots.size) ≤ fuel →
        slots'.size = limits.maxConcurrentTunnels ∨ tr.netErrs.size < tr'.netErrs.size)
  | 0, slots, w, _, hWf, hLe =>
    ⟨hWf, hLe, fun _ h => Or.inl h, fun hFuel => Or.inl (by omega)⟩
  | fuel + 1, slots, w, tr, hWf, hLe => by
    unfold acceptNewClientsAux
    by_cases hCap : slots.size ≥ limits.maxConcurrentTunnels
    · simp only [hCap, ↓reduceIte]
      dsimp only [StateT.run, pure, StateT.pure]
      exact ⟨hWf, hLe, fun _ h => Or.inl h, fun _ => Or.inl (by omega)⟩
    · simp only [hCap, ↓reduceIte]
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      have hNet := hRef.2.1 w (.accept4 listenFd { nonblock := true, cloexec := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [Net.execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
        pure, Pure.pure, StateT.pure, Id.run] at hNet
      rw [inst_net_accept4]
      rcases hRun : sys.net.accept4 listenFd { nonblock := true, cloexec := true } w with ⟨res, w1⟩
      rw [hRun] at hNet
      dsimp only at hNet ⊢
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      have hBud := healthyNetStep_eintrBudget w.netEnv w1.netEnv (.accept4 listenFd { nonblock := true, cloexec := true }) (Net.outcomeOfAccepted res) hNet.1
      cases res with
      | ok pair =>
        rcases pair with ⟨cfd, peerSa⟩
        have hBudEq : w1.netEnv.eintrBudget = w.netEnv.eintrBudget := hBud.2 (fun hc => nomatch hc)
        let newSlot : ClientSlot Nat dnsJob :=
          { phase := .handshake cfd ByteArray.empty (nowMs + limits.headerTimeoutMs)
            eventEmitted := false
            target? := none
            pipelined := ByteArray.empty }
        let tr1 := { tr with openedFds := tr.openedFds.push cfd }
        have hPushSz : (slots.push newSlot).size = slots.size + 1 := Array.size_push ..
        have hSub := healthy_acceptNewClientsAux_laws sys hRef limits listenFd nowMs fuel (slots.push newSlot) w1 tr1 hWf1 (by omega)
        dsimp only [newSlot] at hPushSz
        dsimp only [StateT.run, newSlot, tr1] at hSub ⊢
        rcases hRec : acceptNewClientsAux (instrumentSysOps sys) limits listenFd nowMs fuel (slots.push newSlot) (w1, tr1) with ⟨slots2, wt2⟩
        rcases wt2 with ⟨w2, tr2⟩
        dsimp only [newSlot, tr1] at hRec
        rw [hRec] at hSub
        dsimp only at hSub ⊢
        refine ⟨hSub.1, hSub.2.1, fun s hs => ?_, fun hFuel => hSub.2.2.2 (by omega)⟩
        rcases hSub.2.2.1 s hs with hInPush | hNotFin
        · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hInPush
          rcases hInPush with hOld | rfl
          · exact Or.inl hOld
          · exact Or.inr rfl
        · exact Or.inr hNotFin
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          have hEqEi : Net.outcomeOfAccepted (.error e) = .err Errno.EINTR :=
            congrArg Net.NetOutcome.err (beq_iff_eq.mp hEi)
          obtain ⟨hPosB, hDecB⟩ := hBud.1 hEqEi
          have hSub := healthy_acceptNewClientsAux_laws sys hRef limits listenFd nowMs fuel slots w1 tr hWf1 hLe
          dsimp only [StateT.run] at hSub ⊢
          rcases hRec : acceptNewClientsAux (instrumentSysOps sys) limits listenFd nowMs fuel slots (w1, tr) with ⟨slots2, wt2⟩
          rcases wt2 with ⟨w2, tr2⟩
          rw [hRec] at hSub
          dsimp only at hSub ⊢
          exact ⟨hSub.1, hSub.2.1, hSub.2.2.1, fun hFuel => hSub.2.2.2 (by omega)⟩
        · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
          simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
          dsimp only [StateT.run, pure, StateT.pure]
          exact ⟨hWf1, hLe, fun _ h => Or.inl h, fun _ => Or.inr (by simp)⟩


end LeanSwe.ConnectProxy.Proofs
