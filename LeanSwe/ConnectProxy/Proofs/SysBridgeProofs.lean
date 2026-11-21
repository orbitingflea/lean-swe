import LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge
open LeanSwe.ConnectProxy.HealthySys

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
          dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hn
          dsimp only [StateT.run]
          rw [inst_net_socket]
          rcases hS : sys.net.socket sa.domain .stream { nonblock := true, cloexec := true } 0 wx with ⟨sr, wx'⟩
          rw [hS] at hn
          dsimp only at hn ⊢
          cases sr <;> exact ⟨⟨(wf_iff_parts wx').mpr hn.2.1, hdq, hda, hne, hcf⟩, Or.inr trivial⟩)
        MAX_EINTR_RETRIES (w, tr) ⟨hWf, rfl, rfl, rfl, rfl⟩
      have hSRun' : (retryEintr MAX_EINTR_RETRIES
        ((instrumentSysOps sys).net.socket sa.domain .stream { nonblock := true, cloexec := true } 0)).run (w, tr) = (rSock, (w1, tr1)) := hSRun
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
        dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hConn
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

private theorem healthy_handleCompleteHeadSync_of_eq
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
      dsimp only [execDnsReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
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
      dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
        pure, Pure.pure, StateT.pure, Id.run] at hNet
      rw [inst_net_accept4]
      rcases hRun : sys.net.accept4 listenFd { nonblock := true, cloexec := true } w with ⟨res, w1⟩
      rw [hRun] at hNet
      dsimp only at hNet ⊢
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      have hBud := healthyNetStep_eintrBudget w.netEnv w1.netEnv (.accept4 listenFd { nonblock := true, cloexec := true }) (netOutcomeAccepted res) hNet.1
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
          have hEqEi : netOutcomeAccepted (.error e) = .err Errno.EINTR :=
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

private theorem healthy_stepHandshakeReadAux_of_eq
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (clientFd : Nat)
    (deadlineMs : Nat) :
    ∀ (fuel : Nat) (headBuf : ByteArray)
      (w w' : HealthySysWorld) (tr tr' : SysAuditTrace Nat)
      (slot' : ClientSlot Nat Unit) (ev' : Array ConnectEvent),
      w.wf = true →
      headBuf.size ≤ cfg.limits.maxHeaderBytes →
      StateT.run (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events clientFd deadlineMs fuel headBuf) (w, tr) = ((slot', ev'), (w', tr')) →
      w'.wf = true ∧
      (∀ e ∈ tr.netErrs.toList, e ∈ tr'.netErrs.toList) ∧
      (∀ cfd' buf' dl', slot'.phase = .handshake cfd' buf' dl' →
        ev' = events ∧
        slot'.eventEmitted = slot.eventEmitted ∧
        buf'.size ≤ cfg.limits.maxHeaderBytes ∧
        ((headBuf.size < cfg.limits.maxHeaderBytes ∨ fuel > 0) → buf'.size < cfg.limits.maxHeaderBytes) ∧
        (∃ rxDelta : List UInt8,
          tr'.recvBytes.toList = tr.recvBytes.toList ++ rxDelta ∧
          buf'.data.toList = headBuf.data.toList ++ rxDelta) ∧
        (w.netEnv.eintrBudget + (cfg.limits.maxHeaderBytes - headBuf.size) < fuel →
          Errno.EAGAIN ∈ tr'.netErrs.toList)) ∧
      ((∀ cfd' buf' dl', slot'.phase ≠ .handshake cfd' buf' dl') →
        (∃ c u h p cs ci le dl, slot'.phase = .connecting c u h p cs ci le dl) ∨
        ev'.size = events.size + (if slot.eventEmitted then 0 else 1))
  | 0, headBuf, w, w', tr, tr', slot', ev', hWf, hLe, hRun => by
    dsimp only [stepHandshakeReadAux, stateT_pure_run] at hRun
    injection hRun with hp hw; injection hp with hs he; injection hw with hwe hte
    subst hs; subst he; subst hwe; subst hte
    refine ⟨hWf, fun _ h => h, fun _ buf' _ hPh => ?_, fun hNoHs => absurd rfl (hNoHs clientFd headBuf deadlineMs)⟩
    cases hPh
    exact ⟨rfl, rfl, hLe, fun hOr => by omega, ⟨[], by simp, by simp⟩, fun hLt => by omega⟩
  | fuel + 1, headBuf, w, w', tr, tr', slot', ev', hWf, hLe, hRun => by
    unfold stepHandshakeReadAux at hRun
    by_cases hMax : headBuf.size ≥ cfg.limits.maxHeaderBytes
    · simp only [hMax, ↓reduceIte] at hRun
      obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w w' tr tr' slot' ev' hWf hRun
      exact ⟨hw, hne, fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
    · simp only [hMax, ↓reduceIte] at hRun
      have hLtMax : headBuf.size < cfg.limits.maxHeaderBytes := by omega
      let rem := cfg.limits.maxHeaderBytes - headBuf.size
      let want := UInt32.ofNat (Nat.min rem HANDSHAKE_CHUNK_MAX)
      have hChunkBnd : 0 < HANDSHAKE_CHUNK_MAX ∧ HANDSHAKE_CHUNK_MAX < 4294967296 := by decide
      have hWantToNat : want.toNat = Nat.min rem HANDSHAKE_CHUNK_MAX := by
        have hSmall : Nat.min rem HANDSHAKE_CHUNK_MAX < UInt32.size := by
          simp only [nat_min_eq_min]
          change min rem HANDSHAKE_CHUNK_MAX < 4294967296
          omega
        exact UInt32.toNat_ofNat_of_lt hSmall
      have hWantLeRem : want.toNat ≤ rem := by
        rw [hWantToNat]; simp only [nat_min_eq_min]; omega
      have hWantPos : want.toNat > 0 := by
        rw [hWantToNat]; simp only [nat_min_eq_min]; omega
      obtain ⟨recvRes0, w10, tr10, hRecvRun, hRun⟩ := stateT_bind_eq hRun
      have hRecvRun' : (instrumentSysOps sys).net.recvfrom clientFd want { dontwait := true } (w, tr) = (recvRes0, (w10, tr10)) := hRecvRun
      clear hRecvRun
      rw [inst_net_recvfrom sys clientFd want { dontwait := true } w tr] at hRecvRun'
      have hNet := hRef.2.1 w (.recvfrom clientFd want { dontwait := true }) ((wf_iff_parts w).mp hWf)
      dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
        pure, Pure.pure, StateT.pure, Id.run] at hNet
      rcases hRNet : sys.net.recvfrom clientFd want { dontwait := true } w with ⟨recvRes, w1⟩
      rw [hRNet] at hNet hRecvRun'
      dsimp only at hNet hRecvRun'
      injection hRecvRun' with hrr hwt; injection hwt with hwe hte
      subst hrr; subst hwe; subst hte
      have hWf1 : w1.wf = true := (wf_iff_parts w1).mpr hNet.2.1
      have hBud := healthyNetStep_eintrBudget w.netEnv w1.netEnv (.recvfrom clientFd want { dontwait := true }) (netOutcomeBytes recvRes) hNet.1
      cases recvRes with
      | error e =>
        dsimp only at hRun
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte] at hRun
          have hEqEi : netOutcomeBytes (.error e) = .err Errno.EINTR :=
            congrArg Net.NetOutcome.err (beq_iff_eq.mp hEi)
          obtain ⟨hPosB, hDecB⟩ := hBud.1 hEqEi
          have hSub := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs fuel headBuf w1 w' tr tr' slot' ev' hWf1 hLe hRun
          refine ⟨hSub.1, hSub.2.1, fun cfd' buf' dl' hPh => ?_, hSub.2.2.2⟩
          obtain ⟨hEvE, hEmE, hBLe, hBLt, hRx, hPr⟩ := hSub.2.2.1 cfd' buf' dl' hPh
          exact ⟨hEvE, hEmE, hBLe, fun _ => hBLt (Or.inl hLtMax), hRx, fun hFuel => hPr (by omega)⟩
        · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
          simp only [hEiF, Bool.false_eq_true, ↓reduceIte] at hRun
          have hMono : ∀ x ∈ tr.netErrs.toList, x ∈ (tr.netErrs.push e).toList := by
            intro x hx; simp [Array.toList_push, hx]
          by_cases hAg : (e == Errno.EAGAIN) = true
          · simp only [hAg, ↓reduceIte, stateT_pure_run] at hRun
            injection hRun with hp hw; injection hp with hs he; injection hw with hwe hte
            subst hs; subst he; subst hwe; subst hte
            have hInAg : Errno.EAGAIN ∈ (tr.netErrs.push e).toList := by
              rw [beq_iff_eq.mp hAg]; simp [Array.toList_push]
            refine ⟨hWf1, hMono, fun _ buf' _ hPh => ?_, fun hNoHs => absurd rfl (hNoHs clientFd headBuf deadlineMs)⟩
            cases hPh
            exact ⟨rfl, rfl, hLe, fun _ => hLtMax, ⟨[], by simp, by simp⟩, fun _ => hInAg⟩
          · have hAgF : (e == Errno.EAGAIN) = false := Bool.eq_false_iff.mpr hAg
            simp only [hAgF, Bool.false_eq_true, ↓reduceIte] at hRun
            let trErr := { tr with netErrs := tr.netErrs.push e }
            obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w1 w' trErr tr' slot' ev' hWf1 hRun
            exact ⟨hw, fun x hx => hne x (hMono x hx), fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
      | ok chunk =>
        dsimp only at hRun
        have hBudEq : w1.netEnv.eintrBudget = w.netEnv.eintrBudget := hBud.2 (fun hc => nomatch hc)
        let tr1 := { tr with recvBytes := tr.recvBytes ++
          (let k := Nat.min chunk.size want.toNat; if k == chunk.size then chunk.data else (chunk.extract 0 k).data) }
        by_cases hChunk0 : (chunk.size == 0) = true
        · simp only [hChunk0, ↓reduceIte] at hRun
          obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w1 w' tr1 tr' slot' ev' hWf1 hRun
          exact ⟨hw, hne, fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
        · have hChunkF : (chunk.size == 0) = false := Bool.eq_false_iff.mpr hChunk0
          simp only [hChunkF, Bool.false_eq_true, ↓reduceIte] at hRun
          have hChunkPos : chunk.size > 0 := by
            have hNe : chunk.size ≠ 0 := fun hc => hChunk0 (beq_iff_eq.mpr hc)
            omega
          let takeN := Nat.min chunk.size want.toNat
          let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
          let nextBuf := if headBuf.size == 0 then part else headBuf ++ part
          have hPartData : part.data = (let k := Nat.min chunk.size want.toNat; if k == chunk.size then chunk.data else (chunk.extract 0 k).data) := by
            dsimp only [part, takeN]
            split <;> rfl
          have hPartSz : part.size ≤ rem ∧ part.size > 0 := by
            dsimp only [part, takeN]
            simp only [nat_min_eq_min]
            split
            · rename_i hEq; have := beq_iff_eq.mp hEq; omega
            · simp only [ByteArray.size_extract]; omega
          have hNextSz : nextBuf.size ≤ cfg.limits.maxHeaderBytes ∧ nextBuf.size > headBuf.size := by
            dsimp only [nextBuf]
            by_cases hHb0 : (headBuf.size == 0) = true
            · simp only [hHb0, ↓reduceIte]
              have := beq_iff_eq.mp hHb0; omega
            · simp only [Bool.eq_false_iff.mpr hHb0, Bool.false_eq_true, ↓reduceIte, ByteArray.size_append]
              omega
          have hNextList : nextBuf.data.toList = headBuf.data.toList ++ part.data.toList := by
            dsimp only [nextBuf]
            by_cases hHb0 : (headBuf.size == 0) = true
            · simp only [hHb0, ↓reduceIte]
              have hHbNil : headBuf.data.toList = [] :=
                List.eq_nil_of_length_eq_zero (by have := beq_iff_eq.mp hHb0; simpa using this)
              simp [hHbNil]
            · simp only [Bool.eq_false_iff.mpr hHb0, Bool.false_eq_true, ↓reduceIte]
              simp [ByteArray.data_append]
          cases hScan : findCrlfCrlf nextBuf (headBuf.size - 3) with
          | some pos =>
            rw [hScan] at hRun
            dsimp only at hRun
            let pipeBytes :=
              if pos + 4 ≥ nextBuf.size then ByteArray.empty else nextBuf.extract (pos + 4) nextBuf.size
            have hComp := healthy_handleCompleteHeadSync_of_eq sys hRef cfg slot events clientFd (nextBuf.extract 0 (pos + 4)) pipeBytes w1 w' tr1 tr' slot' ev' hWf1 hRun
            exact ⟨hComp.1, hComp.2.1, fun c b dl hPh => absurd hPh (hComp.2.2.1 c b dl), fun _ => hComp.2.2.2.2.2.1⟩
          | none =>
            rw [hScan] at hRun
            dsimp only at hRun
            by_cases hNextGe : nextBuf.size ≥ cfg.limits.maxHeaderBytes
            · have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want, rem] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              obtain ⟨hw, _, _, hne, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w1 w' tr1 tr' slot' ev' hWf1 hRun
              exact ⟨hw, hne, fun c b dl hPh => absurd hPh (hph c b dl), fun _ => Or.inr hev⟩
            · have hNextLt : nextBuf.size < cfg.limits.maxHeaderBytes := by omega
              have hNextGe' := hNextGe
              dsimp only [nextBuf, part, takeN, want, rem] at hNextGe'
              simp only [hNextGe', ↓reduceIte] at hRun
              have hSub := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs fuel nextBuf w1 w' tr1 tr' slot' ev' hWf1 hNextSz.1 hRun
              refine ⟨hSub.1, hSub.2.1, fun cfd' buf' dl' hPh => ?_, hSub.2.2.2⟩
              obtain ⟨hEvE, hEmE, hBLe, hBLt, ⟨rxDelta2, hTr2, hBuf2⟩, hProg2⟩ := hSub.2.2.1 cfd' buf' dl' hPh
              refine ⟨hEvE, hEmE, hBLe, fun _ => hBLt (Or.inl hNextLt), ⟨part.data.toList ++ rxDelta2, ?_, ?_⟩, fun hFuel => ?_⟩
              · rw [hTr2]; dsimp only [tr1]; rw [Array.toList_append, ← hPartData, List.append_assoc]
              · rw [hBuf2, hNextList, List.append_assoc]
              · exact hProg2 (by omega)

/-- `stepHandshakeReadAux` over ANY `sys` refining `RefinesHealthyCProxySys` preserves `wf` and enforces `headBuf.size ≤ maxHeaderBytes` across arbitrary short `recvfrom` chunks and `EINTR` retries. -/
theorem healthy_stepHandshakeReadAux_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (clientFd : Nat)
    (deadlineMs : Nat)
    (fuel : Nat) (headBuf : ByteArray) (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true)
    (hLe : headBuf.size ≤ cfg.limits.maxHeaderBytes) :
    let ((slot', _), (w', _)) :=
      (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events clientFd deadlineMs fuel headBuf).run (w, tr)
    w'.wf = true ∧
    ∀ cfd' buf' dl', slot'.phase = .handshake cfd' buf' dl' → buf'.size ≤ cfg.limits.maxHeaderBytes := by
  rcases hRun : (stepHandshakeReadAux (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    slot events clientFd deadlineMs fuel headBuf).run (w, tr) with ⟨⟨slot', ev'⟩, w', tr'⟩
  have h := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs fuel headBuf w w' tr tr' slot' ev' hWf hLe hRun
  exact ⟨h.1, fun c b d hp => (h.2.2.1 c b d hp).2.2.1⟩

/-- `stepHandshake` (with `startDnsSync`) over ANY `sys` refining `RefinesHealthyCProxySys` preserves `wf`, enforces `headBuf.size ≤ maxHeaderBytes` (strict `< maxHeaderBytes` after readable wakeups), conserves handshake bytes, retries `EINTR` until `EAGAIN` or transition, and emits a `ConnectEvent` unless entering `.connecting`. -/
theorem healthy_stepHandshakeSync_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (slot : ClientSlot Nat Unit)
    (events : Array ConnectEvent)
    (clientFd : Nat)
    (headBuf : ByteArray)
    (deadlineMs : Nat)
    (cRev : Poll.PollEvents)
    (nowMs : Nat)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true)
    (hLe : headBuf.size ≤ cfg.limits.maxHeaderBytes)
    (hSlotPh : slot.phase = .handshake clientFd headBuf deadlineMs) :
    let ((slot', ev'), (w', tr')) :=
      (stepHandshake (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
        slot events clientFd headBuf deadlineMs cRev nowMs).run (w, tr)
    w'.wf = true ∧
    (∀ cfd' buf' dl', slot'.phase = .handshake cfd' buf' dl' →
      buf'.size ≤ cfg.limits.maxHeaderBytes ∧
      ((cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = true →
        buf'.size < cfg.limits.maxHeaderBytes) ∧
      (∃ rxDelta : List UInt8,
        tr'.recvBytes.toList = tr.recvBytes.toList ++ rxDelta ∧
        buf'.data.toList = headBuf.data.toList ++ rxDelta) ∧
      (cRev.pollin = true ∧
          w.netEnv.eintrBudget + (cfg.limits.maxHeaderBytes - headBuf.size) < MAX_HANDSHAKE_STEPS →
        Errno.EAGAIN ∈ tr'.netErrs.toList)) ∧
    ((∀ cfd' buf' dl', slot'.phase ≠ .handshake cfd' buf' dl') →
      (∃ c u h p cs ci le dl, slot'.phase = .connecting c u h p cs ci le dl) ∨
      ev'.size = events.size + (if slot.eventEmitted then 0 else 1)) := by
  rcases hTop : (stepHandshake (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    slot events clientFd headBuf deadlineMs cRev nowMs).run (w, tr) with ⟨⟨slot', ev'⟩, w', tr'⟩
  have hTop' : StateT.run (stepHandshake (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    slot events clientFd headBuf deadlineMs cRev nowMs) (w, tr) = ((slot', ev'), (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold stepHandshake at hTop'
  by_cases hEv : (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = true
  · simp only [hEv, ↓reduceIte] at hTop'
    obtain ⟨⟨slot1, ev1⟩, w1, tr1, hStep1, hFin⟩ := stateT_bind_eq hTop'
    clear hTop'
    dsimp only at hFin
    obtain ⟨hWf1, _, hHs1, hEx1⟩ := healthy_stepHandshakeReadAux_of_eq sys hRef cfg slot events clientFd deadlineMs MAX_HANDSHAKE_STEPS headBuf w w1 tr tr1 slot1 ev1 hWf hLe hStep1
    clear hStep1
    cases hPh : slot1.phase with
    | handshake cfd hb1 dl =>
      rw [hPh] at hFin; dsimp only at hFin
      by_cases hTo : nowMs ≥ dl
      · simp only [hTo, ↓reduceIte] at hFin
        obtain ⟨hEvEq, hEmEq, _⟩ := hHs1 cfd hb1 dl hPh
        obtain ⟨hw, _, _, _, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot1 ev1 _ cfd 403 w1 w' tr1 tr' slot' ev' hWf1 hFin
        rw [hEvEq, hEmEq] at hev
        exact ⟨hw, fun c b d hEq => absurd hEq (hph c b d), fun _ => Or.inr hev⟩
      · simp only [hTo, ↓reduceIte, stateT_pure_run] at hFin
        injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
        subst hS; subst hE; subst hW; subst hT
        refine ⟨hWf1, fun cfd' buf' dl' hEq => ?_, fun hNoHs => absurd hPh (hNoHs cfd hb1 dl)⟩
        obtain ⟨_, _, hBLe, hBLt, hRx, hPr⟩ := hHs1 cfd' buf' dl' hEq
        exact ⟨hBLe, fun _ => hBLt (Or.inr (by decide)), hRx, fun ⟨_, hF⟩ => hPr hF⟩
    | dns _ _ _ _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | connecting _ _ _ _ _ _ _ _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | relay _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | closingReply _ _ _ _ _ _ =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
    | done =>
      rw [hPh] at hFin; dsimp only [stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      have hNoHs1 : ∀ c b d, slot1.phase ≠ .handshake c b d := by rw [hPh]; intro _ _ _ h; nomatch h
      exact ⟨hWf1, fun _ _ _ hEq => absurd hEq (hNoHs1 _ _ _), fun _ => hEx1 hNoHs1⟩
  · have hEvF : (cRev.pollin || cRev.pollhup || cRev.pollerr || cRev.pollnval) = false := Bool.eq_false_iff.mpr hEv
    have hPollinF : cRev.pollin = false := by
      cases hp : cRev.pollin
      · rfl
      · simp [hp] at hEvF
    simp only [hEvF, Bool.false_eq_true, ↓reduceIte] at hTop'
    obtain ⟨⟨slot1, ev1⟩, w1, tr1, hStep1, hFin⟩ := stateT_bind_eq hTop'
    clear hTop'
    dsimp only [stateT_pure_run] at hStep1
    injection hStep1 with hp hw; injection hp with hs he; injection hw with hwe hte
    subst hs; subst he; subst hwe; subst hte
    dsimp only at hFin
    rw [hSlotPh] at hFin
    dsimp only at hFin
    by_cases hTo : nowMs ≥ deadlineMs
    · simp only [hTo, ↓reduceIte] at hFin
      obtain ⟨hw, _, _, _, _, hph, _, _, hev⟩ := emitAndClosingReply_of_eq sys hRef cfg.limits slot events _ clientFd 403 w w' tr tr' slot' ev' hWf hFin
      exact ⟨hw, fun c b d hEq => absurd hEq (hph c b d), fun _ => Or.inr hev⟩
    · simp only [hTo, ↓reduceIte, stateT_pure_run] at hFin
      injection hFin with hPair hWT; injection hPair with hS hE; injection hWT with hW hT
      subst hS; subst hE; subst hW; subst hT
      refine ⟨hWf, fun cfd' buf' dl' hEq => ?_, fun hNoHs => absurd hSlotPh (hNoHs clientFd headBuf deadlineMs)⟩
      rw [hSlotPh] at hEq
      cases hEq
      exact ⟨hLe, fun hBad => absurd hBad hEv, ⟨[], by simp, by simp⟩,
        fun ⟨hPin, _⟩ => by rw [hPollinF] at hPin; cases hPin⟩

/-- `emitSlotEvent` emits at most one `ConnectEvent` and permanently sets `eventEmitted = true`. -/
theorem emitSlotEvent_at_most_once {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent) (ev : ConnectEvent) :
    let (slot', events') := emitSlotEvent slot events ev
    slot'.eventEmitted = true ∧
    events'.size = events.size + (if slot.eventEmitted then 0 else 1) := by
  unfold emitSlotEvent
  dsimp only
  cases hEm : slot.eventEmitted <;> simp [hEm]

private theorem closeOptFd_instrumented_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (optFd : Option Nat) (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (_, (w', tr')) := (Relay.closeOptFd (instrumentSysOps sys).closeFd optFd).run (w, tr)
    w'.wf = true ∧
    w'.proxyTable = w.proxyTable ∧
    (∀ x ∈ tr.closedFds.toList, x ∈ tr'.closedFds.toList) ∧
    (∀ j, Files.assocGet w.filesEnv.state.fds j = none → Files.assocGet w'.filesEnv.state.fds j = none) ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup →
      (w'.filesEnv.state.fds.map Prod.fst).Nodup ∧
      ∀ d, optFd = some d → d ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds d = none) := by
  cases optFd with
  | none =>
    dsimp only [Relay.closeOptFd, StateT.run, pure, StateT.pure]
    exact ⟨hWf, rfl, fun _ h => h, fun _ h => h, fun hNd => ⟨hNd, fun _ h => nomatch h⟩⟩
  | some d =>
    unfold Relay.closeOptFd
    have hCl := healthy_closeFd_instrumented_laws sys hRef w tr d hWf
    dsimp only [StateT.run] at hCl ⊢
    rcases hR : (instrumentSysOps sys).closeFd d (w, tr) with ⟨_, wt'⟩
    rcases wt' with ⟨w', tr'⟩
    rw [hR] at hCl
    dsimp only at hCl ⊢
    refine ⟨hCl.1, hCl.2.1, ?_, hCl.2.2.2.1, fun hNd => ⟨(hCl.2.2.2.2 hNd).1, fun d' hd' => ?_⟩⟩
    · intro x hx; rw [hCl.2.2.1]; simp [Array.toList_push, hx]
    · injection hd' with heq; subst heq
      refine ⟨?_, (hCl.2.2.2.2 hNd).2⟩
      rw [hCl.2.2.1]; simp [Array.toList_push]

private theorem healthy_teardownSlot_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (slot : ClientSlot Nat Unit) (events : Array ConnectEvent)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true) :
    let (events1, (w1, tr1)) :=
      (teardownSlot (instrumentSysOps sys) (fun _ => pure ()) slot events).run (w, tr)
    w1.wf = true ∧
    w1.proxyTable = w.proxyTable ∧
    events1.size = events.size + (if slot.eventEmitted then 0 else 1) ∧
    (∀ x ∈ tr.closedFds.toList, x ∈ tr1.closedFds.toList) ∧
    (∀ j, Files.assocGet w.filesEnv.state.fds j = none → Files.assocGet w1.filesEnv.state.fds j = none) ∧
    ((w.filesEnv.state.fds.map Prod.fst).Nodup →
      (w1.filesEnv.state.fds.map Prod.fst).Nodup ∧
      ∀ fd ∈ slotOpenFds slot, fd ∈ tr1.closedFds.toList ∧ Files.assocGet w1.filesEnv.state.fds fd = none) := by
  have hEmitSz :
      (match slot.target? with
       | some (h, p) =>
         emitSlotEvent slot events { host := some h, port := some p, outcome := .failed, reason := some "proxy stopped" }
       | none =>
         emitSlotEvent slot events { outcome := .failed, reason := some "proxy stopped" }).2.size =
      events.size + (if slot.eventEmitted then 0 else 1) := by
    cases slot.target? with
    | some _ => exact (emitSlotEvent_at_most_once slot events _).2
    | none => exact (emitSlotEvent_at_most_once slot events _).2
  unfold teardownSlot slotOpenFds
  cases slot.phase with
  | handshake cfd _ _ =>
    dsimp only
    rw [stateT_bind_run]
    have h1 := healthy_closeFd_instrumented_laws sys hRef w tr cfd hWf
    rcases hR1 : ((instrumentSysOps sys).closeFd cfd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only [stateT_pure_run] at h1 ⊢
    refine ⟨h1.1, h1.2.1, hEmitSz, ?_, h1.2.2.2.1, fun hNd => ⟨(h1.2.2.2.2 hNd).1, ?_⟩⟩
    · intro x hx; rw [h1.2.2.1]; simp [Array.toList_push, hx]
    · intro fd hMem; simp only [List.mem_singleton] at hMem; subst hMem
      refine ⟨?_, (h1.2.2.2.2 hNd).2⟩
      rw [h1.2.2.1]; simp [Array.toList_push]
  | dns cfd _ _ _ =>
    dsimp only
    rw [stateT_bind_run, stateT_pure_run]
    dsimp only
    rw [stateT_bind_run]
    have h1 := healthy_closeFd_instrumented_laws sys hRef w tr cfd hWf
    rcases hR1 : ((instrumentSysOps sys).closeFd cfd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only [stateT_pure_run] at h1 ⊢
    refine ⟨h1.1, h1.2.1, hEmitSz, ?_, h1.2.2.2.1, fun hNd => ⟨(h1.2.2.2.2 hNd).1, ?_⟩⟩
    · intro x hx; rw [h1.2.2.1]; simp [Array.toList_push, hx]
    · intro fd hMem; simp only [List.mem_singleton] at hMem; subst hMem
      refine ⟨?_, (h1.2.2.2.2 hNd).2⟩
      rw [h1.2.2.1]; simp [Array.toList_push]
  | connecting cfd ufd _ _ _ _ _ _ =>
    dsimp only
    rw [stateT_bind_run]
    have h1 := healthy_closeFd_instrumented_laws sys hRef w tr ufd hWf
    rcases hR1 : ((instrumentSysOps sys).closeFd ufd).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only at h1 ⊢
    rw [stateT_bind_run]
    have h2 := healthy_closeFd_instrumented_laws sys hRef w1 tr1 cfd h1.1
    rcases hR2 : ((instrumentSysOps sys).closeFd cfd).run (w1, tr1) with ⟨_, w2, tr2⟩
    rw [hR2] at h2
    dsimp only [stateT_pure_run] at h2 ⊢
    refine ⟨h2.1, h2.2.1.trans h1.2.1, hEmitSz, ?_, fun j hj => h2.2.2.2.1 j (h1.2.2.2.1 j hj), fun hNd => ?_⟩
    · intro x hx; rw [h2.2.2.1, h1.2.2.1]; simp [Array.toList_push, hx]
    · have hNd1 := (h1.2.2.2.2 hNd).1
      have hNd2 := (h2.2.2.2.2 hNd1).1
      refine ⟨hNd2, fun fd hMem => ?_⟩
      rcases List.mem_cons.mp hMem with rfl | hRest
      · refine ⟨?_, h2.2.2.2.1 fd (h1.2.2.2.2 hNd).2⟩
        rw [h2.2.2.1, h1.2.2.1]; simp [Array.toList_push]
      · simp only [List.mem_singleton] at hRest; subst hRest
        refine ⟨?_, (h2.2.2.2.2 hNd1).2⟩
        rw [h2.2.2.1]; simp [Array.toList_push]
  | relay st =>
    unfold Relay.closeRelayBoth
    dsimp only
    rw [stateT_bind_run, stateT_bind_run]
    have h1 := closeOptFd_instrumented_laws sys hRef st.clientFd? w tr hWf
    rcases hR1 : (Relay.closeOptFd (instrumentSysOps sys).closeFd st.clientFd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only at h1 ⊢
    rw [stateT_bind_run]
    have h2 := closeOptFd_instrumented_laws sys hRef st.upstreamFd? w1 tr1 h1.1
    rcases hR2 : (Relay.closeOptFd (instrumentSysOps sys).closeFd st.upstreamFd?).run (w1, tr1) with ⟨_, w2, tr2⟩
    rw [hR2] at h2
    dsimp only [stateT_pure_run] at h2 ⊢
    refine ⟨h2.1, h2.2.1.trans h1.2.1, hEmitSz,
      fun x hx => h2.2.2.1 x (h1.2.2.1 x hx),
      fun j hj => h2.2.2.2.1 j (h1.2.2.2.1 j hj),
      fun hNd => ?_⟩
    obtain ⟨hNd1, hOpt1⟩ := h1.2.2.2.2 hNd
    obtain ⟨hNd2, hOpt2⟩ := h2.2.2.2.2 hNd1
    refine ⟨hNd2, fun fd hMem => ?_⟩
    rw [List.mem_append] at hMem
    rcases hMem with hC | hU
    · cases hc : st.clientFd? with
      | none => rw [hc] at hC; cases hC
      | some c =>
        rw [hc, List.mem_singleton] at hC; subst hC
        obtain ⟨hIn1, hNone1⟩ := hOpt1 fd hc
        exact ⟨h2.2.2.1 fd hIn1, h2.2.2.2.1 fd hNone1⟩
    · cases hu : st.upstreamFd? with
      | none => rw [hu] at hU; cases hU
      | some u =>
        rw [hu, List.mem_singleton] at hU; subst hU
        exact hOpt2 fd hu
  | closingReply cfd? _ _ _ _ _ =>
    dsimp only
    rw [stateT_bind_run]
    have h1 := closeOptFd_instrumented_laws sys hRef cfd? w tr hWf
    rcases hR1 : (Relay.closeOptFd (instrumentSysOps sys).closeFd cfd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1
    dsimp only [stateT_pure_run] at h1 ⊢
    refine ⟨h1.1, h1.2.1, hEmitSz, h1.2.2.1, h1.2.2.2.1, fun hNd => ?_⟩
    obtain ⟨hNd1, hOpt1⟩ := h1.2.2.2.2 hNd
    refine ⟨hNd1, fun fd hMem => ?_⟩
    cases hc : cfd? with
    | none => rw [hc] at hMem; cases hMem
    | some c =>
      rw [hc, List.mem_singleton] at hMem; subst hMem
      exact hOpt1 fd hc
  | done =>
    dsimp only [stateT_bind_run, stateT_pure_run]
    exact ⟨hWf, rfl, hEmitSz, fun _ h => h, fun _ h => h, fun hNd => ⟨hNd, fun _ h => nomatch h⟩⟩

/-- `teardownAllSlotsList` over ANY `sys` refining `RefinesHealthyCProxySys`: emits exact 1 `"proxy stopped"` event per undecided slot, preserves `wf`, `Nodup`, and `proxyTable`, and deterministically closes + erases every descriptor in `slotOpenFds`! -/
theorem healthy_teardownAllSlotsList_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys) :
    ∀ (slots : List (ClientSlot Nat Unit)) (events : Array ConnectEvent)
      (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      w.wf = true →
      let (events', (w', tr')) :=
        (teardownAllSlotsList (instrumentSysOps sys) (fun _ => pure ()) slots events).run (w, tr)
      w'.wf = true ∧
      w'.proxyTable = w.proxyTable ∧
      events'.size = events.size + (slots.filter (fun s => !s.eventEmitted)).length ∧
      (∀ x ∈ tr.closedFds.toList, x ∈ tr'.closedFds.toList) ∧
      (∀ j, Files.assocGet w.filesEnv.state.fds j = none → Files.assocGet w'.filesEnv.state.fds j = none) ∧
      ((w.filesEnv.state.fds.map Prod.fst).Nodup →
        (w'.filesEnv.state.fds.map Prod.fst).Nodup ∧
        ∀ fd ∈ slots.flatMap slotOpenFds,
          fd ∈ tr'.closedFds.toList ∧ Files.assocGet w'.filesEnv.state.fds fd = none)
  | [], events, w, tr, hWf => by
    simp only [teardownAllSlotsList, List.filter_nil, List.length_nil, Nat.add_zero]
    exact ⟨hWf, rfl, rfl, fun _ h => h, fun _ h => h, fun hNd => ⟨hNd, fun _ h => nomatch h⟩⟩
  | slot :: rest, events, w, tr, hWf => by
    unfold teardownAllSlotsList
    rw [stateT_bind_run]
    have hSlot := healthy_teardownSlot_laws sys hRef slot events w tr hWf
    rcases hSlotRun : (teardownSlot (instrumentSysOps sys) (fun _ => pure ()) slot events).run (w, tr) with ⟨events1, w1, tr1⟩
    rw [hSlotRun] at hSlot
    dsimp only at hSlot ⊢
    rcases hSlot with ⟨hWf1, hTbl1, hEmitSz, hClosed1, hGet1, hNdSlot⟩
    have hRest := healthy_teardownAllSlotsList_laws sys hRef rest events1 w1 tr1 hWf1
    rcases hRestRun : (teardownAllSlotsList (instrumentSysOps sys) (fun _ => pure ()) rest events1).run (w1, tr1) with ⟨ev2, w2, tr2⟩
    rw [hRestRun] at hRest
    dsimp only at hRest ⊢
    refine ⟨hRest.1, hRest.2.1.trans hTbl1, ?_,
      fun x hx => hRest.2.2.2.1 x (hClosed1 x hx),
      fun j hj => hRest.2.2.2.2.1 j (hGet1 j hj),
      fun hNd => ?_⟩
    · rw [hRest.2.2.1, hEmitSz]
      cases hEm : slot.eventEmitted <;> simp [List.filter, hEm] <;> omega
    · obtain ⟨hNd1, hSlotFds⟩ := hNdSlot hNd
      obtain ⟨hNd2, hRestFds⟩ := hRest.2.2.2.2.2 hNd1
      refine ⟨hNd2, fun fd hMem => ?_⟩
      simp only [List.flatMap_cons, List.mem_append] at hMem
      rcases hMem with hHead | hTail
      · obtain ⟨hIn1, hNone1⟩ := hSlotFds fd hHead
        exact ⟨hRest.2.2.2.1 fd hIn1, hRest.2.2.2.2.1 fd hNone1⟩
      · exact hRestFds fd hTail

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
    ((Relay.closeOptFd (instrumentSysOps sys).closeFd optFd).run (w, tr)).2.2.openedFds = tr.openedFds := by
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
    rcases hR1 : (Relay.closeOptFd (instrumentSysOps sys).closeFd st.clientFd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1; dsimp only at h1 ⊢; rw [stateT_bind_run]
    have h2 := closeOptFd_openedFds_eq sys st.upstreamFd? w1 tr1
    rcases hR2 : (Relay.closeOptFd (instrumentSysOps sys).closeFd st.upstreamFd?).run (w1, tr1) with ⟨_, w2, tr2⟩
    rw [hR2] at h2; dsimp only [stateT_pure_run] at h2 ⊢; exact h2.trans h1
  | closingReply cfd? _ _ _ _ _ =>
    dsimp only; rw [stateT_bind_run]
    have h1 := closeOptFd_openedFds_eq sys cfd? w tr
    rcases hR1 : (Relay.closeOptFd (instrumentSysOps sys).closeFd cfd?).run (w, tr) with ⟨_, w1, tr1⟩
    rw [hR1] at h1; dsimp only [stateT_pure_run] at h1 ⊢; exact h1
  | done => rfl

private theorem teardownAllSlotsList_openedFds_eq
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

private theorem retryEintr_invariant {W α : Type}
    (I : W → Prop)
    (Post : Except Errno α → W → Prop)
    (act : StateM W (Except Errno α))
    (hStep : ∀ w, I w →
      let (r, w') := act.run w
      (r = .error Errno.EINTR → I w') ∧ Post r w') :
    ∀ (fuel : Nat) (w : W), I w →
      let (r, w') := (retryEintr fuel act).run w
      Post r w'
  | 0, w, hI => (hStep w hI).2
  | fuel + 1, w, hI => by
    have h0 := hStep w hI
    dsimp only [retryEintr, StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run] at h0 ⊢
    rcases hAct : act w with ⟨r0, w1⟩
    rw [hAct] at h0
    dsimp only at h0 ⊢
    rcases r0 with e | v
    · by_cases hEi : (e == Errno.EINTR) = true
      · simp only [hEi, ↓reduceIte]
        exact retryEintr_invariant I Post act hStep fuel w1 (h0.1 (congrArg Except.error (beq_iff_eq.mp hEi)))
      · have hEiF : (e == Errno.EINTR) = false := Bool.eq_false_iff.mpr hEi
        simp only [hEiF, Bool.false_eq_true, ↓reduceIte]
        exact h0.2
    · exact h0.2

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
        dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
          pure, Pure.pure, StateT.pure, Id.run] at hn
        dsimp only [StateT.run]
        rw [inst_net_socket]
        rcases hS : sys.net.socket .inet .stream { nonblock := true, cloexec := true } 0 wx with ⟨sr, wx'⟩
        rw [hS] at hn
        dsimp only at hn ⊢
        have hwx' : wx'.wf = true := (wf_iff_parts wx').mpr hn.2.1
        have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.socket .inet .stream { nonblock := true, cloexec := true } 0) (netOutcomeOpened sr) hn.1
        cases sr with
        | error e =>
          dsimp only
          refine ⟨fun hEi => ?_, fun hNe => ?_, ⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, hop⟩⟩
          · injection hEi with he; subst he
            exact ⟨⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, hop⟩, hBud.1 rfl⟩
          · have hNeOut : netOutcomeOpened (.error e) ≠ .err Errno.EINTR := fun hc => by injection hc with he; exact hNe (congrArg Except.error he)
            exact Nat.le_of_eq (hBud.2 hNeOut)
        | ok lfd =>
          dsimp only
          exact ⟨(fun hBad => nomatch hBad), fun _ => Nat.le_of_eq (hBud.2 (fun hc => nomatch hc)),
                 ⟨hwx', hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), hdq, hda, hba, by rw [hop]⟩⟩)
      MAX_EINTR_RETRIES (w₀, tr₀) ⟨hWf₀, rfl, id, rfl, rfl, rfl, rfl⟩
    have hR1' : (retryEintr MAX_EINTR_RETRIES
      ((instrumentSysOps sys).net.socket .inet .stream { nonblock := true, cloexec := true } 0)).run (w₀, tr₀) = (r1, (w1, tr1)) := hR1
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
          dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
            pure, Pure.pure, StateT.pure, Id.run] at hn
          dsimp only [StateT.run]
          rw [inst_net_setsockopt]
          rcases hS : sys.net.setsockopt lfd .reuseAddr 1 wx with ⟨sr, wx'⟩
          rw [hS] at hn
          dsimp only at hn ⊢
          have hP : wx'.wf = true ∧ wx'.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wx') ∧ trx = tr1 :=
            ⟨(wf_iff_parts wx').mpr hn.2.1, hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), htr⟩
          have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.setsockopt lfd .reuseAddr 1) (netOutcomeUnit sr) hn.1
          refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
          · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
          · cases sr with
            | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
            | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he)))
        )
        MAX_EINTR_RETRIES (w1, tr1) ⟨hWf1, hTbl1, hNd1, rfl⟩
      have hR2' : (retryEintr MAX_EINTR_RETRIES ((instrumentSysOps sys).net.setsockopt lfd .reuseAddr 1)).run (w1, tr1) = (r2, (w2, tr2)) := hR2
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
            dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
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
            have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.bind lfd bindAddr) (netOutcomeUnit sr) hn.1
            refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
            · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
            · cases sr with
              | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
              | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he))))
          MAX_EINTR_RETRIES (w2, tr1) ⟨hWf2, hTbl2, hNd2, hDq1, hDa1, fun sa hm => Or.inl (hBa1 ▸ hm), hOp1⟩
        have hR3' : (retryEintr MAX_EINTR_RETRIES ((instrumentSysOps sys).net.bind lfd bindAddr)).run (w2, tr1) = (r3, (w3, tr3)) := hR3
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
              dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
                pure, Pure.pure, StateT.pure, Id.run] at hn
              dsimp only [StateT.run]
              rw [inst_net_listen]
              rcases hS : sys.net.listen lfd 128 wx with ⟨sr, wx'⟩
              rw [hS] at hn
              dsimp only at hn ⊢
              have hP : wx'.wf = true ∧ wx'.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wx') ∧ trx = tr3 :=
                ⟨(wf_iff_parts wx').mpr hn.2.1, hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), htr⟩
              have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.listen lfd 128) (netOutcomeUnit sr) hn.1
              refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
              · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
              · cases sr with
                | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
                | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he))))
            MAX_EINTR_RETRIES (w3, tr3) ⟨hWf3, hTbl3, hNd3, rfl⟩
          have hR4' : (retryEintr MAX_EINTR_RETRIES ((instrumentSysOps sys).net.listen lfd 128)).run (w3, tr3) = (r4, (w4, tr4)) := hR4
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
                dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
                  pure, Pure.pure, StateT.pure, Id.run] at hn
                dsimp only [StateT.run]
                rw [inst_net_getsockname]
                rcases hS : sys.net.getsockname lfd wx with ⟨sr, wx'⟩
                rw [hS] at hn
                dsimp only at hn ⊢
                have hP : wx'.wf = true ∧ wx'.proxyTable = w₀.proxyTable ∧ (fdsNd w₀ → fdsNd wx') ∧ trx = tr3 :=
                  ⟨(wf_iff_parts wx').mpr hn.2.1, hn.2.2.1.trans htbl, fun h0 => hn.2.2.2 (hnd h0), htr⟩
                have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.getsockname lfd) (netOutcomeAddr sr) hn.1
                refine ⟨fun hEi => ⟨hP, ?_⟩, fun hNe => ?_, hP⟩
                · cases sr with | ok _ => cases hEi | error e => injection hEi with he; subst he; exact hBud.1 rfl
                · cases sr with
                  | ok _ => exact Nat.le_of_eq (hBud.2 (fun hc => nomatch hc))
                  | error e => exact Nat.le_of_eq (hBud.2 (fun hc => by injection hc with he; exact hNe (congrArg Except.error he))))
              MAX_EINTR_RETRIES (w4, tr3) ⟨hWf4, hTbl4, hNd4, rfl⟩
            have hR5' : (retryEintr MAX_EINTR_RETRIES ((instrumentSysOps sys).net.getsockname lfd)).run (w4, tr3) = (r5, (w5, tr5)) := hR5
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
                      dsimp only [execNetReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
                        pure, Pure.pure, StateT.pure, Id.run] at hn
                      dsimp only [StateT.run]
                      rw [inst_net_socketpair]
                      rcases hS : sys.net.socketpair .unix .stream { nonblock := true, cloexec := true } wx with ⟨sr, wx'⟩
                      rw [hS] at hn
                      dsimp only at hn ⊢
                      have hwx' : wx'.wf = true := (wf_iff_parts wx').mpr hn.2.1
                      have hBud := healthyNetStep_eintrBudget wx.netEnv wx'.netEnv (.socketpair .unix .stream { nonblock := true, cloexec := true }) (netOutcomePair sr) hn.1
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
                  have hR6' : (retryEintr MAX_EINTR_RETRIES
                    ((instrumentSysOps sys).net.socketpair .unix .stream { nonblock := true, cloexec := true })).run (w5, tr3) = (r6, (w6, tr6)) := hR6
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

private theorem nat_max_eq_max (a b : Nat) : Nat.max a b = max a b := rfl

private theorem foldl_max_handleId_laws {fd : Type} (xs : List (SyncProxyEntry fd)) :
    ∀ (acc : Nat),
      acc ≤ xs.foldl (fun m e => Nat.max m e.handleId) acc ∧
      ∀ e ∈ xs, e.handleId ≤ xs.foldl (fun m e => Nat.max m e.handleId) acc := by
  induction xs with
  | nil => intro acc; exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨hAcc, hMem⟩ := ih (Nat.max acc hd.handleId)
    simp only [nat_max_eq_max] at hAcc ⊢
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) hAcc, fun e he => ?_⟩
    rcases he with rfl | hTail
    · exact Nat.le_trans (Nat.le_max_right _ _) hAcc
    · exact hMem e hTail

/-- `freshSyncHandleId tbl` strictly exceeds every `e.handleId` in `tbl.entries`. -/
theorem freshSyncHandleId_gt {fd : Type} (tbl : SyncProxyTable fd) :
    ∀ e ∈ tbl.entries, e.handleId < freshSyncHandleId tbl := by
  intro e he
  unfold freshSyncHandleId
  have hLe := (foldl_max_handleId_laws tbl.entries 0).2 e he
  simp only [nat_max_eq_max] at hLe ⊢
  omega

private theorem find_none_of_all_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = false) → xs.find? p = none
  | [], _ => rfl
  | x :: tl, h => by
    simp only [List.find?, h x (List.Mem.head _)]
    exact find_none_of_all_false p tl (fun y hy => h y (List.Mem.tail _ hy))

private theorem filter_all_true {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = true) → xs.filter p = xs
  | [], _ => rfl
  | x :: tl, h => by
    simp only [List.filter, h x (List.Mem.head _), filter_all_true p tl (fun y hy => h y (List.Mem.tail _ hy))]

private theorem healthy_stopActiveProxy_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (wBase : HealthySysWorld) (trBase : SysAuditTrace Nat)
    (port : UInt16) (vcfg : ValidProxyConfig)
    (lfd wakeR wakeW : Nat)
    (slots : Array (ClientSlot Nat Unit))
    (events : Array ConnectEvent)
    (hWf : wBase.wf = true) :
    let rawOps := realBridgeTarget.mkRawOps (instrumentSysOps sys)
    let hid := freshSyncHandleId wBase.proxyTable
    let activeEntry : SyncProxyEntry Nat :=
      { handleId := hid
        port := port
        vcfg := vcfg
        listenFd := lfd
        wakeR := wakeR
        wakeW := wakeW
        slots := slots
        events := events }
    let wActive : HealthySysWorld :=
      { wBase with proxyTable := { nextHandleId := hid + 1, entries := activeEntry :: wBase.proxyTable.entries } }
    let proxy : RunningProxy := { handleId := hid, port := port }
    let (stopRes, (w₁, tr₁)) := (rawOps.stopProxy proxy).run (wActive, trBase)
    w₁.wf = true ∧
    w₁.proxyTable.entries = wBase.proxyTable.entries ∧
    tr₁.openedFds = trBase.openedFds ∧
    (∃ finalEvs,
      stopRes = .ok finalEvs ∧
      finalEvs.size = events.size + (slots.toList.filter (fun s => !s.eventEmitted)).length) ∧
    ((wBase.filesEnv.state.fds.map Prod.fst).Nodup →
      (w₁.filesEnv.state.fds.map Prod.fst).Nodup ∧
      ∀ fd ∈ ([lfd, wakeR, wakeW] ++ slots.toList.flatMap slotOpenFds),
        fd ∈ tr₁.closedFds.toList ∧ Files.assocGet w₁.filesEnv.state.fds fd = none) := by
  dsimp only
  let hid := freshSyncHandleId wBase.proxyTable
  have hGt := freshSyncHandleId_gt wBase.proxyTable
  have hRestBne : ∀ e ∈ wBase.proxyTable.entries, (e.handleId != hid) = true := by
    intro e he
    exact bne_iff_ne.mpr (Nat.ne_of_lt (hGt e he))
  have hFilt :
      ({ handleId := hid, port := port, vcfg := vcfg, listenFd := lfd, wakeR := wakeR, wakeW := wakeW,
         slots := slots, events := events } :: wBase.proxyTable.entries).filter (fun e => e.handleId != hid) =
      wBase.proxyTable.entries := by
    simp only [List.filter, bne_self_eq_false]
    exact filter_all_true _ wBase.proxyTable.entries hRestBne
  rcases hTop : ((realBridgeTarget.mkRawOps (instrumentSysOps sys)).stopProxy { handleId := hid, port := port }).run
    ({ wBase with proxyTable := { nextHandleId := hid + 1, entries :=
        { handleId := hid, port := port, vcfg := vcfg, listenFd := lfd, wakeR := wakeR, wakeW := wakeW, slots := slots, events := events } ::
        wBase.proxyTable.entries } }, trBase) with ⟨stopRes, w₁, tr₁⟩
  have hRun : StateT.run ((realBridgeTarget.mkRawOps (instrumentSysOps sys)).stopProxy { handleId := hid, port := port })
    ({ wBase with proxyTable := { nextHandleId := hid + 1, entries :=
        { handleId := hid, port := port, vcfg := vcfg, listenFd := lfd, wakeR := wakeR, wakeW := wakeW, slots := slots, events := events } ::
        wBase.proxyTable.entries } }, trBase) = (stopRes, (w₁, tr₁)) := hTop
  clear hTop
  dsimp only [realBridgeTarget, mkSyncRawOps] at hRun ⊢
  rw [stateT_bind_run, stateT_get_run] at hRun
  dsimp only [List.find?] at hRun
  simp only [beq_self_eq_true] at hRun
  rw [hFilt] at hRun
  rw [stateT_bind_run, stateT_set_run] at hRun
  dsimp only at hRun
  let wSet : HealthySysWorld :=
    { wBase with proxyTable := { nextHandleId := hid + 1, entries := wBase.proxyTable.entries } }
  obtain ⟨finalEvs, wTd, trTd, hRunTd, hRun⟩ := stateT_bind_eq hRun
  have hTd := healthy_teardownAllSlotsList_laws sys hRef slots.toList events wSet trBase hWf
  have hTdOp := teardownAllSlotsList_openedFds_eq sys slots.toList events wSet trBase
  have hRunTd' : (teardownAllSlotsList (instrumentSysOps sys) (fun _ => pure ()) slots.toList events).run (wSet, trBase) =
    (finalEvs, (wTd, trTd)) := hRunTd
  rw [hRunTd'] at hTd hTdOp; clear hRunTd hRunTd'
  dsimp only at hTd hTdOp
  obtain ⟨u1, wC1, trC1, hR1, hRun⟩ := stateT_bind_eq hRun
  have hCl1 := healthy_closeFd_instrumented_laws sys hRef wTd trTd lfd hTd.1
  have hR1' : ((instrumentSysOps sys).closeFd lfd).run (wTd, trTd) = (u1, (wC1, trC1)) := hR1
  rw [hR1'] at hCl1; clear hR1 hR1'
  dsimp only at hCl1
  obtain ⟨u2, wC2, trC2, hR2, hRun⟩ := stateT_bind_eq hRun
  have hCl2 := healthy_closeFd_instrumented_laws sys hRef wC1 trC1 wakeR hCl1.1
  have hR2' : ((instrumentSysOps sys).closeFd wakeR).run (wC1, trC1) = (u2, (wC2, trC2)) := hR2
  rw [hR2'] at hCl2; clear hR2 hR2'
  dsimp only at hCl2
  obtain ⟨u3, wC3, trC3, hR3, hRun⟩ := stateT_bind_eq hRun
  have hCl3 := healthy_closeFd_instrumented_laws sys hRef wC2 trC2 wakeW hCl2.1
  have hR3' : ((instrumentSysOps sys).closeFd wakeW).run (wC2, trC2) = (u3, (wC3, trC3)) := hR3
  rw [hR3'] at hCl3; clear hR3 hR3'
  dsimp only [stateT_pure_run] at hCl3 hRun
  injection hRun with hs hwt; injection hwt with hwe hte
  subst hs; subst hwe; subst hte
  have hTblEq : wC3.proxyTable.entries = wBase.proxyTable.entries := by
    rw [hCl3.2.1, hCl2.2.1, hCl1.2.1, hTd.2.1]
  have hOpEq : trC3.openedFds = trBase.openedFds := by
    rw [hCl3.2.2.1, hCl2.2.2.1, hCl1.2.2.1]
    exact hTdOp
  refine ⟨hCl3.1, hTblEq, hOpEq, ⟨finalEvs, rfl, hTd.2.2.1⟩, fun hNd0 => ?_⟩
  obtain ⟨hNdTd, hTdClosed⟩ := hTd.2.2.2.2.2 hNd0
  obtain ⟨hNd1, hNoneLfd⟩ := hCl1.2.2.2.2 hNdTd
  obtain ⟨hNd2, hNoneWakeR⟩ := hCl2.2.2.2.2 hNd1
  obtain ⟨hNd3, hNoneWakeW⟩ := hCl3.2.2.2.2 hNd2
  refine ⟨hNd3, fun fd hMem => ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hMem
  rcases hMem with rfl | rfl | rfl | hSlotMem
  · refine ⟨?_, hCl3.2.2.2.1 fd (hCl2.2.2.2.1 fd hNoneLfd)⟩
    rw [hCl3.2.2.1, hCl2.2.2.1, hCl1.2.2.1]
    simp [Array.toList_push]
  · refine ⟨?_, hCl3.2.2.2.1 fd hNoneWakeR⟩
    rw [hCl3.2.2.1, hCl2.2.2.1]
    simp [Array.toList_push]
  · refine ⟨?_, hNoneWakeW⟩
    rw [hCl3.2.2.1]
    simp [Array.toList_push]
  · obtain ⟨hInTd, hNoneTd⟩ := hTdClosed fd hSlotMem
    refine ⟨?_, hCl3.2.2.2.1 fd (hCl2.2.2.2.1 fd (hCl1.2.2.2.1 fd hNoneTd))⟩
    rw [hCl3.2.2.1, hCl2.2.2.1, hCl1.2.2.1]
    simp [Array.toList_push, hInTd]

/-- Full teardown, handle-table conservation, double-stop rejection, and `withProxyModel` zero-FD-leak laws over ANY `sys` refining `RefinesHealthyCProxySys`! -/
theorem healthy_stopProxy_and_withProxy_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (w₀ : HealthySysWorld)
    (cfg : ProxyConfig)
    (vcfg : ValidProxyConfig)
    (lfd wakeR wakeW : Nat)
    (slots : Array (ClientSlot Nat Unit))
    (events : Array ConnectEvent)
    (hWf₀ : w₀.wf = true)
    (hNd₀ : (w₀.filesEnv.state.fds.map Prod.fst).Nodup) :
    let rawOps := realBridgeTarget.mkRawOps (instrumentSysOps sys)
    let hid := freshSyncHandleId w₀.proxyTable
    let activeEntry : SyncProxyEntry Nat :=
      { handleId := hid
        port := 8080
        vcfg := vcfg
        listenFd := lfd
        wakeR := wakeR
        wakeW := wakeW
        slots := slots
        events := events }
    let wActive : HealthySysWorld :=
      { w₀ with proxyTable := { nextHandleId := hid + 1, entries := activeEntry :: w₀.proxyTable.entries } }
    let proxy : RunningProxy := { handleId := hid, port := 8080 }
    let (stopRes, (w₁, tr₁)) := (rawOps.stopProxy proxy).run (wActive, {})
    let (dblRes, (w₁d, tr₁d)) := (rawOps.stopProxy proxy).run (w₁, tr₁)
    let (_, (w₂, tr₂)) := (Model.withProxyModel rawOps cfg (fun p => pure (.ok p.port))).run (w₀, {})
    (w₁.wf = true ∧ (rawOps.activeProxyCount.run (w₁, tr₁)).1 = w₀.proxyTable.entries.length) ∧
    (∃ finalEvs,
      stopRes = .ok finalEvs ∧
      finalEvs.size = events.size + (slots.toList.filter (fun s => !s.eventEmitted)).length) ∧
    (∀ fd ∈ ([lfd, wakeR, wakeW] ++ slots.toList.flatMap slotOpenFds),
      fd ∈ tr₁.closedFds.toList ∧ Files.assocGet w₁.filesEnv.state.fds fd = none) ∧
    ((∃ err, dblRes = .error err ∧ err.kind = .invalidInput ∧ err.message ≠ "") ∧
      (rawOps.activeProxyCount.run (w₁d, tr₁d)).1 = w₀.proxyTable.entries.length) ∧
    (w₂.wf = true ∧ (rawOps.activeProxyCount.run (w₂, tr₂)).1 = w₀.proxyTable.entries.length) ∧
    (∀ fd ∈ tr₂.openedFds.toList,
      fd ∈ tr₂.closedFds.toList ∧ Files.assocGet w₂.filesEnv.state.fds fd = none) := by
  dsimp only
  let rawOps := realBridgeTarget.mkRawOps (instrumentSysOps sys)
  let hid := freshSyncHandleId w₀.proxyTable
  let activeEntry : SyncProxyEntry Nat :=
    { handleId := hid, port := 8080, vcfg := vcfg, listenFd := lfd, wakeR := wakeR, wakeW := wakeW, slots := slots, events := events }
  let wActive : HealthySysWorld :=
    { w₀ with proxyTable := { nextHandleId := hid + 1, entries := activeEntry :: w₀.proxyTable.entries } }
  let proxy : RunningProxy := { handleId := hid, port := 8080 }
  have hStop1 := healthy_stopActiveProxy_laws sys hRef w₀ {} 8080 vcfg lfd wakeR wakeW slots events hWf₀
  dsimp only at hStop1
  rcases hRStop1 : (rawOps.stopProxy proxy).run (wActive, {}) with ⟨stopRes, ⟨w₁, tr₁⟩⟩
  have hRStop1' : ((realBridgeTarget.mkRawOps (instrumentSysOps sys)).stopProxy { handleId := freshSyncHandleId w₀.proxyTable, port := 8080 }).run (wActive, {}) = (stopRes, (w₁, tr₁)) := hRStop1
  rw [hRStop1'] at hStop1; clear hRStop1 hRStop1'
  dsimp only at hStop1 ⊢
  rcases hStop1 with ⟨hWf₁, hEntries₁, _, hFinalEvs, hStop1Nd⟩
  obtain ⟨_, hClosed1⟩ := hStop1Nd hNd₀
  have hCnt₁ : (rawOps.activeProxyCount.run (w₁, tr₁)).1 = w₀.proxyTable.entries.length := by
    dsimp only [rawOps, realBridgeTarget, mkSyncRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get, Id.run]
    rw [hEntries₁]
  have hFindNone : w₁.proxyTable.entries.find? (fun e => e.handleId == hid) = none := by
    rw [hEntries₁]
    apply find_none_of_all_false
    intro e he
    exact beq_false_of_ne (Nat.ne_of_lt (freshSyncHandleId_gt w₀.proxyTable e he))
  have hDbl :
      let (dblRes, (w₁d, tr₁d)) := (rawOps.stopProxy proxy).run (w₁, tr₁)
      (∃ err, dblRes = .error err ∧ err.kind = .invalidInput ∧ err.message ≠ "") ∧
      (rawOps.activeProxyCount.run (w₁d, tr₁d)).1 = w₀.proxyTable.entries.length := by
    dsimp only [rawOps, realBridgeTarget, mkSyncRawOps, proxy, hid]
    rw [stateT_bind_run, stateT_get_run]
    dsimp only
    rw [hFindNone]
    dsimp only [stateT_pure_run]
    have hMapErr := mapRawErrorPure_laws (.invalidArgument none "proxy handle is not active")
    refine ⟨⟨_, rfl, hMapErr.2.1, hMapErr.1⟩, ?_⟩
    rw [stateT_bind_run, stateT_get_run]
    dsimp only [stateT_pure_run]
    rw [hEntries₁]
  have hWith :
      let (_, (w₂, tr₂)) := (Model.withProxyModel rawOps cfg (fun p => pure (.ok p.port))).run (w₀, {})
      (w₂.wf = true ∧ (rawOps.activeProxyCount.run (w₂, tr₂)).1 = w₀.proxyTable.entries.length) ∧
      (∀ fd ∈ tr₂.openedFds.toList,
        fd ∈ tr₂.closedFds.toList ∧ Files.assocGet w₂.filesEnv.state.fds fd = none) := by
    rcases hWTop : (Model.withProxyModel rawOps cfg (fun p => pure (.ok p.port))).run (w₀, {}) with ⟨wRes, w₂, tr₂⟩
    have hWRun : StateT.run (Model.withProxyModel rawOps cfg (fun p => pure (.ok p.port))) (w₀, {}) = (wRes, (w₂, tr₂)) := hWTop
    clear hWTop
    dsimp only
    unfold Model.withProxyModel at hWRun
    cases hValCfg : Model.validateConfig cfg with
    | error _ =>
      rw [hValCfg] at hWRun
      dsimp only [stateT_pure_run] at hWRun
      injection hWRun with _ hwt; injection hwt with hwe hte
      subst hwe; subst hte
      dsimp only [rawOps, realBridgeTarget, mkSyncRawOps]
      rw [stateT_bind_run, stateT_get_run]
      dsimp only [stateT_pure_run]
      exact ⟨⟨hWf₀, rfl⟩, fun _ hm => nomatch hm⟩
    | ok vc =>
      rw [hValCfg] at hWRun
      obtain ⟨startRes, wS, trS, hStart, hWRun⟩ := stateT_bind_eq hWRun
      dsimp only [rawOps, realBridgeTarget, mkSyncRawOps] at hStart
      obtain ⟨crRes, wL, trL, hRCr, hStart⟩ := stateT_bind_eq hStart
      have hCr := healthy_createListener_instrumented_laws sys hRef vc w₀ {} hWf₀
      have hRCr' : (createListener (instrumentSysOps sys) vc).run (w₀, {}) = (crRes, (wL, trL)) := hRCr
      rw [hRCr'] at hCr; clear hRCr hRCr'
      dsimp only at hCr
      rcases hCr with ⟨hWfL, hTblL, _, _, _, hNdL, hCrMatch⟩
      cases crRes with
      | error err =>
        dsimp only [stateT_pure_run] at hStart hCrMatch
        injection hStart with hsr hwt; injection hwt with hwe hte
        subst hsr; subst hwe; subst hte
        dsimp only [stateT_pure_run] at hWRun
        injection hWRun with _ hwt2; injection hwt2 with hwe2 hte2
        subst hwe2; subst hte2
        refine ⟨⟨hWfL, ?_⟩, fun fd hm => ?_⟩
        · dsimp only [rawOps, realBridgeTarget, mkSyncRawOps]
          rw [stateT_bind_run, stateT_get_run]
          dsimp only [stateT_pure_run]
          rw [hTblL]
        · rcases hCrMatch.2 hNd₀ fd hm with hEmpty | hCl
          · cases hEmpty
          · exact hCl
      | ok quad =>
        rcases quad with ⟨lfd', wakeR', wakeW', bp'⟩
        dsimp only at hStart hCrMatch
        rw [stateT_bind_run, stateT_get_run] at hStart
        dsimp only at hStart
        rw [stateT_bind_run, stateT_set_run] at hStart
        dsimp only [stateT_pure_run] at hStart
        injection hStart with hsr hwt; injection hwt with hwe hte
        subst hsr; subst hwe; subst hte
        dsimp only at hWRun
        obtain ⟨⟨actRes, stopResW⟩, w2, tr2, hFinRun, hWRun⟩ := stateT_bind_eq hWRun
        rw [stateT_tryFinally_pure_run] at hFinRun
        have hStopW := healthy_stopActiveProxy_laws sys hRef wL trL bp' vc lfd' wakeR' wakeW' #[] #[] hWfL
        let hidW := freshSyncHandleId wL.proxyTable
        let actW : SyncProxyEntry Nat :=
          { handleId := hidW, port := bp', vcfg := vc, listenFd := lfd', wakeR := wakeR', wakeW := wakeW', slots := #[], events := #[] }
        let wActW : HealthySysWorld :=
          { wL with proxyTable := { nextHandleId := hidW + 1, entries := actW :: wL.proxyTable.entries } }
        let proxyW : RunningProxy := { handleId := hidW, port := bp' }
        dsimp only at hStopW
        rcases hRStopW : ((realBridgeTarget.mkRawOps (instrumentSysOps sys)).stopProxy proxyW).run (wActW, trL) with ⟨stopResW0, ⟨w20, tr20⟩⟩
        rw [hRStopW] at hStopW
        have hRStopW' : (rawOps.stopProxy proxyW).run (wActW, trL) = (stopResW0, (w20, tr20)) := hRStopW
        change (let (b, s') := StateT.run (rawOps.stopProxy proxyW) (wActW, trL); ((.ok bp', b), s')) = ((actRes, stopResW), (w2, tr2)) at hFinRun
        rw [show StateT.run (rawOps.stopProxy proxyW) (wActW, trL) = (stopResW0, (w20, tr20)) from hRStopW'] at hFinRun
        clear hRStopW hRStopW'
        dsimp only at hFinRun hStopW
        injection hFinRun with hpair hwt2; injection hpair with ha hs; injection hwt2 with hwe2 hte2
        subst ha; subst hs; subst hwe2; subst hte2
        rcases hStopW with ⟨hWf2, hEntries2, hOp2, ⟨finalEvsW, hOkStop, _⟩, hStopWNd⟩
        subst hOkStop
        dsimp only [stateT_pure_run] at hWRun
        injection hWRun with _ hwt3; injection hwt3 with hwe3 hte3
        subst hwe3; subst hte3
        obtain ⟨_, hAllClosed⟩ := hStopWNd (hNdL hNd₀)
        refine ⟨⟨hWf2, ?_⟩, fun fd hm => ?_⟩
        · dsimp only [rawOps, realBridgeTarget, mkSyncRawOps]
          rw [stateT_bind_run, stateT_get_run]
          dsimp only [stateT_pure_run]
          rw [hEntries2, hTblL]
        · rw [hOp2, hCrMatch.2.2] at hm
          simp only [Array.toList_push, List.nil_append] at hm
          apply hAllClosed fd
          simpa using hm
  rcases hRDbl : (rawOps.stopProxy proxy).run (w₁, tr₁) with ⟨dblRes, ⟨w₁d, tr₁d⟩⟩
  rw [hRDbl] at hDbl
  rcases hRWith : (Model.withProxyModel rawOps cfg (fun p => pure (.ok p.port))).run (w₀, {}) with ⟨_, ⟨w₂, tr₂⟩⟩
  rw [hRWith] at hWith
  exact ⟨⟨hWf₁, hCnt₁⟩, hFinalEvs, hClosed1, hDbl, hWith.1, hWith.2⟩

end LeanSwe.ConnectProxy.Proofs
