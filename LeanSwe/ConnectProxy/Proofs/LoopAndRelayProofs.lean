import LeanSwe.ConnectProxy.Proofs.LoopHandshakeWf

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge


private theorem acceptNewClientsAux_pollOutcomes_eq {dnsJob : Type}
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (limits : ProxyLimits) (lfd nowMs : Nat) :
    ∀ (fuel : Nat) (slots : Array (ClientSlot Nat dnsJob)) (w : HealthySysWorld) (tr : SysAuditTrace Nat),
      ((acceptNewClientsAux (instrumentSysOps sys) limits lfd nowMs fuel slots).run (w, tr)).2.2.pollOutcomes = tr.pollOutcomes
  | 0, _, _, _ => rfl
  | fuel + 1, slots, w, tr => by
    unfold acceptNewClientsAux
    by_cases hCap : slots.size ≥ limits.maxConcurrentTunnels
    · simp only [hCap, ↓reduceIte]; rfl
    · simp only [hCap, ↓reduceIte]
      dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure, Id.run]
      rw [inst_net_accept4]
      rcases sys.net.accept4 lfd { nonblock := true, cloexec := true } w with ⟨r, w1⟩
      dsimp only
      cases r with
      | ok pair =>
        rcases pair with ⟨cfd, _⟩
        exact acceptNewClientsAux_pollOutcomes_eq sys limits lfd nowMs fuel _ w1 _
      | error e =>
        by_cases hEi : (e == Errno.EINTR) = true
        · simp only [hEi, ↓reduceIte]
          exact acceptNewClientsAux_pollOutcomes_eq sys limits lfd nowMs fuel slots w1 tr
        · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem maybeDrainWakeSocket_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (wakeR : Nat) (wakeRev : Poll.PollEvents)
    (w : HealthySysWorld) (tr : SysAuditTrace Nat) (hWf : w.wf = true) :
    let (_, (w', tr')) := (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR wakeRev).run (w, tr)
    w'.wf = true ∧ tr'.pollOutcomes = tr.pollOutcomes := by
  rcases hTop : (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR wakeRev).run (w, tr) with ⟨u, w', tr'⟩
  have hRun : StateT.run (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR wakeRev) (w, tr) = (u, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold maybeDrainWakeSocket at hRun
  split at hRun
  · have hD := drainWakeSocket_laws sys hRef wakeR 64 w tr hWf
    have hRun' : (drainWakeSocket (instrumentSysOps sys).net wakeR 64).run (w, tr) = (u, (w', tr')) := hRun
    rw [hRun'] at hD
    exact hD
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with _ hwt; injection hwt with hw ht; subst hw; subst ht
    exact ⟨hWf, rfl⟩

private theorem maybeAcceptNewClients_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (limits : ProxyLimits) (lfd nowMs : Nat) (listenRev : Poll.PollEvents)
    (slots : Array (ClientSlot Nat Unit))
    (w : HealthySysWorld) (tr : SysAuditTrace Nat)
    (hWf : w.wf = true)
    (hLe : slots.size ≤ limits.maxConcurrentTunnels)
    (hFin : ∀ s ∈ slots.toList, s.isFinished = false) :
    let (accSlots, (w', tr')) :=
      (maybeAcceptNewClients (instrumentSysOps sys) limits lfd nowMs listenRev slots).run (w, tr)
    w'.wf = true ∧
    tr'.pollOutcomes = tr.pollOutcomes ∧
    accSlots.size ≤ limits.maxConcurrentTunnels ∧
    (∀ s ∈ accSlots.toList, s.isFinished = false) := by
  rcases hTop : (maybeAcceptNewClients (instrumentSysOps sys) limits lfd nowMs listenRev slots).run (w, tr) with ⟨accSlots, w', tr'⟩
  have hRun : StateT.run (maybeAcceptNewClients (instrumentSysOps sys) limits lfd nowMs listenRev slots) (w, tr) = (accSlots, (w', tr')) := hTop
  clear hTop
  dsimp only
  unfold maybeAcceptNewClients at hRun
  split at hRun
  · unfold acceptNewClients at hRun
    have hA := healthy_acceptNewClientsAux_laws sys hRef limits lfd nowMs MAX_ACCEPT_BATCH slots w tr hWf hLe
    have hPoA := acceptNewClientsAux_pollOutcomes_eq sys limits lfd nowMs MAX_ACCEPT_BATCH slots w tr
    have hRun' : (acceptNewClientsAux (instrumentSysOps sys) limits lfd nowMs MAX_ACCEPT_BATCH slots).run (w, tr) = (accSlots, (w', tr')) := hRun
    rw [hRun'] at hA hPoA; dsimp only at hA hPoA
    refine ⟨hA.1, hPoA, hA.2.1, fun s hs => ?_⟩
    rcases hA.2.2.1 s hs with hOld | hNF
    · exact hFin s hOld
    · exact hNF
  · dsimp only [stateT_pure_run] at hRun
    injection hRun with hs hwt; injection hwt with hw ht; subst hs; subst hw; subst ht
    exact ⟨hWf, rfl, hLe, hFin⟩

/-- Relational laws for `SysBridge.pollAndStepTickSync`. -/
theorem healthy_pollAndStepTickSync_laws
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (cfg : ProxyConfig)
    (stopFlag : Bool)
    (wakeR lfd : Nat)
    (slots : Array (ClientSlot Nat Unit))
    (events : Array ConnectEvent)
    (w₀ : HealthySysWorld)
    (hWf₀ : w₀.wf = true)
    (hSlotsLe : slots.size ≤ cfg.limits.maxConcurrentTunnels) :
    let (tickOut, (wT, trT)) :=
      (pollAndStepTickSync (instrumentSysOps sys) cfg.limits
        (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
        stopFlag wakeR lfd slots events).run (w₀, {})
    wT.wf = true ∧
    (tickOut = .retryEintr ↔ trT.pollOutcomes = #[some Errno.EINTR]) ∧
    (stopFlag = true → tickOut = .retryEintr ∨ tickOut = .stopOrFatal) ∧
    (stopFlag = false ∧ trT.pollOutcomes = #[none] →
      ∃ nextSlots nextEvs, tickOut = .stepped nextSlots nextEvs) ∧
    (∀ nextSlots nextEvs, tickOut = .stepped nextSlots nextEvs →
      stopFlag = false ∧
      nextSlots.size ≤ cfg.limits.maxConcurrentTunnels ∧
      ∀ s ∈ nextSlots.toList, s.isFinished = false) := by
  rcases hTop : (pollAndStepTickSync (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    stopFlag wakeR lfd slots events).run (w₀, {}) with ⟨tickOut, wT, trT⟩
  have hRun : StateT.run (pollAndStepTickSync (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    stopFlag wakeR lfd slots events) (w₀, {}) = (tickOut, (wT, trT)) := hTop
  clear hTop
  dsimp only
  unfold pollAndStepTickSync pollAndStepTickM at hRun
  obtain ⟨now0, w1, tr1, hM0, hRun⟩ := stateT_bind_eq hRun
  obtain ⟨hWf1, hTr1⟩ := monoNowMs_of_eq sys hRef w₀ w1 {} tr1 now0 hWf₀ hM0; clear hM0
  subst hTr1
  have hAuxEq : ∀ (ls : List (ClientSlot Nat Unit)) (r : Array (Nat × Poll.PollEvents))
      (ix : Array (Option Nat × Option Nat)) (mr : Option Nat) (wx : HealthySysWorld) (trx : SysAuditTrace Nat),
      StateT.run (buildPollBatchAux (m := StateM (HealthySysWorld × SysAuditTrace Nat)) (fun () => pure false) now0 ls r ix mr) (wx, trx) =
      (Id.run (buildPollBatchAux (m := Id) (fun () => pure false) now0 ls r ix mr), (wx, trx)) := by
    intro ls
    induction ls with
    | nil => intro r ix mr wx trx; rfl
    | cons hd tl ih =>
      intro r ix mr wx trx
      unfold buildPollBatchAux
      cases hd.phase with
      | handshake c _ dl => exact ih _ _ _ wx trx
      | dns c _ _ _ => exact ih _ _ _ wx trx
      | connecting c u _ _ _ _ _ dl => exact ih _ _ _ wx trx
      | relay st => exact ih _ _ _ wx trx
      | closingReply c? _ _ _ _ dl => cases c? <;> exact ih _ _ _ wx trx
      | done => exact ih _ _ _ wx trx
  have hBatchEq :
      StateT.run
        (buildPollBatchM (m := StateM (HealthySysWorld × SysAuditTrace Nat))
          (fun () => pure false) wakeR lfd cfg.limits.maxConcurrentTunnels now0 slots)
        (w1, {}) =
      (buildPollBatchSync wakeR lfd cfg.limits.maxConcurrentTunnels now0 slots, (w1, {})) := by
    unfold buildPollBatchSync buildPollBatchM
    rw [stateT_bind_run, hAuxEq]
    rfl
  obtain ⟨bOut, w1b, tr1b, hBRun, hRun⟩ := stateT_bind_eq hRun
  rw [hBatchEq] at hBRun
  injection hBRun with hb hwt; injection hwt with hw1b ht1b
  subst hb; subst hw1b; subst ht1b
  let bRes := buildPollBatchSync wakeR lfd cfg.limits.maxConcurrentTunnels now0 slots
  dsimp only at hRun
  obtain ⟨pRes, w2, tr2, hPRun, hRun⟩ := stateT_bind_eq hRun
  have hPRun' : (instrumentSysOps sys).poll.ppoll bRes.1 bRes.2.2 (w1, {}) = (pRes, (w2, tr2)) := hPRun
  clear hPRun
  rw [inst_poll_ppoll] at hPRun'
  have hPoll := hRef.2.2.1 w1 (.ppoll bRes.1 bRes.2.2) ((wf_iff_parts w1).mp hWf1)
  dsimp only [Poll.execPollReq, Functor.map, StateT.map, StateT.run, bind, Bind.bind, pure, Pure.pure, Id.run] at hPoll
  rcases hSysP : sys.poll.ppoll bRes.1 bRes.2.2 w1 with ⟨pSys, w2Sys⟩
  rw [hSysP] at hPoll hPRun'; dsimp only at hPoll hPRun'
  injection hPRun' with hp hwt; injection hwt with hw2 ht2
  subst hp; subst hw2; subst ht2
  have hWf2 : w2Sys.wf = true := (wf_iff_parts w2Sys).mpr hPoll.2.1
  cases pSys with
  | error e =>
    dsimp only at hRun
    by_cases hEi : (e == Errno.EINTR) = true
    · simp only [hEi, ↓reduceIte, stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have heq := beq_iff_eq.mp hEi
      subst heq
      have hNotNone : (#[some Errno.EINTR] : Array (Option Errno)) ≠ #[none] := by
        intro hBad
        have hList := congrArg Array.toList hBad
        cases hList
      exact And.intro hWf2
        (And.intro (Iff.intro (fun _ => rfl) (fun _ => rfl))
          (And.intro (fun _ => Or.inl rfl)
            (And.intro (fun ⟨_, hBad⟩ => absurd hBad hNotNone)
              (fun _ _ hBad => nomatch hBad))))
    · simp only [Bool.eq_false_iff.mpr hEi, Bool.false_eq_true, ↓reduceIte, stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have hNe : e ≠ Errno.EINTR := fun hc => hEi (beq_iff_eq.mpr hc)
      have hNotNone : (#[some e] : Array (Option Errno)) ≠ #[none] := by
        intro hBad
        have hList := congrArg Array.toList hBad
        cases hList
      have hNotEintr : (#[some e] : Array (Option Errno)) ≠ #[some Errno.EINTR] := by
        intro hArr
        have hList := congrArg Array.toList hArr
        injection hList with hHead _
        injection hHead with he
        exact hNe he
      exact And.intro hWf2
        (And.intro (Iff.intro (fun hBad => nomatch hBad) (fun hArr => absurd hArr hNotEintr))
          (And.intro (fun _ => Or.inr rfl)
            (And.intro (fun ⟨_, hBad⟩ => absurd hBad hNotNone)
              (fun _ _ hBad => nomatch hBad))))
  | ok revents =>
    dsimp only at hRun
    obtain ⟨_, w3, tr3, hWRun, hRun⟩ := stateT_bind_eq hRun
    have hWake := maybeDrainWakeSocket_laws sys hRef wakeR (revents[0]?.getD {}) w2Sys { pollOutcomes := #[none] } hWf2
    have hWRun' : (maybeDrainWakeSocket (instrumentSysOps sys).net wakeR (revents[0]?.getD {})).run (w2Sys, { pollOutcomes := #[none] }) = ((), (w3, tr3)) := hWRun
    rw [hWRun'] at hWake; dsimp only at hWake
    obtain ⟨sfVal, w3b, tr3b, hSfRun, hRun⟩ := stateT_bind_eq hRun
    dsimp only [stateT_pure_run] at hSfRun
    injection hSfRun with hsf hwt; injection hwt with hw3b ht3b
    subst hsf; subst hw3b; subst ht3b
    cases stopFlag with
    | true =>
      simp only [↓reduceIte, stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have hNotEintr : tr3.pollOutcomes ≠ #[some Errno.EINTR] := by
        rw [hWake.2]
        intro hArr
        have hList := congrArg Array.toList hArr
        cases hList
      exact And.intro hWake.1
        (And.intro (Iff.intro (fun hBad => nomatch hBad) (fun hArr => absurd hArr hNotEintr))
          (And.intro (fun _ => Or.inr rfl)
            (And.intro (fun ⟨hBad, _⟩ => nomatch hBad)
              (fun _ _ hBad => nomatch hBad))))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hRun
      obtain ⟨now1, w4, tr4, hM1, hRun⟩ := stateT_bind_eq hRun
      obtain ⟨hWf4, hTr4⟩ := monoNowMs_of_eq sys hRef w3 w4 tr3 tr4 now1 hWake.1 hM1; clear hM1
      obtain ⟨⟨nextSlots, nextEvents⟩, w5, tr5, hSLRun, hRun⟩ := stateT_bind_eq hRun
      have hStepL := stepSlotsListM_laws sys hRef cfg bRes.2.1 revents now1 0 slots.toList
        (Array.emptyWithCapacity slots.size) events w4 tr4 hWf4 (fun _ hm => nomatch hm)
      have hSLRun' : (stepSlotsListM (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg)
          (Model.decideResolvedIps cfg.ipPolicy)
          (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
          (fun () => pure none) (fun () => pure ())
          bRes.2.1 revents now1 0 slots.toList
          (Array.emptyWithCapacity slots.size) events).run (w4, tr4) = ((nextSlots, nextEvents), (w5, tr5)) := hSLRun
      rw [hSLRun'] at hStepL; dsimp only at hStepL
      have hNextLe : nextSlots.size ≤ cfg.limits.maxConcurrentTunnels := by
        have hSz0 : (Array.emptyWithCapacity slots.size : Array (ClientSlot Nat Unit)).size = 0 := rfl
        have hLen : slots.toList.length = slots.size := Array.length_toList
        have hOut := hStepL.2.2.1
        omega
      obtain ⟨postDetached, w5b, tr5b, hPDRun, hRun⟩ := stateT_bind_eq hRun
      dsimp only [stateT_pure_run] at hPDRun
      injection hPDRun with hpd hwt; injection hwt with hw5b ht5b
      subst hpd; subst hw5b; subst ht5b
      dsimp only at hRun
      obtain ⟨acceptedSlots, w6, tr6, hARun, hRun⟩ := stateT_bind_eq hRun
      have hAcc := maybeAcceptNewClients_laws sys hRef cfg.limits lfd now1 (revents[1]?.getD {}) nextSlots w5 tr5 hStepL.1 hNextLe hStepL.2.2.2
      have hARun' : (maybeAcceptNewClients (instrumentSysOps sys) cfg.limits lfd now1 (revents[1]?.getD {}) nextSlots).run (w5, tr5) = (acceptedSlots, (w6, tr6)) := hARun
      rw [hARun'] at hAcc; dsimp only at hAcc
      dsimp only [stateT_pure_run] at hRun
      injection hRun with ho hwt; injection hwt with hw ht
      subst ho; subst hw; subst ht
      have hPoFinal : tr6.pollOutcomes = #[none] :=
        hAcc.2.1.trans (hStepL.2.1.trans ((congrArg _ hTr4).trans hWake.2))
      have hNotEintr : tr6.pollOutcomes ≠ #[some Errno.EINTR] := by
        rw [hPoFinal]
        intro hArr
        have hList := congrArg Array.toList hArr
        cases hList
      refine And.intro hAcc.1
        (And.intro (Iff.intro (fun hBad => nomatch hBad) (fun hArr => absurd hArr hNotEintr))
          (And.intro (fun hBad => nomatch hBad)
            (And.intro (fun _ => ⟨acceptedSlots, nextEvents, rfl⟩)
              (fun ns ne hEq => ?_))))
      injection hEq with hns _
      subst hns
      exact ⟨rfl, hAcc.2.2.1, hAcc.2.2.2⟩


end LeanSwe.ConnectProxy.Proofs
