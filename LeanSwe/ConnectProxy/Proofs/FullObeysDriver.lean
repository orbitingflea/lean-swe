import Core.ConcOps
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.FullStep
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.SysBridge.Driver
import LeanSwe.ConnectProxy.Proofs.FullObeysHelpers
import LeanSwe.ConnectProxy.Proofs.FullObeysLoop

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys
open LeanSwe.ConnectProxy.SysBridge
open LeanSwe.ConnectProxy.SysBridge.Driver

private theorem sysWithAcceptWatch_inv {W fdTy : Type} {inv : W → Prop}
    {sys : CProxySysOpsM (StateM W) fdTy} {conc : Core.ConcOpsM (StateM W)}
    (hSys : SysPreservesInv inv sys)
    (hWriteRef : ∀ {α : Type} (r : conc.Ref α) (v : α) (w : W), inv w → inv ((conc.writeRef r v).run w).2)
    (hitRef : conc.Ref Bool) :
    SysPreservesInv inv (sysWithAcceptWatch sys conc hitRef) := by
  refine ⟨hSys.filesClose, hSys.netSocket, hSys.netSocketpair, hSys.netBind, hSys.netListen, ?_,
    hSys.netConnect, hSys.netGetsockopt, hSys.netSetsockopt, hSys.netGetsockname,
    hSys.netRecvfrom, hSys.netSendto, hSys.netShutdown, hSys.pollPpoll, hSys.dnsGetaddrinfo,
    hSys.timeGettime, hSys.timeNanosleep⟩
  intro lfd fl w hWf
  unfold sysWithAcceptWatch
  try dsimp only
  apply state_bind_inv (hSys.netAccept4 lfd fl w hWf)
  intro r w1 h1
  cases r with
  | ok _ => exact h1
  | error _ =>
    try dsimp only
    split
    · apply state_bind_inv (hWriteRef hitRef true w1 h1); intro _ _ h2; exact h2
    · exact h1

private theorem buildPollBatchAux_inv {W fdTy dnsJob : Type} {inv : W → Prop}
    (pollDnsReady : dnsJob → StateM W Bool)
    (hReady : ∀ j w, inv w → inv ((pollDnsReady j).run w).2)
    (dnsWatchFd : dnsJob → StateM W (Option fdTy))
    (hWatch : ∀ j w, inv w → inv ((dnsWatchFd j).run w).2)
    (nowMs : Nat) :
    ∀ (slots : List (ClientSlot fdTy dnsJob))
      (reqs : Array (fdTy × Poll.PollEvents))
      (indices : Array (Option Nat × Option Nat))
      (minRem? : Option Nat) (w : W),
      inv w →
      inv ((buildPollBatchAux pollDnsReady nowMs slots reqs indices minRem? dnsWatchFd).run w).2
  | [], _, _, _, _, hWf => hWf
  | slot :: rest, reqs, indices, minRem?, w, hWf => by
    unfold buildPollBatchAux
    cases slot.phase with
    | handshake _ _ _ => exact buildPollBatchAux_inv pollDnsReady hReady dnsWatchFd hWatch nowMs rest _ _ _ w hWf
    | connecting _ _ _ _ _ _ _ _ => exact buildPollBatchAux_inv pollDnsReady hReady dnsWatchFd hWatch nowMs rest _ _ _ w hWf
    | relay _ => exact buildPollBatchAux_inv pollDnsReady hReady dnsWatchFd hWatch nowMs rest _ _ _ w hWf
    | closingReply cfd? _ _ _ _ _ =>
      cases cfd? <;> exact buildPollBatchAux_inv pollDnsReady hReady dnsWatchFd hWatch nowMs rest _ _ _ w hWf
    | done => exact buildPollBatchAux_inv pollDnsReady hReady dnsWatchFd hWatch nowMs rest _ _ _ w hWf
    | dns _ _ _ job =>
      try dsimp only
      apply state_bind_inv (hReady job w hWf); intro _ w1 h1
      apply state_bind_inv (hWatch job w1 h1); intro o w2 h2
      cases o <;> exact buildPollBatchAux_inv pollDnsReady hReady dnsWatchFd hWatch nowMs rest _ _ _ w2 h2

/-- Emergency `teardownTrackedM` preserves `inv` for any `sys` preserving `inv` and `conc` obeying
    `Core.ObeysConc inv conc`. -/
theorem driver_teardownTrackedM_inv {W fdTy : Type} {inv : W → Prop}
    {sys : CProxySysOpsM (StateM W) fdTy} {conc : Core.ConcOpsM (StateM W)}
    (hSys : SysPreservesInv inv sys) (hConc : Core.ObeysConc inv conc)
    (slotsRef : conc.Ref (Array (ClientSlot fdTy (ConcDnsJob fdTy conc.Ref conc.TaskHandle))))
    (dnsTasksRef : conc.Ref (Array (ConcDnsJob fdTy conc.Ref conc.TaskHandle)))
    (listenClosedFlag : conc.Ref Bool)
    (listenFd : fdTy) (w : W) (hw : inv w) :
    inv ((teardownTrackedM sys conc slotsRef dnsTasksRef listenClosedFlag listenFd).run w).2 := by
  rcases hConc with ⟨_, _, _, _, hModGetRef, _, _, _, _, _⟩
  have hModRef : ∀ {α : Type} (r : conc.Ref α) (f : α → α) (w0 : W),
      inv w0 → inv ((conc.modifyRef r f).run w0).2 :=
    fun r f w0 hw0 => (hModGetRef r (fun a => ((), f a)) w0 hw0).1
  have hCancelClose : ∀ dj w0, inv w0 → inv ((cancelAndCloseDnsM sys conc dj).run w0).2 := by
    intro dj w0 hw0; unfold cancelAndCloseDnsM
    apply state_bind_inv (hModRef dj.stateRef _ w0 hw0); intro _ w1 h1
    exact sys_closeFd_inv hSys dj.dnsR w1 h1
  have hCancelAll : ∀ (xs : List (ConcDnsJob fdTy conc.Ref conc.TaskHandle)) w0,
      inv w0 → inv ((cancelAllDnsM sys conc xs).run w0).2 := by
    intro xs; induction xs with
    | nil => intro _ h0; exact h0
    | cons dj rest ih =>
      intro w0 hw0; unfold cancelAllDnsM
      apply state_bind_inv (hCancelClose dj w0 hw0); intro _ w1 h1
      exact ih w1 h1
  unfold teardownTrackedM
  apply state_bind_inv (hModGetRef slotsRef _ w hw).1; intro slots w1 h1
  apply state_bind_inv (hModGetRef dnsTasksRef _ w1 h1).1; intro dnsTasks w2 h2
  apply state_bind_inv
    (sys_teardownAllSlotsList_pres hSys (cancelAndCloseDnsM sys conc) hCancelClose slots.toList #[] w2 h2 eventsValid_empty).1
  intro _ w3 h3
  apply state_bind_inv (hCancelAll dnsTasks.toList w3 h3); intro _ w4 h4
  apply state_bind_inv (hModGetRef listenClosedFlag _ w4 h4).1; intro already w5 h5
  cases already with
  | false => simp only [Bool.not_false, ↓reduceIte]; exact sys_closeFd_inv hSys listenFd w5 h5
  | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact h5

/-- Full `runProxyLoopM` invariant theorem: over ANY `sys` preserving `inv` and ANY `conc` obeying
    `Core.ObeysConc inv conc`, every reachable interleaving across all `fuel`, slots, detached DNS
    jobs, and `EventsValid` event logs preserves `inv` and `EventsValid`. -/
theorem driver_runProxyLoopM_pres {W fdTy : Type} {inv : W → Prop}
    {sys : CProxySysOpsM (StateM W) fdTy} {conc : Core.ConcOpsM (StateM W)}
    (hSys : SysPreservesInv inv sys) (hConc : Core.ObeysConc inv conc)
    (vcfg : ValidProxyConfig)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (stopFlag listenClosedFlag : conc.Ref Bool)
    (slotsRef : conc.Ref (Array (ClientSlot fdTy (ConcDnsJob fdTy conc.Ref conc.TaskHandle))))
    (dnsTasksRef : conc.Ref (Array (ConcDnsJob fdTy conc.Ref conc.TaskHandle)))
    (listenFd wakeR : fdTy) :
    ∀ (fuel : Nat)
      (slots : Array (ClientSlot fdTy (ConcDnsJob fdTy conc.Ref conc.TaskHandle)))
      (dnsTasks : Array (ConcDnsJob fdTy conc.Ref conc.TaskHandle))
      (backoffMs : Nat) (events : Array ConnectEvent) (w : W),
      inv w → EventsValid events →
      EvsPres inv ((runProxyLoopM sys conc vcfg onHead onResolved stopFlag listenClosedFlag
        slotsRef dnsTasksRef listenFd wakeR fuel slots dnsTasks backoffMs events).run w) := by
  rcases hConc with ⟨_, hMkRef, hReadRef, hWriteRef, hModGetRef, hSpawn, hHasFin, _, _, hTryCatch⟩
  have hModRef : ∀ {α : Type} (r : conc.Ref α) (f : α → α) (w : W),
      inv w → inv ((conc.modifyRef r f).run w).2 :=
    fun r f w hw => (hModGetRef r (fun a => ((), f a)) w hw).1
  have hIsDone : ∀ (dj : ConcDnsJob fdTy conc.Ref conc.TaskHandle) w, inv w → inv ((isDnsJobDoneM conc dj).run w).2 := by
    intro dj w hw; unfold isDnsJobDoneM
    apply state_bind_inv (hReadRef dj.stateRef w hw); intro _ w1 h1
    try dsimp only
    split; exact h1; exact hHasFin dj.task w1 h1
  have hCancelClose : ∀ dj w, inv w → inv ((cancelAndCloseDnsM sys conc dj).run w).2 := by
    intro dj w hw; unfold cancelAndCloseDnsM
    apply state_bind_inv (hModRef dj.stateRef _ w hw); intro _ w1 h1
    exact sys_closeFd_inv hSys dj.dnsR w1 h1
  have hPrune : ∀ (xs : List (ConcDnsJob fdTy conc.Ref conc.TaskHandle)) acc w,
      inv w → inv ((pruneFinishedDnsM sys conc xs acc).run w).2 := by
    intro xs
    induction xs with
    | nil => intro _ _ hw; exact hw
    | cons dj rest ih =>
      intro acc w hw; unfold pruneFinishedDnsM
      apply state_bind_inv (hIsDone dj w hw); intro b w1 h1
      cases b
      · exact ih _ w1 h1
      · try dsimp only
        apply state_bind_inv (sys_closeFd_inv hSys dj.dnsR w1 h1); intro _ w2 h2
        exact ih acc w2 h2
  have hCancelAll : ∀ (xs : List (ConcDnsJob fdTy conc.Ref conc.TaskHandle)) w,
      inv w → inv ((cancelAllDnsM sys conc xs).run w).2 := by
    intro xs
    induction xs with
    | nil => intro _ hw; exact hw
    | cons dj rest ih =>
      intro w hw; unfold cancelAllDnsM
      apply state_bind_inv (hCancelClose dj w hw); intro _ w1 h1
      exact ih w1 h1
  have hTeardown : ∀ slots dnsTasks evs w, inv w → EventsValid evs →
      EvsPres inv ((teardownLoopM sys conc slotsRef dnsTasksRef listenClosedFlag listenFd slots dnsTasks evs).run w) := by
    intro slots dnsTasks evs w hw hEvs; unfold teardownLoopM
    apply state_bind_evs_pres (hWriteRef slotsRef #[] w hw); intro _ w0 h0
    apply state_bind_evs_pres (hWriteRef dnsTasksRef #[] w0 h0); intro _ w0b h0b
    apply state_bind_evs_pres_of
      (sys_teardownAllSlotsList_pres hSys (cancelAndCloseDnsM sys conc) hCancelClose slots.toList evs w0b h0b hEvs)
    intro evs1 w1 h1 hE1
    apply state_bind_evs_pres (hCancelAll dnsTasks.toList w1 h1); intro _ w2 h2
    apply state_bind_evs_pres (hModGetRef listenClosedFlag _ w2 h2).1; intro already w3 h3
    cases already with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      apply state_bind_evs_pres (sys_closeFd_inv hSys listenFd w3 h3); intro _ _ h4
      exact ⟨h4, hE1⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h3, hE1⟩
  have hStartDns : ∀ slot evs cfd host port w, inv w → EventsValid evs →
      SlotPres inv ((startDnsM sys conc vcfg.config.limits slot evs cfd host port).run w) := by
    intro slot evs cfd host port w hw hEvs; unfold startDnsM
    apply state_bind_slot_pres
      (retryEintr_inv inv (sys.net.socketpair .unix .stream { nonblock := true, cloexec := true })
        (hSys.netSocketpair .unix .stream { nonblock := true, cloexec := true }) MAX_EINTR_RETRIES w hw)
    intro r1 w1 h1
    cases r1 with
    | error _ =>
      try dsimp only
      apply state_bind_slot_pres (sys_enterClosingReply_inv hSys vcfg.config.limits _ cfd 503 w1 h1)
      intro _ _ h2
      exact ⟨h2, emitSlotEvent_eventsValid slot evs _ hEvs (fun h => nomatch h)⟩
    | ok pair =>
      rcases pair with ⟨dnsR, dnsW⟩
      try dsimp only
      apply state_bind_slot_pres (hMkRef ({} : DnsJobState) w1 h1); intro jobRef w2 h2
      have hTaskBody : ∀ w0, inv w0 →
          let (_, w') := (do
            let _ ← tryFinally'
              (do
                match ← conc.tryCatchMsg (sys.dns.getaddrinfo host { family := .any, sockType := .stream }) with
                | .error msg =>
                  let reason := if msg.isEmpty then "dns resolution failed" else msg
                  conc.modifyRef jobRef fun st =>
                    if st.cancelled then st else { st with result? := some (.error reason) }
                | .ok res =>
                  let mapped : Except String (Array IpAddr) :=
                    match res with
                    | .error dnsErr =>
                      .error (if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message)
                    | .ok addrs =>
                      .ok (filterUnscopedDnsAddrs addrs)
                  conc.modifyRef jobRef fun st =>
                    if st.cancelled then st else { st with result? := some mapped })
              (fun _ => do
                conc.modifyRef jobRef fun st =>
                  let st1 :=
                    if st.cancelled || st.result?.isSome then st
                    else { st with result? := some (.error "dns resolution failed") }
                  { st1 with done := true }
                sys.closeFd dnsW)
            pure ()).run w0
          inv w' ∧ True := by
        intro w0 hw0
        have hBody1 : inv ((do
            match ← conc.tryCatchMsg (sys.dns.getaddrinfo host { family := .any, sockType := .stream }) with
            | .error msg =>
              let reason := if msg.isEmpty then "dns resolution failed" else msg
              conc.modifyRef jobRef fun st =>
                if st.cancelled then st else { st with result? := some (.error reason) }
            | .ok res =>
              let mapped : Except String (Array IpAddr) :=
                match res with
                | .error dnsErr =>
                  .error (if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message)
                | .ok addrs =>
                  .ok (filterUnscopedDnsAddrs addrs)
              conc.modifyRef jobRef fun st =>
                if st.cancelled then st else { st with result? := some mapped }).run w0).2 := by
          apply state_bind_inv
            (hTryCatch (sys.dns.getaddrinfo host { family := .any, sockType := .stream })
              (fun _ => True) (fun wa hwa => ⟨hSys.dnsGetaddrinfo host _ wa hwa, trivial⟩) w0 hw0).1
          intro rt wa ha
          cases rt with
          | error _ => exact hModRef jobRef _ wa ha
          | ok _ => exact hModRef jobRef _ wa ha
        have hFin1 : ∀ (_ : Option Unit) wb, inv wb →
            inv ((do
              conc.modifyRef jobRef fun st =>
                let st1 := if st.cancelled || st.result?.isSome then st else { st with result? := some (.error "dns resolution failed") }
                { st1 with done := true }
              sys.closeFd dnsW).run wb).2 := by
          intro _ wb hwb
          apply state_bind_inv (hModRef jobRef _ wb hwb); intro _ wc hc
          exact sys_closeFd_inv hSys dnsW wc hc
        have hInvAll : inv ((do
            let _ ← tryFinally'
              (do
                match ← conc.tryCatchMsg (sys.dns.getaddrinfo host { family := .any, sockType := .stream }) with
                | .error msg =>
                  let reason := if msg.isEmpty then "dns resolution failed" else msg
                  conc.modifyRef jobRef fun st =>
                    if st.cancelled then st else { st with result? := some (.error reason) }
                | .ok res =>
                  let mapped : Except String (Array IpAddr) :=
                    match res with
                    | .error dnsErr =>
                      .error (if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message)
                    | .ok addrs =>
                      .ok (filterUnscopedDnsAddrs addrs)
                  conc.modifyRef jobRef fun st =>
                    if st.cancelled then st else { st with result? := some mapped })
              (fun _ => do
                conc.modifyRef jobRef fun st =>
                  let st1 :=
                    if st.cancelled || st.result?.isSome then st
                    else { st with result? := some (.error "dns resolution failed") }
                  { st1 with done := true }
                sys.closeFd dnsW)
            pure ()).run w0).2 := by
          apply state_bind_inv (state_tryFinally'_inv hBody1 hFin1)
          intro _ _ hf; exact hf
        exact ⟨hInvAll, trivial⟩
      apply state_bind_slot_pres (hSpawn _ (fun _ => True) hTaskBody w2 h2).1
      intro _ _ h3; exact ⟨h3, hEvs⟩
  have hPollDns : ∀ dj w, inv w → inv ((pollDnsM sys conc dj).run w).2 := by
    intro dj w hw; unfold pollDnsM
    apply state_bind_inv (hReadRef dj.stateRef w hw); intro st w1 h1
    cases st.result? with
    | some _ =>
      try dsimp only
      apply state_bind_inv (sys_closeFd_inv hSys dj.dnsR w1 h1); intro _ _ h2; exact h2
    | none =>
      try dsimp only
      apply state_bind_inv (hHasFin dj.task w1 h1); intro _ w2 h2
      split
      · apply state_bind_inv (sys_closeFd_inv hSys dj.dnsR w2 h2); intro _ _ h3; exact h3
      · exact h2
  have hReapExtra : ∀ extraRevs idx (xs : List (ConcDnsJob fdTy conc.Ref conc.TaskHandle)) acc w,
      inv w → inv ((reapExtraDnsListM sys conc extraRevs idx xs acc).run w).2 := by
    intro extraRevs idx xs
    induction xs generalizing idx with
    | nil => intro _ _ hw; exact hw
    | cons dj rest ih =>
      intro acc w hw; unfold reapExtraDnsListM
      try dsimp only
      apply state_bind_inv (hIsDone dj w hw); intro _ w1 h1
      split
      · apply state_bind_inv (sys_closeFd_inv hSys dj.dnsR w1 h1); intro _ w2 h2
        exact ih (idx + 1) acc w2 h2
      · exact ih (idx + 1) _ w1 h1
  intro fuel
  induction fuel with
  | zero => exact fun slots dnsTasks _ events w hw hEvs => hTeardown slots dnsTasks events w hw hEvs
  | succ fuel' ih =>
    intro slots dnsTasks backoffMs events w hw hEvs
    unfold runProxyLoopM
    apply state_bind_evs_pres (hReadRef stopFlag w hw); intro stopB w1 h1
    cases stopB with
    | true => exact hTeardown slots dnsTasks events w1 h1 hEvs
    | false =>
      dsimp only [Bool.false_eq_true, ↓reduceIte]
      apply state_bind_evs_pres (hPrune dnsTasks.toList _ w1 h1); intro liveDns0 w2 h2
      apply state_bind_evs_pres (hWriteRef slotsRef slots w2 h2); intro _ w2b h2b
      apply state_bind_evs_pres (hWriteRef dnsTasksRef liveDns0 w2b h2b); intro _ w3 h3
      apply state_bind_evs_pres (hMkRef false w3 h3); intro hitRef w4 h4
      let tickSys := sysWithAcceptWatch sys conc hitRef
      have hTickSys : SysPreservesInv inv tickSys := sysWithAcceptWatch_inv hSys hWriteRef hitRef
      have hDetach : ∀ dj wa, inv wa → inv ((detachDnsM sys conc dnsTasksRef dj).run wa).2 := by
        intro dj wa hwa; unfold detachDnsM
        apply state_bind_inv (hModGetRef dj.stateRef _ wa hwa).1; intro _ wb hb
        apply state_bind_inv (hHasFin dj.task wb hb); intro _ wc hc
        split
        · exact sys_closeFd_inv hSys dj.dnsR wc hc
        · exact hModRef dnsTasksRef _ wc hc
      have hStepSlots : ∀ (idx : Nat) (sl : List (ClientSlot fdTy (ConcDnsJob fdTy conc.Ref conc.TaskHandle)))
          accS accE indices revs now1 wa, inv wa → EventsValid accE →
          SlotPres inv ((stepSlotsListM tickSys vcfg.config.limits onHead onResolved
            (startDnsM sys conc vcfg.config.limits) (pollDnsM sys conc) (detachDnsM sys conc dnsTasksRef)
            indices revs now1 idx sl accS accE true).run wa) := by
        intro idx sl
        induction sl generalizing idx with
        | nil => intro _ _ _ _ _ _ hwa hEa; exact ⟨hwa, hEa⟩
        | cons s rest ihS =>
          intro accS accE indices revs now1 wa hwa hEa
          unfold stepSlotsListM
          have hOne : ∀ (cRev uRev : Poll.PollEvents),
              SlotPres inv ((stepSlotM tickSys vcfg.config.limits onHead onResolved
                (startDnsM sys conc vcfg.config.limits) (pollDnsM sys conc) (detachDnsM sys conc dnsTasksRef)
                s accE cRev uRev now1 true).run wa) := by
            intro cRev uRev
            unfold stepSlotM
            cases s.phase with
            | handshake cfd hb dl =>
              unfold stepHandshake
              try dsimp only
              split
              · apply state_bind_slot_pres_of
                  (sys_stepHandshakeReadAux_pres hTickSys vcfg.config.limits onHead onResolved
                    (startDnsM sys conc vcfg.config.limits) hStartDns s accE cfd dl MAX_HANDSHAKE_STEPS hb wa hwa hEa)
                intro s1 e1 wb hb1 hE1
                cases s1.phase with
                | handshake cfd1 _ dl1 =>
                  try dsimp only
                  split
                  · apply state_bind_slot_pres (sys_enterClosingReply_inv hTickSys vcfg.config.limits _ cfd1 403 wb hb1)
                    intro _ _ hc
                    exact ⟨hc, emitSlotEvent_eventsValid s1 e1 _ hE1 (fun h => nomatch h)⟩
                  · exact ⟨hb1, hE1⟩
                | _ => exact ⟨hb1, hE1⟩
              · apply state_bind_slot_pres_of (show SlotPres inv ((pure (s, accE) : StateM W _).run wa) from ⟨hwa, hEa⟩)
                intro s1 e1 wb hb1 hE1
                cases s1.phase with
                | handshake cfd1 _ dl1 =>
                  try dsimp only
                  split
                  · apply state_bind_slot_pres (sys_enterClosingReply_inv hTickSys vcfg.config.limits _ cfd1 403 wb hb1)
                    intro _ _ hc
                    exact ⟨hc, emitSlotEvent_eventsValid s1 e1 _ hE1 (fun h => nomatch h)⟩
                  · exact ⟨hb1, hE1⟩
                | _ => exact ⟨hb1, hE1⟩
            | dns cfd host port dj =>
              try dsimp only
              split
              · apply state_bind_slot_pres (hDetach dj wa hwa); intro _ wb hb
                apply state_bind_slot_pres (sys_closeFd_inv hTickSys cfd wb hb); intro _ _ hc
                exact ⟨hc, emitSlotEvent_eventsValid s accE _ hEa (fun h => nomatch h)⟩
              · split
                · apply state_bind_slot_pres (hPollDns dj wa hwa); intro po wb hb
                  cases po with
                  | none => exact ⟨hb, hEa⟩
                  | some pr =>
                    cases pr with
                    | error _ =>
                      try dsimp only
                      apply state_bind_slot_pres (sys_enterClosingReply_inv hTickSys vcfg.config.limits _ cfd 502 wb hb)
                      intro _ _ hc
                      exact ⟨hc, emitSlotEvent_eventsValid s accE _ hEa (fun h => nomatch h)⟩
                    | ok ips =>
                      exact sys_handleResolveDecision_pres hTickSys vcfg.config.limits onResolved s accE cfd host port ips wb hb hEa
                · exact ⟨hwa, hEa⟩
            | connecting cfd ufd host port cands idx lastErr? dl =>
              exact sys_stepConnecting_pres hTickSys vcfg.config.limits s accE cfd ufd host port cands idx lastErr? dl _ _ now1 wa hwa hEa
            | relay st =>
              try dsimp only
              apply state_bind_slot_pres (sys_stepBidirectionalRelay_inv hTickSys st _ _ wa hwa); intro _ _ hb
              try dsimp only
              split <;> exact ⟨hb, hEa⟩
            | closingReply cfd? rb roff sw dr dl =>
              try dsimp only
              apply state_bind_slot_pres (sys_stepClosingReply_inv hTickSys s cfd? rb roff sw dr dl _ now1 wa hwa)
              intro _ _ hb; exact ⟨hb, hEa⟩
            | done => exact ⟨hwa, hEa⟩
          cases hIdx : indices[idx]?.getD (none, none) with
          | mk cIdx? uIdx? =>
            try dsimp only
            apply state_bind_slot_pres_of (hOne _ _); intro s1 e1 wb hb1 hE1
            exact ihS (idx + 1) _ e1 indices revs now1 wb hb1 hE1
      let QTick : PollTickOutcome fdTy (ConcDnsJob fdTy conc.Ref conc.TaskHandle) × W → Prop :=
        fun p => inv p.2 ∧ match p.1 with | .stepped _ evs' => EventsValid evs' | _ => True
      have hTick : ∀ (curBackoff : Nat) (getDetached : StateM W Nat)
          (extraFds : Array fdTy) (onExtra : Array Poll.PollEvents → StateM W Unit),
          (∀ w0, inv w0 → inv (getDetached.run w0).2) →
          (∀ evs w0, inv w0 → inv ((onExtra evs).run w0).2) →
          QTick ((pollAndStepTickM tickSys vcfg.config.limits onHead onResolved
            (conc.readRef stopFlag) (fun _ => pure false)
            (startDnsM sys conc vcfg.config.limits) (pollDnsM sys conc) (detachDnsM sys conc dnsTasksRef)
            wakeR listenFd slots events liveDns0.size curBackoff getDetached
            (fun dj => pure (some dj.dnsR)) true extraFds onExtra).run w4) := by
        intro curBackoff getDetached extraFds onExtra hDet hEx
        unfold pollAndStepTickM
        apply state_bind_post (Q := QTick) (sys_monoNowMs_inv hTickSys w4 h4); intro now0 wa ha
        have hBatch : inv ((buildPollBatchM (m := StateM W) (fun _ => pure false) wakeR listenFd
            vcfg.config.limits.maxConcurrentTunnels now0 slots liveDns0.size curBackoff
            (fun dj => pure (some dj.dnsR))).run wa).2 := by
          unfold buildPollBatchM
          try dsimp only
          apply state_bind_inv
            (buildPollBatchAux_inv (fun _ => pure false) (fun _ _ h => h)
              (fun dj => pure (some dj.dnsR)) (fun _ _ h => h) now0 slots.toList _ _ _ wa ha)
          intro _ _ hb; exact hb
        apply state_bind_post (Q := QTick) hBatch
        intro batch wb hb
        rcases batch with ⟨reqs, indices, minRem?⟩
        try dsimp only
        apply state_bind_post (Q := QTick) (hTickSys.pollPpoll _ _ wb hb); intro rp wc hc
        cases rp with
        | error _ => (try dsimp only); split <;> exact ⟨hc, trivial⟩
        | ok revs =>
          try dsimp only
          have hDr : inv ((maybeDrainWakeSocket tickSys.net wakeR (revs[0]?.getD {})).run wc).2 := by
            unfold maybeDrainWakeSocket; (try dsimp only); split; exact sys_drainWakeSocket_inv hTickSys wakeR 64 wc hc; exact hc
          apply state_bind_post (Q := QTick) hDr; intro _ wd hd
          apply state_bind_post (Q := QTick) (hReadRef stopFlag wd hd); intro stB we he
          cases stB with
          | true => exact ⟨he, trivial⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            split
            · apply state_bind_post (Q := QTick) (hEx _ we he); intro _ wf hf
              apply state_bind_post (Q := QTick) (sys_monoNowMs_inv hTickSys wf hf); intro now1 wg hg
              apply state_bind_post_of (P := SlotPres inv) (Q := QTick)
                (hStepSlots 0 slots.toList (Array.emptyWithCapacity slots.size) events indices revs now1 wg hg hEvs)
              intro pSl wh hh
              rcases pSl with ⟨nextSlots, nextEvents⟩
              try dsimp only
              apply state_bind_post (Q := QTick) (hDet wh hh.1); intro _ wi hi
              have hAcc : ∀ lim, inv ((maybeAcceptNewClients tickSys lim listenFd now1 (revs[1]?.getD {}) nextSlots).run wi).2 := by
                intro lim; unfold maybeAcceptNewClients acceptNewClients; (try dsimp only)
                split; exact sys_acceptNewClientsAux_inv hTickSys lim listenFd now1 MAX_ACCEPT_BATCH nextSlots wi hi; exact hi
              apply state_bind_post (Q := QTick) (hAcc _); intro _ _ hj
              exact ⟨hj, hh.2⟩
            · apply state_bind_post (Q := QTick) (sys_monoNowMs_inv hTickSys we he); intro now1 wg hg
              apply state_bind_post_of (P := SlotPres inv) (Q := QTick)
                (hStepSlots 0 slots.toList (Array.emptyWithCapacity slots.size) events indices revs now1 wg hg hEvs)
              intro pSl wh hh
              rcases pSl with ⟨nextSlots, nextEvents⟩
              try dsimp only
              apply state_bind_post (Q := QTick) (hDet wh hh.1); intro _ wi hi
              have hAcc : ∀ lim, inv ((maybeAcceptNewClients tickSys lim listenFd now1 (revs[1]?.getD {}) nextSlots).run wi).2 := by
                intro lim; unfold maybeAcceptNewClients acceptNewClients; (try dsimp only)
                split; exact sys_acceptNewClientsAux_inv hTickSys lim listenFd now1 MAX_ACCEPT_BATCH nextSlots wi hi; exact hi
              apply state_bind_post (Q := QTick) (hAcc _); intro _ _ hj
              exact ⟨hj, hh.2⟩
      have hDetArg : ∀ w0, inv w0 → inv ((do
          let cur ← conc.readRef dnsTasksRef
          let pruned ← pruneFinishedDnsM sys conc cur.toList (Array.emptyWithCapacity cur.size)
          conc.writeRef dnsTasksRef pruned
          return pruned.size).run w0).2 := by
        intro w0 hw0
        apply state_bind_inv (hReadRef dnsTasksRef w0 hw0); intro cur wi hi
        apply state_bind_inv (hPrune cur.toList _ wi hi); intro pr wj hj
        apply state_bind_inv (hWriteRef dnsTasksRef pr wj hj); intro _ _ hk; exact hk
      have hExArg : ∀ extraRevs w0, inv w0 → inv ((do
          let kept ← reapExtraDnsListM sys conc extraRevs 0 liveDns0.toList (Array.emptyWithCapacity liveDns0.size)
          conc.writeRef dnsTasksRef kept).run w0).2 := by
        intro extraRevs w0 hw0
        apply state_bind_inv (hReapExtra extraRevs 0 liveDns0.toList _ w0 hw0); intro kept wf hf
        exact hWriteRef dnsTasksRef kept wf hf
      apply state_bind_post_of (P := QTick) (Q := EvsPres inv) (hTick _ _ _ _ hDetArg hExArg)
      intro tickOut w5 h5
      cases tickOut with
      | retryEintr =>
        try dsimp only
        apply state_bind_evs_pres (hReadRef dnsTasksRef w5 h5.1); intro curT w6 h6
        exact ih slots curT _ events w6 h6 hEvs
      | stopOrFatal =>
        try dsimp only
        apply state_bind_evs_pres (hReadRef dnsTasksRef w5 h5.1); intro curT w6 h6
        exact hTeardown slots curT events w6 h6 hEvs
      | stepped acceptedSlots nextEvents =>
        try dsimp only
        apply state_bind_evs_pres (hWriteRef slotsRef acceptedSlots w5 h5.1); intro _ w5b h5b
        apply state_bind_evs_pres (hReadRef dnsTasksRef w5b h5b); intro curT w6 h6
        apply state_bind_evs_pres (hPrune curT.toList _ w6 h6); intro nextDns w7 h7
        apply state_bind_evs_pres (hWriteRef dnsTasksRef nextDns w7 h7); intro _ w7b h7b
        apply state_bind_evs_pres (hReadRef hitRef w7b h7b); intro _ w8 h8
        apply state_bind_evs_pres (sys_monoNowMs_inv hSys w8 h8); intro _ w9 h9
        exact ih acceptedSlots nextDns _ nextEvents w9 h9 h5.2

end LeanSwe.ConnectProxy.Proofs
