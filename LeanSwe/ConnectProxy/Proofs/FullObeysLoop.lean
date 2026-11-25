import Core.ConcOps
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.FullStep
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.SysBridge.Driver
import LeanSwe.ConnectProxy.Proofs.FullObeysHelpers

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys
open LeanSwe.ConnectProxy.SysBridge
open LeanSwe.ConnectProxy.SysBridge.Driver

/-- `enterClosingReply` preserves `inv`. -/
theorem sys_enterClosingReply_inv {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (limits : ProxyLimits) (slot : ClientSlot fdTy dnsJob)
    (cfd : fdTy) (code : Nat) (w : W) (hWf : inv w) :
    inv ((enterClosingReply sys limits slot cfd code).run w).2 := by
  unfold enterClosingReply
  try dsimp only
  apply state_bind_inv (sys_monoNowMs_inv hSys w hWf); intro _ w1 h1
  apply state_bind_inv (sys_flushBytesNonblock_inv hSys cfd _ MAX_CLOSING_STEPS 0 w1 h1); intro r w2 h2
  cases r with
  | none =>
    try dsimp only
    apply state_bind_inv (sys_closeFd_inv hSys cfd w2 h2); intro _ _ h3; exact h3
  | some sentOff =>
    try dsimp only
    by_cases hDone : sentOff ≥ (if (code == 403) = true then Relay.reply403Bytes
        else if (code == 503) = true then Relay.reply503Bytes else Relay.reply502Bytes).size
    · simp only [hDone, ↓reduceIte]
      apply state_bind_inv (sys_shutdownWrClean_inv hSys cfd 16 w2 h2); intro b w3 h3
      cases b
      · apply state_bind_inv (sys_closeFd_inv hSys cfd w3 h3); intro _ _ h4; exact h4
      · exact h3
    · simp only [hDone, ↓reduceIte]; exact h2

/-- `startNextConnectAux` preserves `inv` and `EventsValid`. -/
theorem sys_startNextConnectAux_pres {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (limits : ProxyLimits)
    (slot : ClientSlot fdTy dnsJob) (events : Array ConnectEvent)
    (cfd : fdTy) (host : String) (port : UInt16) (cands : Array IpAddr) :
    ∀ (fuel candIdx : Nat) (lastErr? : Option Errno) (w : W),
      inv w → EventsValid events →
      SlotPres inv ((startNextConnectAux sys limits slot events cfd host port cands fuel candIdx lastErr?).run w)
  | 0, _, _, w, hWf, hEvs => by
    unfold startNextConnectAux
    try dsimp only
    apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 502 w hWf)
    intro _ _ h1
    exact ⟨h1, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩
  | fuel + 1, candIdx, lastErr?, w, hWf, hEvs => by
    unfold startNextConnectAux
    try dsimp only
    split
    · apply state_bind_slot_pres
        (retryEintr_inv inv (sys.net.socket _ .stream { nonblock := true, cloexec := true } 0)
          (hSys.netSocket _ .stream { nonblock := true, cloexec := true } 0) MAX_EINTR_RETRIES w hWf)
      intro r1 w1 h1
      cases r1 with
      | error e => exact sys_startNextConnectAux_pres hSys limits slot events cfd host port cands fuel (candIdx + 1) (some e) w1 h1 hEvs
      | ok ufd =>
        try dsimp only
        apply state_bind_slot_pres (hSys.netConnect ufd _ w1 h1)
        intro r2 w2 h2
        cases r2 with
        | ok _ =>
          try dsimp only
          unfold enterRelay
          exact ⟨h2, emitSlotEvent_eventsValid slot events _ hEvs (fun _ => rfl)⟩
        | error e =>
          try dsimp only
          split
          · apply state_bind_slot_pres (sys_monoNowMs_inv hSys w2 h2)
            intro _ _ h3; exact ⟨h3, hEvs⟩
          · apply state_bind_slot_pres (sys_closeFd_inv hSys ufd w2 h2)
            intro _ w3 h3
            exact sys_startNextConnectAux_pres hSys limits slot events cfd host port cands fuel (candIdx + 1) (some e) w3 h3 hEvs
    · apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 502 w hWf)
      intro _ _ h1
      exact ⟨h1, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩

/-- `handleResolveDecision` preserves `inv` and `EventsValid`. -/
theorem sys_handleResolveDecision_pres {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (limits : ProxyLimits)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (slot : ClientSlot fdTy dnsJob) (events : Array ConnectEvent)
    (cfd : fdTy) (host : String) (port : UInt16) (ips : Array IpAddr)
    (w : W) (hWf : inv w) (hEvs : EventsValid events) :
    SlotPres inv ((handleResolveDecision sys limits onResolved slot events cfd host port ips).run w) := by
  unfold handleResolveDecision
  cases onResolved host port ips with
  | deny reason =>
    try dsimp only
    apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 403 w hWf)
    intro _ _ h1
    exact ⟨h1, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩
  | dial primary fallbacks =>
    exact sys_startNextConnectAux_pres hSys limits slot events cfd host port (#[primary] ++ fallbacks) _ 0 none w hWf hEvs

/-- `handleCompleteHead` preserves `inv` and `EventsValid` whenever `startDns` does. -/
theorem sys_handleCompleteHead_pres {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fdTy dnsJob → Array ConnectEvent → fdTy → String → UInt16 →
      StateM W (ClientSlot fdTy dnsJob × Array ConnectEvent))
    (hStartDns : ∀ s evs c h p w, inv w → EventsValid evs →
      SlotPres inv ((startDns s evs c h p).run w))
    (slot : ClientSlot fdTy dnsJob) (events : Array ConnectEvent)
    (cfd : fdTy) (headBytes pipelined : ByteArray)
    (w : W) (hWf : inv w) (hEvs : EventsValid events) :
    SlotPres inv ((handleCompleteHead sys limits onHead onResolved startDns slot events cfd headBytes pipelined).run w) := by
  unfold handleCompleteHead
  cases onHead headBytes with
  | deny host? port? reason =>
    try dsimp only
    apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 403 w hWf)
    intro _ _ h1
    exact ⟨h1, emitSlotEvent_eventsValid { slot with pipelined := pipelined } events _ hEvs (fun h => nomatch h)⟩
  | needResolve host port litIp? =>
    cases litIp? with
    | some litIp =>
      exact sys_handleResolveDecision_pres hSys limits onResolved _ events cfd host port #[litIp] w hWf hEvs
    | none =>
      exact hStartDns _ events cfd host port w hWf hEvs

/-- `stepHandshakeReadAux` preserves `inv` and `EventsValid` whenever `startDns` does. -/
theorem sys_stepHandshakeReadAux_pres {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (limits : ProxyLimits)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (startDns : ClientSlot fdTy dnsJob → Array ConnectEvent → fdTy → String → UInt16 →
      StateM W (ClientSlot fdTy dnsJob × Array ConnectEvent))
    (hStartDns : ∀ s evs c h p w, inv w → EventsValid evs →
      SlotPres inv ((startDns s evs c h p).run w))
    (slot : ClientSlot fdTy dnsJob) (events : Array ConnectEvent)
    (cfd : fdTy) (deadlineMs : Nat) :
    ∀ (fuel : Nat) (headBuf : ByteArray) (w : W), inv w → EventsValid events →
      SlotPres inv ((stepHandshakeReadAux sys limits onHead onResolved startDns slot events cfd deadlineMs fuel headBuf).run w)
  | 0, _, _, hWf, hEvs => ⟨hWf, hEvs⟩
  | fuel + 1, headBuf, w, hWf, hEvs => by
    unfold stepHandshakeReadAux
    try dsimp only
    split
    · apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 403 w hWf)
      intro _ _ h1
      exact ⟨h1, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩
    · apply state_bind_slot_pres (hSys.netRecvfrom cfd _ { dontwait := true } w hWf)
      intro r w1 h1
      cases r with
      | ok chunk =>
        try dsimp only
        split
        · apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 403 w1 h1)
          intro _ _ h2
          exact ⟨h2, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩
        · cases findCrlfCrlf _ _ with
          | some _ =>
            exact sys_handleCompleteHead_pres hSys limits onHead onResolved startDns hStartDns slot events cfd _ _ w1 h1 hEvs
          | none =>
            have hNext : ∀ nb : ByteArray,
                SlotPres inv ((if nb.size ≥ limits.maxHeaderBytes then (do
                  let slot2 ← enterClosingReply sys limits
                    (emitSlotEvent slot events { outcome := .denied, reason := some "request head exceeds maxHeaderBytes" }).1 cfd 403
                  pure (slot2, (emitSlotEvent slot events { outcome := .denied, reason := some "request head exceeds maxHeaderBytes" }).2))
                else stepHandshakeReadAux sys limits onHead onResolved startDns slot events cfd deadlineMs fuel nb).run w1) := by
              intro nb
              split
              · apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 403 w1 h1)
                intro _ _ h2
                exact ⟨h2, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩
              · exact sys_stepHandshakeReadAux_pres hSys limits onHead onResolved startDns hStartDns slot events cfd deadlineMs fuel nb w1 h1 hEvs
            exact hNext _
      | error e =>
        try dsimp only
        split
        · exact sys_stepHandshakeReadAux_pres hSys limits onHead onResolved startDns hStartDns slot events cfd deadlineMs fuel headBuf w1 h1 hEvs
        · split
          · exact ⟨h1, hEvs⟩
          · apply state_bind_slot_pres (sys_enterClosingReply_inv hSys limits _ cfd 403 w1 h1)
            intro _ _ h2
            exact ⟨h2, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩

/-- `stepConnecting` preserves `inv` and `EventsValid`. -/
theorem sys_stepConnecting_pres {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (limits : ProxyLimits)
    (slot : ClientSlot fdTy dnsJob) (events : Array ConnectEvent)
    (cfd ufd : fdTy) (host : String) (port : UInt16)
    (cands : Array IpAddr) (candIdx : Nat) (lastErr? : Option Errno) (dl : Nat)
    (cRev uRev : Poll.PollEvents) (nowMs : Nat)
    (w : W) (hWf : inv w) (hEvs : EventsValid events) :
    SlotPres inv ((stepConnecting sys limits slot events cfd ufd host port cands candIdx lastErr? dl cRev uRev nowMs).run w) := by
  unfold stepConnecting
  try dsimp only
  split
  · apply state_bind_slot_pres (sys_closeFd_inv hSys ufd w hWf); intro _ w1 h1
    apply state_bind_slot_pres (sys_closeFd_inv hSys cfd w1 h1); intro _ _ h2
    exact ⟨h2, emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)⟩
  · split
    · apply state_bind_slot_pres
        (retryEintr_inv inv (sys.net.getsockopt ufd .error) (hSys.netGetsockopt ufd .error) MAX_EINTR_RETRIES w hWf)
      intro ro w1 h1
      have hStep : ∀ (soErr : Errno),
          SlotPres inv ((if (soErr == 0 && uRev.pollout && !uRev.pollerr && !uRev.pollnval) = true then
               pure (enterRelay slot events cfd ufd host port)
             else do
               sys.closeFd ufd
               startNextConnect sys limits slot events cfd host port cands candIdx
                 (some (if soErr != 0 then soErr else Errno.ECONNREFUSED))).run w1) := by
        intro soErr
        split
        · unfold enterRelay; exact ⟨h1, emitSlotEvent_eventsValid slot events _ hEvs (fun _ => rfl)⟩
        · apply state_bind_slot_pres (sys_closeFd_inv hSys ufd w1 h1); intro _ w2 h2
          exact sys_startNextConnectAux_pres hSys limits slot events cfd host port cands _ candIdx _ w2 h2 hEvs
      cases ro with
      | ok code => exact hStep code
      | error e => exact hStep e
    · split
      · apply state_bind_slot_pres (sys_closeFd_inv hSys ufd w hWf); intro _ w1 h1
        exact sys_startNextConnectAux_pres hSys limits slot events cfd host port cands _ candIdx _ w1 h1 hEvs
      · exact ⟨hWf, hEvs⟩

/-- `stepClosingReply` preserves `inv`. -/
theorem sys_stepClosingReply_inv {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (slot : ClientSlot fdTy dnsJob) (cfd? : Option fdTy)
    (rb : ByteArray) (roff : Nat) (sw : Bool) (dr dl : Nat)
    (cRev : Poll.PollEvents) (nowMs : Nat) (w : W) (hWf : inv w) :
    inv ((stepClosingReply sys slot cfd? rb roff sw dr dl cRev nowMs).run w).2 := by
  have hDrain : ∀ cfd fuel d w0, inv w0 → inv ((drainClosingClient sys.net cfd fuel d).run w0).2 := by
    intro cfd fuel
    induction fuel with
    | zero => intro _ _ hw; exact hw
    | succ f ih =>
      intro d w0 hw0; unfold drainClosingClient
      apply state_bind_inv (hSys.netRecvfrom cfd 1024 { dontwait := true } w0 hw0)
      intro r w1 h1
      cases r with
      | ok _ => (try dsimp only); split; exact h1; split; exact h1; exact ih _ w1 h1
      | error _ => (try dsimp only); split; exact ih d w1 h1; split <;> exact h1
  have hSend : ∀ cfd w0, inv w0 → inv ((closingSendStep sys.net cfd rb roff sw cRev).run w0).2 := by
    intro cfd w0 hw0; unfold closingSendStep
    try dsimp only
    split
    · split
      · exact hw0
      · split
        · apply state_bind_inv (sys_flushBytesNonblock_inv hSys cfd rb MAX_CLOSING_STEPS roff w0 hw0)
          intro r w1 h1
          cases r with
          | none => exact h1
          | some _ =>
            try dsimp only
            split
            · apply state_bind_inv (sys_shutdownWrClean_inv hSys cfd 16 w1 h1)
              intro b _ h2; cases b <;> exact h2
            · exact h1
        · exact hw0
    · exact hw0
  unfold stepClosingReply
  cases cfd? with
  | none => exact hWf
  | some cfd =>
    try dsimp only
    apply state_bind_inv (hSend cfd w hWf); intro o1 w1 h1
    cases o1 with
    | none =>
      try dsimp only
      apply state_bind_inv (sys_closeFd_inv hSys cfd w1 h1); intro _ _ h2; exact h2
    | some p =>
      rcases p with ⟨off1, shut1⟩
      try dsimp only
      have h2 : inv ((closingDrainStep sys.net cfd shut1 dr cRev).run w1).2 := by
        unfold closingDrainStep; (try dsimp only); split; exact hDrain cfd MAX_CLOSING_STEPS dr w1 h1; exact h1
      apply state_bind_inv h2; intro o2 w2 h3
      cases o2 with
      | none =>
        try dsimp only
        apply state_bind_inv (sys_closeFd_inv hSys cfd w2 h3); intro _ _ h4; exact h4
      | some _ =>
        try dsimp only
        split
        · apply state_bind_inv (sys_closeFd_inv hSys cfd w2 h3); intro _ _ h4; exact h4
        · exact h3

/-- `acceptNewClientsAux` preserves `inv`. -/
theorem sys_acceptNewClientsAux_inv {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (limits : ProxyLimits) (lfd : fdTy) (nowMs : Nat) :
    ∀ (fuel : Nat) (slots : Array (ClientSlot fdTy dnsJob)) (w : W),
      inv w → inv ((acceptNewClientsAux sys limits lfd nowMs fuel slots).run w).2
  | 0, _, _, hWf => hWf
  | fuel + 1, slots, w, hWf => by
    unfold acceptNewClientsAux
    try dsimp only
    split
    · exact hWf
    · apply state_bind_inv (hSys.netAccept4 lfd { nonblock := true, cloexec := true } w hWf)
      intro r w1 h1
      cases r with
      | ok _ => exact sys_acceptNewClientsAux_inv hSys limits lfd nowMs fuel _ w1 h1
      | error _ => (try dsimp only); split; exact sys_acceptNewClientsAux_inv hSys limits lfd nowMs fuel slots w1 h1; exact h1

/-- `teardownAllSlotsList` preserves `inv` and `EventsValid` whenever `cancelDns` preserves `inv`. -/
theorem sys_teardownAllSlotsList_pres {W fdTy dnsJob : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys)
    (cancelDns : dnsJob → StateM W Unit)
    (hCancel : ∀ j w, inv w → inv ((cancelDns j).run w).2) :
    ∀ (slots : List (ClientSlot fdTy dnsJob)) (events : Array ConnectEvent) (w : W),
      inv w → EventsValid events →
      EvsPres inv ((teardownAllSlotsList sys cancelDns slots events).run w)
  | [], _, _, hWf, hEvs => ⟨hWf, hEvs⟩
  | slot :: rest, events, w, hWf, hEvs => by
    unfold teardownAllSlotsList
    have hSlot : EvsPres inv ((teardownSlot sys cancelDns slot events).run w) := by
      unfold teardownSlot
      have hEv1 : EventsValid (match slot.target? with
          | some (h, p) => emitSlotEvent slot events { host := some h, port := some p, outcome := .failed, reason := some "proxy stopped" }
          | none => emitSlotEvent slot events { outcome := .failed, reason := some "proxy stopped" }).2 := by
        cases slot.target? with
        | none => exact emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)
        | some _ => exact emitSlotEvent_eventsValid slot events _ hEvs (fun h => nomatch h)
      cases slot.phase with
      | handshake cfd _ _ =>
        try dsimp only
        apply state_bind_evs_pres (sys_closeFd_inv hSys cfd w hWf); intro _ _ h1; exact ⟨h1, hEv1⟩
      | dns cfd _ _ job =>
        try dsimp only
        apply state_bind_evs_pres (hCancel job w hWf); intro _ w1 h1
        apply state_bind_evs_pres (sys_closeFd_inv hSys cfd w1 h1); intro _ _ h2; exact ⟨h2, hEv1⟩
      | connecting cfd ufd _ _ _ _ _ _ =>
        try dsimp only
        apply state_bind_evs_pres (sys_closeFd_inv hSys ufd w hWf); intro _ w1 h1
        apply state_bind_evs_pres (sys_closeFd_inv hSys cfd w1 h1); intro _ _ h2; exact ⟨h2, hEv1⟩
      | relay st =>
        try dsimp only
        apply state_bind_evs_pres (sys_closeRelayBoth_inv hSys st w hWf); intro _ _ h1; exact ⟨h1, hEv1⟩
      | closingReply cfd? _ _ _ _ _ =>
        try dsimp only
        apply state_bind_evs_pres (sys_closeOptFd_inv hSys cfd? w hWf); intro _ _ h1; exact ⟨h1, hEv1⟩
      | done => exact ⟨hWf, hEv1⟩
    apply state_bind_evs_pres_of hSlot
    intro evs1 w1 h1 hE1
    exact sys_teardownAllSlotsList_pres hSys cancelDns hCancel rest evs1 w1 h1 hE1

/-- Postcondition for `createListener`: preserves `inv`, non-empty error messages, valid bound port. -/
def CreateListenerPost {W fdTy : Type} (inv : W → Prop) (vcfg : ValidProxyConfig)
    (p : Except ProxyError (fdTy × fdTy × fdTy × UInt16) × W) : Prop :=
  inv p.2 ∧
  match p.1 with
  | .ok (_, _, _, bp) =>
    bp ≠ 0 ∧ (vcfg.config.listenPort ≠ 0 → bp = vcfg.config.listenPort)
  | .error err => err.message ≠ ""

/-- `createListener` preserves `inv`, guarantees non-empty error messages on `.error`, and guarantees
    `boundPort ≠ 0 ∧ (listenPort ≠ 0 → boundPort = listenPort)` on `.ok`. -/
theorem sys_createListener_laws {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (vcfg : ValidProxyConfig) (w : W) (hWf : inv w) :
    CreateListenerPost inv vcfg ((createListener sys vcfg).run w) := by
  let Q := CreateListenerPost (fdTy := fdTy) inv vcfg
  change Q ((createListener sys vcfg).run w)
  unfold createListener
  cases hVal : validateStartLimits vcfg with
  | error err =>
    have hMsg : err.message ≠ "" := by
      unfold validateStartLimits at hVal; dsimp only at hVal
      split at hVal
      · injection hVal with he; subst he; decide
      · cases hVal
    exact ⟨hWf, hMsg⟩
  | ok _ =>
    try dsimp only
    apply state_bind_post (Q := Q)
      (retryEintr_inv inv (sys.net.socket .inet .stream { nonblock := true, cloexec := true } 0)
        (hSys.netSocket .inet .stream { nonblock := true, cloexec := true } 0) MAX_EINTR_RETRIES w hWf)
    intro r1 w1 h1
    cases r1 with
    | error e => exact ⟨h1, (errnoToProxyError_laws vcfg.config.listenPort e).1⟩
    | ok lfd =>
      try dsimp only
      apply state_bind_post (Q := Q)
        (retryEintr_inv inv (sys.net.setsockopt lfd .reuseAddr 1) (hSys.netSetsockopt lfd .reuseAddr 1) MAX_EINTR_RETRIES w1 h1)
      intro r2 w2 h2
      cases r2 with
      | error e =>
        try dsimp only
        apply state_bind_post (Q := Q) (sys_closeFd_inv hSys lfd w2 h2)
        intro _ _ h3; exact ⟨h3, (errnoToProxyError_laws vcfg.config.listenPort e).1⟩
      | ok _ =>
        try dsimp only
        apply state_bind_post (Q := Q)
          (retryEintr_inv inv (sys.net.bind lfd _) (hSys.netBind lfd _) MAX_EINTR_RETRIES w2 h2)
        intro r3 w3 h3
        cases r3 with
        | error e =>
          try dsimp only
          apply state_bind_post (Q := Q) (sys_closeFd_inv hSys lfd w3 h3)
          intro _ _ h4; exact ⟨h4, (errnoToProxyError_laws vcfg.config.listenPort e).1⟩
        | ok _ =>
          try dsimp only
          apply state_bind_post (Q := Q)
            (retryEintr_inv inv (sys.net.listen lfd 128) (hSys.netListen lfd 128) MAX_EINTR_RETRIES w3 h3)
          intro r4 w4 h4
          cases r4 with
          | error e =>
            try dsimp only
            apply state_bind_post (Q := Q) (sys_closeFd_inv hSys lfd w4 h4)
            intro _ _ h5; exact ⟨h5, (errnoToProxyError_laws vcfg.config.listenPort e).1⟩
          | ok _ =>
            try dsimp only
            apply state_bind_post (Q := Q)
              (retryEintr_inv inv (sys.net.getsockname lfd) (hSys.netGetsockname lfd) MAX_EINTR_RETRIES w4 h4)
            intro r5 w5 h5
            cases r5 with
            | error e =>
              try dsimp only
              apply state_bind_post (Q := Q) (sys_closeFd_inv hSys lfd w5 h5)
              intro _ _ h6; exact ⟨h6, (errnoToProxyError_laws vcfg.config.listenPort e).1⟩
            | ok boundSa =>
              try dsimp only
              have hNone : Q ((do
                  sys.closeFd lfd
                  pure (Except.error (mapRawErrorPure (.otherError Errno.EINVAL "getsockname returned invalid loopback port")))).run w5) := by
                apply state_bind_post (Q := Q) (sys_closeFd_inv hSys lfd w5 h5)
                intro _ _ h6; exact ⟨h6, (mapRawErrorPure_laws (.otherError Errno.EINVAL "getsockname returned invalid loopback port")).1⟩
              cases boundSa with
              | ipv4 ip p =>
                try dsimp only
                by_cases hCond : (ip == Net.INADDR_LOOPBACK && p != 0 &&
                    (vcfg.config.listenPort == 0 || p == vcfg.config.listenPort)) = true
                · simp only [hCond, ↓reduceIte]
                  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hCond
                  apply state_bind_post (Q := Q)
                    (retryEintr_inv inv (sys.net.socketpair .unix .stream { nonblock := true, cloexec := true })
                      (hSys.netSocketpair .unix .stream { nonblock := true, cloexec := true }) MAX_EINTR_RETRIES w5 h5)
                  intro r6 w6 h6
                  cases r6 with
                  | error e =>
                    try dsimp only
                    apply state_bind_post (Q := Q) (sys_closeFd_inv hSys lfd w6 h6)
                    intro _ _ h7; exact ⟨h7, (errnoToProxyError_laws vcfg.config.listenPort e).1⟩
                  | ok _ => exact ⟨h6, hCond.1.2, fun hNe => hCond.2.resolve_left hNe⟩
                · simp only [hCond]
                  exact hNone
              | ipv6 _ _ _ _ _ => exact hNone
              | unix _ => exact hNone

end LeanSwe.ConnectProxy.Proofs
