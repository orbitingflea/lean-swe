import Core.ConcOps
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.FullStep
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge

/-- Audit event invariant preserved across all `ConnectProxy` transitions: `.allowed` events never carry a failure reason. -/
def EventsValid (evs : Array ConnectEvent) : Prop :=
  ∀ ev ∈ evs.toList, ev.outcome = .allowed → ev.reason = none

/-- `EventsValid` holds on the empty event array. -/
theorem eventsValid_empty : EventsValid #[] := by
  intro ev h; simp at h

/-- `emitSlotEvent` preserves `EventsValid` whenever the candidate event satisfies `ev.outcome = .allowed → ev.reason = none`. -/
theorem emitSlotEvent_eventsValid {fd dnsJob : Type}
    (slot : ClientSlot fd dnsJob) (events : Array ConnectEvent) (ev : ConnectEvent)
    (hEvs : EventsValid events) (hEv : ev.outcome = .allowed → ev.reason = none) :
    EventsValid (emitSlotEvent slot events ev).2 := by
  unfold emitSlotEvent
  try dsimp only
  split
  · exact hEvs
  · intro e hm
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hm
    rcases hm with hOld | rfl
    · exact hEvs e hOld
    · exact hEv

/-- Bind combinator for `StateM W` invariant preservation. -/
theorem state_bind_inv {W α β : Type} {inv : W → Prop}
    {act : StateM W α} {k : α → StateM W β} {w : W}
    (h1 : inv (act.run w).2)
    (h2 : ∀ a w1, inv w1 → inv ((k a).run w1).2) :
    inv ((act >>= k).run w).2 := by
  dsimp only [bind, StateT.bind, StateT.run, Id.run] at h1 ⊢
  cases h : act w with
  | mk a w1 =>
    rw [h] at h1
    exact h2 a w1 h1

/-- Combined state-invariant and `EventsValid` postcondition on `(γ × Array ConnectEvent) × W`. -/
def SlotPres {W γ : Type} (inv : W → Prop) (p : (γ × Array ConnectEvent) × W) : Prop :=
  inv p.2 ∧ EventsValid p.1.2

/-- Combined state-invariant and `EventsValid` postcondition on `Array ConnectEvent × W`. -/
def EvsPres {W : Type} (inv : W → Prop) (p : Array ConnectEvent × W) : Prop :=
  inv p.2 ∧ EventsValid p.1

/-- Bind combinator for `StateM W` postconditions where the first action preserves `inv`. -/
theorem state_bind_post {W α β : Type} {inv : W → Prop} {Q : β × W → Prop}
    {act : StateM W α} {k : α → StateM W β} {w : W}
    (h1 : inv (act.run w).2)
    (h2 : ∀ a w1, inv w1 → Q ((k a).run w1)) :
    Q ((act >>= k).run w) := by
  dsimp only [bind, StateT.bind, StateT.run, Id.run] at h1 ⊢
  cases h : act w with
  | mk a w1 =>
    rw [h] at h1
    exact h2 a w1 h1

/-- General bind combinator for `StateM W` postconditions threading an intermediate predicate `P`. -/
theorem state_bind_post_of {W α β : Type} {P : α × W → Prop} {Q : β × W → Prop}
    {act : StateM W α} {k : α → StateM W β} {w : W}
    (h1 : P (act.run w))
    (h2 : ∀ a w1, P (a, w1) → Q ((k a).run w1)) :
    Q ((act >>= k).run w) := by
  dsimp only [bind, StateT.bind, StateT.run, Id.run] at h1 ⊢
  cases h : act w with
  | mk a w1 =>
    rw [h] at h1
    exact h2 a w1 h1

/-- Bridge from a `let (a, w1) := act.run w; P a w1` hypothesis into `Q ((act >>= k).run w)`. -/
theorem state_bind_post_let {W α β : Type} {P : α → W → Prop} {Q : β × W → Prop}
    {act : StateM W α} {k : α → StateM W β} {w : W}
    (h1 : let (a, w1) := act.run w; P a w1)
    (h2 : ∀ a w1, P a w1 → Q ((k a).run w1)) :
    Q ((act >>= k).run w) := by
  dsimp only [bind, StateT.bind, StateT.run, Id.run] at h1 ⊢
  cases h : act w with
  | mk a w1 =>
    rw [h] at h1
    exact h2 a w1 h1

/-- Concrete bind combinator for `SlotPres inv` when `act` preserves `inv`. -/
theorem state_bind_slot_pres {W α γ : Type} {inv : W → Prop}
    {act : StateM W α} {k : α → StateM W (γ × Array ConnectEvent)} {w : W}
    (h1 : inv (act.run w).2)
    (h2 : ∀ a w1, inv w1 → SlotPres inv ((k a).run w1)) :
    SlotPres inv ((act >>= k).run w) :=
  state_bind_post (Q := SlotPres inv) h1 h2

/-- Concrete bind combinator for `SlotPres inv` when `act` returns `(γ₁ × Array ConnectEvent)`. -/
theorem state_bind_slot_pres_of {W γ₁ γ₂ : Type} {inv : W → Prop}
    {act : StateM W (γ₁ × Array ConnectEvent)} {k : γ₁ × Array ConnectEvent → StateM W (γ₂ × Array ConnectEvent)} {w : W}
    (h1 : SlotPres inv (act.run w))
    (h2 : ∀ s1 evs1 w1, inv w1 → EventsValid evs1 → SlotPres inv ((k (s1, evs1)).run w1)) :
    SlotPres inv ((act >>= k).run w) :=
  state_bind_post_of (P := SlotPres inv) (Q := SlotPres inv) h1
    (fun ⟨s1, evs1⟩ w1 hp => h2 s1 evs1 w1 hp.1 hp.2)

/-- Concrete bind combinator for `EvsPres inv` when `act` preserves `inv`. -/
theorem state_bind_evs_pres {W α : Type} {inv : W → Prop}
    {act : StateM W α} {k : α → StateM W (Array ConnectEvent)} {w : W}
    (h1 : inv (act.run w).2)
    (h2 : ∀ a w1, inv w1 → EvsPres inv ((k a).run w1)) :
    EvsPres inv ((act >>= k).run w) :=
  state_bind_post (Q := EvsPres inv) h1 h2

/-- Concrete bind combinator for `EvsPres inv` when `act` returns `Array ConnectEvent`. -/
theorem state_bind_evs_pres_of {W : Type} {inv : W → Prop}
    {act : StateM W (Array ConnectEvent)} {k : Array ConnectEvent → StateM W (Array ConnectEvent)} {w : W}
    (h1 : EvsPres inv (act.run w))
    (h2 : ∀ evs1 w1, inv w1 → EventsValid evs1 → EvsPres inv ((k evs1).run w1)) :
    EvsPres inv ((act >>= k).run w) :=
  state_bind_post_of (P := EvsPres inv) (Q := EvsPres inv) h1
    (fun evs1 w1 hp => h2 evs1 w1 hp.1 hp.2)

/-- `tryFinally'` on `StateM W` preserves `inv` when both body and finalizer preserve `inv`. -/
theorem state_tryFinally'_inv {W α β : Type} {inv : W → Prop}
    {body : StateM W α} {fin : Option α → StateM W β} {w : W}
    (hBody : inv (body.run w).2)
    (hFin : ∀ oa w1, inv w1 → inv ((fin oa).run w1).2) :
    inv ((tryFinally' body fin).run w).2 := by
  dsimp only [tryFinally', MonadFinally.tryFinally', bind, pure, StateT.run, Id.run] at hBody ⊢
  cases h : body w with
  | mk a w1 =>
    rw [h] at hBody
    dsimp only
    have hF := hFin (some a) w1 hBody
    dsimp only [StateT.run, Id.run] at hF
    cases hf : fin (some a) w1 with
    | mk _ w2 =>
      rw [hf] at hF
      exact hF

/-- `tryFinally'` on `StateM W` propagates a postcondition from body and finalizer. -/
theorem state_tryFinally'_post {W α β : Type} {P : α × W → Prop} {Q : (α × β) × W → Prop}
    {body : StateM W α} {fin : Option α → StateM W β} {w : W}
    (hBody : P (body.run w))
    (hFin : ∀ a w1, P (a, w1) → Q ((a, ((fin (some a)).run w1).1), ((fin (some a)).run w1).2)) :
    Q ((tryFinally' body fin).run w) := by
  dsimp only [tryFinally', MonadFinally.tryFinally', bind, pure, StateT.run, Id.run] at hBody ⊢
  cases h : body w with
  | mk a w1 =>
    rw [h] at hBody
    dsimp only
    have hF := hFin a w1 hBody
    dsimp only [StateT.run, Id.run] at hF
    cases hf : fin (some a) w1 with
    | mk b w2 =>
      rw [hf] at hF
      exact hF

/-- Minimal invariant-preservation bundle for a `CProxySysOpsM (StateM W) fdTy` with respect to `inv : W → Prop`. -/
structure SysPreservesInv {W fdTy : Type} (inv : W → Prop) (sys : CProxySysOpsM (StateM W) fdTy) : Prop where
  /-- `files.close` preserves `inv`. -/
  filesClose : ∀ d w, inv w → inv ((sys.files.close d).run w).2
  /-- `net.socket` preserves `inv`. -/
  netSocket : ∀ dom st fl p w, inv w → inv ((sys.net.socket dom st fl p).run w).2
  /-- `net.socketpair` preserves `inv`. -/
  netSocketpair : ∀ dom st fl w, inv w → inv ((sys.net.socketpair dom st fl).run w).2
  /-- `net.bind` preserves `inv`. -/
  netBind : ∀ h sa w, inv w → inv ((sys.net.bind h sa).run w).2
  /-- `net.listen` preserves `inv`. -/
  netListen : ∀ h bl w, inv w → inv ((sys.net.listen h bl).run w).2
  /-- `net.accept4` preserves `inv`. -/
  netAccept4 : ∀ h fl w, inv w → inv ((sys.net.accept4 h fl).run w).2
  /-- `net.connect` preserves `inv`. -/
  netConnect : ∀ h sa w, inv w → inv ((sys.net.connect h sa).run w).2
  /-- `net.getsockopt` preserves `inv`. -/
  netGetsockopt : ∀ h opt w, inv w → inv ((sys.net.getsockopt h opt).run w).2
  /-- `net.setsockopt` preserves `inv`. -/
  netSetsockopt : ∀ h opt v w, inv w → inv ((sys.net.setsockopt h opt v).run w).2
  /-- `net.getsockname` preserves `inv`. -/
  netGetsockname : ∀ h w, inv w → inv ((sys.net.getsockname h).run w).2
  /-- `net.recvfrom` preserves `inv`. -/
  netRecvfrom : ∀ h n fl w, inv w → inv ((sys.net.recvfrom h n fl).run w).2
  /-- `net.sendto` preserves `inv`. -/
  netSendto : ∀ h bs fl w, inv w → inv ((sys.net.sendto h bs fl).run w).2
  /-- `net.shutdown` preserves `inv`. -/
  netShutdown : ∀ h how w, inv w → inv ((sys.net.shutdown h how).run w).2
  /-- `poll.ppoll` preserves `inv`. -/
  pollPpoll : ∀ fds to? w, inv w → inv ((sys.poll.ppoll fds to?).run w).2
  /-- `dns.getaddrinfo` preserves `inv`. -/
  dnsGetaddrinfo : ∀ host hints w, inv w → inv ((sys.dns.getaddrinfo host hints).run w).2
  /-- `timeRand.clock_gettime` preserves `inv`. -/
  timeGettime : ∀ clk w, inv w → inv ((sys.timeRand.clock_gettime clk).run w).2
  /-- `timeRand.clock_nanosleep` preserves `inv`. -/
  timeNanosleep : ∀ clk ab ts w, inv w → inv ((sys.timeRand.clock_nanosleep clk ab ts).run w).2

/-- Any `raw : FullSysOpsM (StateM W)` obeying `allowedFullRawStep` preserves `fun w => (proj w).wf = true`. -/
theorem sysPreservesInv_of_obeysStep {W : Type}
    (proj : W → HealthySysWorld) (raw : FullSysOpsM (StateM W))
    (hRaw : Core.ObeysStep proj fullWorldWf (execFullRawStep raw) allowedFullRawStep) :
    SysPreservesInv (fun w => (proj w).wf = true) raw := by
  have stepWf : ∀ (req : FullRawReq) (w : W), (proj w).wf = true →
      (proj ((execFullRawStep raw req).run w).2).wf = true :=
    fun req w hWf => (hRaw w req hWf).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d w hWf
    have h := stepWf (.filesClose d) w hWf
    dsimp only [execFullRawStep, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.files.close d w with | mk _ w' => rw [hR] at h; exact h
  · intro dom st fl p w hWf
    have h := stepWf (.net (.socket dom st fl p)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.socket dom st fl p w with | mk _ w' => rw [hR] at h; exact h
  · intro dom st fl w hWf
    have h := stepWf (.net (.socketpair dom st fl)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.socketpair dom st fl w with | mk _ w' => rw [hR] at h; exact h
  · intro fd sa w hWf
    have h := stepWf (.net (.bind fd sa)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.bind fd sa w with | mk _ w' => rw [hR] at h; exact h
  · intro fd bl w hWf
    have h := stepWf (.net (.listen fd bl)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.listen fd bl w with | mk _ w' => rw [hR] at h; exact h
  · intro fd fl w hWf
    have h := stepWf (.net (.accept4 fd fl)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.accept4 fd fl w with | mk _ w' => rw [hR] at h; exact h
  · intro fd sa w hWf
    have h := stepWf (.net (.connect fd sa)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.connect fd sa w with | mk _ w' => rw [hR] at h; exact h
  · intro fd opt w hWf
    have h := stepWf (.net (.getsockopt fd opt)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.getsockopt fd opt w with | mk _ w' => rw [hR] at h; exact h
  · intro fd opt v w hWf
    have h := stepWf (.net (.setsockopt fd opt v)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.setsockopt fd opt v w with | mk _ w' => rw [hR] at h; exact h
  · intro fd w hWf
    have h := stepWf (.net (.getsockname fd)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.getsockname fd w with | mk _ w' => rw [hR] at h; exact h
  · intro fd n fl w hWf
    have h := stepWf (.net (.recvfrom fd n fl)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.recvfrom fd n fl w with | mk _ w' => rw [hR] at h; exact h
  · intro fd bs fl w hWf
    have h := stepWf (.net (.sendto fd bs fl)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.sendto fd bs fl w with | mk _ w' => rw [hR] at h; exact h
  · intro fd how w hWf
    have h := stepWf (.net (.shutdown fd how)) w hWf
    dsimp only [execFullRawStep, execRawFdNetReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.net.shutdown fd how w with | mk _ w' => rw [hR] at h; exact h
  · intro fds to? w hWf
    have h := stepWf (.pollPpoll fds to?) w hWf
    dsimp only [execFullRawStep, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.poll.ppoll fds to? w with | mk _ w' => rw [hR] at h; exact h
  · intro host hints w hWf
    have h := stepWf (.dns { host := host, hints := hints }) w hWf
    dsimp only [execFullRawStep, Dns.execDnsReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.dns.getaddrinfo host hints w with | mk _ w' => rw [hR] at h; exact h
  · intro clk w hWf
    have h := stepWf (.timeRand (.clock_gettime clk)) w hWf
    dsimp only [execFullRawStep, TimeRand.execTimeRandReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.timeRand.clock_gettime clk w with | mk _ w' => rw [hR] at h; exact h
  · intro clk ab ts w hWf
    have h := stepWf (.timeRand (.clock_nanosleep clk ab ts)) w hWf
    dsimp only [execFullRawStep, TimeRand.execTimeRandReq, Functor.map, StateT.map, bind, StateT.bind, pure, StateT.pure, StateT.run, Id.run] at h ⊢
    cases hR : raw.timeRand.clock_nanosleep clk ab ts w with | mk _ w' => rw [hR] at h; exact h

/-- `retryEintr` preserves any state invariant `inv` preserved by the underlying action. -/
theorem retryEintr_inv {W α : Type} (inv : W → Prop)
    (act : StateM W (Except Errno α))
    (hAct : ∀ w, inv w → inv (act.run w).2) :
    ∀ (fuel : Nat) (w : W), inv w → inv ((retryEintr act fuel).run w).2
  | 0, w, h => hAct w h
  | fuel + 1, w, h => by
    unfold retryEintr
    try dsimp only
    apply state_bind_inv (hAct w h)
    intro r w1 h1
    cases r with
    | ok _ => exact h1
    | error e =>
      try dsimp only
      split
      · exact retryEintr_inv inv act hAct fuel w1 h1
      · exact h1

/-- `closeSysFdAux` preserves `inv`. -/
theorem sys_closeSysFdAux_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (d : fdTy) :
    ∀ (fuel : Nat) (w : W), inv w → inv ((closeSysFdAux sys d fuel).run w).2
  | 0, w, hWf => by
    unfold closeSysFdAux
    try dsimp only
    apply state_bind_inv (hSys.filesClose d w hWf)
    intro _ _ h1; exact h1
  | fuel + 1, w, hWf => by
    unfold closeSysFdAux
    try dsimp only
    apply state_bind_inv (hSys.filesClose d w hWf)
    intro r w1 h1
    cases r with
    | ok _ => exact h1
    | error _ =>
      try dsimp only
      split
      · (try dsimp only); apply state_bind_inv (hSys.timeNanosleep .monotonic false { sec := 0, nsec := 100000 } w1 h1)
        intro _ w2 h2
        exact sys_closeSysFdAux_inv hSys d fuel w2 h2
      · exact h1

/-- `CProxySysOpsM.closeFd` preserves `inv`. -/
theorem sys_closeFd_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (d : fdTy) (w : W) (hWf : inv w) :
    inv ((sys.closeFd d).run w).2 :=
  sys_closeSysFdAux_inv hSys d 64 w hWf

/-- `monoNowMs` preserves `inv`. -/
theorem sys_monoNowMs_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (w : W) (hWf : inv w) :
    inv ((monoNowMs sys).run w).2 := by
  unfold monoNowMs
  try dsimp only
  apply state_bind_inv
    (retryEintr_inv inv (sys.timeRand.clock_gettime .monotonic) (hSys.timeGettime .monotonic) MAX_EINTR_RETRIES w hWf)
  intro r _ h1; cases r <;> exact h1

/-- `drainWakeSocket` preserves `inv`. -/
theorem sys_drainWakeSocket_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (wakeR : fdTy) :
    ∀ (fuel : Nat) (w : W), inv w → inv ((drainWakeSocket sys.net wakeR fuel).run w).2
  | 0, _, hWf => hWf
  | fuel + 1, w, hWf => by
    unfold drainWakeSocket
    try dsimp only
    apply state_bind_inv (hSys.netRecvfrom wakeR 256 { dontwait := true } w hWf)
    intro r w1 h1
    cases r with
    | ok _ => (try dsimp only); split; exact h1; exact sys_drainWakeSocket_inv hSys wakeR fuel w1 h1
    | error _ => (try dsimp only); split; exact sys_drainWakeSocket_inv hSys wakeR fuel w1 h1; exact h1

/-- `NetRelay.flushBytesNonblock` preserves `inv`. -/
theorem sys_flushBytesNonblock_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (fd : fdTy) (bs : ByteArray) :
    ∀ (fuel off : Nat) (w : W), inv w → inv ((NetRelay.flushBytesNonblock sys.net fd bs fuel off).run w).2
  | 0, _, _, hWf => hWf
  | fuel + 1, off, w, hWf => by
    unfold NetRelay.flushBytesNonblock NetRelay.Internal.flushBytesNonblock
    try dsimp only
    split
    · exact hWf
    · (try dsimp only); apply state_bind_inv (hSys.netSendto fd _ { nosignal := true, dontwait := true } w hWf)
      intro r w1 h1
      cases r with
      | ok _ => (try dsimp only); split; exact h1; exact sys_flushBytesNonblock_inv hSys fd bs fuel _ w1 h1
      | error _ => (try dsimp only); split; exact sys_flushBytesNonblock_inv hSys fd bs fuel off w1 h1; split <;> exact h1

/-- `NetRelay.shutdownWrClean` preserves `inv`. -/
theorem sys_shutdownWrClean_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (fd : fdTy) :
    ∀ (fuel : Nat) (w : W), inv w → inv ((NetRelay.shutdownWrClean sys.net fd fuel).run w).2
  | 0, _, hWf => hWf
  | fuel + 1, w, hWf => by
    unfold NetRelay.shutdownWrClean NetRelay.Internal.shutdownWrClean
    try dsimp only
    apply state_bind_inv (hSys.netShutdown fd .wr w hWf)
    intro r w1 h1
    cases r with
    | ok _ => exact h1
    | error _ => (try dsimp only); split; exact sys_shutdownWrClean_inv hSys fd fuel w1 h1; split <;> exact h1

/-- `NetRelay.drainDeadPeerRx` preserves `inv`. -/
theorem sys_drainDeadPeerRx_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (fd : fdTy) :
    ∀ (fuel : Nat) (w : W), inv w → inv ((NetRelay.drainDeadPeerRx sys.net fd fuel).run w).2
  | 0, _, hWf => hWf
  | fuel + 1, w, hWf => by
    unfold NetRelay.drainDeadPeerRx NetRelay.Internal.drainDeadPeerRx
    try dsimp only
    apply state_bind_inv (hSys.netRecvfrom fd 4096 { dontwait := true } w hWf)
    intro r w1 h1
    cases r with
    | ok _ => (try dsimp only); split; exact h1; exact sys_drainDeadPeerRx_inv hSys fd fuel w1 h1
    | error _ => (try dsimp only); split; exact sys_drainDeadPeerRx_inv hSys fd fuel w1 h1; split <;> exact h1

/-- `NetRelay.recvIntoRing` preserves `inv`. -/
theorem sys_recvIntoRing_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (fd : fdTy) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : W), inv w → inv ((NetRelay.recvIntoRing sys.net fd fuel rb).run w).2
  | 0, _, _, hWf => hWf
  | fuel + 1, rb, w, hWf => by
    unfold NetRelay.recvIntoRing NetRelay.Internal.recvIntoRing
    try dsimp only
    split
    · exact hWf
    · (try dsimp only); apply state_bind_inv (hSys.netRecvfrom fd _ { dontwait := true } w hWf)
      intro r w1 h1
      cases r with
      | ok _ => (try dsimp only); split; exact h1; exact sys_recvIntoRing_inv hSys fd fuel _ w1 h1
      | error _ => (try dsimp only); split; exact sys_recvIntoRing_inv hSys fd fuel rb w1 h1; split; exact h1; split <;> exact h1

/-- `NetRelay.flushRingNonblock` preserves `inv`. -/
theorem sys_flushRingNonblock_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (fd : fdTy) :
    ∀ (fuel : Nat) (rb : RingBuf) (w : W), inv w → inv ((NetRelay.flushRingNonblock sys.net fd fuel rb).run w).2
  | 0, _, _, hWf => hWf
  | fuel + 1, rb, w, hWf => by
    unfold NetRelay.flushRingNonblock NetRelay.Internal.flushRingNonblock
    try dsimp only
    split
    · exact hWf
    · (try dsimp only); apply state_bind_inv (hSys.netSendto fd _ { nosignal := true, dontwait := true } w hWf)
      intro r w1 h1
      cases r with
      | ok _ => (try dsimp only); split; exact h1; exact sys_flushRingNonblock_inv hSys fd fuel _ w1 h1
      | error _ => (try dsimp only); split; exact sys_flushRingNonblock_inv hSys fd fuel rb w1 h1; split <;> exact h1

/-- `NetRelay.closeOptFd sys.closeFd` preserves `inv`. -/
theorem sys_closeOptFd_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (optFd : Option fdTy) (w : W) (hWf : inv w) :
    inv ((NetRelay.closeOptFd sys.closeFd optFd).run w).2 := by
  cases optFd with
  | none => exact hWf
  | some d => exact sys_closeFd_inv hSys d w hWf

/-- `Relay.closeRelayBoth sys.closeFd` preserves `inv`. -/
theorem sys_closeRelayBoth_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (st : RelayState fdTy) (w : W) (hWf : inv w) :
    inv ((Relay.closeRelayBoth sys.closeFd st).run w).2 := by
  unfold Relay.closeRelayBoth
  try dsimp only
  apply state_bind_inv (sys_closeOptFd_inv hSys st.clientFd? w hWf)
  intro _ w1 h1
  apply state_bind_inv (sys_closeOptFd_inv hSys st.upstreamFd? w1 h1)
  intro _ _ h2; exact h2

/-- `Relay.stepBidirectionalRelay` preserves `inv`. -/
theorem sys_stepBidirectionalRelay_inv {W fdTy : Type} {inv : W → Prop} {sys : CProxySysOpsM (StateM W) fdTy}
    (hSys : SysPreservesInv inv sys) (st0 : RelayState fdTy)
    (cRev uRev : Poll.PollEvents) (w : W) (hWf : inv w) :
    inv ((Relay.stepBidirectionalRelay sys.net sys.closeFd st0 cRev uRev).run w).2 := by
  have hP1 : ∀ st w0, inv w0 → inv ((stepRelayPrefix sys.net st uRev).run w0).2 := by
    intro st w0 hw0; unfold stepRelayPrefix
    try dsimp only
    split
    · cases st.upstreamFd? with
      | none => exact hw0
      | some ufd =>
        try dsimp only
        apply state_bind_inv (sys_flushBytesNonblock_inv hSys ufd st.pendingPrefix MAX_RELAY_IO_STEPS st.pendingOff w0 hw0)
        intro r _ h1; cases r with | none => exact h1 | some _ => (try dsimp only); split <;> exact h1
    · exact hw0
  have hP2 : ∀ st w0, inv w0 → inv ((stepRelayClientRx sys.net st cRev).run w0).2 := by
    intro st w0 hw0; unfold stepRelayClientRx
    try dsimp only
    split
    · cases st.clientFd? with
      | none => split; exact hw0; split <;> exact hw0
      | some cfd =>
        try dsimp only
        split
        · apply state_bind_inv (sys_drainDeadPeerRx_inv hSys cfd MAX_RELAY_IO_STEPS w0 hw0)
          intro _ _ h1; exact h1
        · split
          · apply state_bind_inv (sys_recvIntoRing_inv hSys cfd MAX_RELAY_IO_STEPS st.c2u w0 hw0)
            intro r _ h1; cases r <;> exact h1
          · exact hw0
    · exact hw0
  have hP3 : ∀ st w0, inv w0 → inv ((stepRelayUpstreamRx sys.net st uRev).run w0).2 := by
    intro st w0 hw0; unfold stepRelayUpstreamRx
    try dsimp only
    split
    · cases st.upstreamFd? with
      | none => exact hw0
      | some ufd =>
        try dsimp only
        apply state_bind_inv (sys_recvIntoRing_inv hSys ufd MAX_RELAY_IO_STEPS st.u2c w0 hw0)
        intro r _ h1; cases r <;> exact h1
    · exact hw0
  have hP4 : ∀ st w0, inv w0 → inv ((stepRelayUpstreamTx sys.net st uRev).run w0).2 := by
    intro st w0 hw0; unfold stepRelayUpstreamTx
    try dsimp only
    split
    · cases st.upstreamFd? with
      | none => exact hw0
      | some ufd =>
        try dsimp only
        apply state_bind_inv (sys_flushRingNonblock_inv hSys ufd MAX_RELAY_IO_STEPS st.c2u w0 hw0)
        intro r _ h1; cases r <;> exact h1
    · exact hw0
  have hP5 : ∀ st w0, inv w0 → inv ((stepRelayClientTx sys.net st cRev).run w0).2 := by
    intro st w0 hw0; unfold stepRelayClientTx
    try dsimp only
    split
    · cases st.clientFd? with
      | none => exact hw0
      | some cfd =>
        try dsimp only
        apply state_bind_inv (sys_flushRingNonblock_inv hSys cfd MAX_RELAY_IO_STEPS st.u2c w0 hw0)
        intro r _ h1; cases r with | none => (try dsimp only); split <;> exact h1 | some _ => exact h1
    · exact hw0
  have hP6 : ∀ st w0, inv w0 → inv ((stepRelayShutdownUpstream sys.net st).run w0).2 := by
    intro st w0 hw0; unfold stepRelayShutdownUpstream
    try dsimp only
    split
    · cases st.upstreamFd? with
      | none => exact hw0
      | some ufd =>
        try dsimp only
        apply state_bind_inv (sys_shutdownWrClean_inv hSys ufd MAX_RELAY_IO_STEPS w0 hw0)
        intro b _ h1; cases b <;> exact h1
    · exact hw0
  have hP7 : ∀ st w0, inv w0 → inv ((stepRelayShutdownClient sys.net st).run w0).2 := by
    intro st w0 hw0; unfold stepRelayShutdownClient
    try dsimp only
    split
    · cases st.clientFd? with
      | none => exact hw0
      | some cfd =>
        try dsimp only
        apply state_bind_inv (sys_shutdownWrClean_inv hSys cfd MAX_RELAY_IO_STEPS w0 hw0)
        intro b _ h1; cases b <;> exact h1
    · exact hw0
  have hReap : ∀ opt b wA, inv wA → inv ((reapIdleFd sys.closeFd opt b).run wA).2 := by
    intro opt b wA hwA; unfold reapIdleFd
    cases opt with
    | none => exact hwA
    | some d =>
      cases b
      · exact hwA
      · dsimp only [↓reduceIte]
        apply state_bind_inv (sys_closeFd_inv hSys d wA hwA)
        intro _ _ h1; exact h1
  have hP8 : ∀ st w0, inv w0 → inv ((stepRelayReapIdle sys.closeFd st).run w0).2 := by
    intro st w0 hw0; unfold stepRelayReapIdle
    try dsimp only
    apply state_bind_inv (hReap st.clientFd? (st.cEof && st.cWrClosed) w0 hw0)
    intro _ w1 h1
    apply state_bind_inv (hReap st.upstreamFd? (st.uEof && st.uWrClosed) w1 h1)
    intro _ _ h2; exact h2
  unfold stepBidirectionalRelay
  try dsimp only
  split
  · exact sys_closeRelayBoth_inv hSys st0 w hWf
  · (try dsimp only); apply state_bind_inv (hP1 st0 w hWf); intro st1 w1 h1
    apply state_bind_inv (hP2 st1 w1 h1); intro o2 w2 h2
    cases o2 with
    | none => exact sys_closeRelayBoth_inv hSys st1 w2 h2
    | some st2 =>
      try dsimp only
      apply state_bind_inv (hP3 st2 w2 h2); intro o3 w3 h3
      cases o3 with
      | none => exact sys_closeRelayBoth_inv hSys st2 w3 h3
      | some st3 =>
        try dsimp only
        apply state_bind_inv (hP4 st3 w3 h3); intro st4 w4 h4
        apply state_bind_inv (hP5 st4 w4 h4); intro o5 w5 h5
        cases o5 with
        | none => exact sys_closeRelayBoth_inv hSys st4 w5 h5
        | some st5 =>
          try dsimp only
          apply state_bind_inv (hP6 st5 w5 h5); intro o6 w6 h6
          cases o6 with
          | none => exact sys_closeRelayBoth_inv hSys st5 w6 h6
          | some st6 =>
            try dsimp only
            apply state_bind_inv (hP7 st6 w6 h6); intro o7 w7 h7
            cases o7 with
            | none => exact sys_closeRelayBoth_inv hSys st6 w7 h7
            | some st7 => exact hP8 st7 w7 h7

end LeanSwe.ConnectProxy.Proofs
