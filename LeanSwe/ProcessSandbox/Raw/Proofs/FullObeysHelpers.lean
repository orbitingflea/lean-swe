import Core.ConcOps
import LeanSwe.NetRelay.Interface
import LeanSwe.ProcessSandbox.Raw.Model.FullStep
import LeanSwe.ProcessSandbox.Raw.SysBridge.Forwarder
import LeanSwe.ProcessSandbox.Raw.SysBridge.Driver
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepBase
import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesTableHelpers

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Forwarder
open LeanSwe.ProcessSandbox.Raw.SysBridge.Driver

/-- Predicate stating that `act : StateM W α` preserves `fullWorldWf (projRaw w) = true`
    and leaves `projCell w` unchanged. -/
def SysFramePres {W C α : Type} (projRaw : W → HealthyRawSysWorld) (projCell : W → C)
    (act : StateM W α) : Prop :=
  ∀ w : W, fullWorldWf (projRaw w) = true →
    let w' := (act.run w).2
    fullWorldWf (projRaw w') = true ∧ projCell w' = projCell w

/-- `rawHostWorldWf` on `mapFullToRawWorld sys tbl` implies `fullWorldWf sys = true`. -/
theorem rawHostWorldWf_mapFullToRawWorld_wf {sys : HealthyRawSysWorld} {tbl : RawTableState}
    (hWf : rawHostWorldWf (mapFullToRawWorld sys tbl) = true) :
    fullWorldWf sys = true := by
  unfold mapFullToRawWorld at hWf
  unfold fullWorldWf
  split at hWf
  · assumption
  · simp [rawHostWorldWf] at hWf

/-- Any `SysFramePres` action preserves `mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))`. -/
theorem preservesProj_of_sysFramePres {W : Type} {Ref TaskH : Type → Type} {α : Type}
    {projRaw : W → HealthyRawSysWorld} {projCell : W → HostCellState Ref TaskH}
    {act : StateM W α} (hAct : SysFramePres projRaw projCell act) :
    PreservesProj (fun w => mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w))) act := by
  intro w hWf
  have hSysWf : fullWorldWf (projRaw w) = true := rawHostWorldWf_mapFullToRawWorld_wf hWf
  have ⟨hSysWf', hCellEq⟩ := hAct w hSysWf
  unfold mapFullToRawWorld
  have hw1 : (projRaw w).wf = true := hSysWf
  have hw2 : (projRaw (act.run w).2).wf = true := hSysWf'
  simp [hw1, hw2, hCellEq]

/-- `pure` satisfies `SysFramePres`. -/
theorem sysFramePres_pure {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    (a : α) : SysFramePres projRaw projCell (pure a : StateM W α) :=
  fun _ hWf => ⟨hWf, rfl⟩

/-- `>>=` preserves `SysFramePres`. -/
theorem sysFramePres_bind {W C α β : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {ma : StateM W α} {k : α → StateM W β}
    (ha : SysFramePres projRaw projCell ma) (hk : ∀ a, SysFramePres projRaw projCell (k a)) :
    SysFramePres projRaw projCell (ma >>= k) := by
  intro w hWf
  have ⟨hWf1, hC1⟩ := ha w hWf
  have ⟨hWf2, hC2⟩ := hk (ma.run w).1 (ma.run w).2 hWf1
  simp only [stateM_bind_run]
  exact ⟨hWf2, hC2.trans hC1⟩

/-- `if` preserves `SysFramePres`. -/
theorem sysFramePres_ite {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {c : Prop} [Decidable c] {t e : StateM W α}
    (ht : SysFramePres projRaw projCell t) (he : SysFramePres projRaw projCell e) :
    SysFramePres projRaw projCell (if c then t else e) := by
  by_cases hc : c <;> simp [hc, ht, he]

/-- `retryEintr` preserves `SysFramePres`. -/
theorem sysFramePres_retryEintr {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {act : StateM W (Except Errno α)} (hAct : SysFramePres projRaw projCell act) :
    ∀ fuel, SysFramePres projRaw projCell (retryEintr act fuel)
  | 0 => hAct
  | fuel + 1 => by
    unfold retryEintr
    refine sysFramePres_bind hAct fun r => ?_
    cases r with
    | ok _ => exact sysFramePres_pure _
    | error _ => exact sysFramePres_ite (sysFramePres_retryEintr hAct fuel) (sysFramePres_pure _)

/-- `List.forIn` preserves `SysFramePres`. -/
theorem sysFramePres_forIn_list {W C α β : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    (body : α → β → StateM W (ForInStep β))
    (hBody : ∀ x b, SysFramePres projRaw projCell (body x b)) :
    ∀ (xs : List α) (b : β), SysFramePres projRaw projCell (forIn xs b body)
  | [], b => sysFramePres_pure b
  | x :: rest, b => by
    intro w hWf
    rw [List.forIn_cons]
    refine sysFramePres_bind (hBody x b) (fun st => ?_) w hWf
    cases st with
    | done b' => exact sysFramePres_pure b'
    | yield b' => exact sysFramePres_forIn_list body hBody rest b'

/-- `Array.forIn` preserves `SysFramePres`. -/
theorem sysFramePres_forIn_array {W C α β : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    (body : α → β → StateM W (ForInStep β))
    (hBody : ∀ x b, SysFramePres projRaw projCell (body x b))
    (arr : Array α) (b : β) :
    SysFramePres projRaw projCell (forIn arr b body) := by
  rw [← Array.forIn_toList]
  exact sysFramePres_forIn_list body hBody arr.toList b

/-- Extract `SysFramePres` for `conc.tryCatchMsg act` from `ObeysConcFrame`. -/
theorem sysFramePres_tryCatchMsg {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {conc : Core.ConcOpsM (StateM W)}
    (hConc : Core.ObeysConcFrame (fun w => fullWorldWf (projRaw w) = true)
      (fun w₁ w₂ => projCell w₂ = projCell w₁) conc)
    {act : StateM W α} (hAct : SysFramePres projRaw projCell act) :
    SysFramePres projRaw projCell (conc.tryCatchMsg act) := by
  intro w hWf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hTry⟩ := hConc
  have hRun := hTry act (fun u _ u' => projCell u' = projCell u) (fun u u' => projCell u' = projCell u)
    (fun _ _ => rfl) (fun u hu => let ⟨hw, hc⟩ := hAct u hu; ⟨hw, hc, hc⟩) w hWf
  rcases hR : (conc.tryCatchMsg act).run w with ⟨res, w'⟩
  rw [hR] at hRun
  cases res with
  | ok _ => exact ⟨hRun.1, hRun.2⟩
  | error _ => exact ⟨hRun.1, hRun.2.2⟩

/-- `catchSysErrno conc` preserves `SysFramePres`. -/
theorem sysFramePres_catchSysErrno {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {conc : Core.ConcOpsM (StateM W)}
    (hConc : Core.ObeysConcFrame (fun w => fullWorldWf (projRaw w) = true)
      (fun w₁ w₂ => projCell w₂ = projCell w₁) conc)
    {act : StateM W (Except Errno α)} (hAct : SysFramePres projRaw projCell act) :
    SysFramePres projRaw projCell (catchSysErrno conc act) := by
  unfold catchSysErrno
  refine sysFramePres_bind (sysFramePres_tryCatchMsg hConc hAct) fun r => ?_
  cases r <;> exact sysFramePres_pure _

/-- `catchSysPf conc` preserves `SysFramePres`. -/
theorem sysFramePres_catchSysPf {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {conc : Core.ConcOpsM (StateM W)}
    (hConc : Core.ObeysConcFrame (fun w => fullWorldWf (projRaw w) = true)
      (fun w₁ w₂ => projCell w₂ = projCell w₁) conc)
    {act : StateM W (Except PostFork.PostForkError α)} (hAct : SysFramePres projRaw projCell act) :
    SysFramePres projRaw projCell (catchSysPf conc act) := by
  unfold catchSysPf
  refine sysFramePres_bind (sysFramePres_tryCatchMsg hConc hAct) fun r => ?_
  cases r <;> exact sysFramePres_pure _

/-- `catchSysOpt conc` preserves `SysFramePres`. -/
theorem sysFramePres_catchSysOpt {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {conc : Core.ConcOpsM (StateM W)}
    (hConc : Core.ObeysConcFrame (fun w => fullWorldWf (projRaw w) = true)
      (fun w₁ w₂ => projCell w₂ = projCell w₁) conc)
    {act : StateM W (Option α)} (hAct : SysFramePres projRaw projCell act) :
    SysFramePres projRaw projCell (catchSysOpt conc act) := by
  unfold catchSysOpt
  refine sysFramePres_bind (sysFramePres_tryCatchMsg hConc hAct) fun r => ?_
  cases r <;> exact sysFramePres_pure _

/-- Universal extractor from `(hRaw, hRawFrame)` for any operation encoded by `FullRawReq`. -/
theorem sysFramePres_of_rawReq {W C α : Type} {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {raw : FullSysOpsM (StateM W)}
    (hRaw : Core.ObeysStep projRaw fullWorldWf (execFullRawStep raw) allowedFullRawStep)
    (hRawFrame : ∀ w req, fullWorldWf (projRaw w) = true →
      projCell ((execFullRawStep raw req).run w).2 = projCell w)
    (req : FullRawReq) (act : StateM W α)
    (hRun : ∀ u : W, ((execFullRawStep raw req).run u).2 = (act.run u).2) :
    SysFramePres projRaw projCell act := by
  intro w hWf
  have hStep := (hRaw w req hWf).1
  have hFr := hRawFrame w req hWf
  rw [hRun w] at hStep hFr
  exact ⟨hStep, hFr⟩

private theorem netRelay_recvIntoRing_frame {W C fd : Type}
    {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {net : Net.NetOpsM (StateM W) fd}
    (hRecv : ∀ h n fl, SysFramePres projRaw projCell (net.recvfrom h n fl)) (h : fd) :
    ∀ fuel rb, SysFramePres projRaw projCell (NetRelay.recvIntoRing net h fuel rb)
  | 0, _ => sysFramePres_pure _
  | fuel + 1, rb => by
    unfold NetRelay.recvIntoRing NetRelay.Internal.recvIntoRing
    refine sysFramePres_ite (sysFramePres_pure _) ?_
    refine sysFramePres_bind (hRecv h _ _) fun r => ?_
    cases r with
    | ok _ =>
      exact sysFramePres_ite (sysFramePres_pure _)
        (netRelay_recvIntoRing_frame hRecv h fuel _)
    | error _ =>
      exact sysFramePres_ite (netRelay_recvIntoRing_frame hRecv h fuel rb)
        (sysFramePres_ite (sysFramePres_pure _)
          (sysFramePres_ite (sysFramePres_pure _) (sysFramePres_pure _)))

private theorem netRelay_flushRingNonblock_frame {W C fd : Type}
    {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {net : Net.NetOpsM (StateM W) fd}
    (hSend : ∀ h bs fl, SysFramePres projRaw projCell (net.sendto h bs fl)) (h : fd) :
    ∀ fuel rb, SysFramePres projRaw projCell (NetRelay.flushRingNonblock net h fuel rb)
  | 0, _ => sysFramePres_pure _
  | fuel + 1, rb => by
    unfold NetRelay.flushRingNonblock NetRelay.Internal.flushRingNonblock
    refine sysFramePres_ite (sysFramePres_pure _) ?_
    refine sysFramePres_bind (hSend h _ _) fun r => ?_
    cases r with
    | ok _ =>
      exact sysFramePres_ite (sysFramePres_pure _)
        (netRelay_flushRingNonblock_frame hSend h fuel _)
    | error _ =>
      exact sysFramePres_ite (netRelay_flushRingNonblock_frame hSend h fuel rb)
        (sysFramePres_ite (sysFramePres_pure _) (sysFramePres_pure _))

private theorem netRelay_shutdownWrClean_frame {W C fd : Type}
    {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {net : Net.NetOpsM (StateM W) fd}
    (hShut : ∀ h how, SysFramePres projRaw projCell (net.shutdown h how)) (h : fd) :
    ∀ fuel, SysFramePres projRaw projCell (NetRelay.shutdownWrClean net h fuel)
  | 0 => sysFramePres_pure _
  | fuel + 1 => by
    unfold NetRelay.shutdownWrClean NetRelay.Internal.shutdownWrClean
    refine sysFramePres_bind (hShut h .wr) fun r => ?_
    cases r with
    | ok _ => exact sysFramePres_pure _
    | error _ =>
      exact sysFramePres_ite (netRelay_shutdownWrClean_frame hShut h fuel)
        (sysFramePres_ite (sysFramePres_pure _) (sysFramePres_pure _))

private theorem forwarder_loop_frame {W C fd : Type}
    {projRaw : W → HealthyRawSysWorld} {projCell : W → C}
    {net : Net.NetOpsM (StateM W) fd} {poll : Poll.PollOpsM (StateM W) fd}
    {closeFd : fd → StateM W Unit} {checkStop : StateM W Bool}
    (hClose : ∀ h, SysFramePres projRaw projCell (closeFd h))
    (hCheck : SysFramePres projRaw projCell checkStop)
    (hSock : ∀ d s fl p, SysFramePres projRaw projCell (net.socket d s fl p))
    (hAcc : ∀ h fl, SysFramePres projRaw projCell (net.accept4 h fl))
    (hConn : ∀ h sa, SysFramePres projRaw projCell (net.connect h sa))
    (hGso : ∀ h opt, SysFramePres projRaw projCell (net.getsockopt h opt))
    (hRecv : ∀ h n fl, SysFramePres projRaw projCell (net.recvfrom h n fl))
    (hSend : ∀ h bs fl, SysFramePres projRaw projCell (net.sendto h bs fl))
    (hShut : ∀ h how, SysFramePres projRaw projCell (net.shutdown h how))
    (hPoll : ∀ es ts, SysFramePres projRaw projCell (poll.ppoll es ts))
    (wakeR : fd) (listeners : Array (fd × UInt16)) :
    ∀ relays fuel, SysFramePres projRaw projCell
      (runForwarderLoop net poll closeFd checkStop wakeR listeners relays fuel) := by
  have hCloseRel : ∀ c, SysFramePres projRaw projCell (closeForwardRelay closeFd c) := fun c =>
    sysFramePres_bind (hClose c.boxFd) fun _ => hClose c.hostFd
  have hCloseAll : ∀ rs, SysFramePres projRaw projCell (closeAllRelays closeFd rs) := fun rs =>
    sysFramePres_bind
      (sysFramePres_forIn_array _ (fun c _ => sysFramePres_bind (hCloseRel c) fun _ => sysFramePres_pure _) rs PUnit.unit)
      fun _ => sysFramePres_pure ()
  have hStepConn : ∀ c rev, SysFramePres projRaw projCell (stepRelayConnect net c rev) := fun c rev => by
    unfold stepRelayConnect
    refine sysFramePres_ite ?_ (sysFramePres_pure _)
    refine sysFramePres_bind (hGso c.hostFd .error) fun r => ?_
    cases r with
    | ok v =>
      by_cases hv : v = 0
      · subst hv; exact sysFramePres_pure _
      · simp [hv]; exact sysFramePres_pure _
    | error _ => exact sysFramePres_pure _
  have hFlushIf : ∀ d rb, SysFramePres projRaw projCell (flushRingIfNonEmpty net d rb) := fun d rb => by
    unfold flushRingIfNonEmpty
    exact sysFramePres_ite (netRelay_flushRingNonblock_frame hSend d _ _) (sysFramePres_pure _)
  have hStepRecvBox : ∀ c br, SysFramePres projRaw projCell (stepRelayRecvBox net c br) := fun c br => by
    unfold stepRelayRecvBox
    refine sysFramePres_ite ?_ (sysFramePres_pure _)
    refine sysFramePres_bind (netRelay_recvIntoRing_frame hRecv c.boxFd _ _) fun r => ?_
    cases r with | none => exact sysFramePres_pure _ | some p => rcases p with ⟨_, _⟩; exact sysFramePres_pure _
  have hStepRecvHost : ∀ c hr, SysFramePres projRaw projCell (stepRelayRecvHost net c hr) := fun c hr => by
    unfold stepRelayRecvHost
    refine sysFramePres_ite ?_ (sysFramePres_pure _)
    refine sysFramePres_bind (netRelay_recvIntoRing_frame hRecv c.hostFd _ _) fun r => ?_
    cases r with | none => exact sysFramePres_pure _ | some p => rcases p with ⟨_, _⟩; exact sysFramePres_pure _
  have hStepFlushHost : ∀ c, SysFramePres projRaw projCell (stepRelayFlushHost net c) := fun c => by
    unfold stepRelayFlushHost
    refine sysFramePres_ite ?_ (sysFramePres_pure _)
    refine sysFramePres_bind (hFlushIf c.hostFd c.b2h) fun r => ?_
    cases r with
    | none => exact sysFramePres_pure _
    | some b2h' =>
      exact sysFramePres_ite
        (sysFramePres_bind (netRelay_shutdownWrClean_frame hShut ({ c with b2h := b2h' } : ForwardRelayConn fd).hostFd _) fun _ => sysFramePres_pure _)
        (sysFramePres_pure _)
  have hMaybeShutBox : ∀ c, SysFramePres projRaw projCell (maybeShutdownBoxWr net c) := fun c => by
    unfold maybeShutdownBoxWr
    exact sysFramePres_ite
      (sysFramePres_bind (netRelay_shutdownWrClean_frame hShut c.boxFd _) fun _ => sysFramePres_pure _)
      (sysFramePres_pure _)
  have hStepRel : ∀ c br hr, SysFramePres projRaw projCell (stepForwardRelay net closeFd c br hr) := fun c0 br hr => by
    unfold stepForwardRelay
    refine sysFramePres_ite (sysFramePres_bind (hCloseRel c0) fun _ => sysFramePres_pure _) ?_
    refine sysFramePres_bind (hStepConn c0 hr) fun rc1 => ?_
    cases rc1 with
    | none => exact sysFramePres_bind (hCloseRel c0) fun _ => sysFramePres_pure _
    | some c1 =>
      refine sysFramePres_bind (hStepRecvBox c1 br) fun rc2 => ?_
      cases rc2 with
      | none => exact sysFramePres_bind (hCloseRel c1) fun _ => sysFramePres_pure _
      | some c2 =>
        refine sysFramePres_bind (hStepRecvHost c2 hr) fun rc3 => ?_
        cases rc3 with
        | none => exact sysFramePres_bind (hCloseRel c2) fun _ => sysFramePres_pure _
        | some c3 =>
          refine sysFramePres_bind (hStepFlushHost c3) fun rc4 => ?_
          cases rc4 with
          | none => exact sysFramePres_bind (hCloseRel c3) fun _ => sysFramePres_pure _
          | some c4 =>
            refine sysFramePres_bind (hFlushIf c4.boxFd c4.h2b) fun rh => ?_
            cases rh with
            | none => exact sysFramePres_bind (hCloseRel c4) fun _ => sysFramePres_pure _
            | some h2b' =>
              refine sysFramePres_bind (hMaybeShutBox { c4 with h2b := h2b' }) fun c6 => ?_
              exact sysFramePres_ite (sysFramePres_bind (hCloseRel c6) fun _ => sysFramePres_pure _) (sysFramePres_pure _)
  have hAccLoop : ∀ lfd hp f rs, SysFramePres projRaw projCell (acceptOnListenerLoop net closeFd lfd hp f rs) := by
    intro lfd hp f
    induction f with
    | zero => intro _; exact sysFramePres_pure _
    | succ f ih =>
      intro rs
      unfold acceptOnListenerLoop
      refine sysFramePres_ite (sysFramePres_pure _) ?_
      refine sysFramePres_bind (hAcc lfd _) fun ra => ?_
      cases ra with
      | error _ => exact sysFramePres_ite (ih rs) (sysFramePres_pure _)
      | ok p =>
        rcases p with ⟨bfd, _⟩
        refine sysFramePres_bind (hSock .inet .stream _ 0) fun rS => ?_
        cases rS with
        | error _ => exact sysFramePres_bind (hClose bfd) fun _ => ih rs
        | ok hfd =>
          refine sysFramePres_bind (hConn hfd _) fun rC => ?_
          cases rC with
          | ok _ => exact ih _
          | error _ =>
            exact sysFramePres_ite (ih _)
              (sysFramePres_bind (hClose hfd) fun _ => sysFramePres_bind (hClose bfd) fun _ => ih rs)
  have hStepAll : ∀ rs ridxs revs rem acc,
      SysFramePres projRaw projCell (stepRelaysAt net closeFd rs ridxs revs rem acc) := by
    intro rs ridxs revs rem
    induction rem with
    | zero => intro _; exact sysFramePres_pure _
    | succ rem ih =>
      intro acc
      unfold stepRelaysAt
      by_cases hi : rs.size - (rem + 1) < rs.size
      · simp only [hi, ↓reduceDIte]
        refine sysFramePres_bind (hStepRel _ _ _) fun rc => ?_
        cases rc <;> exact ih _
      · simp only [hi, ↓reduceDIte]; exact sysFramePres_pure _
  have hTick : ∀ rs, SysFramePres projRaw projCell
      (stepForwarderTick net poll closeFd checkStop wakeR listeners rs) := fun rs => by
    unfold stepForwarderTick
    refine sysFramePres_bind hCheck fun b1 => ?_
    cases b1 with
    | true => exact sysFramePres_pure _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine sysFramePres_bind (hPoll _ none) fun rp => ?_
      cases rp with
      | error _ => exact sysFramePres_ite (sysFramePres_pure _) (sysFramePres_pure _)
      | ok revs =>
        refine sysFramePres_ite (sysFramePres_pure _) ?_
        refine sysFramePres_bind hCheck fun b2 => ?_
        cases b2 with
        | true => exact sysFramePres_pure _
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine sysFramePres_bind (hStepAll rs _ revs rs.size _) fun nextRs => ?_
          refine sysFramePres_bind
            (sysFramePres_forIn_array _ (fun item cur => ?_) _ nextRs)
            fun _ => sysFramePres_pure _
          rcases item with ⟨_, lfd, hp⟩
          exact sysFramePres_ite
            (sysFramePres_bind (hAccLoop lfd hp MAX_ACCEPT_BATCH cur) fun _ => sysFramePres_pure _)
            (sysFramePres_pure _)
  intro relays fuel
  induction fuel generalizing relays with
  | zero => exact hCloseAll relays
  | succ fuel ih =>
    unfold runForwarderLoop
    refine sysFramePres_bind (hTick relays) fun tr => ?_
    cases tr with
    | stop => exact hCloseAll relays
    | retryEintr => exact ih relays
    | stepped rs' => exact ih rs'

/-- `mkSafeSysDepsM raw conc hostPlatformIsLinux hostPlatformTarget` satisfies `DepsPreservesProj`
    under `ObeysStep` (`hRaw`), frame disjointness (`hRawFrame`), and `ObeysConcFrame` (`hConc`). -/
theorem depsPreservesProj_mkSafeSysDepsM {W : Type}
    {projRaw : W → HealthyRawSysWorld} {raw : FullSysOpsM (StateM W)}
    {conc : Core.ConcOpsM (StateM W)}
    {projCell : W → HostCellState conc.Ref conc.TaskHandle}
    (hRaw : Core.ObeysStep projRaw fullWorldWf (execFullRawStep raw) allowedFullRawStep)
    (hRawFrame : ∀ w req, fullWorldWf (projRaw w) = true →
      projCell ((execFullRawStep raw req).run w).2 = projCell w)
    (hConc : Core.ObeysConcFrame (fun w => fullWorldWf (projRaw w) = true)
      (fun w₁ w₂ => projCell w₂ = projCell w₁) conc) :
    DepsPreservesProj (fun w => mapFullToRawWorld (projRaw w) (cellToRawTable (projCell w)))
      (mkSafeSysDepsM raw conc hostPlatformIsLinux hostPlatformTarget) := by
  have hSFilesClose : ∀ h, SysFramePres projRaw projCell ((mkSafeFilesOps conc raw.files).close h) := fun h =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.files (.close h)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetSp : ∀ d s fl, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).socketpair d s fl) := fun d s fl =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.socketpair d s fl)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetSock : ∀ d s fl p, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).socket d s fl p) := fun d s fl p =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.socket d s fl p)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetAcc : ∀ h fl, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).accept4 h fl) := fun h fl =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.accept4 h fl)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetConn : ∀ h sa, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).connect h sa) := fun h sa =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.connect h sa)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetGso : ∀ h opt, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).getsockopt h opt) := fun h opt =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.getsockopt h opt)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetRecv : ∀ h n fl, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).recvfrom h n fl) := fun h n fl =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.recvfrom h n fl)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetSend : ∀ h bs fl, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).sendto h bs fl) := fun h bs fl =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.sendto h bs fl)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSNetShut : ∀ h how, SysFramePres projRaw projCell ((mkSafeNetOps conc raw.net).shutdown h how) := fun h how =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.net (.shutdown h how)) _
      (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run]))
  have hSPoll : ∀ es ts, SysFramePres projRaw projCell ((mkSafePollOps conc raw.poll).ppoll es ts) := fun es ts =>
    sysFramePres_catchSysErrno hConc (sysFramePres_of_rawReq hRaw hRawFrame (.pollPpoll es ts) _
      (fun _ => by dsimp only [execFullRawStep]; rw [stateM_map_run]))
  have hMkRef : ∀ {α : Type} (x : α), SysFramePres projRaw projCell (conc.mkRef x) := fun x w hWf => by
    obtain ⟨_, h1, _⟩ := hConc; exact h1 x w hWf
  have hReadRef : ∀ {α : Type} (r : conc.Ref α), SysFramePres projRaw projCell (conc.readRef r) := fun r w hWf => by
    obtain ⟨_, _, h2, _⟩ := hConc; exact h2 r w hWf
  have hWriteRef : ∀ {α : Type} (r : conc.Ref α) (v : α), SysFramePres projRaw projCell (conc.writeRef r v) := fun r v w hWf => by
    obtain ⟨_, _, _, h3, _⟩ := hConc; exact h3 r v w hWf
  have hModRef : ∀ {α β : Type} (r : conc.Ref α) (f : α → β × α), SysFramePres projRaw projCell (conc.modifyGetRef r f) := fun r f w hWf => by
    obtain ⟨_, _, _, _, h4, _⟩ := hConc; have h := h4 r f w hWf; exact ⟨h.1, h.2.1⟩
  have hWaitTask : ∀ {α : Type} (t : conc.TaskHandle α), SysFramePres projRaw projCell (conc.waitTask t) := fun t w hWf => by
    obtain ⟨_, _, _, _, _, _, _, _, h8, _⟩ := hConc; have h := h8 t w hWf; exact ⟨h.1, h.2.1⟩
  have hSpawn : ∀ {α : Type} (act : StateM W α), SysFramePres projRaw projCell act →
      SysFramePres projRaw projCell (conc.spawnTask act) := fun act hAct w hWf => by
    obtain ⟨_, _, _, _, _, h5, _⟩ := hConc
    have h := h5 act (fun _ => True) (fun u hu => let ⟨hw, hc⟩ := hAct u hu; ⟨hw, hc, trivial⟩) w hWf
    exact ⟨h.1, h.2.1⟩
  refine
    { metaInfo := fun w hWf => by
        have hSys : (projRaw w).wf = true := rawHostWorldWf_mapFullToRawWorld_wf hWf
        simp [mkSafeSysDepsM, mapFullToRawWorld, hSys]
      filesOpenat := fun d p fl m => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.openat d p fl m)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesClose := fun h => preservesProj_of_sysFramePres (hSFilesClose h)
      filesRead := fun h n => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.read h n)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesWrite := fun h bs => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.write h bs)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesFstatat := fun d p fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.fstatat d p fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesFaccessat := fun d p mk fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.faccessat d p mk fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesMkdirat := fun d p m => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.mkdirat d p m)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesUnlinkat := fun d p rm => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.unlinkat d p rm)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesReadlinkat := fun d p c => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.readlinkat d p c)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesFcntl := fun h cmd => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.fcntl h cmd)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      filesReopenReadOnly := fun h => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.files (.reopenReadOnly h)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdFilesReq]; rw [stateM_map_run, stateM_map_run])
      netSocketpair := fun d s fl => preservesProj_of_sysFramePres (hSNetSp d s fl)
      netRecvmsg := fun h mf => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.net (.recvmsg h mf)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdNetReq]; rw [stateM_map_run, stateM_map_run])
      pollPpoll := fun es ts => preservesProj_of_sysFramePres (hSPoll es ts)
      procPipe2 := fun fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.proc (.pipe2 fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdProcReq]; rw [stateM_map_run, stateM_map_run])
      procWaitpid := fun pid fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.proc (.waitpid pid fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdProcReq]; rw [stateM_map_run, stateM_map_run])
      procKill := fun pid sig => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.proc (.kill pid sig)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdProcReq]; rw [stateM_map_run, stateM_map_run])
      procPidfdOpen := fun pid fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.proc (.pidfdOpen pid fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdProcReq]; rw [stateM_map_run, stateM_map_run])
      procPidfdSendSignal := fun h sig fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.proc (.pidfdSendSignal h sig fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdProcReq]; rw [stateM_map_run, stateM_map_run])
      procGetpid := preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.proc .getpid) _ (fun _ => by dsimp only [execFullRawStep, execRawFdProcReq]; rw [stateM_map_run, stateM_map_run])
      procGetuid := preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.proc .getuid) _ (fun _ => by dsimp only [execFullRawStep, execRawFdProcReq]; rw [stateM_map_run, stateM_map_run])
      sandboxLandlockCreateRuleset := fun a fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.sandbox (.landlockCreateRuleset a fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdSandboxReq]; rw [stateM_map_run, stateM_map_run])
      sandboxSeccomp := fun op fl bs => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.sandbox (.seccomp op fl bs)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdSandboxReq]; rw [stateM_map_run, stateM_map_run])
      sandboxMemfdCreate := fun nm fl => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.sandbox (.memfdCreate nm fl)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdSandboxReq]; rw [stateM_map_run, stateM_map_run])
      timeRandClockGettime := fun clk => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.timeRand (.clock_gettime clk)) _ (fun _ => by dsimp only [execFullRawStep, TimeRand.execTimeRandReq]; rw [stateM_map_run, stateM_bind_run, stateM_pure_run])
      timeRandClockNanosleep := fun clk a ts => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.timeRand (.clock_nanosleep clk a ts)) _ (fun _ => by dsimp only [execFullRawStep, TimeRand.execTimeRandReq]; rw [stateM_map_run, stateM_bind_run, stateM_pure_run])
      passwdGetpwuid := fun uid => preservesProj_of_sysFramePres <| sysFramePres_catchSysErrno hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.passwd (.getpwuid uid)) _ (fun _ => by dsimp only [execFullRawStep, Passwd.execPasswdReq]; rw [stateM_map_run, stateM_bind_run, stateM_pure_run])
      postForkSpawn := fun sp => preservesProj_of_sysFramePres <| sysFramePres_catchSysPf hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.postFork (.spawn sp)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdPostForkReq]; rw [stateM_map_run, stateM_map_run])
      postForkSpawnWithBarrier := fun sp => preservesProj_of_sysFramePres <| sysFramePres_catchSysPf hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.postFork (.spawnWithBarrier sp)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdPostForkReq]; rw [stateM_map_run, stateM_map_run])
      postForkReleaseBarrier := fun p => preservesProj_of_sysFramePres <| sysFramePres_catchSysPf hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.postFork (.releaseBarrier p)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdPostForkReq]; rw [stateM_map_run, stateM_map_run])
      postForkAbortBarrier := fun p => preservesProj_of_sysFramePres <| sysFramePres_catchSysPf hConc <|
        sysFramePres_of_rawReq hRaw hRawFrame (.postFork (.abortBarrier p)) _ (fun _ => by dsimp only [execFullRawStep, execRawFdPostForkReq]; rw [stateM_map_run, stateM_map_run])
      getEnvPath := preservesProj_of_sysFramePres <|
        sysFramePres_catchSysOpt hConc <|
          sysFramePres_bind (sysFramePres_of_rawReq hRaw hRawFrame (.envGet "PATH") _
            (fun _ => by dsimp only [execFullRawStep]; rw [stateM_map_run]))
            fun r => by cases r with
              | error _ => exact sysFramePres_pure _
              | ok opt => cases opt <;> exact sysFramePres_pure _
      getEnvHome := preservesProj_of_sysFramePres <|
        sysFramePres_catchSysOpt hConc <|
          sysFramePres_bind (sysFramePres_of_rawReq hRaw hRawFrame (.envGet "HOME") _
            (fun _ => by dsimp only [execFullRawStep]; rw [stateM_map_run]))
            fun r => by cases r <;> exact sysFramePres_pure _
      startFwdTask := fun lfds hports => preservesProj_of_sysFramePres <| by
        dsimp only [mkSafeSysDepsM]
        refine sysFramePres_catchSysErrno hConc ?_
        unfold startForwarderM
        refine sysFramePres_bind (sysFramePres_retryEintr (hSNetSp .unix .stream _) _) fun rsp => ?_
        cases rsp with
        | error _ => exact sysFramePres_pure _
        | ok pair =>
          rcases pair with ⟨wakeR, wakeW⟩
          refine sysFramePres_bind (hMkRef false) fun stopReq => ?_
          refine sysFramePres_bind (hMkRef (some wakeW)) fun _ => ?_
          have hCloseUnit : ∀ h, SysFramePres projRaw projCell
              (do let _ ← (mkSafeFilesOps conc raw.files).close h; pure ()) := fun h =>
            sysFramePres_bind (hSFilesClose h) fun _ => sysFramePres_pure ()
          have hBgLoop := forwarder_loop_frame hCloseUnit (hReadRef stopReq)
            hSNetSock hSNetAcc hSNetConn hSNetGso hSNetRecv hSNetSend hSNetShut hSPoll
            wakeR (lfds.zip hports) #[] FORWARDER_LOOP_FUEL
          refine sysFramePres_bind
            (hSpawn _ (sysFramePres_bind (sysFramePres_tryCatchMsg hConc hBgLoop) fun _ => sysFramePres_pure ()))
            fun _ => sysFramePres_pure _
      stopFwdTask := fun th => preservesProj_of_sysFramePres <| by
        dsimp only [mkSafeSysDepsM]
        refine sysFramePres_bind (sysFramePres_tryCatchMsg hConc ?_) fun _ => sysFramePres_pure ()
        unfold stopForwarderM
        refine sysFramePres_bind (hWriteRef th.stopRequested true) fun _ => ?_
        refine sysFramePres_bind (hModRef th.wakeWRef _) fun w? => ?_
        have hCloseUnit : ∀ h, SysFramePres projRaw projCell
            (do let _ ← (mkSafeFilesOps conc raw.files).close h; pure ()) := fun h =>
          sysFramePres_bind (hSFilesClose h) fun _ => sysFramePres_pure ()
        have hTail : SysFramePres projRaw projCell (do
            let _ ← conc.waitTask th.task
            let closeFd : RawFd → StateM W Unit := fun d => do
              let _ ← (mkSafeFilesOps conc raw.files).close d
              pure ()
            closeFd th.wakeR
            for lfd in th.listenerFds do
              closeFd lfd) :=
          sysFramePres_bind (hWaitTask th.task) fun _ =>
            sysFramePres_bind (hCloseUnit th.wakeR) fun _ =>
              sysFramePres_bind
                (sysFramePres_forIn_array _ (fun lfd _ => sysFramePres_bind (hCloseUnit lfd) fun _ => sysFramePres_pure _) th.listenerFds PUnit.unit)
                fun _ => sysFramePres_pure ()
        cases w? with
        | none => exact hTail
        | some wfd =>
          exact sysFramePres_bind (sysFramePres_retryEintr (hSNetSend wfd _ _) DEFAULT_EINTR_FUEL) fun _ =>
            sysFramePres_bind (hSFilesClose wfd) fun _ => hTail }

end LeanSwe.ProcessSandbox.Raw.Proofs
