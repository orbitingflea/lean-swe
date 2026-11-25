import LeanSwe.ConnectProxy.Proofs.SysBridgeListener

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Relay
open LeanSwe.ConnectProxy.SysBridge


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
