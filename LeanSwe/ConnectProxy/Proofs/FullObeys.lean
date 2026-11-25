import Core.ConcOps
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.FullStep
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.SysBridge.Driver
import LeanSwe.ConnectProxy.Impl
import LeanSwe.ConnectProxy.Proofs.FullObeysHelpers
import LeanSwe.ConnectProxy.Proofs.FullObeysLoop
import LeanSwe.ConnectProxy.Proofs.FullObeysDriver
import LeanSwe.ConnectProxy.Proofs.FullObeysWitness

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys
open LeanSwe.ConnectProxy.SysBridge
open LeanSwe.ConnectProxy.SysBridge.Driver

/-- End-to-end `Core.ObeysStepFromConc` theorem for `Internal.mkFullApiM` over `HealthySysWorld`:
    quantifies universally over all `W`, `raw : FullSysOpsM (StateM W)` obeying `allowedFullRawStep`,
    and `conc : Core.ConcOpsM (StateM W)` obeying `Core.ObeysConc`, proving `HealthySysWorld.wf`
    preservation and all `allowedFullPkgStep` postconditions across every reachable interleaving. -/
theorem obeysStepFromConc_mkFullApiM_full :
    Core.ObeysStepFromConc id fullWorldWf
      execFullRawStep allowedFullRawStep
      fullWorldWf Internal.mkFullApiM
      execPkgStep allowedFullPkgStep := by
  intro W proj raw conc hRaw hConc w req hWf
  let inv : W → Prop := fun s => (proj s).wf = true
  have hSys : SysPreservesInv inv raw :=
    sysPreservesInv_of_obeysStep proj raw hRaw
  have hConc' : Core.ObeysConc inv conc := hConc
  have hLoop := driver_runProxyLoopM_pres hSys hConc'
  have hTd := driver_teardownTrackedM_inv hSys hConc'
  rcases hConc' with ⟨TaskPost, hMkRef, _, hWriteRef, hModGetRef, hSpawn, _, _, hWait, hTryCatch⟩
  dsimp only [execPkgStep, Internal.mkFullApiM, allowedFullPkgStep, id, Function.comp]
  cases hVal : Model.validateConfig req.cfg with
  | error err =>
    dsimp only [pure, StateT.pure, StateT.run, Id.run]
    exact ⟨hWf, rfl, rfl⟩
  | ok vcfg =>
    let QOut : Except ProxyError (UInt16 × Array ConnectEvent) × W → Prop := fun p =>
      inv p.2 ∧ match p.1 with
        | .error err => err.message ≠ ""
        | .ok (val, evs) =>
          ∃ boundPort : UInt16,
            boundPort ≠ 0 ∧
            (vcfg.config.listenPort ≠ 0 → boundPort = vcfg.config.listenPort) ∧
            val = boundPort + req.tag ∧
            EventsValid evs
    let PCr : Except ProxyError (RawFd × RawFd × RawFd × UInt16) → Prop := fun res =>
      match res with
      | .error err => err.message ≠ ""
      | .ok quad => quad.2.2.2 ≠ 0 ∧ (vcfg.config.listenPort ≠ 0 → quad.2.2.2 = vcfg.config.listenPort)
    let QCr : Except String (Except ProxyError (RawFd × RawFd × RawFd × UInt16)) × W → Prop := fun p =>
      inv p.2 ∧ match p.1 with
        | .error msg => msg ≠ ""
        | .ok res => PCr res
    let PLoop : Except String (Array ConnectEvent) → Prop := fun r =>
      match r with
      | .ok evs => EventsValid evs
      | .error msg => msg ≠ ""
    have hMain : QOut ((withProxyM raw conc vcfg (fun rp => pure (.ok (rp.port + req.tag)))).run w) := by
      unfold withProxyM
      have hCrAll : ∀ w0, inv w0 →
          let (res, w') := (createListener raw vcfg).run w0
          inv w' ∧ PCr res := by
        intro w0 hw0
        have hCL := sys_createListener_laws hSys vcfg w0 hw0
        cases hR : (createListener raw vcfg).run w0 with
        | mk res w' =>
          rw [hR] at hCL
          cases res <;> exact hCL
      have hCrTry : QCr ((conc.tryCatchMsg (createListener raw vcfg)).run w) := by
        have hT := hTryCatch (createListener raw vcfg) PCr hCrAll w hWf
        cases hR : (conc.tryCatchMsg (createListener raw vcfg)).run w with
        | mk r w' =>
          rw [hR] at hT
          cases r <;> exact hT
      apply state_bind_post_of (P := QCr) (Q := QOut) hCrTry
      intro crTry w1 h1
      rcases h1 with ⟨hWf1, hCrRes⟩
      cases crTry with
      | error msg =>
        try dsimp only
        exact ⟨hWf1, (mapRawErrorPure_laws (.userError msg)).1⟩
      | ok resCr =>
        cases resCr with
        | error err => exact ⟨hWf1, hCrRes⟩
        | ok quad =>
          rcases quad with ⟨lfd, wakeR, wakeW, boundPort⟩
          rcases hCrRes with ⟨hBpNe0, hBpEq⟩
          try dsimp only
          let PSetup : (conc.Ref Bool × conc.Ref Bool × conc.TaskHandle (Except String (Array ConnectEvent))) → Prop :=
            fun tup => TaskPost tup.2.2 PLoop
          let QSetup : Except String (conc.Ref Bool × conc.Ref Bool × conc.TaskHandle (Except String (Array ConnectEvent))) × W → Prop :=
            fun p => inv p.2 ∧ match p.1 with | .error msg => msg ≠ "" | .ok tup => PSetup tup
          let setupAct : StateM W (conc.Ref Bool × conc.Ref Bool × conc.TaskHandle (Except String (Array ConnectEvent))) := do
            let stopFlag ← conc.mkRef false
            let listenClosedFlag ← conc.mkRef false
            let slotsRef ← conc.mkRef (#[] : Array (ClientSlot RawFd (ConcDnsJob RawFd conc.Ref conc.TaskHandle)))
            let dnsTasksRef ← conc.mkRef (#[] : Array (ConcDnsJob RawFd conc.Ref conc.TaskHandle))
            let loopTask ← conc.spawnTask (do
              match ← conc.tryCatchMsg
                  (runProxyLoopM raw conc vcfg (decideConnectHead vcfg.config)
                    (decideResolvedIps vcfg.config.ipPolicy) stopFlag listenClosedFlag
                    slotsRef dnsTasksRef lfd wakeR LOOP_FUEL #[] #[] 0 #[]) with
              | .ok evs => return (Except.ok evs : Except String (Array ConnectEvent))
              | .error msg =>
                let _ ← conc.tryCatchMsg
                  (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd)
                return (Except.error msg : Except String (Array ConnectEvent)))
            pure (stopFlag, listenClosedFlag, loopTask)
          let QSetupOk : (conc.Ref Bool × conc.Ref Bool × conc.TaskHandle (Except String (Array ConnectEvent))) × W → Prop :=
            fun p => inv p.2 ∧ PSetup p.1
          let QLoopOk : Except String (Array ConnectEvent) × W → Prop :=
            fun p => inv p.2 ∧ PLoop p.1
          have hSetupAll : ∀ w0, inv w0 → let (tup, w') := setupAct.run w0; inv w' ∧ PSetup tup := by
            intro w0 hw0
            have hP : QSetupOk (setupAct.run w0) := by
              dsimp only [setupAct]
              apply state_bind_post (Q := QSetupOk) (hMkRef false w0 hw0); intro stopFlag wa ha
              apply state_bind_post (Q := QSetupOk) (hMkRef false wa ha); intro listenClosedFlag wb hb
              apply state_bind_post (Q := QSetupOk) (hMkRef (#[] : Array (ClientSlot RawFd (ConcDnsJob RawFd conc.Ref conc.TaskHandle))) wb hb)
              intro slotsRef wc hc
              apply state_bind_post (Q := QSetupOk) (hMkRef (#[] : Array (ConcDnsJob RawFd conc.Ref conc.TaskHandle)) wc hc)
              intro dnsTasksRef wd hd
              have hWorkerOk : ∀ wk, inv wk →
                  let (res, wl) := (do
                    match ← conc.tryCatchMsg
                        (runProxyLoopM raw conc vcfg (decideConnectHead vcfg.config)
                          (decideResolvedIps vcfg.config.ipPolicy) stopFlag listenClosedFlag
                          slotsRef dnsTasksRef lfd wakeR LOOP_FUEL #[] #[] 0 #[]) with
                    | .ok evs => return (Except.ok evs : Except String (Array ConnectEvent))
                    | .error msg =>
                      let _ ← conc.tryCatchMsg
                        (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd)
                      return (Except.error msg : Except String (Array ConnectEvent))).run wk
                  inv wl ∧ PLoop res := by
                intro wk hwk
                let loopAct :=
                  runProxyLoopM raw conc vcfg (decideConnectHead vcfg.config)
                    (decideResolvedIps vcfg.config.ipPolicy) stopFlag listenClosedFlag
                    slotsRef dnsTasksRef lfd wakeR LOOP_FUEL #[] #[] 0 #[]
                have hLoopAll : ∀ wm, inv wm →
                    let (evs, wn) := loopAct.run wm
                    inv wn ∧ EventsValid evs := by
                  intro wm hwm
                  have hL := hLoop vcfg (decideConnectHead vcfg.config)
                    (decideResolvedIps vcfg.config.ipPolicy) stopFlag listenClosedFlag
                    slotsRef dnsTasksRef lfd wakeR LOOP_FUEL #[] #[] 0 #[] wm hwm eventsValid_empty
                  cases hR : loopAct.run wm with
                  | mk evs wn => rw [hR] at hL; exact hL
                have hTryL : QLoopOk ((conc.tryCatchMsg loopAct).run wk) := by
                  have hT := hTryCatch loopAct EventsValid hLoopAll wk hwk
                  cases hR : (conc.tryCatchMsg loopAct).run wk with
                  | mk res wn => rw [hR] at hT; cases res <;> exact hT
                have hWPost : QLoopOk
                    ((do
                      match ← conc.tryCatchMsg
                          (runProxyLoopM raw conc vcfg (decideConnectHead vcfg.config)
                            (decideResolvedIps vcfg.config.ipPolicy) stopFlag listenClosedFlag
                            slotsRef dnsTasksRef lfd wakeR LOOP_FUEL #[] #[] 0 #[]) with
                      | .ok evs => return (Except.ok evs : Except String (Array ConnectEvent))
                      | .error msg =>
                        let _ ← conc.tryCatchMsg
                          (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd)
                        return (Except.error msg : Except String (Array ConnectEvent))).run wk) := by
                  apply state_bind_post_of (P := QLoopOk) (Q := QLoopOk) hTryL
                  intro lr wn hn
                  cases lr with
                  | ok evs => exact hn
                  | error msg =>
                    try dsimp only
                    have hTdInv : inv ((conc.tryCatchMsg
                        (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd)).run wn).2 := by
                      have hT := hTryCatch (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd)
                        (fun _ => True)
                        (fun wq hwq => by
                          have h1 := hTd slotsRef dnsTasksRef listenClosedFlag lfd wq hwq
                          cases hR : (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd).run wq with
                          | mk _ wr => rw [hR] at h1; exact ⟨h1, trivial⟩)
                        wn hn.1
                      cases hR : (conc.tryCatchMsg (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd)).run wn with
                      | mk _ wr => rw [hR] at hT; exact hT.1
                    apply state_bind_post (Q := QLoopOk) hTdInv
                    intro _ wp hp
                    exact ⟨hp, hn.2⟩
                cases hR : (do
                    match ← conc.tryCatchMsg
                        (runProxyLoopM raw conc vcfg (decideConnectHead vcfg.config)
                          (decideResolvedIps vcfg.config.ipPolicy) stopFlag listenClosedFlag
                          slotsRef dnsTasksRef lfd wakeR LOOP_FUEL #[] #[] 0 #[]) with
                    | .ok evs => return (Except.ok evs : Except String (Array ConnectEvent))
                    | .error msg =>
                      let _ ← conc.tryCatchMsg
                        (teardownTrackedM raw conc slotsRef dnsTasksRef listenClosedFlag lfd)
                      return (Except.error msg : Except String (Array ConnectEvent))).run wk with
                | mk res wl => rw [hR] at hWPost; exact hWPost
              apply state_bind_post_let
                (P := fun (t : conc.TaskHandle (Except String (Array ConnectEvent))) we => inv we ∧ TaskPost t PLoop)
                (Q := QSetupOk)
                (hSpawn _ PLoop hWorkerOk wd hd)
              intro loopTask we he
              exact he
            cases hR : setupAct.run w0 with
            | mk tup w' => rw [hR] at hP; exact hP
          have hSetupTry : QSetup ((conc.tryCatchMsg setupAct).run w1) := by
            have hT := hTryCatch setupAct PSetup hSetupAll w1 hWf1
            cases hR : (conc.tryCatchMsg setupAct).run w1 with
            | mk r w' => rw [hR] at hT; cases r <;> exact hT
          apply state_bind_post_of (P := QSetup) (Q := QOut) hSetupTry
          intro setupRes w4 h4
          rcases h4 with ⟨hWf4, hSetupPost⟩
          cases setupRes with
          | error msg =>
            try dsimp only
            have hCloseTry : inv ((conc.tryCatchMsg (do
                raw.closeFd lfd
                raw.closeFd wakeR
                raw.closeFd wakeW)).run w4).2 := by
              have hT := hTryCatch (do raw.closeFd lfd; raw.closeFd wakeR; raw.closeFd wakeW)
                (fun _ => True)
                (fun wa hwa => by
                  have hC : inv ((do raw.closeFd lfd; raw.closeFd wakeR; raw.closeFd wakeW).run wa).2 := by
                    apply state_bind_inv (sys_closeFd_inv hSys lfd wa hwa); intro _ wb hb
                    apply state_bind_inv (sys_closeFd_inv hSys wakeR wb hb); intro _ wc hc
                    exact sys_closeFd_inv hSys wakeW wc hc
                  cases hR : (do raw.closeFd lfd; raw.closeFd wakeR; raw.closeFd wakeW).run wa with
                  | mk _ wr => rw [hR] at hC; exact ⟨hC, trivial⟩)
                w4 hWf4
              cases hR : (conc.tryCatchMsg (do raw.closeFd lfd; raw.closeFd wakeR; raw.closeFd wakeW)).run w4 with
              | mk _ wr => rw [hR] at hT; exact hT.1
            apply state_bind_post (Q := QOut) hCloseTry
            intro _ w5 hWf5
            exact ⟨hWf5, (mapRawErrorPure_laws (.userError msg)).1⟩
          | ok tup =>
            rcases tup with ⟨stopFlag, listenClosedFlag, loopTask⟩
            have hTaskPost : TaskPost loopTask PLoop := hSetupPost
            try dsimp only
            let QWait : Except String (Except String (Array ConnectEvent)) × W → Prop := fun p =>
              inv p.2 ∧ match p.1 with
                | .error msg => msg ≠ ""
                | .ok inner => PLoop inner
            let QFin : Except String (Except String (Array ConnectEvent)) × W → Prop := QWait
            let finBody : StateM W (Except String (Array ConnectEvent)) := do
              let (waitRes, _) ←
                tryFinally'
                  (do
                    conc.writeRef stopFlag true
                    let _ ← retryEintr
                      (raw.net.sendto wakeW (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
                      MAX_EINTR_RETRIES
                    conc.waitTask loopTask)
                  (fun _ => do
                    let alreadyClosed ← conc.modifyGetRef listenClosedFlag (fun c => (c, true))
                    if !alreadyClosed then
                      raw.closeFd lfd
                    raw.closeFd wakeR
                    raw.closeFd wakeW)
              match waitRes with
              | .error msg => return (Except.error msg : Except String (Array ConnectEvent))
              | .ok inner => return inner
            have hFinBody : ∀ wa, inv wa → let (r, wb) := finBody.run wa; inv wb ∧ PLoop r := by
              intro wa hwa
              have hP : QLoopOk (finBody.run wa) := by
                dsimp only [finBody]
                have hWaitAct : QWait ((do
                    conc.writeRef stopFlag true
                    let _ ← retryEintr
                      (raw.net.sendto wakeW (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
                      MAX_EINTR_RETRIES
                    conc.waitTask loopTask).run wa) := by
                  apply state_bind_post (Q := QWait) (hWriteRef stopFlag true wa hwa); intro _ wb hb
                  apply state_bind_post (Q := QWait)
                    (retryEintr_inv inv
                      (raw.net.sendto wakeW (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
                      (hSys.netSendto wakeW (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
                      MAX_EINTR_RETRIES wb hb)
                  intro _ wc hc
                  have hW := hWait loopTask PLoop hTaskPost wc hc
                  cases hR : (conc.waitTask loopTask).run wc with
                  | mk wr wd => rw [hR] at hW; cases wr <;> exact hW
                let QPair : (Except String (Except String (Array ConnectEvent)) × Unit) × W → Prop :=
                  fun p => QWait (p.1.1, p.2)
                have hInnerTry : QPair ((tryFinally'
                    (do
                      conc.writeRef stopFlag true
                      let _ ← retryEintr
                        (raw.net.sendto wakeW (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
                        MAX_EINTR_RETRIES
                      conc.waitTask loopTask)
                    (fun _ => do
                      let alreadyClosed ← conc.modifyGetRef listenClosedFlag (fun c => (c, true))
                      if !alreadyClosed then
                        raw.closeFd lfd
                      raw.closeFd wakeR
                      raw.closeFd wakeW)).run wa) := by
                  apply state_tryFinally'_post (P := QWait) (Q := QPair) hWaitAct
                  intro waitRes wd hd
                  have hClose : inv ((do
                      let alreadyClosed ← conc.modifyGetRef listenClosedFlag (fun c => (c, true))
                      if !alreadyClosed then
                        raw.closeFd lfd
                      raw.closeFd wakeR
                      raw.closeFd wakeW).run wd).2 := by
                    apply state_bind_inv (hModGetRef listenClosedFlag _ wd hd.1).1; intro already we he
                    cases already with
                    | false =>
                      simp only [Bool.not_false, ↓reduceIte]
                      apply state_bind_inv (sys_closeFd_inv hSys lfd we he); intro _ wf hf
                      apply state_bind_inv (sys_closeFd_inv hSys wakeR wf hf); intro _ wg hg
                      exact sys_closeFd_inv hSys wakeW wg hg
                    | true =>
                      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                      apply state_bind_inv (sys_closeFd_inv hSys wakeR we he); intro _ wg hg
                      exact sys_closeFd_inv hSys wakeW wg hg
                  exact ⟨hClose, hd.2⟩
                apply state_bind_post_of (P := QPair) (Q := QLoopOk) hInnerTry
                intro pair we he
                rcases pair with ⟨waitRes, _⟩
                cases waitRes with
                | error msg => exact he
                | ok inner => exact he
              cases hR : finBody.run wa with
              | mk r wb => rw [hR] at hP; exact hP
            have hFin : QFin ((conc.tryCatchMsg finBody).run w4) := by
              have hT := hTryCatch finBody PLoop hFinBody w4 hWf4
              cases hR : (conc.tryCatchMsg finBody).run w4 with
              | mk r wb => rw [hR] at hT; cases r <;> exact hT
            let QTry : (Except ProxyError UInt16 × Except String (Except String (Array ConnectEvent))) × W → Prop :=
              fun p => p.1.1 = .ok (boundPort + req.tag) ∧ QFin (p.1.2, p.2)
            have hTry : QTry ((tryFinally'
                (pure (Except.ok (boundPort + req.tag)) : StateM W (Except ProxyError UInt16))
                (fun _ => conc.tryCatchMsg finBody)).run w4) := by
              apply state_tryFinally'_post
                (P := fun p => p.1 = Except.ok (boundPort + req.tag) ∧ p.2 = w4)
                (Q := QTry)
                ⟨rfl, rfl⟩
              intro a wA hA
              rcases hA with ⟨rfl, rfl⟩
              exact ⟨rfl, hFin⟩
            apply state_bind_post_of (P := QTry) (Q := QOut) hTry
            intro pair w11 hPair
            rcases pair with ⟨actRes, stopRes⟩
            rcases hPair with ⟨hActEq, hWf11, hStopPost⟩
            subst hActEq
            try dsimp only
            cases stopRes with
            | error msg =>
              try dsimp only
              exact ⟨hWf11, (mapRawErrorPure_laws (.userError msg)).1⟩
            | ok inner =>
              cases inner with
              | error msg =>
                try dsimp only
                exact ⟨hWf11, (mapRawErrorPure_laws (.userError msg)).1⟩
              | ok evs =>
                try dsimp only
                exact ⟨hWf11, boundPort, hBpNe0, hBpEq, rfl, hStopPost⟩
    cases hRun : (withProxyM raw conc vcfg (fun rp => pure (.ok (rp.port + req.tag)))).run w with
    | mk out w' =>
      rw [hRun] at hMain
      exact hMain

private theorem mapFullWorldToSim_wf_iff (w : HealthySysWorld) :
    proxyStepWf (mapFullWorldToSim w) = true ↔ fullWorldWf w = true := by
  unfold proxyStepWf mapFullWorldToSim fullWorldWf
  cases w.wf <;> decide

/-- Canonical `Core.ObeysStepFromConc` theorem tying `Internal.mkFullApiM` directly to
    `Model.execPkgStep` and `Model.allowedPkgStep` for mechanical `OBEYS_SYNTH` verification. -/
theorem obeysStepFromConc_mkFullApiM :
    Core.ObeysStepFromConc mapFullWorldToSim fullWorldWf
      execFullRawStep allowedFullRawStep
      proxyStepWf Internal.mkFullApiM
      execPkgStep allowedPkgStep := by
  intro W proj raw conc hRaw hConc w req hPkgWf
  have hWf : fullWorldWf (proj w) = true := (mapFullWorldToSim_wf_iff (proj w)).mp hPkgWf
  have hFull := obeysStepFromConc_mkFullApiM_full proj raw conc hRaw hConc w req hWf
  rcases hFull with ⟨hWf', hBody⟩
  dsimp only [id, Function.comp, fullWorldWf] at hWf hWf' hBody
  dsimp only [allowedPkgStep, allowedRawStep, mapFullWorldToSim, Function.comp]
  cases hVal : Model.validateConfig req.cfg with
  | error err =>
    rw [hVal] at hBody
    exact ⟨hBody.1, by rw [hBody.2]⟩
  | ok vcfg =>
    rw [hVal] at hBody
    refine ⟨by rw [hWf, hWf'], ?_⟩
    exact hBody

end LeanSwe.ConnectProxy.Proofs
