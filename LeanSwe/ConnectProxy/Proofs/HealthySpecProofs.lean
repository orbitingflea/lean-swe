import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.HealthySys
import LeanSwe.ConnectProxy.SpecTests
import LeanSwe.ConnectProxy.Proofs.SysBridgeProofs
import LeanSwe.ConnectProxy.Proofs.LoopAndRelayProofs
import LeanSwe.ConnectProxy.Proofs.HealthyWitness

namespace LeanSwe.ConnectProxy.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.SysBridge
open LeanSwe.ConnectProxy.HealthySys

private def cleanInitialWorld : HealthySysWorld :=
  { filesEnv := { state := { Files.FilesState.initial with fds := [] } } }

private theorem cleanInitialWorld_wf : cleanInitialWorld.wf = true := rfl

private theorem cleanInitialWorld_nodup :
    (cleanInitialWorld.filesEnv.state.fds.map Prod.fst).Nodup :=
  List.nodup_nil

/-- `test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws` holds universally over all healthy OS implementations. -/
theorem allPass_healthy_listenerBindLoopbackOnlyAndPortLaws :
    AllPass (test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws realBridgeTarget) := by
  intro sys hRef w₀ ⟨hWf₀, hNd₀⟩ vcfg
  have h := healthy_createListener_instrumented_laws sys hRef vcfg w₀ {} hWf₀
  dsimp only [test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws, realBridgeTarget,
    AllPass, bind, pure, assume, assert] at h ⊢
  rcases hRun : (createListener (instrumentSysOps sys) vcfg).run (w₀, {}) with ⟨res, w₁, tr₁⟩
  rw [hRun] at h
  dsimp only at h ⊢
  rcases h with ⟨hWf₁, hTbl₁, hDq₁, hDa₁, hBa₁, _, hRes⟩
  refine ⟨⟨hWf₁, hTbl₁⟩, ⟨hDq₁, hDa₁⟩, ?_, ?_⟩
  · intro sa hsa
    rcases hBa₁ sa hsa with hNil | hEq
    · cases hNil
    · exact hEq
  · cases res with
    | ok quad =>
      rcases quad with ⟨_, _, _, bp⟩
      exact ⟨⟨hRes.1, hRes.2.1⟩, trivial⟩
    | error err =>
      refine ⟨hRes.1, ?_, trivial⟩
      intro fd hm
      rcases hRes.2 hNd₀ fd hm with hNil | hCl
      · cases hNil
      · exact hCl

private theorem canReach_listener_of_witness
    (sys : CProxySysOpsM (StateM HealthySysWorld) Nat)
    (hRef : RefinesHealthyCProxySys sys)
    (w₀ : HealthySysWorld)
    (hW : w₀.wf = true ∧ (w₀.filesEnv.state.fds.map Prod.fst).Nodup)
    (vcfg : ValidProxyConfig) :
    CanReach (test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws realBridgeTarget) := by
  have hAll := allPass_healthy_listenerBindLoopbackOnlyAndPortLaws
  dsimp only [test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws,
    CanReach, CanReachRun, AllPass, AllPassRun, Id,
    bind, Bind.bind, pure, Pure.pure, nondet, assume, assert] at hAll ⊢
  have hInst := hAll sys hRef w₀ hW vcfg
  refine ⟨sys, hRef, w₀, hW, vcfg, ?_⟩
  generalize (realBridgeTarget.createListener (instrumentSysOps sys) vcfg).run (w₀, {}) = out at hInst ⊢
  rcases out with ⟨res, w₁, tr₁⟩
  rcases res with _ | ⟨_, _, _, _⟩ <;> exact hInst

/-- `test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws` is non-vacuously reachable. -/
theorem canReach_healthy_listenerBindLoopbackOnlyAndPortLaws :
    CanReach (test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws realBridgeTarget) :=
  canReach_listener_of_witness sampleHealthySys sampleHealthySys_refines
    cleanInitialWorld ⟨cleanInitialWorld_wf, cleanInitialWorld_nodup⟩ { config := {} }

/-- `test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect` holds universally over all healthy OS implementations. -/
theorem allPass_healthy_onHeadBeforeDnsAndVerifiedIpConnect :
    AllPass (test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect realBridgeTarget) := by
  intro sys hRef w₀ hWf₀ cfg headBytes pipelined cfd events
  let initSlot : ClientSlot Nat Unit := { phase := .handshake cfd headBytes 1000 }
  have h := healthy_handleCompleteHeadSync_laws sys hRef cfg initSlot events cfd headBytes pipelined w₀ {} hWf₀
  dsimp only [test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect, realBridgeTarget,
    AllPass, bind, pure, assume, assert] at h ⊢
  rcases hRun : (handleCompleteHead (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    initSlot events cfd headBytes pipelined).run (w₀, {}) with ⟨⟨slot₁, events₁⟩, w₁, tr₁⟩
  rw [hRun] at h
  dsimp only at h ⊢
  rcases h with ⟨hWf₁, _, hRelPipe, hConnPipe, hMatch⟩
  refine ⟨hWf₁, ⟨hRelPipe, hConnPipe⟩, ?_⟩
  cases hHead : Model.decideConnectHead cfg headBytes with
  | deny h? p? r =>
    rw [hHead] at hMatch
    exact ⟨⟨hMatch.1, hMatch.2.1, hMatch.2.2⟩, trivial⟩
  | needResolve host port litIp? =>
    cases litIp? with
    | some litIp =>
      rw [hHead] at hMatch
      refine ⟨hMatch.1, ?_, trivial⟩
      intro sa hsa
      rcases hMatch.2 sa hsa with hNil | hOk
      · cases hNil
      · exact hOk
    | none =>
      rw [hHead] at hMatch
      dsimp only at hMatch ⊢
      refine ⟨hMatch.1, ?_⟩
      have hDnsMatch := hMatch.2
      rcases hD : (sys.dns.getaddrinfo host { family := .any, sockType := .stream }).run w₀ with ⟨dnsRes, wD⟩
      rw [hD] at hDnsMatch
      dsimp only at hDnsMatch ⊢
      cases dnsRes with
      | error _ => exact ⟨hDnsMatch, trivial⟩
      | ok addrs =>
        refine ⟨?_, trivial⟩
        intro sa hsa
        rcases hDnsMatch sa hsa with hNil | hOk
        · cases hNil
        · exact hOk

/-- `test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect` is non-vacuously reachable. -/
theorem canReach_healthy_onHeadBeforeDnsAndVerifiedIpConnect :
    CanReach (test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect realBridgeTarget) := by
  have hAll := allPass_healthy_onHeadBeforeDnsAndVerifiedIpConnect
  dsimp only [test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect,
    CanReach, CanReachRun, AllPass, AllPassRun, Id,
    bind, Bind.bind, pure, Pure.pure, nondet, assume, assert] at hAll ⊢
  exact ⟨sampleHealthySys, sampleHealthySys_refines, cleanInitialWorld, cleanInitialWorld_wf,
    {}, ByteArray.empty, ByteArray.empty, 3, #[],
    hAll sampleHealthySys sampleHealthySys_refines cleanInitialWorld cleanInitialWorld_wf
      {} ByteArray.empty ByteArray.empty 3 #[]⟩

/-- `test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr` holds universally over all healthy OS implementations. -/
theorem allPass_healthy_admissionCapsUnderShortReadsAndEintr :
    AllPass (test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr realBridgeTarget) := by
  intro sys hRef w₀ hWf₀ cfg lfd cfd nowMs dlMs slots headBuf cRev events ⟨hSlotsLe, hHeadLe⟩
  let initSlot : ClientSlot Nat Unit := { phase := .handshake cfd headBuf dlMs }
  have hAcc := healthy_acceptNewClientsAux_laws sys hRef cfg.limits lfd nowMs MAX_ACCEPT_BATCH slots w₀ {} hWf₀ hSlotsLe
  have hHs := healthy_stepHandshakeSync_laws sys hRef cfg initSlot events cfd headBuf dlMs cRev nowMs w₀ {} hWf₀ hHeadLe rfl
  dsimp only [test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr, realBridgeTarget,
    listenPollEvents, acceptNewClients, AllPass, bind, pure, assume, assert] at hAcc hHs ⊢
  rcases hRA : (acceptNewClientsAux (instrumentSysOps sys) cfg.limits lfd nowMs MAX_ACCEPT_BATCH slots).run (w₀, {}) with ⟨slots', w₁, tr₁⟩
  rw [hRA] at hAcc
  rcases hRH : (stepHandshake (instrumentSysOps sys) cfg.limits
    (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy)
    (startDnsSync (instrumentSysOps sys) cfg.limits (Model.decideResolvedIps cfg.ipPolicy))
    initSlot events cfd headBuf dlMs cRev nowMs).run (w₀, {}) with ⟨⟨slot', ev'⟩, w₂, tr₂⟩
  rw [hRH] at hHs
  dsimp only at hAcc hHs ⊢
  refine ⟨rfl, ⟨hAcc.1, hAcc.2.1, hAcc.2.2.2⟩, ⟨hHs.1, ?_, hHs.2.2⟩, trivial⟩
  intro cfd' buf' dl' hPh
  obtain ⟨hLe', hLt', ⟨rxDelta, hRecvEq, hBufEq⟩, hProg'⟩ := hHs.2.1 cfd' buf' dl' hPh
  simp only [List.nil_append] at hRecvEq
  rw [← hRecvEq] at hBufEq
  exact ⟨hLe', hLt', hBufEq, hProg'⟩

/-- `test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr` is non-vacuously reachable. -/
theorem canReach_healthy_admissionCapsUnderShortReadsAndEintr :
    CanReach (test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr realBridgeTarget) := by
  have hAll := allPass_healthy_admissionCapsUnderShortReadsAndEintr
  dsimp only [test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr,
    CanReach, CanReachRun, AllPass, AllPassRun, Id,
    bind, Bind.bind, pure, Pure.pure, nondet, assume, assert] at hAll ⊢
  exact ⟨sampleHealthySys, sampleHealthySys_refines, cleanInitialWorld, cleanInitialWorld_wf,
    {}, 3, 4, 0, 1000, #[], ByteArray.empty, {}, #[],
    ⟨Nat.zero_le _, Nat.zero_le _⟩,
    hAll sampleHealthySys sampleHealthySys_refines cleanInitialWorld cleanInitialWorld_wf
      {} 3 4 0 1000 #[] ByteArray.empty {} #[] ⟨Nat.zero_le _, Nat.zero_le _⟩⟩

/-- `test_cproxy_healthy_relayByteConservationShortIoAndEintr` holds universally over all healthy OS implementations. -/
theorem allPass_healthy_relayByteConservationShortIoAndEintr :
    AllPass (test_cproxy_healthy_relayByteConservationShortIoAndEintr realBridgeTarget) := by
  intro sys hRef w₀ hWf₀ fd ufd fuel rb pipelined hCap
  have hRx := healthy_recvIntoRing_laws sys hRef fd fuel rb w₀ {} hWf₀ hCap
  have hTx := healthy_flushRingNonblock_laws sys hRef fd fuel rb w₀ {} hWf₀ hCap
  have hPipe := healthy_stepBidirectionalRelay_pipe_laws sys hRef fd ufd pipelined w₀ hWf₀
  have hRst := healthy_stepBidirectionalRelay_rst_laws sys hRef fd ufd w₀ hWf₀
  dsimp only [test_cproxy_healthy_relayByteConservationShortIoAndEintr, realBridgeTarget,
    AllPass, bind, pure, assume, assert] at hRx hTx hPipe hRst ⊢
  rcases hRR : (Relay.recvIntoRing (instrumentSysOps sys).net fd fuel rb).run (w₀, {}) with ⟨rxRes, w₁, tr₁⟩
  rw [hRR] at hRx
  rcases hRT : (Relay.flushRingNonblock (instrumentSysOps sys).net fd fuel rb).run (w₀, {}) with ⟨txRes, w₂, tr₂⟩
  rw [hRT] at hTx
  rcases hRP : (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
    (Relay.RelayState.init fd ufd pipelined) {} { pollout := true }).run (w₀, {}) with ⟨stPipe, w₃, tr₃⟩
  rw [hRP] at hPipe
  rcases hRS : (Relay.stepBidirectionalRelay (instrumentSysOps sys).net (instrumentSysOps sys).closeFd
    (Relay.RelayState.init fd ufd ByteArray.empty) {} { pollin := true, pollerr := true, pollhup := true }).run (w₀, {}) with ⟨stRst, w₄, tr₄⟩
  rw [hRS] at hRst
  dsimp only at hRx hTx hPipe hRst ⊢
  refine ⟨hRx.1, ?_⟩
  cases rxRes with
  | none =>
    rcases hRx.2.2.2 with ⟨eRx, heRxMem, hRxNil | hRxBad⟩
    · cases hRxNil
    · refine ⟨⟨eRx, heRxMem, hRxBad⟩, hTx.1, ?_⟩
      cases txRes with
      | none =>
        rcases hTx.2.2.2 with ⟨eTx, heTxMem, hTxNil | hTxNe⟩
        · cases hTxNil
        · exact ⟨⟨eTx, heTxMem, hTxNe⟩, hPipe, hRst, trivial⟩
      | some rbTx =>
        rcases hTx.2.2.2 with ⟨hLenTx, ⟨txDelta, hSentEq, hConsTx⟩, hProgTx⟩
        simp only [List.nil_append] at hSentEq
        rw [← hSentEq] at hConsTx
        exact ⟨⟨hLenTx, hConsTx, hProgTx⟩, hPipe, hRst, trivial⟩
  | some pair =>
    rcases pair with ⟨rb', eof⟩
    rcases hRx.2.2.2 with ⟨hLen, ⟨rxDelta, hRecvEq, hCons⟩, hProg⟩
    simp only [List.nil_append] at hRecvEq
    rw [← hRecvEq] at hCons
    refine ⟨⟨hLen, hCons, hProg⟩, hTx.1, ?_⟩
    cases txRes with
    | none =>
      rcases hTx.2.2.2 with ⟨eTx, heTxMem, hTxNil | hTxNe⟩
      · cases hTxNil
      · exact ⟨⟨eTx, heTxMem, hTxNe⟩, hPipe, hRst, trivial⟩
    | some rbTx =>
      rcases hTx.2.2.2 with ⟨hLenTx, ⟨txDelta, hSentEq, hConsTx⟩, hProgTx⟩
      simp only [List.nil_append] at hSentEq
      rw [← hSentEq] at hConsTx
      exact ⟨⟨hLenTx, hConsTx, hProgTx⟩, hPipe, hRst, trivial⟩

/-- `test_cproxy_healthy_relayByteConservationShortIoAndEintr` is non-vacuously reachable. -/
theorem canReach_healthy_relayByteConservationShortIoAndEintr :
    CanReach (test_cproxy_healthy_relayByteConservationShortIoAndEintr realBridgeTarget) := by
  have hAll := allPass_healthy_relayByteConservationShortIoAndEintr
  dsimp only [test_cproxy_healthy_relayByteConservationShortIoAndEintr,
    CanReach, CanReachRun, AllPass, AllPassRun, Id,
    bind, Bind.bind, pure, Pure.pure, nondet, assume, assert] at hAll ⊢
  exact ⟨sampleHealthySys, sampleHealthySys_refines, cleanInitialWorld, cleanInitialWorld_wf,
    3, 4, 2, {}, ByteArray.empty, Nat.zero_le _,
    hAll sampleHealthySys sampleHealthySys_refines cleanInitialWorld cleanInitialWorld_wf
      3 4 2 {} ByteArray.empty (Nat.zero_le _)⟩

/-- `test_cproxy_healthy_withProxyAndStopClosesAllFds` holds universally over all healthy OS implementations. -/
theorem allPass_healthy_withProxyAndStopClosesAllFds :
    AllPass (test_cproxy_healthy_withProxyAndStopClosesAllFds realBridgeTarget) := by
  intro sys hRef w₀ ⟨hWf₀, hNd₀⟩ cfg vcfg lfd wakeR wakeW slots events
  have h := healthy_stopProxy_and_withProxy_laws sys hRef w₀ cfg vcfg lfd wakeR wakeW slots events hWf₀ hNd₀
  dsimp only [test_cproxy_healthy_withProxyAndStopClosesAllFds, AllPass, AllPassRun, Id,
    bind, Bind.bind, pure, Pure.pure, assume, assert] at h ⊢
  let entry0 : SyncProxyEntry Nat :=
    { handleId := freshSyncHandleId w₀.proxyTable
      port := 8080
      vcfg := vcfg
      listenFd := lfd
      wakeR := wakeR
      wakeW := wakeW
      slots := slots
      events := events }
  let tbl0 : SyncProxyTable Nat :=
    { nextHandleId := freshSyncHandleId w₀.proxyTable + 1
      entries := entry0 :: w₀.proxyTable.entries }
  let wAct : HealthySysWorld := { w₀ with proxyTable := tbl0 }
  rcases hR1 : ((realBridgeTarget.mkRawOps (instrumentSysOps sys)).stopProxy
    { handleId := freshSyncHandleId w₀.proxyTable, port := 8080 }).run (wAct, {}) with ⟨stopRes, w₁, tr₁⟩
  dsimp only [wAct, tbl0, entry0] at hR1
  rw [hR1] at h
  dsimp only at h ⊢
  rcases hR2 : ((realBridgeTarget.mkRawOps (instrumentSysOps sys)).stopProxy
    { handleId := freshSyncHandleId w₀.proxyTable, port := 8080 }).run (w₁, tr₁) with ⟨dblRes, w₁d, tr₁d⟩
  rw [hR2] at h
  dsimp only at h ⊢
  rcases hR3 : (Model.withProxyModel (realBridgeTarget.mkRawOps (instrumentSysOps sys)) cfg
    (fun p => StateT.pure (.ok p.port))).run (w₀, {}) with ⟨_, w₂, tr₂⟩
  rw [hR3] at h
  dsimp only at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, trivial⟩

/-- `test_cproxy_healthy_withProxyAndStopClosesAllFds` is non-vacuously reachable. -/
theorem canReach_healthy_withProxyAndStopClosesAllFds :
    CanReach (test_cproxy_healthy_withProxyAndStopClosesAllFds realBridgeTarget) := by
  have hAll := allPass_healthy_withProxyAndStopClosesAllFds
  dsimp only [test_cproxy_healthy_withProxyAndStopClosesAllFds,
    CanReach, CanReachRun, AllPass, AllPassRun, Id,
    bind, Bind.bind, pure, Pure.pure, nondet, assume, assert] at hAll ⊢
  exact ⟨sampleHealthySys, sampleHealthySys_refines, cleanInitialWorld,
    ⟨cleanInitialWorld_wf, cleanInitialWorld_nodup⟩, {}, { config := {} }, 3, 4, 5, #[], #[],
    hAll sampleHealthySys sampleHealthySys_refines cleanInitialWorld
      ⟨cleanInitialWorld_wf, cleanInitialWorld_nodup⟩ {} { config := {} } 3 4 5 #[] #[]⟩

/-- `test_cproxy_healthy_pollAndStepTickAndFallbackConnect` holds universally over all healthy OS implementations. -/
theorem allPass_healthy_pollAndStepTickAndFallbackConnect :
    AllPass (test_cproxy_healthy_pollAndStepTickAndFallbackConnect realBridgeTarget) := by
  intro sys hRef w₀ ⟨hWf₀, hNd₀⟩ cfg wakeR lfd cfd ufd host port candidates candIdx nowMs dlMs pipelined replyBytes cRev uRev stopFlag slots events ⟨hSlotsLe, hCandsAllow⟩
  let connSlot : ClientSlot Nat Unit :=
    { phase := .connecting cfd ufd host port candidates candIdx none dlMs
      pipelined := pipelined
      target? := some (host, port) }
  let closeSlot : ClientSlot Nat Unit :=
    { phase := .closingReply (some cfd) replyBytes 0 false 0 dlMs }
  have hBatch := buildPollBatchSync_laws wakeR lfd cfg.limits.maxConcurrentTunnels nowMs slots
  have hConn := healthy_stepConnecting_laws sys hRef cfg connSlot events cfd ufd host port candidates candIdx none dlMs cRev uRev nowMs w₀ {} hWf₀
  have hClose := healthy_stepClosingReply_laws sys hRef closeSlot (some cfd) replyBytes 0 false 0 dlMs cRev nowMs w₀ {} hWf₀
  have hTick := healthy_pollAndStepTickSync_laws sys hRef cfg stopFlag wakeR lfd slots events w₀ hWf₀ hSlotsLe
  dsimp only [test_cproxy_healthy_pollAndStepTickAndFallbackConnect, realBridgeTarget,
    stepSyncSlot, stepSlotM, AllPass, bind, pure, assume, assert] at hBatch hConn hClose hTick ⊢
  rcases hB : buildPollBatchSync wakeR lfd cfg.limits.maxConcurrentTunnels nowMs slots with ⟨reqs, indices, timeout?⟩
  rw [hB] at hBatch
  rcases hRC : (stepConnecting (instrumentSysOps sys) cfg.limits connSlot events cfd ufd host port candidates candIdx none dlMs cRev uRev nowMs).run (w₀, {}) with ⟨⟨connSlot', connEvs'⟩, wC, trC⟩
  rw [hRC] at hConn
  dsimp only [Functor.map, StateT.map, StateT.bind, StateT.pure, StateT.run] at hClose hTick ⊢
  rcases hRCl : stepClosingReply (instrumentSysOps sys) closeSlot (some cfd) replyBytes 0 false 0 dlMs cRev nowMs (w₀, {}) with ⟨closeSlot', wCl, trCl⟩
  rw [hRCl] at hClose
  rcases hRT : pollAndStepTickSync (instrumentSysOps sys) cfg.limits (Model.decideConnectHead cfg) (Model.decideResolvedIps cfg.ipPolicy) stopFlag wakeR lfd slots events (w₀, {}) with ⟨tickOut, wT, trT⟩
  rw [hRT] at hTick
  dsimp only [hRCl, hRT] at hBatch hConn hClose hTick ⊢
  refine ⟨hBatch, ?_, ?_, hTick, trivial⟩
  · refine ⟨hConn.1, hConn.2.2.1, ?_, ?_, fun hCE => hConn.2.2.2.2.2.1 hCE hNd₀, hConn.2.2.2.2.2.2⟩
    · intro sa hsa
      rcases hConn.2.2.2.1 hCandsAllow sa hsa with hNil | hOk
      · cases hNil
      · exact hOk
    · intro st hRel
      exact hConn.2.2.2.2.1 st hRel (fun hc => nomatch hc)
  · obtain ⟨hToDone, hDoneCl⟩ := hClose.2.2 cfd rfl
    exact ⟨hClose.1, hToDone, hDoneCl hNd₀⟩

/-- `test_cproxy_healthy_pollAndStepTickAndFallbackConnect` is non-vacuously reachable. -/
theorem canReach_healthy_pollAndStepTickAndFallbackConnect :
    CanReach (test_cproxy_healthy_pollAndStepTickAndFallbackConnect realBridgeTarget) := by
  have hAll := allPass_healthy_pollAndStepTickAndFallbackConnect
  dsimp only [test_cproxy_healthy_pollAndStepTickAndFallbackConnect,
    CanReach, CanReachRun, AllPass, AllPassRun, Id,
    bind, Bind.bind, pure, Pure.pure, nondet, assume, assert] at hAll ⊢
  exact ⟨sampleHealthySys, sampleHealthySys_refines, cleanInitialWorld,
    ⟨cleanInitialWorld_wf, cleanInitialWorld_nodup⟩,
    {}, 3, 4, 5, 6, "example.com", 443, #[], 0, 0, 1000, ByteArray.empty, ByteArray.empty,
    {}, {}, false, #[], #[],
    ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩,
    hAll sampleHealthySys sampleHealthySys_refines cleanInitialWorld
      ⟨cleanInitialWorld_wf, cleanInitialWorld_nodup⟩
      {} 3 4 5 6 "example.com" 443 #[] 0 0 1000 ByteArray.empty ByteArray.empty
      {} {} false #[] #[] ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩⟩

end LeanSwe.ConnectProxy.Proofs
