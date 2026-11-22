import Core.NondetTest
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge
import LeanSwe.ConnectProxy.HealthySys
import LeanSwe.ConnectProxy.SpecTests
import LeanSwe.ConnectProxy.Proofs.HealthyWitness

/-! Compile-time negative specification mutants for `LeanSwe.ConnectProxy`. -/

namespace LeanSwe.ConnectProxy

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.ConnectProxy.Model

private def referencePureApi : ConnectProxyApi :=
  { parseIpAddr := Model.parseIpAddr
    parseIpPrefix := Model.parseIpPrefix
    isGlobalIp := Model.isGlobalIp
    allowsIp := Model.allowsIp
    parseConnectRequest := Model.parseConnectRequest
    validateConfig := Model.validateConfig
    withProxy := fun _ _ => pure (.error { kind := .ioError, message := "unused" }) }

private def referenceMkApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (ops : RawConnectProxyOpsM m) : ConnectProxyApiM m :=
  { parseIpAddr := Model.parseIpAddr
    parseIpPrefix := Model.parseIpPrefix
    isGlobalIp := Model.isGlobalIp
    allowsIp := Model.allowsIp
    parseConnectRequest := Model.parseConnectRequest
    validateConfig := Model.validateConfig
    withProxy := fun cfg action => Model.withProxyModel ops cfg action }

example : ¬ Core.AllPass (test_cproxy_parseIpAddr_validAndRejectsWildcardsOctalInvalid
    { referencePureApi with
      parseIpAddr := fun s =>
        if s == "10.1*" then .ok (.v4 0x0a010000) else Model.parseIpAddr s }) := by
  intro h
  have h0 := (h "10.1*").2.1
  revert h0
  decide

example : ¬ Core.AllPass (test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority
    { referencePureApi with
      parseConnectRequest := fun raw =>
        if raw == "GET http://api.anthropic.com/ HTTP/1.1\r\nHost: api.anthropic.com\r\n\r\n".toUTF8 then
          .ok { host := "api.anthropic.com", port := 80 }
        else
          Model.parseConnectRequest raw }) := by
  intro h
  have h0 := h ("GET http://api.anthropic.com/ HTTP/1.1\r\nHost: api.anthropic.com\r\n\r\n".toUTF8)
  dsimp [test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority, referencePureApi, bind, assert] at h0
  have hFalse : (Model.parseConnectRequest "GET http://api.anthropic.com/ HTTP/1.1\r\nHost: api.anthropic.com\r\n\r\n".toUTF8).isOk = false := by decide
  rw [← h0.1] at hFalse
  revert hFalse
  decide

example : ¬ Core.AllPass (test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal
    (fun _ _ _ => .dial { host := "api.anthropic.com", port := 443, primaryIp := .v4 0x08080808 })) := by
  intro h
  dsimp [test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal, Core.AllPass, bind, assert] at h
  rcases h.2.1 with ⟨_, hSub⟩
  cases hSub

example : ¬ Core.AllPass (test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal
    (fun cfg head resolve =>
      if head == "CONNECT api.anthropic.com:8443 HTTP/1.1\r\n\r\n".toUTF8 then
        .dial { host := "api.anthropic.com", port := 8443, primaryIp := .v4 0x08080808 }
      else
        Model.authorizeConnect cfg head resolve)) := by
  intro h
  dsimp [test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal, Core.AllPass, bind, assert] at h
  rcases h.2.2.2.2.1 with ⟨_, hPort⟩
  cases hPort

example : ¬ Core.AllPass (test_cproxy_isGlobalIp_completeIanaRfc6890Table
    { referencePureApi with
      isGlobalIp := fun ip =>
        if ip == .v4 0x64400001 || ip == .v4 0xe0000001 then true else Model.isGlobalIp ip }) := by
  intro h
  have h0 := (h (.v4 0x64400001)).1
  revert h0
  decide

example : ¬ Core.AllPass (test_cproxy_parseIpPrefix_exactBitmaskAndRejectsWildcards
    { referencePureApi with
      parseIpPrefix := fun s =>
        if s == "10.1*" then .ok (.v4 0x0a000000 8) else Model.parseIpPrefix s }) := by
  intro h
  have h0 := (h "10.1*").2.1
  revert h0
  decide

example : ¬ Core.AllPass (test_cproxy_allowsIp_banAlwaysOverridesAllow
    { referencePureApi with
      allowsIp := fun policy ip =>
        if policy.extraAllows.toList.any (fun p => prefixContains p ip) then true
        else Model.allowsIp policy ip }) := by
  intro h
  have h0 := (h {} (.v4 0x08080808)).2.1
  revert h0
  decide

example : ¬ Core.AllPass (test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan
    { referencePureApi with
      allowsIp := fun policy ip =>
        let inBase := match policy.base with | .publicOnly => Model.isGlobalIp ip | .empty => false
        let inExtra := policy.extraAllows.toList.any (fun p => prefixContains p ip)
        (inBase || inExtra) && !policy.extraBans.toList.any (fun b => prefixContains b ip) }) := by
  intro h
  have h0 := h 0xa9fea9fe 0 1 0 0x01000001 0x08080808 0 0 0 1 0 (.v4 0xa9fea9fe 32) (by decide)
  dsimp [test_cproxy_allowsIp_ipv4InIpv6NeverBypassesBan, bind, assert] at h0
  have h1 := h0.2.2.2.1
  revert h1
  decide

example : ¬ Core.AllPass (test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly
    (fun _ _ resolve =>
      match resolve "api.example.com" with
      | .ok ips =>
        match ips.toList with
        | first :: rest => .dial { host := "api.example.com", port := 443, primaryIp := first, fallbackIps := rest.toArray }
        | [] => .deny (some "api.example.com") (some 443) "empty"
      | .error e => .dnsFailed "api.example.com" 443 e)) := by
  intro h
  dsimp [test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly, Core.AllPass, bind, assert] at h
  have h1 := h.1
  revert h1
  decide

example : ¬ Core.AllPass (test_cproxy_validateConfig_limitsPortZeroAndIdempotence
    { referencePureApi with
      validateConfig := fun cfg =>
        if cfg.listenPort == 0 then .error { kind := .invalidInput, message := "rejected 0" }
        else Model.validateConfig cfg }) := by
  intro h
  have h0 := (h {}).2.1
  dsimp [referencePureApi] at h0
  cases h0

example : ¬ Core.AllPass (test_cproxy_validateConfig_limitsPortZeroAndIdempotence
    { referencePureApi with
      validateConfig := fun cfg => .ok { config := cfg } }) := by
  intro h
  have h0 := (h { limits := { maxHeaderBytes := 0 } }).1
  have hFalse : (Model.validateConfig { limits := { maxHeaderBytes := 0 } }).isOk = false := by decide
  rw [← h0] at hFalse
  revert hFalse
  decide

example : ¬ Core.AllPass (test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal
    (fun cfg head resolve =>
      Model.authorizeConnect { cfg with limits := { cfg.limits with maxHeaderBytes := 1000000 } } head resolve)) := by
  intro h
  dsimp [test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal, Core.AllPass, bind, assert] at h
  rcases h.2.2.2.2.2.2.1 with ⟨_, _, _, hBig⟩
  have hEval : Model.authorizeConnect
      { allowedTargets := #[{ host := "api.anthropic.com", port := 443 }], limits := { maxHeaderBytes := 1000000 } }
      ("CONNECT api.anthropic.com:443 HTTP/1.1\r\nX-Pad: 012345678901234567890123456789\r\n\r\n").toUTF8
      (fun _ => .error "DNS SHOULD NOT BE QUERIED") =
      .dnsFailed "api.anthropic.com" 443 "DNS SHOULD NOT BE QUERIED" := by decide
  rw [hEval] at hBig
  cases hBig

example : ¬ Core.AllPass (test_cproxy_withProxy_invalidConfig_hasZeroSideEffects
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun _ _ => do
          let _ ← ops.startProxy { config := {} } (fun _ => .deny none none "bad") (fun _ _ _ => .deny "bad")
          return .error { kind := .invalidInput, message := "touched raw ops" } })) := by
  intro h
  have h0 := h {} { limits := { maxHeaderBytes := 0 } }
  dsimp [test_cproxy_withProxy_invalidConfig_hasZeroSideEffects] at h0
  have hVal : Model.validateConfig { limits := { maxHeaderBytes := 0 } } =
      .error { kind := .invalidInput, message := "ProxyLimits.maxHeaderBytes must be greater than 0" } := rfl
  rw [hVal] at h0
  dsimp [mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0
  have hEq := congrArg (·.startCalls) h0.1.2
  revert hEq
  decide

example : ¬ Core.AllPass (test_cproxy_withProxy_universalConfigAndLifecycleEquivalence
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun cfg action =>
          Model.withProxyModel ops { cfg with listenPort := 0 } action })) := by
  intro h
  have h0 := h {} { listenPort := 8080 } 1
  dsimp [test_cproxy_withProxy_universalConfigAndLifecycleEquivalence, Model.withProxyModel,
    mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
    tryFinally', MonadFinally.tryFinally', assert] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_cproxy_withProxy_universalConfigAndLifecycleEquivalence
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun cfg action => do
          match Model.validateConfig cfg with
          | .error e => return .error e
          | .ok vcfg =>
            match ← ops.startProxy vcfg (Model.decideConnectHead vcfg.config) (Model.decideResolvedIps vcfg.config.ipPolicy) with
            | .error e =>
              let _ ← ops.stopProxy { handleId := 999, port := 1 }
              return .error e
            | .ok proxy =>
              let (actRes, stopRes) ← tryFinally' (action proxy) (fun _ => ops.stopProxy proxy)
              match actRes, stopRes with
              | .error ae, _ => return .error ae
              | .ok _, .error se => return .error se
              | .ok a, .ok evs => return .ok (a, evs) })) := by
  intro h
  let sFail : MockProxySimState := { failStartWith := some { kind := .addressInUse, message := "in use" } }
  have h0 := h sFail {} 1
  dsimp [test_cproxy_withProxy_universalConfigAndLifecycleEquivalence, sFail,
    mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0
  have hStop := h0.2.1.2.2.1
  revert hStop
  decide

example : ¬ Core.AllPass (test_cproxy_withProxy_universalConfigAndLifecycleEquivalence
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun cfg action => do
          match Model.validateConfig cfg with
          | .error e => return .error e
          | .ok vcfg =>
            match ← ops.startProxy vcfg (Model.decideConnectHead vcfg.config) (Model.decideResolvedIps vcfg.config.ipPolicy) with
            | .error e => return .error e
            | .ok proxy =>
              let (actRes, stopRes) ← tryFinally' (action proxy) (fun _ => ops.stopProxy proxy)
              match actRes, stopRes with
              | .error ae, _ => return .error ae
              | .ok a, .error _ => return .ok (a, #[])
              | .ok a, .ok evs => return .ok (a, evs) })) := by
  intro h
  let sStopFail : MockProxySimState := { failStopWith := some { kind := .ioError, message := "stop failed" } }
  have h0 := h sStopFail {} 1
  dsimp [test_cproxy_withProxy_universalConfigAndLifecycleEquivalence, sStopFail,
    mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
    tryFinally', MonadFinally.tryFinally', assert] at h0
  cases h0.2.1.1

example : ¬ Core.AllPass (test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun cfg action => do
          match Model.validateConfig cfg with
          | .error e => return .error e
          | .ok vcfg =>
            let dropFallbacks : String → UInt16 → Array IpAddr → ResolveDecision := fun hst prt ips =>
              match Model.decideResolvedIps vcfg.config.ipPolicy hst prt ips with
              | .deny r => .deny r
              | .dial primary _ => .dial primary #[]
            match ← ops.startProxy vcfg (Model.decideConnectHead vcfg.config) dropFallbacks with
            | .error e => return .error e
            | .ok proxy =>
              let (actRes, stopRes) ← tryFinally' (action proxy) (fun _ => ops.stopProxy proxy)
              match actRes, stopRes with
              | .error ae, _ => return .error ae
              | .ok _, .error se => return .error se
              | .ok a, .ok evs => return .ok (a, evs) })) := by
  intro h
  have h0 := h 7
  dsimp [test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory,
    mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
    tryFinally', MonadFinally.tryFinally', assert] at h0
  have hDialed := h0.2.2.1
  revert hDialed
  decide

example : ¬ Core.AllPass (test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun cfg action => do
          let vres ← (referenceMkApiM ops).withProxy cfg action
          return vres.map (fun (v, _) => (v, #[])) })) := by
  intro h
  have h0 := h 7
  dsimp [test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory, referenceMkApiM,
    Model.withProxyModel, mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
    tryFinally', MonadFinally.tryFinally', assert] at h0
  have hEv := h0.2.2.2.1.2
  revert hEv
  decide

example : ¬ Core.AllPass (test_cproxy_withProxy_callbackError_tearsDownAndPreservesError
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun cfg action => do
          match Model.validateConfig cfg with
          | .error e => return .error e
          | .ok vcfg =>
            match ← ops.startProxy vcfg (Model.decideConnectHead vcfg.config) (Model.decideResolvedIps vcfg.config.ipPolicy) with
            | .error e => return .error e
            | .ok proxy =>
              match ← action proxy with
              | .error ae => return .error ae
              | .ok a =>
                match ← ops.stopProxy proxy with
                | .error se => return .error se
                | .ok evs => return .ok (a, evs) })) := by
  intro h
  have h0 := h {} { kind := .ioError, message := "callback failed" } rfl
  dsimp [test_cproxy_withProxy_callbackError_tearsDownAndPreservesError,
    mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0
  have hStop := h0.2.1.2
  revert hStop
  decide

example : ¬ Core.AllPass (test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown
    (fun ops =>
      { referenceMkApiM ops with
        withProxy := fun cfg action => do
          match Model.validateConfig cfg with
          | .error e => return .error e
          | .ok vcfg =>
            match ← ops.startProxy vcfg (Model.decideConnectHead vcfg.config) (Model.decideResolvedIps vcfg.config.ipPolicy) with
            | .error e => return .error e
            | .ok proxy =>
              let actRes ← action proxy
              let stopRes ← ops.stopProxy proxy
              match actRes, stopRes with
              | .error ae, _ => return .error ae
              | .ok _, .error se => return .error se
              | .ok a, .ok evs => return .ok (a, evs) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown,
    mockRawProxyOpsEx, mockRawProxyOps, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    StateT.run, bind, pure, throw, throwThe, MonadExceptOf.throw, assert] at h0
  have hStop := h0.2.1.2
  revert hStop
  decide

example : ¬ Core.AllPass (test_cproxy_healthy_listenerBindLoopbackOnlyAndPortLaws
    { HealthySys.realBridgeTarget with
      createListener := fun _ _ => pure (.ok (3, 4, 5, 0)) }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    ⟨rfl, List.nodup_nil⟩ { config := {} }
  exact h0.2.2.2.1.1 rfl

example : ¬ Core.AllPass (test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect
    { HealthySys.realBridgeTarget with
      handleCompleteHeadSync := fun _ _ _ _ slot evs _ _ _ =>
        fun (w, tr) => ((slot, evs), (w, { tr with dnsQueries := tr.dnsQueries.push "leaked.invalid" })) }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    rfl { limits := { maxHeaderBytes := 0 } } (ByteArray.mk #[65]) ByteArray.empty 3 #[]
  have hDec : Model.decideConnectHead { limits := { maxHeaderBytes := 0 } } (ByteArray.mk #[65]) =
    .deny none none "request head exceeds maxHeaderBytes" := rfl
  dsimp [test_cproxy_healthy_onHeadBeforeDnsAndVerifiedIpConnect, StateT.run, bind, assert] at h0
  rw [hDec] at h0
  have hEq : (#["leaked.invalid"] : Array String) = #[] := h0.2.2.1.1
  cases hEq

example : ¬ Core.AllPass (test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr
    { HealthySys.realBridgeTarget with
      listenPollinEnabled := fun _ _ => true }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    rfl { limits := { maxConcurrentTunnels := 0 } } 3 4 0 1000 #[] ByteArray.empty {} #[]
    ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hPollin : true = decide (0 < 0) := h0.1
  cases hPollin

example : ¬ Core.AllPass (test_cproxy_healthy_admissionCapsUnderShortReadsAndEintr
    { HealthySys.realBridgeTarget with
      stepHandshakeSync := fun _ _ _ _ slot evs cfd headBuf dl _ _ =>
        pure ({ slot with phase := .handshake cfd headBuf dl }, evs) }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    rfl { limits := { maxHeaderBytes := 1 } } 3 4 0 1000 #[] (ByteArray.mk #[65]) { pollin := true } #[]
    ⟨Nat.zero_le _, Nat.le_refl 1⟩
  have hStay := (h0.2.2.1.2.1 4 (ByteArray.mk #[65]) 1000 rfl).2.1 rfl
  exact Nat.lt_irrefl 1 hStay

example : ¬ Core.AllPass (test_cproxy_healthy_relayByteConservationShortIoAndEintr
    { HealthySys.realBridgeTarget with
      recvIntoRing := fun _ _ _ _ => pure (some ({ buf := ByteArray.mk #[42], off := 0 }, false)) }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    rfl 3 4 0 {} ByteArray.empty (Nat.zero_le _)
  have hCons : ({ buf := ByteArray.mk #[42], off := 0 } : NetRelay.RingBuf).toList =
    ({} : NetRelay.RingBuf).toList ++ (#[] : Array UInt8).toList := h0.2.1.2.1
  revert hCons
  decide

example : ¬ Core.AllPass (test_cproxy_healthy_relayByteConservationShortIoAndEintr
    { HealthySys.realBridgeTarget with
      recvIntoRing := fun _ _ _ _ => pure none }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    rfl 3 4 0 {} ByteArray.empty (Nat.zero_le _)
  rcases h0.2.1 with ⟨_, hMem, _⟩
  cases hMem

example : ¬ Core.AllPass (test_cproxy_healthy_relayByteConservationShortIoAndEintr
    { HealthySys.realBridgeTarget with
      stepBidirectionalRelay := fun _ st _ _ =>
        pure { st with pendingPrefix := ByteArray.empty, pendingOff := 0 } }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    rfl 3 4 0 {} (ByteArray.mk #[88]) (Nat.zero_le _)
  have hPipe := (h0.2.2.2.2.1.2.1 rfl).1
  revert hPipe
  decide

example : ¬ Core.AllPass (test_cproxy_healthy_relayByteConservationShortIoAndEintr
    { HealthySys.realBridgeTarget with
      stepBidirectionalRelay := fun _ st _ uRev =>
        if uRev.pollerr then pure {} else pure st }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    rfl 3 4 0 {} ByteArray.empty (Nat.zero_le _)
  rcases h0.2.2.2.2.2.1.2 with ⟨_, hMem, _⟩ | ⟨hFd, _⟩
  · cases hMem
  · cases hFd

example : ¬ Core.AllPass (test_cproxy_healthy_withProxyAndStopClosesAllFds
    { HealthySys.realBridgeTarget with
      mkRawOps := fun _ =>
        { startProxy := fun _ _ _ => pure (.error { kind := .ioError, message := "unused" })
          stopProxy := fun _ => fun (w, tr) =>
            (.ok #[], ({ w with proxyTable := { w.proxyTable with entries := [] } }, tr))
          activeProxyCount := fun (w, tr) => (w.proxyTable.entries.length, (w, tr))
          mapRawError := Model.mapRawErrorPure } }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    ⟨rfl, List.nodup_nil⟩ {} { config := {} } 3 4 5 #[] #[]
  have hClosed := (h0.2.2.1 3 (List.Mem.head _)).1
  cases hClosed

example : ¬ Core.AllPass (test_cproxy_healthy_pollAndStepTickAndFallbackConnect
    { HealthySys.realBridgeTarget with
      pollAndStepTickSync := fun _ _ _ _ _ _ _ _ _ =>
        fun (w, tr) => (.stopOrFatal, (w, { tr with pollOutcomes := #[some LinuxSyscall.Errno.EINTR] })) }) := by
  intro h
  have h0 := h Proofs.sampleHealthySys Proofs.sampleHealthySys_refines
    { filesEnv := { state := { LinuxSyscall.Files.FilesState.initial with fds := [] } } }
    ⟨rfl, List.nodup_nil⟩ {} 3 4 5 6 "example.com" 443 #[] 0 0 1000
    ByteArray.empty ByteArray.empty {} {} false #[] #[]
    ⟨Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hRetry : SysBridge.PollTickOutcome.stopOrFatal = .retryEintr :=
    h0.2.2.2.1.2.1.mpr rfl
  cases hRetry

end LeanSwe.ConnectProxy
