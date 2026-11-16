import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Impl
import LeanSwe.ConnectProxy.SpecTests

namespace LeanSwe.ConnectProxy.Proofs

open Core
open Core.NondetTest
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Raw
open LeanSwe.ConnectProxy.Model

private theorem sappend_nonempty (a b : String) (hb : b ≠ "") : a ++ b ≠ "" := by
  intro h
  exact hb (String.append_eq_empty_iff.mp h).2

private theorem normalizeTargetHost_err_props {raw : String} {err : ProxyError}
    (h : normalizeTargetHost raw = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold normalizeTargetHost at h
  dsimp only at h
  split at h
  · injection h with hE; subst hE; exact ⟨rfl, by decide⟩
  · split at h
    · injection h with hE; subst hE; exact ⟨rfl, sappend_nonempty _ _ (by decide)⟩
    · split at h
      · split at h
        · split at h
          · split at h
            · injection h with hE; subst hE; exact ⟨rfl, sappend_nonempty _ _ (by decide)⟩
            · split at h
              · cases h
              · injection h with hE; subst hE; exact ⟨rfl, sappend_nonempty _ _ (by decide)⟩
          · injection h with hE; subst hE; exact ⟨rfl, sappend_nonempty _ _ (by decide)⟩
        · injection h with hE; subst hE; exact ⟨rfl, sappend_nonempty _ _ (by decide)⟩
      · split at h
        · cases h
        · split at h
          · cases h
          · injection h with hE; subst hE; exact ⟨rfl, sappend_nonempty _ _ (by decide)⟩

private theorem mapExceptList_err_props :
    ∀ (rs : List TargetRule) {err : ProxyError},
      mapExceptList normalizeTargetRule rs = .error err →
      err.kind = .invalidInput ∧ err.message ≠ ""
  | [], _, h => nomatch h
  | r :: rest, _, h => by
    simp only [mapExceptList, bind, Except.bind] at h
    cases hr : normalizeTargetRule r with
    | error er =>
      rw [hr] at h; injection h with hE; subst hE
      unfold normalizeTargetRule at hr
      split at hr
      · injection hr with hE; subst hE; exact ⟨rfl, by decide⟩
      · split at hr
        · cases hr
        · rename_i eh hHost
          injection hr with hE; subst hE
          exact normalizeTargetHost_err_props hHost
    | ok nr =>
      rw [hr] at h; dsimp at h
      cases hRest : mapExceptList normalizeTargetRule rest with
      | error er => rw [hRest] at h; injection h with hE; subst hE; exact mapExceptList_err_props rest hRest
      | ok nrs => rw [hRest] at h; cases h

private theorem validateConfig_err_props {cfg : ProxyConfig} {err : ProxyError}
    (h : validateConfig cfg = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold validateConfig at h
  split at h
  · injection h with hE; subst hE; exact ⟨rfl, by decide⟩
  · split at h
    · injection h with hE; subst hE; exact ⟨rfl, by decide⟩
    · split at h
      · injection h with hE; subst hE; exact ⟨rfl, by decide⟩
      · split at h
        · injection h with hE; subst hE; exact ⟨rfl, by decide⟩
        · split at h
          · injection h with hE; subst hE; exact ⟨rfl, by decide⟩
          · split at h
            · injection h with hE; subst hE; exact ⟨rfl, by decide⟩
            · simp only [bind, Except.bind] at h
              split at h
              · rename_i e' hMap
                injection h with hE; subst hE
                exact mapExceptList_err_props _ hMap
              · cases h

private theorem validateConfig_props {cfg : ProxyConfig} {vcfg : ValidProxyConfig}
    (h : validateConfig cfg = .ok vcfg) :
    vcfg.config.listenPort = cfg.listenPort ∧
    (vcfg.config.limits.maxHeaderBytes == 0 ||
     vcfg.config.limits.headerTimeoutMs == 0 ||
     vcfg.config.limits.connectTimeoutMs == 0 ||
     vcfg.config.limits.maxConcurrentTunnels == 0) = false := by
  unfold validateConfig at h
  split at h <;> try cases h
  rename_i h1
  split at h <;> try cases h
  rename_i h2
  split at h <;> try cases h
  rename_i h3
  split at h <;> try cases h
  rename_i h4
  split at h <;> try cases h
  split at h <;> try cases h
  simp only [bind, Except.bind] at h
  split at h <;> cases h
  simp only [Bool.not_eq_true] at h1 h2 h3 h4
  simp [h1, h2, h3, h4]

private theorem foldl_max_ge_init : ∀ (xs : List Nat) (init : Nat),
    init ≤ xs.foldl Nat.max init
  | [], init => Nat.le_refl init
  | z :: zs, init =>
    Nat.le_trans (Nat.le_max_left init z) (foldl_max_ge_init zs (Nat.max init z))

private theorem foldl_max_ge : ∀ (xs : List Nat) (init x : Nat),
    x ∈ xs → x ≤ xs.foldl Nat.max init
  | [], _, _, h => nomatch h
  | y :: ys, init, x, h => by
    simp only [List.foldl]
    rcases List.mem_cons.mp h with rfl | hMem
    · exact Nat.le_trans (Nat.le_max_right init x) (foldl_max_ge_init ys (Nat.max init x))
    · exact foldl_max_ge ys (Nat.max init y) x hMem

private theorem not_contains_fresh_hid (xs : List Nat) (nextId : Nat) :
    (!(Nat.max nextId ((xs.foldl Nat.max 0) + 1) :: xs).contains
      (Nat.max nextId ((xs.foldl Nat.max 0) + 1))) = false := by
  simp

private theorem filter_fresh_hid (xs : List Nat) (nextId : Nat) :
    ((Nat.max nextId ((xs.foldl Nat.max 0) + 1) :: xs).filter
      (· != Nat.max nextId ((xs.foldl Nat.max 0) + 1))) = xs := by
  have hSelf : (Nat.max nextId ((xs.foldl Nat.max 0) + 1) !=
      Nat.max nextId ((xs.foldl Nat.max 0) + 1)) = false :=
    bne_self_eq_false _
  simp only [List.filter, hSelf]
  rw [List.filter_eq_self]
  intro x hx
  have hle : x ≤ xs.foldl Nat.max 0 := foldl_max_ge xs 0 x hx
  have hlt : x < Nat.max nextId ((xs.foldl Nat.max 0) + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hle) (Nat.le_max_right _ _)
  exact bne_iff_ne.mpr (Nat.ne_of_lt hlt)

private theorem runSimulatedAttempts_size
    (dnsTable : List (String × DnsSimResult))
    (failConnectIps : List IpAddr)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision) :
    ∀ (attempts : List SimulatedClientAttempt)
      (evs : Array ConnectEvent) (qs : Array String) (ds : Array (IpAddr × UInt16)),
      (runSimulatedAttempts dnsTable failConnectIps onHead onResolved attempts evs qs ds).1.size =
        evs.size + attempts.length
  | [], evs, qs, ds => by simp [runSimulatedAttempts]
  | a :: rest, evs, qs, ds => by
    simp only [runSimulatedAttempts, List.length_cons]
    rw [runSimulatedAttempts_size dnsTable failConnectIps onHead onResolved rest]
    simp only [Array.size_push]
    omega

/-- `test_cproxy_withProxy_invalidConfig_hasZeroSideEffects` holds universally for `Internal.mkApiM`. -/
theorem allPass_withProxy_invalidConfig_hasZeroSideEffects :
    AllPass (test_cproxy_withProxy_invalidConfig_hasZeroSideEffects Internal.mkApiM) := by
  intro s₀ cfg
  dsimp [test_cproxy_withProxy_invalidConfig_hasZeroSideEffects, Internal.mkApiM, AllPass, bind, assume, assert]
  cases hVal : Model.validateConfig cfg with
  | ok _ =>
    intro hFalse
    nomatch hFalse
  | error err =>
    obtain ⟨hKind, hMsg⟩ := validateConfig_err_props hVal
    dsimp [Model.withProxyModel, StateT.run, bind, StateT.bind, pure, StateT.pure]
    rw [hVal]
    exact ⟨⟨⟨err, rfl, hKind, hMsg⟩, rfl⟩, trivial⟩

/-- `test_cproxy_withProxy_invalidConfig_hasZeroSideEffects` is reachable on `Internal.mkApiM` with `maxHeaderBytes = 0`. -/
theorem canReach_withProxy_invalidConfig_hasZeroSideEffects :
    CanReach (test_cproxy_withProxy_invalidConfig_hasZeroSideEffects Internal.mkApiM) := by
  let cfg : ProxyConfig := { limits := { maxHeaderBytes := 0 } }
  have hAll := allPass_withProxy_invalidConfig_hasZeroSideEffects {} cfg
  dsimp [test_cproxy_withProxy_invalidConfig_hasZeroSideEffects, AllPass, bind, assume, assert] at hAll
  have hVal : Model.validateConfig cfg =
      .error { kind := .invalidInput, message := "ProxyLimits.maxHeaderBytes must be greater than 0" } := rfl
  dsimp [CanReach, test_cproxy_withProxy_invalidConfig_hasZeroSideEffects, bind, assume, assert]
  refine ⟨{}, cfg, ?_⟩
  rw [hVal] at hAll ⊢
  exact hAll

/-- `test_cproxy_withProxy_universalConfigAndLifecycleEquivalence` holds universally for `Internal.mkApiM`. -/
theorem allPass_withProxy_universalConfigAndLifecycleEquivalence :
    AllPass (test_cproxy_withProxy_universalConfigAndLifecycleEquivalence Internal.mkApiM) := by
  intro s₀ cfg val
  dsimp [test_cproxy_withProxy_universalConfigAndLifecycleEquivalence, Internal.mkApiM, AllPass, bind, assert]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  dsimp [Model.withProxyModel, StateT.run, bind, StateT.bind, pure, StateT.pure]
  cases hVal : Model.validateConfig cfg with
  | error _ =>
    exact ⟨rfl, trivial⟩
  | ok vcfg =>
    obtain ⟨hPort, hLim⟩ := validateConfig_props hVal
    dsimp [mockRawProxyOps, tryFinally', MonadFinally.tryFinally', bind, StateT.bind, pure, StateT.pure, Id.run]
    rw [hLim]
    dsimp [bind, StateT.bind, pure, StateT.pure, Id.run]
    cases hStart : s₀.failStartWith with
    | some _ =>
      dsimp [bind, StateT.bind, pure, StateT.pure, Id.run]
      exact ⟨⟨rfl, rfl, rfl, rfl⟩, trivial⟩
    | none =>
      dsimp [bind, StateT.bind, pure, StateT.pure, Id.run]
      rw [not_contains_fresh_hid s₀.activeHandles s₀.nextHandleId,
        filter_fresh_hid s₀.activeHandles s₀.nextHandleId]
      dsimp [bind, StateT.bind, pure, StateT.pure, Id.run]
      cases hStop : s₀.failStopWith with
      | some _ =>
        dsimp [bind, StateT.bind, pure, StateT.pure, Id.run]
        exact ⟨⟨rfl, rfl, rfl, rfl⟩, trivial⟩
      | none =>
        dsimp [bind, StateT.bind, pure, StateT.pure, Id.run]
        refine ⟨⟨_, _, rfl, ?_, ?_, ?_, rfl⟩, trivial⟩
        · rw [hPort]
          by_cases hp : cfg.listenPort == 0
          · simp only [hp, ↓reduceIte]
            by_cases he : s₀.ephemeralPort == 0
            · simp [he]
            · simp only [he, Bool.false_eq_true, ↓reduceIte]
              exact fun h0 => he (beq_iff_eq.mpr h0)
          · simp only [hp, Bool.false_eq_true, ↓reduceIte]
            exact fun h0 => hp (beq_iff_eq.mpr h0)
        · rw [hPort]
          by_cases hp : cfg.listenPort == 0
          · exact Or.inl (beq_iff_eq.mp hp)
          · simp [hp]
        · have hSz := runSimulatedAttempts_size s₀.dnsTable s₀.failConnectIps
            (decideConnectHead vcfg.config) (decideResolvedIps vcfg.config.ipPolicy)
            s₀.scriptedAttempts.toList #[] s₀.dnsQueries s₀.dialedEndpoints
          simpa using hSz

/-- `test_cproxy_withProxy_universalConfigAndLifecycleEquivalence` is reachable on `Internal.mkApiM`. -/
theorem canReach_withProxy_universalConfigAndLifecycleEquivalence :
    CanReach (test_cproxy_withProxy_universalConfigAndLifecycleEquivalence Internal.mkApiM) :=
  ⟨{}, {}, 0, allPass_withProxy_universalConfigAndLifecycleEquivalence {} {} 0⟩

/-- `test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory` holds universally for `Internal.mkApiM`. -/
theorem allPass_withProxy_ephemeralPortVerifiedDialAndEventHistory :
    AllPass (test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory Internal.mkApiM) := by
  intro val
  let cfg : ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[
        { host := "API.Example.COM", port := 443 },
        { host := "down.example.com", port := 443 }
      ]
      ipPolicy := { base := .publicOnly, extraBans := #[.v4 0x0a000000 8] } }
  let s₀ : MockProxySimState :=
    { ephemeralPort := 51234
      dnsTable := [
        ("api.example.com", .resolved #[.v4 0x7f000001, mkNat64WellKnownIpv6 0x0a000001, .v4 0x5db8d822, .v4 0x08080808]),
        ("down.example.com", .resolved #[.v4 0x09090909])
      ]
      failConnectIps := [.v4 0x5db8d822, .v4 0x09090909]
      scriptedAttempts := #[
        .completedHead "GET http://api.example.com/ HTTP/1.1\r\n\r\n".toUTF8 none,
        .completedHead "CONNECT evil.example.com:443 HTTP/1.1\r\n\r\n".toUTF8 none,
        .completedHead "CONNECT api.example.com:443 HTTP/1.1\r\n\r\n".toUTF8 none,
        .completedHead "CONNECT down.example.com:443 HTTP/1.1\r\n\r\n".toUTF8 none,
        .inFlightAtStop (some "api.example.com") (some 443)
      ] }
  let expectedEvs : Array ConnectEvent :=
    #[{ host := none, port := none, outcome := .denied, reason := some "unsupported HTTP method 'GET' (only CONNECT is permitted)" },
      { host := some "evil.example.com", port := some 443, outcome := .denied, reason := some "target (host, port) not in allowedTargets" },
      { host := some "api.example.com", port := some 443, outcome := .allowed, reason := none },
      { host := some "down.example.com", port := some 443, outcome := .failed, reason := some "all verified upstream IPs failed connect" },
      { host := some "api.example.com", port := some 443, outcome := .failed, reason := some "proxy stopped" }]
  let expectedState : MockProxySimState :=
    { s₀ with
      activeHandles := []
      nextHandleId := 2
      startCalls := 1
      stopCalls := 1
      dnsQueries := #["api.example.com", "down.example.com"]
      dialedEndpoints := #[(.v4 0x5db8d822, 443), (.v4 0x08080808, 443), (.v4 0x09090909, 443)]
      lastStoppedEvents := expectedEvs }
  have hRunVal : (Model.withProxyModel mockRawProxyOps cfg (fun proxy =>
      if proxy.port == 51234 then pure (.ok val) else pure (.error { kind := .ioError, message := "unexpected bound port" }))).run s₀ =
      (.ok (val, expectedEvs), expectedState) := rfl
  dsimp only [test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory, Internal.mkApiM]
  rw [hRunVal]
  dsimp [bind, assert]
  refine ⟨by decide, by decide, by decide, ⟨rfl, by decide⟩, by decide, by decide, by decide, by decide, by decide, trivial⟩

/-- `test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory` is reachable on `Internal.mkApiM`. -/
theorem canReach_withProxy_ephemeralPortVerifiedDialAndEventHistory :
    CanReach (test_cproxy_withProxy_ephemeralPortVerifiedDialAndEventHistory Internal.mkApiM) :=
  ⟨0, allPass_withProxy_ephemeralPortVerifiedDialAndEventHistory 0⟩

/-- `test_cproxy_withProxy_callbackError_tearsDownAndPreservesError` holds universally for `Internal.mkApiM`. -/
theorem allPass_withProxy_callbackError_tearsDownAndPreservesError :
    AllPass (test_cproxy_withProxy_callbackError_tearsDownAndPreservesError Internal.mkApiM) := by
  intro s₀ actionErr hStart
  dsimp [test_cproxy_withProxy_callbackError_tearsDownAndPreservesError, Internal.mkApiM,
    Model.withProxyModel, mockRawProxyOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
    tryFinally', MonadFinally.tryFinally', Id.run, AllPass, assume, assert]
  have hVal : Model.validateConfig { listenPort := 0, allowedTargets := #[{ host := "api.example.com", port := 443 }] } =
      .ok { config := { listenPort := 0, allowedTargets := #[{ host := "api.example.com", port := 443 }] } } := rfl
  rw [hVal]
  dsimp [StateT.bind, StateT.pure, Id.run, bind, pure]
  rw [hStart]
  dsimp [StateT.bind, StateT.pure, Id.run, bind, pure]
  rw [not_contains_fresh_hid s₀.activeHandles s₀.nextHandleId,
    filter_fresh_hid s₀.activeHandles s₀.nextHandleId]
  dsimp [StateT.bind, StateT.pure, Id.run, bind, pure]
  cases hStop : s₀.failStopWith <;>
    (dsimp [StateT.bind, StateT.pure, Id.run, bind, pure]; exact ⟨rfl, ⟨rfl, rfl⟩, rfl, trivial⟩)

/-- `test_cproxy_withProxy_callbackError_tearsDownAndPreservesError` is reachable on `Internal.mkApiM`. -/
theorem canReach_withProxy_callbackError_tearsDownAndPreservesError :
    CanReach (test_cproxy_withProxy_callbackError_tearsDownAndPreservesError Internal.mkApiM) :=
  ⟨{}, { kind := .ioError, message := "callback error" }, rfl,
    allPass_withProxy_callbackError_tearsDownAndPreservesError {} { kind := .ioError, message := "callback error" } rfl⟩

/-- `test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown` holds universally for `Internal.mkApiM`. -/
theorem allPass_withProxy_exceptionTriggersMonadFinallyTeardown :
    AllPass (test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown Internal.mkApiM) := by
  intro s₀ ⟨hStart, hStop⟩
  dsimp [test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown, Internal.mkApiM,
    Model.withProxyModel, mockRawProxyOpsEx, mockRawProxyOps,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    StateT.run, bind, StateT.bind, pure, StateT.pure,
    tryFinally', MonadFinally.tryFinally', throw, throwThe, MonadExceptOf.throw,
    AllPass, assume, assert]
  have hVal : Model.validateConfig { listenPort := 0, allowedTargets := #[{ host := "api.example.com", port := 443 }] } =
      .ok { config := { listenPort := 0, allowedTargets := #[{ host := "api.example.com", port := 443 }] } } := rfl
  rw [hVal]
  dsimp [ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, StateT.bind, StateT.pure, Id.run, bind, pure]
  rw [hStart]
  dsimp [ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, StateT.bind, StateT.pure, Id.run, bind, pure]
  rw [not_contains_fresh_hid s₀.activeHandles s₀.nextHandleId,
    filter_fresh_hid s₀.activeHandles s₀.nextHandleId, hStop]
  dsimp [ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, StateT.bind, StateT.pure, Id.run, bind, pure]
  exact ⟨rfl, ⟨rfl, rfl⟩, rfl, trivial⟩

/-- `test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown` is reachable on `Internal.mkApiM`. -/
theorem canReach_withProxy_exceptionTriggersMonadFinallyTeardown :
    CanReach (test_cproxy_withProxy_exceptionTriggersMonadFinallyTeardown Internal.mkApiM) :=
  ⟨{}, ⟨rfl, rfl⟩, allPass_withProxy_exceptionTriggersMonadFinallyTeardown {} ⟨rfl, rfl⟩⟩

end LeanSwe.ConnectProxy.Proofs
