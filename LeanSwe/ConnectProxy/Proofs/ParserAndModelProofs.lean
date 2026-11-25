import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.SpecTests
import LeanSwe.ConnectProxy.Proofs.HostNormProofs

namespace LeanSwe.ConnectProxy.Proofs

open Core
open Core.NondetTest
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model

local macro "solve_invalid_input" : tactic =>
  `(tactic| exact ⟨rfl, by
    dsimp only [ToString.toString]
    repeat (first | apply nonEmpty_append_left | decide)⟩)

private theorem normalizeTargetRule_err_props {r : TargetRule} {err : ProxyError}
    (h : Model.normalizeTargetRule r = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.normalizeTargetRule at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · cases h
    · rename_i hHost
      injection h with hEq; subst hEq
      exact normalizeTargetHost_err_props hHost

private theorem normalizeTargetRule_idempotent {r y : TargetRule}
    (h : Model.normalizeTargetRule r = .ok y) :
    Model.normalizeTargetRule y = .ok y := by
  unfold Model.normalizeTargetRule at h
  split at h
  · cases h
  · rename_i hPort
    split at h
    · rename_i normHost _ hHost
      injection h with hEq; subst hEq
      unfold Model.normalizeTargetRule
      simp only [hPort, Bool.false_eq_true, ↓reduceIte, normalizeTargetHost_idempotent hHost]
    · cases h

private theorem mapExceptList_normalizeTargetRule_err_props :
    ∀ (rs : List TargetRule) {err : ProxyError},
      Model.mapExceptList Model.normalizeTargetRule rs = .error err →
      err.kind = .invalidInput ∧ err.message ≠ ""
  | [], _, h => nomatch h
  | r :: rest, _, h => by
    simp only [Model.mapExceptList, bind, Except.bind] at h
    cases hr : Model.normalizeTargetRule r with
    | error er =>
      rw [hr] at h
      injection h with hEq; subst hEq
      exact normalizeTargetRule_err_props hr
    | ok nr =>
      rw [hr] at h
      dsimp only at h
      cases hRest : Model.mapExceptList Model.normalizeTargetRule rest with
      | error er =>
        rw [hRest] at h
        injection h with hEq; subst hEq
        exact mapExceptList_normalizeTargetRule_err_props rest hRest
      | ok _ =>
        rw [hRest] at h
        cases h

private theorem mapExceptList_normalizeTargetRule_idempotent :
    ∀ (rs ys : List TargetRule),
      Model.mapExceptList Model.normalizeTargetRule rs = .ok ys →
      Model.mapExceptList Model.normalizeTargetRule ys = .ok ys
  | [], ys, h => by
    simp only [Model.mapExceptList] at h
    injection h with hEq; subst hEq
    rfl
  | r :: rest, ys, h => by
    simp only [Model.mapExceptList, bind, Except.bind] at h
    cases hr : Model.normalizeTargetRule r with
    | error er => rw [hr] at h; cases h
    | ok y =>
      rw [hr] at h
      dsimp only at h
      cases hRest : Model.mapExceptList Model.normalizeTargetRule rest with
      | error er => rw [hRest] at h; cases h
      | ok yrest =>
        rw [hRest] at h
        injection h with hEq; subst hEq
        simp only [Model.mapExceptList, bind, Except.bind,
          normalizeTargetRule_idempotent hr,
          mapExceptList_normalizeTargetRule_idempotent rest yrest hRest]

private theorem parseConnectRequest_ok_props {raw : ByteArray} {rule : TargetRule}
    (h : Model.parseConnectRequest raw = .ok rule) :
    rule.port ≠ 0 ∧ (!rule.host.toList.contains '*') = true := by
  unfold Model.parseConnectRequest at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  dsimp only at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  rename_i portNat _
  split at h
  · cases h
  · rename_i hRange
    split at h
    · rename_i normHost _ hHost
      injection h with hEq; subst hEq
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_gt_eq] at hRange
      refine ⟨?_, normalizeTargetHost_ok_no_star hHost⟩
      intro hZero
      have hNat : (UInt16.ofNat portNat).toNat = 0 := congrArg UInt16.toNat hZero
      have hMod : portNat % 65536 = 0 := by simpa [UInt16.toNat_ofNat] using hNat
      rw [Nat.mod_eq_of_lt (by omega)] at hMod
      exact hRange.1 hMod
    · cases h

/-- Every error returned by `Model.parseConnectRequest` has kind `.invalidInput` and a non-empty message. -/
theorem parseConnectRequest_err_props {raw : ByteArray} {err : ProxyError}
    (h : Model.parseConnectRequest raw = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.parseConnectRequest at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · injection h with hEq; subst hEq; solve_invalid_input
    · split at h
      · injection h with hEq; subst hEq; solve_invalid_input
      · dsimp only at h
        split at h
        · split at h
          · injection h with hEq; subst hEq; solve_invalid_input
          · split at h
            · injection h with hEq; subst hEq; solve_invalid_input
            · split at h
              · injection h with hEq; subst hEq; solve_invalid_input
              · split at h
                · injection h with hEq; subst hEq; solve_invalid_input
                · split at h
                  · injection h with hEq; subst hEq; solve_invalid_input
                  · split at h
                    · injection h with hEq; subst hEq; solve_invalid_input
                    · split at h
                      · cases h
                      · rename_i hHost
                        injection h with hEq; subst hEq
                        exact normalizeTargetHost_err_props hHost
        · injection h with hEq; subst hEq; solve_invalid_input

/-- Every error returned by `Model.validateConfig` has kind `.invalidInput` and a non-empty message. -/
theorem validateConfig_err_props {cfg : ProxyConfig} {err : ProxyError}
    (h : Model.validateConfig cfg = .error err) :
    err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Model.validateConfig at h
  split at h
  · injection h with hEq; subst hEq; solve_invalid_input
  · split at h
    · injection h with hEq; subst hEq; solve_invalid_input
    · split at h
      · injection h with hEq; subst hEq; solve_invalid_input
      · split at h
        · injection h with hEq; subst hEq; solve_invalid_input
        · split at h
          · injection h with hEq; subst hEq; solve_invalid_input
          · split at h
            · injection h with hEq; subst hEq; solve_invalid_input
            · simp only [bind, Except.bind] at h
              split at h
              · rename_i hMap
                injection h with hEq; subst hEq
                exact mapExceptList_normalizeTargetRule_err_props _ hMap
              · cases h

private theorem validateConfig_idempotent {cfg : ProxyConfig} {vcfg : ValidProxyConfig}
    (h : Model.validateConfig cfg = .ok vcfg) :
    Model.validateConfig vcfg.config = .ok vcfg := by
  unfold Model.validateConfig at h
  split at h <;> try cases h
  rename_i h1
  split at h <;> try cases h
  rename_i h2
  split at h <;> try cases h
  rename_i h3
  split at h <;> try cases h
  rename_i h4
  split at h <;> try cases h
  rename_i h5
  split at h <;> try cases h
  rename_i h6
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i normTargets hMap
    injection h with hEq; subst hEq
    unfold Model.validateConfig
    simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
      mapExceptList_normalizeTargetRule_idempotent _ _ hMap]

/-- Structural properties guaranteed whenever `Model.decideConnectHead` returns `.needResolve`. -/
theorem decideConnectHead_needResolve_props {cfg : ProxyConfig} {head : ByteArray}
    {host : String} {port : UInt16} {litIp? : Option IpAddr}
    (h : Model.decideConnectHead cfg head = .needResolve host port litIp?) :
    head.size ≤ cfg.limits.maxHeaderBytes ∧
    Model.parseConnectRequest head = .ok { host := host, port := port } ∧
    Model.matchesAllowedTarget cfg.allowedTargets { host := host, port := port } = true ∧
    Model.literalIpOfHost? host = litIp? := by
  unfold Model.decideConnectHead at h
  split at h
  · cases h
  · rename_i hNotOver
    have hSize : head.size ≤ cfg.limits.maxHeaderBytes := Nat.le_of_not_lt hNotOver
    split at h
    · cases h
    · rename_i target hParse
      split at h
      · rename_i hAllowed
        injection h with hHost hPort hLit
        subst hHost; subst hPort; subst hLit
        exact ⟨hSize, hParse, hAllowed, rfl⟩
      · cases h

/-- `authorizeConnect` only produces `.dial plan` for bounded valid `CONNECT` requests matching `allowedTargets`, dialing verified IPs from the literal or resolved snapshot. -/
theorem specOnlyAllowedTargetAndVerifiedIpDialed :
    SpecOnlyAllowedTargetAndVerifiedIpDialed := by
  intro cfg head resolveHost plan hAuth
  unfold Model.authorizeConnect at hAuth
  cases hHead : Model.decideConnectHead cfg head with
  | deny h p r =>
    rw [hHead] at hAuth; cases hAuth
  | needResolve host port litIp? =>
    rw [hHead] at hAuth
    obtain ⟨hSize, hParse, hAllowed, hLitEq⟩ := decideConnectHead_needResolve_props hHead
    cases litIp? with
    | some litIp =>
      cases hAllowLit : Model.allowsIp cfg.ipPolicy litIp with
      | false =>
        simp only [Model.decideResolvedIps, List.filter, hAllowLit] at hAuth
        cases hAuth
      | true =>
        simp only [Model.decideResolvedIps, List.filter, hAllowLit] at hAuth
        injection hAuth with hPlan
        subst hPlan
        refine ⟨hSize, hParse, hAllowed, hAllowLit, ?_, ?_⟩
        · intro ip hip; nomatch hip
        · rw [hLitEq]; exact ⟨rfl, rfl⟩
    | none =>
      dsimp only at hAuth
      cases hRes : resolveHost host with
      | error dnsErr =>
        rw [hRes] at hAuth; cases hAuth
      | ok resolved =>
        rw [hRes] at hAuth
        dsimp only at hAuth
        unfold Model.decideResolvedIps at hAuth
        cases hFiltEq : resolved.toList.filter (Model.allowsIp cfg.ipPolicy) with
        | nil =>
          rw [hFiltEq] at hAuth; cases hAuth
        | cons primary rest =>
          rw [hFiltEq] at hAuth
          dsimp only at hAuth
          injection hAuth with hPlan
          subst hPlan
          have hPrimMem : primary ∈ resolved.toList.filter (Model.allowsIp cfg.ipPolicy) := by
            rw [hFiltEq]; exact List.Mem.head _
          obtain ⟨hPrimIn, hPrimAllow⟩ := List.mem_filter.mp hPrimMem
          refine ⟨hSize, hParse, hAllowed, hPrimAllow, ?_, ?_⟩
          · intro ip hip
            have hRest : ip ∈ rest := by simpa using hip
            have hInFilt : ip ∈ resolved.toList.filter (Model.allowsIp cfg.ipPolicy) := by
              rw [hFiltEq]; exact List.Mem.tail _ hRest
            exact (List.mem_filter.mp hInFilt).2
          · rw [hLitEq]
            refine ⟨resolved, hRes, hPrimIn, ?_⟩
            intro ip hip
            have hRest : ip ∈ rest := by simpa using hip
            have hInFilt : ip ∈ resolved.toList.filter (Model.allowsIp cfg.ipPolicy) := by
              rw [hFiltEq]; exact List.Mem.tail _ hRest
            exact (List.mem_filter.mp hInFilt).1

/-- `AllPass` proof of `test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority` on `defaultApi`. -/
theorem proof_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority :
    Core.AllPass (test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority defaultApi) := by
  intro raw
  dsimp [test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority, defaultApi, Internal.mkFullApiM,
    Core.AllPass, bind, assert]
  refine ⟨rfl, ?_⟩
  cases h : Model.parseConnectRequest raw with
  | ok _ => exact ⟨parseConnectRequest_ok_props h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  | error err => exact ⟨parseConnectRequest_err_props h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `CanReach` witness for `test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority` on `defaultApi`. -/
theorem reach_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority :
    Core.CanReach (test_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority defaultApi) :=
  ⟨ByteArray.empty, proof_cproxy_parseConnectRequest_onlyConnectAndNormalizedAuthority ByteArray.empty⟩

/-- `AllPass` proof of `test_cproxy_validateConfig_limitsPortZeroAndIdempotence` on `defaultApi`. -/
theorem proof_cproxy_validateConfig_limitsPortZeroAndIdempotence :
    Core.AllPass (test_cproxy_validateConfig_limitsPortZeroAndIdempotence defaultApi) := by
  intro cfg
  dsimp [test_cproxy_validateConfig_limitsPortZeroAndIdempotence, defaultApi, Internal.mkFullApiM,
    Core.AllPass, bind, assert]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases h : Model.validateConfig cfg with
  | error err => exact ⟨validateConfig_err_props h, trivial⟩
  | ok vcfg => exact ⟨validateConfig_idempotent h, trivial⟩

/-- `CanReach` witness for `test_cproxy_validateConfig_limitsPortZeroAndIdempotence` on `defaultApi`. -/
theorem reach_cproxy_validateConfig_limitsPortZeroAndIdempotence :
    Core.CanReach (test_cproxy_validateConfig_limitsPortZeroAndIdempotence defaultApi) :=
  ⟨{}, proof_cproxy_validateConfig_limitsPortZeroAndIdempotence {}⟩

/-- `AllPass` proof of `test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal` on `Model.authorizeConnect`. -/
theorem proof_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal :
    Core.AllPass (test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal Model.authorizeConnect) := by
  dsimp [test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal, Core.AllPass, bind, assert]
  refine ⟨rfl, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, trivial⟩

/-- `CanReach` witness for `test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal` on `Model.authorizeConnect`. -/
theorem reach_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal :
    Core.CanReach (test_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal Model.authorizeConnect) :=
  proof_cproxy_model_authorizeConnect_exactHostPortAndOversizedRefusal

/-- `AllPass` proof of `test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly` on `Model.authorizeConnect`. -/
theorem proof_cproxy_model_authorizeConnect_selectsVerifiedIpOnly :
    Core.AllPass (test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly Model.authorizeConnect) := by
  dsimp [test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly, Core.AllPass, bind, assert]
  refine ⟨rfl, ⟨_, rfl⟩, rfl, trivial⟩

/-- `CanReach` witness for `test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly` on `Model.authorizeConnect`. -/
theorem reach_cproxy_model_authorizeConnect_selectsVerifiedIpOnly :
    Core.CanReach (test_cproxy_model_authorizeConnect_selectsVerifiedIpOnly Model.authorizeConnect) :=
  proof_cproxy_model_authorizeConnect_selectsVerifiedIpOnly

end LeanSwe.ConnectProxy.Proofs
