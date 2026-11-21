import Core.Refines
import Core.Assumptions
import LeanSwe.ConnectProxy.Proofs.IpPolicyProofs
import LeanSwe.ConnectProxy.Proofs.ParserAndModelProofs
import LeanSwe.ConnectProxy.Proofs.Lifecycle
import LeanSwe.ConnectProxy.Proofs.HealthyWitness
import LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs
import LeanSwe.ConnectProxy.Proofs.SysBridgeProofs
import LeanSwe.ConnectProxy.Proofs.LoopAndRelayProofs
import LeanSwe.ConnectProxy.Proofs.HealthySpecProofs

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.ConnectProxy

/-- `parseIpAddr` never fails with `.addressInUse`. -/
theorem cproxy_parseIpAddr_never_addressInUse (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .addressInUse (LeanSwe.ConnectProxy.parseIpAddr s) := by
  cases h : LeanSwe.ConnectProxy.parseIpAddr s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpAddr_err_props h).1]; decide

/-- `parseIpAddr` never fails with `.permissionDenied`. -/
theorem cproxy_parseIpAddr_never_permissionDenied (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .permissionDenied (LeanSwe.ConnectProxy.parseIpAddr s) := by
  cases h : LeanSwe.ConnectProxy.parseIpAddr s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpAddr_err_props h).1]; decide

/-- `parseIpAddr` never fails with `.resourceExhausted`. -/
theorem cproxy_parseIpAddr_never_resourceExhausted (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .resourceExhausted (LeanSwe.ConnectProxy.parseIpAddr s) := by
  cases h : LeanSwe.ConnectProxy.parseIpAddr s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpAddr_err_props h).1]; decide

/-- `parseIpAddr` never fails with `.ioError`. -/
theorem cproxy_parseIpAddr_never_ioError (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .ioError (LeanSwe.ConnectProxy.parseIpAddr s) := by
  cases h : LeanSwe.ConnectProxy.parseIpAddr s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpAddr_err_props h).1]; decide

/-- `parseIpPrefix` never fails with `.addressInUse`. -/
theorem cproxy_parseIpPrefix_never_addressInUse (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .addressInUse (LeanSwe.ConnectProxy.parseIpPrefix s) := by
  cases h : LeanSwe.ConnectProxy.parseIpPrefix s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpPrefix_err_props h).1]; decide

/-- `parseIpPrefix` never fails with `.permissionDenied`. -/
theorem cproxy_parseIpPrefix_never_permissionDenied (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .permissionDenied (LeanSwe.ConnectProxy.parseIpPrefix s) := by
  cases h : LeanSwe.ConnectProxy.parseIpPrefix s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpPrefix_err_props h).1]; decide

/-- `parseIpPrefix` never fails with `.resourceExhausted`. -/
theorem cproxy_parseIpPrefix_never_resourceExhausted (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .resourceExhausted (LeanSwe.ConnectProxy.parseIpPrefix s) := by
  cases h : LeanSwe.ConnectProxy.parseIpPrefix s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpPrefix_err_props h).1]; decide

/-- `parseIpPrefix` never fails with `.ioError`. -/
theorem cproxy_parseIpPrefix_never_ioError (s : String) :
    Core.NeverErrorKindPure ProxyError.kind .ioError (LeanSwe.ConnectProxy.parseIpPrefix s) := by
  cases h : LeanSwe.ConnectProxy.parseIpPrefix s with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseIpPrefix_err_props h).1]; decide

/-- `parseConnectRequest` never fails with `.addressInUse`. -/
theorem cproxy_parseConnectRequest_never_addressInUse (raw : ByteArray) :
    Core.NeverErrorKindPure ProxyError.kind .addressInUse (LeanSwe.ConnectProxy.parseConnectRequest raw) := by
  cases h : LeanSwe.ConnectProxy.parseConnectRequest raw with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseConnectRequest_err_props h).1]; decide

/-- `parseConnectRequest` never fails with `.permissionDenied`. -/
theorem cproxy_parseConnectRequest_never_permissionDenied (raw : ByteArray) :
    Core.NeverErrorKindPure ProxyError.kind .permissionDenied (LeanSwe.ConnectProxy.parseConnectRequest raw) := by
  cases h : LeanSwe.ConnectProxy.parseConnectRequest raw with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseConnectRequest_err_props h).1]; decide

/-- `parseConnectRequest` never fails with `.resourceExhausted`. -/
theorem cproxy_parseConnectRequest_never_resourceExhausted (raw : ByteArray) :
    Core.NeverErrorKindPure ProxyError.kind .resourceExhausted (LeanSwe.ConnectProxy.parseConnectRequest raw) := by
  cases h : LeanSwe.ConnectProxy.parseConnectRequest raw with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseConnectRequest_err_props h).1]; decide

/-- `parseConnectRequest` never fails with `.ioError`. -/
theorem cproxy_parseConnectRequest_never_ioError (raw : ByteArray) :
    Core.NeverErrorKindPure ProxyError.kind .ioError (LeanSwe.ConnectProxy.parseConnectRequest raw) := by
  cases h : LeanSwe.ConnectProxy.parseConnectRequest raw with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(parseConnectRequest_err_props h).1]; decide

/-- `validateConfig` never fails with `.addressInUse`. -/
theorem cproxy_validateConfig_never_addressInUse (cfg : ProxyConfig) :
    Core.NeverErrorKindPure ProxyError.kind .addressInUse (LeanSwe.ConnectProxy.validateConfig cfg) := by
  cases h : LeanSwe.ConnectProxy.validateConfig cfg with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(validateConfig_err_props h).1]; decide

/-- `validateConfig` never fails with `.permissionDenied`. -/
theorem cproxy_validateConfig_never_permissionDenied (cfg : ProxyConfig) :
    Core.NeverErrorKindPure ProxyError.kind .permissionDenied (LeanSwe.ConnectProxy.validateConfig cfg) := by
  cases h : LeanSwe.ConnectProxy.validateConfig cfg with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(validateConfig_err_props h).1]; decide

/-- `validateConfig` never fails with `.resourceExhausted`. -/
theorem cproxy_validateConfig_never_resourceExhausted (cfg : ProxyConfig) :
    Core.NeverErrorKindPure ProxyError.kind .resourceExhausted (LeanSwe.ConnectProxy.validateConfig cfg) := by
  cases h : LeanSwe.ConnectProxy.validateConfig cfg with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(validateConfig_err_props h).1]; decide

/-- `validateConfig` never fails with `.ioError`. -/
theorem cproxy_validateConfig_never_ioError (cfg : ProxyConfig) :
    Core.NeverErrorKindPure ProxyError.kind .ioError (LeanSwe.ConnectProxy.validateConfig cfg) := by
  cases h : LeanSwe.ConnectProxy.validateConfig cfg with
  | ok _ => trivial
  | error e => dsimp only [Core.NeverErrorKindPure]; rw [(validateConfig_err_props h).1]; decide

private theorem refinesStepFrom_mkScopedApiM :
    Core.RefinesStepFromFinally id Model.proxyStepWf
      Model.execRawStep Model.allowedRawStep
      Model.proxyStepWf Internal.mkScopedApiM
      Model.execPkgStep Model.allowedPkgStep := by
  intro W proj rawOps hRaw w req hWf
  dsimp only [Model.execPkgStep, Internal.mkScopedApiM, Model.allowedPkgStep]
  cases hVal : Model.validateConfig req.cfg with
  | error err =>
    exact ⟨rfl, rfl⟩
  | ok vcfg =>
    exact hRaw w { vcfg, tag := req.tag } hWf

/-- Full public `Interface` refinement of `LeanSwe.ConnectProxy` against `LeanSwe.ConnectProxy.Model`. -/
theorem refines_model :
    Core.RefinesPureEq LeanSwe.ConnectProxy.parseIpAddr Model.parseIpAddr ∧
    Core.RefinesPureEq LeanSwe.ConnectProxy.parseIpPrefix Model.parseIpPrefix ∧
    Core.RefinesPureEq LeanSwe.ConnectProxy.isGlobalIp Model.isGlobalIp ∧
    Core.RefinesPureEq2 LeanSwe.ConnectProxy.allowsIp Model.allowsIp ∧
    Core.RefinesPureEq LeanSwe.ConnectProxy.parseConnectRequest Model.parseConnectRequest ∧
    Core.RefinesPureEq LeanSwe.ConnectProxy.validateConfig Model.validateConfig ∧
    Core.RefinesStepFromFinally id Model.proxyStepWf
      Model.execRawStep Model.allowedRawStep
      Model.proxyStepWf Internal.mkScopedApiM
      Model.execPkgStep Model.allowedPkgStep :=
  ⟨fun _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   fun _ _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   refinesStepFrom_mkScopedApiM⟩

end LeanSwe.ConnectProxy.Proofs
