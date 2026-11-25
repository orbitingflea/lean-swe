import Core.Obeys
import Core.ConcOps
import Core.Assumptions
import LeanSwe.ConnectProxy.Proofs.IpPolicyProofs
import LeanSwe.ConnectProxy.Proofs.ParserAndModelProofs
import LeanSwe.ConnectProxy.Proofs.Lifecycle
import LeanSwe.ConnectProxy.Proofs.HealthyWitness
import LeanSwe.ConnectProxy.Proofs.SysBridgeCoreProofs
import LeanSwe.ConnectProxy.Proofs.SysBridgeProofs
import LeanSwe.ConnectProxy.Proofs.LoopAndRelayProofs
import LeanSwe.ConnectProxy.Proofs.HealthySpecProofs
import LeanSwe.ConnectProxy.Proofs.FullObeys

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

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.ConnectProxy` (`Internal.mkFullApiM`
    over `LinuxSyscall.{Files,Net,Poll,Dns,TimeRand}` and `Core.ConcOpsM`) against
    `LeanSwe.ConnectProxy.Model` and `HealthySysWorld`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.ConnectProxy.parseIpAddr Model.parseIpAddr ∧
    Core.ObeysPureEq LeanSwe.ConnectProxy.parseIpPrefix Model.parseIpPrefix ∧
    Core.ObeysPureEq LeanSwe.ConnectProxy.isGlobalIp Model.isGlobalIp ∧
    Core.ObeysPureEq2 LeanSwe.ConnectProxy.allowsIp Model.allowsIp ∧
    Core.ObeysPureEq LeanSwe.ConnectProxy.parseConnectRequest Model.parseConnectRequest ∧
    Core.ObeysPureEq LeanSwe.ConnectProxy.validateConfig Model.validateConfig ∧
    Core.ObeysStepFromConc Model.mapFullWorldToSim Model.fullWorldWf
      Model.execFullRawStep Model.allowedFullRawStep
      Model.proxyStepWf Internal.mkFullApiM
      Model.execPkgStep Model.allowedPkgStep ∧
    Core.ObeysStepFromConc id Model.fullWorldWf
      Model.execFullRawStep Model.allowedFullRawStep
      Model.fullWorldWf Internal.mkFullApiM
      Model.execPkgStep Model.allowedFullPkgStep :=
  ⟨fun _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   fun _ _ => rfl,
   fun _ => rfl,
   fun _ => rfl,
   obeysStepFromConc_mkFullApiM,
   obeysStepFromConc_mkFullApiM_full⟩

/-- Non-vacuity witness showing both `FullSysOpsM` and `Core.ConcOpsM` hypotheses of `obeys_model`
    are inhabited by a pure schedule-driven witness (`sched : Nat → Bool`, exercising pending `none`
    and interleaved execution). -/
theorem obeys_model_nonvacuous (sched : Nat → Bool) :
    ∃ (W : Type) (proj : W → Internal.HealthySys.HealthySysWorld)
      (sys : Model.FullSysOpsM (StateM W)) (conc : Core.ConcOpsM (StateM W)),
      Core.ObeysStep proj Model.fullWorldWf (Model.execFullRawStep sys) Model.allowedFullRawStep ∧
      Core.ObeysConc (fun w => Model.fullWorldWf (proj w) = true) conc :=
  ⟨Internal.HealthySys.HealthySysWorld × Nat, Prod.fst, sampleHealthySysSched,
   schedConcOps Internal.HealthySys.HealthySysWorld sched,
   sampleHealthySysSched_obeys,
   schedConcOps_obeysConc (fun w => Model.fullWorldWf w = true) sched⟩

end LeanSwe.ConnectProxy.Proofs
