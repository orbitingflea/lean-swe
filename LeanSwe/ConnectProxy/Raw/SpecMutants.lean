import Core.NondetTest
import LeanSwe.ConnectProxy.Raw.Types
import LeanSwe.ConnectProxy.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.ConnectProxy.Raw`. -/

namespace LeanSwe.ConnectProxy.Raw

open Core (NondetTest)
open Core.NondetTest

private def stubRawOps : RawConnectProxyOps :=
  { mapRawError := fun
      | .invalidArgument errno? _ =>
        { kind := .invalidInput, errnoCode := errno?, message := "invalid argument" }
      | .addressInUse _ errno _ =>
        { kind := .addressInUse, errnoCode := some errno, message := "address in use" }
      | .permissionDenied errno _ =>
        { kind := .permissionDenied, errnoCode := some errno, message := "permission denied" }
      | .resourceExhausted errno _ =>
        { kind := .resourceExhausted, errnoCode := some errno, message := "resource exhausted" }
      | .otherError errno _ =>
        { kind := .ioError, errnoCode := some errno, message := "os error" }
      | .userError _ =>
        { kind := .ioError, errnoCode := none, message := "user error" }
    startProxy := fun _ _ _ => pure (.error { kind := .ioError, message := "stub" })
    stopProxy := fun _ => pure (.ok #[])
    activeProxyCount := pure 0 }

private def stubStateRawOps : RawConnectProxyOpsM (StateM (List Nat)) :=
  { mapRawError := stubRawOps.mapRawError
    startProxy := fun vcfg _ _ s =>
      let lim := vcfg.config.limits
      if lim.maxHeaderBytes == 0 || lim.headerTimeoutMs == 0 ||
         lim.connectTimeoutMs == 0 || lim.maxConcurrentTunnels == 0 then
        (.error { kind := .invalidInput, message := "zero limit" }, s)
      else
        let hid := (s.foldl Nat.max 0) + 1
        let p : UInt16 := if vcfg.config.listenPort == 0 then 49152 else vcfg.config.listenPort
        (.ok { handleId := hid, port := p }, hid :: s)
    stopProxy := fun proxy s =>
      if !s.contains proxy.handleId then
        (.error { kind := .invalidInput, message := "not active" }, s)
      else
        (.ok #[], s.filter (· != proxy.handleId))
    activeProxyCount := fun s => (s.length, s) }

example : ¬ Core.AllPass (test_cproxyRaw_mapRawError_returnsNonEmptyMessage
    { stubRawOps with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  simp [assert] at h0

example : ¬ Core.AllPass (test_cproxyRaw_mapRawError_preservesKindAndFields
    { stubRawOps with
      mapRawError := fun
        | .addressInUse _ errno _ => { kind := .ioError, errnoCode := some errno, message := "wrong kind" }
        | other => stubRawOps.mapRawError other }) := by
  intro h
  have h0 := h (.addressInUse 8080 98 "EADDRINUSE")
  simp [assert] at h0

example : ¬ Core.AllPass (test_cproxyRaw_startProxy_zeroLimits_failsInvalidInput
    { stubStateRawOps with
      startProxy := fun _ _ _ s => (.ok { handleId := 1, port := 49152 }, 1 :: s) }) := by
  intro h
  let badCfg : ValidProxyConfig := { config := { limits := { maxHeaderBytes := 0 } } }
  have h0 := h [] badCfg (Or.inl rfl)
  simp [stubStateRawOps, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount
    { stubStateRawOps with
      startProxy := fun _ _ _ s => (.ok { handleId := 1, port := 0 }, 1 :: s) }) := by
  intro h
  have h0 := h [] { config := { listenPort := 0 } }
  simp [stubStateRawOps, StateT.run, bind, assert] at h0

example : ¬ Core.AllPass (test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount
    { stubStateRawOps with
      stopProxy := fun _ s => (.ok #[], s) }) := by
  intro h
  have h0 := h [] { config := { listenPort := 8080 } }
  simp [stubStateRawOps, StateT.run, bind, assert] at h0

end LeanSwe.ConnectProxy.Raw
