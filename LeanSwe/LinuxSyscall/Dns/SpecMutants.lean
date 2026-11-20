import LeanSwe.LinuxSyscall.Dns.SpecTests
import LeanSwe.LinuxSyscall.Dns.Impl

/-! Compile-time negative specification mutants for `LeanSwe.LinuxSyscall.Dns`. -/

namespace LeanSwe.LinuxSyscall.Dns

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

example : ¬ Core.AllPass (test_dns_validateHost_semantics (fun h => !h.isEmpty)) := by
  intro h
  have h0 := h "a\x00b"
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_addrHelpers_semantics (fun _ => "127.0.0.1")) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_addrHelpers_semantics
    (fun a => s!"{a.format}%0")
    DnsAddr.isLoopback) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_addrHelpers_semantics
    DnsAddr.format
    (fun _ => true)) := by
  intro h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_classifyGaiKind_semantics (fun rc =>
    if rc == EAI_NONAME then .invalidHost else classifyGaiKind rc)) := by
  intro h
  have h0 := h EAI_NONAME
  exact absurd h0.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_wireTags_semantics
    (fun | .any => 1 | .ipv4 => 1 | .ipv6 => 2)
    SockTypeHint.toWire) := by
  intro h
  have h0 := h .any .ipv4 .any .any
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_dns_wireTags_semantics
    AddrFamilyHint.toWire
    (fun | .any => 1 | .stream => 1 | .dgram => 2)) := by
  intro h
  have h0 := h .any .any .any .stream
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun _ _ => pure (.ok []) }) := by
  intro h
  have h1 := (h defaultOfflineOracle "127.0.0.1" {} (.ok [])).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun h f =>
        if h == "::1%lo" then pure (.ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1])
        else modelOps.getaddrinfo h f }) := by
  intro h
  have h1 := (h defaultOfflineOracle "::1%lo" {} (.ok [])).1
  simp [Pure.pure, allowedDnsOutcome, parsePureNumericAddr?,
    parseScopedNonNumericZone?, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun h f =>
        if h == "fe80::1%" && f.family == .ipv4 then
          pure (.error { kind := .nameNotFound, gaiCode := EAI_NONAME, errno? := none, message := "x" })
        else modelOps.getaddrinfo h f }) := by
  intro h
  have h1 := (h defaultOfflineOracle "fe80::1%" { family := .ipv4, sockType := .stream } (.ok [])).1
  simp [Pure.pure, allowedDnsOutcome, parsePureNumericAddr?,
    parseScopedNonNumericZone?, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun h f =>
        if h == "localhost" && f.family == .ipv4 && f.sockType == .any then
          pure (.ok [.ipv4 127 0 0 1])
        else modelOps.getaddrinfo h f }) := by
  intro h
  have h1 := (h defaultOfflineOracle "localhost" { family := .ipv4, sockType := .any } (.ok [])).1
  simp [Pure.pure, allowedDnsOutcome, parsePureNumericAddr?,
    parseScopedNonNumericZone?, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun _ _ =>
        pure (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EFAULT, message := "x" }) }) := by
  intro h
  have h1 := (h defaultOfflineOracle "127.0.0.1" {} (.ok [])).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1

example : ¬ Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome
    { getaddrinfo := fun _ _ =>
        pure (.error { kind := .otherGai, gaiCode := -13, errno? := none, message := "x" }) }) := by
  intro h
  have h1 := (h defaultOfflineOracle "127.0.0.1" {} (.ok [])).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun _ => { getaddrinfo := fun _ _ => .ok [] })) := by
  intro h
  have h1 := (h (fun _ _ _ => .ok ByteArray.empty) "127.0.0.1" {} []).1
  simp [allowedDnsOutcome, validateHost, String.any] at h1

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun _ => { getaddrinfo := fun _ _ =>
      Except.error ({ kind := .nameNotFound, gaiCode := EAI_FAIL, errno? := none, message := "x" }) })) := by
  intro h
  let exp := [DnsAddr.ipv4 127 0 0 1]
  have h2 := (h (fun _ _ _ => .ok (encodeWireRecords exp)) "example.invalid." {} exp).2.1
  simp [allowedDnsOutcome, parsePureNumericAddr?, parseScopedNonNumericZone?,
    validateHost, String.any] at h2
  exact absurd h2 (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun raw =>
      { getaddrinfo := fun host hints =>
          match raw host hints.sockType.toWire hints.family.toWire with
          | .ok _ => .ok [.ipv4 127 0 0 1]
          | .error _ => Except.error ({ kind := .nameNotFound, gaiCode := EAI_FAIL, errno? := none, message := "x" }) })) := by
  intro h
  let exp := [DnsAddr.ipv4 127 0 0 1]
  have h2 := (h
    (fun _ fam sock =>
      if fam == 1 && sock == 2 then .ok (encodeWireRecords exp)
      else .error (EAI_FAIL, 0, ByteArray.empty))
    "127.0.0.1" { family := .ipv4, sockType := .dgram } exp).2.1
  simp [allowedDnsOutcome, parsePureNumericAddr?, validateHost, String.any] at h2
  exact absurd h2 (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun raw =>
      { getaddrinfo := fun host hints =>
          match (Internal.mkDnsOpsM (m := Id) { getaddrinfo := raw }).getaddrinfo host hints with
          | .ok xs => .ok xs
          | .error e => .error { e with errno? := none } })) := by
  intro h
  have h3 := (h (fun _ _ _ => .error (EAI_SYSTEM, Errno.ENOMEM, "oom".toUTF8)) "127.0.0.1" {} []).2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at h3
  have hv : validateHost "127.0.0.1" = true := by simp [validateHost, String.any]
  rw [hv] at h3
  dsimp at h3
  rw [Internal.mkDnsOpsM_id_error_eq "127.0.0.1" hv {} EAI_SYSTEM Errno.ENOMEM "oom".toUTF8] at h3
  injection h3 with hErr
  injection hErr with _ _ hEno _
  exact absurd hEno (by decide)

example : ¬ Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
    (fun raw =>
      { getaddrinfo := fun host hints =>
          match (Internal.mkDnsOpsM (m := Id) { getaddrinfo := raw }).getaddrinfo host hints with
          | .ok xs => .ok xs
          | .error e => .error { e with message := "x" } })) := by
  intro h
  have h3 := (h (fun _ _ _ => .error (EAI_AGAIN, 0, "temp err".toUTF8)) "127.0.0.1" {} []).2.2.1
  dsimp [Core.NondetTest.assert, Bind.bind] at h3
  have hv : validateHost "127.0.0.1" = true := by simp [validateHost, String.any]
  rw [hv] at h3
  dsimp at h3
  rw [Internal.mkDnsOpsM_id_error_eq "127.0.0.1" hv {} EAI_AGAIN 0 "temp err".toUTF8] at h3
  injection h3 with hErr
  injection hErr with _ _ _ hMsg
  have hUtf8 : String.fromUTF8? "temp err".toUTF8 = some "temp err" := by
    simp [String.fromUTF8?, String.toUTF8, "temp err".isValidUTF8]
  rw [hUtf8] at hMsg
  exact absurd hMsg (by decide)

example : ¬ Core.AllPass (test_dns_healthyStep_and_healthyModelOps
    (ops := { getaddrinfo := fun host hints => do
      let env ← get
      if !validateHost host then
        return .error invalidHostError
      else
        match parsePureNumericAddr? host with
        | some rawAddr =>
          match mapAddrForHints hints rawAddr with
          | some expAddr => return .ok (expandSockType hints [expAddr])
          | none => return .error (emptyPayloadError host hints)
        | none =>
          let _ := env
          return .error (emptyPayloadError host hints) })) := by
  intro h
  have hvLocal : validateHost "localhost" = true := by simp [validateHost, String.any]
  have hPLoc : parsePureNumericAddr? "localhost" = none := rfl
  have hLoc :
      ((if !validateHost "localhost" then
          (pure (.error invalidHostError) : StateM HealthyEnv DnsOutcome)
        else
          match parsePureNumericAddr? "localhost" with
          | some rawAddr =>
            match mapAddrForHints { family := .any, sockType := .stream } rawAddr with
            | some expAddr => pure (.ok (expandSockType { family := .any, sockType := .stream } [expAddr]))
            | none => pure (.error (emptyPayloadError "localhost" { family := .any, sockType := .stream }))
          | none =>
            pure (.error (emptyPayloadError "localhost" { family := .any, sockType := .stream }))).run
        (HealthyEnv.initial 1 defaultOfflineOracle)) =
      (.ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0, .ipv4 127 0 0 1],
       HealthyEnv.initial 1 defaultOfflineOracle) := h.2.2.2.1
  rw [hvLocal, hPLoc] at hLoc
  cases hLoc

example : ¬ Core.AllPass (test_dns_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if !env.wf || isCriticalFault out then none
      else if allowedDnsOutcome req.host req.hints out then some env
      else none)) := by
  intro h
  have hNumAgain := h.2.2.2.2.2.1.1
  have hv127 : validateHost "127.0.0.1" = true := by simp [validateHost, String.any]
  have hMsgX : ("x" : String).isEmpty = false := by simp [String.isEmpty]
  have hMis : isNumericFamilyMismatch "127.0.0.1" { family := .ipv4, sockType := .stream } = false := rfl
  have hAo : allowedDnsOutcome "127.0.0.1" { family := .ipv4, sockType := .stream }
      (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" }) = true := by
    simp only [allowedDnsOutcome, hv127, hMsgX, hMis, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    decide
  have hNoBad : (!(HealthyEnv.initial 1 defaultOfflineOracle).wf ||
      isCriticalFault (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" })) = false := by
    decide
  change (if !(HealthyEnv.initial 1 defaultOfflineOracle).wf ||
      isCriticalFault (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" }) then none
    else if allowedDnsOutcome "127.0.0.1" { family := .ipv4, sockType := .stream }
      (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" }) then
      some (HealthyEnv.initial 1 defaultOfflineOracle) else none) = none at hNumAgain
  rw [hNoBad, hAo] at hNumAgain
  cases hNumAgain

example : ¬ Core.AllPass (test_dns_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if !env.wf || isCriticalFault out then none
      else (allowedStep env.state req out).map (fun s' => { state := s', eintrBudget := env.eintrBudget }))) := by
  intro h
  have hEintr0 := h.2.2.2.2.2.2.2.2.1.2
  have hvLocal : validateHost "localhost" = true := by simp [validateHost, String.any]
  have hMsgX : ("x" : String).isEmpty = false := by simp [String.isEmpty]
  have hPLoc : parsePureNumericAddr? "localhost" = none := rfl
  have hHLoc : parseHybridScopedNumericZone? "localhost" = none := rfl
  have hMisLoc : isNumericFamilyMismatch "localhost" {} = false := rfl
  have hAo : allowedDnsOutcome "localhost" {}
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) = true := by
    simp only [allowedDnsOutcome, hvLocal, hMsgX, hMisLoc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    decide
  have hAl : allowedStep (HealthyEnv.initial 0 defaultOfflineOracle).state { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) =
      some DnsState.initial := by
    unfold allowedStep
    rw [hAo]
    simp [HealthyEnv.initial, DnsState.initial, hvLocal, hPLoc, hHLoc]
  have hNoBad : (!(HealthyEnv.initial 0 defaultOfflineOracle).wf ||
      isCriticalFault (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" })) = false := by
    decide
  change (if !(HealthyEnv.initial 0 defaultOfflineOracle).wf ||
      isCriticalFault (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) then none
    else (allowedStep (HealthyEnv.initial 0 defaultOfflineOracle).state { host := "localhost" }
      (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" })).map _) = none at hEintr0
  rw [hNoBad, hAl] at hEintr0
  cases hEintr0

example : ¬ Core.AllPass (test_dns_healthyStep_and_healthyModelOps
    (ops := { getaddrinfo := fun host hints env =>
      match parsePureNumericAddr? host, parseHybridScopedNumericZone? host with
      | none, some (baseAddr, sc) =>
        if hints.family == .ipv4 then
          (.error (emptyPayloadError host hints), env)
        else
          (.ok (expandSockType hints [withIpv6Scope sc baseAddr]), env)
      | _, _ => (healthyModelResolve env.state.oracle host hints, env) })) := by
  intro h
  let ifaceOracle : DnsOracle :=
    { lookup := fun _ _ => .ok [.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7] }
  let env7 : HealthyEnv := { state := { oracle := ifaceOracle, ambientSeccomp := false }, eintrBudget := 1 }
  let hostHyb := "fe80::1%305419896"
  let hints6 : ResolveHints := { family := .ipv6, sockType := .stream }
  have hvHyb : validateHost hostHyb = true := by simp [hostHyb, validateHost, String.any]
  have hHHyb : parseHybridScopedNumericZone? hostHyb =
      some (.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0, 305419896) := by decide
  have hPHyb : parsePureNumericAddr? hostHyb = none :=
    parsePureNumericAddr_none_of_parseHybridScopedNumericZone hHHyb
  have h0 := (h.2.2.2.2.2.2.2.2.2 env7 rfl hostHyb hints6).2.1.2
    (.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0) 305419896 hHHyb rfl
  rw [hPHyb, hHHyb] at h0
  have hMod : modelResolve ifaceOracle hostHyb hints6 =
      .ok [.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7] := by
    unfold modelResolve normalizeOracleOutcome ifaceOracle
    simp only [hvHyb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPHyb, hHHyb]
    rfl
  rw [hMod] at h0
  dsimp only [expandSockType, withIpv6Scope, Bool.false_eq_true, ↓reduceIte] at h0
  injection h0 with hList
  injection hList with hHead _
  exact absurd (congrArg DnsAddr.scopeId hHead) (by decide)

example : ¬ Core.AllPass (test_dns_healthyStep_and_healthyModelOps
    (ops := { getaddrinfo := fun host hints env =>
      if host == "fe80::1%eth0" then
        (.error (emptyPayloadError host hints), env)
      else
        (healthyModelResolve env.state.oracle host hints, env) })) := by
  intro h
  let ifaceOracle : DnsOracle :=
    { lookup := fun _ _ => .ok [.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7] }
  let env7 : HealthyEnv := { state := { oracle := ifaceOracle, ambientSeccomp := false }, eintrBudget := 1 }
  let hostSym := "fe80::1%eth0"
  let hints6 : ResolveHints := { family := .ipv6, sockType := .stream }
  have hvSym : validateHost hostSym = true := by simp [hostSym, validateHost, String.any]
  have hPSym : parsePureNumericAddr? hostSym = none := by decide
  have hHSym : parseHybridScopedNumericZone? hostSym = none := by decide
  have hEq := (h.2.2.2.2.2.2.2.2.2 env7 rfl hostSym hints6).2.2.1.2 ⟨hPSym, hHSym⟩
  have hRun : ((({ getaddrinfo := fun host hints env =>
      if host == "fe80::1%eth0" then
        (.error (emptyPayloadError host hints), env)
      else
        (healthyModelResolve env.state.oracle host hints, env) } : DnsOpsM (StateM HealthyEnv)).getaddrinfo
      hostSym hints6).run env7).1 = .error (emptyPayloadError hostSym hints6) := rfl
  change ((({ getaddrinfo := fun host hints env =>
      if host == "fe80::1%eth0" then
        (.error (emptyPayloadError host hints), env)
      else
        (healthyModelResolve env.state.oracle host hints, env) } : DnsOpsM (StateM HealthyEnv)).getaddrinfo
      hostSym hints6).run env7).1 = _ at hEq
  rw [hRun] at hEq
  have hMod : modelResolve ifaceOracle hostSym hints6 =
      .ok [.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7] := by
    have hSc : parseScopedNonNumericZone? hostSym =
        some (.ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0, ['e', 't', 'h', '0']) := by decide
    unfold modelResolve normalizeOracleOutcome ifaceOracle
    simp only [hvSym, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPSym, hHSym, hSc]
    rfl
  rw [hMod] at hEq
  cases hEq

example : ¬ Core.AllPass (test_dns_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if decide (env.eintrBudget ≥ 2) && isEintrOutcome out then
        (healthyStep env req out).map (fun env' => { env' with eintrBudget := env.eintrBudget })
      else
        healthyStep env req out)) := by
  intro h
  let outEi : DnsOutcome :=
    .error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }
  have hvLocal : validateHost "localhost" = true := by simp [validateHost, String.any]
  have hMsgX : ("x" : String).isEmpty = false := by simp [String.isEmpty]
  have hAo : allowedDnsOutcome "localhost" {} outEi = true := by
    simp only [outEi, allowedDnsOutcome, hvLocal, hMsgX,
      show isNumericFamilyMismatch "localhost" {} = false from rfl,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    decide
  have hAl : allowedStep (HealthyEnv.initial 2 defaultOfflineOracle).state { host := "localhost" } outEi =
      some DnsState.initial := by
    unfold allowedStep
    rw [hAo]
    simp [HealthyEnv.initial, DnsState.initial, hvLocal,
      show parsePureNumericAddr? "localhost" = none from rfl,
      show parseHybridScopedNumericZone? "localhost" = none from rfl]
  have hStep := ((h.2.2.2.2.2.2.2.2.2 (HealthyEnv.initial 1 defaultOfflineOracle) rfl "localhost" {}).2.2.2
    (HealthyEnv.initial 2 defaultOfflineOracle) { host := "localhost" } outEi).1
  dsimp only [healthyStep] at hStep
  have hG : (!(HealthyEnv.initial 2 defaultOfflineOracle).wf || isCriticalFault outEi) = false := by decide
  rw [hG, hAl] at hStep
  exact absurd (congrArg (Option.map HealthyEnv.eintrBudget) hStep) (by decide)

end LeanSwe.LinuxSyscall.Dns
