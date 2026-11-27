import Core.Obeys
import LeanSwe.LinuxSyscall.Dns.Model.Refines
import LeanSwe.LinuxSyscall.Dns.Proofs.OracleAndMkRawProofs

/-!
# Capability-Parametric `Core.Obeys` Proofs for `LeanSwe.LinuxSyscall.Dns`

Proves `mkDnsOpsM_obeysStepFrom` and `rawHealthyModelOps_obeysStep_of` for
`LeanSwe.LinuxSyscall.Dns.Proofs.obeys_model`.
-/

namespace LeanSwe.LinuxSyscall.Dns.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

@[simp] private theorem stateT_bind_eq {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    StateT.bind x f w = f (x w).1 (x w).2 := rfl

@[simp] private theorem stateT_pure_eq {W α : Type} (a : α) (w : W) :
    StateT.pure (m := Id) a w = (a, w) := rfl

private theorem decodeRawHints?_toWire (hints : ResolveHints) :
    Model.decodeRawHints? hints.family.toWire hints.sockType.toWire = some hints := by
  rcases hints with ⟨fam, st⟩
  cases fam <;> cases st <;> rfl

private theorem classifyGaiError_eq_rawGaiErrorToDnsError
    (host : String) (hints : ResolveHints) (rc : Int32) (eno : UInt32) (msgBytes : ByteArray) :
    Internal.classifyGaiError host hints rc eno msgBytes =
      Model.rawGaiErrorToDnsError host hints rc eno msgBytes := by
  unfold Internal.classifyGaiError Model.rawGaiErrorToDnsError
    Internal.decodeErrorMessage Model.decodeRawErrorMessage
  rw [Internal.normalizeGaiCodeForHostImpl_eq]
  rfl

private theorem allowedDnsOutcome_of_healthyStep {env env' : HealthyEnv}
    {req : DnsReq} {out : DnsOutcome}
    (h : healthyStep env req out = some env') :
    allowedDnsOutcome req.host req.hints out = true := by
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault out) = true
  · simp [hBad] at h
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => simp [hAl] at h
    | some _ =>
      unfold allowedStep at hAl
      cases hAo : allowedDnsOutcome req.host req.hints out
      · simp [hAo] at hAl
      · rfl

private theorem fromUTF8?_toUTF8_eq (s : String) :
    String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  split
  · rfl
  · next hNot => exact absurd s.isValidUTF8 hNot

private theorem dnsErrorKind_eq_of_beq {a b : DnsErrorKind} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem rawGaiErrorToDnsError_roundtrip
    (host : String) (hints : ResolveHints) (err : DnsError)
    (hv : validateHost host = true)
    (hAo : allowedDnsOutcome host hints (.error err) = true) :
    Model.rawGaiErrorToDnsError host hints err.gaiCode (err.errno?.getD 0) err.message.toUTF8 =
      err := by
  rcases err with ⟨kind, gaiCode, errno?, message⟩
  unfold allowedDnsOutcome at hAo
  have hnv : (!validateHost host) = false := by simp [hv]
  simp only [hnv, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hAo
  rcases hAo with ⟨⟨⟨⟨⟨⟨_, hValid⟩, hKindBeq⟩, hAF⟩, hMis⟩, hEno⟩, hMsgNe⟩
  have hNorm : normalizeGaiCodeForHost host hints gaiCode = gaiCode := by
    unfold normalizeGaiCodeForHost
    simp only [hValid, ↓reduceIte]
    by_cases hM : isNumericFamilyMismatch host hints = true
    · simp only [hM, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq] at hMis ⊢
      have h1 : (gaiCode == EAI_NONAME) = false := beq_false_of_ne hMis.1
      have h2 : (gaiCode == EAI_NODATA) = false := beq_false_of_ne hMis.2
      simp [h1, h2]
    · have hMF : isNumericFamilyMismatch host hints = false := Bool.eq_false_iff.mpr hM
      simp only [hMF, Bool.false_eq_true, ↓reduceIte] at hAF ⊢
      cases hEqAF : (gaiCode == EAI_ADDRFAMILY)
      · rfl
      · rw [hEqAF] at hAF; simp at hAF
  have hKind : classifyGaiKind gaiCode = kind := (dnsErrorKind_eq_of_beq hKindBeq).symm
  have hMsg : Model.decodeRawErrorMessage message.toUTF8 = message := by
    unfold Model.decodeRawErrorMessage
    rw [fromUTF8?_toUTF8_eq]
    have hEmptyF : message.isEmpty = false := by
      cases he : message.isEmpty <;> simp_all
    simp [hEmptyF]
  unfold Model.rawGaiErrorToDnsError
  dsimp only
  rw [hNorm, hKind, hMsg]
  cases errno? with
  | none => simp [Option.getD]
  | some eno =>
    dsimp only [Option.getD] at hEno ⊢
    simp [hEno]

/-- `Internal.mkDnsOpsM` lifts any raw C-ABI bundle obeying `Model.allowedRawStep` to `Model.allowedPkgStep`. -/
theorem mkDnsOpsM_obeysStepFrom :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkDnsOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  rcases req with ⟨host, hints⟩
  dsimp only [Function.comp, id] at hWf ⊢
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    have hStep := hRaw w
      { host := host, familyWire := hints.family.toWire, sockTypeWire := hints.sockType.toWire } hWf
    dsimp only [Model.execRawStep, Model.allowedRawStep, StateT.run] at hStep
    simp only [hv, ↓reduceIte, decodeRawHints?_toWire hints] at hStep
    dsimp only [Model.execPkgStep, execDnsReq, Internal.mkDnsOpsM,
      Bind.bind, Pure.pure, StateT.run, Model.allowedPkgStep]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq]
    rcases hCall : raw.getaddrinfo host hints.family.toWire hints.sockType.toWire w with ⟨rawRes, w'⟩
    rw [hCall] at hStep
    cases rawRes with
    | error p =>
      rcases p with ⟨rc, eno, msgBytes⟩
      dsimp only [stateT_pure_eq] at hStep ⊢
      rw [classifyGaiError_eq_rawGaiErrorToDnsError]
      exact hStep
    | ok recBytes =>
      dsimp only at hStep ⊢
      rcases hStep with ⟨addrs, rfl, hHealthy⟩
      have hAo : allowedDnsOutcome host hints (.ok addrs) = true :=
        allowedDnsOutcome_of_healthyStep hHealthy
      unfold allowedDnsOutcome at hAo
      simp only [hnv, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hAo
      rcases hAo with ⟨⟨⟨hNemp, hAll⟩, hMult⟩, hTrail⟩
      have hemp : addrs.isEmpty = false := by
        cases h1 : addrs.isEmpty <;> simp_all
      have hDec : Internal.decodeRecords (encodeWireRecords addrs) = .ok addrs :=
        decodeRecords_encodeRecords addrs
      have hBadF : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = false := by
        simp [hemp, hAll]
      have hMultF : (!matchesSockTypeMultiplicity hints addrs) = false := by
        simp [hMult]
      rw [hDec]
      dsimp only
      simp only [hBadF, Internal.matchesSockTypeMultiplicityImpl_eq, hMultF, Bool.false_eq_true, ↓reduceIte,
        Internal.parsePureNumericAddrImpl_eq, Internal.mapAddrForHintsImpl_eq,
        Internal.expandSockTypeImpl_eq, Internal.parseHybridScopedNumericZoneImpl_eq,
        Internal.matchesHybridScopedAddrsImpl_eq, Internal.parseScopedNonNumericZoneImpl_eq,
        Internal.canSymbolicScopedOkImpl_eq, Internal.matchesSymbolicScopedAddrsImpl_eq]
      cases hP : parsePureNumericAddr? host with
      | some rawAddr =>
        simp only [hP] at hTrail
        cases hM : mapAddrForHints hints rawAddr with
        | none => simp [hM] at hTrail
        | some expAddr =>
          simp only [hM] at hTrail ⊢
          simp only [hTrail, ↓reduceIte, stateT_pure_eq]
          exact hHealthy
      | none =>
        simp only [hP] at hTrail
        cases hHyb : parseHybridScopedNumericZone? host with
        | some hp =>
          rcases hp with ⟨baseAddr, sc⟩
          simp only [hHyb] at hTrail ⊢
          simp only [hTrail, ↓reduceIte, stateT_pure_eq]
          exact hHealthy
        | none =>
          simp only [hHyb] at hTrail
          cases hZ : parseScopedNonNumericZone? host with
          | none =>
            simpa [stateT_pure_eq] using hHealthy
          | some p =>
            rcases p with ⟨baseAddr, zoneCs⟩
            simp only [hZ] at hTrail ⊢
            simp only [hTrail, ↓reduceIte, stateT_pure_eq]
            exact hHealthy
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [Model.execPkgStep, execDnsReq, Internal.mkDnsOpsM,
      Bind.bind, Pure.pure, StateT.run, stateT_pure_eq,
      Model.allowedPkgStep, hnv, ↓reduceIte]
    have hAo : allowedDnsOutcome host hints (.error invalidHostError) = true := by
      unfold allowedDnsOutcome
      simp only [hnv, ↓reduceIte]
      decide
    have hAl : allowedStep (proj w).state { host := host, hints := hints } (.error invalidHostError) =
        some (proj w).state := by
      unfold allowedStep
      simp [hAo, hnv]
    have hNoC : isCriticalFault (.error invalidHostError) = false := by decide
    have hNoE : isEintrOutcome (.error invalidHostError) = false := by decide
    rcases hw : proj w with ⟨st, bud⟩
    rw [hw] at hWf hAl
    rw [allowedStep_healthy_tight ⟨st, bud⟩ { host := host, hints := hints }
      (.error invalidHostError) st hAl hWf (by simp [hNoE]) hNoC]
    simp [hNoE]

/-- `Model.rawHealthyModelOps` satisfies `Model.allowedRawStep` given `RefinesHealthyDns healthyModelOps`. -/
theorem rawHealthyModelOps_obeysStep_of
    (hRef : RefinesHealthyDns healthyModelOps) :
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep := by
  intro env req hWf
  rcases req with ⟨host, famWire, sockWire⟩
  simp only [id, Model.execRawStep, Model.allowedRawStep, Model.rawHealthyModelOps,
    Bind.bind, Pure.pure, StateT.run] at hWf ⊢
  by_cases hv : validateHost host = true
  · simp only [hv, ↓reduceIte]
    cases hDec : Model.decodeRawHints? famWire sockWire with
    | none => simp
    | some hints =>
      simp only [stateT_bind_eq]
      have hHealthy := hRef env { host := host, hints := hints } hWf
      have hRun : (healthyModelOps.getaddrinfo host hints) env =
          (healthyModelResolve env.state.oracle host hints, env) := rfl
      dsimp only [id, execDnsReq, StateT.run] at hHealthy
      rw [hRun] at hHealthy ⊢
      dsimp only at hHealthy ⊢
      cases hRes : healthyModelResolve env.state.oracle host hints with
      | ok addrs =>
        rw [hRes] at hHealthy
        simp only [stateT_pure_eq]
        exact ⟨addrs, rfl, hHealthy⟩
      | error err =>
        rw [hRes] at hHealthy
        simp only [stateT_pure_eq]
        have hAo : allowedDnsOutcome host hints (.error err) = true :=
          allowedDnsOutcome_of_healthyStep hHealthy
        rw [rawGaiErrorToDnsError_roundtrip host hints err hv hAo]
        exact hHealthy
  · simp [hv]

end LeanSwe.LinuxSyscall.Dns.Proofs
