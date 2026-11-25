import Core.Obeys
import LeanSwe.LinuxSyscall.Dns.Model.Refines
import LeanSwe.LinuxSyscall.Dns.Proofs.OracleAndMkRawProofs
import LeanSwe.LinuxSyscall.Dns.Proofs.Obeys

namespace LeanSwe.LinuxSyscall.Dns.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

/-- Soundness of `healthyStep` with respect to `allowedStep`: every `healthyStep` transition is a valid `allowedStep` transition (hence also satisfies `allowedDnsOutcome`), preserves `HealthyEnv.wf`, excludes curated critical OS faults, and strictly decreases `eintrBudget` on `EINTR`. -/
theorem healthyStep_implies_allowedStep
    (env env' : HealthyEnv) (req : DnsReq) (out : DnsOutcome)
    (h : healthyStep env req out = some env') :
    allowedStep env.state req out = some env'.state ∧
    allowedDnsOutcome req.host req.hints out = true ∧
    env.wf = true ∧
    env'.wf = true ∧
    isCriticalFault out = false ∧
    env'.eintrBudget ≤ env.eintrBudget ∧
    (isEintrOutcome out = true → env'.eintrBudget < env.eintrBudget) := by
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault out) = true
  · simp [hBad] at h
  · have hWf : env.wf = true := by
      cases hw : env.wf <;> simp_all
    have hNoCrit : isCriticalFault out = false := by
      cases hc : isCriticalFault out <;> simp_all
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => rw [hAl] at h; contradiction
    | some s' =>
      rw [hAl] at h
      dsimp only at h
      have hsEq : s' = env.state := allowedStep_state_eq env.state s' req out hAl
      have hAllowedOut : allowedDnsOutcome req.host req.hints out = true := by
        unfold allowedStep at hAl
        cases hAo : allowedDnsOutcome req.host req.hints out
        · simp [hAo] at hAl
        · rfl
      cases hEi : isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        dsimp only
        exact ⟨rfl, hAllowedOut, hWf, by simpa [HealthyEnv.wf, hsEq] using hWf,
          hNoCrit, Nat.le_refl _, fun hc => by cases hc⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hb : env.eintrBudget > 0
        · simp only [hb, ↓reduceIte, Option.some.injEq] at h
          subst h
          dsimp only
          exact ⟨rfl, hAllowedOut, hWf, by simpa [HealthyEnv.wf, hsEq] using hWf,
            hNoCrit, Nat.sub_le _ _, fun _ => by omega⟩
        · simp [hb] at h

/-- Tightness on numeric IP literals: on a healthy OS (`healthyStep`), any valid in-family pure numeric IPv4 or IPv6 literal (`parsePureNumericAddr?` + `mapAddrForHints`) succeeds unconditionally with `expandSockType hints [expAddr]`, never failing with `EAI_AGAIN`, `EAI_NONAME`, `EAI_FAIL`, or `EAI_SYSTEM`. -/
theorem healthyStep_numeric_literal_succeeds
    (env env' : HealthyEnv) (host : String) (hints : ResolveHints)
    (rawAddr expAddr : DnsAddr) (out : DnsOutcome)
    (hP : parsePureNumericAddr? host = some rawAddr)
    (hM : mapAddrForHints hints rawAddr = some expAddr)
    (hStep : healthyStep env { host := host, hints := hints } out = some env') :
    out = .ok (expandSockType hints [expAddr]) ∧
    env'.eintrBudget = env.eintrBudget := by
  rcases healthyStep_implies_allowedStep env env' { host := host, hints := hints } out hStep with
    ⟨hAl, hAo, hWf, _, hNoCrit, _, _⟩
  have hv : validateHost host = true := validateHost_of_parsePureNumericAddr hP
  have hSecF : env.state.ambientSeccomp = false := by
    unfold HealthyEnv.wf at hWf
    cases hb : env.state.ambientSeccomp <;> simp_all
  unfold allowedStep at hAl
  simp only [hAo, hv, hSecF, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hP, hM] at hAl
  cases out with
  | error err =>
    simp [hNoCrit] at hAl
  | ok addrs =>
    unfold allowedDnsOutcome at hAo
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hP, hM, Bool.and_eq_true] at hAo
    have hEq : addrs = expandSockType hints [expAddr] := list_dnsAddr_eq_of_beq hAo.2
    subst hEq
    refine ⟨rfl, ?_⟩
    unfold healthyStep at hStep
    simp only [hWf, Bool.not_true, isCriticalFault, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hStep
    cases hAl' : allowedStep env.state { host := host, hints := hints } (.ok (expandSockType hints [expAddr])) with
    | none => simp [hAl'] at hStep
    | some s2 =>
      simp only [hAl', isEintrOutcome, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hStep
      exact (congrArg HealthyEnv.eintrBudget hStep).symm

/-- Universal corollary over any `ops` satisfying `RefinesHealthyDnsAt proj ops`: valid in-family numeric IP literals resolve unconditionally to `.ok (expandSockType hints [expAddr])` without consuming `eintrBudget`. -/
theorem refinesHealthy_numeric_literal_ok
    {W : Type} {proj : W → HealthyEnv} {ops : DnsOpsM (StateM W)}
    (hRef : RefinesHealthyDnsAt proj ops)
    (w : W) (host : String) (hints : ResolveHints) (rawAddr expAddr : DnsAddr)
    (hWf : (proj w).wf = true)
    (hP : parsePureNumericAddr? host = some rawAddr)
    (hM : mapAddrForHints hints rawAddr = some expAddr) :
    let (res, w') := (ops.getaddrinfo host hints).run w
    res = .ok (expandSockType hints [expAddr]) ∧
    (proj w').wf = true ∧
    (proj w').eintrBudget = (proj w).eintrBudget := by
  have hStep := hRef w { host := host, hints := hints } hWf
  dsimp only [execDnsReq, StateT.run] at hStep ⊢
  cases hRun : ops.getaddrinfo host hints w with
  | mk res w' =>
    rw [hRun] at hStep
    dsimp only at hStep ⊢
    rcases healthyStep_numeric_literal_succeeds (proj w) (proj w') host hints rawAddr expAddr res hP hM hStep with
      ⟨hRes, hBud⟩
    rcases healthyStep_implies_allowedStep (proj w) (proj w') { host := host, hints := hints } res hStep with
      ⟨_, _, _, hWf', _, _, _⟩
    exact ⟨hRes, hWf', hBud⟩

/-- Tightness on `< IFNAMSIZ` numeric-scoped link/multicast-local IPv6 literals: on a healthy OS (`healthyStep`), any non-`.ipv4` hybrid numeric-scoped literal (`parseHybridScopedNumericZone?`) succeeds unconditionally with `.ok addrs` satisfying `matchesHybridScopedAddrs hints baseAddr sc addrs = true` (reflecting `glibc` `if_nametoindex`-before-`strtoul` precedence) without consuming `eintrBudget`. -/
theorem healthyStep_hybrid_scoped_succeeds
    (env env' : HealthyEnv) (host : String) (hints : ResolveHints)
    (baseAddr : DnsAddr) (sc : UInt32) (out : DnsOutcome)
    (hHyb : parseHybridScopedNumericZone? host = some (baseAddr, sc))
    (hFam : (hints.family != .ipv4) = true)
    (hStep : healthyStep env { host := host, hints := hints } out = some env') :
    (∃ addrs, out = .ok addrs ∧ matchesHybridScopedAddrs hints baseAddr sc addrs = true) ∧
    env'.eintrBudget = env.eintrBudget := by
  rcases healthyStep_implies_allowedStep env env' { host := host, hints := hints } out hStep with
    ⟨hAl, hAo, hWf, _, hNoCrit, _, _⟩
  have hv : validateHost host = true := validateHost_of_parseHybridScopedNumericZone hHyb
  have hPureNone : parsePureNumericAddr? host = none :=
    parsePureNumericAddr_none_of_parseHybridScopedNumericZone hHyb
  have hSecF : env.state.ambientSeccomp = false := by
    unfold HealthyEnv.wf at hWf
    cases hb : env.state.ambientSeccomp <;> simp_all
  unfold allowedStep at hAl
  simp only [hAo, hv, hSecF, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    hPureNone, hHyb, hFam] at hAl
  cases out with
  | error _ => simp [hNoCrit] at hAl
  | ok addrs =>
    unfold allowedDnsOutcome at hAo
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hPureNone, hHyb, Bool.and_eq_true] at hAo
    refine ⟨⟨addrs, rfl, hAo.2⟩, ?_⟩
    unfold healthyStep at hStep
    simp only [hWf, Bool.not_true, isCriticalFault, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hStep
    cases hAl' : allowedStep env.state { host := host, hints := hints } (.ok addrs) with
    | none => simp [hAl'] at hStep
    | some s2 =>
      simp only [hAl', isEintrOutcome, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hStep
      exact (congrArg HealthyEnv.eintrBudget hStep).symm


/-- Reference `healthyModelOps` refines `healthyStep` universally across all hostnames, hints, and `DnsOracle` instances. -/
theorem healthyModelOps_refinesHealthyDns :
    RefinesHealthyDns healthyModelOps := by
  intro env req hWf
  dsimp only [id, execDnsReq, healthyModelOps, Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get] at hWf ⊢
  have hSecF : env.state.ambientSeccomp = false := by
    unfold HealthyEnv.wf at hWf
    cases hb : env.state.ambientSeccomp <;> simp_all
  unfold healthyModelResolve
  by_cases hv : validateHost req.host = true
  · have hnv : (!validateHost req.host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    cases hP : parsePureNumericAddr? req.host with
    | some rawAddr =>
      dsimp only
      cases hM : mapAddrForHints req.hints rawAddr with
      | some expAddr =>
        dsimp only
        have hne : (expandSockType req.hints [expAddr]).isEmpty = false := by
          cases hsock : req.hints.sockType <;> simp [expandSockType, hsock]
        have hExpMatch : ([expAddr] : List DnsAddr).all (addrMatchesHints req.hints) = true := by
          simp [mapAddrForHints_matchesHints req.hints rawAddr expAddr hM]
        have hAll := expandSockType_all_matchesHints req.hints [expAddr] hExpMatch
        have hMult := expandSockType_matchesSockTypeMultiplicity req.hints [expAddr]
        have hAo : allowedDnsOutcome req.host req.hints (.ok (expandSockType req.hints [expAddr])) = true := by
          unfold allowedDnsOutcome
          simp [hnv, hne, hAll, hMult, hP, hM, list_dnsAddr_beq_refl]
        have hAl : allowedStep env.state req (.ok (expandSockType req.hints [expAddr])) = some env.state := by
          unfold allowedStep
          simp [hAo, hnv, hSecF, hP, hM]
        rw [allowedStep_healthy_tight env req _ env.state hAl hWf (fun hc => by cases hc) rfl]
        rfl
      | none =>
        dsimp only
        have hMis : isNumericFamilyMismatch req.host req.hints = true := by
          unfold isNumericFamilyMismatch
          simp [hP, hM]
        have hAo := allowedDnsOutcome_emptyPayloadError req.host hv req.hints
        have hNoCE := emptyPayloadError_not_critical_or_eintr req.host req.hints
        have hEmpEq : emptyPayloadError req.host req.hints =
            { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none,
              message := "Address family for hostname not supported" } := by
          unfold emptyPayloadError
          simp [hMis]
        have hAl : allowedStep env.state req (.error (emptyPayloadError req.host req.hints)) = some env.state := by
          unfold allowedStep
          rw [hAo]
          simp only [Bool.not_true, hnv, hSecF, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hP, hM, hEmpEq]
          rfl
        rw [allowedStep_healthy_tight env req _ env.state hAl hWf (by simp [hNoCE.2]) hNoCE.1]
        simp [hNoCE.2]
    | none =>
      dsimp only
      cases hHyb : parseHybridScopedNumericZone? req.host with
      | some hp =>
        rcases hp with ⟨baseAddr, sc⟩
        dsimp only
        by_cases hFam4 : (req.hints.family == .ipv4) = true
        · simp only [hFam4, ↓reduceIte]
          have hFamNe : (req.hints.family != .ipv4) = false := by
            revert hFam4; cases req.hints.family <;> decide
          have hMis : isNumericFamilyMismatch req.host req.hints = true := by
            unfold isNumericFamilyMismatch
            simp [hP, hHyb, hFam4]
          have hAo := allowedDnsOutcome_emptyPayloadError req.host hv req.hints
          have hNoCE := emptyPayloadError_not_critical_or_eintr req.host req.hints
          have hEmpEq : emptyPayloadError req.host req.hints =
              { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none,
                message := "Address family for hostname not supported" } := by
            unfold emptyPayloadError
            simp [hMis]
          have hAl : allowedStep env.state req (.error (emptyPayloadError req.host req.hints)) = some env.state := by
            unfold allowedStep
            rw [hAo]
            simp only [Bool.not_true, hnv, hSecF, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hP, hHyb, hFamNe, hEmpEq]
            rfl
          rw [allowedStep_healthy_tight env req _ env.state hAl hWf (by simp [hNoCE.2]) hNoCE.1]
          simp [hNoCE.2]
        · have hFam4F : (req.hints.family == .ipv4) = false := Bool.eq_false_iff.mpr hFam4
          have hFamNe : (req.hints.family != .ipv4) = true := by
            revert hFam4F; cases req.hints.family <;> decide
          simp only [hFam4F, Bool.false_eq_true, ↓reduceIte]
          cases hNorm : normalizeOracleOutcome req.host req.hints (env.state.oracle.lookup req.host req.hints) with
          | ok addrs =>
            dsimp only
            have hAo : allowedDnsOutcome req.host req.hints (.ok addrs) = true := by
              have hs := normalizeOracleOutcome_soundAgainstAllowedOutcome req.host req.hints
                (env.state.oracle.lookup req.host req.hints)
              rw [hNorm] at hs
              exact hs
            have hAl : allowedStep env.state req (.ok addrs) = some env.state := by
              unfold allowedStep
              simp [hAo, hnv, hSecF, hP, hHyb, hFamNe]
            rw [allowedStep_healthy_tight env req (.ok addrs) env.state hAl hWf (fun hc => by cases hc) rfl]
            rfl
          | error _ =>
            dsimp only
            let fbAddrs := expandSockType req.hints [withIpv6Scope sc baseAddr]
            have hne : fbAddrs.isEmpty = false := by
              cases hsock : req.hints.sockType <;> simp [fbAddrs, expandSockType, hsock]
            have hSymAl := allowsSymbolicIpv6Zone_of_parseHybridScopedNumericZone hHyb
            have hOneMatch : ([withIpv6Scope sc baseAddr] : List DnsAddr).all (addrMatchesHints req.hints) = true := by
              simp [addrMatchesHints_withIpv6Scope_of_allowsSymbolic req.hints baseAddr sc hFamNe hSymAl]
            have hAll : fbAddrs.all (addrMatchesHints req.hints) = true :=
              expandSockType_all_matchesHints req.hints [withIpv6Scope sc baseAddr] hOneMatch
            have hMult : matchesSockTypeMultiplicity req.hints fbAddrs = true :=
              expandSockType_matchesSockTypeMultiplicity req.hints [withIpv6Scope sc baseAddr]
            have hHybMatch : matchesHybridScopedAddrs req.hints baseAddr sc fbAddrs = true := by
              unfold matchesHybridScopedAddrs
              simp [fbAddrs, hFamNe, list_dnsAddr_beq_refl]
            have hAo : allowedDnsOutcome req.host req.hints (.ok fbAddrs) = true := by
              unfold allowedDnsOutcome
              simp only [hnv, Bool.false_eq_true, ↓reduceIte, hne, Bool.not_false, hAll, hMult,
                hP, hHyb, hHybMatch, Bool.and_self]
            have hAl : allowedStep env.state req (.ok fbAddrs) = some env.state := by
              unfold allowedStep
              simp [hAo, hnv, hSecF, hP, hHyb, hFamNe]
            rw [allowedStep_healthy_tight env req (.ok fbAddrs) env.state hAl hWf (fun hc => by cases hc) rfl]
            rfl
      | none =>
        dsimp only
        let base := normalizeOracleOutcome req.host req.hints (env.state.oracle.lookup req.host req.hints)
        change healthyStep env req
          (if isCriticalFault base || isEintrOutcome base then .error (emptyPayloadError req.host req.hints) else base) =
          some env
        by_cases hCE : (isCriticalFault base || isEintrOutcome base) = true
        · simp only [hCE, ↓reduceIte]
          have hAo := allowedDnsOutcome_emptyPayloadError req.host hv req.hints
          have hNoCE := emptyPayloadError_not_critical_or_eintr req.host req.hints
          have hAl : allowedStep env.state req (.error (emptyPayloadError req.host req.hints)) = some env.state := by
            unfold allowedStep
            simp [hAo, hnv, hSecF, hP, hHyb]
          rw [allowedStep_healthy_tight env req _ env.state hAl hWf (by simp [hNoCE.2]) hNoCE.1]
          simp [hNoCE.2]
        · have hCEF : (isCriticalFault base || isEintrOutcome base) = false := Bool.eq_false_iff.mpr hCE
          have hNoC : isCriticalFault base = false := by
            cases hc : isCriticalFault base <;> simp_all
          have hNoE : isEintrOutcome base = false := by
            cases he : isEintrOutcome base <;> simp_all
          simp only [hCEF, Bool.false_eq_true, ↓reduceIte]
          have hAo := normalizeOracleOutcome_soundAgainstAllowedOutcome req.host req.hints
            (env.state.oracle.lookup req.host req.hints)
          have hAl : allowedStep env.state req base = some env.state := by
            unfold allowedStep
            simp [base, hAo, hnv, hSecF, hP, hHyb]
          rw [allowedStep_healthy_tight env req base env.state hAl hWf (by simp [hNoE]) hNoC]
          simp [hNoE]
  · have hnv : (!validateHost req.host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    have hAo : allowedDnsOutcome req.host req.hints (.error invalidHostError) = true := by
      unfold allowedDnsOutcome
      simp only [hnv, ↓reduceIte]
      decide
    have hAl : allowedStep env.state req (.error invalidHostError) = some env.state := by
      unfold allowedStep
      simp [hAo, hnv]
    have hNoC : isCriticalFault (.error invalidHostError) = false := by decide
    have hNoE : isEintrOutcome (.error invalidHostError) = false := by decide
    rw [allowedStep_healthy_tight env req (.error invalidHostError) env.state hAl hWf (by simp [hNoE]) hNoC]
    simp [hNoE]

/-- Oracle-fidelity of `healthyModelResolve` on non-numeric hostnames: whenever `isNumericHostLiteral host = false` and `modelResolve oracle host hints` is neither a curated critical OS fault nor `EINTR`, `healthyModelResolve oracle host hints` equals `modelResolve oracle host hints`. -/
theorem healthyModelResolve_eq_modelResolve_of_nonFault
    (oracle : DnsOracle) (host : String) (hints : ResolveHints)
    (hNonNum : isNumericHostLiteral host = false)
    (hNoCrit : isCriticalFault (modelResolve oracle host hints) = false)
    (hNoEintr : isEintrOutcome (modelResolve oracle host hints) = false) :
    healthyModelResolve oracle host hints = modelResolve oracle host hints := by
  have hPNone : parsePureNumericAddr? host = none :=
    parsePureNumericAddr_none_of_not_numericLiteral hNonNum
  have hHNone : parseHybridScopedNumericZone? host = none :=
    parseHybridScopedNumericZone_none_of_not_numericLiteral hNonNum
  unfold healthyModelResolve modelResolve at *
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte, hPNone, hHNone] at hNoCrit hNoEintr ⊢
    simp [hNoCrit, hNoEintr]
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp [hnv]

/-- Oracle-fidelity of `healthyModelResolve` on hybrid numeric-scoped IPv6 literals (`parseHybridScopedNumericZone?`): under non-`.ipv4` hints, `healthyModelResolve` returns `modelResolve oracle host hints` whenever `(modelResolve oracle host hints)` succeeds (`if_nametoindex` interface match), and otherwise falls back to `.ok (expandSockType hints [withIpv6Scope sc baseAddr])` (`strtoul` numeric scope). -/
theorem healthyModelResolve_hybrid_scoped_eq
    (oracle : DnsOracle) (host : String) (hints : ResolveHints)
    (baseAddr : DnsAddr) (sc : UInt32)
    (hHyb : parseHybridScopedNumericZone? host = some (baseAddr, sc))
    (hFam : (hints.family != .ipv4) = true) :
    healthyModelResolve oracle host hints =
      match modelResolve oracle host hints with
      | .ok addrs => .ok addrs
      | .error _ => .ok (expandSockType hints [withIpv6Scope sc baseAddr]) := by
  have hv : validateHost host = true := validateHost_of_parseHybridScopedNumericZone hHyb
  have hnv : (!validateHost host) = false := by simp [hv]
  have hPNone : parsePureNumericAddr? host = none :=
    parsePureNumericAddr_none_of_parseHybridScopedNumericZone hHyb
  have hFamF : (hints.family == .ipv4) = false := by
    revert hFam; cases hints.family <;> decide
  unfold healthyModelResolve modelResolve
  simp only [hnv, Bool.false_eq_true, ↓reduceIte, hPNone, hHyb, hFamF]
  cases normalizeOracleOutcome host hints (oracle.lookup host hints) <;> rfl

/-- Lens-lifting composition theorem: lifting any `ops` satisfying `RefinesHealthyDns` along `(getEnv, setEnv)` with `∀ w e, getEnv (setEnv w e) = e` satisfies `RefinesHealthyDnsAt getEnv`. -/
theorem refinesHealthyDnsAt_of_lens
    {W : Type} (getEnv : W → HealthyEnv) (setEnv : W → HealthyEnv → W)
    (hGetSet : ∀ (w : W) (e : HealthyEnv), getEnv (setEnv w e) = e)
    {ops : DnsOpsM (StateM HealthyEnv)} (hRef : RefinesHealthyDns ops) :
    RefinesHealthyDnsAt getEnv
      { getaddrinfo := fun host hints w =>
          let (res, e') := (ops.getaddrinfo host hints).run (getEnv w)
          (res, setEnv w e') } := by
  intro w req hWf
  have hStep := hRef (getEnv w) req hWf
  dsimp only [id, execDnsReq, StateT.run] at hStep ⊢
  cases hC : ops.getaddrinfo req.host req.hints (getEnv w) with
  | mk res e' => rw [hC] at hStep; simp only [hGetSet]; exact hStep

/-- Exact oracle-lift parity of `healthyModelResolve` on all hosts outside `parsePureNumericAddr?` and `parseHybridScopedNumericZone?` (including symbolic scoped IPv6 zones such as `"fe80::1%eth0"`): returns `.error (emptyPayloadError host hints)` on curated critical faults or `EINTR`, and `modelResolve oracle host hints` otherwise. -/
theorem healthyModelResolve_eq_of_nonPureNonHybrid
    (oracle : DnsOracle) (host : String) (hints : ResolveHints)
    (hPNone : parsePureNumericAddr? host = none)
    (hHNone : parseHybridScopedNumericZone? host = none) :
    healthyModelResolve oracle host hints =
      if isCriticalFault (modelResolve oracle host hints) ||
          isEintrOutcome (modelResolve oracle host hints) then
        .error (emptyPayloadError host hints)
      else
        modelResolve oracle host hints := by
  unfold healthyModelResolve modelResolve
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp [hnv, hPNone, hHNone]
  · have hnv : (!validateHost host) = true := by simp [hv]
    have hInvNoCE : (isCriticalFault (.error invalidHostError) ||
        isEintrOutcome (.error invalidHostError)) = false := by decide
    simp [hnv, hInvNoCE]

/-- Proof of `test_dns_healthyStep_and_healthyModelOps`. -/
theorem test_dns_healthyStep_and_healthyModelOps_ok :
    Core.AllPass test_dns_healthyStep_and_healthyModelOps := by
  dsimp only [test_dns_healthyStep_and_healthyModelOps, Core.NondetTest.assert, Bind.bind, Pure.pure]
  have hv127 : validateHost "127.0.0.1" = true := by rw [validateHost_eq]; decide
  have hvLocal : validateHost "localhost" = true := by rw [validateHost_eq]; decide
  have hvZ2 : validateHost "fe80::1%lo" = true := by rw [validateHost_eq]; decide
  have hMsgX : ("x" : String).isEmpty = false := by simp [String.isEmpty]
  have hP127 : parsePureNumericAddr? "127.0.0.1" = some (.ipv4 127 0 0 1) := rfl
  have hPLoc : parsePureNumericAddr? "localhost" = none := rfl
  have hHLoc : parseHybridScopedNumericZone? "localhost" = none := rfl
  have hPZ2 : parsePureNumericAddr? "fe80::1%lo" = none := rfl
  have hHZ2 : parseHybridScopedNumericZone? "fe80::1%lo" = none := rfl
  have hMis127v6 : isNumericFamilyMismatch "127.0.0.1" { family := .ipv6, sockType := .stream } = true := rfl
  have hMisLoc : isNumericFamilyMismatch "localhost" {} = false := rfl
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [HealthyEnv.initial, DnsState.initial, healthyModelOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      healthyModelResolve, hv127, hP127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [HealthyEnv.initial, DnsState.initial, healthyModelOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      healthyModelResolve, hvLocal, hPLoc, hHLoc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      defaultOfflineOracle, normalizeOracleOutcome, isCriticalFault, isEintrOutcome]; rfl
  · simp only [HealthyEnv.initial, DnsState.initial, healthyModelOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure, get, MonadStateOf.get, getThe, StateT.get,
      healthyModelResolve, hvZ2, hPZ2, hHZ2, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      defaultOfflineOracle, normalizeOracleOutcome, isCriticalFault, isEintrOutcome]; rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp only [healthyStep, HealthyEnv.initial, HealthyEnv.wf, DnsState.initial,
        allowedStep, allowedDnsOutcome, hv127, hMsgX, hP127]
      decide
    · simp only [healthyStep, HealthyEnv.initial, HealthyEnv.wf, DnsState.initial,
        allowedStep, allowedDnsOutcome, hv127, hMsgX, hP127]
      decide
    · have hAo : allowedDnsOutcome "127.0.0.1" { family := .ipv6, sockType := .stream }
          (.error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none, message := "x" }) = true := by
        simp only [allowedDnsOutcome, hv127, hMsgX, hMis127v6, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        decide
      have hAl : allowedStep DnsState.initial
          { host := "127.0.0.1", hints := { family := .ipv6, sockType := .stream } }
          (.error { kind := .otherGai, gaiCode := EAI_ADDRFAMILY, errno? := none, message := "x" }) =
          some DnsState.initial := by
        unfold allowedStep
        rw [hAo]
        simp only [Bool.not_true, hv127, DnsState.initial, Bool.or_self, Bool.false_eq_true,
          ↓reduceIte, hP127, mapAddrForHints]
        simp [EAI_ADDRFAMILY]
      rw [allowedStep_healthy_tight (HealthyEnv.initial 1 defaultOfflineOracle) _ _ DnsState.initial
        hAl rfl (fun hc => by cases hc) (by decide)]
      rfl
  · refine ⟨?_, ?_⟩
    · have hAo : allowedDnsOutcome "localhost" {}
          (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" }) = true := by
        simp only [allowedDnsOutcome, hvLocal, hMsgX, hMisLoc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        decide
      have hAl : allowedStep DnsState.initial { host := "localhost" }
          (.error { kind := .temporaryFailure, gaiCode := EAI_AGAIN, errno? := none, message := "x" }) =
          some DnsState.initial := by
        unfold allowedStep
        rw [hAo]
        simp [hvLocal, DnsState.initial, hPLoc, hHLoc]
      rw [allowedStep_healthy_tight (HealthyEnv.initial 1 defaultOfflineOracle) _ _ DnsState.initial
        hAl rfl (fun hc => by cases hc) (by decide)]
      rfl
    · have hAo : allowedDnsOutcome "localhost" {}
          (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EMFILE, message := "x" }) = true := by
        simp only [allowedDnsOutcome, hvLocal, hMsgX, hMisLoc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        decide
      have hAl : allowedStep DnsState.initial { host := "localhost" }
          (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EMFILE, message := "x" }) =
          some DnsState.initial := by
        unfold allowedStep
        rw [hAo]
        simp [hvLocal, DnsState.initial, hPLoc, hHLoc]
      rw [allowedStep_healthy_tight (HealthyEnv.initial 1 defaultOfflineOracle) _ _ DnsState.initial
        hAl rfl (by decide) (by decide)]
      rfl
  · refine ⟨by decide, by decide, by decide, by decide⟩
  · have hAo : allowedDnsOutcome "localhost" {}
        (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) = true := by
      simp only [allowedDnsOutcome, hvLocal, hMsgX, hMisLoc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      decide
    have hAl : allowedStep DnsState.initial { host := "localhost" }
        (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" }) =
        some DnsState.initial := by
      unfold allowedStep
      rw [hAo]
      simp [hvLocal, DnsState.initial, hPLoc, hHLoc]
    refine ⟨?_, ?_⟩
    · rw [allowedStep_healthy_tight (HealthyEnv.initial 1 defaultOfflineOracle) _ _ DnsState.initial
        hAl rfl (by decide) (by decide)]
      rfl
    · unfold healthyStep
      change (if !(HealthyEnv.initial 0 defaultOfflineOracle).wf ||
          isCriticalFault (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" })
        then none else _) = none
      have hG : (!(HealthyEnv.initial 0 defaultOfflineOracle).wf ||
          isCriticalFault (.error { kind := .systemError, gaiCode := EAI_SYSTEM, errno? := some Errno.EINTR, message := "x" })) = false := by
        decide
      rw [hG]
      dsimp only [Bool.false_eq_true, ↓reduceIte, HealthyEnv.initial]
      rw [hAl]
      decide
  · intro env hWf host hints
    have hStep := healthyModelOps_refinesHealthyDns env { host := host, hints := hints } hWf
    dsimp only [id, execDnsReq, StateT.run] at hStep ⊢
    have hRun : healthyModelOps.getaddrinfo host hints env =
        (healthyModelResolve env.state.oracle host hints, env) := rfl
    rw [hRun] at hStep ⊢
    dsimp only at hStep ⊢
    have hWf' := (healthyStep_implies_allowedStep env env { host := host, hints := hints } _ hStep).2.2.2.1
    refine ⟨⟨hStep, hWf', rfl⟩, ⟨?_, ?_⟩, ⟨rfl, ?_⟩, fun _ _ _ => ⟨rfl, trivial⟩⟩
    · intro ⟨hNonNum, hNoCrit, hNoEi⟩
      exact healthyModelResolve_eq_modelResolve_of_nonFault env.state.oracle host hints hNonNum hNoCrit hNoEi
    · intro baseAddr sc hHyb hFam
      exact healthyModelResolve_hybrid_scoped_eq env.state.oracle host hints baseAddr sc hHyb hFam
    · intro ⟨hPNone, hHNone⟩
      exact healthyModelResolve_eq_of_nonPureNonHybrid env.state.oracle host hints hPNone hHNone

/-- Reachability witness for `test_dns_healthyStep_and_healthyModelOps`. -/
theorem reach_dns_healthyStep_and_healthyModelOps :
    Core.CanReach test_dns_healthyStep_and_healthyModelOps := by
  have hAll := test_dns_healthyStep_and_healthyModelOps_ok
  have hRest := hAll.2.2.2.2.2.2.2.2.2 (HealthyEnv.initial 1 defaultOfflineOracle) rfl "localhost" {}
  refine ⟨hAll.1, hAll.2.1, hAll.2.2.1, hAll.2.2.2.1, hAll.2.2.2.2.1,
    hAll.2.2.2.2.2.1, hAll.2.2.2.2.2.2.1, hAll.2.2.2.2.2.2.2.1, hAll.2.2.2.2.2.2.2.2.1,
    HealthyEnv.initial 1 defaultOfflineOracle, rfl, "localhost", {},
    hRest.1, hRest.2.1, hRest.2.2.1,
    HealthyEnv.initial 1 defaultOfflineOracle, { host := "localhost" }, .ok [], ?_⟩
  exact hRest.2.2.2 (HealthyEnv.initial 1 defaultOfflineOracle) { host := "localhost" } (.ok [])


/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.LinuxSyscall.Dns` against `Model`. -/
theorem obeys_model :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkDnsOpsM Model.execPkgStep Model.allowedPkgStep :=
  mkDnsOpsM_obeysStepFrom

/-- Non-vacuity witness for `LeanSwe.LinuxSyscall.Dns` `obeys_model` (`HealthyEnv.wf`, `allowedRawStep`, and `allowedPkgStep` are simultaneously inhabited). -/
theorem obeys_model_nonvacuous :
    (∃ env₀ : HealthyEnv, HealthyEnv.wf env₀ = true) ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execRawStep Model.rawHealthyModelOps) Model.allowedRawStep ∧
    Core.ObeysStepId HealthyEnv.wf
      (Model.execPkgStep healthyModelOps) Model.allowedPkgStep :=
  ⟨⟨HealthyEnv.initial, rfl⟩,
   rawHealthyModelOps_obeysStep_of healthyModelOps_refinesHealthyDns,
   healthyModelOps_refinesHealthyDns⟩

end LeanSwe.LinuxSyscall.Dns.Proofs
