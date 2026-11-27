import LeanSwe.LinuxSyscall.Dns.Proofs.OpsSoundnessProofs

namespace LeanSwe.LinuxSyscall.Dns.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

theorem normalizeOracleOutcome_soundAgainstAllowedOutcome (host : String)
    (hints : ResolveHints) (rawOut : Except DnsError (List DnsAddr)) :
    allowedDnsOutcome host hints (normalizeOracleOutcome host hints rawOut) = true := by
  unfold normalizeOracleOutcome
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    cases hlook : rawOut with
    | ok addrs =>
      dsimp only
      have hAllFiltered := filterMap_mapAddrForHints_all hints addrs
      generalize hKept :
          (if !(addrs.filterMap (mapAddrForHints hints)).isEmpty &&
              matchesSockTypeMultiplicity hints (addrs.filterMap (mapAddrForHints hints)) then
            addrs.filterMap (mapAddrForHints hints)
          else
            expandSockType hints (addrs.filterMap (mapAddrForHints hints))) = kept
      have hMult : matchesSockTypeMultiplicity hints kept = true := by
        rw [← hKept]
        split
        · rename_i hBr
          simp only [Bool.and_eq_true] at hBr
          exact hBr.2
        · exact expandSockType_matchesSockTypeMultiplicity hints _
      have hAllKept : kept.all (addrMatchesHints hints) = true := by
        rw [← hKept]
        split
        · exact hAllFiltered
        · exact expandSockType_all_matchesHints hints _ hAllFiltered
      cases hP : parsePureNumericAddr? host with
      | some rawAddr =>
        dsimp only
        cases hM : mapAddrForHints hints rawAddr with
        | none =>
          dsimp only
          exact allowedDnsOutcome_emptyPayloadError host hv hints
        | some expAddr =>
          dsimp only
          by_cases hEq : (kept == expandSockType hints [expAddr]) = true
          · simp only [hEq, ↓reduceIte]
            unfold allowedDnsOutcome
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, hP, hM, hEq, Bool.and_true]
            have hne : (expandSockType hints [expAddr]).isEmpty = false := by
              cases hsock : hints.sockType <;> simp [expandSockType, hsock]
            have hExpMatch : ([expAddr] : List DnsAddr).all (addrMatchesHints hints) = true := by
              simp [mapAddrForHints_matchesHints hints rawAddr expAddr hM]
            have hAll := expandSockType_all_matchesHints hints [expAddr] hExpMatch
            have hEq' : kept = expandSockType hints [expAddr] :=
              list_dnsAddr_eq_of_beq hEq
            have hne' : kept.isEmpty = false := by
              rw [hEq']; exact hne
            have hAll' : kept.all (addrMatchesHints hints) = true := by
              rw [hEq']; exact hAll
            simp [hne', hAll', hMult]
          · have hEqF : (kept == expandSockType hints [expAddr]) = false :=
              Bool.eq_false_iff.mpr hEq
            simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
            refine allowedDnsOutcome_of_error host hv hints _
              (by decide) (by decide) (by decide) (by simp [EAI_FAIL, EAI_ADDRFAMILY]) ?_ (by rfl) (by decide)
            split <;> decide
      | none =>
        dsimp only
        cases hHyb : parseHybridScopedNumericZone? host with
        | some hp =>
          rcases hp with ⟨baseAddr, sc⟩
          dsimp only
          by_cases hHybOk : (!kept.isEmpty && matchesHybridScopedAddrs hints baseAddr sc kept) = true
          · simp only [hHybOk, ↓reduceIte]
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hHybOk
            rcases hHybOk with ⟨hNemp, hMatch⟩
            unfold allowedDnsOutcome
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, hNemp, Bool.not_false, hAllKept, hMult,
              hP, hHyb, hMatch, Bool.and_self]
          · have hHybF : (!kept.isEmpty && matchesHybridScopedAddrs hints baseAddr sc kept) = false :=
              Bool.eq_false_iff.mpr hHybOk
            simp only [hHybF, Bool.false_eq_true, ↓reduceIte]
            exact allowedDnsOutcome_emptyPayloadError host hv hints
        | none =>
          dsimp only
          cases hZ : parseScopedNonNumericZone? host with
          | some p =>
            rcases p with ⟨baseAddr, zoneCs⟩
            dsimp only
            by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
                !kept.isEmpty &&
                matchesSymbolicScopedAddrs hints baseAddr kept) = true
            · simp only [hScOk, ↓reduceIte]
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hScOk
              rcases hScOk with ⟨⟨hCan, hNemp⟩, hMatch⟩
              unfold allowedDnsOutcome
              simp only [hnv, Bool.false_eq_true, ↓reduceIte, hNemp, Bool.not_false, hAllKept, hMult,
                hP, hHyb, hZ, hCan, hMatch, Bool.and_self]
            · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                  !kept.isEmpty &&
                  matchesSymbolicScopedAddrs hints baseAddr kept) = false :=
                Bool.eq_false_iff.mpr hScOk
              simp only [hScF, Bool.false_eq_true, ↓reduceIte]
              exact allowedDnsOutcome_emptyPayloadError host hv hints
          | none =>
            dsimp only
            by_cases hemp : kept.isEmpty = true
            · simp only [hemp, ↓reduceIte]
              exact allowedDnsOutcome_emptyPayloadError host hv hints
            · have hempF : kept.isEmpty = false := Bool.eq_false_iff.mpr hemp
              simp only [hempF, Bool.false_eq_true, ↓reduceIte]
              unfold allowedDnsOutcome
              simp only [hnv, Bool.false_eq_true, ↓reduceIte, hempF, Bool.not_false, hAllKept, hMult,
                hP, hHyb, hZ, Bool.and_self]
    | error err =>
      dsimp only
      let code' := normalizeGaiCodeForHost host hints err.gaiCode
      let errno?' : Option Errno := match err.errno? with
        | some eno => if code' == EAI_SYSTEM && eno != 0 && eno != Errno.EFAULT then some eno else none
        | none => none
      let msg' := if err.message.isEmpty then "getaddrinfo failed" else err.message
      rcases Internal.normalizeGaiCodeForHost_invariants host hints err.gaiCode with ⟨hValid, hAF, hMis⟩
      refine allowedDnsOutcome_of_error host hv hints
        { kind := classifyGaiKind code', gaiCode := code', errno? := errno?', message := msg' }
        ?_ hValid (Internal.dnsErrorKind_beq_refl _) hAF hMis ?_ ?_
      · have hkindNe := Internal.classifyGaiKind_ne_invalidHost code'
        cases hk : classifyGaiKind code' <;>
          first | exact absurd hk hkindNe | rfl
      · dsimp only [errno?']
        cases hErrEno : err.errno? with
        | none => rfl
        | some e =>
          dsimp only
          by_cases hSys : (code' == EAI_SYSTEM && e != 0 && e != Errno.EFAULT) = true
          · simp only [hSys, ↓reduceIte]
          · have hSysF : (code' == EAI_SYSTEM && e != 0 && e != Errno.EFAULT) = false :=
              Bool.eq_false_iff.mpr hSys
            simp only [hSysF, Bool.false_eq_true, ↓reduceIte]
      · by_cases hm : err.message = ""
        · simp [msg', hm, String.isEmpty]
        · simp [msg', String.isEmpty, hm]
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

private theorem modelResolve_soundAgainstAllowedOutcome (oracle : DnsOracle) (host : String)
    (hints : ResolveHints) :
    allowedDnsOutcome host hints (modelResolve oracle host hints) = true := by
  unfold modelResolve
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    exact normalizeOracleOutcome_soundAgainstAllowedOutcome host hints (oracle.lookup host hints)
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- Proof of `test_dns_modelOps_soundAgainstAllowedOutcome` for `modelOps`. -/
theorem test_dns_modelOps_soundAgainstAllowedOutcome_ok :
    Core.AllPass (test_dns_modelOps_soundAgainstAllowedOutcome modelOps) := by
  intro oracle host hints rawOut
  dsimp only [test_dns_modelOps_soundAgainstAllowedOutcome, Core.NondetTest.assert, Bind.bind,
    modelOps, Pure.pure, StateT.run, StateT.bind, StateT.pure,
    get, MonadStateOf.get, getThe, StateT.get]
  have hv127 : validateHost "127.0.0.1" = true := by rw [validateHost_eq]; decide
  have hvEmpty : validateHost "" = false := by rw [validateHost_eq]; decide
  have hvNul : validateHost "a\x00b" = false := by rw [validateHost_eq]; decide
  have hvLocal : validateHost "localhost" = true := by rw [validateHost_eq]; decide
  have hvZ1 : validateHost "::1%lo" = true := by rw [validateHost_eq]; decide
  have hvZ2 : validateHost "fe80::1%lo" = true := by rw [validateHost_eq]; decide
  have hvZ3 : validateHost "fe80::1%" = true := by rw [validateHost_eq]; decide
  have hvBad : validateHost "bad host" = true := by rw [validateHost_eq]; decide
  have hvA : validateHost "::ffff:127.0.0.1" = true := by rw [validateHost_eq]; decide
  have hvMZ : validateHost "::ffff:127.0.0.1%lo" = true := by rw [validateHost_eq]; decide
  refine ⟨modelResolve_soundAgainstAllowedOutcome oracle host hints,
    normalizeOracleOutcome_soundAgainstAllowedOutcome host hints rawOut, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  · simp [allowedDnsOutcome, hv127]
  · simp only [allowedDnsOutcome, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvLocal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvZ1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, classifyGaiKind, EAI_NONAME]
    intro _ _ _ hK; exact absurd hK (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, classifyGaiKind, EAI_NONAME, EAI_SYSTEM]
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, classifyGaiKind, EAI_SYSTEM, Errno.EFAULT]
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ _ hLe _; exact absurd hLe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ hGe _; exact absurd hGe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ hGe _; exact absurd hGe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode]
    intro _ hEq _; exact absurd hEq (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, EAI_BADFLAGS]
    intro _ _ hLe _; exact absurd hLe (by decide)
  · simp [allowedDnsOutcome, hv127, isValidGaiCode, EAI_SERVICE]
  · simp only [allowedDnsOutcome, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvZ3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [allowedDnsOutcome, hvBad, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; decide
  · simp only [modelResolve, defaultOfflineOracle, hvA, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvLocal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvLocal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · have hP127 : parsePureNumericAddr? "127.0.0.1" = some (.ipv4 127 0 0 1) := by rfl
    simp only [modelResolve, defaultOfflineOracle, hv127, hP127, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvZ1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvZ2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvZ3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hvMZ, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]; rfl
  · simp only [modelResolve, defaultOfflineOracle, hv127, Bool.not_true, Bool.false_eq_true, ↓reduceIte, normalizeOracleOutcome]
  · have hP127 : parsePureNumericAddr? "127.0.0.1" = some (.ipv4 127 0 0 1) := by rfl
    simp only [defaultOfflineOracle, hv127, hP127, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [defaultOfflineOracle, hvZ2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp [normalizeOracleOutcome, hvEmpty]
  · simp [normalizeOracleOutcome, hvNul]

/-- Proof of `test_dns_mkRawOps_soundAgainstAllowedOutcome` for `Internal.mkDnsOpsM` (`Id`). -/
theorem test_dns_mkRawOps_soundAgainstAllowedOutcome_ok :
    Core.AllPass (test_dns_mkRawOps_soundAgainstAllowedOutcome
      (fun raw => Internal.mkDnsOpsM (m := Id) { getaddrinfo := raw })) := by
  intro rawFn host hints expectedAddrs
  dsimp only [test_dns_mkRawOps_soundAgainstAllowedOutcome, Core.NondetTest.assert, Bind.bind]
  refine ⟨mkDnsOpsM_id_soundAgainstAllowedOutcome { getaddrinfo := rawFn } host hints, ?_, ?_, trivial⟩
  · rw [Bool.or_eq_true]
    cases hR : rawFn host hints.family.toWire hints.sockType.toWire with
    | error e =>
      left
      simp
    | ok bytes =>
      by_cases hv : validateHost host = true
      · by_cases hAllowed : allowedDnsOutcome host hints (.ok expectedAddrs) = true
        · by_cases hBytes : (bytes.data == (encodeWireRecords expectedAddrs).data) = true
          · right
            have hRaw : rawFn host hints.family.toWire hints.sockType.toWire =
                .ok (encodeWireRecords expectedAddrs) := by
              rw [hR, ByteArray.ext (eq_of_beq hBytes)]
            unfold allowedDnsOutcome at hAllowed
            have hnv : (!validateHost host) = false := by simp [hv]
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hAllowed
            rcases hAllowed with ⟨⟨⟨hNemp, hAll⟩, hMult⟩, hTrail⟩
            have hemp : expectedAddrs.isEmpty = false := by
              cases h1 : expectedAddrs.isEmpty <;> simp_all
            unfold Internal.mkDnsOpsM
            dsimp only [Bind.bind, Pure.pure]
            simp only [hnv, Bool.false_eq_true, ↓reduceIte, hRaw, Internal.decodeRecords_encodeRecords,
              hemp, hAll, Internal.matchesSockTypeMultiplicityImpl_eq, hMult, Bool.not_true, Bool.or_self, ↓reduceIte,
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
                simp only [hTrail, ↓reduceIte, list_dnsAddr_beq_refl]
            | none =>
              simp only [hP] at hTrail
              cases hHyb : parseHybridScopedNumericZone? host with
              | some hp =>
                rcases hp with ⟨baseAddr, sc⟩
                simp only [hHyb] at hTrail ⊢
                simp only [hTrail, ↓reduceIte, list_dnsAddr_beq_refl]
              | none =>
                simp only [hHyb] at hTrail
                cases hZ : parseScopedNonNumericZone? host with
                | none =>
                  simp only [list_dnsAddr_beq_refl]
                | some p =>
                  rcases p with ⟨baseAddr, zoneCs⟩
                  simp only [hZ, Bool.and_eq_true] at hTrail ⊢
                  simp only [hTrail.1, hTrail.2, and_self, ↓reduceIte, list_dnsAddr_beq_refl]
          · left; simp [hv, hAllowed, hBytes]
        · left; simp [hv, hAllowed]
      · left; simp [hv]
  · cases hv : validateHost host with
    | false => trivial
    | true =>
      cases hR : rawFn host hints.family.toWire hints.sockType.toWire with
      | ok _ => trivial
      | error p =>
        rcases p with ⟨rc, eno, msgBytes⟩
        dsimp only
        have hEq := Internal.mkDnsOpsM_id_error_eq host hv hints rc eno msgBytes
        unfold Internal.mkDnsOpsM at hEq ⊢
        dsimp only [Bind.bind, Pure.pure] at hEq ⊢
        rw [hR]
        exact hEq

theorem allowedStep_state_eq
    (s s' : DnsState) (req : DnsReq) (out : DnsOutcome)
    (h : allowedStep s req out = some s') :
    s' = s := by
  unfold allowedStep at h
  split at h
  · contradiction
  · split at h
    · injection h with hEq; exact hEq.symm
    · cases hP : parsePureNumericAddr? req.host with
      | none =>
        rw [hP] at h
        dsimp only at h
        cases hHyb : parseHybridScopedNumericZone? req.host with
        | none =>
          rw [hHyb] at h
          injection h with hEq; exact hEq.symm
        | some _ =>
          rw [hHyb] at h
          dsimp only at h
          split at h
          · cases out with
            | ok _ => injection h with hEq; exact hEq.symm
            | error _ => split at h <;> simp_all
          · cases out with
            | ok _ => contradiction
            | error _ => split at h <;> simp_all
      | some rawAddr =>
        rw [hP] at h
        dsimp only at h
        cases hM : mapAddrForHints req.hints rawAddr with
        | some _ =>
          rw [hM] at h
          dsimp only at h
          cases out with
          | ok _ => injection h with hEq; exact hEq.symm
          | error _ => split at h <;> simp_all
        | none =>
          rw [hM] at h
          dsimp only at h
          cases out with
          | ok _ => contradiction
          | error _ => split at h <;> simp_all

/-- Initial healthy `Dns` environments satisfy `HealthyEnv.wf`. -/
theorem healthyEnv_initial_wf (budget : Nat) (oracle : DnsOracle) :
    (HealthyEnv.initial budget oracle).wf = true :=
  rfl

/-- Tightness by construction: every `allowedStep` transition from a healthy `Dns` environment without curated critical faults (and with positive `eintrBudget` on `EINTR`) is accepted by `healthyStep`. -/
theorem allowedStep_healthy_tight
    (env : HealthyEnv) (req : DnsReq) (out : DnsOutcome) (s' : DnsState)
    (hStep : allowedStep env.state req out = some s')
    (hWf : env.wf = true)
    (hBudget : isEintrOutcome out = true → 0 < env.eintrBudget)
    (hNoCrit : isCriticalFault out = false) :
    healthyStep env req out =
      some { state := s',
             eintrBudget := if isEintrOutcome out then env.eintrBudget - 1 else env.eintrBudget } := by
  unfold healthyStep
  have hGuard : (!env.wf || isCriticalFault out) = false := by simp [hWf, hNoCrit]
  simp only [hGuard, Bool.false_eq_true, ↓reduceIte, hStep]
  cases hEi : isEintrOutcome out
  · simp
  · have hb : env.eintrBudget > 0 := hBudget hEi
    simp [hb]


theorem emptyPayloadError_not_critical_or_eintr (host : String) (hints : ResolveHints) :
    isCriticalFault (.error (emptyPayloadError host hints)) = false ∧
    isEintrOutcome (.error (emptyPayloadError host hints)) = false := by
  unfold emptyPayloadError
  split
  · exact ⟨by decide, by decide⟩
  · split
    · exact ⟨by decide, by decide⟩
    · split <;> exact ⟨by decide, by decide⟩

theorem addrMatchesHints_withIpv6Scope_of_allowsSymbolic
    (hints : ResolveHints) (baseAddr : DnsAddr) (sc : UInt32)
    (hFam : (hints.family != .ipv4) = true)
    (hAl : allowsSymbolicIpv6Zone baseAddr = true) :
    addrMatchesHints hints (withIpv6Scope sc baseAddr) = true := by
  cases baseAddr with
  | ipv4 => simp [allowsSymbolicIpv6Zone] at hAl
  | ipv6 =>
    cases hf : hints.family with
    | any => simp [addrMatchesHints, hf]
    | ipv4 => rw [hf] at hFam; exact absurd hFam (by decide)
    | ipv6 => simp [withIpv6Scope, addrMatchesHints, hf, DnsAddr.isIpv6]


end LeanSwe.LinuxSyscall.Dns.Proofs
