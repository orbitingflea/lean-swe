import LeanSweProofs.LinuxSyscall.Dns.Proofs.CodecAndGaiHelpers

namespace LeanSwe.LinuxSyscall.Dns.Proofs

open Core
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Dns

private theorem decode_post_sound (host : String) (hv : validateHost host = true)
    (hints : ResolveHints) (recBytes : ByteArray) :
    allowedDnsOutcome host hints
      (match Internal.decodeRecords recBytes with
      | .error e => .error e
      | .ok addrs =>
        if addrs.isEmpty || !addrs.all (addrMatchesHints hints) then
          .error (emptyPayloadError host hints)
        else if !matchesSockTypeMultiplicity hints addrs then
          .error { kind := .nameNotFound
                   gaiCode := EAI_FAIL
                   errno? := none
                   message := "Socket-type multiplicity mismatch" }
        else
          match parsePureNumericAddr? host with
          | some rawAddr =>
            match mapAddrForHints hints rawAddr with
            | none => .error (emptyPayloadError host hints)
            | some expAddr =>
              if addrs == expandSockType hints [expAddr] then
                .ok addrs
              else
                .error { kind := .nameNotFound
                         gaiCode := EAI_FAIL
                         errno? := none
                         message := "Numeric literal resolution mismatch" }
          | none =>
            match parseHybridScopedNumericZone? host with
            | some (baseAddr, sc) =>
              if matchesHybridScopedAddrs hints baseAddr sc addrs then
                .ok addrs
              else
                .error (emptyPayloadError host hints)
            | none =>
              match parseScopedNonNumericZone? host with
              | some (baseAddr, zoneCs) =>
                if canSymbolicScopedOk hints baseAddr zoneCs &&
                    matchesSymbolicScopedAddrs hints baseAddr addrs then
                  .ok addrs
                else
                  .error (emptyPayloadError host hints)
              | none => .ok addrs) = true := by
  cases hDec : Internal.decodeRecords recBytes with
  | error err =>
    have hinv := Internal.decodeRecords_error_invariants recBytes err hDec
    rcases hinv with ⟨hk, hcode, heno, hmsg⟩
    have hmsg' : (!err.message.isEmpty) = true := by simpa using hmsg
    refine allowedDnsOutcome_of_error host hv hints err ?_ ?_ ?_ ?_ ?_ ?_ hmsg'
    · rw [hk]; decide
    · rw [hcode]; decide
    · rw [hk, hcode]; decide
    · rw [hcode]; simp [EAI_OVERFLOW, EAI_ADDRFAMILY]
    · rw [hcode]
      split <;> decide
    · rw [heno]
  | ok addrs =>
    dsimp only
    by_cases hBad : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = true
    · simp only [hBad, ↓reduceIte]
      exact allowedDnsOutcome_emptyPayloadError host hv hints
    · have hBadF : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = false :=
        Bool.eq_false_iff.mpr hBad
      have hempF : addrs.isEmpty = false := by
        cases h1 : addrs.isEmpty <;> simp_all
      have hall : addrs.all (addrMatchesHints hints) = true := by
        cases h2 : addrs.all (addrMatchesHints hints) <;> simp_all
      simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
      by_cases hMultF : (!matchesSockTypeMultiplicity hints addrs) = true
      · simp only [hMultF, ↓reduceIte]
        refine allowedDnsOutcome_of_error host hv hints _
          (by decide) (by decide) (by decide) (by simp [EAI_FAIL, EAI_ADDRFAMILY]) ?_ (by rfl) (by decide)
        split <;> decide
      · have hMultNeg : (!matchesSockTypeMultiplicity hints addrs) = false :=
          Bool.eq_false_iff.mpr hMultF
        have hMult : matchesSockTypeMultiplicity hints addrs = true := by
          cases h3 : matchesSockTypeMultiplicity hints addrs <;> simp_all
        simp only [hMultNeg, Bool.false_eq_true, ↓reduceIte]
        cases hParse : parsePureNumericAddr? host with
        | some rawAddr =>
          dsimp only
          cases hMap : mapAddrForHints hints rawAddr with
          | none =>
            dsimp only
            exact allowedDnsOutcome_emptyPayloadError host hv hints
          | some expAddr =>
            dsimp only
            by_cases hEq : (addrs == expandSockType hints [expAddr]) = true
            · simp only [hEq, ↓reduceIte]
              unfold allowedDnsOutcome
              have hnv : (!validateHost host) = false := by simp [hv]
              simp [hnv, hempF, hall, hMult, hParse, hMap, hEq]
            · have hEqF : (addrs == expandSockType hints [expAddr]) = false :=
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
            by_cases hHybOk : matchesHybridScopedAddrs hints baseAddr sc addrs = true
            · simp only [hHybOk, ↓reduceIte]
              unfold allowedDnsOutcome
              have hnv : (!validateHost host) = false := by simp [hv]
              simp [hnv, hempF, hall, hMult, hParse, hHyb, hHybOk]
            · have hHybF : matchesHybridScopedAddrs hints baseAddr sc addrs = false :=
                Bool.eq_false_iff.mpr hHybOk
              simp only [hHybF, Bool.false_eq_true, ↓reduceIte]
              exact allowedDnsOutcome_emptyPayloadError host hv hints
          | none =>
            dsimp only
            cases hScoped : parseScopedNonNumericZone? host with
            | none =>
              unfold allowedDnsOutcome
              have hnv : (!validateHost host) = false := by simp [hv]
              simp [hnv, hempF, hall, hMult, hParse, hHyb, hScoped]
            | some p =>
              rcases p with ⟨baseAddr, zoneCs⟩
              dsimp only
              by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
                  matchesSymbolicScopedAddrs hints baseAddr addrs) = true
              · simp only [hScOk, ↓reduceIte]
                unfold allowedDnsOutcome
                have hnv : (!validateHost host) = false := by simp [hv]
                simp [hnv, hempF, hall, hMult, hParse, hHyb, hScoped, hScOk]
              · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                    matchesSymbolicScopedAddrs hints baseAddr addrs) = false :=
                  Bool.eq_false_iff.mpr hScOk
                simp only [hScF, Bool.false_eq_true, ↓reduceIte]
                exact allowedDnsOutcome_emptyPayloadError host hv hints

private theorem baseio_bind_eq {α β : Type} (x : BaseIO α) (f : α → BaseIO β) (w : Void IO.RealWorld) :
    (x >>= f) w = f (x w).1 (x w).2 :=
  rfl

theorem validateHost_eq (h : String) :
    validateHost h = (!h.toList.isEmpty && !h.toList.any (· == '\x00')) := by
  unfold validateHost
  have hEmpty : h.isEmpty = h.toList.isEmpty := by
    cases hl : h.toList with
    | nil =>
      have : h = "" := String.ext (by simp [hl])
      subst this; decide
    | cons _ _ =>
      have hne : h ≠ "" := by intro he; subst he; simp at hl
      simp [hne]
  simp [String.any, hEmpty]

private theorem eio_ofBaseIO_eq {α : Type} (x : BaseIO α) (w : Void IO.RealWorld) :
    (liftM x : IO α) w = EST.Out.ok (x w).1 (x w).2 :=
  rfl

private theorem io_bind_ok {α β : Type} (x : IO α) (f : α → IO β) (w w' : Void IO.RealWorld) (a : α)
    (hx : x w = EST.Out.ok a w') :
    (x >>= f) w = f a w' := by
  change EST.bind x f w = f a w'
  simp [EST.bind, hx]

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (Pure.pure (f := IO) a) w = EST.Out.ok a w :=
  rfl

private theorem io_pure_match {α : Type} (P : α → Bool) (a : α) (w : Void IO.RealWorld) (h : P a = true) :
    (match (Pure.pure (f := IO) a) w with | .ok res _ => P res = true | .error _ _ => False) := by
  rw [io_pure_eq]
  exact h

/-- `Internal.mkDnsOps` is definitionally `Internal.mkDnsOpsM` specialized to `IO`. -/
theorem mkDnsOps_eq_mkDnsOpsM (raw : Internal.PosixDnsOps) :
    Internal.mkDnsOps raw = Internal.mkDnsOpsM raw :=
  rfl

/-- `defaultOps.getaddrinfo` is definitionally `fun host hints => liftM (defaultOpsBase.getaddrinfo host hints)`. -/
theorem defaultOps_eq_liftM_defaultOpsBase :
    ∀ host hints, defaultOps.getaddrinfo host hints = liftM (defaultOpsBase.getaddrinfo host hints) :=
  fun _ _ => rfl

/-- `Dns.getaddrinfo` forwards `(host, hints)` directly to `defaultOps.getaddrinfo`. -/
theorem getaddrinfo_eq_defaultOps (host : String) (hints : ResolveHints) :
    Dns.getaddrinfo host hints = defaultOps.getaddrinfo host hints :=
  rfl

/-- Single-argument `Dns.getaddrinfo host` uses `{ family := .any, sockType := .stream }` (`{}`). -/
theorem getaddrinfo_default_hints_eq (host : String) :
    Dns.getaddrinfo host = defaultOps.getaddrinfo host { family := .any, sockType := .stream } :=
  rfl

/-- Pure `Id` soundness bridge for `Internal.mkDnsOpsM`. -/
theorem mkDnsOpsM_id_soundAgainstAllowedOutcome
    (raw : Internal.PosixDnsOpsM Id) (host : String) (hints : ResolveHints) :
    allowedDnsOutcome host hints ((Internal.mkDnsOpsM raw).getaddrinfo host hints) = true := by
  unfold Internal.mkDnsOpsM
  dsimp only [Bind.bind, Pure.pure]
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    cases hRaw : raw.getaddrinfo host hints.family.toWire hints.sockType.toWire with
    | ok recBytes =>
      simp only [Internal.emptyPayloadErrorImpl_eq, Internal.matchesSockTypeMultiplicityImpl_eq,
        Internal.parsePureNumericAddrImpl_eq, Internal.mapAddrForHintsImpl_eq,
        Internal.expandSockTypeImpl_eq, Internal.parseHybridScopedNumericZoneImpl_eq,
        Internal.matchesHybridScopedAddrsImpl_eq, Internal.parseScopedNonNumericZoneImpl_eq,
        Internal.canSymbolicScopedOkImpl_eq, Internal.matchesSymbolicScopedAddrsImpl_eq]
      exact decode_post_sound host hv hints recBytes
    | error p =>
      rcases p with ⟨rc, eno, msgBytes⟩
      have hId := Internal.mkDnsOpsM_id_error_sound host hints rc eno msgBytes
      simp only [Internal.mkDnsOpsM, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Pure.pure] at hId
      exact hId
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- Soundness bridge: every `BaseIO` call through `Internal.mkDnsOpsM raw` satisfies `Model.allowedDnsOutcome`. -/
theorem mkDnsOpsM_soundAgainstAllowedOutcome
    (raw : Internal.PosixDnsOpsM BaseIO) (host : String) (hints : ResolveHints)
    (w : Void IO.RealWorld) :
    allowedDnsOutcome host hints ((Internal.mkDnsOpsM raw).getaddrinfo host hints w).1 = true := by
  unfold Internal.mkDnsOpsM
  dsimp only
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    rw [baseio_bind_eq]
    cases hRaw : (raw.getaddrinfo host hints.family.toWire hints.sockType.toWire w).1 with
    | ok recBytes =>
      have hPost := decode_post_sound host hv hints recBytes
      dsimp only
      cases hDec : Internal.decodeRecords recBytes with
      | error err =>
        rw [baseio_pure_fst]
        simpa [hDec] using hPost
      | ok addrs =>
        dsimp only
        simp only [Internal.emptyPayloadErrorImpl_eq, Internal.matchesSockTypeMultiplicityImpl_eq,
          Internal.parsePureNumericAddrImpl_eq, Internal.mapAddrForHintsImpl_eq,
          Internal.expandSockTypeImpl_eq, Internal.parseHybridScopedNumericZoneImpl_eq,
          Internal.matchesHybridScopedAddrsImpl_eq, Internal.parseScopedNonNumericZoneImpl_eq,
          Internal.canSymbolicScopedOkImpl_eq, Internal.matchesSymbolicScopedAddrsImpl_eq]
        simp only [hDec] at hPost
        by_cases hBad : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = true
        · simp only [hBad, ↓reduceIte] at hPost ⊢
          rw [baseio_pure_fst]; exact hPost
        · have hBadF : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = false :=
            Bool.eq_false_iff.mpr hBad
          simp only [hBadF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
          by_cases hMultF : (!matchesSockTypeMultiplicity hints addrs) = true
          · simp only [hMultF, ↓reduceIte] at hPost ⊢
            rw [baseio_pure_fst]; exact hPost
          · have hMultNeg : (!matchesSockTypeMultiplicity hints addrs) = false :=
              Bool.eq_false_iff.mpr hMultF
            simp only [hMultNeg, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
            cases hP : parsePureNumericAddr? host with
            | some rawAddr =>
              cases hM : mapAddrForHints hints rawAddr with
              | none =>
                simp only [hP, hM] at hPost ⊢
                rw [baseio_pure_fst]; exact hPost
              | some expAddr =>
                simp only [hP, hM] at hPost ⊢
                by_cases hEq : (addrs == expandSockType hints [expAddr]) = true
                · simp only [hEq, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
                · have hEqF : (addrs == expandSockType hints [expAddr]) = false :=
                    Bool.eq_false_iff.mpr hEq
                  simp only [hEqF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
            | none =>
              cases hHyb : parseHybridScopedNumericZone? host with
              | some hp =>
                rcases hp with ⟨baseAddr, sc⟩
                simp only [hP, hHyb] at hPost ⊢
                by_cases hHybOk : matchesHybridScopedAddrs hints baseAddr sc addrs = true
                · simp only [hHybOk, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
                · have hHybF : matchesHybridScopedAddrs hints baseAddr sc addrs = false :=
                    Bool.eq_false_iff.mpr hHybOk
                  simp only [hHybF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
              | none =>
                cases hZ : parseScopedNonNumericZone? host with
                | none =>
                  simp only [hP, hHyb, hZ] at hPost ⊢
                  rw [baseio_pure_fst]; exact hPost
                | some p =>
                  rcases p with ⟨baseAddr, zoneCs⟩
                  simp only [hP, hHyb, hZ] at hPost ⊢
                  by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
                      matchesSymbolicScopedAddrs hints baseAddr addrs) = true
                  · simp only [hScOk, ↓reduceIte] at hPost ⊢
                    rw [baseio_pure_fst]; exact hPost
                  · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                        matchesSymbolicScopedAddrs hints baseAddr addrs) = false :=
                      Bool.eq_false_iff.mpr hScOk
                    simp only [hScF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                    rw [baseio_pure_fst]; exact hPost
    | error p =>
      rcases p with ⟨rc, eno, msgBytes⟩
      rw [baseio_pure_fst]
      have hId := Internal.mkDnsOpsM_id_error_sound host hints rc eno msgBytes
      simp only [Internal.mkDnsOpsM, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Pure.pure] at hId
      exact hId
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    rw [baseio_pure_fst]
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- Soundness bridge in `BaseIO` for `LeanSwe.LinuxSyscall.Dns.defaultOpsBase`. -/
theorem defaultOpsBase_soundAgainstAllowedOutcome
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    allowedDnsOutcome host hints (defaultOpsBase.getaddrinfo host hints w).1 = true :=
  mkDnsOpsM_soundAgainstAllowedOutcome _ host hints w

/-- Soundness bridge in `IO`: whenever `raw.getaddrinfo` returns without throwing an `IO.Error`, `(Internal.mkDnsOps raw).getaddrinfo host hints` returns `.ok res` satisfying `allowedDnsOutcome host hints res`. -/
theorem mkDnsOps_soundAgainstAllowedOutcome
    (raw : Internal.PosixDnsOps)
    (hNoThrow : ∀ h f s (w0 : Void IO.RealWorld),
      ∃ r w1, raw.getaddrinfo h f s w0 = EST.Out.ok r w1)
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    match (Internal.mkDnsOps raw).getaddrinfo host hints w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False := by
  unfold Internal.mkDnsOps Internal.mkDnsOpsM
  dsimp only
  by_cases hv : validateHost host = true
  · have hnv : (!validateHost host) = false := by simp [hv]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    rcases hNoThrow host hints.family.toWire hints.sockType.toWire w with
      ⟨rawOut, w1, hRaw⟩
    rw [io_bind_ok _ _ w w1 rawOut hRaw]
    cases rawOut with
    | error p =>
      rcases p with ⟨rc, eno, msgBytes⟩
      have hId := Internal.mkDnsOpsM_id_error_sound host hints rc eno msgBytes
      simp only [Internal.mkDnsOpsM, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Bind.bind, Pure.pure] at hId
      exact io_pure_match (allowedDnsOutcome host hints) _ w1 hId
    | ok recBytes =>
      have hPost := decode_post_sound host hv hints recBytes
      dsimp only
      cases hDec : Internal.decodeRecords recBytes with
      | error err =>
        simp only [hDec] at hPost
        exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
      | ok addrs =>
        dsimp only
        simp only [Internal.emptyPayloadErrorImpl_eq, Internal.matchesSockTypeMultiplicityImpl_eq,
          Internal.parsePureNumericAddrImpl_eq, Internal.mapAddrForHintsImpl_eq,
          Internal.expandSockTypeImpl_eq, Internal.parseHybridScopedNumericZoneImpl_eq,
          Internal.matchesHybridScopedAddrsImpl_eq, Internal.parseScopedNonNumericZoneImpl_eq,
          Internal.canSymbolicScopedOkImpl_eq, Internal.matchesSymbolicScopedAddrsImpl_eq]
        simp only [hDec] at hPost
        by_cases hBad : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = true
        · simp only [hBad, ↓reduceIte] at hPost ⊢
          exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
        · have hBadF : (addrs.isEmpty || !addrs.all (addrMatchesHints hints)) = false :=
            Bool.eq_false_iff.mpr hBad
          simp only [hBadF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
          by_cases hMultF : (!matchesSockTypeMultiplicity hints addrs) = true
          · simp only [hMultF, ↓reduceIte] at hPost ⊢
            exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
          · have hMultNeg : (!matchesSockTypeMultiplicity hints addrs) = false :=
              Bool.eq_false_iff.mpr hMultF
            simp only [hMultNeg, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
            cases hP : parsePureNumericAddr? host with
            | some rawAddr =>
              cases hM : mapAddrForHints hints rawAddr with
              | none =>
                simp only [hP, hM] at hPost ⊢
                exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
              | some expAddr =>
                simp only [hP, hM] at hPost ⊢
                by_cases hEq : (addrs == expandSockType hints [expAddr]) = true
                · simp only [hEq, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
                · have hEqF : (addrs == expandSockType hints [expAddr]) = false :=
                    Bool.eq_false_iff.mpr hEq
                  simp only [hEqF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
            | none =>
              cases hHyb : parseHybridScopedNumericZone? host with
              | some hp =>
                rcases hp with ⟨baseAddr, sc⟩
                simp only [hP, hHyb] at hPost ⊢
                by_cases hHybOk : matchesHybridScopedAddrs hints baseAddr sc addrs = true
                · simp only [hHybOk, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
                · have hHybF : matchesHybridScopedAddrs hints baseAddr sc addrs = false :=
                    Bool.eq_false_iff.mpr hHybOk
                  simp only [hHybF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
              | none =>
                cases hZ : parseScopedNonNumericZone? host with
                | none =>
                  simp only [hP, hHyb, hZ] at hPost ⊢
                  exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
                | some p =>
                  rcases p with ⟨baseAddr, zoneCs⟩
                  simp only [hP, hHyb, hZ] at hPost ⊢
                  by_cases hScOk : (canSymbolicScopedOk hints baseAddr zoneCs &&
                      matchesSymbolicScopedAddrs hints baseAddr addrs) = true
                  · simp only [hScOk, ↓reduceIte] at hPost ⊢
                    exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
                  · have hScF : (canSymbolicScopedOk hints baseAddr zoneCs &&
                        matchesSymbolicScopedAddrs hints baseAddr addrs) = false :=
                      Bool.eq_false_iff.mpr hScOk
                    simp only [hScF, Bool.false_eq_true, ↓reduceIte] at hPost ⊢
                    exact io_pure_match (allowedDnsOutcome host hints) _ w1 hPost
  · have hnv : (!validateHost host) = true := by simp [hv]
    simp only [hnv, ↓reduceIte]
    refine io_pure_match (allowedDnsOutcome host hints) _ w ?_
    unfold allowedDnsOutcome
    simp only [hnv, ↓reduceIte]
    decide

/-- End-to-end `IO` soundness bridge for `LeanSwe.LinuxSyscall.Dns.defaultOps` (`Interface.lean`): never throws `IO.Error` and always returns an `allowedDnsOutcome`. -/
theorem defaultOps_soundAgainstAllowedOutcome
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    match defaultOps.getaddrinfo host hints w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False := by
  change match (liftM (defaultOpsBase.getaddrinfo host hints) : IO _) w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False
  rw [eio_ofBaseIO_eq]
  exact defaultOpsBase_soundAgainstAllowedOutcome host hints w

/-- End-to-end `IO` soundness bridge for public `LeanSwe.LinuxSyscall.Dns.getaddrinfo` (`Interface.lean`). -/
theorem getaddrinfo_soundAgainstAllowedOutcome
    (host : String) (hints : ResolveHints) (w : Void IO.RealWorld) :
    match Dns.getaddrinfo host hints w with
    | .ok res _ => allowedDnsOutcome host hints res = true
    | .error _ _ => False :=
  defaultOps_soundAgainstAllowedOutcome host hints w

/-- In `BaseIO`, `(Internal.mkDnsOpsM raw).getaddrinfo host hints` never emits `.invalidHost` once `validateHost host = true`. -/
theorem mkDnsOps_never_invalidHost_of_valid
    (raw : Internal.PosixDnsOpsM BaseIO) (host : String) (hints : ResolveHints)
    (hv : validateHost host = true) (w : Void IO.RealWorld) :
    Core.NeverErrorKindBaseIO DnsError.kind .invalidHost
      ((Internal.mkDnsOpsM raw).getaddrinfo host hints) w := by
  have hs := mkDnsOpsM_soundAgainstAllowedOutcome raw host hints w
  unfold Core.NeverErrorKindBaseIO
  unfold allowedDnsOutcome at hs
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
  cases hRes : (Internal.mkDnsOpsM raw).getaddrinfo host hints w with
  | mk val st =>
    cases hVal : val with
    | ok _ => trivial
    | error err =>
      have hFst : ((Internal.mkDnsOpsM raw).getaddrinfo host hints w).1 = .error err := by
        rw [hRes, hVal]
      rw [hFst] at hs
      simp only [Bool.and_eq_true] at hs
      have hne : (err.kind != .invalidHost) = true := hs.1.1.1.1.1.1
      dsimp only
      intro he
      rw [he] at hne
      revert hne
      decide

/-- When a `BaseIO` raw hook returns non-empty hint-matching encoded `addrs` on a valid host (matching any numeric/zoned literal and sockType multiplicity), `(Internal.mkDnsOpsM raw).getaddrinfo host hints` can never fail with any `DnsErrorKind`. -/
theorem mkDnsOps_never_error_when_encoded
    (raw : Internal.PosixDnsOpsM BaseIO) (host : String) (hints : ResolveHints) (addrs : List DnsAddr)
    (hv : validateHost host = true)
    (hne : addrs.isEmpty = false)
    (hm : addrs.all (addrMatchesHints hints) = true)
    (hMult : matchesSockTypeMultiplicity hints addrs = true)
    (hNum : ∀ rawAddr, parsePureNumericAddr? host = some rawAddr →
      ∃ expAddr, mapAddrForHints hints rawAddr = some expAddr ∧ addrs = expandSockType hints [expAddr])
    (hHybrid : ∀ baseAddr sc, parseHybridScopedNumericZone? host = some (baseAddr, sc) →
      matchesHybridScopedAddrs hints baseAddr sc addrs = true)
    (hScoped : ∀ baseAddr zoneCs, parseScopedNonNumericZone? host = some (baseAddr, zoneCs) →
      canSymbolicScopedOk hints baseAddr zoneCs = true ∧
      matchesSymbolicScopedAddrs hints baseAddr addrs = true)
    (hRawOk : ∀ w0 : Void IO.RealWorld,
      (raw.getaddrinfo host hints.family.toWire hints.sockType.toWire w0).1 =
        Except.ok (Internal.encodeRecords addrs))
    (kind : DnsErrorKind) (w : Void IO.RealWorld) :
    Core.NeverErrorKindBaseIO DnsError.kind kind
      ((Internal.mkDnsOpsM raw).getaddrinfo host hints) w := by
  unfold Core.NeverErrorKindBaseIO Internal.mkDnsOpsM
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [baseio_bind_eq, hRawOk w]
  dsimp only
  simp only [decodeRecords_encodeRecords, hne, hm, Internal.matchesSockTypeMultiplicityImpl_eq, hMult,
    Bool.false_eq_true, Bool.not_true, Bool.or_self, ↓reduceIte,
    Internal.parsePureNumericAddrImpl_eq, Internal.mapAddrForHintsImpl_eq,
    Internal.expandSockTypeImpl_eq, Internal.parseHybridScopedNumericZoneImpl_eq,
    Internal.matchesHybridScopedAddrsImpl_eq, Internal.parseScopedNonNumericZoneImpl_eq,
    Internal.canSymbolicScopedOkImpl_eq, Internal.matchesSymbolicScopedAddrsImpl_eq]
  cases hP : parsePureNumericAddr? host with
  | some rawAddr =>
    rcases hNum rawAddr hP with ⟨expAddr, hMap, hEq⟩
    dsimp only
    simp only [hMap, hEq, list_dnsAddr_beq_refl, ↓reduceIte]
    exact trivial
  | none =>
    cases hHyb : parseHybridScopedNumericZone? host with
    | some hp =>
      rcases hp with ⟨baseAddr, sc⟩
      have hHybOk := hHybrid baseAddr sc hHyb
      dsimp only
      simp only [hHybOk, ↓reduceIte]
      exact trivial
    | none =>
      cases hZ : parseScopedNonNumericZone? host with
      | none =>
        dsimp only
        trivial
      | some p =>
        rcases p with ⟨baseAddr, zoneCs⟩
        rcases hScoped baseAddr zoneCs hZ with ⟨hCan, hMatch⟩
        dsimp only
        simp only [hCan, hMatch, Bool.and_self, ↓reduceIte]
        exact trivial

/-- Proof of `test_dns_validateHost_semantics` for `validateHost`. -/
theorem test_dns_validateHost_semantics_ok :
    Core.AllPass (test_dns_validateHost_semantics validateHost) := by
  intro h
  simp only [Core.NondetTest.assert, Bind.bind, validateHost_eq]
  exact ⟨by decide, by decide, by decide, by decide, by decide, trivial, trivial⟩

/-- Proof of `test_dns_addrHelpers_semantics` for `DnsAddr.format` and `DnsAddr.isLoopback`. -/
theorem test_dns_addrHelpers_semantics_ok :
    Core.AllPass (test_dns_addrHelpers_semantics DnsAddr.format DnsAddr.isLoopback) := by
  dsimp [test_dns_addrHelpers_semantics]
  simp only [Core.NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Proof of `test_dns_classifyGaiKind_semantics` for `classifyGaiKind`. -/
theorem test_dns_classifyGaiKind_semantics_ok :
    Core.AllPass (test_dns_classifyGaiKind_semantics classifyGaiKind) := by
  intro rc
  simp only [Core.NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  have hne := Internal.classifyGaiKind_ne_invalidHost rc
  cases hk : classifyGaiKind rc <;>
    first | exact absurd hk hne | decide

/-- Proof of `test_dns_wireTags_semantics` for `AddrFamilyHint.toWire` and `SockTypeHint.toWire`. -/
theorem test_dns_wireTags_semantics_ok :
    Core.AllPass (test_dns_wireTags_semantics AddrFamilyHint.toWire SockTypeHint.toWire) := by
  intro f1 f2 s1 s2
  dsimp only [test_dns_wireTags_semantics, Core.NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, trivial⟩
  · cases f1 <;> cases f2 <;> decide
  · cases s1 <;> cases s2 <;> decide


end LeanSwe.LinuxSyscall.Dns.Proofs
