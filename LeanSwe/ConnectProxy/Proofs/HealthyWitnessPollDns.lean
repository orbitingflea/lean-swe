import LeanSwe.ConnectProxy.Proofs.HealthyWitnessNetOps

namespace LeanSwe.ConnectProxy.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal.SysBridge
open LeanSwe.ConnectProxy.Internal.HealthySys

/-- Internal ConnectProxy proof helper `fallbackPollErrno`. -/
def fallbackPollErrno (s : Poll.PollState) : Poll.PollReq → Errno
  | .eventfd2 _ _ => Errno.EMFILE
  | .ppoll entries timeout =>
    match Poll.preCheckPoll (.ppoll entries timeout) with
    | some preErr => preErr
    | none =>
      match Poll.evalPollList s entries.toList with
      | .error pinErr => pinErr
      | .ok _ => Errno.EMFILE

private theorem evalPollListAux_err_ebadf (s : Poll.PollState) :
    ∀ (xs : List (Poll.HandleId × Poll.PollEvents)) (acc : List Poll.PollEvents) (e : Errno),
      Poll.evalPollListAux s xs acc = .error e → e = Errno.EBADF
  | [], _, _, h => nomatch h
  | (hid, reqEv) :: rest, acc, e, h => by
    unfold Poll.evalPollListAux at h
    cases hGet : Poll.assocGet s.fds hid with
    | none =>
      rw [hGet] at h
      injection h with hEq
      exact hEq.symm
    | some desc =>
      rw [hGet] at h
      exact evalPollListAux_err_ebadf s rest (Poll.computeDescRevents desc reqEv :: acc) e h

private theorem preCheckPoll_ppoll_err (entries : Array (Poll.HandleId × Poll.PollEvents))
    (timeout : Option Poll.Timespec) (preErr : Errno)
    (hPre : Poll.preCheckPoll (.ppoll entries timeout) = some preErr) :
    preErr = Errno.EINVAL := by
  dsimp only [Poll.preCheckPoll] at hPre
  have hCond : ∀ b : Bool, (if b = true then some Errno.EINVAL else none) = some preErr → preErr = Errno.EINVAL := by
    intro b hb
    cases b
    · cases hb
    · injection hb with he; exact he.symm
  exact hCond _ hPre

/-- Internal ConnectProxy proof helper `fallbackPollErrno_healthy`. -/
theorem fallbackPollErrno_healthy (env : Poll.HealthyEnv) (req : Poll.PollReq)
    (hWf : env.wf = true) :
    Poll.healthyStep env req (.err (fallbackPollErrno env.state req)) = some env := by
  have hNotWf : (!env.wf) = false := by simp [hWf]
  cases req with
  | eventfd2 iv fl =>
    unfold fallbackPollErrno Poll.healthyStep Poll.isCriticalFault Poll.allowedStep Poll.stepPollCore Poll.isEintrOutcome
    rw [hNotWf]
    have h1 : Errno.isCriticalOsErrno Errno.EMFILE = false := by decide
    have h2 : (Errno.EMFILE.isTransientOsErrno || Errno.EMFILE == Errno.ENODEV) = true := by decide
    have h3 : (Errno.EMFILE == Errno.EINTR) = false := by decide
    simp [h1, h2, h3]
  | ppoll entries timeout =>
    unfold fallbackPollErrno
    dsimp only
    cases hPre : Poll.preCheckPoll (.ppoll entries timeout) with
    | some preErr =>
      have hEq : preErr = Errno.EINVAL := preCheckPoll_ppoll_err entries timeout preErr hPre
      subst hEq
      unfold Poll.healthyStep Poll.isCriticalFault Poll.allowedStep Poll.stepPollCore Poll.isEintrOutcome
      dsimp only
      rw [hNotWf, hPre]
      have h1 : Errno.isCriticalOsErrno Errno.EINVAL = false := by decide
      have h3 : (Errno.EINVAL == Errno.EINTR) = false := by decide
      simp [h1, h3]
    | none =>
      dsimp only
      cases hPin : Poll.evalPollList env.state entries.toList with
      | error pinErr =>
        have hEq : pinErr = Errno.EBADF := evalPollListAux_err_ebadf env.state entries.toList [] pinErr hPin
        subst hEq
        unfold Poll.healthyStep Poll.isCriticalFault Poll.allowedStep Poll.stepPollCore Poll.isEintrOutcome
        dsimp only
        rw [hNotWf, hPre, hPin]
        have h1 : Errno.isCriticalOsErrno Errno.EBADF = false := by decide
        have h3 : (Errno.EBADF == Errno.EINTR) = false := by decide
        simp [h1, h3]
      | ok revList =>
        dsimp only
        unfold Poll.healthyStep Poll.isCriticalFault Poll.allowedStep Poll.stepPollCore Poll.isEintrOutcome
        dsimp only
        rw [hNotWf, hPre, hPin]
        have h1 : Errno.isCriticalOsErrno Errno.EMFILE = false := by decide
        have h2 : Errno.EMFILE.isTransientOsErrno = true := by decide
        have h3 : (Errno.EMFILE == Errno.EINTR) = false := by decide
        simp [h1, h2, h3]

/-- Internal ConnectProxy proof helper `runSamplePollOp`. -/
def runSamplePollOp {α : Type}
    (req : Poll.PollReq)
    (pack : Except Errno α → Poll.PollOutcome)
    (unpack : Poll.PollOutcome → Option (Except Errno α)) :
    StateM HealthySysWorld (Except Errno α) := fun w =>
  let env := w.pollEnv
  let fbErr := fallbackPollErrno env.state req
  match Poll.stepPollCore env.state req none with
  | some (candOut, _) =>
    match unpack candOut with
    | some candRes =>
      match Poll.healthyStep env req (pack candRes) with
      | some env' =>
        if env'.wf then (candRes, { w with pollEnv := env' })
        else (.error fbErr, w)
      | none => (.error fbErr, w)
    | none => (.error fbErr, w)
  | none => (.error fbErr, w)

/-- Sample `PollOpsM` executing `Poll.stepPollCore` with verified healthy fallback. -/
def sampleHealthyPollOps : Poll.PollOpsM (StateM HealthySysWorld) Nat :=
  { ppoll := fun fds to? =>
      runSamplePollOp (.ppoll fds to?) Poll.outcomeOfPolled
        (fun | .polled rev => some (.ok rev) | .err e => some (.error e) | _ => none)
    eventfd2 := fun iv fl =>
      runSamplePollOp (.eventfd2 iv fl) Poll.outcomeOfOpened
        (fun | .opened h => some (.ok h) | .err e => some (.error e) | _ => none) }


private def dnsAddrFamilyErr : Dns.DnsError :=
  { kind := .otherGai
    gaiCode := Dns.EAI_ADDRFAMILY
    errno? := none
    message := "Address family for hostname not supported" }

private def dnsNoNameErr : Dns.DnsError :=
  { kind := .nameNotFound
    gaiCode := Dns.EAI_NONAME
    errno? := none
    message := "Name or service not known" }

/-- Internal ConnectProxy proof helper `fallbackDnsOutcome`. -/
def fallbackDnsOutcome (req : Dns.DnsReq) : Dns.DnsOutcome :=
  if !Dns.validateHost req.host then
    .error Dns.invalidHostError
  else
    match Dns.parsePureNumericAddr? req.host with
    | some rawAddr =>
      match Dns.mapAddrForHints req.hints rawAddr with
      | some expAddr => .ok (Dns.expandSockType req.hints [expAddr])
      | none => .error dnsAddrFamilyErr
    | none =>
      match Dns.parseHybridScopedNumericZone? req.host with
      | some (baseAddr, sc) =>
        if req.hints.family == .ipv4 then
          .error dnsAddrFamilyErr
        else
          .ok (Dns.expandSockType req.hints [Dns.withIpv6Scope sc baseAddr])
      | none =>
        if Dns.isNumericFamilyMismatch req.host req.hints then
          .error dnsAddrFamilyErr
        else
          .error dnsNoNameErr

private theorem dnsAddr_beq_refl (a : Dns.DnsAddr) : (a == a) = true := by
  cases a <;> simp [BEq.beq, Dns.instBEqDnsAddr.beq]

private theorem list_dnsAddr_beq_refl : ∀ (xs : List Dns.DnsAddr), (xs == xs) = true
  | [] => rfl
  | x :: rest => by
    change (x == x && (rest == rest)) = true
    rw [dnsAddr_beq_refl x, Bool.true_and]
    exact list_dnsAddr_beq_refl rest

private theorem dns_healthyStep_of_allowed {env : Dns.HealthyEnv} {req : Dns.DnsReq} {out : Dns.DnsOutcome}
    (hWf : env.wf = true)
    (hAl : Dns.allowedStep env.state req out = some env.state)
    (hNoC : Dns.isCriticalFault out = false)
    (hNoE : Dns.isEintrOutcome out = false) :
    Dns.healthyStep env req out = some env := by
  have hNotWf : (!env.wf) = false := by simp [hWf]
  unfold Dns.healthyStep
  rw [hNotWf, hNoC, Bool.false_or]
  simp only [Bool.false_eq_true, ↓reduceIte, hAl, hNoE]

private theorem mapAddrForHints_matchesHints (hints : Dns.ResolveHints) (raw exp : Dns.DnsAddr)
    (h : Dns.mapAddrForHints hints raw = some exp) :
    Dns.addrMatchesHints hints exp = true := by
  unfold Dns.mapAddrForHints at h
  cases hf : hints.family with
  | any => simp [Dns.addrMatchesHints, hf]
  | ipv4 =>
    rw [hf] at h; dsimp only at h
    split at h
    · injection h with hEq; subst hEq; simp [Dns.addrMatchesHints, hf, Dns.DnsAddr.isIpv4]
    · injection h with hEq; subst hEq; simp [Dns.addrMatchesHints, hf, Dns.DnsAddr.isIpv4]
    · cases h
  | ipv6 =>
    rw [hf] at h; dsimp only at h
    split at h
    · cases h
    · injection h with hEq; subst hEq; simp [Dns.addrMatchesHints, hf, Dns.DnsAddr.isIpv6]

private theorem expandSockType_single_props (hints : Dns.ResolveHints) (a : Dns.DnsAddr)
    (hMatch : Dns.addrMatchesHints hints a = true) :
    (!(Dns.expandSockType hints [a]).isEmpty) = true ∧
    (Dns.expandSockType hints [a]).all (Dns.addrMatchesHints hints) = true ∧
    Dns.matchesSockTypeMultiplicity hints (Dns.expandSockType hints [a]) = true := by
  cases hs : hints.sockType <;>
    simp [Dns.expandSockType, Dns.matchesSockTypeMultiplicity, Dns.checkSockTriples, hs, hMatch, dnsAddr_beq_refl]

private theorem allowsSymbolic_of_hybrid (host : String) (baseAddr : Dns.DnsAddr) (sc : UInt32)
    (h : Dns.parseHybridScopedNumericZone? host = some (baseAddr, sc)) :
    Dns.allowsSymbolicIpv6Zone baseAddr = true := by
  unfold Dns.parseHybridScopedNumericZone? at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · split at h
            · rename_i hAl; injection h with hp; cases hp; exact hAl
            · cases h
          · cases h
        · cases h
      · cases h

private theorem withIpv6Scope_matchesHints (hints : Dns.ResolveHints) (baseAddr : Dns.DnsAddr) (sc : UInt32)
    (hFam : (hints.family != .ipv4) = true)
    (hAl : Dns.allowsSymbolicIpv6Zone baseAddr = true) :
    Dns.addrMatchesHints hints (Dns.withIpv6Scope sc baseAddr) = true := by
  cases baseAddr with
  | ipv4 _ _ _ _ => cases hAl
  | ipv6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases hf : hints.family with
    | any => simp [Dns.addrMatchesHints, hf]
    | ipv4 => rw [hf] at hFam; cases hFam
    | ipv6 => simp [Dns.withIpv6Scope, Dns.addrMatchesHints, hf, Dns.DnsAddr.isIpv6]

private theorem dnsAddrFamilyErr_allowed (host : String) (hints : Dns.ResolveHints)
    (hnv : (!Dns.validateHost host) = false)
    (hMis : Dns.isNumericFamilyMismatch host hints = true) :
    Dns.allowedDnsOutcome host hints (.error dnsAddrFamilyErr) = true := by
  unfold Dns.allowedDnsOutcome
  rw [hnv]; simp only [Bool.false_eq_true, ↓reduceIte, hMis]
  decide

private theorem dnsNoNameErr_allowed (host : String) (hints : Dns.ResolveHints)
    (hnv : (!Dns.validateHost host) = false)
    (hMis : Dns.isNumericFamilyMismatch host hints = false) :
    Dns.allowedDnsOutcome host hints (.error dnsNoNameErr) = true := by
  unfold Dns.allowedDnsOutcome
  rw [hnv]; simp only [Bool.false_eq_true, ↓reduceIte, hMis]
  decide

/-- Internal ConnectProxy proof helper `fallbackDnsOutcome_healthy`. -/
theorem fallbackDnsOutcome_healthy (env : Dns.HealthyEnv) (req : Dns.DnsReq)
    (hWf : env.wf = true) :
    Dns.healthyStep env req (fallbackDnsOutcome req) = some env := by
  have hSecF : env.state.ambientSeccomp = false := by
    unfold Dns.HealthyEnv.wf at hWf
    cases hb : env.state.ambientSeccomp <;> simp_all
  unfold fallbackDnsOutcome
  by_cases hnv : (!Dns.validateHost req.host) = true
  · simp only [hnv, ↓reduceIte]
    have hAo : Dns.allowedDnsOutcome req.host req.hints (.error Dns.invalidHostError) = true := by
      unfold Dns.allowedDnsOutcome; simp only [hnv, ↓reduceIte]; decide
    apply dns_healthyStep_of_allowed hWf _ (by decide) (by decide)
    unfold Dns.allowedStep; simp [hAo, hnv]
  · have hnvF : (!Dns.validateHost req.host) = false := Bool.eq_false_iff.mpr hnv
    simp only [hnvF, Bool.false_eq_true, ↓reduceIte]
    cases hP : Dns.parsePureNumericAddr? req.host with
    | some rawAddr =>
      dsimp only
      cases hM : Dns.mapAddrForHints req.hints rawAddr with
      | some expAddr =>
        dsimp only
        obtain ⟨hNe, hAll, hMult⟩ := expandSockType_single_props req.hints expAddr
          (mapAddrForHints_matchesHints req.hints rawAddr expAddr hM)
        have hEqSelf := list_dnsAddr_beq_refl (Dns.expandSockType req.hints [expAddr])
        have hAo : Dns.allowedDnsOutcome req.host req.hints (.ok (Dns.expandSockType req.hints [expAddr])) = true := by
          unfold Dns.allowedDnsOutcome
          simp [hnvF, hNe, hAll, hMult, hP, hM, hEqSelf]
        apply dns_healthyStep_of_allowed hWf _ rfl rfl
        unfold Dns.allowedStep; simp [hAo, hnvF, hSecF, hP, hM]
      | none =>
        dsimp only
        have hMis : Dns.isNumericFamilyMismatch req.host req.hints = true := by
          unfold Dns.isNumericFamilyMismatch; simp [hP, hM]
        have hAo := dnsAddrFamilyErr_allowed req.host req.hints hnvF hMis
        apply dns_healthyStep_of_allowed hWf _ (by decide) (by decide)
        unfold Dns.allowedStep
        simp only [hAo, Bool.not_true, hnvF, hSecF, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hP, hM]
        rfl
    | none =>
      dsimp only
      cases hHyb : Dns.parseHybridScopedNumericZone? req.host with
      | some pair =>
        rcases pair with ⟨baseAddr, sc⟩
        dsimp only
        by_cases hFam4 : (req.hints.family == .ipv4) = true
        · simp only [hFam4, ↓reduceIte]
          have hFamNe : (req.hints.family != .ipv4) = false := by
            revert hFam4; cases req.hints.family <;> decide
          have hMis : Dns.isNumericFamilyMismatch req.host req.hints = true := by
            unfold Dns.isNumericFamilyMismatch; simp [hP, hHyb, hFam4]
          have hAo := dnsAddrFamilyErr_allowed req.host req.hints hnvF hMis
          apply dns_healthyStep_of_allowed hWf _ (by decide) (by decide)
          unfold Dns.allowedStep
          simp only [hAo, Bool.not_true, hnvF, hSecF, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hP, hHyb, hFamNe]
          rfl
        · have hFam4F : (req.hints.family == .ipv4) = false := Bool.eq_false_iff.mpr hFam4
          have hFamNe : (req.hints.family != .ipv4) = true := by
            revert hFam4F; cases req.hints.family <;> decide
          simp only [hFam4F, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨hNe, hAll, hMult⟩ := expandSockType_single_props req.hints (Dns.withIpv6Scope sc baseAddr)
            (withIpv6Scope_matchesHints req.hints baseAddr sc hFamNe (allowsSymbolic_of_hybrid req.host baseAddr sc hHyb))
          have hEqSelf := list_dnsAddr_beq_refl (Dns.expandSockType req.hints [Dns.withIpv6Scope sc baseAddr])
          have hHybMatch : Dns.matchesHybridScopedAddrs req.hints baseAddr sc
              (Dns.expandSockType req.hints [Dns.withIpv6Scope sc baseAddr]) = true := by
            unfold Dns.matchesHybridScopedAddrs
            simp [hFamNe, hEqSelf]
          have hAo : Dns.allowedDnsOutcome req.host req.hints
              (.ok (Dns.expandSockType req.hints [Dns.withIpv6Scope sc baseAddr])) = true := by
            unfold Dns.allowedDnsOutcome
            simp [hnvF, hNe, hAll, hMult, hP, hHyb, hHybMatch]
          apply dns_healthyStep_of_allowed hWf _ rfl rfl
          unfold Dns.allowedStep; simp [hAo, hnvF, hSecF, hP, hHyb, hFamNe]
      | none =>
        dsimp only
        by_cases hMis : Dns.isNumericFamilyMismatch req.host req.hints = true
        · simp only [hMis, ↓reduceIte]
          have hAo := dnsAddrFamilyErr_allowed req.host req.hints hnvF hMis
          apply dns_healthyStep_of_allowed hWf _ (by decide) (by decide)
          unfold Dns.allowedStep; simp [hAo, hnvF, hSecF, hP, hHyb]
        · have hMisF : Dns.isNumericFamilyMismatch req.host req.hints = false := Bool.eq_false_iff.mpr hMis
          simp only [hMisF, Bool.false_eq_true, ↓reduceIte]
          have hAo := dnsNoNameErr_allowed req.host req.hints hnvF hMisF
          apply dns_healthyStep_of_allowed hWf _ (by decide) (by decide)
          unfold Dns.allowedStep; simp [hAo, hnvF, hSecF, hP, hHyb]

/-- Internal ConnectProxy proof helper `runSampleDnsOp`. -/
def runSampleDnsOp (host : String) (hints : Dns.ResolveHints) :
    StateM HealthySysWorld Dns.DnsOutcome := fun w =>
  let env := w.dnsEnv
  let req : Dns.DnsReq := { host := host, hints := hints }
  let candOut := ((Dns.healthyModelOps.getaddrinfo host hints).run env).1
  match Dns.healthyStep env req candOut with
  | some env' =>
    if env'.wf then (candOut, { w with dnsEnv := env' })
    else (fallbackDnsOutcome req, w)
  | none => (fallbackDnsOutcome req, w)

/-- Sample `DnsOpsM` executing `Dns.healthyModelOps` with verified healthy fallback. -/
def sampleHealthyDnsOps : Dns.DnsOpsM (StateM HealthySysWorld) :=
  { getaddrinfo := runSampleDnsOp }

end LeanSwe.ConnectProxy.Proofs
