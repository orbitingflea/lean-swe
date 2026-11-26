import LeanSwe.LinuxSyscall.Sandbox.SpecTests

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def landlockInitWithHostFds : SandboxSysState :=
  ((SandboxSysState.unprivileged.withHostFd 100 true).withHostFd 101 false).withPseudoFd 102

private def stubUnitOps : SandboxOpsM (StateM Unit) HandleId :=
  { landlockCreateRuleset := fun attr? _ =>
      match attr? with
      | none => pure (.ok (.version 9))
      | some _ => pure (.ok (.ruleset 0))
    landlockAddRule := fun _ _ => pure (.ok ())
    landlockRestrictSelf := fun _ => pure (.ok ())
    seccomp := fun _ _ _ => pure (.ok 0)
    prctl := fun _ => pure (.ok 0)
    setrlimit := fun _ _ _ => pure (.ok ())
    memfdCreate := fun _ _ => pure (.ok 1) }

private theorem mkRepBytes_size (n : Nat) : (mkRepBytes n).data.size = n := by
  unfold mkRepBytes
  rw [List.size_toArray, List.length_replicate]

private theorem hasEmbeddedNulLoop_mkRepBytes (n : Nat) :
    ∀ k i : Nat, hasEmbeddedNulLoop (mkRepBytes n) i k = false
  | 0, _ => rfl
  | k + 1, i => by
    unfold hasEmbeddedNulLoop
    split
    · have hElem : (mkRepBytes n)[i] = (97 : UInt8) := by
        show (mkRepBytes n).data[i] = (97 : UInt8)
        unfold mkRepBytes
        exact List.getElem_replicate ..
      rw [hElem]
      exact hasEmbeddedNulLoop_mkRepBytes n k (i + 1)
    · rfl

/-- `mkRepBytes n` contains no embedded NUL byte for every `n`. -/
theorem mkRepBytes_noNul (n : Nat) : hasEmbeddedNul (mkRepBytes n) = false :=
  hasEmbeddedNulLoop_mkRepBytes n (mkRepBytes n).size 0

example : ¬ Core.AllPass (test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.1.1

example : ¬ Core.AllPass (test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig
    { stubUnitOps with
      prctl := fun
        | .setPdeathsig sig =>
          if sig > MAX_LINUX_SIGNAL then pure (.error Errno.EINVAL) else pure (.ok 0)
        | _ => pure (.ok 0)
      landlockRestrictSelf := fun _ => pure (.error Errno.EPERM)
      seccomp := fun _ _ _ => pure (.error Errno.EACCES) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  have hGet1 : (Except.ok (0 : UInt32) : Except Errno UInt32) = Except.ok 1 :=
    h.2.2.2.2.2.2.1.2.1
  injection hGet1 with hEq
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf
    stubUnitOps () 100 101 102) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.2.1.1

example : ¬ Core.AllPass (test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf
    { modelOps with
      landlockCreateRuleset := fun attr? flags =>
        match attr?, flags with
        | some { handledAccessFs := 0, handledAccessNet := 0 }, 0 =>
          pure (.error Errno.EINVAL)
        | _, _ => modelOps.landlockCreateRuleset attr? flags }
    landlockInitWithHostFds 100 101 102) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf,
    Bind.bind, assert, pure] at h
  have hEm : (Except.error Errno.EINVAL : Except Errno (LandlockCreateResult HandleId)) =
      Except.error Errno.ENOMSG := h.2.2.2.1.1
  injection hEm with hCode
  exact absurd hCode (by decide)

example : ¬ Core.AllPass (test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf
    { stubUnitOps with
      landlockCreateRuleset := fun attr? flags =>
        match attr?, flags with
        | none, 1 => pure (.ok (.version 9))
        | none, _ => pure (.error Errno.EINVAL)
        | some { handledAccessFs := 0, handledAccessNet := 0 }, 0 => pure (.error Errno.ENOMSG)
        | some a, 0 =>
          if (a.handledAccessFs &&& ~~~LANDLOCK_ACCESS_FS_V4_ALL) != 0 ||
             (a.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0 then
            pure (.error Errno.EINVAL)
          else
            pure (.ok (.ruleset 0))
        | some _, _ => pure (.error Errno.EINVAL)
      landlockAddRule := fun rs rule =>
        if rs == 999 then pure (.error Errno.EBADF)
        else if rs == 1 || rs == 102 then pure (.error Errno.EBADFD)
        else
          match rule with
          | .pathBeneath p acc =>
            if acc == 0 then pure (.error Errno.ENOMSG)
            else if (acc &&& LANDLOCK_ACCESS_FS_WRITE_FILE) != 0 then pure (.error Errno.EINVAL)
            else if p == 999 then pure (.error Errno.EBADF)
            else if p == 1 || p == 102 || p == 0 then pure (.error Errno.EBADFD)
            else if p == 101 && (acc &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0 then pure (.error Errno.EINVAL)
            else pure (.ok ())
          | .netPort port acc =>
            if acc == 0 then pure (.error Errno.ENOMSG)
            else if acc == LANDLOCK_ACCESS_NET_BIND_TCP || port > 65535 then pure (.error Errno.EINVAL)
            else pure (.ok ())
      landlockRestrictSelf := fun rs =>
        if rs == 999 then pure (.error Errno.EBADF)
        else if rs == 1 || rs == 102 then pure (.error Errno.EBADFD)
        else pure (.ok ()) } () 100 101 102) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  have hBefore : (Except.error Errno.EBADF : Except Errno Unit) = Except.error Errno.EPERM :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  injection hBefore with hCode
  exact absurd hCode (by decide)

private theorem exists_overFilter :
    ∃ p : ByteArray, p.data.size > SECCOMP_MAX_FILTER_INSNS * 8 :=
  ⟨mkRepBytes 1288, by rw [mkRepBytes_size]; decide⟩

private theorem exists_exact250 :
    ∃ p : ByteArray, p.data.size > MFD_NAME_MAX ∧ hasEmbeddedNul p = false ∧ p.data.size = 250 :=
  ⟨mkRepBytes 250, by rw [mkRepBytes_size]; decide, mkRepBytes_noNul 250, mkRepBytes_size 250⟩

example : ¬ Core.AllPass (test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation
    stubUnitOps ()) := by
  intro h
  rcases exists_overFilter with ⟨pBig, hpBig⟩
  have h0 := h pBig hpBig
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.2.1.1

example : ¬ Core.AllPass (test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation
    { stubUnitOps with
      seccomp := fun op flags bytes =>
        match op with
        | .getActionAvail a =>
          if flags.toBits != 0 then pure (.error Errno.EINVAL)
          else if isKnownSeccompAction a then pure (.ok 0)
          else pure (.error Errno.EOPNOTSUPP)
        | .setModeFilter =>
          if !isValidSeccompFilterByteLen bytes.data.size then pure (.error Errno.EINVAL)
          else pure (.error Errno.EPERM) } ()) := by
  intro h
  rcases exists_overFilter with ⟨pBig, hpBig⟩
  have h0 := h pBig hpBig
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  have hNoNnp : (Except.error Errno.EPERM : Except Errno UInt32) = Except.error Errno.EACCES :=
    h0.2.2.1.2.2.2
  injection hNoNnp with hCode
  exact absurd hCode (by decide)

example : ¬ Core.AllPass (test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile
    stubUnitOps ()) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  cases h.1.1

example : ¬ Core.AllPass (test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile
    { stubUnitOps with
      setrlimit := fun _ cur max =>
        if max > 1024 then pure (.error Errno.EPERM)
        else if cur > max then pure (.error Errno.EINVAL)
        else pure (.ok ()) } ()) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile,
    stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h
  have hPrec : (Except.error Errno.EPERM : Except Errno Unit) = Except.error Errno.EINVAL :=
    h.2.1.2.2.2.2.1
  injection hPrec with hCode
  exact absurd hCode (by decide)

example : ¬ Core.AllPass (test_sandbox_ops_memfdCreate_nameBoundsAndFlags
    stubUnitOps ()) := by
  intro h
  rcases exists_exact250 with ⟨p250, hpOver, _, _⟩
  have h0 := h (ByteArray.mk #[97, 0, 98]) (by decide) p250 hpOver
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_sandbox_ops_memfdCreate_nameBoundsAndFlags
    { stubUnitOps with
      memfdCreate := fun name flags =>
        if hasEmbeddedNul name || name.data.size > 250 then pure (.error Errno.EINVAL)
        else if flags.noexecSeal && flags.exec then pure (.error Errno.EINVAL)
        else pure (.ok name.data.size) } ()) := by
  intro h
  rcases exists_exact250 with ⟨p250, hpOver, hpNoNul, hpSz⟩
  have h0 := h (ByteArray.mk #[97, 0, 98]) (by decide) p250 hpOver
  dsimp only [stubUnitOps, Bind.bind, assert, StateT.run, pure, StateT.pure] at h0
  have hFail := h0.2.1.1
  rw [hpNoNul, hpSz] at hFail
  cases hFail

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_relationalInvariants
    (fun s req out =>
      match out with
      | .err e => if e == Errno.EFAULT then some s else allowedStep s req out
      | _ => allowedStep s req out)) := by
  intro h
  exact absurd h.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_relationalInvariants
    (fun s req out =>
      match allowedStepCore s req out with
      | some s' => some s'
      | none => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_relationalInvariants,
    Bind.bind, assert, pure] at h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 (by decide)

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_relationalInvariants
    (fun s req out =>
      if s.seccompMayIntercept then
        match out with
        | .err e =>
          if e != Errno.EFAULT && 1 ≤ e.toNat && e.toNat ≤ 4095 then some s else none
        | _ => allowedStepCore s req out
      else
        allowedStepCore s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_relationalInvariants,
    Bind.bind, assert, pure] at h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_relationalInvariants
    (fun s req out =>
      match req, out with
      | .memfdCreate _ { noexecSeal := false, exec := false, .. }, .err e =>
        if e == Errno.EACCES then some { s with memfdNoexecStrict? := some true }
        else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_relationalInvariants,
    Bind.bind, assert, pure] at h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_relationalInvariants
    (fun s req out =>
      match req, out with
      | .landlockCreateRuleset none 1, .landlockVersion v =>
        if v.toNat < 4 then none else some { s with landlockAbi? := some v }
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_relationalInvariants,
    Bind.bind, assert, pure] at h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_environmentFreeAndOPath
    (fun s req out =>
      match req, out with
      | .prctl .getNoNewPrivs, .u32 1 =>
        if s.noNewPrivs? == some true then some s else none
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_environmentFreeAndOPath,
    Bind.bind, assert, pure] at h
  exact h.1

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_environmentFreeAndOPath
    (fun s req out =>
      match req, out with
      | .landlockRestrictSelf _, .unit =>
        if s.noNewPrivs? != some true then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_environmentFreeAndOPath,
    Bind.bind, assert, pure] at h
  exact h.2.2.2.1

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_environmentFreeAndOPath
    (fun s req out =>
      match req, out with
      | .landlockRestrictSelf _, .err e =>
        if e == Errno.E2BIG && s.landlockLayers < LANDLOCK_MAX_STACKED_LAYERS then none
        else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_environmentFreeAndOPath,
    Bind.bind, assert, pure] at h
  exact h.2.2.2.2.2.2.2.1

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_environmentFreeAndOPath
    (fun s req out =>
      match req, out with
      | .setrlimit res _ max, .unit =>
        if max > (s.getRlimit res).hardUpper then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_environmentFreeAndOPath,
    Bind.bind, assert, pure] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_environmentFreeAndOPath
    (fun s req out =>
      match req, out with
      | .landlockAddRule rs _, .err e =>
        if rs == 50 && e == Errno.EBADFD then none else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_environmentFreeAndOPath,
    Bind.bind, assert, pure] at h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_model_allowedStep_environmentFreeAndOPath
    (fun s req out =>
      match req, out with
      | .landlockAddRule rs _, .err e =>
        if rs == 53 then
          if e == Errno.EBADFD then some s else none
        else allowedStep s req out
      | _, _ => allowedStep s req out)) := by
  intro h
  dsimp only [Core.AllPass, test_sandbox_model_allowedStep_environmentFreeAndOPath,
    Bind.bind, assert, pure] at h
  exact absurd h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_model_modelOpsRefinesAllowedStep
    { modelOps with
      landlockCreateRuleset := fun attr? flags => do
        let s ← get
        match attr? with
        | some a =>
          if flags == 0 && s.defaultLandlockAbi < 4 then return .ok (.ruleset s.nextHid)
          else modelOps.landlockCreateRuleset (some a) flags
        | none => modelOps.landlockCreateRuleset none flags }
    allowedStep) := by
  intro h
  have h0 := h.2 { SandboxSysState.initial with defaultLandlockAbi := 0 } rfl
    (.landlockCreateRuleset (some { handledAccessFs := 0, handledAccessNet := 0 }) 0)
  dsimp only [execSandboxReq, Bind.bind, assert, StateT.run, StateT.bind, StateT.get,
    StateT.pure, pure, get, getThe, MonadState.get, MonadStateOf.get] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_healthyStep_and_healthyModelOps
    (isCrit := fun e => Errno.isCriticalOsErrno e || e == Errno.EMFILE)) := by
  intro h
  have h0 := h Errno.EMFILE
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      match req, out with
      | .setrlimit _ _ _, .err e =>
        if e == Errno.EMFILE then some env else healthyStep env req out
      | _, _ => healthyStep env req out)) := by
  intro h
  have h0 := h Errno.EINTR
  exact absurd h0.2.2.2.2.2.2.2.1.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_healthyStep_and_healthyModelOps
    (ops := { healthyModelOps with memfdCreate := fun _ _ => pure (.error Errno.EMFILE) })) := by
  intro h
  have h0 := h Errno.EINTR
  cases h0.2.2.2.2.2.2.2.2.2.1.2.2.2

example : ¬ Core.AllPass (test_sandbox_healthyStep_and_healthyModelOps
    (ops := { healthyModelOps with
      landlockCreateRuleset := fun attr? flags env =>
        match attr? with
        | none => healthyModelOps.landlockCreateRuleset none flags env
        | some _ => (.error Errno.ENOSPC, env) })) := by
  intro h
  have h0 := (h Errno.EINTR).2.2.2.2.2.2.2.2.2.2 (HealthyEnv.initial 1) rfl
    (.landlockCreateRuleset (some { handledAccessFs := LANDLOCK_ACCESS_FS_EXECUTE }) 0)
  have hEq := congrArg Prod.fst h0.1.1
  exact absurd hEq (by decide)

example : ¬ Core.AllPass (test_sandbox_healthyStep_and_healthyModelOps
    (step := fun env req out =>
      if decide (env.eintrBudget ≥ 2) && isEintrOutcome out then
        (healthyStep env req out).map (fun env' => { env' with eintrBudget := env.eintrBudget })
      else
        healthyStep env req out)) := by
  intro h
  have hRest := (h Errno.EINTR).2.2.2.2.2.2.2.2.2.2 (HealthyEnv.initial 1) rfl (.prctl .setNoNewPrivs)
  have hStep := (hRest.2 (HealthyEnv.initial 2) (.prctl .setNoNewPrivs) (.err Errno.EINTR)).1
  exact absurd (congrArg (Option.map HealthyEnv.eintrBudget) hStep) (by decide)

end LeanSwe.LinuxSyscall.Sandbox
