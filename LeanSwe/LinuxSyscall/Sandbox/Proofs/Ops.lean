import LeanSwe.LinuxSyscall.Sandbox.SpecTests

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass CanReach CanReachRun)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def unprivInitWithHostFds : SandboxSysState :=
  ((SandboxSysState.unprivileged.withHostFd 100 true).withHostFd 101 false).withPseudoFd 102

private theorem hasEmbeddedNul_mkRepBytes_97 :
    ∀ n, (List.replicate n (97 : UInt8)).any (· == (0 : UInt8)) = false
  | 0 => rfl
  | n + 1 => hasEmbeddedNul_mkRepBytes_97 n

private theorem mkRepBytes_size (n : Nat) : (mkRepBytes n).data.size = n := by
  unfold mkRepBytes
  rw [List.size_toArray, List.length_replicate]

private theorem mkRepBytes_noNul (n : Nat) : hasEmbeddedNul (mkRepBytes n) = false := by
  unfold hasEmbeddedNul mkRepBytes
  rw [List.toList_toArray]
  exact hasEmbeddedNul_mkRepBytes_97 n

/-- `modelOps.prctl` satisfies `test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig` from `SandboxSysState.unprivileged`. -/
theorem sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig_allPass :
    AllPass (test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig modelOps SandboxSysState.unprivileged) := by
  dsimp only [AllPass, test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig, NondetTest.assert,
    Bind.bind, Pure.pure]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies `test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf` on pre-populated `unprivInitWithHostFds`. -/
theorem sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf_allPass :
    AllPass (test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf modelOps unprivInitWithHostFds 100 101 102) := by
  dsimp only [AllPass, test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf, NondetTest.assert,
    Bind.bind, Pure.pure]
  have hs0 : unprivInitWithHostFds =
      ((SandboxSysState.unprivileged.withHostFd 100 true).withHostFd 101 false).withPseudoFd 102 := rfl
  rw [hs0]
  have hVer : (modelOps.landlockCreateRuleset none LANDLOCK_CREATE_RULESET_VERSION
      (((SandboxSysState.unprivileged.withHostFd 100 true).withHostFd 101 false).withPseudoFd 102)).1 =
      .ok (.version 9) := rfl
  have hAbi4 : 4 ≤ effectiveModelLandlockAbi
      (modelOps.landlockCreateRuleset none LANDLOCK_CREATE_RULESET_VERSION
        (((SandboxSysState.unprivileged.withHostFd 100 true).withHostFd 101 false).withPseudoFd 102)).2 := by
    decide
  repeat first
    | exact trivial
    | exact rfl
    | exact hVer
    | exact hAbi4
    | refine ⟨?_, ?_⟩

/-- `modelOps.seccomp` satisfies `test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation` from `SandboxSysState.unprivileged`. -/
theorem sandbox_ops_seccomp_actionAvailNnpAndBpfValidation_allPass :
    AllPass (test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation modelOps SandboxSysState.unprivileged) := by
  intro overFilter hOver
  have hOverB : decide (overFilter.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8) = false :=
    decide_eq_false (Nat.not_le_of_gt hOver)
  have hTooMany : StateT.run (modelOps.seccomp .setModeFilter {} overFilter) SandboxSysState.unprivileged =
      (.error Errno.EINVAL, SandboxSysState.unprivileged) := by
    dsimp only [modelOps, isValidSeccompFilterByteLen, StateT.run, Id.run, Pure.pure, Bind.bind,
      StateT.bind, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
    simp only [hOverB, Bool.and_false, Bool.not_false, Bool.true_or, ↓reduceIte]
    rfl
  dsimp only [AllPass, test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation, NondetTest.assert,
    Bind.bind, Pure.pure]
  rw [hTooMany]
  dsimp only [StateT.run, Id.run]
  repeat first | exact trivial | exact rfl | refine ⟨?_, ?_⟩

/-- Reachability witness for `test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation`. -/
theorem sandbox_ops_seccomp_actionAvailNnpAndBpfValidation_canReach :
    CanReach (test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation modelOps SandboxSysState.unprivileged) := by
  refine ⟨mkRepBytes (SECCOMP_MAX_FILTER_INSNS * 8 + 8), ?_, ?_⟩
  · rw [mkRepBytes_size]; decide
  · have hSz : decide ((mkRepBytes (SECCOMP_MAX_FILTER_INSNS * 8 + 8)).data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8) = false := by
      rw [mkRepBytes_size]; decide
    have hTooMany : StateT.run (modelOps.seccomp .setModeFilter {} (mkRepBytes (SECCOMP_MAX_FILTER_INSNS * 8 + 8)))
        SandboxSysState.unprivileged = (.error Errno.EINVAL, SandboxSysState.unprivileged) := by
      dsimp only [modelOps, isValidSeccompFilterByteLen, StateT.run, Id.run, Pure.pure, Bind.bind,
        StateT.bind, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
      simp only [hSz, Bool.and_false, Bool.not_false, Bool.true_or, ↓reduceIte]
      rfl
    dsimp only [CanReachRun, test_sandbox_ops_seccomp_actionAvailNnpAndBpfValidation, NondetTest.assert,
      Bind.bind, Pure.pure]
    rw [hTooMany]
    dsimp only [StateT.run, Id.run]
    repeat first | exact trivial | exact rfl | refine ⟨?_, ?_⟩

/-- `modelOps.setrlimit` satisfies `test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile` from `SandboxSysState.unprivileged`. -/
theorem sandbox_ops_setrlimit_curMaxMonotonicAndNofile_allPass :
    AllPass (test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile modelOps SandboxSysState.unprivileged) := by
  dsimp only [AllPass, test_sandbox_ops_setrlimit_curMaxMonotonicAndNofile, NondetTest.assert,
    Bind.bind, Pure.pure, StateT.run, Id.run]
  repeat first
    | exact trivial
    | exact rfl
    | refine ⟨0, rfl⟩
    | refine ⟨?_, ?_⟩
  · decide
  · dsimp only [modelOps, SandboxSysState.unprivileged, asciiBytes, hasEmbeddedNul,
      StateT.bind, StateT.pure, StateT.get, StateT.set, Pure.pure, Bind.bind,
      get, getThe, MonadStateOf.get, set]
    exact ⟨⟨rfl, ⟨0, rfl⟩⟩, trivial⟩

/-- `modelOps.memfdCreate` satisfies `test_sandbox_ops_memfdCreate_nameBoundsAndFlags` from `SandboxSysState.unprivileged`. -/
theorem sandbox_ops_memfdCreate_nameBoundsAndFlags_allPass :
    AllPass (test_sandbox_ops_memfdCreate_nameBoundsAndFlags modelOps SandboxSysState.unprivileged) := by
  intro badNul hNul overMax hOver
  have hOverB : decide (MFD_NAME_MAX < overMax.data.size) = true := decide_eq_true hOver
  have h249Nul : hasEmbeddedNul (mkRepBytes 249) = false := mkRepBytes_noNul 249
  have h249Sz : decide (MFD_NAME_MAX < (mkRepBytes 249).data.size) = false := by
    rw [mkRepBytes_size]; decide
  dsimp only [AllPass, test_sandbox_ops_memfdCreate_nameBoundsAndFlags, NondetTest.assert,
    Bind.bind, Pure.pure, modelOps, SandboxSysState.unprivileged, StateT.run, Id.run,
    StateT.bind, StateT.pure, get, getThe, MonadStateOf.get, set, StateT.get, StateT.set]
  simp only [hNul, Bool.true_or, hOverB, Bool.or_true, h249Nul, h249Sz, Bool.false_or, ↓reduceIte]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨by decide, by decide, by decide⟩, trivial⟩

/-- Reachability witness for `test_sandbox_ops_memfdCreate_nameBoundsAndFlags`. -/
theorem sandbox_ops_memfdCreate_nameBoundsAndFlags_canReach :
    CanReach (test_sandbox_ops_memfdCreate_nameBoundsAndFlags modelOps SandboxSysState.unprivileged) := by
  refine ⟨ByteArray.mk #[0], by decide, mkRepBytes 250, ?_, ?_⟩
  · rw [mkRepBytes_size]; decide
  · have h250Sz : decide (MFD_NAME_MAX < (mkRepBytes 250).data.size) = true := by
      rw [mkRepBytes_size]; decide
    have h249Nul : hasEmbeddedNul (mkRepBytes 249) = false := mkRepBytes_noNul 249
    have h249Sz : decide (MFD_NAME_MAX < (mkRepBytes 249).data.size) = false := by
      rw [mkRepBytes_size]; decide
    dsimp only [test_sandbox_ops_memfdCreate_nameBoundsAndFlags, CanReachRun, NondetTest.assert,
      Bind.bind, Pure.pure, modelOps, SandboxSysState.unprivileged, StateT.run, Id.run,
      StateT.bind, StateT.pure, get, getThe, MonadStateOf.get, set, StateT.get, StateT.set]
    simp only [h250Sz, Bool.or_true, h249Nul, h249Sz, Bool.false_or, ↓reduceIte]
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨by decide, by decide, by decide⟩, trivial⟩

end LeanSwe.LinuxSyscall.Sandbox
