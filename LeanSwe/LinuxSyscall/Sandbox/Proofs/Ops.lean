import LeanSwe.LinuxSyscall.Sandbox.SpecTests

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass CanReach CanReachRun)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private theorem hasEmbeddedNul_mkRepBytes_97 :
    ∀ n, (List.replicate n (97 : UInt8)).any (· == (0 : UInt8)) = false
  | 0 => rfl
  | n + 1 => hasEmbeddedNul_mkRepBytes_97 n

private theorem mkRepBytes_size (n : Nat) : (mkRepBytes n).data.size = n := by
  unfold mkRepBytes
  rw [List.size_toArray, List.length_replicate]

private theorem mkRepBytes_noNul (n : Nat) : hasEmbeddedNul (mkRepBytes n) = false := by
  rw [hasEmbeddedNul_eq_toList_any]
  unfold mkRepBytes
  rw [List.toList_toArray]
  exact hasEmbeddedNul_mkRepBytes_97 n

/-- `modelOps.prctl` satisfies `test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig` from `SandboxSysState.unprivileged`. -/
theorem sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig_allPass :
    AllPass (test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig modelOps SandboxSysState.unprivileged) := by
  dsimp only [AllPass, test_sandbox_ops_prctl_noNewPrivsSubreaperAndPdeathsig, NondetTest.assert,
    Bind.bind, Pure.pure]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩

/-- `modelOps` satisfies `test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf` on `SandboxSysState.unprivileged` pre-populated with host directory FD `100`, regular FD `101`, and pseudo-FS FD `102`. -/
theorem sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf_allPass :
    AllPass (test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf modelOps
      (((SandboxSysState.unprivileged.withHostFd 100 true).withHostFd 101 false).withPseudoFd 102) 100 101 102) := by
  dsimp only [AllPass, test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf, NondetTest.assert,
    Bind.bind, Pure.pure]
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

private def memfdEmptyRes : Except Errno HandleId × SandboxSysState :=
  (modelOps.memfdCreate ByteArray.empty { cloexec := true, allowSealing := true }).run SandboxSysState.unprivileged

private def memfdS1 : SandboxSysState := memfdEmptyRes.2

private def memfdS2 : SandboxSysState :=
  { memfdS1 with
    fds := assocSet memfdS1.fds memfdS1.nextHid { kind := .memfd false true, cloexec := true }
    nextHid := Nat.max memfdS1.nextHid (memfdS1.nextHid + 1)
    memfdEnabled := true }

private theorem memfdCreate_einval_eq (name : ByteArray)
    (hBad : (hasEmbeddedNul name || decide (MFD_NAME_MAX < name.data.size)) = true) :
    (modelOps.memfdCreate name {}).run SandboxSysState.unprivileged =
      (.error Errno.EINVAL, SandboxSysState.unprivileged) := by
  dsimp only [modelOps, StateT.run, Id.run, StateT.bind, StateT.pure,
    Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, StateT.get]
  rw [hBad]
  rfl

private theorem memfdCreate_valid_eq (name : ByteArray) (flags : MemfdFlags) (s : SandboxSysState)
    (hNul : hasEmbeddedNul name = false)
    (hSz : decide (MFD_NAME_MAX < name.data.size) = false)
    (hExec : flags.exec = false)
    (hCur : s.rlimitNofile.curExact = false) :
    (modelOps.memfdCreate name flags).run s =
      (.ok s.nextHid,
        { s with
          fds := assocSet s.fds s.nextHid
            { kind := .memfd flags.allowSealing flags.noexecSeal, cloexec := flags.cloexec }
          nextHid := Nat.max s.nextHid (s.nextHid + 1)
          memfdEnabled := true
          memfdNoexecStrict? := s.memfdNoexecStrict? }) := by
  dsimp only [modelOps, StateT.run, Id.run, StateT.bind, StateT.pure,
    Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set, StateT.get, StateT.set]
  simp only [hNul, hSz, hExec, hCur, Bool.false_or, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem memfdCreate_249_eq :
    (modelOps.memfdCreate (mkRepBytes 249) { cloexec := true, noexecSeal := true }).run memfdS1 =
      (.ok memfdS1.nextHid, memfdS2) := by
  have hSz : decide (MFD_NAME_MAX < (mkRepBytes 249).data.size) = false := by
    rw [mkRepBytes_size]; decide
  exact memfdCreate_valid_eq (mkRepBytes 249) { cloexec := true, noexecSeal := true } memfdS1
    (mkRepBytes_noNul 249) hSz rfl rfl

private theorem memfdCreate_rest_eq :
    ((modelOps.memfdCreate (asciiBytes ['a']) { noexecSeal := true, exec := true }).run SandboxSysState.unprivileged).1 =
        .error Errno.EINVAL ∧
    (modelOps.memfdCreate ByteArray.empty { cloexec := true, allowSealing := true }).run SandboxSysState.unprivileged =
        (.ok 0, memfdS1) ∧
    ((modelOps.memfdCreate (asciiBytes ['e']) { cloexec := false, exec := true }).run memfdS2).1 =
        .ok 2 :=
  ⟨rfl, rfl, rfl⟩

private theorem memfdCreate_conf_eq :
    (modelOps.memfdCreate (asciiBytes ['a']) { noexecSeal := true, exec := true }).run
      SandboxSysState.unprivileged =
      (.error Errno.EINVAL,
        ((modelOps.memfdCreate (asciiBytes ['a']) { noexecSeal := true, exec := true }).run
          SandboxSysState.unprivileged).2) :=
  rfl

private theorem memfdCreate_exec_eq :
    (modelOps.memfdCreate (asciiBytes ['e']) { cloexec := false, exec := true }).run memfdS2 =
      (.ok 2,
        ((modelOps.memfdCreate (asciiBytes ['e']) { cloexec := false, exec := true }).run
          memfdS2).2) :=
  rfl

/-- `modelOps.memfdCreate` satisfies `test_sandbox_ops_memfdCreate_nameBoundsAndFlags` from `SandboxSysState.unprivileged`. -/
theorem sandbox_ops_memfdCreate_nameBoundsAndFlags_allPass :
    AllPass (test_sandbox_ops_memfdCreate_nameBoundsAndFlags modelOps SandboxSysState.unprivileged) := by
  intro badNul hNul overMax hOver
  have hNulEq := memfdCreate_einval_eq badNul (by rw [hNul, Bool.true_or])
  have hOverEq := memfdCreate_einval_eq overMax (by rw [decide_eq_true hOver, Bool.or_true])
  dsimp only [AllPass, test_sandbox_ops_memfdCreate_nameBoundsAndFlags]
  rw [hNulEq, hOverEq]
  dsimp only [Id.run]
  rw [memfdCreate_conf_eq]
  dsimp only [Id.run]
  rw [memfdCreate_rest_eq.2.1]
  dsimp only [Id.run]
  rw [memfdCreate_249_eq]
  dsimp only [Id.run]
  rw [memfdCreate_exec_eq]
  dsimp only [Id.run, NondetTest.assert, Bind.bind, Pure.pure]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨by decide, by decide, by decide⟩, trivial⟩

private theorem test_memfd_canReach_step (badNul overMax : ByteArray)
    (hNul : hasEmbeddedNul badNul = true)
    (hOver : overMax.data.size > MFD_NAME_MAX) :
    CanReach (test_sandbox_ops_memfdCreate_nameBoundsAndFlags modelOps SandboxSysState.unprivileged) := by
  have hNulEq := memfdCreate_einval_eq badNul (by rw [hNul, Bool.true_or])
  have hOverEq := memfdCreate_einval_eq overMax (by rw [decide_eq_true hOver, Bool.or_true])
  dsimp only [CanReach, CanReachRun, test_sandbox_ops_memfdCreate_nameBoundsAndFlags]
  refine ⟨badNul, hNul, overMax, hOver, ?_⟩
  rw [hNulEq, hOverEq]
  dsimp only [Id.run]
  rw [memfdCreate_conf_eq]
  dsimp only [Id.run]
  rw [memfdCreate_rest_eq.2.1]
  dsimp only [Id.run]
  rw [memfdCreate_249_eq]
  dsimp only [Id.run]
  rw [memfdCreate_exec_eq]
  dsimp only [Id.run, NondetTest.assert, Bind.bind, Pure.pure]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨by decide, by decide, by decide⟩, trivial⟩

/-- Reachability witness for `test_sandbox_ops_memfdCreate_nameBoundsAndFlags`. -/
theorem sandbox_ops_memfdCreate_nameBoundsAndFlags_canReach :
    CanReach (test_sandbox_ops_memfdCreate_nameBoundsAndFlags modelOps SandboxSysState.unprivileged) :=
  test_memfd_canReach_step (ByteArray.mk #[0]) (mkRepBytes 250) rfl (by rw [mkRepBytes_size]; decide)

end LeanSwe.LinuxSyscall.Sandbox
