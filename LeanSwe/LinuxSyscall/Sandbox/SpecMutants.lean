import LeanSwe.LinuxSyscall.Sandbox.SpecTests

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private def baseWrapperOps (raw : PosixSandboxOpsM (StateM Nat) Nat) :
    SandboxOpsM (StateM Nat) Nat :=
  { landlockCreateRuleset := fun attr? flags =>
      match attr? with
      | none =>
        if flags == 0 then pure (.error Errno.EINVAL)
        else do
          match ← raw.landlockQuery flags with
          | .ok v => return .ok (.version v)
          | .error e => return .error e
      | some attr =>
        if flags != 0 then pure (.error Errno.EINVAL)
        else do
          match ← raw.landlockCreate attr.handledAccessFs attr.handledAccessNet with
          | .ok h => return .ok (.ruleset h)
          | .error e => return .error e
    landlockAddRule := fun rs rule =>
      match rule with
      | .pathBeneath p acc => raw.landlockAddPathBeneath rs p acc
      | .netPort port acc => raw.landlockAddNetPort rs port acc
    landlockRestrictSelf := raw.landlockRestrictSelf
    seccomp := fun op flags filterBytes =>
      match op with
      | .getActionAvail a =>
        if flags.toBits != 0 then pure (.error Errno.EINVAL)
        else raw.seccompGetActionAvail a
      | .setModeFilter =>
        if !isValidSeccompFilterByteLen filterBytes.data.size ||
            !hasSafeSeccompRetBytes filterBytes then
          pure (.error Errno.EINVAL)
        else raw.seccompSetFilter flags.toBits filterBytes
    prctl := fun op =>
      let (tag, arg) := op.toRaw
      raw.prctl tag arg
    setrlimit := fun res cur max => raw.setrlimit res.toTag cur max
    memfdCreate := fun name flags =>
      if hasEmbeddedNul name || name.data.size > MFD_NAME_MAX then pure (.error Errno.EINVAL)
      else raw.memfdCreate name flags.toBits }

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

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    (fun e => e == Errno.EFAULT || Errno.isTransientOsErrno e)
    SandboxErrorKind.ofErrno) := by
  intro h
  have h0 := h Errno.EFAULT
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    Errno.isTransientOsErrno
    (fun e => if e == ENOMSG then .permissionDenied else SandboxErrorKind.ofErrno e)) := by
  intro h
  have h0 := h ENOMSG
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    Errno.isTransientOsErrno
    (fun e => if e == EBADFD then .invalidArg else SandboxErrorKind.ofErrno e)) := by
  intro h
  have h0 := h EBADFD
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_errno_classificationAndConstants
    Errno.isTransientOsErrno
    (fun e => if e == Errno.ENOENT then .invalidArg else SandboxErrorKind.ofErrno e)) := by
  intro h
  have h0 := h Errno.ENOENT
  exact absurd h0.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encSeccomp := fun f => { f with tsyncEsrch := false }.toBits)) := by
  intro h
  have h0 := h { tsyncEsrch := false } { tsyncEsrch := true }
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encSeccomp := fun f =>
      (if f.tsync then (2 : UInt32) else 0) |||
      (if f.log then (1 : UInt32) else 0) |||
      (if f.specAllow then (4 : UInt32) else 0) |||
      (if f.tsyncEsrch then (16 : UInt32) else 0))) := by
  intro h
  have h0 := h {} {}
  exact absurd h0.2.1.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encPrctl := fun
      | .setChildSubreaper _ => (2, 0)
      | other => other.toRaw)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 (.setChildSubreaper false) (.setChildSubreaper true) 0
  exact absurd h1.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encRlimit := fun _ => 0)) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .nofile
  exact absurd h2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encMemfd := fun f =>
      (if f.cloexec then (1 : UInt32) else 0) |||
      (if f.allowSealing then (2 : UInt32) else 0) |||
      (if f.noexecSeal then (4 : UInt32) else 0) |||
      (if f.exec then (16 : UInt32) else 0))) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .core
  have h3 := h2.2.2 {} {}
  exact absurd h3.2.1.2.2.2.1 (by decide)

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (encBpf := fun prog =>
      ByteArray.mk ((prog.flatMap fun insn =>
        encodeSockFilterInsn { insn with jt := insn.jf, jf := insn.jt }).toArray))
    (decBpf := fun b =>
      (decodeSockFilters b).map (List.map fun insn => { insn with jt := insn.jf, jf := insn.jt }))) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .core
  have h3 := h2.2.2 {} {}
  have h4 := h3.2.2.2 { code := 0x0015, jt := 1, jf := 2, k := 0 }
  have hWire := h4.1
  have hNe : ByteArray.mk #[0x15, 0, 2, 1, 0, 0, 0, 0] ≠
      ByteArray.mk #[0x15, 0, 1, 2, 0, 0, 0, 0] := by
    intro heq
    have hd : (#[0x15, 0, 2, 1, 0, 0, 0, 0] : Array UInt8) = #[0x15, 0, 1, 2, 0, 0, 0, 0] :=
      congrArg ByteArray.data heq
    exact absurd hd (by decide)
  exact hNe hWire

example : ¬ Core.AllPass (test_sandbox_flags_andBpfCodecInjective
    (decBpf := fun b =>
      match decodeSockFilters b with
      | some p => some p
      | none => some [])) := by
  intro h
  have h0 := h {} {}
  have h1 := h0.2.2.2 .setNoNewPrivs .setNoNewPrivs 0
  have h2 := h1.2.2 .core .core
  have h3 := h2.2.2 {} {}
  have h4 := h3.2.2.2 { code := 0x0006, jt := 0, jf := 0, k := 0 }
  have h5 := h4.2 []
  have h6 := h5.2 (ByteArray.mk #[0]) (by decide)
  cases h6.1

example : ¬ Core.AllPass (test_sandbox_impl_wrapperGuards fun raw =>
    { baseWrapperOps raw with
      landlockCreateRuleset := fun attr? flags =>
        match attr? with
        | none => do
          let _ ← raw.landlockQuery flags
          if flags == 0 then return .error Errno.EINVAL
          else return .ok (.version (flags + 100))
        | some a => (baseWrapperOps raw).landlockCreateRuleset (some a) flags }) := by
  intro h
  have hOver : (mkRepBytes 250).data.size > MFD_NAME_MAX := by rw [mkRepBytes_size]; decide
  have hOkNm : hasEmbeddedNul (mkRepBytes 4) = false ∧ (mkRepBytes 4).data.size ≤ MFD_NAME_MAX := by
    rw [mkRepBytes_noNul, mkRepBytes_size]; exact ⟨rfl, by decide⟩
  have hOkF : allowAllSeccompFilterBytes.data.size > 0 ∧
      allowAllSeccompFilterBytes.data.size % 8 = 0 ∧
      allowAllSeccompFilterBytes.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8 ∧
      hasSafeSeccompRetBytes allowAllSeccompFilterBytes = true :=
    ⟨by decide, by decide, by decide, by decide⟩
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver
    (mkRepBytes 4) hOkNm
    ByteArray.empty (Or.inl rfl)
    allowAllSeccompFilterBytes hOkF
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hCnt : (1 : Nat) = 0 := congrArg Prod.snd h0.1
  cases hCnt

example : ¬ Core.AllPass (test_sandbox_impl_wrapperGuards fun raw =>
    { baseWrapperOps raw with
      landlockCreateRuleset := fun attr? flags =>
        match attr? with
        | none =>
          if flags == 0 then pure (.error Errno.EINVAL)
          else do
            match ← raw.landlockQuery flags with
            | .ok v => return .ok (.version v)
            | .error _ => return .error Errno.EINVAL
        | some a => (baseWrapperOps raw).landlockCreateRuleset (some a) flags }) := by
  intro h
  have hOver : (mkRepBytes 250).data.size > MFD_NAME_MAX := by rw [mkRepBytes_size]; decide
  have hOkNm : hasEmbeddedNul (mkRepBytes 4) = false ∧ (mkRepBytes 4).data.size ≤ MFD_NAME_MAX := by
    rw [mkRepBytes_noNul, mkRepBytes_size]; exact ⟨rfl, by decide⟩
  have hOkF : allowAllSeccompFilterBytes.data.size > 0 ∧
      allowAllSeccompFilterBytes.data.size % 8 = 0 ∧
      allowAllSeccompFilterBytes.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8 ∧
      hasSafeSeccompRetBytes allowAllSeccompFilterBytes = true :=
    ⟨by decide, by decide, by decide, by decide⟩
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver
    (mkRepBytes 4) hOkNm
    ByteArray.empty (Or.inl rfl)
    allowAllSeccompFilterBytes hOkF
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hErr := congrArg Prod.fst
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  injection hErr with hCode
  exact absurd hCode (by decide)

example : ¬ Core.AllPass (test_sandbox_impl_wrapperGuards fun raw =>
    { baseWrapperOps raw with
      memfdCreate := fun name flags =>
        if hasEmbeddedNul name then pure (.error Errno.EINVAL)
        else raw.memfdCreate name flags.toBits }) := by
  intro h
  have hOver : (mkRepBytes 250).data.size > MFD_NAME_MAX := by rw [mkRepBytes_size]; decide
  have hOkNm : hasEmbeddedNul (mkRepBytes 4) = false ∧ (mkRepBytes 4).data.size ≤ MFD_NAME_MAX := by
    rw [mkRepBytes_noNul, mkRepBytes_size]; exact ⟨rfl, by decide⟩
  have hOkF : allowAllSeccompFilterBytes.data.size > 0 ∧
      allowAllSeccompFilterBytes.data.size % 8 = 0 ∧
      allowAllSeccompFilterBytes.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8 ∧
      hasSafeSeccompRetBytes allowAllSeccompFilterBytes = true :=
    ⟨by decide, by decide, by decide, by decide⟩
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver
    (mkRepBytes 4) hOkNm
    ByteArray.empty (Or.inl rfl)
    allowAllSeccompFilterBytes hOkF
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hMfd := h0.2.2.2.2.2.1
  rw [mkRepBytes_noNul] at hMfd
  have hFst := congrArg Prod.fst hMfd
  cases hFst

example : ¬ Core.AllPass (test_sandbox_impl_wrapperGuards fun raw =>
    { baseWrapperOps raw with
      seccomp := fun op flags filterBytes =>
        match op with
        | .getActionAvail a =>
          if flags.toBits != 0 then pure (.error Errno.EINVAL)
          else raw.seccompGetActionAvail a
        | .setModeFilter =>
          if filterBytes.data.size == 0 || filterBytes.data.size % 8 != 0 then
            pure (.error Errno.EINVAL)
          else
            raw.seccompSetFilter flags.toBits filterBytes }) := by
  intro h
  have hOver : (mkRepBytes 250).data.size > MFD_NAME_MAX := by rw [mkRepBytes_size]; decide
  have hOkNm : hasEmbeddedNul (mkRepBytes 4) = false ∧ (mkRepBytes 4).data.size ≤ MFD_NAME_MAX := by
    rw [mkRepBytes_noNul, mkRepBytes_size]; exact ⟨rfl, by decide⟩
  have hBad161 : (mkRepBytes 1288).data.size = 0 ∨ (mkRepBytes 1288).data.size % 8 ≠ 0 ∨
      (mkRepBytes 1288).data.size > SECCOMP_MAX_FILTER_INSNS * 8 ∨
      hasSafeSeccompRetBytes (mkRepBytes 1288) = false := by
    rw [mkRepBytes_size]; exact Or.inr (Or.inr (Or.inl (by decide)))
  have hOkF : allowAllSeccompFilterBytes.data.size > 0 ∧
      allowAllSeccompFilterBytes.data.size % 8 = 0 ∧
      allowAllSeccompFilterBytes.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8 ∧
      hasSafeSeccompRetBytes allowAllSeccompFilterBytes = true :=
    ⟨by decide, by decide, by decide, by decide⟩
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver
    (mkRepBytes 4) hOkNm
    (mkRepBytes 1288) hBad161
    allowAllSeccompFilterBytes hOkF
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hSec := h0.2.2.2.1
  rw [mkRepBytes_size] at hSec
  have hFst := congrArg Prod.fst hSec
  cases hFst

example : ¬ Core.AllPass (test_sandbox_impl_seccompSafetyGuards fun raw =>
    { baseWrapperOps raw with
      seccomp := fun op flags filterBytes =>
        match op with
        | .getActionAvail a => (baseWrapperOps raw).seccomp (.getActionAvail a) flags filterBytes
        | .setModeFilter =>
          if !isValidSeccompFilterByteLen filterBytes.data.size then pure (.error Errno.EINVAL)
          else raw.seccompSetFilter flags.toBits filterBytes }) := by
  intro h
  have h0 := h {}
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hCnt := congrArg Prod.snd h0.1
  exact absurd hCnt (by decide)

example : ¬ Core.AllPass (test_sandbox_impl_seccompSafetyGuards fun raw =>
    { baseWrapperOps raw with
      seccomp := fun op flags filterBytes =>
        match op with
        | .getActionAvail a => (baseWrapperOps raw).seccomp (.getActionAvail a) flags filterBytes
        | .setModeFilter =>
          let allowEfault := match decodeSockFilters filterBytes with
            | none => false
            | some prog => prog.all fun insn =>
              if insn.code == 0x003c then false
              else if (insn.code &&& 0x0007) == 0x0006 then
                insn.code == 0x0006 &&
                  (let act := insn.k &&& SECCOMP_RET_ACTION_FULL
                   act == SECCOMP_RET_ALLOW || act == SECCOMP_RET_LOG ||
                   (act == SECCOMP_RET_ERRNO && (insn.k &&& 0xFFFF) != 0))
              else true
          if !isValidSeccompFilterByteLen filterBytes.data.size || !allowEfault then
            pure (.error Errno.EINVAL)
          else raw.seccompSetFilter flags.toBits filterBytes }) := by
  intro h
  have h0 := h {}
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hCnt := congrArg Prod.snd h0.2.1
  exact absurd hCnt (by decide)

example : ¬ Core.AllPass (test_sandbox_impl_seccompSafetyGuards fun raw =>
    { baseWrapperOps raw with
      seccomp := fun op flags filterBytes =>
        match op with
        | .getActionAvail a => (baseWrapperOps raw).seccomp (.getActionAvail a) flags filterBytes
        | .setModeFilter =>
          let allowKill := match decodeSockFilters filterBytes with
            | none => false
            | some prog => prog.all fun insn =>
              isSafeSeccompInsn insn ||
                (insn.code == 0x0006 && (insn.k &&& SECCOMP_RET_ACTION_FULL) == SECCOMP_RET_KILL_PROCESS)
          if !isValidSeccompFilterByteLen filterBytes.data.size || !allowKill then
            pure (.error Errno.EINVAL)
          else raw.seccompSetFilter flags.toBits filterBytes }) := by
  intro h
  have h0 := h {}
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hCnt := congrArg Prod.snd h0.2.2.1
  exact absurd hCnt (by decide)

example : ¬ Core.AllPass (test_sandbox_impl_seccompSafetyGuards fun raw =>
    { baseWrapperOps raw with
      seccomp := fun op flags filterBytes =>
        match op with
        | .getActionAvail a => (baseWrapperOps raw).seccomp (.getActionAvail a) flags filterBytes
        | .setModeFilter =>
          let allowRetA := match decodeSockFilters filterBytes with
            | none => false
            | some prog => prog.all fun insn =>
              isSafeSeccompInsn insn || insn.code == 0x0016
          if !isValidSeccompFilterByteLen filterBytes.data.size || !allowRetA then
            pure (.error Errno.EINVAL)
          else raw.seccompSetFilter flags.toBits filterBytes }) := by
  intro h
  have h0 := h {}
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hCnt := congrArg Prod.snd h0.2.2.2.2.2.2.1
  exact absurd hCnt (by decide)

example : ¬ Core.AllPass (test_sandbox_impl_seccompSafetyGuards fun raw =>
    { baseWrapperOps raw with
      seccomp := fun op flags filterBytes =>
        match op with
        | .getActionAvail a => (baseWrapperOps raw).seccomp (.getActionAvail a) flags filterBytes
        | .setModeFilter =>
          let allowDivX := match decodeSockFilters filterBytes with
            | none => false
            | some prog => prog.all fun insn =>
              isSafeSeccompInsn insn || insn.code == 0x003c
          if !isValidSeccompFilterByteLen filterBytes.data.size || !allowDivX then
            pure (.error Errno.EINVAL)
          else raw.seccompSetFilter flags.toBits filterBytes }) := by
  intro h
  have h0 := h {}
  dsimp only [baseWrapperOps, Bind.bind, assert, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h0
  have hCnt := congrArg Prod.snd h0.2.2.2.2.2.2.2.2.1
  exact absurd hCnt (by decide)

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
      Except.error ENOMSG := h.2.2.2.1.1
  injection hEm with hCode
  exact absurd hCode (by decide)

example : ¬ Core.AllPass (test_sandbox_ops_landlock_rulesetAddRuleAndRestrictSelf
    { stubUnitOps with
      landlockCreateRuleset := fun attr? flags =>
        match attr?, flags with
        | none, 1 => pure (.ok (.version 9))
        | none, _ => pure (.error Errno.EINVAL)
        | some { handledAccessFs := 0, handledAccessNet := 0 }, 0 => pure (.error ENOMSG)
        | some a, 0 =>
          if (a.handledAccessFs &&& ~~~LANDLOCK_ACCESS_FS_V4_ALL) != 0 ||
             (a.handledAccessNet &&& ~~~LANDLOCK_ACCESS_NET_ALL) != 0 then
            pure (.error Errno.EINVAL)
          else
            pure (.ok (.ruleset 0))
        | some _, _ => pure (.error Errno.EINVAL)
      landlockAddRule := fun rs rule =>
        if rs == 999 then pure (.error Errno.EBADF)
        else if rs == 1 || rs == 102 then pure (.error EBADFD)
        else
          match rule with
          | .pathBeneath p acc =>
            if acc == 0 then pure (.error ENOMSG)
            else if (acc &&& LANDLOCK_ACCESS_FS_WRITE_FILE) != 0 then pure (.error Errno.EINVAL)
            else if p == 999 then pure (.error Errno.EBADF)
            else if p == 1 || p == 102 || p == 0 then pure (.error EBADFD)
            else if p == 101 && (acc &&& LANDLOCK_DIR_ONLY_FS_MASK) != 0 then pure (.error Errno.EINVAL)
            else pure (.ok ())
          | .netPort port acc =>
            if acc == 0 then pure (.error ENOMSG)
            else if acc == LANDLOCK_ACCESS_NET_BIND_TCP || port > 65535 then pure (.error Errno.EINVAL)
            else pure (.ok ())
      landlockRestrictSelf := fun rs =>
        if rs == 999 then pure (.error Errno.EBADF)
        else if rs == 1 || rs == 102 then pure (.error EBADFD)
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
        if rs == 50 && e == EBADFD then none else allowedStep s req out
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
          if e == EBADFD then some s else none
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
