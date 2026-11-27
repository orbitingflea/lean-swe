import LeanSweProofs.LinuxSyscall.Sandbox.SpecTests
import LeanSweProofs.LinuxSyscall.Sandbox.SpecMutants.Extra

/-! Wrapper-guard and seccomp-safety negative specification mutants for `LeanSwe.LinuxSyscall.Sandbox`. -/

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private theorem mkRepBytes_size (n : Nat) : (mkRepBytes n).data.size = n := by
  unfold mkRepBytes
  rw [List.size_toArray, List.length_replicate]

private theorem hOver250 : (mkRepBytes 250).data.size > MFD_NAME_MAX := by
  rw [mkRepBytes_size]; decide

private theorem hOkNm4 : hasEmbeddedNul (mkRepBytes 4) = false ∧ (mkRepBytes 4).data.size ≤ MFD_NAME_MAX := by
  rw [mkRepBytes_noNul, mkRepBytes_size]; exact ⟨rfl, by decide⟩

private theorem hOkFilter : allowAllSeccompFilterBytes.data.size > 0 ∧
    allowAllSeccompFilterBytes.data.size % 8 = 0 ∧
    allowAllSeccompFilterBytes.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8 ∧
    hasSafeSeccompRetBytes allowAllSeccompFilterBytes = true :=
  ⟨by decide, by decide, by decide, by decide⟩

private theorem hBadFilter161 : (mkRepBytes 1288).data.size = 0 ∨ (mkRepBytes 1288).data.size % 8 ≠ 0 ∨
    (mkRepBytes 1288).data.size > SECCOMP_MAX_FILTER_INSNS * 8 ∨
    hasSafeSeccompRetBytes (mkRepBytes 1288) = false := by
  rw [mkRepBytes_size]; exact Or.inr (Or.inr (Or.inl (by decide)))

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
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver250
    (mkRepBytes 4) hOkNm4
    ByteArray.empty (Or.inl rfl)
    allowAllSeccompFilterBytes hOkFilter
  dsimp only [Bind.bind, assert, pure] at h0
  have h1 := h0.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h1
  have hCnt : (1 : Nat) = 0 := congrArg Prod.snd h1
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
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver250
    (mkRepBytes 4) hOkNm4
    ByteArray.empty (Or.inl rfl)
    allowAllSeccompFilterBytes hOkFilter
  dsimp only [Bind.bind, assert, pure] at h0
  have hRaw := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hRaw
  have hErr := congrArg Prod.fst hRaw
  injection hErr with hCode
  exact absurd hCode (by decide)

example : ¬ Core.AllPass (test_sandbox_impl_wrapperGuards fun raw =>
    { baseWrapperOps raw with
      memfdCreate := fun name flags =>
        if hasEmbeddedNul name then pure (.error Errno.EINVAL)
        else raw.memfdCreate name flags.toBits }) := by
  intro h
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver250
    (mkRepBytes 4) hOkNm4
    ByteArray.empty (Or.inl rfl)
    allowAllSeccompFilterBytes hOkFilter
  dsimp only [Bind.bind, assert, pure] at h0
  have hMfd := h0.2.2.2.2.2.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hMfd
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
  have h0 := h {} 1 (by decide) { tsync := true } (by decide) {} 0 .getNoNewPrivs .core 0 0 {}
    Errno.ENOMEM
    (ByteArray.mk #[97, 0, 98]) (by decide)
    (mkRepBytes 250) hOver250
    (mkRepBytes 4) hOkNm4
    (mkRepBytes 1288) hBadFilter161
    allowAllSeccompFilterBytes hOkFilter
  dsimp only [Bind.bind, assert, pure] at h0
  have hSec := h0.2.2.2.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at hSec
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
  dsimp only [Bind.bind, assert, pure] at h0
  have h1 := h0.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h1
  have hCnt := congrArg Prod.snd h1
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
  dsimp only [Bind.bind, assert, pure] at h0
  have h1 := h0.2.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h1
  have hCnt := congrArg Prod.snd h1
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
  dsimp only [Bind.bind, assert, pure] at h0
  have h1 := h0.2.2.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h1
  have hCnt := congrArg Prod.snd h1
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
  dsimp only [Bind.bind, assert, pure] at h0
  have h1 := h0.2.2.2.2.2.2.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h1
  have hCnt := congrArg Prod.snd h1
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
  dsimp only [Bind.bind, assert, pure] at h0
  have h1 := h0.2.2.2.2.2.2.2.2.1
  dsimp only [baseWrapperOps, Bind.bind, StateT.run, StateT.bind, pure,
    StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h1
  have hCnt := congrArg Prod.snd h1
  exact absurd hCnt (by decide)

end LeanSwe.LinuxSyscall.Sandbox
