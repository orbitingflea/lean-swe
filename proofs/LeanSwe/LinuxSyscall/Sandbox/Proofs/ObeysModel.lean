import Core.Obeys
import LeanSwe.LinuxSyscall.Sandbox.Impl
import LeanSwe.LinuxSyscall.Sandbox.Model.Refines
import LeanSwe.LinuxSyscall.Sandbox.Proofs.HealthyStep

/-!
Canonical `Core.ObeysStepFrom` capability-refinement proofs (`obeysStepFrom_sandbox`,
`modelRawOps_obeys_allowedRawStep`) for `LeanSwe.LinuxSyscall.Sandbox`.
-/

namespace LeanSwe.LinuxSyscall.Sandbox

open LeanSwe.LinuxSyscall

private theorem decodeSeccompFlags?_toBits (f : SeccompFlags) :
    Model.decodeSeccompFlags? f.toBits = some f := by
  cases f with
  | mk b1 b2 b3 b4 b5 =>
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

private theorem seccompFlags_eq_empty_of_toBits_zero {f : SeccompFlags}
    (h : (f.toBits != 0) = false) :
    f = {} := by
  cases f with
  | mk b1 b2 b3 b4 b5 =>
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
      first | rfl | cases h

private theorem decodePrctlOp?_toRaw (op : PrctlOp) :
    Model.decodePrctlOp? op.toRaw.1 op.toRaw.2 = some op := by
  cases op with
  | setNoNewPrivs => rfl
  | getNoNewPrivs => rfl
  | setChildSubreaper enable => cases enable <;> rfl
  | setPdeathsig _ => rfl

private theorem decodeRlimitResource?_toTag (res : RlimitResource) :
    Model.decodeRlimitResource? res.toTag = some res := by
  cases res <;> rfl

private theorem decodeMemfdFlags?_toBits (f : MemfdFlags) :
    Model.decodeMemfdFlags? f.toBits = some f := by
  cases f with
  | mk b1 b2 b3 b4 =>
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

private theorem healthyStep_pure_einval (env : HealthyEnv) (req : SandboxReq)
    (hwf : env.wf = true)
    (hCore : allowedStepCore env.state req (.err Errno.EINVAL) = some env.state)
    (hFail : failsPureWrapperGuard req = true) :
    healthyStep env req (.err Errno.EINVAL) = some env := by
  have hAl : allowedStep env.state req (.err Errno.EINVAL) = some env.state := by
    unfold allowedStep
    simp [hFail, hCore]
  have hNoCrit : isCriticalFault (.err Errno.EINVAL) = false := rfl
  have hNoEi : isEintrOutcome (.err Errno.EINVAL) = false := rfl
  have hTight := allowedStep_healthy_tight env req (.err Errno.EINVAL) env.state hAl hwf
    (by simp [hNoEi]) hNoCrit
  simp only [hNoEi, Bool.false_eq_true, ↓reduceIte] at hTight
  cases env
  exact hTight

private theorem healthyStep_seccomp_getActionAvail_irrel
    (env : HealthyEnv) (action : UInt32) (flags : SeccompFlags)
    (fb₁ fb₂ : ByteArray) (out : SandboxOutcome) :
    healthyStep env (.seccomp (.getActionAvail action) flags fb₁) out =
      healthyStep env (.seccomp (.getActionAvail action) flags fb₂) out := by
  have hCore : allowedStepCore env.state (.seccomp (.getActionAvail action) flags fb₁) out =
      allowedStepCore env.state (.seccomp (.getActionAvail action) flags fb₂) out := by
    cases out <;> rfl
  have hAl : allowedStep env.state (.seccomp (.getActionAvail action) flags fb₁) out =
      allowedStep env.state (.seccomp (.getActionAvail action) flags fb₂) out := by
    unfold allowedStep failsPureWrapperGuard
    rw [hCore]
  unfold healthyStep
  rw [hAl]

/-- Canonical `Core.ObeysStepFrom` refinement lifting `PosixSandboxOpsM` to `SandboxOpsM`. -/
theorem obeysStepFrom_sandbox :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkSandboxOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hwf
  dsimp only [Function.comp_apply, id, Model.rawStepWf] at hwf ⊢
  cases req with
  | landlockCreateRuleset attr? flags =>
    cases attr? with
    | none =>
      by_cases hFl : (flags == 0) = true
      · have h0 : flags = 0 := eq_of_beq hFl
        subst h0
        dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [beq_self_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
          StateT.run, StateT.bind, StateT.pure]
        exact healthyStep_pure_einval (proj w) (.landlockCreateRuleset none 0) hwf rfl rfl
      · have hStep := hRaw w (.landlockQuery flags) hwf
        dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
          Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
        dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [hFl, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
          StateT.run, StateT.bind]
        cases hCall : raw.landlockQuery flags w with
        | mk res w' =>
          rw [hCall] at hStep
          cases res <;> exact hStep
    | some attr =>
      by_cases hFl : (flags != 0) = true
      · dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [hFl, ↓reduceIte, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have hCore : allowedStepCore (proj w).state (.landlockCreateRuleset (some attr) flags)
            (.err Errno.EINVAL) = some (proj w).state := by
          unfold allowedStepCore
          have hEf : (Errno.EINVAL == Errno.EFAULT) = false := rfl
          simp [hEf, hFl]
        exact healthyStep_pure_einval (proj w) (.landlockCreateRuleset (some attr) flags)
          hwf hCore hFl
      · have h0 : flags = 0 := by
          cases hb : (flags == 0)
          · simp [bne, hb] at hFl
          · exact eq_of_beq hb
        subst h0
        have hStep := hRaw w (.landlockCreate attr.handledAccessFs attr.handledAccessNet) hwf
        have hAttr : ({ handledAccessFs := attr.handledAccessFs,
                        handledAccessNet := attr.handledAccessNet } : LandlockRulesetAttr) = attr := by
          cases attr; rfl
        dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
          Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
        rw [hAttr] at hStep
        dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [hFl, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
          StateT.run, StateT.bind]
        cases hCall : raw.landlockCreate attr.handledAccessFs attr.handledAccessNet w with
        | mk res w' =>
          rw [hCall] at hStep
          cases res <;> exact hStep
  | landlockAddRule ruleset rule =>
    cases rule with
    | pathBeneath parentFd access =>
      have hStep := hRaw w (.landlockAddPathBeneath ruleset parentFd access) hwf
      dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
        Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
        Internal.mkSandboxOpsM, Internal.mkSandboxOps,
        Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
      exact hStep
    | netPort port access =>
      have hStep := hRaw w (.landlockAddNetPort ruleset port access) hwf
      dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
        Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
        Internal.mkSandboxOpsM, Internal.mkSandboxOps,
        Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
      exact hStep
  | landlockRestrictSelf ruleset =>
    have hStep := hRaw w (.landlockRestrictSelf ruleset) hwf
    dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
      Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
      Internal.mkSandboxOpsM, Internal.mkSandboxOps,
      Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    exact hStep
  | seccomp op flags filterBytes =>
    cases op with
    | getActionAvail action =>
      by_cases hFl : (flags.toBits != 0) = true
      · dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [hFl, ↓reduceIte, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have hCore : allowedStepCore (proj w).state
            (.seccomp (.getActionAvail action) flags filterBytes) (.err Errno.EINVAL) =
            some (proj w).state := by
          unfold allowedStepCore
          have hEf : (Errno.EINVAL == Errno.EFAULT) = false := rfl
          simp [hEf, hFl]
        exact healthyStep_pure_einval (proj w)
          (.seccomp (.getActionAvail action) flags filterBytes) hwf hCore hFl
      · have hFlEq : flags = {} := seccompFlags_eq_empty_of_toBits_zero
          (Bool.eq_false_iff.mpr hFl)
        subst hFlEq
        have hStep := hRaw w (.seccompGetActionAvail action) hwf
        dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
          Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
        dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [hFl, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
          StateT.run, StateT.bind]
        rw [healthyStep_seccomp_getActionAvail_irrel _ _ _ filterBytes ByteArray.empty]
        exact hStep
    | setModeFilter =>
      by_cases hG : (!isValidSeccompFilterByteLen filterBytes.size ||
          !hasSafeSeccompRetBytes filterBytes) = true
      · dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [hG, ↓reduceIte, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
        have hCore : allowedStepCore (proj w).state
            (.seccomp .setModeFilter flags filterBytes) (.err Errno.EINVAL) =
            some (proj w).state := by
          unfold allowedStepCore
          have hEf : (Errno.EINVAL == Errno.EFAULT) = false := rfl
          simp [hEf]
          intro h1 h2
          simp [h1, h2] at hG
        exact healthyStep_pure_einval (proj w)
          (.seccomp .setModeFilter flags filterBytes) hwf hCore hG
      · have hStep := hRaw w (.seccompSetFilter flags.toBits filterBytes) hwf
        dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
          Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
        rw [decodeSeccompFlags?_toBits flags] at hStep
        dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
          Internal.mkSandboxOpsM, Internal.mkSandboxOps]
        simp only [hG, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
          StateT.run, StateT.bind]
        exact hStep
  | prctl op =>
    have hStep := hRaw w (.prctl op.toRaw.1 op.toRaw.2) hwf
    dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
      Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
    rw [decodePrctlOp?_toRaw op] at hStep
    dsimp only [Option.map, Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
      Internal.mkSandboxOpsM, Internal.mkSandboxOps,
      Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    exact hStep
  | setrlimit res cur max =>
    have hStep := hRaw w (.setrlimit res.toTag cur max) hwf
    dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
      Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
    rw [decodeRlimitResource?_toTag res] at hStep
    dsimp only [Option.map, Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
      Internal.mkSandboxOpsM, Internal.mkSandboxOps,
      Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep ⊢
    exact hStep
  | memfdCreate name flags =>
    by_cases hBad : (name.size > MFD_NAME_MAX || hasEmbeddedNul name) = true
    · dsimp only [Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
        Internal.mkSandboxOpsM, Internal.mkSandboxOps]
      simp only [hBad, ↓reduceIte, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
      have hBadModel : (hasEmbeddedNul name || decide (name.data.size > MFD_NAME_MAX)) = true := by
        change (decide (name.data.size > MFD_NAME_MAX) || hasEmbeddedNul name) = true at hBad
        rw [Bool.or_comm]; exact hBad
      have hCore : allowedStepCore (proj w).state (.memfdCreate name flags)
          (.err Errno.EINVAL) = some (proj w).state := by
        unfold allowedStepCore
        have hEf : (Errno.EINVAL == Errno.EFAULT) = false := rfl
        simp [hEf]
        intro h1 h2
        simp [h1] at hBad
        omega
      exact healthyStep_pure_einval (proj w) (.memfdCreate name flags) hwf hCore hBadModel
    · have hStep := hRaw w (.memfdCreate name flags.toBits) hwf
      dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep,
        Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure] at hStep
      rw [decodeMemfdFlags?_toBits flags] at hStep
      dsimp only [Option.map, Model.allowedPkgStep, Model.execPkgStep, execSandboxReq,
        Internal.mkSandboxOpsM, Internal.mkSandboxOps] at hStep ⊢
      simp only [hBad, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure,
        StateT.run, StateT.bind]
      exact hStep

/-- Reference `Model.modelRawOps` satisfies `Core.ObeysStep` against `Model.allowedRawStep`. -/
theorem modelRawOps_obeys_allowedRawStep :
    Core.ObeysStep id Model.rawStepWf (Model.execRawStep Model.modelRawOps) Model.allowedRawStep := by
  intro env req hwf
  dsimp only [id, Model.rawStepWf] at hwf ⊢
  cases req with
  | landlockQuery flags =>
    have hRef := healthyModelOps_refinesHealthySandbox env (.landlockCreateRuleset none flags) hwf
    dsimp only [id, execSandboxReq, Model.allowedRawStep, Model.decodeRawStepReq?,
      Model.execRawStep, Model.modelRawOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure] at hRef ⊢
    cases hCall : healthyModelOps.landlockCreateRuleset none flags env with
    | mk res env' =>
      rw [hCall] at hRef
      cases res with
      | error e => exact hRef
      | ok cr =>
        cases cr with
        | version v => exact hRef
        | ruleset hid =>
          have hCore := (healthyStep_implies_allowedStep env env'
            (.landlockCreateRuleset none flags) (.opened hid) hRef).2.1
          unfold allowedStepCore at hCore
          simp at hCore
  | landlockCreate fs net =>
    have hRef := healthyModelOps_refinesHealthySandbox env
      (.landlockCreateRuleset (some { handledAccessFs := fs, handledAccessNet := net }) 0) hwf
    dsimp only [id, execSandboxReq, Model.allowedRawStep, Model.decodeRawStepReq?,
      Model.execRawStep, Model.modelRawOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure] at hRef ⊢
    cases hCall : healthyModelOps.landlockCreateRuleset
        (some { handledAccessFs := fs, handledAccessNet := net }) 0 env with
    | mk res env' =>
      rw [hCall] at hRef
      cases res with
      | error e => exact hRef
      | ok cr =>
        cases cr with
        | ruleset hid => exact hRef
        | version v =>
          have hCore := (healthyStep_implies_allowedStep env env'
            (.landlockCreateRuleset (some { handledAccessFs := fs, handledAccessNet := net }) 0)
            (.landlockVersion v) hRef).2.1
          contradiction
  | landlockAddPathBeneath rs parentFd access =>
    have hRef := healthyModelOps_refinesHealthySandbox env
      (.landlockAddRule rs (.pathBeneath parentFd access)) hwf
    dsimp only [id, execSandboxReq, Model.allowedRawStep, Model.decodeRawStepReq?,
      Model.execRawStep, Model.modelRawOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure] at hRef ⊢
    exact hRef
  | landlockAddNetPort rs port access =>
    have hRef := healthyModelOps_refinesHealthySandbox env
      (.landlockAddRule rs (.netPort port access)) hwf
    dsimp only [id, execSandboxReq, Model.allowedRawStep, Model.decodeRawStepReq?,
      Model.execRawStep, Model.modelRawOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure] at hRef ⊢
    exact hRef
  | landlockRestrictSelf rs =>
    have hRef := healthyModelOps_refinesHealthySandbox env (.landlockRestrictSelf rs) hwf
    dsimp only [id, execSandboxReq, Model.allowedRawStep, Model.decodeRawStepReq?,
      Model.execRawStep, Model.modelRawOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure] at hRef ⊢
    exact hRef
  | seccompGetActionAvail action =>
    have hRef := healthyModelOps_refinesHealthySandbox env
      (.seccomp (.getActionAvail action) {} ByteArray.empty) hwf
    dsimp only [id, execSandboxReq, Model.allowedRawStep, Model.decodeRawStepReq?,
      Model.execRawStep, Model.modelRawOps, Bind.bind, Pure.pure,
      StateT.run, StateT.bind, StateT.pure] at hRef ⊢
    exact hRef
  | seccompSetFilter flagsBits filterBytes =>
    dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep, Model.modelRawOps]
    cases hDec : Model.decodeSeccompFlags? flagsBits with
    | none =>
      simp [hwf, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    | some flags =>
      have hRef := healthyModelOps_refinesHealthySandbox env
        (.seccomp .setModeFilter flags filterBytes) hwf
      dsimp only [id, execSandboxReq, Bind.bind, Pure.pure,
        StateT.run, StateT.bind, StateT.pure] at hRef ⊢
      exact hRef
  | prctl cmdTag arg =>
    dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep, Model.modelRawOps]
    cases hDec : Model.decodePrctlOp? cmdTag arg with
    | none =>
      simp [Option.map, hwf, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    | some op =>
      have hRef := healthyModelOps_refinesHealthySandbox env (.prctl op) hwf
      dsimp only [Option.map, id, execSandboxReq, Bind.bind, Pure.pure,
        StateT.run, StateT.bind, StateT.pure] at hRef ⊢
      exact hRef
  | setrlimit resTag cur max =>
    dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep, Model.modelRawOps]
    cases hDec : Model.decodeRlimitResource? resTag with
    | none =>
      simp [Option.map, hwf, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    | some res =>
      have hRef := healthyModelOps_refinesHealthySandbox env (.setrlimit res cur max) hwf
      dsimp only [Option.map, id, execSandboxReq, Bind.bind, Pure.pure,
        StateT.run, StateT.bind, StateT.pure] at hRef ⊢
      exact hRef
  | memfdCreate name flagsBits =>
    dsimp only [Model.allowedRawStep, Model.decodeRawStepReq?, Model.execRawStep, Model.modelRawOps]
    cases hDec : Model.decodeMemfdFlags? flagsBits with
    | none =>
      simp [Option.map, hwf, Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure]
    | some flags =>
      have hRef := healthyModelOps_refinesHealthySandbox env (.memfdCreate name flags) hwf
      dsimp only [Option.map, id, execSandboxReq, Bind.bind, Pure.pure,
        StateT.run, StateT.bind, StateT.pure] at hRef ⊢
      exact hRef

end LeanSwe.LinuxSyscall.Sandbox
