import Core.NondetTest
import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model
import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Interface
import LeanSwe.ProcessSandbox.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.ProcessSandbox`. -/

namespace LeanSwe.ProcessSandbox

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.ProcessSandbox.Model

private def stubCompileSeccompBpf (arch : SeccompArch) : Array SockFilter :=
  #[ bpfStmt BPF_LD_W_ABS 4
   , bpfJump BPF_JMP_JEQ_K (auditArchOf arch) 1 0
   , bpfStmt BPF_RET_K 0x00050001
   , bpfStmt BPF_RET_K 0x7fff0000 ]

private theorem validMockBytes_wire8 :
    isValidMockSeccompBytes (ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f]) = true := rfl

private theorem validMockBytes_stubX86 :
    isValidMockSeccompBytes (encodeSeccompBpfModel (stubCompileSeccompBpf .x86_64)) = true := rfl

private theorem validMockBytes_stubAarch64 :
    isValidMockSeccompBytes (encodeSeccompBpfModel (stubCompileSeccompBpf .aarch64)) = true := rfl

private theorem validMockBytes_empty :
    isValidMockSeccompBytes ByteArray.empty = false := rfl

private def stubRunGeneric {m : Type → Type} [Monad m] [MonadFinally m]
    (raw : RawProcessSandboxOpsM m) (spec : BoxSpec) : m (Except SandboxError SandboxResult) := do
  match validateSpecPure spec with
  | .error e => return .error e
  | .ok valid =>
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    match ← raw.preflight req with
    | .error e =>
      return .error { e with kind := .unavailable, message := if e.message.isEmpty then "unavailable" else e.message }
    | .ok () =>
      match ← raw.hostSeccompArch with
      | .error e =>
        return .error { e with kind := .unavailable, message := if e.message.isEmpty then "arch unavailable" else e.message }
      | .ok arch =>
        match ← raw.discoverHostPreset with
        | .error e =>
          return .error { e with message := if e.message.isEmpty then "preset error" else e.message }
        | .ok preset =>
          let plan := compilePlan valid preset
          let seccompBytes := encodeSeccompBpfModel (stubCompileSeccompBpf arch)
          match ← raw.sealPlan plan seccompBytes with
          | .error e =>
            return .error { e with message := if e.message.isEmpty then "sealPlan error" else e.message }
          | .ok ph =>
            let (res, _) ← tryFinally' (do
              match ← raw.spawnBox ph with
              | .error e =>
                return .error { e with message := if e.message.isEmpty then "spawnBox error" else e.message }
              | .ok bh =>
                let (boxRes, _) ← tryFinally' (do
                  let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                    if plan.portForwards.isEmpty then
                      pure (Except.ok none)
                    else do
                      match ← raw.startPortForwarders bh plan.portForwards with
                      | .error e =>
                        pure (Except.error { e with message := if e.message.isEmpty then "forwarder error" else e.message })
                      | .ok fh =>
                        pure (Except.ok (some fh))
                  match fwdRes with
                  | .error e => return .error e
                  | .ok fwdOpt =>
                    let (ioRes, _) ← tryFinally'
                      (raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                      (fun _ =>
                        match fwdOpt with
                        | some fh => do let _ ← raw.stopPortForwarders fh; pure ()
                        | none => pure ())
                    match ioRes with
                    | .error e =>
                      return .error { e with message := if e.message.isEmpty then "io error" else e.message }
                    | .ok out =>
                      return .ok out
                ) (fun _ => do
                  let _ ← raw.killProcessGroup bh
                  let _ ← raw.pidfdKill bh
                  let _ ← raw.reapBox bh
                  pure ())
                return boxRes
            ) (fun _ => do
              let _ ← raw.closePlan ph
              pure ())
            return res

private def stubMkApi {m : Type → Type} [Monad m] [MonadFinally m]
    (raw : RawProcessSandboxOpsM m) : ProcessSandboxApiM m :=
  { validateSpec := validateSpecPure
    run := stubRunGeneric raw
    isAvailable := do
      match ← raw.preflight { needMemoryCgroup := true, needPidsCgroup := true } with
      | .ok () => return true
      | .error _ => return false }

private def stubApi : ProcessSandboxApi :=
  { validateSpec := validateSpecPure
    run := fun _ => pure (.error { kind := .unavailable, message := "stub" })
    isAvailable := pure false }

private def validAcceptStub (s : BoxSpec) : ValidBoxSpec :=
  { program := s.program
    args := s.args
    cwd := s.cwd.getD "/tmp"
    stdin := s.stdin
    mounts := s.mounts
    allowBoxLocalhost := s.allowBoxLocalhost
    portForwards := s.portForwards
    env := s.env
    limits := s.limits }

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsEmptyOrNulProgramAndArgs
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h { program := "" } rfl
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsInvalidCwd
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h { program := "sh", cwd := some "relative/dir" } "relative/dir" rfl (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsInvalidMountPaths
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h "../escape" (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsDuplicateBoxPath
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h (.scratch "/work") (.scratch "/work/") "/work" rfl rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsProtectedSystemBoxPaths
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h "/usr/bin" ["usr", "bin"] rfl rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsZeroAndDuplicatePorts
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h 8080 (by decide)
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_limitsRules
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  simp [Core.AllPass, test_psandbox_validateSpec_limitsRules, Bind.bind, assert] at h

example : ¬ Core.AllPass (test_psandbox_validateSpec_rejectsInvalidEnv
    { stubApi with validateSpec := fun s => .ok (validAcceptStub s) }) := by
  intro h
  have h0 := h { program := "sh", env := #[("BAD=KEY", "1")] } 0 (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandbox_validateSpec_defaultsOverridesAndIdempotence
    { stubApi with
      validateSpec := fun s =>
        match validateSpecPure s with
        | .error e => .error e
        | .ok v => .ok { v with cwd := "/" } }) := by
  intro h
  have h0 := h "FOO" "1" "2" (by decide) (by decide)
  have hEval :
      validateSpecPure
        { program := "python3"
          args := #["-c", "pass"]
          cwd := none
          mounts := #[.readOnly "/work/src" "/workspace/"]
          env := #[("FOO", "1"), ("FOO", "2")] } =
      .ok
        { program := "python3"
          args := #["-c", "pass"]
          cwd := "/tmp"
          stdin := ByteArray.empty
          mounts := #[.scratch "/tmp", .readOnly "/work/src" "/workspace"]
          allowBoxLocalhost := false
          portForwards := #[]
          env := #[("PATH", "/usr/bin:/bin"), ("FOO", "2")]
          limits := {} } := rfl
  dsimp [test_psandbox_validateSpec_defaultsOverridesAndIdempotence] at h0
  rw [hEval] at h0
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_invalidSpec_hasZeroSideEffects
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s => (.error { kind := .invalidInput, message := "leaked" }, { s with spawnCalls := s.spawnCalls + 1 }) })) := by
  intro h
  have h0 := h {} { program := "" }
  simp [stubMkApi, validateSpecPure, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandbox_isAvailable_and_failClosedUnavailable
    (fun raw => { stubMkApi raw with isAvailable := pure true })) := by
  intro h
  have h0 := h { hostBaseAvailable := false }
  simp [Bind.bind, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
            { s with lastSealedPlan := some { program := "env", emptyRoot := false } }) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  simp [Bind.bind, isValidCompiledPlan, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_outcomesAndOutputCap
    (fun raw =>
      { stubMkApi raw with
        run := fun _ => pure (.error { kind := .unavailable, message := "hijacked exit 125" }) })) := by
  intro h
  have h0 := h 125 9 ByteArray.empty ByteArray.empty
  simp [Bind.bind, StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_portForwarderBracket
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl, rfl⟩ rfl rfl
  simp [Bind.bind, StateT.run, Except.isOk, Except.toBool, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_conservesResourcesOnAllOutcomesAndErrors
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
            { s with openPlans := 99 :: s.openPlans }) })) := by
  intro h
  have h0 := h {} { program := "/bin/true" }
  simp [Bind.bind, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandbox_run_monadFinallyCleansUpOnCancellation
    (fun raw =>
      { validateSpec := validateSpecPure
        isAvailable := pure true
        run := fun spec => do
          match validateSpecPure spec with
          | .error e => return .error e
          | .ok valid =>
            let preset ← raw.discoverHostPreset
            match preset with
            | .error e => return .error e
            | .ok pr =>
              let plan := compilePlan valid pr
              let seccompBytes := ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f]
              match ← raw.sealPlan plan seccompBytes with
              | .error e => return .error e
              | .ok ph =>
                match ← raw.spawnBox ph with
                | .error e =>
                  let _ ← raw.closePlan ph
                  return .error e
                | .ok bh =>
                  let r ← raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes
                  let _ ← raw.killProcessGroup bh
                  let _ ← raw.pidfdKill bh
                  let _ ← raw.reapBox bh
                  let _ ← raw.closePlan ph
                  return r })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  dsimp [test_psandbox_run_monadFinallyCleansUpOnCancellation, mockRawOpsEx, mockRawOps,
    liftMockState, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validMockBytes_wire8,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd,
    Bind.bind, Pure.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h0
  exact absurd h0.1.2.1 (by decide)

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    (fun _ st _ => .ok st)) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, validateSpecPure,
    normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux, hasNulChar,
    validateMountsList, validateAndNormalizeMount, isReservedBoxSegs, reservedSystemTopDirs,
    formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs, defaultSandboxPath,
    defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.1

example : ¬ Core.AllPass (test_psandbox_model_hostUnchangedOutsideGrants
    (fun _ st _ => .ok { st with host := { st.host with hostAdminState := { powerGeneration := 1 } } })) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_hostUnchangedOutsideGrants,
    SpecHostUnchangedOutsideGrantsOn, assert] at h
  let validPlan : CompiledSandboxPlan := compilePlan default {}
  have hv : ValidCompiledPlan validPlan := rfl
  have hBlk := (h.1.1 validPlan {} (.adminOp .rebootOrKexec) hv).1 rfl
  simp [Except.isOk, Except.toBool] at hBlk

example : ¬ Core.AllPass (test_psandbox_model_zeroSurvivingBoxProcs
    stepGuestSyscall
    (fun st => st)) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_zeroSurvivingBoxProcs,
    SpecZeroSurvivingBoxProcsOn, assert] at h
  let validPlan : CompiledSandboxPlan := compilePlan default {}
  have hv : ValidCompiledPlan validPlan := rfl
  let stInit : SandboxWorldState := { box := { boxProcs := [1], boxMemoryBytes := 0 } }
  have hSurv := h.1 validPlan stInit [] hv
    (by intro maxP hp; injection hp with hpEq; subst hpEq; decide)
    (by intro maxM hm; injection hm with hmEq; subst hmEq; decide)
  have hProcs := hSurv.2.2.1
  simp [stInit, runGuestTraceWith] at hProcs

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure
    (fun valid _ => { program := valid.program, emptyRoot := false })) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  have hSound := h.1 { program := "/bin/true" } default {} hVal
  exact absurd hSound.2.1 (by decide)

private def mutantSilentUnsandboxedFallback (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec => do
      match validateSpecPure spec with
      | .error e => return .error e
      | .ok _ =>
        return .ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

example : ¬ Core.AllPass (test_psandbox_isAvailable_and_failClosedUnavailable
    mutantSilentUnsandboxedFallback) := by
  intro h
  have h0 := h {}
  dsimp [test_psandbox_isAvailable_and_failClosedUnavailable, Bind.bind, nondet, assume, assert] at h0
  have hUnavail := h0.2 { hostBaseAvailable := false } { program := "/bin/true" } rfl (Or.inl rfl)
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  dsimp [mutantSilentUnsandboxedFallback, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure] at hUnavail
  rw [hVal] at hUnavail
  rcases hUnavail.1.1 with ⟨e, he, _⟩
  cases he

private def mutantMagicExit97And98 (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec => do
      match ← stubRunGeneric raw spec with
      | .error e => return .error e
      | .ok res =>
        match res.outcome with
        | .exited 97 => return .error { kind := .unavailable, message := "magic exit 97" }
        | .exited 98 => return .ok { res with outcome := .timedOut }
        | _ => return .ok res }

example : ¬ Core.AllPass (test_psandbox_run_outcomesAndOutputCap mutantMagicExit97And98) := by
  intro h
  have h97 := h 97 9 ByteArray.empty ByteArray.empty
  dsimp [test_psandbox_run_outcomesAndOutputCap, mutantMagicExit97And98, stubRunGeneric,
    validMockBytes_stubX86,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h97
  cases h97.1.1

example : ¬ Core.AllPass (test_psandbox_run_outcomesAndOutputCap
    (fun raw =>
      { stubMkApi raw with
        run := fun spec => do
          match ← stubRunGeneric raw spec with
          | .error e => return .error e
          | .ok res =>
            if res.outcome == .exited 98 then return .ok { res with outcome := .timedOut }
            else return .ok res })) := by
  intro h
  have h98 := h 98 9 ByteArray.empty ByteArray.empty
  dsimp [test_psandbox_run_outcomesAndOutputCap, stubRunGeneric,
    validMockBytes_stubX86,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h98
  injection h98.1.1 with hRes
  injection hRes with hOut
  cases hOut

private def mutantRoBindRootStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .fsRead _ => .ok st
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics mutantRoBindRootStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantRoBindRootStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  have hHome := h0.2.2.2.2.2.2.1
  simp [Except.isOk, Except.toBool] at hHome

private def mutantOmitDefaultTmpCompile (valid : ValidBoxSpec) (preset : HostRuntimePreset) :
    CompiledSandboxPlan :=
  let base := compilePlan valid preset
  { base with userMounts := base.userMounts.filter (fun m => mountBoxPath m != "/tmp") }

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure mutantOmitDefaultTmpCompile) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  have hSound := h.1 { program := "/bin/true" } default {} hVal
  exact absurd hSound.1 (by unfold ValidCompiledPlan; decide)

private def mutantLeakHostLoopbackStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .tcpSend true port payload =>
    if port == 0 then .error .networkBlocked
    else
      .ok { st with host := { st.host with hostPorts := st.host.hostPorts ++ [(port, payload)] } }
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_hostUnchangedOutsideGrants mutantLeakHostLoopbackStep) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_hostUnchangedOutsideGrants,
    SpecHostUnchangedOutsideGrantsOn, assert] at h
  let basePlan := compilePlan { (default : ValidBoxSpec) with allowBoxLocalhost := true } {}
  have hv : ValidCompiledPlan basePlan := rfl
  have hBoxLocal := (h.1.1 basePlan {} (.tcpSend true 9999 ByteArray.empty) hv).2 rfl
  rcases hBoxLocal with ⟨st', hStep, hHostEq⟩
  dsimp [mutantLeakHostLoopbackStep] at hStep
  injection hStep with hSt
  subst hSt
  have hLen := congrArg (fun hs => hs.hostPorts.length) hHostEq
  simp at hLen

private def mutantInheritHostEnvCompile (valid : ValidBoxSpec) (preset : HostRuntimePreset) :
    CompiledSandboxPlan :=
  let base := compilePlan valid preset
  { base with env := base.env.push ("SECRET_KEY", "leaked_host_token") }

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure mutantInheritHostEnvCompile) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  have hSound := h.1 { program := "/bin/true" } default {} hVal
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hEnvProp, _⟩ := hSound
  have hEnv := hEnvProp ("SECRET_KEY", "leaked_host_token") (by decide)
  rcases hEnv with hPath | hInSpec
  · injection hPath with hk _; exact absurd hk (by decide)
  · simp at hInSpec

private def mutantPerProcessRlimitMemStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .mmapAnon bytes =>
    if match plan.limits.memoryMaxBytes with
        | some maxM => decide (bytes > maxM)
        | none => false then
      .error .memoryLimitExceeded
    else
      .ok { st with box := { st.box with boxMemoryBytes := st.box.boxMemoryBytes + bytes } }
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_zeroSurvivingBoxProcs
    mutantPerProcessRlimitMemStep reapAndTeardownBox) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_zeroSurvivingBoxProcs,
    SpecZeroSurvivingBoxProcsOn, assert] at h
  let smallValid : ValidBoxSpec :=
    { (default : ValidBoxSpec) with
      limits := { timeoutMs := 1000, memoryMaxBytes := some 1024, pidsMax := some 8 } }
  let smallPlan : CompiledSandboxPlan := compilePlan smallValid {}
  have hv : ValidCompiledPlan smallPlan := rfl
  let stInit : SandboxWorldState := { box := { boxProcs := [1], boxMemoryBytes := 0 } }
  let twoChildTrace : List GuestSyscall := [.cloneProc 2 false, .mmapAnon 1024, .mmapAnon 1024]
  have hRes := h.1 smallPlan stInit twoChildTrace hv
    (by intro maxP hp; injection hp with hpEq; subst hpEq; decide)
    (by intro maxM hm; injection hm with hmEq; subst hmEq; decide)
  have hMem := hRes.2.1 1024 rfl
  exact absurd hMem (by decide)

example : ¬ Core.AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    (fun raw =>
      { stubMkApi raw with
        run := fun _ s =>
          (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
            { s with lastSealedPlan := some { (compilePlan default {}) with directCgroupV2Fs := false } }) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  simp [Bind.bind, isValidCompiledPlan, StateT.run, assert] at h0

private def mutantFallbackOnSpawnUnavailable (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec => do
      match validateSpecPure spec with
      | .error e => return .error e
      | .ok valid =>
        let req : PreflightReq :=
          { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
            needPidsCgroup := valid.limits.pidsMax.isSome }
        match ← raw.preflight req with
        | .error e => return .error { e with kind := .unavailable, message := "unavailable" }
        | .ok () =>
          match ← raw.discoverHostPreset with
          | .error e => return .error e
          | .ok preset =>
            let seccompBytes := ByteArray.mk #[6, 0, 0, 0, 0, 0, 0xff, 0x7f]
            match ← raw.sealPlan (compilePlan valid preset) seccompBytes with
            | .error e => return .error e
            | .ok ph =>
              let sp ← raw.spawnBox ph
              let _ ← raw.closePlan ph
              match sp with
              | .error _ =>
                return .ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
              | .ok bh =>
                let _ ← raw.reapBox bh
                return .ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

example : ¬ Core.AllPass (test_psandbox_isAvailable_and_failClosedUnavailable
    mutantFallbackOnSpawnUnavailable) := by
  intro h
  have h0 := h {}
  dsimp [test_psandbox_isAvailable_and_failClosedUnavailable, Bind.bind, nondet, assume, assert] at h0
  have hUnavail := h0.2 { hostBaseAvailable := false } { program := "/bin/true" } rfl (Or.inl rfl)
  have hSpawn := hUnavail.2 {} { program := "/bin/true" } rfl ⟨rfl, rfl, rfl⟩
  dsimp [mutantFallbackOnSpawnUnavailable, mockRawOps, allocMockHandleId, isValidSandboxHandleId,
    validMockBytes_wire8,
    UInt64.size, validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars,
    splitSlashAux, hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure] at hSpawn
  rcases hSpawn.1.1 with ⟨e, he, _⟩
  cases he

private def mutantDropStdinRun (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric { raw with readBoxOutput := fun bh _ t m => raw.readBoxOutput bh ByteArray.empty t m } spec }

example : ¬ Core.AllPass (test_psandbox_run_forwardsStdinAndTimeoutMs mutantDropStdinRun) := by
  intro h
  have h0 := h {} ("payload".toUTF8) 5000 (by decide) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  dsimp [test_psandbox_run_forwardsStdinAndTimeoutMs, mutantDropStdinRun, stubRunGeneric,
    validMockBytes_stubX86,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h0
  have hStdin := h0.1.2.1
  injection hStdin with hEq
  have hSz := congrArg ByteArray.size hEq
  exact absurd hSz (by decide)

private def mutantDropTimeoutRun (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric { raw with readBoxOutput := fun bh stdin _ m => raw.readBoxOutput bh stdin 0 m } spec }

example : ¬ Core.AllPass (test_psandbox_run_forwardsStdinAndTimeoutMs mutantDropTimeoutRun) := by
  intro h
  have h0 := h {} ByteArray.empty 5000 (by decide) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  dsimp [test_psandbox_run_forwardsStdinAndTimeoutMs, mutantDropTimeoutRun, stubRunGeneric,
    validMockBytes_stubX86,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h0
  have hTout := h0.1.2.2.1
  exact absurd hTout (by decide)

private def insertByDepthUnstable {α : Type} (depth : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if depth x < depth y then x :: y :: ys else y :: insertByDepthUnstable depth x ys

private def sortByDepthUnstable {α : Type} (depth : α → Nat) : List α → List α
  | [] => []
  | x :: xs => insertByDepthUnstable depth x (sortByDepthUnstable depth xs)

private def mutantUnstableMountSortRun (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric
        { raw with
          sealPlan := fun plan seccompBytes =>
            raw.sealPlan
              { plan with userMounts := (sortByDepthUnstable mountBoxDepth plan.userMounts.toList).toArray }
              seccompBytes }
        spec }

example : ¬ Core.AllPass (test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan
    mutantUnstableMountSortRun) := by
  intro h
  have h0 := h {} ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  dsimp [test_psandbox_run_sealsSoundEmptyRootAndHomeMaskedPlan, mutantUnstableMountSortRun,
    stubRunGeneric, validMockBytes_stubX86,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sanitizePresetSystemEntry,
    allowlistedSystemRootPaths, allowlistedEtcPaths, parseSafePresetTargetSegs,
    expandPresetTopSymlink, isStrictlyNestedInDirs, dedupByFirst, presetEntryBoxPath,
    sortByDepth, insertByDepth, sortByDepthUnstable, insertByDepthUnstable,
    mountBoxDepth, mountBoxPath, tryFinally', MonadFinally.tryFinally',
    Bind.bind, Pure.pure, StateT.run, StateT.bind, StateT.pure, assert] at h0
  have hMounts := h0.2.2.2.2.2.2.2.2.1
  exact absurd hMounts (by decide)

private def mutantSkipSymlinkHomeExpandCompile (valid : ValidBoxSpec) (preset : HostRuntimePreset) :
    CompiledSandboxPlan :=
  let base := compilePlan valid preset
  { base with maskedPresetPaths := #[] }

example : ¬ Core.AllPass (test_psandbox_model_compilePlanSound
    validateSpecPure mutantSkipSymlinkHomeExpandCompile) := by
  intro h
  dsimp [Core.AllPass, test_psandbox_model_compilePlanSound,
    SpecCompilePlanSoundOn, assert] at h
  have hVal : validateSpecPure { program := "/bin/true" } = .ok default := rfl
  let symPreset : HostRuntimePreset :=
    { systemEntries := #[.readOnlyDir "/usr", .topSymlink "/lib" "usr/lib"]
      excludedHomePaths := #["/lib/custom_home/bob"] }
  have hSound := h.1 { program := "/bin/true" } default symPreset hVal
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hMaskProp⟩ := hSound
  dsimp [mutantSkipSymlinkHomeExpandCompile] at hMaskProp
  have hInSys :
      (.readOnlyDir "/usr" : PresetSystemEntry) ∈
        (compilePlan default symPreset).presetSystemEntries.toList := by
    change (.readOnlyDir "/usr" : PresetSystemEntry) ∈
      [.readOnlyDir "/usr", .topSymlink "/lib" "usr/lib"]
    exact List.Mem.head _
  have hMask := hMaskProp "/lib/custom_home/bob" ["lib", "custom_home", "bob"] (by decide) rfl
    ⟨.readOnlyDir "/usr", hInSys, ["usr"], rfl, by decide, by decide, by decide⟩
  exact absurd hMask.1 (by decide)

private def mutantBlockAnonSocketpairOnlyStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .anonUnixSocketpair _ => .error .blockedBySeccompOrNamespace
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    mutantBlockAnonSocketpairOnlyStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantBlockAnonSocketpairOnlyStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.2.1

private def mutantClone3EpermOnlyStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .clone3Attempt => .error .blockedBySeccompOrNamespace
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    mutantClone3EpermOnlyStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantClone3EpermOnlyStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.2.2.2.2.1

private def mutantWritableEtcHostsStep
    (plan : CompiledSandboxPlan) (st : SandboxWorldState) (sc : GuestSyscall) :
    Except SyscallBlockReason SandboxWorldState :=
  match sc with
  | .fsWrite "/etc/hosts" _ => .ok st
  | _ => stepGuestSyscall plan st sc

example : ¬ Core.AllPass (test_psandbox_model_threeCategorySyscallSemantics
    mutantWritableEtcHostsStep) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩
  dsimp [test_psandbox_model_threeCategorySyscallSemantics, mutantWritableEtcHostsStep,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, validateAndNormalizeMount, isReservedBoxSegs,
    reservedSystemTopDirs, formatAbsSegs, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, mountBoxPath, Bind.bind, assert] at h0
  cases h0.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private def mutantRunHardcodeX86Seccomp
    (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric
        { raw with
          sealPlan := fun plan _ =>
            raw.sealPlan plan (encodeSeccompBpfModel (stubCompileSeccompBpf .x86_64)) }
        spec }

example : ¬ Core.AllPass (test_seccomp_run_queriesHostArchAndSealsEncodedFilter
    mutantRunHardcodeX86Seccomp) := by
  intro h
  have h0 := h .aarch64 {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  dsimp [test_seccomp_run_queriesHostArchAndSealsEncodedFilter, mutantRunHardcodeX86Seccomp,
    stubMkApi, stubRunGeneric, validMockBytes_stubX86,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, assert] at h0
  have hSealed := h0.1.2.2.2.2.2.1
  injection hSealed with hBytes
  have hFlat : ∀ (xs : List SockFilter),
      (xs.flatMap Seccomp.Impl.encodeSockFilterList).length = 8 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x rest ih =>
      have hlen : (Seccomp.Impl.encodeSockFilterList x).length = 8 := rfl
      rw [List.flatMap_cons, List.length_append, hlen, ih, List.length_cons]
      omega
  have hEnc : ∀ (prog : Array SockFilter),
      (Seccomp.Impl.encodeSeccompBpf prog).size = 8 * prog.size := by
    intro prog
    unfold Seccomp.Impl.encodeSeccompBpf
    change (prog.toList.flatMap Seccomp.Impl.encodeSockFilterList).toArray.size = 8 * prog.size
    rw [List.size_toArray, hFlat, Array.length_toList]
  have hProgSize : 10 < (Seccomp.Impl.compileSeccompBpf .aarch64).size := by decide
  have hLhsSize : (encodeSeccompBpfModel (stubCompileSeccompBpf .x86_64)).size < 80 := by decide
  dsimp only [Seccomp.encodeSeccompBpf, Seccomp.compileSeccompBpf, Seccomp.defaultApi] at hBytes
  have hSz := congrArg ByteArray.size hBytes
  rw [hEnc (Seccomp.Impl.compileSeccompBpf .aarch64)] at hSz
  omega

private def mutantRunSealEmptySeccompBytes
    (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec =>
      stubRunGeneric
        { raw with sealPlan := fun plan _ => raw.sealPlan plan ByteArray.empty }
        spec }

example : ¬ Core.AllPass (test_seccomp_run_queriesHostArchAndSealsEncodedFilter
    mutantRunSealEmptySeccompBytes) := by
  intro h
  have h0 := h .x86_64 {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  dsimp [test_seccomp_run_queriesHostArchAndSealsEncodedFilter, mutantRunSealEmptySeccompBytes,
    stubMkApi, stubRunGeneric, validMockBytes_empty,
    mockRawOps, allocMockHandleId, isValidSandboxHandleId, UInt64.size,
    validateSpecPure, normalizeCleanAbsPath, parseCleanAbsSegs, splitSlashChars, splitSlashAux,
    hasNulChar, validateMountsList, allDistinct, isValidEnvPair, dedupEnvPairs,
    defaultSandboxPath, defaultSandboxCwd, compilePlan, sortByDepth, insertByDepth, mountBoxDepth,
    mountBoxPath, tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure,
    StateT.run, StateT.bind, StateT.pure, Except.isOk, Except.toBool, assert] at h0
  exact absurd h0.1.1 (by decide)

private def mutantRunWrongArchErrorKind
    (raw : RawProcessSandboxOpsM (StateM MockSandboxState)) :
    ProcessSandboxApiM (StateM MockSandboxState) :=
  { stubMkApi raw with
    run := fun spec => do
      match ← raw.hostSeccompArch with
      | .error _ => return .error { kind := .ioError, message := "arch lookup ioError" }
      | .ok _ => stubRunGeneric raw spec }

example : ¬ Core.AllPass (test_seccomp_run_queriesHostArchAndSealsEncodedFilter
    mutantRunWrongArchErrorKind) := by
  intro h
  have h0 := h .x86_64 {} ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  have hFail := h0.2 { hostSeccompArch? := none } { program := "/bin/true" } rfl ⟨rfl, rfl, rfl, rfl⟩
  dsimp [mutantRunWrongArchErrorKind, mockRawOps, StateT.run, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, assert] at hFail
  rcases hFail.1.1 with ⟨e, he, hKind, _⟩
  injection he with he'
  subst he'
  cases hKind

end LeanSwe.ProcessSandbox
