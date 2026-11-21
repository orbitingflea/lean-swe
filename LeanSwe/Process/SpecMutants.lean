import Core.NondetTest
import LeanSwe.Process.Types
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Impl
import LeanSwe.Process.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Process`. -/

namespace LeanSwe.Process

open Core (NondetTest)
open Core.NondetTest

private def stubProcessApi : ProcessApi :=
  { mapRawError := fun
      | .executableNotFound prog errno _ =>
        { kind := .notFound, program := some prog, errnoCode := some errno, message := "not found" }
      | .permissionDenied prog? errno _ =>
        { kind := .permissionDenied, program := prog?, errnoCode := some errno, message := "permission denied" }
      | .invalidArgument prog? errno _ =>
        { kind := .invalidInput, program := prog?, errnoCode := some errno, message := "invalid argument" }
      | .timedOut prog _ _ =>
        { kind := .timedOut, program := some prog, message := "timed out" }
      | .outputLimitExceeded prog _ _ =>
        { kind := .outputLimitExceeded, program := some prog, message := "output limit exceeded" }
      | .signaled prog sig _ =>
        { kind := .terminatedBySignal, program := some prog, signal := some sig, message := "signaled" }
      | .otherError errno _ =>
        { kind := .ioError, errnoCode := some errno, message := "os error" }
      | .userError _ =>
        { kind := .ioError, message := "process error" }
    validateRequest := fun req =>
      if req.program.isEmpty then
        .error { kind := .invalidInput, program := some req.program, message := "empty program" }
      else if req.program.toList.contains '\x00' then
        .error { kind := .invalidInput, program := some req.program, message := "NUL in program" }
      else if req.args.any (fun a => a.toList.contains '\x00') then
        .error { kind := .invalidInput, program := some req.program, message := "NUL in args" }
      else if match req.cwd with | some d => d.toList.contains '\x00' | none => false then
        .error { kind := .invalidInput, program := some req.program, message := "NUL in cwd" }
      else if req.env.any (fun kv =>
          kv.1.isEmpty || kv.1.toList.contains '=' || kv.1.toList.contains '\x00' ||
          match kv.2 with | some v => v.toList.contains '\x00' | none => false) then
        .error { kind := .invalidInput, program := some req.program, message := "invalid env" }
      else if req.timeoutMs == some 0 then
        .error { kind := .invalidInput, program := some req.program, message := "zero timeout" }
      else
        let dedup := req.env.foldl (fun acc kv =>
          (acc.filter (fun p => p.1 != kv.1)).push kv) #[]
        .ok { req with env := dedup }
    mkCommandRequest := fun program args => { program := program, args := args }
    withTextInput := fun req text => { req with stdin := text.toUTF8 }
    run := fun _ => pure (.error { kind := .ioError, message := "stub" })
    runChecked := fun _ => pure (.error { kind := .ioError, message := "stub" })
    runCommand := fun _ _ => pure (.error { kind := .ioError, message := "stub" })
    runCommandChecked := fun _ _ => pure (.error { kind := .ioError, message := "stub" })
    activeProcessCount := pure 0 }

private def stubStatefulRun (req : ExecRequest) : StateM Nat (Except ProcessError ExecResult) :=
  match stubProcessApi.validateRequest req with
  | .error e => pure (.error e)
  | .ok norm =>
    pure (.ok { exitCode := 1, stdout := "hello".toUTF8, stderr := norm.stdin })

private def stubStatefulRunChecked (req : ExecRequest) : StateM Nat (Except ProcessError ExecResult) :=
  match stubProcessApi.validateRequest req with
  | .error e => pure (.error e)
  | .ok norm =>
    pure (.error {
      kind := .nonZeroExit
      program := some norm.program
      exitCode := some 1
      stdout := some "hello".toUTF8
      stderr := some norm.stdin
      message := "non-zero exit" })

private def stubStatefulApi : ProcessApiM (StateM Nat) :=
  { mapRawError := stubProcessApi.mapRawError
    validateRequest := stubProcessApi.validateRequest
    mkCommandRequest := stubProcessApi.mkCommandRequest
    withTextInput := stubProcessApi.withTextInput
    run := stubStatefulRun
    runChecked := stubStatefulRunChecked
    runCommand := fun prog args =>
      stubStatefulRun (stubProcessApi.mkCommandRequest prog args)
    runCommandChecked := fun prog args =>
      stubStatefulRunChecked (stubProcessApi.mkCommandRequest prog args)
    activeProcessCount := fun n => (n, n) }

example : ¬ Core.AllPass (test_process_mapRawError_returnsNonEmptyMessage
    { stubProcessApi with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_mapRawError_preservesKindAndFields
    { stubProcessApi with
      mapRawError := fun
        | .outputLimitExceeded prog _ _ =>
          { kind := .ioError, program := some prog, message := "too big" }
        | other => stubProcessApi.mapRawError other }) := by
  intro h
  have h0 := h (.outputLimitExceeded "cat" 64 "cap")
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsEmptyProgram
    { stubProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "" } rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsNulInProgram
    { stubProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "a\x00b" } (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsNulInArg
    { stubProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", args := #["x\x00y"] } 0 (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsNulInCwd
    { stubProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", cwd := some "/tmp/\x00bad" } ⟨"/tmp/\x00bad", rfl, by decide⟩
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsInvalidEnv
    { stubProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", env := #[("A=B", some "1")] } 0 (by decide) (Or.inr (Or.inl (by decide)))
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsZeroTimeout
    { stubProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", timeoutMs := some 0 } rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_acceptsValidRequest
    { stubProcessApi with
      validateRequest := fun req =>
        if req.maxOutputBytes == some 0 then
          .error { kind := .invalidInput, message := "bad limit" }
        else stubProcessApi.validateRequest req }) := by
  intro h
  let req : ExecRequest :=
    { program := "echo"
      cwd := some "/tmp"
      timeoutMs := some 100
      maxOutputBytes := some 0
      inheritEnv := false
      env := #[("A", none)] }
  have h0 := h req (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [req, assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_idempotent
    { stubProcessApi with
      validateRequest := fun req =>
        if req.args.isEmpty then .ok { req with args := #["extra"] }
        else .error { kind := .invalidInput, message := "not idempotent" } }) := by
  intro h
  have h0 := h { program := "echo" }
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_preservesDirectArgsAndOptions
    { stubProcessApi with
      validateRequest := fun req =>
        .ok { req with program := "/bin/sh", args := #["-c", req.program] } }) := by
  intro h
  have h0 := h { program := "echo", args := #["a; rm -rf /"] }
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_envOverride_lastWins
    { stubProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h "echo" "FOO" (some "1") none
    (by decide) (by decide) (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_preservesDistinctEnv
    { stubProcessApi with
      validateRequest := fun req =>
        .ok { req with env := req.env.filter (fun kv => kv.2.isSome) } }) := by
  intro h
  have h0 := h "echo" "A" "B" (some "1") none
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_mkCommandRequest_preservesProgramAndArgsVerbatim
    { stubProcessApi with
      mkCommandRequest := fun p a => { program := "/bin/sh", args := #["-c", p] ++ a } }) := by
  intro h
  have h0 := h "echo" #["$(id)"]
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_withTextInput_encodesUtf8
    { stubProcessApi with
      withTextInput := fun req _ => { req with stdin := ByteArray.empty } }) := by
  intro h
  have h0 := h { program := "cat" } "hi"
  simp [assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_process_run_invalidRequest_doesNotLeak
    { stubStatefulApi with
      run := fun _ n => (.error { kind := .invalidInput, message := "bad" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "" }
  dsimp [test_process_run_invalidRequest_doesNotLeak] at h0
  have hVal : stubStatefulApi.validateRequest { program := "" } =
      .error { kind := .invalidInput, program := some "", message := "empty program" } := rfl
  rw [hVal] at h0
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt
    { stubStatefulApi with
      run := fun _ => pure (.ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty })
      runChecked := fun _ => pure (.ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty }) }) := by
  intro h
  have h0 := h 0 { program := "false" }
  simp [StateT.run, pure, StateT.pure, bind, assume, assert] at h0

example : ¬ Core.AllPass (test_process_runChecked_zeroExit_matchesRun
    { stubStatefulApi with
      run := fun _ => pure (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty })
      runChecked := fun _ => pure (.error { kind := .nonZeroExit, message := "wrong" }) }) := by
  intro h
  have h0 := h 0 { program := "true" } rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_process_run_neverLeaksProcesses
    { stubStatefulApi with
      run := fun _ n => (.error { kind := .timedOut, message := "timed out" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "sleep", timeoutMs := some 10 }
  simp [stubStatefulApi, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_process_timeout_cleansUpAndErrors
    { stubStatefulApi with
      run := fun req n =>
        (.error { kind := .timedOut, program := some req.program, message := "timed out" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "sleep", timeoutMs := some 10 } (by decide) rfl
  simp [stubStatefulApi, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_process_run_noTimeout_neverTimesOut
    { stubStatefulApi with
      run := fun req => pure (.error { kind := .timedOut, program := some req.program, message := "timed out" }) }) := by
  intro h
  have h0 := h 0 { program := "echo", timeoutMs := none } rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_outputLimit_cleansUpAndErrors
    { stubStatefulApi with
      run := fun req n =>
        (.error { kind := .outputLimitExceeded, program := some req.program, message := "too big" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "yes", maxOutputBytes := some 16 } (by decide) rfl
  simp [stubStatefulApi, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_process_run_respectsMaxOutputBytes
    { stubStatefulApi with
      run := fun _ =>
        pure (.ok { exitCode := 0, stdout := "exceeded!".toUTF8, stderr := ByteArray.empty }) }) := by
  intro h
  have h0 := h 0 { program := "echo", maxOutputBytes := some 2 } 2 rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_process_run_onError_returnsNonEmptyMessage
    { stubStatefulApi with
      run := fun _ => pure (.error { kind := .ioError, message := "" }) }) := by
  intro h
  have h0 := h 0 { program := "bad" }
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_run_usesNormalizedRequest
    { stubStatefulApi with
      validateRequest := fun req => .ok { req with env := #[("A", some "2")] }
      run := fun req =>
        pure (.ok { exitCode := 0, stdout := if req.env.size > 1 then "raw".toUTF8 else ByteArray.empty, stderr := ByteArray.empty }) }) := by
  intro h
  have h0 := h 0 { program := "env", env := #[("A", some "1"), ("A", some "2")] }
  simp [StateT.run, pure, StateT.pure, assert] at h0
  have hSize := congrArg (fun p => match p.1 with | .ok r => r.stdout.size | .error _ => 0) h0
  simp at hSize

example : ¬ Core.AllPass (test_process_runCommand_eq_runMkCommandRequest
    { stubStatefulApi with
      run := fun _ => pure (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty })
      runCommand := fun _ _ => pure (.error { kind := .ioError, message := "diverged" }) }) := by
  intro h
  have h0 := h 0 "echo" #["hi"]
  simp [StateT.run, pure, StateT.pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest
    { stubStatefulApi with
      runChecked := fun _ => pure (.error { kind := .nonZeroExit, message := "failed" })
      runCommandChecked := fun _ _ => pure (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }) }) := by
  intro h
  have h0 := h 0 "echo" #["hi"]
  simp [StateT.run, pure, StateT.pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_process_runChecked_propagatesRunError
    { stubStatefulApi with
      run := fun _ => pure (.error { kind := .notFound, message := "missing" })
      runChecked := fun _ => pure (.error { kind := .ioError, message := "changed" }) }) := by
  intro h
  have h0 := h 0 { program := "missing" }
  simp [StateT.run, pure, StateT.pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_process_runChecked_neverLeaksProcesses
    { stubStatefulApi with
      runChecked := fun _ n => (.error { kind := .timedOut, message := "timed out" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "sleep", timeoutMs := some 10 }
  simp [stubStatefulApi, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_process_run_noOutputLimit_neverExceedsLimit
    { stubStatefulApi with
      run := fun req => pure (.error { kind := .outputLimitExceeded, program := some req.program, message := "cap" }) }) := by
  intro h
  have h0 := h 0 { program := "echo", maxOutputBytes := none } rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_runChecked_onError_returnsNonEmptyMessage
    { stubStatefulApi with
      runChecked := fun _ => pure (.error { kind := .nonZeroExit, message := "" }) }) := by
  intro h
  have h0 := h 0 { program := "false" }
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_signaled_cleansUpAndErrors
    { stubStatefulApi with
      run := fun req =>
        pure (.error { kind := .terminatedBySignal, program := some req.program, signal := none, message := "killed" }) }) := by
  intro h
  have h0 := h 0 { program := "sleep" } rfl
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules
    (fun files prog _ envPairs fuel =>
      SysBridge.resolveExecutablePath files prog none envPairs fuel)) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_validateWorkingDir_chdirSemantics
    (fun _ _ _ => pure (.ok ()))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly
    (fun _ _ _ _ _ _ _ _ _ _ =>
      pure (.ok (.eof "abc".toUTF8 ByteArray.empty)))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof
    (fun files _ timeRand stdin startMs timeoutMs? _ stepFuel st _ => do
      let (inFdNext?, _, _, _, _) ←
        SysBridge.stepStdinOpt files timeRand st.inFd? stdin startMs timeoutMs? st.stdinPos stepFuel
      SysBridge.closeOpt files inFdNext?
      SysBridge.closeOpt files st.outFd?
      SysBridge.closeOpt files st.errFd?
      return .ok (.eof ByteArray.empty ByteArray.empty))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps
    (fun deps tbl eintrFuel ioFuel =>
      let base := SysBridge.mkRawOpsM deps tbl eintrFuel ioFuel
      { base with killProcessGroup := fun _ => pure (.ok ()) })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

example : ¬ Core.AllPass (test_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds
    (fun deps _ _ req => do
      match ← deps.proc.pipe2 { cloexec := true } with
      | .error e => return .error (SysBridge.mapErrno (some req.program) "pipe2" e)
      | .ok (inR, inW) =>
        match ← deps.proc.pipe2 { cloexec := true } with
        | .error e =>
          SysBridge.closeOpt deps.files (some inR)
          SysBridge.closeOpt deps.files (some inW)
          return .error (SysBridge.mapErrno (some req.program) "pipe2" e)
        | .ok _ =>
          match ← deps.proc.pipe2 { cloexec := true } with
          | .error e =>
            SysBridge.closeOpt deps.files (some inR)
            SysBridge.closeOpt deps.files (some inW)
            return .error (SysBridge.mapErrno (some req.program) "pipe2" e)
          | .ok _ =>
            return .ok { handleId := 0, pid := 1, pgid := 1 })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

/-- Mutant `mkApiM` corrupting `.signaled` signal number and swapping `stdout`/`stderr` is rejected by `test_process_mkApiM_preservesExactAwaitOutcomes`. -/
theorem mutant_mkApiM_corruptedSignaledAndSwappedStreams_rejected :
    ¬ Core.AllPass (test_process_mkApiM_preservesExactAwaitOutcomes
      (fun raw =>
        let base := Internal.mkApiM raw
        { base with
          run := fun req => do
            match ← base.run req with
            | .ok res => return .ok { res with stdout := res.stderr, stderr := res.stdout }
            | .error e => return .error { e with signal := e.signal.map (· + 1) } })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

/-- Mutant `resolveExecutablePath` accepting `+x` FIFO inodes instead of continuing `PATH` search is rejected by `test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules`. -/
theorem mutant_resolveExecutablePath_acceptsFifo_rejected :
    ¬ Core.AllPass (test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules
      (fun files prog cwd? _ _ => do
        if prog.toList.contains '/' then
          return .ok prog
        let p := SysBridge.probePathBytes cwd? "fifobin" prog
        match ← files.fstatat none p {} with
        | .ok _ => return .ok ("fifobin/" ++ prog)
        | .error e => return .error (SysBridge.mapErrno (some prog) "execvp" e))) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

/-- Mutant `mkRawOpsM` sending `SIGKILL` to `0` on `pgid = 1` or skipping pre-`PATH` `cwd` validation is rejected by `test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError`. -/
theorem mutant_mkRawOpsM_pgid1KillZero_rejected :
    ¬ Core.AllPass (test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError
      (fun deps tbl eintrFuel ioFuel =>
        let base := SysBridge.mkRawOpsM deps tbl eintrFuel ioFuel
        { base with
          killProcessGroup := fun _ => do
            let _ ← deps.proc.kill 0 .sigterm
            let _ ← deps.proc.kill 0 .sigkill
            return .ok () })) := by
  intro ⟨h, _⟩
  exact absurd h (by decide +kernel)

end LeanSwe.Process
