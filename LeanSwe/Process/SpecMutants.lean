import Core.NondetTest
import LeanSwe.Process.Types
import LeanSwe.Process.Model
import LeanSwe.Process.SpecTests
import LeanSwe.Process.SpecMutants.Extra

/-! Compile-time negative specification mutants for `LeanSwe.Process`. -/

namespace LeanSwe.Process

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Process.SpecMutants

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    match decEq e1 e2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hEq => by injection hEq with h'; exact h h')
  | .ok a1, .ok a2 =>
    match decEq a1 a2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hEq => by injection hEq with h'; exact h h')
  | .error _, .ok _ => isFalse (fun hEq => by cases hEq)
  | .ok _, .error _ => isFalse (fun hEq => by cases hEq)

private instance {α : Type} [DecidableEq α] : DecidableEq (Id α) :=
  inferInstanceAs (DecidableEq α)

private def capOutputPair (out err : ByteArray) : Option Nat → ByteArray × ByteArray
  | none => (out, err)
  | some lim =>
    let outCap := out.extract 0 (Nat.min out.size lim)
    let errCap := err.extract 0 (Nat.min err.size (lim - outCap.size))
    (outCap, errCap)

private def refRawIoOps : RawProcessOpsM IO :=
  { mapRawError := Model.mapRawErrorModel
    spawn := fun req =>
      if req.program == "missing" then
        pure (.error (Model.mapRawErrorModel (.executableNotFound "missing" 2 "not found")))
      else
        let pid : Int := if req.program == "true" then 1 else 2
        pure (.ok { handleId := 1, pid := pid, pgid := 1 })
    awaitOutput := fun h stdin _ max? =>
      let (out, err) := capOutputPair "hello".toUTF8 stdin max?
      let code : Int := if h.pid == 1 then 0 else 1
      pure (.ok (.exited { exitCode := code, stdout := out, stderr := err }))
    killProcessGroup := fun _ => pure (.ok ())
    reap := fun _ => pure (.ok ())
    activeProcessCount := pure 0 }

private def refProcessApi : ProcessApi :=
  refMkApiM refRawIoOps

private def refRawNatOps : RawProcessOpsM (StateM Nat) :=
  { mapRawError := Model.mapRawErrorModel
    spawn := fun req =>
      if req.program == "missing" then
        pure (.error (Model.mapRawErrorModel (.executableNotFound "missing" 2 "not found")))
      else
        modifyGet fun n =>
          let pid : Int := if req.program == "true" then 1 else 2
          (.ok { handleId := n + 1, pid := pid, pgid := 1 }, n + 1)
    awaitOutput := fun h stdin _ max? =>
      let (out, err) := capOutputPair "hello".toUTF8 stdin max?
      let code : Int := if h.pid == 1 then 0 else 1
      pure (.ok (.exited { exitCode := code, stdout := out, stderr := err }))
    killProcessGroup := fun _ => pure (.ok ())
    reap := fun _ => modifyGet fun n => (.ok (), n - 1)
    activeProcessCount := get }

private def refStatefulApi : ProcessApiM (StateM Nat) :=
  refMkApiM refRawNatOps

example : ¬ Core.AllPass (test_process_mapRawError_returnsNonEmptyMessage
    { refProcessApi with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_mapRawError_preservesKindAndFields
    { refProcessApi with
      mapRawError := fun
        | .outputLimitExceeded prog _ _ =>
          { kind := .ioError, program := some prog, message := "too big" }
        | other => refProcessApi.mapRawError other }) := by
  intro h
  have h0 := h (.outputLimitExceeded "cat" 64 "cap")
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsEmptyProgram
    { refProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "" } rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsNulInProgram
    { refProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "a\x00b" } (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsNulInArg
    { refProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", args := #["x\x00y"] } 0 (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsNulInCwd
    { refProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", cwd := some "/tmp/\x00bad" } ⟨"/tmp/\x00bad", rfl, by decide⟩
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsInvalidEnv
    { refProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", env := #[("A=B", some "1")] } 0 (by decide) (Or.inr (Or.inl (by decide)))
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_rejectsZeroTimeout
    { refProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h { program := "echo", timeoutMs := some 0 } rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_acceptsValidRequest
    { refProcessApi with
      validateRequest := fun req =>
        if req.maxOutputBytes == some 0 then
          .error { kind := .invalidInput, message := "bad limit" }
        else refProcessApi.validateRequest req }) := by
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
    { refProcessApi with
      validateRequest := fun req =>
        if req.args.isEmpty then .ok { req with args := #["extra"] }
        else .error { kind := .invalidInput, message := "not idempotent" } }) := by
  intro h
  have h0 := h { program := "echo" }
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_preservesDirectArgsAndOptions
    { refProcessApi with
      validateRequest := fun req =>
        .ok { req with program := "/bin/sh", args := #["-c", req.program] } }) := by
  intro h
  have h0 := h { program := "echo", args := #["a; rm -rf /"] }
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_envOverride_lastWins
    { refProcessApi with validateRequest := fun req => .ok req }) := by
  intro h
  have h0 := h "echo" "FOO" (some "1") none
    (by decide) (by decide) (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_validateRequest_preservesDistinctEnv
    { refProcessApi with
      validateRequest := fun req =>
        .ok { req with env := req.env.filter (fun kv => kv.2.isSome) } }) := by
  intro h
  have h0 := h "echo" "A" "B" (some "1") none
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_mkCommandRequest_preservesProgramAndArgsVerbatim
    { refProcessApi with
      mkCommandRequest := fun p a => { program := "/bin/sh", args := #["-c", p] ++ a } }) := by
  intro h
  have h0 := h "echo" #["$(id)"]
  simp [assert] at h0

example : ¬ Core.AllPass (test_process_withTextInput_encodesUtf8
    { refProcessApi with
      withTextInput := fun req _ => { req with stdin := ByteArray.empty } }) := by
  intro h
  have h0 := h { program := "cat" } "hi"
  simp [assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_process_run_invalidRequest_doesNotLeak
    { refStatefulApi with
      run := fun _ n => (.error { kind := .invalidInput, message := "bad" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "" }
  dsimp [test_process_run_invalidRequest_doesNotLeak] at h0
  have hVal : refStatefulApi.validateRequest { program := "" } =
      .error { kind := .invalidInput, program := some "", message := "executable program must not be empty" } := rfl
  rw [hVal] at h0
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt
    { refStatefulApi with runChecked := refStatefulApi.run }) := by
  intro h
  have h0 := h 0 { program := "false" }
  have hRun : (refStatefulApi.run { program := "false" }).run 0 =
      (.ok { exitCode := 1, stdout := "hello".toUTF8, stderr := ByteArray.empty }, 0) := by
    decide +kernel
  dsimp only [Core.AllPass, test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt,
    nondet, bind] at h0
  rw [hRun] at h0
  have h1 := h0 (by decide)
  rcases h1.1.1 with ⟨e, hErr, _⟩
  cases hErr

example : ¬ Core.AllPass (test_process_runChecked_zeroExit_matchesRun
    { refStatefulApi with
      runChecked := fun _ => pure (.error { kind := .nonZeroExit, message := "wrong" }) }) := by
  intro h
  have h0 := h 0 { program := "true" }
  have hRun : (refStatefulApi.run { program := "true" }).run 0 =
      (.ok { exitCode := 0, stdout := "hello".toUTF8, stderr := ByteArray.empty }, 0) := by
    decide +kernel
  dsimp only [Core.AllPass, test_process_runChecked_zeroExit_matchesRun,
    nondet, bind] at h0
  rw [hRun] at h0
  have h1 := h0 rfl
  simp [StateT.run, pure, StateT.pure, assert] at h1
  cases congrArg Prod.fst h1

example : ¬ Core.AllPass (test_process_run_neverLeaksProcesses
    { refStatefulApi with
      run := fun _ n => (.error { kind := .timedOut, message := "timed out" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "sleep", timeoutMs := some 10 }
  simp [refStatefulApi, refMkApiM, refRawNatOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, assert] at h0

example : ¬ Core.AllPass (test_process_timeout_cleansUpAndErrors
    { refStatefulApi with
      run := fun req n =>
        (.error { kind := .timedOut, program := some req.program, message := "timed out" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "sleep", timeoutMs := some 10 } (by decide) rfl
  simp [refStatefulApi, refMkApiM, refRawNatOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, assert] at h0

example : ¬ Core.AllPass (test_process_run_noTimeout_neverTimesOut
    { refStatefulApi with
      run := fun req => pure (.error { kind := .timedOut, program := some req.program, message := "timed out" }) }) := by
  intro h
  have h0 := h 0 { program := "echo", timeoutMs := none } rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_outputLimit_cleansUpAndErrors
    { refStatefulApi with
      run := fun req n =>
        (.error { kind := .outputLimitExceeded, program := some req.program, message := "too big" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "yes", maxOutputBytes := some 16 } (by decide) rfl
  simp [refStatefulApi, refMkApiM, refRawNatOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, assert] at h0

example : ¬ Core.AllPass (test_process_run_respectsMaxOutputBytes
    { refStatefulApi with
      run := fun _ =>
        pure (.ok { exitCode := 0, stdout := "exceeded!".toUTF8, stderr := ByteArray.empty }) }) := by
  intro h
  have h0 := h 0 { program := "echo", maxOutputBytes := some 2 } 2 rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_process_run_onError_returnsNonEmptyMessage
    { refStatefulApi with
      run := fun _ => pure (.error { kind := .ioError, message := "" }) }) := by
  intro h
  have h0 := h 0 { program := "bad" }
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_run_usesNormalizedRequest
    { refStatefulApi with
      run := fun req =>
        if req.env.size > 1 then
          pure (.ok { exitCode := 0, stdout := "raw".toUTF8, stderr := ByteArray.empty })
        else
          refStatefulApi.run req }) := by
  intro h
  let req : ExecRequest := { program := "env", env := #[("A", some "1"), ("A", some "2")] }
  have h0 := h 0 req
  have hVal : refStatefulApi.validateRequest req =
      .ok { program := "env", env := #[("A", some "2")] } := by
    decide +kernel
  have hNorm : (refStatefulApi.run { program := "env", env := #[("A", some "2")] }).run 0 =
      (.ok { exitCode := 1, stdout := "hello".toUTF8, stderr := ByteArray.empty }, 0) := by
    decide +kernel
  dsimp only [Core.AllPass, test_process_run_usesNormalizedRequest, nondet, bind] at h0
  rw [hVal] at h0
  dsimp only [req, assert] at h0
  have hEq := h0.1
  simp only [show (#[("A", some "1"), ("A", some "2")] : Array (String × Option String)).size > 1 from by decide,
    ↓reduceIte, show ¬ ((#[("A", some "2")] : Array (String × Option String)).size > 1) from by decide] at hEq
  rw [hNorm] at hEq
  have hSize := congrArg (fun p => match p.1 with | .ok r => r.stdout.size | .error _ => 0) hEq
  exact absurd hSize (by decide)

example : ¬ Core.AllPass (test_process_runCommand_eq_runMkCommandRequest
    { refStatefulApi with
      runCommand := fun _ _ => pure (.error { kind := .ioError, message := "diverged" }) }) := by
  intro h
  have h0 := h 0 "echo" #["hi"]
  have hRun : (refStatefulApi.run (refStatefulApi.mkCommandRequest "echo" #["hi"])).run 0 =
      (.ok { exitCode := 1, stdout := "hello".toUTF8, stderr := ByteArray.empty }, 0) := by
    decide +kernel
  dsimp only [Core.AllPass, test_process_runCommand_eq_runMkCommandRequest, nondet, bind, assert] at h0
  rw [hRun] at h0
  cases h0.1

example : ¬ Core.AllPass (test_process_runCommandChecked_eq_runCheckedMkCommandRequest
    { refStatefulApi with
      runCommandChecked := fun _ _ => pure (.ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }) }) := by
  intro h
  have h0 := h 0 "echo" #["hi"]
  have hChk : ((refStatefulApi.runChecked (refStatefulApi.mkCommandRequest "echo" #["hi"])).run 0).1.isOk = false := by
    decide +kernel
  dsimp only [Core.AllPass, test_process_runCommandChecked_eq_runCheckedMkCommandRequest, nondet, bind, assert] at h0
  have hOk := congrArg (fun p => p.1.isOk) h0.1
  rw [hChk] at hOk
  cases hOk

example : ¬ Core.AllPass (test_process_runChecked_propagatesRunError
    { refStatefulApi with
      runChecked := fun _ => pure (.error { kind := .ioError, message := "changed" }) }) := by
  intro h
  have h0 := h 0 { program := "missing" }
  have hRun : (refStatefulApi.run { program := "missing" }).run 0 =
      (.error (Model.mapRawErrorModel (.executableNotFound "missing" 2 "not found")), 0) := by
    decide +kernel
  dsimp only [Core.AllPass, test_process_runChecked_propagatesRunError, nondet, bind] at h0
  rw [hRun] at h0
  dsimp only [assert, StateT.run, pure, StateT.pure] at h0
  have hKind := congrArg (fun p => match p.1 with | .error e => e.kind | .ok _ => .ioError) h0.1
  exact absurd hKind (by decide)

example : ¬ Core.AllPass (test_process_runChecked_neverLeaksProcesses
    { refStatefulApi with
      runChecked := fun _ n => (.error { kind := .timedOut, message := "timed out" }, n + 1) }) := by
  intro h
  have h0 := h 0 { program := "sleep", timeoutMs := some 10 }
  simp [refStatefulApi, refMkApiM, refRawNatOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get, assert] at h0

example : ¬ Core.AllPass (test_process_run_noOutputLimit_neverExceedsLimit
    { refStatefulApi with
      run := fun req => pure (.error { kind := .outputLimitExceeded, program := some req.program, message := "cap" }) }) := by
  intro h
  have h0 := h 0 { program := "echo", maxOutputBytes := none } rfl
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_runChecked_onError_returnsNonEmptyMessage
    { refStatefulApi with
      runChecked := fun _ => pure (.error { kind := .nonZeroExit, message := "" }) }) := by
  intro h
  have h0 := h 0 { program := "false" }
  simp [StateT.run, pure, StateT.pure, assert] at h0

example : ¬ Core.AllPass (test_process_signaled_cleansUpAndErrors
    { refStatefulApi with
      run := fun req =>
        pure (.error { kind := .terminatedBySignal, program := some req.program, signal := none, message := "killed" }) }) := by
  intro h
  have h0 := h 0 { program := "sleep" } rfl
  simp [StateT.run, assert] at h0

end LeanSwe.Process
