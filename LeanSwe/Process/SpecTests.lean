import Core.NondetTest
import LeanSwe.Process.Types

namespace LeanSwe.Process

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `api.mapRawError` carries a non-empty diagnostic message. -/
def test_process_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let raw ← nondet ProcessRawError
  let err := api.mapRawError raw
  assert (err.message ≠ "")

/-- `api.mapRawError` maps every `ProcessRawError` variant to its exact `ProcessErrorKind` and metadata. -/
def test_process_mapRawError_preservesKindAndFields
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let raw ← nondet ProcessRawError
  let err := api.mapRawError raw
  match raw with
  | .executableNotFound prog errno _ =>
    assert (err.kind = .notFound ∧ err.program = some prog ∧ err.errnoCode = some errno)
  | .permissionDenied prog? errno _ =>
    assert (err.kind = .permissionDenied ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .invalidArgument prog? errno _ =>
    assert (err.kind = .invalidInput ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .timedOut prog _ _ =>
    assert (err.kind = .timedOut ∧ err.program = some prog)
  | .outputLimitExceeded prog _ _ =>
    assert (err.kind = .outputLimitExceeded ∧ err.program = some prog)
  | .signaled prog sig _ =>
    assert (err.kind = .terminatedBySignal ∧ err.program = some prog ∧ err.signal = some sig)
  | .otherError errno _ =>
    assert (err.kind = .ioError ∧ err.errnoCode = some errno)
  | .userError _ =>
    assert (err.kind = .ioError)

/-- `api.validateRequest` rejects an empty `program` with `.invalidInput` and a non-empty message. -/
def test_process_validateRequest_rejectsEmptyProgram
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume (req.program = "")
  match api.validateRequest req with
  | .ok _ => assert False
  | .error err => assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects NUL bytes in `program` with `.invalidInput`. -/
def test_process_validateRequest_rejectsNulInProgram
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume ('\x00' ∈ req.program.toList)
  match api.validateRequest req with
  | .ok _ => assert False
  | .error err => assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects NUL bytes in any argument in `args` with `.invalidInput`. -/
def test_process_validateRequest_rejectsNulInArg
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  let i ← nondet Nat
  assume (i < req.args.size)
  assume ('\x00' ∈ req.args[i]!.toList)
  match api.validateRequest req with
  | .ok _ => assert False
  | .error err => assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects NUL bytes in `cwd` with `.invalidInput`. -/
def test_process_validateRequest_rejectsNulInCwd
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume (∃ d, req.cwd = some d ∧ '\x00' ∈ d.toList)
  match api.validateRequest req with
  | .ok _ => assert False
  | .error err => assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects empty env keys, `'='` in env keys, or NUL bytes in env keys/values. -/
def test_process_validateRequest_rejectsInvalidEnv
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  let i ← nondet Nat
  assume (i < req.env.size)
  let entry := req.env[i]!
  assume (entry.1 = "" ∨ '=' ∈ entry.1.toList ∨ '\x00' ∈ entry.1.toList ∨
    (∃ v, entry.2 = some v ∧ '\x00' ∈ v.toList))
  match api.validateRequest req with
  | .ok _ => assert False
  | .error err => assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects `timeoutMs = some 0` with `.invalidInput`. -/
def test_process_validateRequest_rejectsZeroTimeout
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume (req.timeoutMs = some 0)
  match api.validateRequest req with
  | .ok _ => assert False
  | .error err => assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- Every valid `ExecRequest` (non-empty `program`, no NUL bytes, valid env keys, non-zero timeout) is accepted by `api.validateRequest`. -/
def test_process_validateRequest_acceptsValidRequest
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume (req.program ≠ "" ∧ !req.program.toList.contains '\x00')
  assume (req.args.toList.all (fun a => !a.toList.contains '\x00'))
  assume (match req.cwd with | some d => !d.toList.contains '\x00' | none => true)
  assume (req.env.toList.all (fun kv =>
    kv.1 != "" && !kv.1.toList.contains '=' && !kv.1.toList.contains '\x00' &&
    match kv.2 with | some v => !v.toList.contains '\x00' | none => true))
  assume (req.timeoutMs ≠ some 0)
  match api.validateRequest req with
  | .error _ => assert False
  | .ok _ => assert True

/-- `api.validateRequest` is idempotent on all valid requests. -/
def test_process_validateRequest_idempotent
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  match api.validateRequest req with
  | .error _ => assume False
  | .ok norm => assert (api.validateRequest norm = .ok norm)

/-- `api.validateRequest` preserves `program`, direct `args` (no shell wrapping), `cwd`, `inheritEnv`, `stdin`, and limits. -/
def test_process_validateRequest_preservesDirectArgsAndOptions
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  match api.validateRequest req with
  | .error _ => assume False
  | .ok norm =>
    assert (norm.program = req.program ∧
      norm.args = req.args ∧
      norm.cwd = req.cwd ∧
      norm.inheritEnv = req.inheritEnv ∧
      norm.stdin = req.stdin ∧
      norm.timeoutMs = req.timeoutMs ∧
      norm.maxOutputBytes = req.maxOutputBytes)

/-- Duplicate environment keys `(k, v₁), (k, v₂)` in `req.env` normalize to `[(k, v₂)]` (last-write-wins, including `none` removals). -/
def test_process_validateRequest_envOverride_lastWins
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let prog ← nondet String
  let k ← nondet String
  let v₁ ← nondet (Option String)
  let v₂ ← nondet (Option String)
  assume (prog ≠ "" ∧ !prog.toList.contains '\x00')
  assume (k ≠ "" ∧ !k.toList.contains '=' ∧ !k.toList.contains '\x00')
  assume (match v₁ with | some v => !v.toList.contains '\x00' | none => true)
  assume (match v₂ with | some v => !v.toList.contains '\x00' | none => true)
  let req : ExecRequest := { program := prog, env := #[(k, v₁), (k, v₂)] }
  match api.validateRequest req with
  | .error _ => assert False
  | .ok norm => assert (norm.env = #[(k, v₂)])

/-- Distinct valid environment entries `(k₁, v₁), (k₂, v₂)` (`k₁ ≠ k₂`, including `none` removals) are preserved by `api.validateRequest`. -/
def test_process_validateRequest_preservesDistinctEnv
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let prog ← nondet String
  let k₁ ← nondet String
  let k₂ ← nondet String
  let v₁ ← nondet (Option String)
  let v₂ ← nondet (Option String)
  assume (prog ≠ "" ∧ !prog.toList.contains '\x00')
  assume (k₁ ≠ "" ∧ !k₁.toList.contains '=' ∧ !k₁.toList.contains '\x00')
  assume (k₂ ≠ "" ∧ !k₂.toList.contains '=' ∧ !k₂.toList.contains '\x00')
  assume (k₁ ≠ k₂)
  assume (match v₁ with | some v => !v.toList.contains '\x00' | none => true)
  assume (match v₂ with | some v => !v.toList.contains '\x00' | none => true)
  let req : ExecRequest := { program := prog, env := #[(k₁, v₁), (k₂, v₂)] }
  match api.validateRequest req with
  | .error _ => assert False
  | .ok norm => assert (norm.env = #[(k₁, v₁), (k₂, v₂)])

/-- `api.mkCommandRequest` stores `program` and `args` verbatim (no `/bin/sh -c` wrapping) with clean defaults. -/
def test_process_mkCommandRequest_preservesProgramAndArgsVerbatim
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let program ← nondet String
  let args ← nondet (Array String)
  let req := api.mkCommandRequest program args
  assert (req.program = program ∧
    req.args = args ∧
    req.cwd = none ∧
    req.env = #[] ∧
    req.inheritEnv = true ∧
    req.stdin = ByteArray.empty ∧
    req.timeoutMs = none ∧
    req.maxOutputBytes = none)

/-- `api.withTextInput` UTF-8 encodes `stdin` while preserving all other request fields. -/
def test_process_withTextInput_encodesUtf8
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  let text ← nondet String
  let updated := api.withTextInput req text
  assert (updated.stdin = text.toUTF8 ∧
    updated.program = req.program ∧
    updated.args = req.args ∧
    updated.cwd = req.cwd ∧
    updated.env = req.env ∧
    updated.inheritEnv = req.inheritEnv ∧
    updated.timeoutMs = req.timeoutMs ∧
    updated.maxOutputBytes = req.maxOutputBytes)

/-- Running an invalid request fails with `.invalidInput` without spawning or altering state. -/
def test_process_run_invalidRequest_doesNotLeak
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  match api.validateRequest req with
  | .ok _ => assume False
  | .error _ =>
    let (res, s₁) := (api.run req).run s₀
    assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ s₁ = s₀)

/-- `api.run` behaves identically on `req` and its `validateRequest` normalization. -/
def test_process_run_usesNormalizedRequest
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  match api.validateRequest req with
  | .error _ => assume False
  | .ok norm =>
    assert ((api.run req).run s₀ = (api.run norm).run s₀)

/-- `api.runCommand prog args` matches `api.run (api.mkCommandRequest prog args)`. -/
def test_process_runCommand_eq_runMkCommandRequest
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let prog ← nondet String
  let args ← nondet (Array String)
  assert ((api.runCommand prog args).run s₀ = (api.run (api.mkCommandRequest prog args)).run s₀)

/-- `api.runCommandChecked prog args` matches `api.runChecked (api.mkCommandRequest prog args)`. -/
def test_process_runCommandChecked_eq_runCheckedMkCommandRequest
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let prog ← nondet String
  let args ← nondet (Array String)
  assert ((api.runCommandChecked prog args).run s₀ =
    (api.runChecked (api.mkCommandRequest prog args)).run s₀)

/-- `run` returns `.ok` on non-zero exit codes, whereas `runChecked` returns `.nonZeroExit` with captured outputs. -/
def test_process_run_allowsNonZeroExit_and_runChecked_rejectsIt
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let (res, s₁) := (api.run req).run s₀
  match res with
  | .error _ => assume False
  | .ok out =>
    assume (out.exitCode ≠ 0)
    let (checkedRes, s₂) := (api.runChecked req).run s₀
    assert ((∃ e, checkedRes = .error e ∧
      e.kind = .nonZeroExit ∧
      e.program = some req.program ∧
      e.exitCode = some out.exitCode ∧
      e.stdout = some out.stdout ∧
      e.stderr = some out.stderr ∧
      e.message ≠ "") ∧ s₂ = s₁)

/-- When `run` returns exit code `0`, `runChecked` returns the exact same `.ok` result and state. -/
def test_process_runChecked_zeroExit_matchesRun
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let (res, s₁) := (api.run req).run s₀
  match res with
  | .error _ => assume False
  | .ok out =>
    assume (out.exitCode = 0)
    assert ((api.runChecked req).run s₀ = (.ok out, s₁))

/-- When `run` fails with an error, `runChecked` propagates the exact same error and state. -/
def test_process_runChecked_propagatesRunError
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let (res, s₁) := (api.run req).run s₀
  match res with
  | .ok _ => assume False
  | .error err =>
    assert ((api.runChecked req).run s₀ = (.error err, s₁))

/-- `api.run` preserves `activeProcessCount` across all outcomes. -/
def test_process_run_neverLeaksProcesses
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let n₀ := (api.activeProcessCount.run s₀).1
  let (_, s₁) := (api.run req).run s₀
  let n₁ := (api.activeProcessCount.run s₁).1
  assert (n₁ = n₀)

/-- `api.runChecked` preserves `activeProcessCount` across all outcomes. -/
def test_process_runChecked_neverLeaksProcesses
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let n₀ := (api.activeProcessCount.run s₀).1
  let (_, s₁) := (api.runChecked req).run s₀
  let n₁ := (api.activeProcessCount.run s₁).1
  assert (n₁ = n₀)

/-- When `api.run` returns `.timedOut` on a timed request, it restores `activeProcessCount` and preserves `program` and a non-empty message. -/
def test_process_timeout_cleansUpAndErrors
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  assume (req.timeoutMs ≠ none)
  let n₀ := (api.activeProcessCount.run s₀).1
  let (res, s₁) := (api.run req).run s₀
  match res with
  | .error err =>
    assume (err.kind = .timedOut)
    assert (err.program = some req.program ∧
      err.message ≠ "" ∧
      (api.activeProcessCount.run s₁).1 = n₀)
  | .ok _ => assume False

/-- Commands with `timeoutMs = none` never fail with `.timedOut`. -/
def test_process_run_noTimeout_neverTimesOut
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  assume (req.timeoutMs = none)
  let (res, _) := (api.run req).run s₀
  match res with
  | .ok _ => pure ()
  | .error err => assert (err.kind ≠ .timedOut)

/-- When `api.run` returns `.outputLimitExceeded`, it restores `activeProcessCount` and preserves `program` and a non-empty message. -/
def test_process_outputLimit_cleansUpAndErrors
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  assume (req.maxOutputBytes ≠ none)
  let n₀ := (api.activeProcessCount.run s₀).1
  let (res, s₁) := (api.run req).run s₀
  match res with
  | .error err =>
    assume (err.kind = .outputLimitExceeded)
    assert (err.program = some req.program ∧
      err.message ≠ "" ∧
      (api.activeProcessCount.run s₁).1 = n₀)
  | .ok _ => assume False

/-- Commands with `maxOutputBytes = none` never fail with `.outputLimitExceeded`. -/
def test_process_run_noOutputLimit_neverExceedsLimit
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  assume (req.maxOutputBytes = none)
  let (res, _) := (api.run req).run s₀
  match res with
  | .ok _ => pure ()
  | .error err => assert (err.kind ≠ .outputLimitExceeded)

/-- Every successful `api.run` under `maxOutputBytes = some limit` caps `stdout.size + stderr.size ≤ limit`. -/
def test_process_run_respectsMaxOutputBytes
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let limit ← nondet Nat
  assume (req.maxOutputBytes = some limit)
  let (res, _) := (api.run req).run s₀
  match res with
  | .ok out => assert (out.stdout.size + out.stderr.size ≤ limit)
  | .error _ => assume False

/-- When `api.run` returns `.terminatedBySignal`, it restores `activeProcessCount` and preserves `program`, `signal`, and a non-empty message. -/
def test_process_signaled_cleansUpAndErrors
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let n₀ := (api.activeProcessCount.run s₀).1
  let (res, s₁) := (api.run req).run s₀
  match res with
  | .error err =>
    assume (err.kind = .terminatedBySignal)
    assert (err.program = some req.program ∧
      err.signal ≠ none ∧
      err.message ≠ "" ∧
      (api.activeProcessCount.run s₁).1 = n₀)
  | .ok _ => assume False

/-- Every error returned by `api.run` carries a non-empty diagnostic message. -/
def test_process_run_onError_returnsNonEmptyMessage
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let (res, _) := (api.run req).run s₀
  match res with
  | .ok _ => assume False
  | .error err => assert (err.message ≠ "")

/-- Every error returned by `api.runChecked` carries a non-empty diagnostic message. -/
def test_process_runChecked_onError_returnsNonEmptyMessage
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let (res, _) := (api.runChecked req).run s₀
  match res with
  | .ok _ => assume False
  | .error err => assert (err.message ≠ "")

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

end LeanSwe.Process
