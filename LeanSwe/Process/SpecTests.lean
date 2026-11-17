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
  NondetTest.assert (err.message ≠ "")

/-- `api.mapRawError` maps every `ProcessRawError` variant to its exact `ProcessErrorKind` and metadata. -/
def test_process_mapRawError_preservesKindAndFields
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let raw ← nondet ProcessRawError
  let err := api.mapRawError raw
  match raw with
  | .executableNotFound prog errno _ =>
    NondetTest.assert (err.kind = .notFound ∧ err.program = some prog ∧ err.errnoCode = some errno)
  | .permissionDenied prog? errno _ =>
    NondetTest.assert (err.kind = .permissionDenied ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .invalidArgument prog? errno _ =>
    NondetTest.assert (err.kind = .invalidInput ∧ err.program = prog? ∧ err.errnoCode = some errno)
  | .timedOut prog _ _ =>
    NondetTest.assert (err.kind = .timedOut ∧ err.program = some prog)
  | .outputLimitExceeded prog _ _ =>
    NondetTest.assert (err.kind = .outputLimitExceeded ∧ err.program = some prog)
  | .signaled prog sig _ =>
    NondetTest.assert (err.kind = .terminatedBySignal ∧ err.program = some prog ∧ err.signal = some sig)
  | .otherError errno _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.errnoCode = some errno)
  | .userError _ =>
    NondetTest.assert (err.kind = .ioError)

/-- `api.validateRequest` rejects an empty `program` with `.invalidInput` and a non-empty message. -/
def test_process_validateRequest_rejectsEmptyProgram
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume (req.program = "")
  match api.validateRequest req with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects NUL bytes in `program` with `.invalidInput`. -/
def test_process_validateRequest_rejectsNulInProgram
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume ('\x00' ∈ req.program.toList)
  match api.validateRequest req with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects NUL bytes in any argument in `args` with `.invalidInput`. -/
def test_process_validateRequest_rejectsNulInArg
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  let i ← nondet Nat
  assume (i < req.args.size)
  assume ('\x00' ∈ req.args[i]!.toList)
  match api.validateRequest req with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects NUL bytes in `cwd` with `.invalidInput`. -/
def test_process_validateRequest_rejectsNulInCwd
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume (∃ d, req.cwd = some d ∧ '\x00' ∈ d.toList)
  match api.validateRequest req with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")

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
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")

/-- `api.validateRequest` rejects `timeoutMs = some 0` with `.invalidInput`. -/
def test_process_validateRequest_rejectsZeroTimeout
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  assume (req.timeoutMs = some 0)
  match api.validateRequest req with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")

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
  | .error _ => NondetTest.assert False
  | .ok _ => NondetTest.assert True

/-- `api.validateRequest` is idempotent on all valid requests. -/
def test_process_validateRequest_idempotent
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  match api.validateRequest req with
  | .error _ => assume False
  | .ok norm => NondetTest.assert (api.validateRequest norm = .ok norm)

/-- `api.validateRequest` preserves `program`, direct `args` (no shell wrapping), `cwd`, `inheritEnv`, `stdin`, and limits. -/
def test_process_validateRequest_preservesDirectArgsAndOptions
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let req ← nondet ExecRequest
  match api.validateRequest req with
  | .error _ => assume False
  | .ok norm =>
    NondetTest.assert (norm.program = req.program ∧
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
  | .error _ => NondetTest.assert False
  | .ok norm => NondetTest.assert (norm.env = #[(k, v₂)])

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
  | .error _ => NondetTest.assert False
  | .ok norm => NondetTest.assert (norm.env = #[(k₁, v₁), (k₂, v₂)])

/-- `api.mkCommandRequest` stores `program` and `args` verbatim (no `/bin/sh -c` wrapping) with clean defaults. -/
def test_process_mkCommandRequest_preservesProgramAndArgsVerbatim
    {runner} [NondetTest runner] (api : ProcessApi) : runner Unit := do
  let program ← nondet String
  let args ← nondet (Array String)
  let req := api.mkCommandRequest program args
  NondetTest.assert (req.program = program ∧
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
  NondetTest.assert (updated.stdin = text.toUTF8 ∧
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
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ s₁ = s₀)

/-- `api.run` behaves identically on `req` and its `validateRequest` normalization. -/
def test_process_run_usesNormalizedRequest
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  match api.validateRequest req with
  | .error _ => assume False
  | .ok norm =>
    NondetTest.assert ((api.run req).run s₀ = (api.run norm).run s₀)

/-- `api.runCommand prog args` matches `api.run (api.mkCommandRequest prog args)`. -/
def test_process_runCommand_eq_runMkCommandRequest
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let prog ← nondet String
  let args ← nondet (Array String)
  NondetTest.assert ((api.runCommand prog args).run s₀ = (api.run (api.mkCommandRequest prog args)).run s₀)

/-- `api.runCommandChecked prog args` matches `api.runChecked (api.mkCommandRequest prog args)`. -/
def test_process_runCommandChecked_eq_runCheckedMkCommandRequest
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let prog ← nondet String
  let args ← nondet (Array String)
  NondetTest.assert ((api.runCommandChecked prog args).run s₀ =
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
    NondetTest.assert ((∃ e, checkedRes = .error e ∧
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
    NondetTest.assert ((api.runChecked req).run s₀ = (.ok out, s₁))

/-- When `run` fails with an error, `runChecked` propagates the exact same error and state. -/
def test_process_runChecked_propagatesRunError
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let (res, s₁) := (api.run req).run s₀
  match res with
  | .ok _ => assume False
  | .error err =>
    NondetTest.assert ((api.runChecked req).run s₀ = (.error err, s₁))

/-- `api.run` preserves `activeProcessCount` across all outcomes. -/
def test_process_run_neverLeaksProcesses
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let n₀ := (api.activeProcessCount.run s₀).1
  let (_, s₁) := (api.run req).run s₀
  let n₁ := (api.activeProcessCount.run s₁).1
  NondetTest.assert (n₁ = n₀)

/-- `api.runChecked` preserves `activeProcessCount` across all outcomes. -/
def test_process_runChecked_neverLeaksProcesses
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let n₀ := (api.activeProcessCount.run s₀).1
  let (_, s₁) := (api.runChecked req).run s₀
  let n₁ := (api.activeProcessCount.run s₁).1
  NondetTest.assert (n₁ = n₀)

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
    NondetTest.assert (err.program = some req.program ∧
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
  | .error err => NondetTest.assert (err.kind ≠ .timedOut)

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
    NondetTest.assert (err.program = some req.program ∧
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
  | .error err => NondetTest.assert (err.kind ≠ .outputLimitExceeded)

/-- Every successful `api.run` under `maxOutputBytes = some limit` caps `stdout.size + stderr.size ≤ limit`. -/
def test_process_run_respectsMaxOutputBytes
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let limit ← nondet Nat
  assume (req.maxOutputBytes = some limit)
  let (res, _) := (api.run req).run s₀
  match res with
  | .ok out => NondetTest.assert (out.stdout.size + out.stderr.size ≤ limit)
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
    NondetTest.assert (err.program = some req.program ∧
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
  | .error err => NondetTest.assert (err.message ≠ "")

/-- Every error returned by `api.runChecked` carries a non-empty diagnostic message. -/
def test_process_runChecked_onError_returnsNonEmptyMessage
    {S : Type} {runner} [NondetTest runner] (api : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet ExecRequest
  let (res, _) := (api.runChecked req).run s₀
  match res with
  | .ok _ => assume False
  | .error err => NondetTest.assert (err.message ≠ "")

end LeanSwe.Process
