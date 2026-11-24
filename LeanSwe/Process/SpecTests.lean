import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.PostFork.Types
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal

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

/-- State recorded while probing candidate `PATH` entries in `resolveExecutablePath`. -/
structure PathProbeState where
  /-- Ordered list of filesystem path bytes passed to `fstatat`. -/
  probedPaths : Array ByteArray := #[]
  /-- Remaining `EINTR` budget injected before `fstatat` succeeds or fails. -/
  eintrBudget : Nat := 0

/-- Deterministic `FilesOpsM` fixture recording `fstatat` probes and serving directory vs executable entries. -/
def mkPathProbeFilesOps : LinuxSyscall.Files.FilesOpsM (StateM PathProbeState) Nat where
  openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
  openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
  close := fun _ => pure (.ok ())
  read := fun _ _ => pure (.ok ByteArray.empty)
  write := fun _ _ => pure (.ok 0)
  fstat := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
  fstatat := fun _ path _ => modifyGet fun s =>
    if s.eintrBudget > 0 then
      (.error LinuxSyscall.Errno.EINTR, { s with eintrBudget := s.eintrBudget - 1 })
    else
      let s' := { s with probedPaths := s.probedPaths.push path }
      if path == "/work/sub/dirbin/mytool".toUTF8 || path == "/work/admindir".toUTF8 then
        (.ok { kind := .dir, size := 0, mode := 0o755, ino := 10, dev := 1, nlink := 2,
               mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }, s')
      else if path == "/work/okdir".toUTF8 then
        (.ok { kind := .dir, size := 0, mode := 0o755, ino := 12, dev := 1, nlink := 2,
               mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }, s')
      else if path == "/work/sub/fifobin/mytool".toUTF8 then
        (.ok { kind := .fifo, size := 0, mode := 0o755, ino := 13, dev := 1, nlink := 1,
               mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }, s')
      else if path == "/work/sub/relbin/mytool".toUTF8 || path == "/usr/bin/systool".toUTF8 then
        (.ok { kind := .reg, size := 64, mode := 0o755, ino := 11, dev := 1, nlink := 1,
               mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 }, s')
      else
        (.error LinuxSyscall.Errno.ENOENT, s')
  faccessat := fun _ path mask flags => modifyGet fun s =>
    if (path == "/work/sub/relbin/mytool".toUTF8 ||
        path == "/usr/bin/systool".toUTF8 ||
        path == "/work/sub/fifobin/mytool".toUTF8 ||
        path == "/work/okdir".toUTF8) &&
        mask.exec && flags.eaccess then
      (.ok (), s)
    else
      (.error LinuxSyscall.Errno.EACCES, s)
  mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
  getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
  fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
  flock := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
  fcntl := fun _ _ => pure (.ok 0)
  fsync := fun _ => pure (.ok ())
  getcwd := fun _ => pure (.ok "/".toUTF8)
  lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ESPIPE)
  reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
  dupStdio := fun _ => pure (.error LinuxSyscall.Errno.EBADF)

/-- `SysBridge.resolveExecutablePath` bypasses `PATH` when `'/' ∈ program`, maps empty `PATH` segments (`""`, `:/usr/bin`, `/usr/bin:`, `a::b`) to `"."` per POSIX `execvp(3)`, prepends `cwd` for relative `PATH` entries (retrying `EINTR` and skipping non-regular directories/FIFOs) while returning a child-CWD-relative `execve` path, and probes absolute `PATH` entries directly. -/
def test_process_sysBridge_resolveExecutablePath_relativeCwdAndPathRules
    {runner} [NondetTest runner]
    (resolveFn :
      LinuxSyscall.Files.FilesOpsM (StateM PathProbeState) Nat →
      String → Option String → Array ByteArray → Nat →
      StateM PathProbeState (Except ProcessError String)) : runner Unit := do
  let rSlash :=
    (resolveFn mkPathProbeFilesOps "sub/mytool" (some "/work/sub") #["PATH=/usr/bin".toUTF8] 2).run {}
  let rEmpty :=
    (resolveFn mkPathProbeFilesOps "mytool" (some "/work/sub") #["PATH=".toUTF8] 2).run {}
  let rRel :=
    (resolveFn mkPathProbeFilesOps "mytool" (some "/work/sub")
      #["PATH=dirbin:fifobin:relbin:/usr/bin".toUTF8] 2).run { eintrBudget := 1 }
  let rSoleFifo :=
    (resolveFn mkPathProbeFilesOps "mytool" (some "/work/sub") #["PATH=fifobin".toUTF8] 2).run {}
  let rAbs :=
    (resolveFn mkPathProbeFilesOps "systool" (some "/work/sub") #["PATH=/usr/bin".toUTF8] 2).run {}
  let rColon :=
    (resolveFn mkPathProbeFilesOps "systool" (some "/work/sub") #["PATH=:/usr/bin".toUTF8] 2).run {}
  let emptyOk : Bool := match rEmpty.1 with
    | .error err => err.kind == .notFound && err.program == some "mytool"
    | .ok _ => false
  let fifoPermOk : Bool := match rSoleFifo.1 with
    | .error err => err.kind == .permissionDenied && err.program == some "mytool"
    | .ok _ => false
  let slashOk : Bool := match rSlash.1 with | .ok p => p == "sub/mytool" | .error _ => false
  let relOk : Bool := match rRel.1 with | .ok p => p == "relbin/mytool" | .error _ => false
  let absOk : Bool := match rAbs.1 with | .ok p => p == "/usr/bin/systool" | .error _ => false
  let colonOk : Bool := match rColon.1 with | .ok p => p == "/usr/bin/systool" | .error _ => false
  NondetTest.assert (
    slashOk = true ∧
    rSlash.2.probedPaths = #[] ∧
    emptyOk = true ∧
    rEmpty.2.probedPaths = #["/work/sub/./mytool".toUTF8] ∧
    relOk = true ∧
    rRel.2.probedPaths = #[
      "/work/sub/dirbin/mytool".toUTF8,
      "/work/sub/fifobin/mytool".toUTF8,
      "/work/sub/relbin/mytool".toUTF8] ∧
    fifoPermOk = true ∧
    absOk = true ∧
    rAbs.2.probedPaths = #["/usr/bin/systool".toUTF8] ∧
    colonOk = true ∧
    rColon.2.probedPaths = #["/work/sub/./systool".toUTF8, "/usr/bin/systool".toUTF8])

/-- `SysBridge.validateWorkingDir` accepts `none` and accessible directories while rejecting empty `""` (`ENOENT` without root probing), regular files (`ENOTDIR`), and non-searchable directories (`EACCES`) with `program` attributed to `cwd`. -/
def test_process_sysBridge_validateWorkingDir_chdirSemantics
    {runner} [NondetTest runner]
    (probePathBytesFn : Option String → String → String → ByteArray)
    (validateCwdFn :
      LinuxSyscall.Files.FilesOpsM (StateM PathProbeState) Nat →
      Option String → Nat →
      StateM PathProbeState (Except ProcessError Unit)) : runner Unit := do
  let rNone := (validateCwdFn mkPathProbeFilesOps none 2).run {}
  let rEmpty := (validateCwdFn mkPathProbeFilesOps (some "") 2).run {}
  let rNotDir := (validateCwdFn mkPathProbeFilesOps (some "/usr/bin/systool") 2).run {}
  let rNoPerm := (validateCwdFn mkPathProbeFilesOps (some "/work/admindir") 2).run {}
  let rOk := (validateCwdFn mkPathProbeFilesOps (some "/work/okdir") 2).run { eintrBudget := 1 }
  let emptyOk : Bool := match rEmpty.1 with
    | .error e => e.kind == .notFound && e.program == some ""
    | .ok () => false
  let notDirOk : Bool := match rNotDir.1 with
    | .error e =>
      e.kind == .ioError && e.errnoCode == some LinuxSyscall.Errno.ENOTDIR &&
      e.program == some "/usr/bin/systool"
    | .ok () => false
  let noPermOk : Bool := match rNoPerm.1 with
    | .error e => e.kind == .permissionDenied && e.program == some "/work/admindir"
    | .ok () => false
  NondetTest.assert (
    rNone.1.isOk = true ∧
    rNone.2.probedPaths = #[] ∧
    emptyOk = true ∧
    rEmpty.2.probedPaths = #[] ∧
    notDirOk = true ∧
    noPermOk = true ∧
    rOk.1.isOk = true ∧
    probePathBytesFn (some "") "relbin" "mytool" = "relbin/mytool".toUTF8)

/-- State scripted across non-blocking `stdin` / `stdout` / `stderr` pipe I/O steps. -/
structure PipeScriptState where
  /-- Currently open descriptor table (`11` = stdin, `12` = stdout, `14` = stderr, `99` = ambient FD). -/
  openFds : List Nat := [11, 12, 14, 99]
  /-- Cumulative bytes accepted on `stdin` (`11`). -/
  writtenStdin : ByteArray := ByteArray.empty
  /-- Script cursor for `stdin` writes. -/
  writeStep : Nat := 0
  /-- Script cursor for `stdout` reads. -/
  outStep : Nat := 0
  /-- Script cursor for `stderr` reads. -/
  errStep : Nat := 0
  /-- Count of `ppoll` waits issued during pipe streaming. -/
  pollCount : Nat := 0

/-- Scripted `FilesOpsM` injecting `EINTR`, short `write`/`read` chunks, and `EAGAIN` across all 3 parent pipes. -/
def mkPipeScriptFilesOps : LinuxSyscall.Files.FilesOpsM (StateM PipeScriptState) Nat where
  openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
  openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
  close := fun fd => modifyGet fun s =>
    if fd ∈ s.openFds then
      (.ok (), { s with openFds := s.openFds.erase fd })
    else
      (.error LinuxSyscall.Errno.EBADF, s)
  write := fun fd data => modifyGet fun s =>
    if fd == 11 && 11 ∈ s.openFds then
      match s.writeStep with
      | 0 => (.error LinuxSyscall.Errno.EINTR, { s with writeStep := 1 })
      | 1 =>
        let n := Nat.min 2 data.size
        (.ok (UInt32.ofNat n),
         { s with writtenStdin := s.writtenStdin ++ data.extract 0 n, writeStep := 2 })
      | 2 => (.error LinuxSyscall.Errno.EAGAIN, { s with writeStep := 3 })
      | _ =>
        (.ok (UInt32.ofNat data.size),
         { s with writtenStdin := s.writtenStdin ++ data, writeStep := s.writeStep + 1 })
    else
      (.error LinuxSyscall.Errno.EBADF, s)
  read := fun fd _ => modifyGet fun s =>
    if fd == 12 && 12 ∈ s.openFds then
      match s.outStep with
      | 0 => (.error LinuxSyscall.Errno.EINTR, { s with outStep := 1 })
      | 1 => (.ok "abc".toUTF8, { s with outStep := 2 })
      | 2 => (.error LinuxSyscall.Errno.EAGAIN, { s with outStep := 3 })
      | 3 => (.error LinuxSyscall.Errno.EAGAIN, { s with outStep := 4 })
      | 4 => (.error LinuxSyscall.Errno.EAGAIN, { s with outStep := 5 })
      | 5 => (.ok "def".toUTF8, { s with outStep := 6 })
      | _ => (.ok ByteArray.empty, { s with outStep := s.outStep + 1 })
    else if fd == 14 && 14 ∈ s.openFds then
      match s.errStep with
      | 0 => (.error LinuxSyscall.Errno.EAGAIN, { s with errStep := 1 })
      | 1 => (.error LinuxSyscall.Errno.EAGAIN, { s with errStep := 2 })
      | 2 => (.error LinuxSyscall.Errno.EAGAIN, { s with errStep := 3 })
      | 3 => (.ok "xy".toUTF8, { s with errStep := 4 })
      | 4 => (.error LinuxSyscall.Errno.EINTR, { s with errStep := 5 })
      | 5 => (.ok "!".toUTF8, { s with errStep := 6 })
      | _ => (.ok ByteArray.empty, { s with errStep := s.errStep + 1 })
    else
      (.error LinuxSyscall.Errno.EBADF, s)
  fstat := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
  fstatat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
  faccessat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
  getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
  fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
  fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
  flock := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
  fcntl := fun _ _ => pure (.ok 0)
  fsync := fun _ => pure (.ok ())
  getcwd := fun _ => pure (.ok "/".toUTF8)
  lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ESPIPE)
  reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
  dupStdio := fun _ => pure (.error LinuxSyscall.Errno.EBADF)

/-- Scripted `PollOpsM` injecting one `EINTR` retry and reporting requested readiness events while counting `ppoll` calls. -/
def mkPipeScriptPollOps : LinuxSyscall.Poll.PollOpsM (StateM PipeScriptState) Nat where
  ppoll := fun entries _ => modifyGet fun s =>
    if s.pollCount == 0 then
      (.error LinuxSyscall.Errno.EINTR, { s with pollCount := 1 })
    else
      (.ok (entries.map Prod.snd), { s with pollCount := s.pollCount + 1 })
  eventfd2 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)

/-- Scripted `TimeRandOpsM` fixture for deterministic `streamPipesLoop` specs. -/
def mkPipeScriptTimeOps : LinuxSyscall.TimeRand.TimeRandOpsM (StateM PipeScriptState) where
  clock_gettime := fun _ => pure (.ok { sec := 0, nsec := 0 })
  clock_nanosleep := fun _ _ _ => pure (.ok ())
  getrandom := fun _ _ => pure (.ok ByteArray.empty)

/-- `SysBridge.streamPipesLoop` reassembles `stdin`, `stdout`, and `stderr` losslessly across `ppoll` `EINTR`, short `write`/`read` chunks, `EAGAIN`, and `EINTR` retries while closing all 3 parent pipe FDs and preserving ambient FDs. -/
def test_process_sysBridge_streamPipes_shortReadWriteEagainEintrReassembly
    {runner} [NondetTest runner]
    (streamFn :
      LinuxSyscall.Files.FilesOpsM (StateM PipeScriptState) Nat →
      LinuxSyscall.Poll.PollOpsM (StateM PipeScriptState) Nat →
      LinuxSyscall.TimeRand.TimeRandOpsM (StateM PipeScriptState) →
      ByteArray → Nat → Option Nat → Option Nat → Nat →
      Internal.StreamLoopState Nat → Nat →
      StateM PipeScriptState (Except ProcessError Internal.StreamPhaseOutcome)) : runner Unit := do
  let initLoop : Internal.StreamLoopState Nat :=
    { inFd? := some 11, outFd? := some 12, errFd? := some 14 }
  let r :=
    (streamFn mkPipeScriptFilesOps mkPipeScriptPollOps mkPipeScriptTimeOps "hello".toUTF8 0 none none 4 initLoop 10).run {}
  let resOk : Bool := match r.1 with
    | .ok out => out == .eof "abcdef".toUTF8 "xy!".toUTF8
    | .error _ => false
  NondetTest.assert (
    resOk = true ∧
    r.2.writtenStdin = "hello".toUTF8 ∧
    r.2.openFds = [99] ∧
    r.2.pollCount ≥ 2)

/-- `SysBridge.streamPipesLoop` finishes writing remaining `stdin` bytes across `EAGAIN` even after child `stdout` and `stderr` pipes have already reached `EOF`. -/
def test_process_sysBridge_streamPipes_drainsStdinAfterOutErrEof
    {runner} [NondetTest runner]
    (streamFn :
      LinuxSyscall.Files.FilesOpsM (StateM PipeScriptState) Nat →
      LinuxSyscall.Poll.PollOpsM (StateM PipeScriptState) Nat →
      LinuxSyscall.TimeRand.TimeRandOpsM (StateM PipeScriptState) →
      ByteArray → Nat → Option Nat → Option Nat → Nat →
      Internal.StreamLoopState Nat → Nat →
      StateM PipeScriptState (Except ProcessError Internal.StreamPhaseOutcome)) : runner Unit := do
  let initLoop : Internal.StreamLoopState Nat :=
    { inFd? := some 11, outFd? := some 12, errFd? := some 14 }
  let r :=
    (streamFn mkPipeScriptFilesOps mkPipeScriptPollOps mkPipeScriptTimeOps "hello".toUTF8 0 none none 4 initLoop 10).run
      { outStep := 6, errStep := 6 }
  let resOk : Bool := match r.1 with
    | .ok out => out == .eof ByteArray.empty ByteArray.empty
    | .error _ => false
  NondetTest.assert (
    resOk = true ∧
    r.2.writtenStdin = "hello".toUTF8 ∧
    r.2.openFds = [99])

/-- Simulation state for `maxOutputBytes` truncation, process-group kill, reap, and FD conservation. -/
structure CapSimState where
  /-- Active `SysBridge` process slot table. -/
  tbl : Internal.ProcTableState Nat := {}
  /-- Next fresh pipe handle ID. -/
  nextFd : Nat := 10
  /-- Currently open OS descriptors (`[3, 4]` ambient). -/
  openFds : List Nat := [3, 4]
  /-- Recorded parent `stdout` read pipe FD. -/
  outReadFd : Nat := 0
  /-- Whether oversized `stdout` chunk has been emitted. -/
  outSent : Bool := false
  /-- Whether simulated child process group `42` is still alive. -/
  groupAlive : Bool := true
  /-- Sequence of `(target, sig)` calls sent to `kill`. -/
  killedTargets : Array (Int32 × LinuxSyscall.Process.Signal) := #[]
  /-- Sequence of `pid`s passed to `waitpid`. -/
  reapedPids : Array Int32 := #[]

/-- Deterministic `SysDepsM` fixture where child `pid = 42, pgid = 42` emits `10` bytes against a `4`-byte limit. -/
def mkCapSimDeps : Internal.SysDepsM (StateM CapSimState) Nat where
  proc :=
    { pipe2 := fun _ => modifyGet fun s =>
        let r := s.nextFd
        let w := s.nextFd + 1
        (.ok (r, w), { s with nextFd := s.nextFd + 2, openFds := w :: r :: s.openFds })
      waitpid := fun pid _ => modifyGet fun s =>
        (.ok (.signaled 42 9 false),
         { s with groupAlive := false, reapedPids := s.reapedPids.push pid })
      kill := fun target sig => modifyGet fun s =>
        let killed' :=
          if sig == .sigzero then s.killedTargets else s.killedTargets.push (target, sig)
        if sig == .sigkill then
          (.ok (), { s with groupAlive := false, killedTargets := killed' })
        else if sig == .sigzero && !s.groupAlive then
          (.error LinuxSyscall.Errno.ESRCH, { s with killedTargets := killed' })
        else
          (.ok (), { s with killedTargets := killed' })
      pidfd_open := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
      pidfd_send_signal := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
      getpid := pure (.ok 1)
      getuid := pure (.ok 1000) }
  files :=
    { openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      close := fun fd => modifyGet fun s =>
        if fd ∈ s.openFds then
          (.ok (), { s with openFds := s.openFds.erase fd })
        else
          (.error LinuxSyscall.Errno.EBADF, s)
      read := fun fd _ => modifyGet fun s =>
        if fd == s.outReadFd && !s.outSent then
          (.ok "0123456789".toUTF8, { s with outSent := true })
        else
          (.ok ByteArray.empty, s)
      write := fun _ data => pure (.ok (UInt32.ofNat data.size))
      fstat := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      fstatat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      faccessat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      flock := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fcntl := fun _ _ => pure (.ok 0)
      fsync := fun _ => pure (.ok ())
      getcwd := fun _ => pure (.ok "/".toUTF8)
      lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ESPIPE)
      reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      dupStdio := fun _ => pure (.error LinuxSyscall.Errno.EBADF) }
  poll :=
    { ppoll := fun entries _ => pure (.ok (entries.map Prod.snd))
      eventfd2 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
  timeRand :=
    { clock_gettime := fun _ => pure (.ok { sec := 0, nsec := 0 })
      clock_nanosleep := fun _ _ _ => pure (.ok ())
      getrandom := fun _ _ => pure (.ok ByteArray.empty) }
  postFork :=
    { spawn := fun spec => modifyGet fun s =>
        let outR := match spec.stdio with
          | .redirect _ (.handle outW) _ _ => outW - 1
          | _ => 0
        (.ok { pid := 42, pgid := some 42 }, { s with outReadFd := outR })
      spawnWithBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      releaseBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      abortBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" }) }
  listAmbientEnv := pure (.ok #["PATH=/bin".toUTF8])

/-- On `maxOutputBytes = some 4`, `SysBridge.mkRawOpsM` truncates captured output to `4` bytes, sends `SIGTERM` and `SIGKILL` to `-pgid` (`-42`), reaps `pid = 42`, restores `activeProcessCount = 0`, and conserves ambient `openFds = [3, 4]` with zero leaked pipe FDs. -/
def test_process_sysBridge_maxOutputBytes_truncatesKillsAndReaps
    {runner} [NondetTest runner]
    (stateTblFn :
      (CapSimState → Internal.ProcTableState Nat) →
      (CapSimState → Internal.ProcTableState Nat → CapSimState) →
      Internal.ProcTableOpsM (StateM CapSimState) Nat)
    (mkRawFn :
      Internal.SysDepsM (StateM CapSimState) Nat →
      Internal.ProcTableOpsM (StateM CapSimState) Nat →
      Nat → Nat →
      RawProcessOpsM (StateM CapSimState)) : runner Unit := do
  let ops :=
    mkRawFn mkCapSimDeps (stateTblFn (·.tbl) (fun s t => { s with tbl := t })) 2 4
  let prog : StateM CapSimState (Bool × Nat) := do
    match ← ops.spawn { program := "/bin/big", inheritEnv := false } with
    | .error _ => return (false, 99)
    | .ok h =>
      let aw ← ops.awaitOutput h ByteArray.empty none (some 4)
      let kg ← ops.killProcessGroup h
      let rp ← ops.reap h
      let cnt ← ops.activeProcessCount
      let okAw := match aw with
        | .ok out => out == .outputLimitExceeded "0123".toUTF8 ByteArray.empty
        | .error _ => false
      return (okAw && kg.isOk && rp.isOk, cnt)
  let r := prog.run {}
  NondetTest.assert (
    r.1.1 = true ∧
    r.1.2 = 0 ∧
    ((-42 : Int32), LinuxSyscall.Process.Signal.sigterm) ∈ r.2.killedTargets.toList ∧
    ((-42 : Int32), LinuxSyscall.Process.Signal.sigkill) ∈ r.2.killedTargets.toList ∧
    (42 : Int32) ∈ r.2.reapedPids.toList ∧
    r.2.openFds = [3, 4])

/-- Simulation state for partial `pipe2` `EMFILE` failures on the 2nd or 3rd pipe pair in `spawnPure`. -/
structure PipeFailSimState where
  /-- Active `SysBridge` process slot table. -/
  tbl : Internal.ProcTableState Nat := {}
  /-- Number of `pipe2` calls allowed to succeed before failing with `EMFILE`. -/
  pipeBudget : Nat := 1
  /-- Next fresh pipe handle ID. -/
  nextFd : Nat := 10
  /-- Currently open OS descriptors (`[5]` ambient). -/
  openFds : List Nat := [5]
  /-- Whether `postFork.spawn` was invoked despite `pipe2` failure. -/
  postForkCalled : Bool := false

/-- Deterministic `SysDepsM` fixture failing `pipe2` with `Errno.EMFILE` once `pipeBudget` reaches `0`. -/
def mkPipeFailSimDeps : Internal.SysDepsM (StateM PipeFailSimState) Nat where
  proc :=
    { pipe2 := fun _ => modifyGet fun s =>
        if s.pipeBudget == 0 then
          (.error LinuxSyscall.Errno.EMFILE, s)
        else
          let r := s.nextFd
          let w := s.nextFd + 1
          (.ok (r, w),
           { s with pipeBudget := s.pipeBudget - 1, nextFd := s.nextFd + 2, openFds := w :: r :: s.openFds })
      waitpid := fun _ _ => pure (.error LinuxSyscall.Errno.ECHILD)
      kill := fun _ _ => pure (.ok ())
      pidfd_open := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
      pidfd_send_signal := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
      getpid := pure (.ok 1)
      getuid := pure (.ok 1000) }
  files :=
    { openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      close := fun fd => modifyGet fun s =>
        if fd ∈ s.openFds then
          (.ok (), { s with openFds := s.openFds.erase fd })
        else
          (.error LinuxSyscall.Errno.EBADF, s)
      read := fun _ _ => pure (.ok ByteArray.empty)
      write := fun _ _ => pure (.ok 0)
      fstat := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      fstatat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      faccessat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      flock := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fcntl := fun _ _ => pure (.ok 0)
      fsync := fun _ => pure (.ok ())
      getcwd := fun _ => pure (.ok "/".toUTF8)
      lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ESPIPE)
      reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      dupStdio := fun _ => pure (.error LinuxSyscall.Errno.EBADF) }
  poll :=
    { ppoll := fun entries _ => pure (.ok (entries.map Prod.snd))
      eventfd2 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
  timeRand :=
    { clock_gettime := fun _ => pure (.ok { sec := 0, nsec := 0 })
      clock_nanosleep := fun _ _ _ => pure (.ok ())
      getrandom := fun _ _ => pure (.ok ByteArray.empty) }
  postFork :=
    { spawn := fun _ => modifyGet fun s =>
        (.ok { pid := 50, pgid := some 50 }, { s with postForkCalled := true })
      spawnWithBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      releaseBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      abortBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" }) }
  listAmbientEnv := pure (.ok #["PATH=/bin".toUTF8])

/-- When `pipe2` fails with `EMFILE` on either the 2nd or 3rd pipe pair, `SysBridge.spawnPure` closes every previously allocated pipe FD, never calls `postFork.spawn`, inserts no process-table slot, and conserves ambient `openFds = [5]`. -/
def test_process_sysBridge_partialPipe2Failure_cleansUpAllocatedFds
    {runner} [NondetTest runner]
    (stateTblFn :
      (PipeFailSimState → Internal.ProcTableState Nat) →
      (PipeFailSimState → Internal.ProcTableState Nat → PipeFailSimState) →
      Internal.ProcTableOpsM (StateM PipeFailSimState) Nat)
    (spawnFn :
      Internal.SysDepsM (StateM PipeFailSimState) Nat →
      Internal.ProcTableOpsM (StateM PipeFailSimState) Nat →
      Nat → ExecRequest →
      StateM PipeFailSimState (Except ProcessError ProcessHandle)) : runner Unit := do
  let tblOps := stateTblFn (fun (s : PipeFailSimState) => s.tbl) (fun s t => { s with tbl := t })
  let req : ExecRequest := { program := "/bin/true", inheritEnv := false }
  let r1 := (spawnFn mkPipeFailSimDeps tblOps 2 req).run { pipeBudget := 1 }
  let r2 := (spawnFn mkPipeFailSimDeps tblOps 2 req).run { pipeBudget := 2 }
  let err1Ok : Bool := match r1.1 with
    | .error err =>
      err.kind == .ioError && err.errnoCode == some LinuxSyscall.Errno.EMFILE && err.program == some "/bin/true"
    | .ok _ => false
  let err2Ok : Bool := match r2.1 with
    | .error err =>
      err.kind == .ioError && err.errnoCode == some LinuxSyscall.Errno.EMFILE && err.program == some "/bin/true"
    | .ok _ => false
  NondetTest.assert (
    err1Ok = true ∧
    r1.2.postForkCalled = false ∧
    r1.2.tbl.slots.isEmpty = true ∧
    r1.2.openFds = [5] ∧
    err2Ok = true ∧
    r2.2.postForkCalled = false ∧
    r2.2.tbl.slots.isEmpty = true ∧
    r2.2.openFds = [5])

/-- Scripted `RawProcessOpsM` state exercising exact `ExecResult` and `ProcessError` payload preservation across all 4 `ExecOutcome` variants. -/
structure OutcomeScriptState where
  /-- Active unreaped process count. -/
  active : Nat := 0
  /-- Script selector (`0` = exit `0`, `1` = exit `7`, `2` = signaled `15`, `3` = timedOut, `4` = outputLimitExceeded). -/
  mode : Nat := 0
  /-- Count of `killProcessGroup` invocations. -/
  killed : Nat := 0
  /-- Count of `reap` invocations. -/
  reaped : Nat := 0

/-- Deterministic `RawProcessOpsM` fixture returning distinct equal-length `stdout`/`stderr` payloads across every `ExecOutcome` constructor. -/
def mkOutcomeScriptRawOps :
    RawProcessOpsM (StateM OutcomeScriptState) where
  mapRawError := fun _ => { kind := .ioError, message := "err" }
  spawn := fun _ => modifyGet fun s =>
    (.ok { handleId := 1, pid := 77, pgid := 77 }, { s with active := s.active + 1 })
  awaitOutput := fun _ _ _ _ => do
    let s ← get
    match s.mode with
    | 0 => pure (.ok (.exited { exitCode := 0, stdout := "OUT0".toUTF8, stderr := "ERR0".toUTF8 }))
    | 1 => pure (.ok (.exited { exitCode := 7, stdout := "OUT7".toUTF8, stderr := "ERR7".toUTF8 }))
    | 2 => pure (.ok (.signaled 15 "SOUT".toUTF8 "SERR".toUTF8))
    | 3 => pure (.ok (.timedOut "TOUT".toUTF8 "TERR".toUTF8))
    | _ => pure (.ok (.outputLimitExceeded "LOUT".toUTF8 "LERR".toUTF8))
  killProcessGroup := fun _ => modifyGet fun s => (.ok (), { s with killed := s.killed + 1 })
  reap := fun _ => modifyGet fun s =>
    (.ok (), { s with active := s.active - 1, reaped := s.reaped + 1 })
  activeProcessCount := do return (← get).active

/-- `Process.Internal.mkApiM` preserves exact `ExecResult` (`exitCode`, `stdout`, `stderr`) on `.exited`, exact `signal` and captured `stdout`/`stderr` on `.signaled`, and exact captured `stdout`/`stderr` on `.timedOut` and `.outputLimitExceeded` while killing and reaping cleanly. -/
def test_process_mkApiM_preservesExactAwaitOutcomes
    {runner} [NondetTest runner]
    (mkApiFn :
      RawProcessOpsM (StateM OutcomeScriptState) →
      ProcessApiM (StateM OutcomeScriptState)) : runner Unit := do
  let api := mkApiFn mkOutcomeScriptRawOps
  let req : ExecRequest := { program := "/bin/demo", timeoutMs := some 50, maxOutputBytes := some 16 }
  let r0 := (api.run req).run { mode := 0 }
  let rc0 := (api.runChecked req).run { mode := 0 }
  let r1 := (api.run req).run { mode := 1 }
  let rc1 := (api.runChecked req).run { mode := 1 }
  let r2 := (api.run req).run { mode := 2 }
  let r3 := (api.run req).run { mode := 3 }
  let r4 := (api.run req).run { mode := 4 }
  let ok0 : Bool := match r0.1, rc0.1 with
    | .ok a, .ok b =>
      a == { exitCode := 0, stdout := "OUT0".toUTF8, stderr := "ERR0".toUTF8 } && a == b &&
      r0.2.active == 0 && r0.2.killed == 0 && r0.2.reaped == 1
    | _, _ => false
  let ok1 : Bool := match r1.1, rc1.1 with
    | .ok a, .error e =>
      a == { exitCode := 7, stdout := "OUT7".toUTF8, stderr := "ERR7".toUTF8 } &&
      e.kind == .nonZeroExit && e.exitCode == some 7 &&
      e.stdout == some "OUT7".toUTF8 && e.stderr == some "ERR7".toUTF8 &&
      rc1.2.active == 0 && rc1.2.killed == 0 && rc1.2.reaped == 1
    | _, _ => false
  let ok2 : Bool := match r2.1 with
    | .error e =>
      e.kind == .terminatedBySignal && e.program == some "/bin/demo" &&
      e.signal == some 15 && e.stdout == some "SOUT".toUTF8 && e.stderr == some "SERR".toUTF8 &&
      r2.2.active == 0 && r2.2.killed == 1 && r2.2.reaped == 1
    | .ok _ => false
  let ok3 : Bool := match r3.1 with
    | .error e =>
      e.kind == .timedOut && e.program == some "/bin/demo" &&
      e.stdout == some "TOUT".toUTF8 && e.stderr == some "TERR".toUTF8 &&
      r3.2.active == 0 && r3.2.killed == 1 && r3.2.reaped == 1
    | .ok _ => false
  let ok4 : Bool := match r4.1 with
    | .error e =>
      e.kind == .outputLimitExceeded && e.program == some "/bin/demo" &&
      e.stdout == some "LOUT".toUTF8 && e.stderr == some "LERR".toUTF8 &&
      r4.2.active == 0 && r4.2.killed == 1 && r4.2.reaped == 1
    | .ok _ => false
  NondetTest.assert (ok0 = true ∧ ok1 = true ∧ ok2 = true ∧ ok3 = true ∧ ok4 = true)

/-- Simulation state auditing pre-`PATH` `cwd` validation, `ChildSpecM` isolation fields, `O_CLOEXEC`/`O_NONBLOCK` pipe setup, `pgid = 1` safe `kill` targeting, and `.chdir` error attribution. -/
structure SpawnAuditState where
  /-- Active `SysBridge` process slot table. -/
  tbl : Internal.ProcTableState Nat := {}
  /-- Next fresh pipe handle ID. -/
  nextFd : Nat := 20
  /-- Currently open OS descriptors (`[7]` ambient). -/
  openFds : List Nat := [7]
  /-- Whether every `pipe2` call set `cloexec = true`. -/
  allPipeCloexec : Bool := true
  /-- Descriptors configured with `O_NONBLOCK` via `fcntl (.setFl true false)`. -/
  nonblockFds : Array Nat := #[]
  /-- Whether `postFork.spawn` received the exact expected isolated `ChildSpecM`. -/
  childSpecExact : Bool := false
  /-- Whether `postFork.spawn` should simulate a post-fork `.chdir` failure. -/
  failChdir : Bool := false
  /-- Targets passed to `kill` (excluding `.sigzero` probes). -/
  killedTargets : Array (Int32 × LinuxSyscall.Process.Signal) := #[]

/-- Deterministic `SysDepsM` fixture auditing `cwd` pre-validation, `ChildSpecM` isolation invariants, `pgid = 1` `kill` safety, and `.chdir` failure attribution. -/
def mkSpawnAuditDeps : Internal.SysDepsM (StateM SpawnAuditState) Nat where
  proc :=
    { pipe2 := fun flags => modifyGet fun s =>
        let r := s.nextFd
        let w := s.nextFd + 1
        (.ok (r, w),
         { s with
           nextFd := s.nextFd + 2
           openFds := w :: r :: s.openFds
           allPipeCloexec := s.allPipeCloexec && flags.cloexec })
      waitpid := fun _ _ => pure (.ok (.exited 1 0))
      kill := fun target sig => modifyGet fun s =>
        let kt := if sig == .sigzero then s.killedTargets else s.killedTargets.push (target, sig)
        (.ok (), { s with killedTargets := kt })
      pidfd_open := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
      pidfd_send_signal := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
      getpid := pure (.ok 1)
      getuid := pure (.ok 1000) }
  files :=
    { openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      close := fun fd => modifyGet fun s =>
        if fd ∈ s.openFds then
          (.ok (), { s with openFds := s.openFds.erase fd })
        else
          (.error LinuxSyscall.Errno.EBADF, s)
      read := fun _ _ => pure (.ok ByteArray.empty)
      write := fun _ data => pure (.ok (UInt32.ofNat data.size))
      fstat := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      fstatat := fun _ path _ =>
        if path == "/valid_dir".toUTF8 || path == "/no_access_dir".toUTF8 then
          pure (.ok { kind := .dir, size := 0, mode := 0o755, ino := 2, dev := 1, nlink := 2,
                      mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 })
        else if path == "/valid_dir/relbin/tool".toUTF8 || path == "/not_a_dir".toUTF8 then
          pure (.ok { kind := .reg, size := 32, mode := 0o755, ino := 3, dev := 1, nlink := 1,
                      mtimeSec := 0, mtimeNsec := 0, atimeSec := 0, atimeNsec := 0 })
        else
          pure (.error LinuxSyscall.Errno.ENOENT)
      faccessat := fun _ path mask flags =>
        if (path == "/valid_dir".toUTF8 || path == "/valid_dir/relbin/tool".toUTF8) &&
            mask.exec && flags.eaccess then
          pure (.ok ())
        else
          pure (.error LinuxSyscall.Errno.EACCES)
      mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOENT)
      getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.EACCES)
      fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      flock := fun _ _ => pure (.error LinuxSyscall.Errno.EBADF)
      fcntl := fun fd cmd => modifyGet fun s =>
        match cmd with
        | .setFl true false => (.ok 0, { s with nonblockFds := s.nonblockFds.push fd })
        | _ => (.ok 0, s)
      fsync := fun _ => pure (.ok ())
      getcwd := fun _ => pure (.ok "/".toUTF8)
      lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ESPIPE)
      reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.EBADF)
      dupStdio := fun _ => pure (.error LinuxSyscall.Errno.EBADF) }
  poll :=
    { ppoll := fun entries _ => pure (.ok (entries.map Prod.snd))
      eventfd2 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
  timeRand :=
    { clock_gettime := fun _ => pure (.ok { sec := 0, nsec := 0 })
      clock_nanosleep := fun _ _ _ => pure (.ok ())
      getrandom := fun _ _ => pure (.ok ByteArray.empty) }
  postFork :=
    { spawn := fun spec => modifyGet fun s =>
        if s.failChdir then
          (.error { kind := .childFailed
                    errno := some LinuxSyscall.Errno.ENOENT
                    childFailure := some { stage := .chdir, errno := LinuxSyscall.Errno.ENOENT }
                    message := "chdir failed" }, s)
        else
          let specOk :=
            spec.path == "relbin/tool" &&
            spec.argv == #[PostFork.ArgToken.lit "tool", PostFork.ArgToken.lit "--flag"] &&
            spec.cwd == some "/valid_dir" &&
            spec.env == #[] &&
            spec.rawEnv == #["A=1".toUTF8, "PATH=relbin".toUTF8] &&
            spec.stdio == .redirect (.handle 20) (.handle 23) (.handle 25) true &&
            spec.fdPolicy == .inheritNonCloexec #[] &&
            spec.closeFds == #[.handle 21, .handle 22, .handle 24] &&
            spec.processGroup == .newGroup &&
            spec.sigpipe == .resetDefault &&
            spec.forkMode == .direct
          (.ok { pid := 1, pgid := some 1 }, { s with childSpecExact := specOk })
      spawnWithBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      releaseBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      abortBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" }) }
  listAmbientEnv := pure (.ok #[])

/-- `SysBridge.mkRawOpsM` pre-validates `req.cwd` before `PATH` search (`ENOTDIR`, `EACCES`, `ENOENT`, `""`), enforces `O_CLOEXEC` pipes, `O_NONBLOCK` parent pipe ends, and isolated `ChildSpecM` (`processGroup = .newGroup`, `sigpipe = .resetDefault`, `forkMode = .direct`, exact `closeFds`), maps `pgid = 1` to `kill(1, ...)` rather than `0` or `-1`, and attributes post-fork `.chdir` errors to `req.cwd`. -/
def test_process_sysBridge_spawnCwdIsolationKillPgid1AndChdirError
    {runner} [NondetTest runner]
    (stateTblFn :
      (SpawnAuditState → Internal.ProcTableState Nat) →
      (SpawnAuditState → Internal.ProcTableState Nat → SpawnAuditState) →
      Internal.ProcTableOpsM (StateM SpawnAuditState) Nat)
    (mkRawFn :
      Internal.SysDepsM (StateM SpawnAuditState) Nat →
      Internal.ProcTableOpsM (StateM SpawnAuditState) Nat →
      Nat → Nat →
      RawProcessOpsM (StateM SpawnAuditState)) : runner Unit := do
  let ops :=
    mkRawFn mkSpawnAuditDeps (stateTblFn (·.tbl) (fun s t => { s with tbl := t })) 2 4
  let rNotDir :=
    (ops.spawn { program := "missing_prog", cwd := some "/not_a_dir", inheritEnv := false,
                 env := #[("PATH", some "relbin")] }).run {}
  let rNoAcc :=
    (ops.spawn { program := "missing_prog", cwd := some "/no_access_dir", inheritEnv := false,
                 env := #[("PATH", some "/valid_dir/relbin")] }).run {}
  let rNoEnt :=
    (ops.spawn { program := "missing_prog", cwd := some "/missing_cwd", inheritEnv := false,
                 env := #[("PATH", some "/valid_dir/relbin")] }).run {}
  let rEmptyCwd :=
    (ops.spawn { program := "tool", cwd := some "", inheritEnv := false,
                 env := #[("PATH", some "valid_dir/relbin")] }).run {}
  let validReq : ExecRequest :=
    { program := "tool"
      args := #["--flag"]
      cwd := some "/valid_dir"
      inheritEnv := false
      env := #[("A", some "1"), ("PATH", some "relbin")] }
  let rChdirFail := (ops.spawn validReq).run { failChdir := true }
  let fullProg : StateM SpawnAuditState (Bool × Nat) := do
    match ← ops.spawn validReq with
    | .error _ => return (false, 99)
    | .ok h =>
      let aw ← ops.awaitOutput h "hi".toUTF8 none none
      let kg ← ops.killProcessGroup h
      let rp ← ops.reap h
      let cnt ← ops.activeProcessCount
      return (aw.isOk && kg.isOk && rp.isOk, cnt)
  let rFull := fullProg.run {}
  let notDirOk : Bool := match rNotDir.1 with
    | .error e => e.kind == .ioError && e.errnoCode == some LinuxSyscall.Errno.ENOTDIR && e.program == some "/not_a_dir"
    | .ok _ => false
  let noAccOk : Bool := match rNoAcc.1 with
    | .error e => e.kind == .permissionDenied && e.errnoCode == some LinuxSyscall.Errno.EACCES && e.program == some "/no_access_dir"
    | .ok _ => false
  let noEntOk : Bool := match rNoEnt.1 with
    | .error e => e.kind == .notFound && e.errnoCode == some LinuxSyscall.Errno.ENOENT && e.program == some "/missing_cwd"
    | .ok _ => false
  let emptyCwdOk : Bool := match rEmptyCwd.1 with
    | .error e => e.kind == .notFound && e.errnoCode == some LinuxSyscall.Errno.ENOENT && e.program == some ""
    | .ok _ => false
  let chdirFailOk : Bool := match rChdirFail.1 with
    | .error e => e.kind == .notFound && e.program == some "/valid_dir" && rChdirFail.2.openFds == [7]
    | .ok _ => false
  NondetTest.assert (
    notDirOk = true ∧
    noAccOk = true ∧
    noEntOk = true ∧
    emptyCwdOk = true ∧
    chdirFailOk = true ∧
    rFull.1.1 = true ∧
    rFull.1.2 = 0 ∧
    rFull.2.allPipeCloexec = true ∧
    rFull.2.childSpecExact = true ∧
    rFull.2.nonblockFds = #[21, 22, 24] ∧
    ((1 : Int32), LinuxSyscall.Process.Signal.sigterm) ∈ rFull.2.killedTargets.toList ∧
    ((1 : Int32), LinuxSyscall.Process.Signal.sigkill) ∈ rFull.2.killedTargets.toList ∧
    rFull.2.openFds = [7])

/-- `Internal.mkApiM.spawn` rejects every invalid `SpawnRequest` with `.invalidInput` and a non-empty message without calling `raw.spawn` or mutating state. -/
def test_process_spawn_invalidRequest_doesNotCallRaw
    {runner} [NondetTest runner]
    (mkApiFn : RawProcessOpsM (StateM Nat) → ProcessApiM (StateM Nat)) : runner Unit := do
  let s₀ ← nondet Nat
  let req ← nondet SpawnRequest
  let raw : RawProcessOpsM (StateM Nat) :=
    { mapRawError := fun _ => { kind := .ioError, message := "err" }
      spawn := fun _ => modifyGet fun n => (.ok { handleId := n, pid := 1, pgid := 1 }, n + 1)
      awaitOutput := fun _ _ _ _ => pure (.error { kind := .ioError, message := "unused" })
      killProcessGroup := fun _ => pure (.ok ())
      reap := fun _ => pure (.ok ())
      activeProcessCount := get }
  let api := mkApiFn raw
  match api.validateRequest { toSpawnRequest := req } with
  | .ok _ => assume False
  | .error _ =>
    let (res, s₁) := (api.spawn req).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ s₁ = s₀)

/-- `Internal.mkApiM.spawn` passes the `validateSpawnRequest`-normalized request (with default `ExecRequest` I/O fields) to `raw.spawn` and behaves identically on `req` and `norm`. -/
def test_process_spawn_usesNormalizedRequest
    {runner} [NondetTest runner]
    (mkApiFn : RawProcessOpsM (StateM (Option ExecRequest)) → ProcessApiM (StateM (Option ExecRequest))) :
    runner Unit := do
  let req ← nondet SpawnRequest
  let raw : RawProcessOpsM (StateM (Option ExecRequest)) :=
    { mapRawError := fun _ => { kind := .ioError, message := "err" }
      spawn := fun r => modifyGet fun _ => (.ok { handleId := 1, pid := 7, pgid := 7 }, some r)
      awaitOutput := fun _ _ _ _ => pure (.error { kind := .ioError, message := "unused" })
      killProcessGroup := fun _ => pure (.ok ())
      reap := fun _ => pure (.ok ())
      activeProcessCount := pure 0 }
  let api := mkApiFn raw
  match api.validateRequest { toSpawnRequest := req } with
  | .error _ => assume False
  | .ok norm =>
    let (res1, seen1) := (api.spawn req).run none
    let (res2, seen2) := (api.spawn norm.toSpawnRequest).run none
    NondetTest.assert (seen1 = some norm ∧ seen2 = some norm ∧ res1 = res2)

/-- `Internal.mkApiM.awaitOutput` rejects `timeoutMs = some 0` with `.invalidInput` and a non-empty message without invoking `raw.awaitOutput` or mutating state. -/
def test_process_awaitOutput_rejectsZeroTimeout
    {runner} [NondetTest runner]
    (mkApiFn : RawProcessOpsM (StateM Nat) → ProcessApiM (StateM Nat)) : runner Unit := do
  let s₀ ← nondet Nat
  let h ← nondet ProcessHandle
  let stdin ← nondet ByteArray
  let maxOut ← nondet (Option Nat)
  let raw : RawProcessOpsM (StateM Nat) :=
    { mapRawError := fun _ => { kind := .ioError, message := "err" }
      spawn := fun _ => pure (.error { kind := .ioError, message := "unused" })
      awaitOutput := fun _ _ _ _ => modifyGet fun n =>
        (.ok (.exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }), n + 1)
      killProcessGroup := fun _ => pure (.ok ())
      reap := fun _ => pure (.ok ())
      activeProcessCount := get }
  let api := mkApiFn raw
  let (res, s₁) := (api.awaitOutput h stdin (some 0) maxOut).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧ s₁ = s₀)

/-- Scripted `RawProcessOpsM` state auditing validated `spawn`, `awaitOutput`, `killProcessGroup`, and `reap` delegation and empty-message error normalization. -/
structure LifecycleScriptState where
  /-- Active unreaped handle count. -/
  active : Nat := 0
  /-- Failure mode selector (`0` = ok, `1` = spawn error, `2` = awaitOutput error, `3` = killProcessGroup error, `4` = reap error). -/
  failMode : Nat := 0
  /-- Recorded arguments passed to `raw.awaitOutput`. -/
  lastAwait : Option (ProcessHandle × ByteArray × Option Nat × Option Nat) := none
  /-- Count of `raw.killProcessGroup` invocations. -/
  killed : Nat := 0
  /-- Count of `raw.reap` invocations. -/
  reaped : Nat := 0

/-- Deterministic `RawProcessOpsM` fixture exercising handle lifecycle delegation and empty-message error normalization. -/
def mkLifecycleScriptRawOps : RawProcessOpsM (StateM LifecycleScriptState) where
  mapRawError := fun _ => { kind := .ioError, message := "err" }
  spawn := fun _ => modifyGet fun s =>
    if s.failMode == 1 then
      (.error { kind := .notFound, message := "" }, s)
    else
      (.ok { handleId := 3, pid := 88, pgid := 88 }, { s with active := s.active + 1 })
  awaitOutput := fun h stdin to? max? => modifyGet fun s =>
    let s' := { s with lastAwait := some (h, stdin, to?, max?) }
    if s.failMode == 2 then
      (.error { kind := .ioError, message := "" }, s')
    else
      (.ok (.exited { exitCode := 5, stdout := "LO".toUTF8, stderr := "LE".toUTF8 }), s')
  killProcessGroup := fun _ => modifyGet fun s =>
    let s' := { s with killed := s.killed + 1 }
    if s.failMode == 3 then
      (.error { kind := .permissionDenied, message := "" }, s')
    else
      (.ok (), s')
  reap := fun _ => modifyGet fun s =>
    if s.failMode == 4 then
      (.error { kind := .ioError, message := "" }, { s with reaped := s.reaped + 1 })
    else
      (.ok (), { s with active := s.active - 1, reaped := s.reaped + 1 })
  activeProcessCount := do return (← get).active

/-- `Internal.mkApiM` delegates validated `spawn`, `awaitOutput`, `killProcessGroup`, and `reap` cleanly to `raw` and normalizes empty error messages across all 4 lifecycle operations. -/
def test_process_lifecycle_delegatesAndNormalizesErrors
    {runner} [NondetTest runner]
    (mkApiFn :
      RawProcessOpsM (StateM LifecycleScriptState) →
      ProcessApiM (StateM LifecycleScriptState)) : runner Unit := do
  let api := mkApiFn mkLifecycleScriptRawOps
  let req : SpawnRequest := { program := "/bin/demo", args := #["x"] }
  let okProg : StateM LifecycleScriptState Bool := do
    match ← api.spawn req with
    | .error _ => return false
    | .ok h =>
      let c1 ← api.activeProcessCount
      let aw ← api.awaitOutput h "in".toUTF8 (some 250) (some 64)
      let kg ← api.killProcessGroup h
      let rp ← api.reap h
      let c2 ← api.activeProcessCount
      let awOk := match aw with
        | .ok (.exited out) => out == { exitCode := 5, stdout := "LO".toUTF8, stderr := "LE".toUTF8 }
        | _ => false
      return (h == { handleId := 3, pid := 88, pgid := 88 } &&
        c1 == 1 && awOk && kg.isOk && rp.isOk && c2 == 0)
  let rOk := okProg.run {}
  let h0 : ProcessHandle := { handleId := 3, pid := 88, pgid := 88 }
  let rSpErr := (api.spawn req).run { failMode := 1 }
  let rAwErr := (api.awaitOutput h0 ByteArray.empty (some 10) none).run { failMode := 2 }
  let rKgErr := (api.killProcessGroup h0).run { failMode := 3 }
  let rRpErr := (api.reap h0).run { failMode := 4 }
  let spErrOk : Bool := match rSpErr.1 with
    | .error e => e.kind == .notFound && !e.message.isEmpty
    | .ok _ => false
  let awErrOk : Bool := match rAwErr.1 with
    | .error e => e.kind == .ioError && !e.message.isEmpty
    | .ok _ => false
  let kgErrOk : Bool := match rKgErr.1 with
    | .error e => e.kind == .permissionDenied && !e.message.isEmpty
    | .ok _ => false
  let rpErrOk : Bool := match rRpErr.1 with
    | .error e => e.kind == .ioError && !e.message.isEmpty
    | .ok _ => false
  NondetTest.assert (
    rOk.1 = true ∧
    rOk.2.lastAwait = some (h0, "in".toUTF8, some 250, some 64) ∧
    rOk.2.killed = 1 ∧
    rOk.2.reaped = 1 ∧
    spErrOk = true ∧
    awErrOk = true ∧
    kgErrOk = true ∧
    rpErrOk = true)

/-- Complete error-kind coverage table for every fallible public entrypoint in `LeanSwe.Process`. -/
def errorCoverage : List (Core.ErrorObligation ProcessErrorKind) :=
  [ { request := "LeanSwe.Process.validateRequest"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_validateRequest_invalidInput" .real }
  , { request := "LeanSwe.Process.validateRequest"
      errorKind := .notFound
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_validateRequest_never_notFound" }
  , { request := "LeanSwe.Process.validateRequest"
      errorKind := .permissionDenied
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_validateRequest_never_permissionDenied" }
  , { request := "LeanSwe.Process.validateRequest"
      errorKind := .timedOut
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_validateRequest_never_timedOut" }
  , { request := "LeanSwe.Process.validateRequest"
      errorKind := .outputLimitExceeded
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_validateRequest_never_outputLimitExceeded" }
  , { request := "LeanSwe.Process.validateRequest"
      errorKind := .terminatedBySignal
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_validateRequest_never_terminatedBySignal" }
  , { request := "LeanSwe.Process.validateRequest"
      errorKind := .nonZeroExit
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_validateRequest_never_nonZeroExit" }
  , { request := "LeanSwe.Process.validateRequest"
      errorKind := .ioError
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_validateRequest_never_ioError" }
  , { request := "LeanSwe.Process.run"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_run_notFound" .real }
  , { request := "LeanSwe.Process.run"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_run_permissionDenied" .real }
  , { request := "LeanSwe.Process.run"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_run_invalidInput" .real }
  , { request := "LeanSwe.Process.run"
      errorKind := .timedOut
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_run_timedOut" .real }
  , { request := "LeanSwe.Process.run"
      errorKind := .outputLimitExceeded
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_run_outputLimitExceeded" .real }
  , { request := "LeanSwe.Process.run"
      errorKind := .terminatedBySignal
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_run_terminatedBySignal" .real }
  , { request := "LeanSwe.Process.run"
      errorKind := .nonZeroExit
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_run_never_nonZeroExit" }
  , { request := "LeanSwe.Process.run"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_run_ioError" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_notFound" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_permissionDenied" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_invalidInput" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .timedOut
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_timedOut" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .outputLimitExceeded
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_outputLimitExceeded" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .terminatedBySignal
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_terminatedBySignal" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .nonZeroExit
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_nonZeroExit" .real }
  , { request := "LeanSwe.Process.runChecked"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runChecked_ioError" .real }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommand_notFound" .real }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommand_permissionDenied" .real }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommand_invalidInput" .real }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .timedOut
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_runCommand_never_timedOut" }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .outputLimitExceeded
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_runCommand_never_outputLimitExceeded" }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .terminatedBySignal
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommand_terminatedBySignal" .real }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .nonZeroExit
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_runCommand_never_nonZeroExit" }
  , { request := "LeanSwe.Process.runCommand"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommand_ioError" .real }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_notFound" .real }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_permissionDenied" .real }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_invalidInput" .real }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .timedOut
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_runCommandChecked_never_timedOut" }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .outputLimitExceeded
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_runCommandChecked_never_outputLimitExceeded" }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .terminatedBySignal
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_terminatedBySignal" .real }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .nonZeroExit
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_nonZeroExit" .real }
  , { request := "LeanSwe.Process.runCommandChecked"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_runCommandChecked_ioError" .real }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_spawn_notFound" .real }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_spawn_permissionDenied" .real }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_spawn_invalidInput" .real }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .timedOut
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_spawn_never_timedOut" }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .outputLimitExceeded
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_spawn_never_outputLimitExceeded" }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .terminatedBySignal
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_spawn_never_terminatedBySignal" }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .nonZeroExit
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_spawn_never_nonZeroExit" }
  , { request := "LeanSwe.Process.spawn"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_spawn_ioError" .real }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_notFound" .mocked }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_permissionDenied" .mocked }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_invalidInput" .real }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .timedOut
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_awaitOutput_never_timedOut" }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .outputLimitExceeded
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_awaitOutput_never_outputLimitExceeded" }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .terminatedBySignal
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_awaitOutput_never_terminatedBySignal" }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .nonZeroExit
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_awaitOutput_never_nonZeroExit" }
  , { request := "LeanSwe.Process.awaitOutput"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_awaitOutput_ioError" .real }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_notFound" .mocked }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_permissionDenied" .mocked }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_invalidInput" .mocked }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .timedOut
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_killProcessGroup_never_timedOut" }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .outputLimitExceeded
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_killProcessGroup_never_outputLimitExceeded" }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .terminatedBySignal
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_killProcessGroup_never_terminatedBySignal" }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .nonZeroExit
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_killProcessGroup_never_nonZeroExit" }
  , { request := "LeanSwe.Process.killProcessGroup"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_killProcessGroup_ioError" .mocked }
  , { request := "LeanSwe.Process.reap"
      errorKind := .notFound
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_reap_notFound" .mocked }
  , { request := "LeanSwe.Process.reap"
      errorKind := .permissionDenied
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_reap_permissionDenied" .mocked }
  , { request := "LeanSwe.Process.reap"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_reap_invalidInput" .mocked }
  , { request := "LeanSwe.Process.reap"
      errorKind := .timedOut
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_reap_never_timedOut" }
  , { request := "LeanSwe.Process.reap"
      errorKind := .outputLimitExceeded
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_reap_never_outputLimitExceeded" }
  , { request := "LeanSwe.Process.reap"
      errorKind := .terminatedBySignal
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_reap_never_terminatedBySignal" }
  , { request := "LeanSwe.Process.reap"
      errorKind := .nonZeroExit
      justification := .provedImpossible "LeanSwe.Process.Proofs.process_reap_never_nonZeroExit" }
  , { request := "LeanSwe.Process.reap"
      errorKind := .ioError
      justification := .tested "LeanSwe.Process.RuntimeTests.err_process_reap_ioError" .mocked }
  ]

end LeanSwe.Process
