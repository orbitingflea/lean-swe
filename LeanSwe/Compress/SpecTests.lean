import Core.NondetTest
import Core.Assumptions
import LeanSwe.Process.Types
import LeanSwe.Compress.Types
import LeanSwe.Compress.Model

namespace LeanSwe.Compress

open Core (NondetTest AssumptionObligation ErrorObligation)
open Core.NondetTest
open LeanSwe.Process
  (ProcessErrorKind ProcessError ExecRequest ExecResult ProcessApiM)

/-- Builder function constructing a `CompressApiM m` from an injected `ProcessApiM m`. -/
abbrev CompressBuilder (m : Type → Type) :=
  ProcessApiM m → CompressApiM m

/-- CLI executable name for a `Codec`. -/
def codecProgram : Codec → String
  | .zstd => "zstd"
  | .xz => "xz"
  | .gzip => "gzip"

/-- Valid compression level predicate per `Codec`. -/
def isValidLevel (codec : Codec) : Option Nat → Bool
  | none => true
  | some lvl =>
    match codec with
    | .zstd => 1 ≤ lvl && lvl ≤ 19
    | .xz => lvl ≤ 9
    | .gzip => 1 ≤ lvl && lvl ≤ 9

/-- Valid worker thread count predicate per `Codec`. -/
def isValidThreads (codec : Codec) : Option Nat → Bool
  | none => true
  | some t =>
    match codec with
    | .zstd => t ≤ 4294967295
    | .xz => t ≤ 16384
    | .gzip => false

/-- Valid input and options predicate for `compressWith`. -/
def isValidCompressInput (codec : Codec) (opts : CompressOptions) (input : ByteArray) : Bool :=
  opts.timeoutMs > 0 &&
  opts.maxOutputBytes > 0 &&
  isValidLevel codec opts.level &&
  isValidThreads codec opts.threads &&
  match opts.maxInputBytes with
  | none => true
  | some lim => input.size ≤ lim

/-- Valid input and options predicate for `decompressWith`. -/
def isValidDecompressInput (opts : DecompressOptions) (input : ByteArray) : Bool :=
  opts.timeoutMs > 0 &&
  opts.maxOutputBytes > 0 &&
  match opts.maxInputBytes with
  | none => true
  | some lim => input.size ≤ lim

/-- Expected direct `execvp` argument array for `compressWith`. -/
def expectedCompressArgs (codec : Codec) (opts : CompressOptions) : Array String :=
  let levelArgs : Array String :=
    match opts.level with
    | none => #[]
    | some lvl => #[s!"-{lvl}"]
  let threadArgs : Array String :=
    match opts.threads with
    | none => #[]
    | some t => #[s!"-T{t}"]
  match codec with
  | .zstd => #["-c", "-q", "--no-progress"] ++ levelArgs ++ threadArgs
  | .xz => #["-c", "-q"] ++ levelArgs ++ threadArgs
  | .gzip => #["-c", "-n"] ++ levelArgs

/-- Expected direct `execvp` argument array for `decompressWith`. -/
def expectedDecompressArgs : Codec → Array String
  | .zstd => #["-d", "-c", "-q", "--no-progress", "--format=zstd"]
  | .xz => #["-d", "-c", "-q", "-T1", "--format=xz"]
  | .gzip => #["-d", "-c", "-n"]

/-- Expected `CompressError.stderr` decoding: `none` on empty or invalid UTF-8, `some s` on non-empty valid UTF-8. -/
def expectedStderr (bs : ByteArray) : Option String :=
  if bs.isEmpty then none else String.fromUTF8? bs

/-- Expected environment overrides clearing inherited codec configuration variables and pinning `LC_ALL=C`. -/
def expectedSanitizedEnv (_codec : Codec) : Array (String × Option String) :=
  #[("XZ_OPT", none),
    ("XZ_DEFAULTS", none),
    ("ZSTD_CLEVEL", none),
    ("ZSTD_NBTHREADS", none),
    ("GZIP", none),
    ("LC_ALL", some "C")]

/-- Expected pipe buffer slack beyond `maxOutputBytes` passed to `LeanSwe.Process`. -/
def expectedStderrPipeSlack : Nat := 4096

/-- Expected POSIX `errno` predicate for OS resource exhaustion (`IO.Error.resourceExhausted`) or `PATH` `ENAMETOOLONG` (`36`). -/
def expectedResourceOrPathIoErrno (code : UInt32) : Bool :=
  code == 7 || code == 11 || code == 12 || code == 23 || code == 24 ||
  code == 28 || code == 31 || code == 36 || code == 37 || code == 63 ||
  code == 90 || code == 105

/-- Return `true` iff a `.invalidInput` `ProcessError` represents an OS resource or `PATH` `Errno`. -/
def isResourceExhaustedProcessError (pe : ProcessError) : Bool :=
  pe.kind == .invalidInput &&
  match pe.errnoCode with
  | some code => expectedResourceOrPathIoErrno code
  | none => false

/-- Expected `CompressErrorKind` classification for a `ProcessErrorKind`. -/
def expectedProcessErrorKind : ProcessErrorKind → CompressErrorKind
  | .notFound => .toolNotFound
  | .permissionDenied => .toolNotFound
  | .invalidInput => .invalidInput
  | .timedOut => .timedOut
  | .outputLimitExceeded => .outputLimitExceeded
  | .terminatedBySignal => .commandFailed
  | .nonZeroExit => .commandFailed
  | .ioError => .ioError

/-- Expected `CompressErrorKind` classification for a full `ProcessError`. -/
def expectedProcessErrorKindFor (pe : ProcessError) : CompressErrorKind :=
  if isResourceExhaustedProcessError pe then .ioError
  else expectedProcessErrorKind pe.kind

/-- Expected normalized `exitCode` for `classifyProcessError` matching `Model.isWellFormedCompressError`. -/
def expectedProcessErrorExitCode (kind : CompressErrorKind) (exitCode : Option Int) : Option Int :=
  match kind with
  | .commandFailed =>
    match exitCode with
    | some c => if c != 0 then some c else none
    | none => none
  | _ => none

/-- Deterministic mock process state for `ProcessApiM (StateM MockProcState)` spec tests. -/
structure MockProcState where
  /-- Scripted response for `proc.run`. -/
  onRun : ExecRequest → Except ProcessError ExecResult :=
    fun req => .ok { exitCode := 0, stdout := req.stdin, stderr := ByteArray.empty }
  /-- Recorded `ExecRequest` values passed to `proc.run` in invocation order. -/
  ran : List ExecRequest := []
  /-- Total `proc.run` calls attempted. -/
  runAttempts : Nat := 0

/-- Deterministic `ProcessApiM (StateM MockProcState)` backed by `MockProcState`. -/
def mockProcessApi : ProcessApiM (StateM MockProcState) :=
  { mapRawError := fun
      | .executableNotFound prog errno detail =>
        { kind := .notFound, program := some prog, errnoCode := some errno, message := detail }
      | .permissionDenied prog? errno detail =>
        { kind := .permissionDenied, program := prog?, errnoCode := some errno, message := detail }
      | .invalidArgument prog? errno detail =>
        { kind := .invalidInput, program := prog?, errnoCode := some errno, message := detail }
      | .timedOut prog _ detail =>
        { kind := .timedOut, program := some prog, message := detail }
      | .outputLimitExceeded prog _ detail =>
        { kind := .outputLimitExceeded, program := some prog, message := detail }
      | .signaled prog sig detail =>
        { kind := .terminatedBySignal, program := some prog, signal := some sig, message := detail }
      | .otherError errno detail =>
        { kind := .ioError, errnoCode := some errno, message := detail }
      | .userError detail =>
        { kind := .ioError, message := detail }
    validateRequest := fun req => .ok req
    mkCommandRequest := fun program args => { program := program, args := args }
    withTextInput := fun req text => { req with stdin := text.toUTF8 }
    spawn := fun _ => pure (.error { kind := .ioError, message := "unused" })
    awaitOutput := fun _ _ _ _ => pure (.error { kind := .ioError, message := "unused" })
    killProcessGroup := fun _ => pure (.ok ())
    reap := fun _ => pure (.ok ())
    run := fun req => do
      let s ← get
      set { s with ran := s.ran ++ [req], runAttempts := s.runAttempts + 1 }
      return s.onRun req
    runChecked := fun req => do
      let s ← get
      set { s with ran := s.ran ++ [req], runAttempts := s.runAttempts + 1 }
      match s.onRun req with
      | .error e => return .error e
      | .ok res =>
        if res.exitCode == 0 then return .ok res
        else
          return .error
            { kind := .nonZeroExit
              program := some req.program
              exitCode := some res.exitCode
              stdout := some res.stdout
              stderr := some res.stderr
              message := s!"process '{req.program}' exited with status {res.exitCode}" }
    runCommand := fun program args => do
      let req : ExecRequest := { program := program, args := args }
      let s ← get
      set { s with ran := s.ran ++ [req], runAttempts := s.runAttempts + 1 }
      return s.onRun req
    runCommandChecked := fun program args => do
      let req : ExecRequest := { program := program, args := args }
      let s ← get
      set { s with ran := s.ran ++ [req], runAttempts := s.runAttempts + 1 }
      match s.onRun req with
      | .error e => return .error e
      | .ok res =>
        if res.exitCode == 0 then return .ok res
        else
          return .error
            { kind := .nonZeroExit
              program := some req.program
              exitCode := some res.exitCode
              stdout := some res.stdout
              stderr := some res.stderr
              message := s!"process '{req.program}' exited with status {res.exitCode}" }
    activeProcessCount := return 0 }

/-- Invalid `CompressOptions` or `input.size > maxInputBytes` fail with `.invalidInput` without calling `proc` or mutating state. -/
def test_compress_compressWith_invalidOptionsRejectWithoutSpawn
    {S : Type} {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM S))
    (proc : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let codec ← nondet Codec
  let opts ← nondet CompressOptions
  let input ← nondet ByteArray
  assume (isValidCompressInput codec opts input = false)
  let (res, s₁) := ((mkApi proc).compressWith codec opts input).run s₀
  NondetTest.assert
    (∃ e, res = .error e ∧
      e.kind = .invalidInput ∧
      e.codec = some codec ∧
      e.exitCode = none ∧
      e.stderr = none ∧
      e.message ≠ "")
  NondetTest.assert (s₁ = s₀)

/-- Invalid `DecompressOptions` or `input.size > maxInputBytes` fail with `.invalidInput` without calling `proc` or mutating state. -/
def test_compress_decompressWith_invalidOptionsRejectWithoutSpawn
    {S : Type} {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM S))
    (proc : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let codec ← nondet Codec
  let opts ← nondet DecompressOptions
  let input ← nondet ByteArray
  assume (isValidDecompressInput opts input = false)
  let (res, s₁) := ((mkApi proc).decompressWith codec opts input).run s₀
  NondetTest.assert
    (∃ e, res = .error e ∧
      e.kind = .invalidInput ∧
      e.codec = some codec ∧
      e.exitCode = none ∧
      e.stderr = none ∧
      e.message ≠ "")
  NondetTest.assert (s₁ = s₀)

/-- Valid `compressWith` builds exact direct `execvp` args, strips inherited codec env vars, passes `stdin` (including empty), and enforces `maxOutputBytes`. -/
def test_compress_compressWith_buildsExactExecRequest
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let opts ← nondet CompressOptions
  let input ← nondet ByteArray
  let outBytes ← nondet ByteArray
  let errBytes ← nondet ByteArray
  assume (isValidCompressInput codec opts input = true)
  let s₀ : MockProcState :=
    { onRun := fun _ =>
        .ok { exitCode := 0, stdout := outBytes, stderr := errBytes } }
  let (res, s₁) := ((mkApi mockProcessApi).compressWith codec opts input).run s₀
  if outBytes.size ≤ opts.maxOutputBytes then
    NondetTest.assert (res = .ok outBytes)
  else
    NondetTest.assert
      (∃ e, res = .error e ∧
        e.kind = .outputLimitExceeded ∧
        e.codec = some codec ∧
        e.exitCode = none ∧
        e.stderr = expectedStderr errBytes ∧
        e.message ≠ "")
  NondetTest.assert (s₁.runAttempts = 1)
  NondetTest.assert (s₁.ran =
    [{ program := codecProgram codec
       args := expectedCompressArgs codec opts
       cwd := none
       env := expectedSanitizedEnv codec
       inheritEnv := true
       stdin := input
       timeoutMs := some opts.timeoutMs
       maxOutputBytes := some (opts.maxOutputBytes + expectedStderrPipeSlack) }])

/-- Valid `decompressWith` always invokes the codec subprocess (even for `ByteArray.empty`), strips codec env vars, checks `maxOutputBytes`, and validates container framing on exit `0`. -/
def test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let opts ← nondet DecompressOptions
  let input ← nondet ByteArray
  let exitCode ← nondet Int
  let outBytes ← nondet ByteArray
  let errBytes ← nondet ByteArray
  assume (isValidDecompressInput opts input = true)
  let s₀ : MockProcState :=
    { onRun := fun _ =>
        .ok { exitCode := exitCode, stdout := outBytes, stderr := errBytes } }
  let (res, s₁) := ((mkApi mockProcessApi).decompressWith codec opts input).run s₀
  NondetTest.assert (s₁.runAttempts = 1)
  NondetTest.assert (s₁.ran =
    [{ program := codecProgram codec
       args := expectedDecompressArgs codec
       cwd := none
       env := expectedSanitizedEnv codec
       inheritEnv := true
       stdin := input
       timeoutMs := some opts.timeoutMs
       maxOutputBytes := some (opts.maxOutputBytes + expectedStderrPipeSlack) }])
  if exitCode != 0 then
    NondetTest.assert
      (∃ e, res = .error e ∧
        e.kind = .corruptData ∧
        e.codec = some codec ∧
        e.exitCode = some exitCode ∧
        e.stderr = expectedStderr errBytes ∧
        e.message ≠ "")
  else if outBytes.size > opts.maxOutputBytes then
    if codec == .gzip && !Model.hasGzipHeader input then
      NondetTest.assert
        (∃ e, res = .error e ∧
          e.kind = .corruptData ∧
          e.codec = some codec ∧
          e.exitCode = none ∧
          e.stderr = none ∧
          e.message ≠ "")
    else
      NondetTest.assert
        (∃ e, res = .error e ∧
          e.kind = .outputLimitExceeded ∧
          e.codec = some codec ∧
          e.exitCode = none ∧
          e.stderr = expectedStderr errBytes ∧
          e.message ≠ "")
  else
    if codec == .gzip && !Model.hasGzipHeader input then
      NondetTest.assert
        (∃ e, res = .error e ∧
          e.kind = .corruptData ∧
          e.codec = some codec ∧
          e.exitCode = none ∧
          e.stderr = none ∧
          e.message ≠ "")
    else
      NondetTest.assert (res = .ok outBytes)

/-- `compress` and `decompress` are equivalent to `compressWith _ {}` and `decompressWith _ {}` for any `proc`. -/
def test_compress_defaults_matchWithDefaultOptions
    {S : Type} {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM S))
    (proc : ProcessApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let codec ← nondet Codec
  let input ← nondet ByteArray
  let api := mkApi proc
  NondetTest.assert ((api.compress codec input).run s₀ = (api.compressWith codec {} input).run s₀)
  NondetTest.assert ((api.decompress codec input).run s₀ = (api.decompressWith codec {} input).run s₀)

/-- `proc.run` errors (`notFound`/`permissionDenied` → `.toolNotFound`, etc.) map completely with preserved non-empty messages. -/
def test_compress_spawnErrors_mappedCorrectly
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let isDecompress ← nondet Bool
  let copts ← nondet CompressOptions
  let dopts ← nondet DecompressOptions
  let pe ← nondet ProcessError
  let input ← nondet ByteArray
  assume (if isDecompress then isValidDecompressInput dopts input = true else isValidCompressInput codec copts input = true)
  let s₀ : MockProcState :=
    { onRun := fun _ => .error pe }
  let api := mkApi mockProcessApi
  let (res, s₁) :=
    if isDecompress then
      (api.decompressWith codec dopts input).run s₀
    else
      (api.compressWith codec copts input).run s₀
  NondetTest.assert (s₁.runAttempts = 1)
  NondetTest.assert
    (∃ e, res = .error e ∧
      e.kind =
        (if isDecompress && (pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
            codec == .gzip && !Model.hasGzipHeader input then
          .corruptData
        else
          expectedProcessErrorKindFor pe) ∧
      e.codec = some codec ∧
      e.exitCode =
        (if isDecompress && (pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
            codec == .gzip && !Model.hasGzipHeader input then
          none
        else
          expectedProcessErrorExitCode (expectedProcessErrorKindFor pe) pe.exitCode) ∧
      e.stderr =
        (match expectedProcessErrorKindFor pe with
        | .toolNotFound | .invalidInput => none
        | _ => pe.stderr.bind expectedStderr) ∧
      e.message ≠ "" ∧
      (pe.message = "" ∨ e.message = pe.message ∨
        (isDecompress && (pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
          codec == .gzip && !Model.hasGzipHeader input)))

/-- Abnormal `proc.run` outcomes (`.timedOut`, `.outputLimitExceeded`, `.terminatedBySignal`, `.ioError`) classify cleanly and honor gzip framing precedence. -/
def test_compress_awaitOutcomes_classified
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let isDecompress ← nondet Bool
  let copts ← nondet CompressOptions
  let dopts ← nondet DecompressOptions
  let input ← nondet ByteArray
  let outBytes ← nondet ByteArray
  let errBytes ← nondet ByteArray
  let sig ← nondet Int
  let outcomeKind ← nondet Nat
  assume (outcomeKind < 4)
  assume (if isDecompress then isValidDecompressInput dopts input = true else isValidCompressInput codec copts input = true)
  let runRes : Except ProcessError ExecResult :=
    if outcomeKind == 0 then
      .error { kind := .timedOut, program := some (codecProgram codec), stdout := some outBytes, stderr := some errBytes, message := "process timed out" }
    else if outcomeKind == 1 then
      .error { kind := .outputLimitExceeded, program := some (codecProgram codec), stdout := some outBytes, stderr := some errBytes, message := "process exceeded output byte limit" }
    else if outcomeKind == 2 then
      .error { kind := .terminatedBySignal, program := some (codecProgram codec), signal := some sig, stdout := some outBytes, stderr := some errBytes, message := "process terminated by signal" }
    else
      .error { kind := .ioError, message := "pipe read failed" }
  let expectedKind : CompressErrorKind :=
    if outcomeKind == 0 then
      if isDecompress && codec == .gzip && !Model.hasGzipHeader input then .corruptData else .timedOut
    else if outcomeKind == 1 then
      if isDecompress && codec == .gzip && !Model.hasGzipHeader input then .corruptData else .outputLimitExceeded
    else if outcomeKind == 2 then .commandFailed
    else .ioError
  let s₀ : MockProcState :=
    { onRun := fun _ => runRes }
  let api := mkApi mockProcessApi
  let (res, s₁) :=
    if isDecompress then
      (api.decompressWith codec dopts input).run s₀
    else
      (api.compressWith codec copts input).run s₀
  NondetTest.assert (s₁.runAttempts = 1)
  NondetTest.assert
    (∃ e, res = .error e ∧
      e.kind = expectedKind ∧
      e.codec = some codec ∧
      e.message ≠ "")

/-- Non-zero subprocess exits yield `.commandFailed` on compression and `.corruptData` on decompression (including `gzip` exit `2`), with normalized `stderr`. -/
def test_compress_exitCodes_compressVsDecompress_andStderr
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let exitCode ← nondet Int
  let input ← nondet ByteArray
  let errBytes ← nondet ByteArray
  assume (exitCode ≠ 0)
  let s₀ : MockProcState :=
    { onRun := fun _ =>
        .ok { exitCode := exitCode, stdout := ByteArray.empty, stderr := errBytes } }
  let api := mkApi mockProcessApi
  let (cRes, _) := (api.compressWith codec {} input).run s₀
  let (dRes, _) := (api.decompressWith codec {} input).run s₀
  NondetTest.assert
    (∃ ce, cRes = .error ce ∧
      ce.kind = .commandFailed ∧
      ce.codec = some codec ∧
      ce.exitCode = some exitCode ∧
      ce.stderr = expectedStderr errBytes ∧
      ce.message ≠ "")
  NondetTest.assert
    (∃ de, dRes = .error de ∧
      de.kind = .corruptData ∧
      de.codec = some codec ∧
      de.exitCode = some exitCode ∧
      de.stderr = expectedStderr errBytes ∧
      de.message ≠ "")

/-- `isToolAvailable` runs `<binary> --version` with sanitized env, `timeoutMs = some 5000`, `maxOutputBytes = some 65536`, and returns `true` iff exit code is `0`. -/
def test_compress_isToolAvailable_checksVersion
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let runOk ← nondet Bool
  let exitCode ← nondet Int
  let s₀ : MockProcState :=
    { onRun := fun _ =>
        if runOk then .ok { exitCode := exitCode, stdout := ByteArray.empty, stderr := ByteArray.empty }
        else .error { kind := .notFound, program := some (codecProgram codec), message := "missing" } }
  let (avail, s₁) := ((mkApi mockProcessApi).isToolAvailable codec).run s₀
  NondetTest.assert (s₁.runAttempts = 1)
  NondetTest.assert (s₁.ran =
    [{ program := codecProgram codec
       args := #["--version"]
       cwd := none
       env := expectedSanitizedEnv codec
       inheritEnv := true
       stdin := ByteArray.empty
       timeoutMs := some 5000
       maxOutputBytes := some 65536 }])
  if runOk then
    NondetTest.assert (avail = (exitCode == 0))
  else
    NondetTest.assert (avail = false)

/-- Stateful relational behavior model `api` satisfies `allowedCompressStep`, `allowedDecompressStep`, and `allowedIsToolAvailable`, including multi-step round-trip and repeated `decompressWith` determinism. -/
def test_compress_modelApi_soundAgainstAllowedOutcome
    {runner} [NondetTest runner]
    (api : CompressApiM (StateT Model.State (ReaderM Model.CompressEnv))) : runner Unit := do
  let env ← nondet Model.CompressEnv
  let codec ← nondet Codec
  let copts ← nondet CompressOptions
  let dopts ← nondet DecompressOptions
  let input ← nondet ByteArray
  let rawBytes ← nondet ByteArray
  let st₀ := Model.State.empty
  let (cRes0, stC0) := ((api.compress codec input).run st₀).run env
  NondetTest.assert (Model.allowedCompressStep env st₀ codec {} input cRes0 stC0 = true)
  let rt0Ok : Bool :=
    match cRes0 with
    | .ok comp0 =>
      let (dRt0, stRt0) := ((api.decompress codec comp0).run stC0).run env
      let (dRtWith, stRtWith) := ((api.decompressWith codec dopts comp0).run stRt0).run env
      Model.allowedDecompressStep env stC0 codec {} comp0 dRt0 stRt0 &&
        Model.allowedDecompressStep env stRt0 codec dopts comp0 dRtWith stRtWith
    | .error _ => true
  NondetTest.assert (rt0Ok = true)
  let (cRes, stC) := ((api.compressWith codec copts input).run st₀).run env
  NondetTest.assert (Model.allowedCompressStep env st₀ codec copts input cRes stC = true)
  let rtOk : Bool :=
    match cRes with
    | .ok comp =>
      let (dRt, stRt) := ((api.decompressWith codec dopts comp).run stC).run env
      Model.allowedDecompressStep env stC codec dopts comp dRt stRt
    | .error _ => true
  NondetTest.assert (rtOk = true)
  let (dRes0, stD0) := ((api.decompress codec rawBytes).run st₀).run env
  NondetTest.assert (Model.allowedDecompressStep env st₀ codec {} rawBytes dRes0 stD0 = true)
  let (dRes, stD) := ((api.decompressWith codec dopts rawBytes).run stD0).run env
  NondetTest.assert (Model.allowedDecompressStep env stD0 codec dopts rawBytes dRes stD = true)
  let (avail, stA) := ((api.isToolAvailable codec).run st₀).run env
  NondetTest.assert (Model.allowedIsToolAvailable env codec avail = true ∧ stA = st₀)

/-- Spec-conforming pure process-outcome predicate linking a `Process.run` response to `Model.CompressEnv`, `Model.State`, and `Model` behavior. -/
def rawCompressCallConforms (env : Model.CompressEnv) (st₀ : Model.State) (codec : Codec)
    (opts : CompressOptions) (input : ByteArray)
    (outcome : Except ProcessError ExecResult) : Bool :=
  match outcome with
  | .error pe =>
    !pe.message.isEmpty &&
    match pe.kind with
    | .notFound | .permissionDenied => env.toolStatus codec == .missingOrNonExec
    | .invalidInput =>
      if isResourceExhaustedProcessError pe then
        env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
      else
        env.toolStatus codec == .pathSymlinkLoop
    | .ioError => env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
    | .timedOut => env.toolStatus codec == .available && env.allowTimeout
    | .terminatedBySignal => env.toolStatus codec == .available && env.allowExternalSignal
    | .nonZeroExit => false
    | .outputLimitExceeded =>
      env.toolStatus codec == .available && opts.maxOutputBytes < Model.maxCompressedBound codec input.size
  | .ok res =>
    if res.exitCode != 0 then
      env.toolStatus codec == .available && env.allowExternalSignal
    else if res.stdout.size > opts.maxOutputBytes then
      env.toolStatus codec == .available && opts.maxOutputBytes < Model.maxCompressedBound codec input.size
    else
      env.toolStatus codec == .available &&
      Model.hasCanonicalCompressedFraming codec res.stdout &&
      (match st₀.lookup codec res.stdout with
       | some prev => prev == input
       | none => true)

/-- Spec conformance predicate for `.timedOut` outcomes in `rawDecompressCallConforms`. -/
def rawTimedOutDecompressConforms (env : Model.CompressEnv) (st₀ : Model.State) (codec : Codec)
    (input : ByteArray) : Bool :=
  env.toolStatus codec == .available && env.allowTimeout &&
  match st₀.lookup codec input with
  | some _ => codec != .gzip || Model.hasGzipHeader input
  | none => true

/-- Spec-conforming pure process-outcome predicate linking decompression `Process.run` outcomes to `Model.CompressEnv`, `Model.State`, and `Model` behavior. -/
def rawDecompressCallConforms (env : Model.CompressEnv) (st₀ : Model.State) (codec : Codec)
    (opts : DecompressOptions) (input : ByteArray)
    (outcome : Except ProcessError ExecResult) : Bool :=
  match outcome with
  | .error pe =>
    !pe.message.isEmpty &&
    match pe.kind with
    | .notFound | .permissionDenied => env.toolStatus codec == .missingOrNonExec
    | .invalidInput =>
      if isResourceExhaustedProcessError pe then
        env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
      else
        env.toolStatus codec == .pathSymlinkLoop
    | .ioError => env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
    | .timedOut => rawTimedOutDecompressConforms env st₀ codec input
    | .terminatedBySignal => env.toolStatus codec == .available && env.allowExternalSignal
    | .nonZeroExit => false
    | .outputLimitExceeded =>
      env.toolStatus codec == .available &&
      match st₀.lookup codec input with
      | some expected =>
        expected.size > opts.maxOutputBytes &&
        (codec != .gzip || Model.hasGzipHeader input)
      | none => true
  | .ok res =>
    env.toolStatus codec == .available &&
    match st₀.lookup codec input with
    | some expected =>
      if res.exitCode != 0 then false
      else if res.stdout.size > opts.maxOutputBytes then
        expected.size > opts.maxOutputBytes &&
        (codec != .gzip || Model.hasGzipHeader input)
      else
        expected.size ≤ opts.maxOutputBytes &&
        res.stdout == expected &&
        (codec != .gzip || Model.hasGzipHeader input)
    | none => true

/-- Spec-conforming pure process-outcome predicate linking `--version` probe `Process.run` outcomes to `Model.CompressEnv`. -/
def rawVersionCallConforms (env : Model.CompressEnv) (codec : Codec)
    (outcome : Except ProcessError ExecResult) : Bool :=
  match outcome with
  | .error _ =>
    match env.toolStatus codec with
    | .available => env.allowTimeout || env.allowResourceIoError || env.allowExternalSignal
    | _ => true
  | .ok res =>
    match env.toolStatus codec with
    | .available =>
      if res.exitCode == 0 then true
      else env.allowTimeout || env.allowResourceIoError || env.allowExternalSignal
    | _ => res.exitCode != 0

/-- Build pure `ProcessApiM Id` whose `run` produces predetermined `procOut`. -/
def scriptedProcessApiId (procOut : Except ProcessError ExecResult) : ProcessApiM Id :=
  { mapRawError := mockProcessApi.mapRawError
    validateRequest := fun req => .ok req
    mkCommandRequest := fun program args => { program := program, args := args }
    withTextInput := fun req text => { req with stdin := text.toUTF8 }
    spawn := fun _ => .error { kind := .ioError, message := "unused" }
    awaitOutput := fun _ _ _ _ => .error { kind := .ioError, message := "unused" }
    killProcessGroup := fun _ => .ok ()
    reap := fun _ => .ok ()
    run := fun _ => procOut
    runChecked := fun _ => procOut
    runCommand := fun _ _ => procOut
    runCommandChecked := fun _ _ => procOut
    activeProcessCount := 0 }

/-- Wrapper `mkApi (scriptedProcessApiId procOut)` is sound against stateful `Model.allowedCompressStep`, `Model.allowedDecompressStep`, and `Model.allowedIsToolAvailable`. -/
def test_compress_internalApi_soundAgainstAllowedOutcome
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder Id) : runner Unit := do
  let env ← nondet Model.CompressEnv
  let st₀ ← nondet Model.State
  let codec ← nondet Codec
  let copts ← nondet CompressOptions
  let dopts ← nondet DecompressOptions
  let input ← nondet ByteArray
  let rawC ← nondet (Except ProcessError ExecResult)
  let rawC0 ← nondet (Except ProcessError ExecResult)
  let rawD ← nondet (Except ProcessError ExecResult)
  let rawD0 ← nondet (Except ProcessError ExecResult)
  let rawV ← nondet (Except ProcessError ExecResult)
  assume (rawCompressCallConforms env st₀ codec copts input rawC = true)
  assume (rawCompressCallConforms env st₀ codec {} input rawC0 = true)
  assume (rawDecompressCallConforms env st₀ codec dopts input rawD = true)
  assume (rawDecompressCallConforms env st₀ codec {} input rawD0 = true)
  assume (rawVersionCallConforms env codec rawV = true)
  let resC := (mkApi (scriptedProcessApiId rawC)).compressWith codec copts input
  let stC := match resC with | .ok c => st₀.record codec c input | .error _ => st₀
  NondetTest.assert (Model.allowedCompressStep env st₀ codec copts input resC stC = true)
  let resC0 := (mkApi (scriptedProcessApiId rawC0)).compress codec input
  let stC0 := match resC0 with | .ok c => st₀.record codec c input | .error _ => st₀
  NondetTest.assert (Model.allowedCompressStep env st₀ codec {} input resC0 stC0 = true)
  let resD := (mkApi (scriptedProcessApiId rawD)).decompressWith codec dopts input
  let stD := match resD with | .ok o => st₀.record codec input o | .error _ => st₀
  NondetTest.assert (Model.allowedDecompressStep env st₀ codec dopts input resD stD = true)
  let resD0 := (mkApi (scriptedProcessApiId rawD0)).decompress codec input
  let stD0 := match resD0 with | .ok o => st₀.record codec input o | .error _ => st₀
  NondetTest.assert (Model.allowedDecompressStep env st₀ codec {} input resD0 stD0 = true)
  NondetTest.assert
    (Model.allowedIsToolAvailable env codec
      ((mkApi (scriptedProcessApiId rawV)).isToolAvailable codec) = true)

/-- Public `Compress.*` entry points (`defaultApi`, `compress`, `decompress`, `compressWith`, `decompressWith`, `isToolAvailable`) match `mkApi proc`. -/
def test_compress_publicApi_matchesDefaultOps
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder IO)
    (dfltApi : CompressApi)
    (compressFn : Codec → ByteArray → IO (Except CompressError ByteArray))
    (decompressFn : Codec → ByteArray → IO (Except CompressError ByteArray))
    (compressWithFn : Codec → CompressOptions → ByteArray → IO (Except CompressError ByteArray))
    (decompressWithFn : Codec → DecompressOptions → ByteArray → IO (Except CompressError ByteArray))
    (isToolAvailFn : Codec → IO Bool)
    (proc : ProcessApiM IO) : runner Unit := do
  let codec ← nondet Codec
  let copts ← nondet CompressOptions
  let dopts ← nondet DecompressOptions
  let input ← nondet ByteArray
  let baseApi := mkApi proc
  NondetTest.assert (dfltApi = baseApi)
  NondetTest.assert (compressWithFn codec copts input = dfltApi.compressWith codec copts input)
  NondetTest.assert (decompressWithFn codec dopts input = dfltApi.decompressWith codec dopts input)
  NondetTest.assert (compressFn codec input = dfltApi.compress codec input)
  NondetTest.assert (decompressFn codec input = dfltApi.decompress codec input)
  NondetTest.assert (isToolAvailFn codec = dfltApi.isToolAvailable codec)

/-- `chk` (`Model.hasGzipHeader`) accepts canonical `enc .gzip` (`encodeStored .gzip`) streams and rejects `.zstd`/`.xz` cross-codec streams, legacy `.Z`/`pack`, PKZIP, and short `< 20`-byte buffers. -/
def test_compress_model_framingRejectsCrossCodecAndLegacy
    {runner} [NondetTest runner]
    (enc : Codec → ByteArray → ByteArray)
    (chk : ByteArray → Bool) : runner Unit := do
  let gzSample := enc .gzip ByteArray.empty
  let gzText := enc .gzip "hello lean-swe!\n".toUTF8
  let zstSample := enc .zstd ByteArray.empty
  let xzSample := enc .xz ByteArray.empty
  let lzwStream := ByteArray.mk #[0x1F, 0x9D, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let packStream := ByteArray.mk #[0x1F, 0x1E, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let pkzipStream := ByteArray.mk #[0x50, 0x4B, 0x03, 0x04, 0x0A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let shortGzip := gzSample.extract 0 19
  NondetTest.assert (chk gzSample = true)
  NondetTest.assert (chk gzText = true)
  NondetTest.assert (chk zstSample = false)
  NondetTest.assert (chk xzSample = false)
  NondetTest.assert (chk lzwStream = false)
  NondetTest.assert (chk packStream = false)
  NondetTest.assert (chk pkzipStream = false)
  NondetTest.assert (chk shortGzip = false)

/-- `boundFn` (`maxCompressedBound`) and `canonFn` (`hasCanonicalCompressedFraming`) enforce tight upper bounds and strict header/footer framing without false positives. -/
def test_compress_model_boundsAndCanonicalFraming_tight
    {runner} [NondetTest runner]
    (boundFn : Codec → Nat → Nat)
    (canonFn : Codec → ByteArray → Bool) : runner Unit := do
  let codec ← nondet Codec
  let gzSample := Model.encodeStored .gzip ByteArray.empty
  let zstSample := Model.encodeStored .zstd ByteArray.empty
  let xzSample := Model.encodeStored .xz ByteArray.empty
  let gzNonZeroFlg := ByteArray.mk #[
    0x1F, 0x8B, 0x08, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03,
    0x61, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let xzBadFooter := ByteArray.mk #[
    0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x00, 0xFF, 0x12, 0xD9, 0x41,
    0x00, 0x00, 0x00, 0x00, 0x1C, 0xDF, 0x44, 0x21, 0x1F, 0xB6, 0xF3, 0x7D,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x59, 0x00]
  NondetTest.assert (boundFn codec 0 ≤ 512 ∧ boundFn codec 1024 ≤ 2048 ∧ boundFn codec 65536 ≤ 70000)
  NondetTest.assert (canonFn codec (Model.encodeStored codec ByteArray.empty) = true)
  NondetTest.assert (canonFn codec ByteArray.empty = false)
  NondetTest.assert (canonFn .zstd gzSample = false ∧ canonFn .zstd xzSample = false)
  NondetTest.assert (canonFn .gzip zstSample = false ∧ canonFn .gzip xzSample = false ∧ canonFn .gzip gzNonZeroFlg = false)
  NondetTest.assert (canonFn .xz gzSample = false ∧ canonFn .xz zstSample = false ∧ canonFn .xz xzBadFooter = false)

/-- `minSzFn` (`Model.minCompressedSize`), `allowCompStepFn` (`Model.allowedCompressStep`), `allowDecStepFn` (`Model.allowedDecompressStep`), `recFn` (`Model.State.record`), and `lkFn` (`Model.State.lookup`) enforce tight minimum stream sizes, exact stateful round-trip recovery, limit enforcement, deterministic replay, and cross-codec rejection on `.gzip`/`.zstd`. -/
def test_compress_model_statefulRoundTrip_andContracts_tight
    {runner} [NondetTest runner]
    (minSzFn : Codec → Nat)
    (allowCompStepFn : Model.CompressEnv → Model.State → Codec → CompressOptions → ByteArray → Except CompressError ByteArray → Model.State → Bool)
    (allowDecStepFn : Model.CompressEnv → Model.State → Codec → DecompressOptions → ByteArray → Except CompressError ByteArray → Model.State → Bool)
    (recFn : Model.State → Codec → ByteArray → ByteArray → Model.State)
    (lkFn : Model.State → Codec → ByteArray → Option ByteArray) : runner Unit := do
  let codec ← nondet Codec
  let envAvail : Model.CompressEnv := { toolStatus := fun _ => .available }
  let plain := ByteArray.mk #[0x41, 0x42]
  let wrongPlain := ByteArray.mk #[0x43]
  let sampleStream := Model.encodeStored codec plain
  let errOutLim : CompressError :=
    { kind := .outputLimitExceeded, codec := some codec, message := "exceeded" }
  let errCorrupt : CompressError :=
    { kind := .corruptData, codec := some codec, exitCode := some 1, message := "corrupt" }
  let zstSample := Model.encodeStored .zstd ByteArray.empty
  let xzBcjSample := ByteArray.mk #[
    0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04, 0xE6, 0xD6, 0xB4, 0x46,
    0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00]
  let st1 := recFn Model.State.empty codec sampleStream plain
  let stExtXz := recFn Model.State.empty .xz xzBcjSample plain
  NondetTest.assert (minSzFn .zstd = 9 ∧ minSzFn .gzip = 20 ∧ minSzFn .xz = 32 ∧ sampleStream.size ≥ minSzFn codec)
  NondetTest.assert (lkFn Model.State.empty codec sampleStream = none ∧ lkFn st1 codec sampleStream = some plain)
  NondetTest.assert
    (allowCompStepFn envAvail Model.State.empty codec {} plain (.ok sampleStream) st1 = true ∧
     allowCompStepFn envAvail Model.State.empty codec {} plain (.ok (ByteArray.mk #[0x00])) st1 = false ∧
     allowCompStepFn envAvail Model.State.empty codec { maxOutputBytes := 4096 } plain (.error errOutLim) Model.State.empty = false)
  NondetTest.assert
    (allowDecStepFn envAvail st1 codec {} sampleStream (.ok plain) st1 = true ∧
     allowDecStepFn envAvail st1 codec {} sampleStream (.ok wrongPlain) st1 = false ∧
     allowDecStepFn envAvail st1 codec {} sampleStream (.error errCorrupt) st1 = false ∧
     allowDecStepFn envAvail st1 codec { maxOutputBytes := 1 } sampleStream (.ok plain) st1 = false ∧
     allowDecStepFn envAvail st1 codec { maxOutputBytes := 1 } sampleStream (.error errOutLim) st1 = true ∧
     allowDecStepFn envAvail st1 codec { maxOutputBytes := 1 } sampleStream (.error errCorrupt) st1 = false)
  NondetTest.assert
    (allowDecStepFn envAvail Model.State.empty .xz {} xzBcjSample (.ok plain) stExtXz = true ∧
     allowDecStepFn envAvail Model.State.empty codec {} sampleStream (.error errCorrupt) Model.State.empty = true ∧
     allowDecStepFn envAvail Model.State.empty .gzip {} (ByteArray.mk #[0x1F, 0x9D, 0x90]) (.ok plain)
       (recFn Model.State.empty .gzip (ByteArray.mk #[0x1F, 0x9D, 0x90]) plain) = false ∧
     allowDecStepFn envAvail Model.State.empty .gzip {} zstSample (.ok plain)
       (recFn Model.State.empty .gzip zstSample plain) = false)

/-- External CLI boundary assumptions for `zstd`, `xz`, and `gzip` subprocesses executed via `LeanSwe.Compress`,
    verified at runtime in `LeanSwe.Compress.RuntimeTests` with nonce-authenticated logging. -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.Compress.assume_compress_isToolAvailable_installedCodecsReportTrue"
      subject := "LeanSwe.Compress.isToolAvailable"
      formalPred? := none }
  , { name := "LeanSwe.Compress.assume_compress_roundTrip_validAndConcatenatedStreams"
      subject := "LeanSwe.Compress.compress"
      formalPred? := none }
  , { name := "LeanSwe.Compress.assume_compress_compressWith_gzipDeterministicAndOptionsRoundTrip"
      subject := "LeanSwe.Compress.compressWith"
      formalPred? := none }
  , { name := "LeanSwe.Compress.assume_compress_decompress_pythonReferenceInterop"
      subject := "LeanSwe.Compress.decompress"
      formalPred? := none }
  , { name := "LeanSwe.Compress.assume_compress_decompress_rejectsCorruptTruncatedAndTrailingGarbage"
      subject := "LeanSwe.Compress.decompress"
      formalPred? := none }
  , { name := "LeanSwe.Compress.assume_compress_defaultApi_sanitizesCodecEnvAndReportsMissingTool"
      subject := "LeanSwe.Compress.defaultApi"
      formalPred? := none }
  , { name := "LeanSwe.Compress.assume_compress_decompressWith_enforcesMaxOutputBytesOnBomb"
      subject := "LeanSwe.Compress.decompressWith"
      formalPred? := none } ]

/-- Complete `4 × 7` `(request, errorKind)` coverage matrix for `LeanSwe.Compress` (`CompressErrorKind`). -/
def errorCoverage : List (ErrorObligation CompressErrorKind) :=
  [ { request := "LeanSwe.Compress.compress"
      errorKind := .toolNotFound
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compress_toolNotFound" .real }
  , { request := "LeanSwe.Compress.compress"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compress_invalidInput" .real }
  , { request := "LeanSwe.Compress.compress"
      errorKind := .corruptData
      justification := .provedImpossible "LeanSwe.Compress.Proofs.compress_compress_never_corruptData" }
  , { request := "LeanSwe.Compress.compress"
      errorKind := .outputLimitExceeded
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compress_outputLimitExceeded" .real }
  , { request := "LeanSwe.Compress.compress"
      errorKind := .timedOut
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compress_timedOut" .mocked }
  , { request := "LeanSwe.Compress.compress"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compress_commandFailed" .mocked }
  , { request := "LeanSwe.Compress.compress"
      errorKind := .ioError
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compress_ioError" .real }
  , { request := "LeanSwe.Compress.decompress"
      errorKind := .toolNotFound
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompress_toolNotFound" .real }
  , { request := "LeanSwe.Compress.decompress"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompress_invalidInput" .real }
  , { request := "LeanSwe.Compress.decompress"
      errorKind := .corruptData
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompress_corruptData" .real }
  , { request := "LeanSwe.Compress.decompress"
      errorKind := .outputLimitExceeded
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompress_outputLimitExceeded" .real }
  , { request := "LeanSwe.Compress.decompress"
      errorKind := .timedOut
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompress_timedOut" .mocked }
  , { request := "LeanSwe.Compress.decompress"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompress_commandFailed" .mocked }
  , { request := "LeanSwe.Compress.decompress"
      errorKind := .ioError
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompress_ioError" .real }
  , { request := "LeanSwe.Compress.compressWith"
      errorKind := .toolNotFound
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_toolNotFound" .real }
  , { request := "LeanSwe.Compress.compressWith"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_invalidInput" .real }
  , { request := "LeanSwe.Compress.compressWith"
      errorKind := .corruptData
      justification := .provedImpossible "LeanSwe.Compress.Proofs.compress_compressWith_never_corruptData" }
  , { request := "LeanSwe.Compress.compressWith"
      errorKind := .outputLimitExceeded
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_outputLimitExceeded" .real }
  , { request := "LeanSwe.Compress.compressWith"
      errorKind := .timedOut
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_timedOut" .real }
  , { request := "LeanSwe.Compress.compressWith"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_commandFailed" .mocked }
  , { request := "LeanSwe.Compress.compressWith"
      errorKind := .ioError
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_ioError" .real }
  , { request := "LeanSwe.Compress.decompressWith"
      errorKind := .toolNotFound
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_toolNotFound" .real }
  , { request := "LeanSwe.Compress.decompressWith"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_invalidInput" .real }
  , { request := "LeanSwe.Compress.decompressWith"
      errorKind := .corruptData
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_corruptData" .real }
  , { request := "LeanSwe.Compress.decompressWith"
      errorKind := .outputLimitExceeded
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_outputLimitExceeded" .real }
  , { request := "LeanSwe.Compress.decompressWith"
      errorKind := .timedOut
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_timedOut" .real }
  , { request := "LeanSwe.Compress.decompressWith"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_commandFailed" .mocked }
  , { request := "LeanSwe.Compress.decompressWith"
      errorKind := .ioError
      justification := .tested "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_ioError" .real } ]

end LeanSwe.Compress
