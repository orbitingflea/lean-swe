import Core.NondetTest
import Core.Assumptions
import LeanSwe.Process.Types
import LeanSwe.Compress.Types
import LeanSwe.Compress.Model

namespace LeanSwe.Compress

open Core (NondetTest AssumptionObligation ErrorObligation)
open Core.NondetTest
open LeanSwe.Process
  (ProcessErrorKind ProcessError ExecRequest ExecResult ProcessHandle ExecOutcome RawProcessOpsM)

/-- Builder function constructing a `CompressApiM m` from an injected `RawProcessOpsM m`. -/
abbrev CompressBuilder (m : Type → Type) :=
  RawProcessOpsM m → CompressApiM m

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
  | .zstd => #["-d", "-c", "-q", "--no-progress"]
  | .xz => #["-d", "-c", "-q"]
  | .gzip => #["-d", "-c", "-n"]

/-- Expected `CompressError.stderr` decoding: `none` on empty or invalid UTF-8, `some s` on non-empty valid UTF-8. -/
def expectedStderr (bs : ByteArray) : Option String :=
  if bs.isEmpty then none else String.fromUTF8? bs

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

/-- Deterministic mock process state for `RawProcessOpsM (StateM MockProcState)` spec tests. -/
structure MockProcState where
  /-- Scripted response for `raw.spawn`. -/
  onSpawn : ExecRequest → Except ProcessError ProcessHandle :=
    fun _ => .ok { handleId := 1, pid := 100, pgid := 100 }
  /-- Scripted response for `raw.awaitOutput`. -/
  onAwait : ProcessHandle → ByteArray → Option Nat → Option Nat → Except ProcessError ExecOutcome :=
    fun _ stdin _ _ => .ok (.exited { exitCode := 0, stdout := stdin, stderr := ByteArray.empty })
  /-- Scripted response for `raw.reap`. -/
  onReap : ProcessHandle → Except ProcessError Unit := fun _ => .ok ()
  /-- Recorded `ExecRequest` values passed to `raw.spawn` in invocation order. -/
  spawned : List ExecRequest := []
  /-- Total `raw.spawn` calls attempted. -/
  spawnAttempts : Nat := 0
  /-- Total `raw.killProcessGroup` calls observed. -/
  killCount : Nat := 0
  /-- Total `raw.reap` calls observed. -/
  reapCount : Nat := 0
  /-- Active un-reaped handle count. -/
  activeHandles : Nat := 0

/-- Deterministic `RawProcessOpsM (StateM MockProcState)` backed by `MockProcState`. -/
def mockRawOps : RawProcessOpsM (StateM MockProcState) :=
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
    spawn := fun req => do
      let s ← get
      set { s with spawned := s.spawned ++ [req], spawnAttempts := s.spawnAttempts + 1 }
      match s.onSpawn req with
      | .error e => return .error e
      | .ok h =>
        modify fun s' => { s' with activeHandles := s'.activeHandles + 1 }
        return .ok h
    awaitOutput := fun h stdin timeoutMs maxOutputBytes => do
      let s ← get
      return s.onAwait h stdin timeoutMs maxOutputBytes
    killProcessGroup := fun _ => do
      modify fun s => { s with killCount := s.killCount + 1 }
      return .ok ()
    reap := fun h => do
      let s ← get
      set { s with reapCount := s.reapCount + 1, activeHandles := s.activeHandles - 1 }
      return s.onReap h
    activeProcessCount := do
      return (← get).activeHandles }

/-- Invalid `CompressOptions` or `input.size > maxInputBytes` fail with `.invalidInput` without calling `raw` or mutating state. -/
def test_compress_compressWith_invalidOptionsRejectWithoutSpawn
    {S : Type} {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM S))
    (raw : RawProcessOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let codec ← nondet Codec
  let opts ← nondet CompressOptions
  let input ← nondet ByteArray
  assume (isValidCompressInput codec opts input = false)
  let (res, s₁) := ((mkApi raw).compressWith codec opts input).run s₀
  NondetTest.assert
    (∃ e, res = .error e ∧
      e.kind = .invalidInput ∧
      e.codec = some codec ∧
      e.exitCode = none ∧
      e.stderr = none ∧
      e.message ≠ "")
  NondetTest.assert (s₁ = s₀)

/-- Invalid `DecompressOptions` or `input.size > maxInputBytes` fail with `.invalidInput` without calling `raw` or mutating state. -/
def test_compress_decompressWith_invalidOptionsRejectWithoutSpawn
    {S : Type} {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM S))
    (raw : RawProcessOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let codec ← nondet Codec
  let opts ← nondet DecompressOptions
  let input ← nondet ByteArray
  assume (isValidDecompressInput opts input = false)
  let (res, s₁) := ((mkApi raw).decompressWith codec opts input).run s₀
  NondetTest.assert
    (∃ e, res = .error e ∧
      e.kind = .invalidInput ∧
      e.codec = some codec ∧
      e.exitCode = none ∧
      e.stderr = none ∧
      e.message ≠ "")
  NondetTest.assert (s₁ = s₀)

/-- Valid `compressWith` builds exact direct `execvp` args, strips inherited codec env vars, passes `stdin` (including empty), reaps cleanly, and returns stdout. -/
def test_compress_compressWith_buildsExactExecRequest
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let opts ← nondet CompressOptions
  let input ← nondet ByteArray
  let outBytes ← nondet ByteArray
  let active₀ ← nondet Nat
  assume (isValidCompressInput codec opts input = true)
  let s₀ : MockProcState :=
    { activeHandles := active₀
      onAwait := fun _ _ _ _ =>
        .ok (.exited { exitCode := 0, stdout := outBytes, stderr := ByteArray.empty }) }
  let (res, s₁) := ((mkApi mockRawOps).compressWith codec opts input).run s₀
  NondetTest.assert (res = .ok outBytes)
  NondetTest.assert (s₁.spawnAttempts = 1 ∧ s₁.reapCount = 1 ∧ s₁.killCount = 0)
  NondetTest.assert (s₁.activeHandles = active₀)
  NondetTest.assert (s₁.spawned =
    [{ program := codecProgram codec
       args := expectedCompressArgs codec opts
       cwd := none
       env := codecSanitizedEnv
       inheritEnv := true
       stdin := input
       timeoutMs := some opts.timeoutMs
       maxOutputBytes := some opts.maxOutputBytes }])

/-- Valid `decompressWith` always invokes the codec subprocess (even for `ByteArray.empty`), strips codec env vars, and handles exit `0` vs non-zero `.corruptData`. -/
def test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let opts ← nondet DecompressOptions
  let input ← nondet ByteArray
  let exitCode ← nondet Int
  let outBytes ← nondet ByteArray
  let errBytes ← nondet ByteArray
  let active₀ ← nondet Nat
  assume (isValidDecompressInput opts input = true)
  let s₀ : MockProcState :=
    { activeHandles := active₀
      onAwait := fun _ _ _ _ =>
        .ok (.exited { exitCode := exitCode, stdout := outBytes, stderr := errBytes }) }
  let (res, s₁) := ((mkApi mockRawOps).decompressWith codec opts input).run s₀
  NondetTest.assert (s₁.spawnAttempts = 1 ∧ s₁.reapCount = 1 ∧ s₁.killCount = 0)
  NondetTest.assert (s₁.activeHandles = active₀)
  NondetTest.assert (s₁.spawned =
    [{ program := codecProgram codec
       args := expectedDecompressArgs codec
       cwd := none
       env := codecSanitizedEnv
       inheritEnv := true
       stdin := input
       timeoutMs := some opts.timeoutMs
       maxOutputBytes := some opts.maxOutputBytes }])
  if exitCode == 0 then
    NondetTest.assert (res = .ok outBytes)
  else
    NondetTest.assert
      (∃ e, res = .error e ∧
        e.kind = .corruptData ∧
        e.codec = some codec ∧
        e.exitCode = some exitCode ∧
        e.stderr = expectedStderr errBytes ∧
        e.message ≠ "")

/-- `compress` and `decompress` are equivalent to `compressWith _ {}` and `decompressWith _ {}` for any `raw`. -/
def test_compress_defaults_matchWithDefaultOptions
    {S : Type} {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM S))
    (raw : RawProcessOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let codec ← nondet Codec
  let input ← nondet ByteArray
  let api := mkApi raw
  NondetTest.assert ((api.compress codec input).run s₀ = (api.compressWith codec {} input).run s₀)
  NondetTest.assert ((api.decompress codec input).run s₀ = (api.decompressWith codec {} input).run s₀)

/-- `spawn` errors (`notFound`/`permissionDenied` → `.toolNotFound`, etc.) map completely with preserved non-empty messages and no leaked handles. -/
def test_compress_spawnErrors_mappedCorrectly
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let isDecompress ← nondet Bool
  let pe ← nondet ProcessError
  let input ← nondet ByteArray
  let active₀ ← nondet Nat
  let s₀ : MockProcState :=
    { activeHandles := active₀
      onSpawn := fun _ => .error pe }
  let api := mkApi mockRawOps
  let (res, s₁) :=
    if isDecompress then
      (api.decompressWith codec {} input).run s₀
    else
      (api.compressWith codec {} input).run s₀
  NondetTest.assert (s₁.spawnAttempts = 1 ∧ s₁.activeHandles = active₀)
  NondetTest.assert
    (∃ e, res = .error e ∧
      e.kind = expectedProcessErrorKind pe.kind ∧
      e.codec = some codec ∧
      e.exitCode = pe.exitCode ∧
      e.stderr = (pe.stderr.bind expectedStderr) ∧
      e.message ≠ "" ∧
      (pe.message = "" ∨ e.message = pe.message))

/-- `awaitOutput` abnormal outcomes (`.timedOut`, `.outputLimitExceeded`, `.signaled`, `.error`) clean up process groups and classify errors cleanly. -/
def test_compress_awaitOutcomes_cleanedUpAndClassified
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let isDecompress ← nondet Bool
  let input ← nondet ByteArray
  let outBytes ← nondet ByteArray
  let errBytes ← nondet ByteArray
  let sig ← nondet Int
  let active₀ ← nondet Nat
  let outcomeKind ← nondet Nat
  assume (outcomeKind < 4)
  let outcomeRes : Except ProcessError ExecOutcome :=
    if outcomeKind == 0 then
      .ok (.timedOut outBytes errBytes)
    else if outcomeKind == 1 then
      .ok (.outputLimitExceeded outBytes errBytes)
    else if outcomeKind == 2 then
      .ok (.signaled sig outBytes errBytes)
    else
      .error { kind := .ioError, message := "pipe read failed" }
  let expectedKind : CompressErrorKind :=
    if outcomeKind == 0 then .timedOut
    else if outcomeKind == 1 then .outputLimitExceeded
    else if outcomeKind == 2 then .commandFailed
    else .ioError
  let s₀ : MockProcState :=
    { activeHandles := active₀
      onAwait := fun _ _ _ _ => outcomeRes }
  let api := mkApi mockRawOps
  let (res, s₁) :=
    if isDecompress then
      (api.decompressWith codec {} input).run s₀
    else
      (api.compressWith codec {} input).run s₀
  NondetTest.assert (s₁.spawnAttempts = 1 ∧ s₁.killCount = 1 ∧ s₁.reapCount = 1)
  NondetTest.assert (s₁.activeHandles = active₀)
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
    { onAwait := fun _ _ _ _ =>
        .ok (.exited { exitCode := exitCode, stdout := ByteArray.empty, stderr := errBytes }) }
  let api := mkApi mockRawOps
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
def test_compress_isToolAvailable_checksVersionAndCleansUp
    {runner} [NondetTest runner]
    (mkApi : CompressBuilder (StateM MockProcState)) : runner Unit := do
  let codec ← nondet Codec
  let spawnOk ← nondet Bool
  let exitCode ← nondet Int
  let active₀ ← nondet Nat
  let s₀ : MockProcState :=
    { activeHandles := active₀
      onSpawn := fun _ =>
        if spawnOk then .ok { handleId := 1, pid := 100, pgid := 100 }
        else .error { kind := .notFound, program := some (codecProgram codec), message := "missing" }
      onAwait := fun _ _ _ _ =>
        .ok (.exited { exitCode := exitCode, stdout := ByteArray.empty, stderr := ByteArray.empty }) }
  let (avail, s₁) := ((mkApi mockRawOps).isToolAvailable codec).run s₀
  NondetTest.assert (s₁.spawnAttempts = 1 ∧ s₁.activeHandles = active₀)
  NondetTest.assert (s₁.spawned =
    [{ program := codecProgram codec
       args := #["--version"]
       cwd := none
       env := codecSanitizedEnv
       inheritEnv := true
       stdin := ByteArray.empty
       timeoutMs := some 5000
       maxOutputBytes := some 65536 }])
  if spawnOk then
    NondetTest.assert (s₁.reapCount = 1)
    NondetTest.assert (avail = (exitCode == 0))
  else
    NondetTest.assert (avail = false)

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
