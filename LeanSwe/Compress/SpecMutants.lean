import Core.NondetTest
import LeanSwe.Process.Types
import LeanSwe.Compress.Types
import LeanSwe.Compress.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Compress`. -/

namespace LeanSwe.Compress

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Process
  (ProcessErrorKind ProcessError ExecRequest ExecResult ProcessApiM)

private def noopCompressBuilder {m : Type → Type} [Monad m] : CompressBuilder m :=
  fun _ =>
    { compress := fun _ _ => pure (.error { kind := .ioError, message := "noop" })
      decompress := fun _ _ => pure (.error { kind := .ioError, message := "noop" })
      compressWith := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      decompressWith := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      isToolAvailable := fun _ => pure false }

private def buggyCompressBuilderAcceptsBadOpts : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun _ _ input => pure (.ok input)
      decompressWith := fun _ _ input => pure (.ok input) }

private def buggyCompressBuilderNoEnvSanitize : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := #[]
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← proc.run req with
        | .error e => return .error { kind := expectedProcessErrorKind e.kind, codec := some codec, message := "err" }
        | .ok res => return .ok res.stdout }

private def buggyDecompressBuilderEmptyShortCircuit : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      decompressWith := fun codec opts input => do
        if input.isEmpty then
          return .ok ByteArray.empty
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedDecompressArgs codec
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← proc.run req with
        | .error e => return .error { kind := expectedProcessErrorKind e.kind, codec := some codec, message := "err" }
        | .ok res =>
          if res.exitCode == 0 then return .ok res.stdout
          else return .error { kind := .corruptData, codec := some codec, exitCode := some res.exitCode, message := "bad" } }

private def buggyCompressBuilderPermDeniedAsCommandFailed : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← proc.run req with
        | .error _ => return .error { kind := .commandFailed, codec := some codec, message := "run failed" }
        | .ok _ => return .ok ByteArray.empty }

private def buggyCompressBuilderMisclassifiesTimeout : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← proc.run req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "other" }
        | .ok res => return .ok res.stdout }

private def buggyCompressBuilderGzipExit2Ok : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun codec _ _ =>
        pure (.error { kind := .commandFailed, codec := some codec, exitCode := some 1, message := "fail" })
      decompressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedDecompressArgs codec
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← proc.run req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "run" }
        | .ok res =>
          if res.exitCode == 0 || (codec == .gzip && res.exitCode == 2) then
            return .ok res.stdout
          else
            return .error { kind := .corruptData, codec := some codec, exitCode := some res.exitCode, message := "corrupt" } }

private def buggyCompressBuilderBadIsToolAvailable : CompressBuilder (StateM MockProcState) :=
  fun _ =>
    { noopCompressBuilder mockProcessApi with
      isToolAvailable := fun _ => pure false }

private def buggyCompressBuilderIgnoresOutputLimit : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some (opts.maxOutputBytes + expectedStderrPipeSlack) }
        match ← proc.run req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "run" }
        | .ok res =>
          if res.exitCode == 0 then return .ok res.stdout
          else return .error { kind := .commandFailed, codec := some codec, exitCode := some res.exitCode, message := "fail" } }

private def buggyModelApiRawInput : CompressApiM (StateT Model.State (ReaderM Model.CompressEnv)) :=
  { Model.modelApi with
    compressWith := fun _ _ input => pure (.ok input) }

private def buggyModelApiForgetsRoundTrip : CompressApiM (StateT Model.State (ReaderM Model.CompressEnv)) :=
  { Model.modelApi with
    decompress := fun codec _ =>
      pure (.error { kind := .corruptData, codec := some codec, message := "forgot" }) }

private def buggyHasGzipHeaderAcceptsAll : ByteArray → Bool
  | _ => true

example : ¬ Core.AllPass (test_compress_compressWith_invalidOptionsRejectWithoutSpawn buggyCompressBuilderAcceptsBadOpts mockProcessApi) := by
  intro h
  have h0 := h {} .gzip { threads := some 2 } ByteArray.empty (by decide)
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_compress_compressWith_invalidOptionsRejectWithoutSpawn buggyCompressBuilderAcceptsBadOpts mockProcessApi) := by
  intro h
  have h0 := h {} .xz { threads := some 16385 } ByteArray.empty (by decide)
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_compress_decompressWith_invalidOptionsRejectWithoutSpawn buggyCompressBuilderAcceptsBadOpts mockProcessApi) := by
  intro h
  have h0 := h {} .zstd { timeoutMs := 0 } ByteArray.empty (by decide)
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_compress_compressWith_buildsExactExecRequest buggyCompressBuilderNoEnvSanitize) := by
  intro h
  have h0 := h .xz {} ByteArray.empty ByteArray.empty ByteArray.empty (by decide)
  have hReq := h0.2.2.1
  dsimp [test_compress_compressWith_buildsExactExecRequest, buggyCompressBuilderNoEnvSanitize, mockProcessApi,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at hReq
  cases hReq

example : ¬ Core.AllPass (test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit buggyDecompressBuilderEmptyShortCircuit) := by
  intro h
  have h0 := h .zstd {} ByteArray.empty 1 ByteArray.empty ByteArray.empty (by decide)
  have hAttempts := h0.1
  dsimp [test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit,
    buggyDecompressBuilderEmptyShortCircuit, StateT.run, bind, StateT.bind, pure, StateT.pure] at hAttempts
  exact absurd hAttempts (by decide)

example : ¬ Core.AllPass (test_compress_defaults_matchWithDefaultOptions
    (fun proc =>
      { noopCompressBuilder proc with
        compress := fun _ _ => pure (.ok ByteArray.empty)
        compressWith := fun _ _ _ => pure (.error { kind := .invalidInput, message := "diff" }) })
    mockProcessApi) := by
  intro h
  have h0 := h {} .zstd ByteArray.empty
  have hEq := h0.1
  dsimp [StateT.run, pure, StateT.pure] at hEq
  cases hEq

example : ¬ Core.AllPass (test_compress_spawnErrors_mappedCorrectly buggyCompressBuilderPermDeniedAsCommandFailed) := by
  intro h
  have h0 := h .zstd false {} {} { kind := .permissionDenied, message := "eacces" } ByteArray.empty (by decide)
  rcases h0.2.1 with ⟨e, he, hkind, _⟩
  dsimp [test_compress_spawnErrors_mappedCorrectly, buggyCompressBuilderPermDeniedAsCommandFailed, mockProcessApi,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at he
  cases he
  cases hkind

example : ¬ Core.AllPass (test_compress_awaitOutcomes_classified buggyCompressBuilderMisclassifiesTimeout) := by
  intro h
  have h0 := h .zstd false {} {} ByteArray.empty ByteArray.empty ByteArray.empty 9 0 (by decide) (by decide)
  rcases h0.2.1 with ⟨e, he, hkind, _⟩
  dsimp [test_compress_awaitOutcomes_classified, buggyCompressBuilderMisclassifiesTimeout, mockProcessApi,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at he hkind
  cases he
  cases hkind

example : ¬ Core.AllPass (test_compress_exitCodes_compressVsDecompress_andStderr buggyCompressBuilderGzipExit2Ok) := by
  intro h
  have h0 := h .gzip 2 ByteArray.empty "gzip: stdin: decompression OK, trailing garbage ignored\n".toUTF8 (by decide)
  rcases h0.2.1 with ⟨e, he, _⟩
  dsimp [test_compress_exitCodes_compressVsDecompress_andStderr, buggyCompressBuilderGzipExit2Ok, mockProcessApi,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at he
  cases he

example : ¬ Core.AllPass (test_compress_isToolAvailable_checksVersion buggyCompressBuilderBadIsToolAvailable) := by
  intro h
  have h0 := h .zstd true 0
  have hAttempts := h0.1
  dsimp [test_compress_isToolAvailable_checksVersion, buggyCompressBuilderBadIsToolAvailable,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at hAttempts
  exact absurd hAttempts (by decide)

example : ¬ Core.AllPass (test_compress_compressWith_buildsExactExecRequest buggyCompressBuilderIgnoresOutputLimit) := by
  intro h
  have h0 := h .zstd { maxOutputBytes := 1 } ByteArray.empty (ByteArray.mk #[1, 2]) ByteArray.empty (by decide)
  have hRes := h0.1
  dsimp [test_compress_compressWith_buildsExactExecRequest, buggyCompressBuilderIgnoresOutputLimit, mockProcessApi,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at hRes
  rcases hRes with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_compress_modelApi_soundAgainstAllowedOutcome buggyModelApiRawInput) := by
  intro h
  have h0 := h {} .zstd {} {} ByteArray.empty ByteArray.empty
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_compress_modelApi_soundAgainstAllowedOutcome buggyModelApiForgetsRoundTrip) := by
  intro h
  have h0 := h {} .zstd {} {} ByteArray.empty ByteArray.empty
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_compress_model_framingRejectsCrossCodecAndLegacy
    Model.encodeStored buggyHasGzipHeaderAcceptsAll) := by
  intro h
  exact absurd h.2.2.1 (by decide)

example : ¬ Core.AllPass (test_compress_internalApi_soundAgainstAllowedOutcome
    (fun proc =>
      { noopCompressBuilder proc with
        compressWith := fun _ _ input => pure (.ok input) })) := by
  intro h
  let okRes : Except ProcessError ExecResult :=
    .ok { exitCode := 0, stdout := Model.encodeStored .zstd ByteArray.empty, stderr := ByteArray.empty }
  let okD : Except ProcessError ExecResult :=
    .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  have h0 := h { toolStatus := fun _ => .available } Model.State.empty .zstd { maxOutputBytes := 0 } {} ByteArray.empty
    okRes okRes okD okD okD
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_compress_publicApi_matchesDefaultOps
    noopCompressBuilder
    (noopCompressBuilder { mapRawError := mockProcessApi.mapRawError
                           validateRequest := fun req => .ok req
                           mkCommandRequest := fun program args => { program := program, args := args }
                           withTextInput := fun req text => { req with stdin := text.toUTF8 }
                           spawn := fun _ => pure (.error { kind := .notFound, message := "m" })
                           awaitOutput := fun _ _ _ _ => pure (.error { kind := .notFound, message := "m" })
                           killProcessGroup := fun _ => pure (.ok ())
                           reap := fun _ => pure (.ok ())
                           run := fun _ => pure (.error { kind := .notFound, message := "m" })
                           runChecked := fun _ => pure (.error { kind := .notFound, message := "m" })
                           runCommand := fun _ _ => pure (.error { kind := .notFound, message := "m" })
                           runCommandChecked := fun _ _ => pure (.error { kind := .notFound, message := "m" })
                           activeProcessCount := pure 0 })
    (fun _ _ => pure (.error { kind := .ioError, message := "noop" }))
    (fun _ _ => pure (.ok ByteArray.empty))
    (fun _ _ _ => pure (.error { kind := .ioError, message := "noop" }))
    (fun _ _ _ => pure (.error { kind := .ioError, message := "noop" }))
    (fun _ => pure false)
    { mapRawError := mockProcessApi.mapRawError
      validateRequest := fun req => .ok req
      mkCommandRequest := fun program args => { program := program, args := args }
      withTextInput := fun req text => { req with stdin := text.toUTF8 }
      spawn := fun _ => pure (.error { kind := .notFound, message := "m" })
      awaitOutput := fun _ _ _ _ => pure (.error { kind := .notFound, message := "m" })
      killProcessGroup := fun _ => pure (.ok ())
      reap := fun _ => pure (.ok ())
      run := fun _ => pure (.error { kind := .notFound, message := "m" })
      runChecked := fun _ => pure (.error { kind := .notFound, message := "m" })
      runCommand := fun _ _ => pure (.error { kind := .notFound, message := "m" })
      runCommandChecked := fun _ _ => pure (.error { kind := .notFound, message := "m" })
      activeProcessCount := pure 0 }) := by
  intro h
  have h0 := h .zstd {} {} ByteArray.empty
  have hDec := h0.2.2.2.2.1
  dsimp [noopCompressBuilder] at hDec
  rcases (inferInstance : Nonempty (Void IO.RealWorld)) with ⟨w⟩
  have hEval := congrArg (fun x => x w) hDec
  cases hEval

example : ¬ Core.AllPass (test_compress_spawnErrors_mappedCorrectly buggyCompressBuilderNoEnvSanitize) := by
  intro h
  have h0 := h .zstd false {} {} { kind := .invalidInput, errnoCode := some 11, message := "resource temporarily unavailable" }
    ByteArray.empty (by decide)
  rcases h0.2.1 with ⟨e, he, hkind, _⟩
  dsimp [test_compress_spawnErrors_mappedCorrectly, buggyCompressBuilderNoEnvSanitize, mockProcessApi,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at he
  cases he
  dsimp [expectedProcessErrorKindFor, isResourceExhaustedProcessError, expectedResourceOrPathIoErrno,
    expectedProcessErrorKind] at hkind
  cases hkind

private def buggyCompressBuilderStderrOomAsIoError : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun codec _ _ =>
        pure (.error { kind := .ioError, codec := some codec, message := "io" })
      decompressWith := fun codec _ _ =>
        pure (.error { kind := .ioError, codec := some codec, message := "io" }) }

example : ¬ Core.AllPass (test_compress_exitCodes_compressVsDecompress_andStderr buggyCompressBuilderStderrOomAsIoError) := by
  intro h
  have h0 := h .gzip 1 ByteArray.empty "\ngzip: memory_exhausted\n".toUTF8 (by decide)
  rcases h0.2.1 with ⟨de, hde, hdkind, _⟩
  dsimp [test_compress_exitCodes_compressVsDecompress_andStderr, buggyCompressBuilderStderrOomAsIoError,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at hde hdkind
  cases hde
  exact absurd hdkind (by decide)

private def buggyCompressBuilderPartialEnvAndBloatedSlack : CompressBuilder (StateM MockProcState) :=
  fun proc =>
    { noopCompressBuilder proc with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := #[("XZ_OPT", none), ("XZ_DEFAULTS", none), ("GZIP", none)]
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some (opts.maxOutputBytes + 1073741824) }
        match ← proc.run req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "run" }
        | .ok _ => return .ok ByteArray.empty }

example : ¬ Core.AllPass (test_compress_compressWith_buildsExactExecRequest buggyCompressBuilderPartialEnvAndBloatedSlack) := by
  intro h
  have h0 := h .zstd {} ByteArray.empty ByteArray.empty ByteArray.empty (by decide)
  have hReq := h0.2.2.1
  dsimp [test_compress_compressWith_buildsExactExecRequest, buggyCompressBuilderPartialEnvAndBloatedSlack,
    mockProcessApi, expectedSanitizedEnv, expectedStderrPipeSlack, StateT.run, bind, StateT.bind, pure, StateT.pure] at hReq
  have hEnv := congrArg (fun xs => xs.map (·.env)) hReq
  exact absurd hEnv (by decide)

example : ¬ Core.AllPass (test_compress_model_boundsAndCanonicalFraming_tight
    (fun _ n => n + 100000000) Model.hasCanonicalCompressedFraming) := by
  intro h
  have h0 := h .zstd
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_compress_model_boundsAndCanonicalFraming_tight
    Model.maxCompressedBound (fun _ _ => true)) := by
  intro h
  have h0 := h .zstd
  exact absurd h0.2.2.1 (by decide)

example : ¬ Core.AllPass (test_compress_model_statefulRoundTrip_andContracts_tight
    (fun _ => 0)
    Model.allowedCompressStep Model.allowedDecompressStep
    Model.State.record Model.State.lookup) := by
  intro h
  have h0 := h .zstd
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_compress_model_statefulRoundTrip_andContracts_tight
    Model.minCompressedSize
    (fun _ _ _ _ _ _ _ => true) Model.allowedDecompressStep
    Model.State.record Model.State.lookup) := by
  intro h
  have h0 := h .zstd
  exact absurd h0.2.2.1.2.1 (by decide)

example : ¬ Core.AllPass (test_compress_model_statefulRoundTrip_andContracts_tight
    Model.minCompressedSize
    Model.allowedCompressStep (fun _ _ _ _ _ _ _ => true)
    Model.State.record Model.State.lookup) := by
  intro h
  have h0 := h .zstd
  exact absurd h0.2.2.2.1.2.1 (by decide)

example : ¬ Core.AllPass (test_compress_model_statefulRoundTrip_andContracts_tight
    Model.minCompressedSize
    Model.allowedCompressStep Model.allowedDecompressStep
    (fun st _ _ _ => st) Model.State.lookup) := by
  intro h
  have h0 := h .zstd
  exact absurd h0.2.1.2 (by decide)

example : ¬ Core.AllPass (test_compress_model_statefulRoundTrip_andContracts_tight
    Model.minCompressedSize
    Model.allowedCompressStep Model.allowedDecompressStep
    Model.State.record (fun _ _ _ => none)) := by
  intro h
  have h0 := h .zstd
  exact absurd h0.2.1.2 (by decide)

end LeanSwe.Compress
