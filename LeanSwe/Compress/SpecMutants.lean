import Core.NondetTest
import LeanSwe.Process.Types
import LeanSwe.Compress.Types
import LeanSwe.Compress.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Compress`. -/

namespace LeanSwe.Compress

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Process
  (ProcessErrorKind ProcessError ExecRequest ExecResult ProcessHandle ExecOutcome RawProcessOpsM)

private def noopCompressBuilder {m : Type → Type} [Monad m] : CompressBuilder m :=
  fun _ =>
    { compress := fun _ _ => pure (.error { kind := .ioError, message := "noop" })
      decompress := fun _ _ => pure (.error { kind := .ioError, message := "noop" })
      compressWith := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      decompressWith := fun _ _ _ => pure (.error { kind := .ioError, message := "noop" })
      isToolAvailable := fun _ => pure false }

private def buggyCompressBuilderAcceptsBadOpts : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
      compressWith := fun _ _ input => pure (.ok input)
      decompressWith := fun _ _ input => pure (.ok input) }

private def buggyCompressBuilderNoEnvSanitize : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := #[]
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← raw.spawn req with
        | .error e => return .error { kind := expectedProcessErrorKind e.kind, codec := some codec, message := "err" }
        | .ok h =>
          match ← raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes with
          | .ok (.exited res) =>
            let _ ← raw.reap h
            return .ok res.stdout
          | _ =>
            let _ ← raw.killProcessGroup h
            let _ ← raw.reap h
            return .error { kind := .ioError, codec := some codec, message := "fail" } }

private def buggyDecompressBuilderEmptyShortCircuit : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
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
        match ← raw.spawn req with
        | .error e => return .error { kind := expectedProcessErrorKind e.kind, codec := some codec, message := "err" }
        | .ok h =>
          match ← raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes with
          | .ok (.exited res) =>
            let _ ← raw.reap h
            if res.exitCode == 0 then return .ok res.stdout
            else return .error { kind := .corruptData, codec := some codec, exitCode := some res.exitCode, message := "bad" }
          | _ =>
            let _ ← raw.killProcessGroup h
            let _ ← raw.reap h
            return .error { kind := .ioError, codec := some codec, message := "fail" } }

private def buggyCompressBuilderPermDeniedAsCommandFailed : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← raw.spawn req with
        | .error _ => return .error { kind := .commandFailed, codec := some codec, message := "spawn failed" }
        | .ok h =>
          let _ ← raw.reap h
          return .ok ByteArray.empty }

private def buggyCompressBuilderNoKillOnTimeout : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some opts.maxOutputBytes }
        match ← raw.spawn req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "spawn" }
        | .ok h =>
          match ← raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes with
          | .ok (.timedOut _ _) =>
            let _ ← raw.reap h
            return .error { kind := .timedOut, codec := some codec, message := "timed out" }
          | _ =>
            let _ ← raw.reap h
            return .error { kind := .ioError, codec := some codec, message := "other" } }

private def buggyCompressBuilderGzipExit2Ok : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
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
        match ← raw.spawn req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "spawn" }
        | .ok h =>
          match ← raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes with
          | .ok (.exited res) =>
            let _ ← raw.reap h
            if res.exitCode == 0 || (codec == .gzip && res.exitCode == 2) then
              return .ok res.stdout
            else
              return .error { kind := .corruptData, codec := some codec, exitCode := some res.exitCode, message := "corrupt" }
          | _ =>
            let _ ← raw.reap h
            return .error { kind := .ioError, codec := some codec, message := "other" } }

private def buggyCompressBuilderBadIsToolAvailable : CompressBuilder (StateM MockProcState) :=
  fun _ =>
    { noopCompressBuilder mockRawOps with
      isToolAvailable := fun _ => pure false }

private def buggyCompressBuilderIgnoresOutputLimit : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := expectedSanitizedEnv codec
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some (opts.maxOutputBytes + expectedStderrPipeSlack) }
        match ← raw.spawn req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "spawn" }
        | .ok h =>
          match ← raw.awaitOutput h req.stdin req.timeoutMs req.maxOutputBytes with
          | .ok (.exited res) =>
            let _ ← raw.reap h
            if res.exitCode == 0 then return .ok res.stdout
            else return .error { kind := .commandFailed, codec := some codec, exitCode := some res.exitCode, message := "fail" }
          | _ =>
            let _ ← raw.killProcessGroup h
            let _ ← raw.reap h
            return .error { kind := .ioError, codec := some codec, message := "other" } }

private def buggyModelApiRawInput : CompressApiM (StateT Model.State (ReaderM Model.CompressEnv)) :=
  { Model.modelApi with
    compressWith := fun _ _ input => pure (.ok input) }

private def buggyModelApiForgetsRoundTrip : CompressApiM (StateT Model.State (ReaderM Model.CompressEnv)) :=
  { Model.modelApi with
    decompress := fun codec _ =>
      pure (.error { kind := .corruptData, codec := some codec, message := "forgot" }) }

private def buggyHasGzipHeaderAcceptsAll : ByteArray → Bool
  | _ => true

example : ¬ Core.AllPass (test_compress_compressWith_invalidOptionsRejectWithoutSpawn buggyCompressBuilderAcceptsBadOpts mockRawOps) := by
  intro h
  have h0 := h {} .gzip { threads := some 2 } ByteArray.empty (by decide)
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_compress_compressWith_invalidOptionsRejectWithoutSpawn buggyCompressBuilderAcceptsBadOpts mockRawOps) := by
  intro h
  have h0 := h {} .xz { threads := some 16385 } ByteArray.empty (by decide)
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_compress_decompressWith_invalidOptionsRejectWithoutSpawn buggyCompressBuilderAcceptsBadOpts mockRawOps) := by
  intro h
  have h0 := h {} .zstd { timeoutMs := 0 } ByteArray.empty (by decide)
  rcases h0.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_compress_compressWith_buildsExactExecRequest buggyCompressBuilderNoEnvSanitize) := by
  intro h
  have h0 := h .xz {} ByteArray.empty ByteArray.empty ByteArray.empty 0 (by decide)
  have hReq := h0.2.2.2.1
  dsimp [test_compress_compressWith_buildsExactExecRequest, buggyCompressBuilderNoEnvSanitize, mockRawOps,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at hReq
  cases hReq

example : ¬ Core.AllPass (test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit buggyDecompressBuilderEmptyShortCircuit) := by
  intro h
  have h0 := h .zstd {} ByteArray.empty 1 ByteArray.empty ByteArray.empty 0 (by decide)
  have hAttempts := h0.1
  dsimp [test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit,
    buggyDecompressBuilderEmptyShortCircuit, StateT.run, bind, StateT.bind, pure, StateT.pure] at hAttempts
  exact absurd hAttempts.1 (by decide)

example : ¬ Core.AllPass (test_compress_defaults_matchWithDefaultOptions
    (fun raw =>
      { noopCompressBuilder raw with
        compress := fun _ _ => pure (.ok ByteArray.empty)
        compressWith := fun _ _ _ => pure (.error { kind := .invalidInput, message := "diff" }) })
    mockRawOps) := by
  intro h
  have h0 := h {} .zstd ByteArray.empty
  have hEq := h0.1
  dsimp [StateT.run, pure, StateT.pure] at hEq
  cases hEq

example : ¬ Core.AllPass (test_compress_spawnErrors_mappedCorrectly buggyCompressBuilderPermDeniedAsCommandFailed) := by
  intro h
  have h0 := h .zstd false {} {} { kind := .permissionDenied, message := "eacces" } ByteArray.empty 0 (by decide)
  rcases h0.2.1 with ⟨e, he, hkind, _⟩
  dsimp [test_compress_spawnErrors_mappedCorrectly, buggyCompressBuilderPermDeniedAsCommandFailed, mockRawOps,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at he
  cases he
  cases hkind

example : ¬ Core.AllPass (test_compress_awaitOutcomes_cleanedUpAndClassified buggyCompressBuilderNoKillOnTimeout) := by
  intro h
  have h0 := h .zstd false {} {} ByteArray.empty ByteArray.empty ByteArray.empty 9 0 0 (by decide) (by decide)
  have hKills := h0.1
  dsimp [test_compress_awaitOutcomes_cleanedUpAndClassified, buggyCompressBuilderNoKillOnTimeout, mockRawOps,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at hKills
  exact absurd hKills.2.1 (by decide)

example : ¬ Core.AllPass (test_compress_exitCodes_compressVsDecompress_andStderr buggyCompressBuilderGzipExit2Ok) := by
  intro h
  have h0 := h .gzip 2 ByteArray.empty "gzip: stdin: decompression OK, trailing garbage ignored\n".toUTF8 (by decide)
  rcases h0.2.1 with ⟨e, he, _⟩
  dsimp [test_compress_exitCodes_compressVsDecompress_andStderr, buggyCompressBuilderGzipExit2Ok, mockRawOps,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at he
  cases he

example : ¬ Core.AllPass (test_compress_isToolAvailable_checksVersionAndCleansUp buggyCompressBuilderBadIsToolAvailable) := by
  intro h
  have h0 := h .zstd true 0 0
  have hAttempts := h0.1
  dsimp [test_compress_isToolAvailable_checksVersionAndCleansUp, buggyCompressBuilderBadIsToolAvailable,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at hAttempts
  exact absurd hAttempts.1 (by decide)

example : ¬ Core.AllPass (test_compress_compressWith_buildsExactExecRequest buggyCompressBuilderIgnoresOutputLimit) := by
  intro h
  have h0 := h .zstd { maxOutputBytes := 1 } ByteArray.empty (ByteArray.mk #[1, 2]) ByteArray.empty 0 (by decide)
  have hRes := h0.1
  dsimp [test_compress_compressWith_buildsExactExecRequest, buggyCompressBuilderIgnoresOutputLimit, mockRawOps,
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
    (fun raw =>
      { noopCompressBuilder raw with
        compressWith := fun _ _ input => pure (.ok input) })) := by
  intro h
  let okRes : Except ProcessError ExecOutcome :=
    .ok (.exited { exitCode := 0, stdout := Model.encodeStored .zstd ByteArray.empty, stderr := ByteArray.empty })
  let okD : Except ProcessError ExecOutcome :=
    .ok (.exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty })
  have h0 := h { toolStatus := fun _ => .available } Model.State.empty .zstd { maxOutputBytes := 0 } {} ByteArray.empty
    0 0 0 okRes okRes okD okD okD
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_compress_publicApi_matchesDefaultOps
    noopCompressBuilder
    (noopCompressBuilder { mapRawError := mockRawOps.mapRawError
                           spawn := fun _ => pure (.error { kind := .notFound, message := "m" })
                           awaitOutput := fun _ _ _ _ => pure (.error { kind := .ioError, message := "m" })
                           killProcessGroup := fun _ => pure (.ok ())
                           reap := fun _ => pure (.ok ())
                           activeProcessCount := pure 0 })
    (fun _ _ => pure (.error { kind := .ioError, message := "noop" }))
    (fun _ _ => pure (.ok ByteArray.empty))
    (fun _ _ _ => pure (.error { kind := .ioError, message := "noop" }))
    (fun _ _ _ => pure (.error { kind := .ioError, message := "noop" }))
    (fun _ => pure false)
    { mapRawError := mockRawOps.mapRawError
      spawn := fun _ => pure (.error { kind := .notFound, message := "m" })
      awaitOutput := fun _ _ _ _ => pure (.error { kind := .ioError, message := "m" })
      killProcessGroup := fun _ => pure (.ok ())
      reap := fun _ => pure (.ok ())
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
    ByteArray.empty 0 (by decide)
  rcases h0.2.1 with ⟨e, he, hkind, _⟩
  dsimp [test_compress_spawnErrors_mappedCorrectly, buggyCompressBuilderNoEnvSanitize, mockRawOps,
    StateT.run, bind, StateT.bind, pure, StateT.pure] at he
  cases he
  dsimp [expectedProcessErrorKindFor, isResourceExhaustedProcessError, expectedResourceOrPathIoErrno,
    expectedProcessErrorKind] at hkind
  cases hkind

private def buggyCompressBuilderStderrOomAsIoError : CompressBuilder (StateM MockProcState) :=
  fun raw =>
    { noopCompressBuilder raw with
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
  fun raw =>
    { noopCompressBuilder raw with
      compressWith := fun codec opts input => do
        let req : ExecRequest :=
          { program := codecProgram codec
            args := expectedCompressArgs codec opts
            env := #[("XZ_OPT", none), ("XZ_DEFAULTS", none), ("GZIP", none)]
            inheritEnv := true
            stdin := input
            timeoutMs := some opts.timeoutMs
            maxOutputBytes := some (opts.maxOutputBytes + 1073741824) }
        match ← raw.spawn req with
        | .error _ => return .error { kind := .ioError, codec := some codec, message := "spawn" }
        | .ok h =>
          let _ ← raw.reap h
          return .ok ByteArray.empty }

example : ¬ Core.AllPass (test_compress_compressWith_buildsExactExecRequest buggyCompressBuilderPartialEnvAndBloatedSlack) := by
  intro h
  have h0 := h .zstd {} ByteArray.empty ByteArray.empty ByteArray.empty 0 (by decide)
  have hReq := h0.2.2.2.1
  dsimp [test_compress_compressWith_buildsExactExecRequest, buggyCompressBuilderPartialEnvAndBloatedSlack,
    mockRawOps, expectedSanitizedEnv, expectedStderrPipeSlack, StateT.run, bind, StateT.bind, pure, StateT.pure] at hReq
  have hEnv := congrArg (fun xs => xs.map ExecRequest.env) hReq
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
