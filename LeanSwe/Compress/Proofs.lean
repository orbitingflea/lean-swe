import LeanSwe.Compress.Types
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSwe.Compress.SpecTests

namespace LeanSwe.Compress.Proofs

open Core
open Core.NondetTest
open LeanSwe.Process
open LeanSwe.Compress

private theorem validateCompressOptions_false_implies_error (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) (h : isValidCompressInput codec opts input = false) :
    ∃ e, Internal.validateCompressOptions codec opts input = .error e ∧
      e.kind = .invalidInput ∧ e.codec = some codec ∧
      e.exitCode = none ∧ e.stderr = none ∧ e.message ≠ "" := by
  unfold Internal.validateCompressOptions
  cases ht : (opts.timeoutMs == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases ho : (opts.maxOutputBytes == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ht0 : opts.timeoutMs > 0 := by
        cases htv : opts.timeoutMs with
        | zero => rw [htv] at ht; cases ht
        | succ _ => omega
      have ho0 : opts.maxOutputBytes > 0 := by
        cases hov : opts.maxOutputBytes with
        | zero => rw [hov] at ho; cases ho
        | succ _ => omega
      cases hmax : opts.maxInputBytes <;> cases hcol : codec <;> cases hl : opts.level <;>
        cases hth : opts.threads <;>
        simp_all [isValidCompressInput, isValidLevel, isValidThreads] <;>
        (repeat (first | contradiction | omega | exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp⟩ | (split <;> simp_all)))
    · simp only [↓reduceIte]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp⟩
  · simp only [↓reduceIte]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp⟩

private theorem validateCompressOptions_true_implies_ok (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) (h : isValidCompressInput codec opts input = true) :
    Internal.validateCompressOptions codec opts input = .ok () ∧ opts.timeoutMs ≠ 0 := by
  simp only [isValidCompressInput, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨ht, ho⟩, hLvl⟩, hThr⟩, hIn⟩
  have htout : (opts.timeoutMs == 0) = false := beq_false_of_ne (by omega)
  have hout : (opts.maxOutputBytes == 0) = false := beq_false_of_ne (by omega)
  refine ⟨?_, by omega⟩
  unfold Internal.validateCompressOptions
  cases hcol : codec <;> cases hmax : opts.maxInputBytes <;> cases hl : opts.level <;>
    cases hth : opts.threads <;> simp_all [isValidLevel, isValidThreads]

private theorem validateDecompressOptions_false_implies_error (codec : Codec) (opts : DecompressOptions)
    (input : ByteArray) (h : isValidDecompressInput opts input = false) :
    ∃ e, Internal.validateDecompressOptions codec opts input = .error e ∧
      e.kind = .invalidInput ∧ e.codec = some codec ∧
      e.exitCode = none ∧ e.stderr = none ∧ e.message ≠ "" := by
  unfold Internal.validateDecompressOptions
  cases ht : (opts.timeoutMs == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases ho : (opts.maxOutputBytes == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ht0 : opts.timeoutMs > 0 := by
        cases htv : opts.timeoutMs with
        | zero => rw [htv] at ht; cases ht
        | succ _ => omega
      have ho0 : opts.maxOutputBytes > 0 := by
        cases hov : opts.maxOutputBytes with
        | zero => rw [hov] at ho; cases ho
        | succ _ => omega
      cases hmax : opts.maxInputBytes <;>
        simp_all [isValidDecompressInput] <;>
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp⟩
    · simp only [↓reduceIte]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp⟩
  · simp only [↓reduceIte]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, by simp⟩

private theorem validateDecompressOptions_true_implies_ok (codec : Codec) (opts : DecompressOptions)
    (input : ByteArray) (h : isValidDecompressInput opts input = true) :
    Internal.validateDecompressOptions codec opts input = .ok () ∧ opts.timeoutMs ≠ 0 := by
  simp only [isValidDecompressInput, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨ht, ho⟩, hIn⟩
  have htout : (opts.timeoutMs == 0) = false := beq_false_of_ne (by omega)
  have hout : (opts.maxOutputBytes == 0) = false := beq_false_of_ne (by omega)
  refine ⟨?_, by omega⟩
  unfold Internal.validateDecompressOptions
  cases hmax : opts.maxInputBytes <;> simp_all

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem nonEmptyMsg_eq_of_ne_empty (fallback msg : String) (hm : msg ≠ "") :
    Internal.nonEmptyMsg fallback msg = msg := by
  unfold Internal.nonEmptyMsg
  have hem : msg.isEmpty = false := by
    simp [String.isEmpty, hm]
  simp [hem]

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

private theorem codecProgram_ne_empty (codec : Codec) :
    Internal.codecProgram codec ≠ "" := by
  cases codec <;> decide

private theorem mkCompressArgs_eq_expected (codec : Codec) (opts : CompressOptions) :
    Internal.mkCompressArgs codec opts = expectedCompressArgs codec opts := by
  cases codec <;> cases opts.level <;> cases opts.threads <;> rfl

private theorem mkDecompressArgs_eq_expected (codec : Codec) :
    Internal.mkDecompressArgs codec = expectedDecompressArgs codec := by
  cases codec <;> rfl

private theorem codecProgram_eq_expected (codec : Codec) :
    Internal.codecProgram codec = codecProgram codec := by
  cases codec <;> rfl

private theorem codecSanitizedEnv_eq_expected (codec : Codec) :
    Internal.codecSanitizedEnv = expectedSanitizedEnv codec := rfl

private theorem stderrPipeSlack_eq_expected :
    Internal.stderrPipeSlack = expectedStderrPipeSlack := rfl

private theorem decodeStderr_eq_expected (bs : ByteArray) :
    Internal.decodeStderr bs = expectedStderr bs := rfl

private theorem isResourceExhausted_of_kind {pe : ProcessError} (h : pe.kind ≠ .invalidInput) :
    isResourceExhaustedProcessError pe = false := by
  unfold isResourceExhaustedProcessError
  cases hpk : pe.kind with
  | invalidInput => exact absurd hpk h
  | notFound | permissionDenied | timedOut | outputLimitExceeded | terminatedBySignal | nonZeroExit | ioError => rfl

private theorem classifyProcessError_spec (codec : Codec) (pe : ProcessError) :
    let e := Internal.classifyProcessError codec pe
    e.kind = expectedProcessErrorKindFor pe ∧
    e.codec = some codec ∧
    e.exitCode = expectedProcessErrorExitCode (expectedProcessErrorKindFor pe) pe.exitCode ∧
    e.stderr =
      (match expectedProcessErrorKindFor pe with
      | .toolNotFound | .invalidInput => none
      | _ => pe.stderr.bind expectedStderr) ∧
    e.message ≠ "" ∧
    (pe.message = "" ∨ e.message = pe.message) := by
  unfold Internal.classifyProcessError
  have hResEq : Internal.isResourceExhaustedProcessError pe = isResourceExhaustedProcessError pe := rfl
  have hk : (match pe.kind with
      | .notFound => CompressErrorKind.toolNotFound
      | .permissionDenied => .toolNotFound
      | .invalidInput => if Internal.isResourceExhaustedProcessError pe then .ioError else .invalidInput
      | .timedOut => .timedOut
      | .outputLimitExceeded => .outputLimitExceeded
      | .terminatedBySignal => .commandFailed
      | .nonZeroExit => .commandFailed
      | .ioError => .ioError) = expectedProcessErrorKindFor pe := by
    rw [hResEq]
    cases hpk : pe.kind with
    | invalidInput =>
      by_cases hRes : isResourceExhaustedProcessError pe = true <;>
        simp [expectedProcessErrorKindFor, expectedProcessErrorKind, hpk, hRes]
    | notFound | permissionDenied | timedOut | outputLimitExceeded | terminatedBySignal | nonZeroExit | ioError =>
      have hNe : pe.kind ≠ .invalidInput := by rw [hpk]; intro hc; cases hc
      simp [expectedProcessErrorKindFor, expectedProcessErrorKind, hpk, isResourceExhausted_of_kind hNe]
  have hex : (match (match pe.kind with
        | .notFound => CompressErrorKind.toolNotFound
        | .permissionDenied => .toolNotFound
        | .invalidInput => if Internal.isResourceExhaustedProcessError pe then .ioError else .invalidInput
        | .timedOut => .timedOut
        | .outputLimitExceeded => .outputLimitExceeded
        | .terminatedBySignal => .commandFailed
        | .nonZeroExit => .commandFailed
        | .ioError => .ioError) with
      | .commandFailed =>
        match pe.exitCode with
        | some c => if c != 0 then some c else none
        | none => none
      | _ => none) = expectedProcessErrorExitCode (expectedProcessErrorKindFor pe) pe.exitCode := by
    rw [hk]
    rfl
  have hErr : (match (match pe.kind with
        | .notFound => CompressErrorKind.toolNotFound
        | .permissionDenied => .toolNotFound
        | .invalidInput => if Internal.isResourceExhaustedProcessError pe then .ioError else .invalidInput
        | .timedOut => .timedOut
        | .outputLimitExceeded => .outputLimitExceeded
        | .terminatedBySignal => .commandFailed
        | .nonZeroExit => .commandFailed
        | .ioError => .ioError) with
      | .toolNotFound | .invalidInput => none
      | _ => pe.stderr.bind Internal.decodeStderr) =
      (match expectedProcessErrorKindFor pe with
      | .toolNotFound | .invalidInput => none
      | _ => pe.stderr.bind expectedStderr) := by
    rw [hk]
    cases expectedProcessErrorKindFor pe <;> cases pe.stderr <;> rfl
  have hf : Internal.codecProgram codec ++ " process invocation failed" ≠ "" :=
    append_head_ne_empty _ _ (codecProgram_ne_empty codec)
  refine ⟨hk, rfl, hex, hErr, nonEmptyMsg_ne_empty _ _ hf, ?_⟩
  · by_cases hm : pe.message = ""
    · exact Or.inl hm
    · exact Or.inr (nonEmptyMsg_eq_of_ne_empty _ _ hm)

private theorem classifyExitResult_nonzero_msg (codec : Codec) (isDecompress : Bool)
    (res : ExecResult) :
    let fallback :=
      if isDecompress then
        Internal.codecProgram codec ++ " decompression failed with exit code " ++ toString res.exitCode
      else
        Internal.codecProgram codec ++ " compression failed with exit code " ++ toString res.exitCode
    (match Internal.decodeStderr res.stderr with
      | some s => Internal.nonEmptyMsg fallback s
      | none => fallback) ≠ "" := by
  intro fallback
  have hf : fallback ≠ "" := by
    dsimp [fallback]
    cases isDecompress <;>
      exact append_head_ne_empty _ _ (append_head_ne_empty _ _ (codecProgram_ne_empty codec))
  cases h : Internal.decodeStderr res.stderr with
  | none => exact hf
  | some s => exact nonEmptyMsg_ne_empty _ _ hf

/-- Proof of `test_compress_compressWith_invalidOptionsRejectWithoutSpawn` for `Internal.mkApiM`. -/
theorem proof_compress_compressWith_invalidOptionsRejectWithoutSpawn
    {S : Type} (proc : ProcessApiM (StateM S)) :
    AllPass (test_compress_compressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM proc) := by
  intro s₀ codec opts input hInvalid
  rcases validateCompressOptions_false_implies_error codec opts input hInvalid with
    ⟨e, hVal, hKind, hCodec, hExit, hErr, hMsg⟩
  dsimp only [Internal.mkApiM, Internal.compressWith, StateT.run, bind, StateT.bind, pure, StateT.pure,
    assert]
  rw [hVal]
  dsimp
  exact ⟨⟨e, rfl, hKind, hCodec, hExit, hErr, hMsg⟩, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_compressWith_invalidOptionsRejectWithoutSpawn`. -/
theorem reach_compress_compressWith_invalidOptionsRejectWithoutSpawn :
    CanReach (test_compress_compressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM mockProcessApi) := by
  refine ⟨{}, .gzip, { threads := some 2 }, ByteArray.empty, by decide, ?_⟩
  exact proof_compress_compressWith_invalidOptionsRejectWithoutSpawn mockProcessApi
    {} .gzip { threads := some 2 } ByteArray.empty (by decide)

/-- Proof of `test_compress_decompressWith_invalidOptionsRejectWithoutSpawn` for `Internal.mkApiM`. -/
theorem proof_compress_decompressWith_invalidOptionsRejectWithoutSpawn
    {S : Type} (proc : ProcessApiM (StateM S)) :
    AllPass (test_compress_decompressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM proc) := by
  intro s₀ codec opts input hInvalid
  rcases validateDecompressOptions_false_implies_error codec opts input hInvalid with
    ⟨e, hVal, hKind, hCodec, hExit, hErr, hMsg⟩
  dsimp only [Internal.mkApiM, Internal.decompressWith, StateT.run, bind, StateT.bind, pure, StateT.pure,
    assert]
  rw [hVal]
  dsimp
  exact ⟨⟨e, rfl, hKind, hCodec, hExit, hErr, hMsg⟩, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_decompressWith_invalidOptionsRejectWithoutSpawn`. -/
theorem reach_compress_decompressWith_invalidOptionsRejectWithoutSpawn :
    CanReach (test_compress_decompressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM mockProcessApi) := by
  refine ⟨{}, .zstd, { timeoutMs := 0 }, ByteArray.empty, by decide, ?_⟩
  exact proof_compress_decompressWith_invalidOptionsRejectWithoutSpawn mockProcessApi
    {} .zstd { timeoutMs := 0 } ByteArray.empty (by decide)

/-- Proof of `test_compress_compressWith_buildsExactExecRequest` for `Internal.mkApiM`. -/
theorem proof_compress_compressWith_buildsExactExecRequest :
    AllPass (test_compress_compressWith_buildsExactExecRequest Internal.mkApiM) := by
  intro codec opts input outBytes errBytes hValid
  rcases validateCompressOptions_true_implies_ok codec opts input hValid with ⟨hVal, _⟩
  dsimp only [test_compress_compressWith_buildsExactExecRequest, Internal.mkApiM,
    Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
  rw [hVal]
  dsimp only [mockProcessApi, Internal.classifyExitResult, StateT.run, bind, StateT.bind,
    pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set,
    StateT.get, StateT.set, Internal.mkCompressRequest]
  dsimp
  simp only [mkCompressArgs_eq_expected, codecProgram_eq_expected, codecSanitizedEnv_eq_expected codec,
    stderrPipeSlack_eq_expected]
  by_cases hOut : outBytes.size ≤ opts.maxOutputBytes
  · have hGt : ¬ (outBytes.size > opts.maxOutputBytes) := by omega
    simp only [hOut, hGt, ↓reduceIte]
    exact ⟨trivial, trivial, trivial, trivial⟩
  · have hGt : outBytes.size > opts.maxOutputBytes := by omega
    simp only [hOut, hGt, ↓reduceIte]
    refine ⟨⟨_, rfl, rfl, rfl, rfl, decodeStderr_eq_expected errBytes,
      append_head_ne_empty _ _ (codecProgram_ne_empty codec)⟩,
      trivial, trivial, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_compressWith_buildsExactExecRequest`. -/
theorem reach_compress_compressWith_buildsExactExecRequest :
    CanReach (test_compress_compressWith_buildsExactExecRequest Internal.mkApiM) := by
  refine ⟨.zstd, { level := some 3, threads := some 0 }, ByteArray.empty, ByteArray.empty, ByteArray.empty, by decide, ?_⟩
  exact proof_compress_compressWith_buildsExactExecRequest
    .zstd { level := some 3, threads := some 0 } ByteArray.empty ByteArray.empty ByteArray.empty (by decide)

/-- Proof of `test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit` for `Internal.mkApiM`. -/
theorem proof_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit :
    AllPass (test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit Internal.mkApiM) := by
  intro codec opts input exitCode outBytes errBytes hValid
  rcases validateDecompressOptions_true_implies_ok codec opts input hValid with ⟨hVal, _⟩
  dsimp only [test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit, Internal.mkApiM,
    Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
  rw [hVal]
  dsimp only [mockProcessApi, Internal.classifyExitResult, StateT.run, bind, StateT.bind,
    pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set,
    StateT.get, StateT.set, Internal.mkDecompressRequest]
  dsimp
  simp only [mkDecompressArgs_eq_expected, codecProgram_eq_expected, codecSanitizedEnv_eq_expected codec,
    stderrPipeSlack_eq_expected]
  by_cases hNz : (exitCode != 0) = true
  · simp only [hNz, ↓reduceIte]
    refine ⟨trivial, trivial,
      ⟨_, rfl, rfl, rfl, rfl, decodeStderr_eq_expected errBytes,
        classifyExitResult_nonzero_msg codec true { exitCode := exitCode, stdout := outBytes, stderr := errBytes }⟩, trivial⟩
  · simp only [hNz, Bool.false_eq_true, ↓reduceIte]
    by_cases hOut : outBytes.size > opts.maxOutputBytes
    · simp only [hOut, ↓reduceIte]
      by_cases hGh : (codec == .gzip && !Model.hasGzipHeader input) = true
      · have hGhI : (codec == .gzip && !Internal.hasGzipHeader input) = true := hGh
        simp only [Bool.true_and, hGh, hGhI, ↓reduceIte]
        refine ⟨trivial, trivial,
          ⟨_, rfl, rfl, rfl, rfl, rfl,
            append_head_ne_empty _ _ (codecProgram_ne_empty codec)⟩, trivial⟩
      · have hGhF : (codec == .gzip && !Model.hasGzipHeader input) = false :=
          Bool.eq_false_iff.mpr hGh
        have hGhFI : (codec == .gzip && !Internal.hasGzipHeader input) = false := hGhF
        simp only [Bool.true_and, hGhF, hGhFI, Bool.false_eq_true, ↓reduceIte]
        refine ⟨trivial, trivial,
          ⟨_, rfl, rfl, rfl, rfl, decodeStderr_eq_expected errBytes,
            append_head_ne_empty _ _ (codecProgram_ne_empty codec)⟩, trivial⟩
    · simp only [hOut, ↓reduceIte]
      by_cases hGh : (codec == .gzip && !Model.hasGzipHeader input) = true
      · have hGhI : (codec == .gzip && !Internal.hasGzipHeader input) = true := hGh
        simp only [Bool.true_and, hGh, hGhI, ↓reduceIte]
        refine ⟨trivial, trivial,
          ⟨_, rfl, rfl, rfl, rfl, rfl,
            append_head_ne_empty _ _ (codecProgram_ne_empty codec)⟩, trivial⟩
      · have hGhF : (codec == .gzip && !Model.hasGzipHeader input) = false :=
          Bool.eq_false_iff.mpr hGh
        have hGhFI : (codec == .gzip && !Internal.hasGzipHeader input) = false := hGhF
        simp only [Bool.true_and, hGhF, hGhFI, Bool.false_eq_true, ↓reduceIte]
        trivial

/-- Non-vacuity `CanReach` witness for `test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit`. -/
theorem reach_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit :
    CanReach (test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit Internal.mkApiM) := by
  refine ⟨.gzip, {}, ByteArray.empty, 2, ByteArray.empty, "trailing".toUTF8, by decide, ?_⟩
  exact proof_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit
    .gzip {} ByteArray.empty 2 ByteArray.empty "trailing".toUTF8 (by decide)

/-- Proof of `test_compress_defaults_matchWithDefaultOptions` for `Internal.mkApiM`. -/
theorem proof_compress_defaults_matchWithDefaultOptions
    {S : Type} (proc : ProcessApiM (StateM S)) :
    AllPass (test_compress_defaults_matchWithDefaultOptions Internal.mkApiM proc) := by
  intro s₀ codec input
  dsimp only [test_compress_defaults_matchWithDefaultOptions, Internal.mkApiM,
    bind, pure, assert]
  exact ⟨rfl, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_defaults_matchWithDefaultOptions`. -/
theorem reach_compress_defaults_matchWithDefaultOptions :
    CanReach (test_compress_defaults_matchWithDefaultOptions Internal.mkApiM mockProcessApi) :=
  ⟨{}, .zstd, ByteArray.empty, proof_compress_defaults_matchWithDefaultOptions mockProcessApi {} .zstd ByteArray.empty⟩

/-- Proof of `test_compress_spawnErrors_mappedCorrectly` for `Internal.mkApiM`. -/
theorem proof_compress_spawnErrors_mappedCorrectly :
    AllPass (test_compress_spawnErrors_mappedCorrectly Internal.mkApiM) := by
  intro codec isDecompress copts dopts pe input hValid
  have hPeSpec := classifyProcessError_spec codec pe
  cases isDecompress with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hValid
    rcases validateCompressOptions_true_implies_ok codec copts input hValid with ⟨hVal, _⟩
    dsimp only [test_compress_spawnErrors_mappedCorrectly, Internal.mkApiM,
      Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hVal]
    dsimp only [mockProcessApi, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
    dsimp
    exact ⟨rfl, ⟨Internal.classifyProcessError codec pe, rfl,
      hPeSpec.1, hPeSpec.2.1, hPeSpec.2.2.1, hPeSpec.2.2.2.1, hPeSpec.2.2.2.2.1,
      match hPeSpec.2.2.2.2.2 with | Or.inl h => Or.inl h | Or.inr h => Or.inr (Or.inl h)⟩, trivial⟩
  | true =>
    simp only [↓reduceIte] at hValid
    rcases validateDecompressOptions_true_implies_ok codec dopts input hValid with ⟨hVal, _⟩
    dsimp only [test_compress_spawnErrors_mappedCorrectly, Internal.mkApiM,
      Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
    simp only [↓reduceIte]
    rw [hVal]
    dsimp only [mockProcessApi, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
    by_cases hLim : (pe.kind == .outputLimitExceeded || pe.kind == .timedOut) = true
    · by_cases hGh : (codec == .gzip && !Model.hasGzipHeader input) = true
      · have hGhI : (codec == .gzip && !Internal.hasGzipHeader input) = true := hGh
        have hIf : ((pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
            codec == .gzip && !Internal.hasGzipHeader input) = true := by
          rw [Bool.and_assoc, hLim, hGhI]; rfl
        rw [ite_eq_left hIf]
        exact ⟨rfl, ⟨_, rfl, by simp only [Bool.true_and, hLim, hGh, ↓reduceIte], rfl,
          by simp only [Bool.true_and, hLim, hGh, ↓reduceIte],
          by have hNotLim : (expectedProcessErrorKindFor pe = .outputLimitExceeded ∨ expectedProcessErrorKindFor pe = .timedOut) := by
               cases hpk : pe.kind with
               | outputLimitExceeded =>
                 exact Or.inl (by simp [expectedProcessErrorKindFor, expectedProcessErrorKind, hpk, isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)])
               | timedOut =>
                 exact Or.inr (by simp [expectedProcessErrorKindFor, expectedProcessErrorKind, hpk, isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)])
               | notFound | permissionDenied | invalidInput | terminatedBySignal | nonZeroExit | ioError =>
                 exfalso; rw [hpk] at hLim; cases hLim
             rcases hNotLim with hpk | hpk <;>
               (change pe.stderr.bind Internal.decodeStderr = _; rw [hpk]; rfl),
          append_head_ne_empty _ _ (codecProgram_ne_empty codec),
          Or.inr (Or.inr (by simp only [hLim, hGh, Bool.true_and]))⟩, trivial⟩
      · have hGhF : (codec == .gzip && !Model.hasGzipHeader input) = false :=
          Bool.eq_false_iff.mpr hGh
        have hGhFI : (codec == .gzip && !Internal.hasGzipHeader input) = false := hGhF
        have hIf : ((pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
            codec == .gzip && !Internal.hasGzipHeader input) = false := by
          rw [Bool.and_assoc, hGhFI, Bool.and_false]
        rw [ite_eq_right (Bool.eq_false_iff.mp hIf)]
        exact ⟨rfl, ⟨Internal.classifyProcessError codec pe, rfl,
          by simpa [hLim, hGhF] using hPeSpec.1, hPeSpec.2.1,
          by simpa [hLim, hGhF] using hPeSpec.2.2.1,
          hPeSpec.2.2.2.1, hPeSpec.2.2.2.2.1,
          match hPeSpec.2.2.2.2.2 with | Or.inl h => Or.inl h | Or.inr h => Or.inr (Or.inl h)⟩, trivial⟩
    · have hLimF : (pe.kind == .outputLimitExceeded || pe.kind == .timedOut) = false :=
        Bool.eq_false_iff.mpr hLim
      have hIf : ((pe.kind == .outputLimitExceeded || pe.kind == .timedOut) &&
          codec == .gzip && !Internal.hasGzipHeader input) = false := by
        rw [Bool.and_assoc, hLimF, Bool.false_and]
      rw [ite_eq_right (Bool.eq_false_iff.mp hIf)]
      exact ⟨rfl, ⟨Internal.classifyProcessError codec pe, rfl,
        by simpa [hLim] using hPeSpec.1, hPeSpec.2.1,
        by simpa [hLim] using hPeSpec.2.2.1,
        hPeSpec.2.2.2.1, hPeSpec.2.2.2.2.1,
        match hPeSpec.2.2.2.2.2 with | Or.inl h => Or.inl h | Or.inr h => Or.inr (Or.inl h)⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_spawnErrors_mappedCorrectly`. -/
theorem reach_compress_spawnErrors_mappedCorrectly :
    CanReach (test_compress_spawnErrors_mappedCorrectly Internal.mkApiM) :=
  ⟨.xz, false, {}, {}, { kind := .permissionDenied, program := some "xz", message := "eacces" },
    ByteArray.empty, by decide,
    proof_compress_spawnErrors_mappedCorrectly .xz false {} {}
      { kind := .permissionDenied, program := some "xz", message := "eacces" } ByteArray.empty (by decide)⟩

/-- Proof of `test_compress_awaitOutcomes_classified` for `Internal.mkApiM`. -/
theorem proof_compress_awaitOutcomes_classified :
    AllPass (test_compress_awaitOutcomes_classified Internal.mkApiM) := by
  intro codec isDecompress copts dopts input outBytes errBytes sig outcomeKind hKind hValid
  have hCases : outcomeKind = 0 ∨ outcomeKind = 1 ∨ outcomeKind = 2 ∨ outcomeKind = 3 := by omega
  have hf : Internal.codecProgram codec ++ " process invocation failed" ≠ "" :=
    append_head_ne_empty _ _ (codecProgram_ne_empty codec)
  cases isDecompress with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hValid
    rcases validateCompressOptions_true_implies_ok codec copts input hValid with ⟨hValC, _⟩
    rcases hCases with rfl | rfl | rfl | rfl
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hValC]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (0 == 0) = true from rfl, ↓reduceIte, Bool.false_and]
      exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hValC]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (1 == 0) = false from rfl, show (1 == 1) = true from rfl,
        Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hValC]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (2 == 0) = false from rfl, show (2 == 1) = false from rfl, show (2 == 2) = true from rfl,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hValC]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (3 == 0) = false from rfl, show (3 == 1) = false from rfl, show (3 == 2) = false from rfl,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩
  | true =>
    simp only [↓reduceIte] at hValid
    rcases validateDecompressOptions_true_implies_ok codec dopts input hValid with ⟨hValD, _⟩
    rcases hCases with rfl | rfl | rfl | rfl
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [↓reduceIte]
      rw [hValD]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (0 == 0) = true from rfl, ↓reduceIte, Bool.true_and]
      by_cases hGh : (codec == .gzip && !Model.hasGzipHeader input) = true
      · have hGhI : (codec == .gzip && !Internal.hasGzipHeader input) = true := hGh
        simp only [Bool.and_assoc, hGh, hGhI, ↓reduceIte]
        exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact append_head_ne_empty _ _ (codecProgram_ne_empty codec)⟩, trivial⟩
      · have hGhF : (codec == .gzip && !Model.hasGzipHeader input) = false :=
          Bool.eq_false_iff.mpr hGh
        have hGhFI : (codec == .gzip && !Internal.hasGzipHeader input) = false := hGhF
        simp only [Bool.and_assoc, hGhF, hGhFI, Bool.false_eq_true, ↓reduceIte]
        exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [↓reduceIte]
      rw [hValD]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (1 == 0) = false from rfl, show (1 == 1) = true from rfl,
        Bool.false_eq_true, ↓reduceIte, Bool.true_and]
      by_cases hGh : (codec == .gzip && !Model.hasGzipHeader input) = true
      · have hGhI : (codec == .gzip && !Internal.hasGzipHeader input) = true := hGh
        simp only [Bool.and_assoc, hGh, hGhI, ↓reduceIte]
        exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact append_head_ne_empty _ _ (codecProgram_ne_empty codec)⟩, trivial⟩
      · have hGhF : (codec == .gzip && !Model.hasGzipHeader input) = false :=
          Bool.eq_false_iff.mpr hGh
        have hGhFI : (codec == .gzip && !Internal.hasGzipHeader input) = false := hGhF
        simp only [Bool.and_assoc, hGhF, hGhFI, Bool.false_eq_true, ↓reduceIte]
        exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [↓reduceIte]
      rw [hValD]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (2 == 0) = false from rfl, show (2 == 1) = false from rfl, show (2 == 2) = true from rfl,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩
    · dsimp only [test_compress_awaitOutcomes_classified, Internal.mkApiM,
        Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
      simp only [↓reduceIte]
      rw [hValD]
      dsimp only [mockProcessApi, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
        pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
      change _ ∧ _ ∧ True
      simp only [show (3 == 0) = false from rfl, show (3 == 1) = false from rfl, show (3 == 2) = false from rfl,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, ⟨_, rfl, rfl, rfl, by dsimp; exact nonEmptyMsg_ne_empty _ _ hf⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_awaitOutcomes_classified`. -/
theorem reach_compress_awaitOutcomes_classified :
    CanReach (test_compress_awaitOutcomes_classified Internal.mkApiM) :=
  ⟨.zstd, true, {}, {}, ByteArray.empty, ByteArray.empty, ByteArray.empty, 9, 0, by decide, by decide,
    proof_compress_awaitOutcomes_classified
      .zstd true {} {} ByteArray.empty ByteArray.empty ByteArray.empty 9 0 (by decide) (by decide)⟩

/-- Proof of `test_compress_exitCodes_compressVsDecompress_andStderr` for `Internal.mkApiM`. -/
theorem proof_compress_exitCodes_compressVsDecompress_andStderr :
    AllPass (test_compress_exitCodes_compressVsDecompress_andStderr Internal.mkApiM) := by
  intro codec exitCode input errBytes hnz
  have hbeq : (exitCode == 0) = false := beq_false_of_ne hnz
  have hValC : Internal.validateCompressOptions codec {} input = .ok () := by
    cases codec <;> rfl
  have hValD : Internal.validateDecompressOptions codec {} input = .ok () := by
    cases codec <;> rfl
  dsimp only [test_compress_exitCodes_compressVsDecompress_andStderr, Internal.mkApiM,
    Internal.compressWith, Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
  rw [hValC, hValD]
  dsimp only [mockProcessApi, Internal.classifyExitResult, StateT.run, bind, StateT.bind,
    pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
  dsimp
  have hNz : (exitCode != 0) = true := by
    simp only [bne, hbeq, Bool.not_false]
  simp only [hNz, ↓reduceIte]
  refine ⟨⟨_, rfl, rfl, rfl, rfl, decodeStderr_eq_expected errBytes,
    classifyExitResult_nonzero_msg codec false { exitCode := exitCode, stdout := ByteArray.empty, stderr := errBytes }⟩,
    ⟨_, rfl, rfl, rfl, rfl, decodeStderr_eq_expected errBytes,
    classifyExitResult_nonzero_msg codec true { exitCode := exitCode, stdout := ByteArray.empty, stderr := errBytes }⟩,
    trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_exitCodes_compressVsDecompress_andStderr`. -/
theorem reach_compress_exitCodes_compressVsDecompress_andStderr :
    CanReach (test_compress_exitCodes_compressVsDecompress_andStderr Internal.mkApiM) :=
  ⟨.gzip, 2, ByteArray.empty, "trailing".toUTF8, by decide,
    proof_compress_exitCodes_compressVsDecompress_andStderr .gzip 2 ByteArray.empty "trailing".toUTF8 (by decide)⟩

/-- Proof of `test_compress_isToolAvailable_checksVersion` for `Internal.mkApiM`. -/
theorem proof_compress_isToolAvailable_checksVersion :
    AllPass (test_compress_isToolAvailable_checksVersion Internal.mkApiM) := by
  intro codec runOk exitCode
  dsimp only [test_compress_isToolAvailable_checksVersion, Internal.mkApiM,
    Internal.isToolAvailable, bind, StateT.bind, pure, StateT.pure, assert]
  cases runOk with
  | false =>
    dsimp only [mockProcessApi, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set,
      Internal.mkToolVersionRequest]
    dsimp
    simp only [codecProgram_eq_expected, codecSanitizedEnv_eq_expected codec]
    exact ⟨rfl, rfl, rfl, trivial⟩
  | true =>
    dsimp only [mockProcessApi, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set,
      Internal.mkToolVersionRequest]
    dsimp
    simp only [codecProgram_eq_expected, codecSanitizedEnv_eq_expected codec]
    exact ⟨rfl, rfl, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_isToolAvailable_checksVersion`. -/
theorem reach_compress_isToolAvailable_checksVersion :
    CanReach (test_compress_isToolAvailable_checksVersion Internal.mkApiM) :=
  ⟨.zstd, true, 0, proof_compress_isToolAvailable_checksVersion .zstd true 0⟩

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (x >>= f) w =
      match x w with
      | EST.Out.ok a w' => f a w'
      | EST.Out.error e w' => EST.Out.error e w' := by
  change EST.bind x f w = _
  unfold EST.bind
  cases x w <;> rfl

private theorem io_tryCatch_eq {α : Type} (x : IO α) (h : IO.Error → IO α) (w : Void IO.RealWorld) :
    (tryCatch x h) w =
      match x w with
      | EST.Out.ok a w' => EST.Out.ok a w'
      | EST.Out.error e w' => h e w' := by
  change EST.tryCatch x h w = _
  unfold EST.tryCatch
  cases x w <;> rfl

private theorem catchProc_never_throws {α : Type} (prog? : Option String)
    (act : IO (Except ProcessError α)) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.catchProc prog? act w = EST.Out.ok r w' := by
  have heq : LeanSwe.Process.SysBridge.catchProc prog? act w =
      EST.tryCatch act
        (fun err => EST.pure (.error (LeanSwe.Process.SysBridge.mapIoError prog? err))) w := rfl
  rw [heq]
  cases h : act w with
  | ok a w' => exact ⟨a, w', by simp [EST.tryCatch, h]⟩
  | error err w' =>
    exact ⟨.error (LeanSwe.Process.SysBridge.mapIoError prog? err), w',
      by simp [EST.tryCatch, EST.pure, h]⟩

private theorem defaultOps_spawn_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.spawn req w = EST.Out.ok r w' :=
  catchProc_never_throws (some req.program) _ w

private theorem defaultOps_awaitOutput_never_throws (h : LeanSwe.Process.ProcessHandle)
    (stdin : ByteArray) (timeoutMs maxOut : Option Nat) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.awaitOutput h stdin timeoutMs maxOut w = EST.Out.ok r w' :=
  catchProc_never_throws none _ w

private theorem defaultOps_killProcessGroup_never_throws (h : LeanSwe.Process.ProcessHandle)
    (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.killProcessGroup h w = EST.Out.ok r w' :=
  catchProc_never_throws none _ w

private theorem defaultOps_reap_never_throws (h : LeanSwe.Process.ProcessHandle)
    (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.reap h w = EST.Out.ok r w' :=
  catchProc_never_throws none _ w

private theorem processRun_defaultOps_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Internal.run LeanSwe.Process.SysBridge.defaultOps req w = EST.Out.ok r w' := by
  unfold LeanSwe.Process.Internal.run
  cases hVal : LeanSwe.Process.Internal.validateRequest req with
  | error e =>
    dsimp only
    rw [io_pure_eq]
    exact ⟨Except.error e, w, rfl⟩
  | ok vreq =>
    dsimp only
    rw [io_bind_eq]
    rcases defaultOps_spawn_never_throws vreq w with ⟨rSpawn, w1, hSpawn⟩
    rw [hSpawn]
    cases rSpawn with
    | error err =>
      dsimp only
      rw [io_pure_eq]
      exact ⟨_, _, rfl⟩
    | ok h =>
      dsimp only
      rw [io_bind_eq]
      rcases defaultOps_awaitOutput_never_throws h vreq.stdin vreq.timeoutMs vreq.maxOutputBytes w1 with
        ⟨rAwait, w2, hAwait⟩
      rw [hAwait]
      rcases rAwait with err | outcome
      · dsimp only
        rw [io_bind_eq]
        rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, w3, hKill⟩
        rw [hKill]; dsimp only; rw [io_bind_eq]
        rcases defaultOps_reap_never_throws h w3 with ⟨_, w4, hReap⟩
        rw [hReap]; dsimp only; rw [io_pure_eq]
        exact ⟨_, _, rfl⟩
      · cases outcome with
        | exited res =>
          dsimp only
          rw [io_bind_eq]
          rcases defaultOps_reap_never_throws h w2 with ⟨rReap, w3, hReap⟩
          rw [hReap]
          cases rReap <;> (dsimp only; rw [io_pure_eq]; exact ⟨_, _, rfl⟩)
        | signaled _ _ _ =>
          dsimp only
          rw [io_bind_eq]
          rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, w3, hKill⟩
          rw [hKill]; dsimp only; rw [io_bind_eq]
          rcases defaultOps_reap_never_throws h w3 with ⟨_, w4, hReap⟩
          rw [hReap]; dsimp only; rw [io_pure_eq]
          exact ⟨_, _, rfl⟩
        | timedOut _ _ =>
          dsimp only
          rw [io_bind_eq]
          rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, w3, hKill⟩
          rw [hKill]; dsimp only; rw [io_bind_eq]
          rcases defaultOps_reap_never_throws h w3 with ⟨_, w4, hReap⟩
          rw [hReap]; dsimp only; rw [io_pure_eq]
          exact ⟨_, _, rfl⟩
        | outputLimitExceeded _ _ =>
          dsimp only
          rw [io_bind_eq]
          rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, w3, hKill⟩
          rw [hKill]; dsimp only; rw [io_bind_eq]
          rcases defaultOps_reap_never_throws h w3 with ⟨_, w4, hReap⟩
          rw [hReap]; dsimp only; rw [io_pure_eq]
          exact ⟨_, _, rfl⟩

private theorem validateCompressOptions_error_ne_corruptData (codec : Codec)
    (opts : CompressOptions) (input : ByteArray) {e : CompressError}
    (h : Internal.validateCompressOptions codec opts input = .error e) :
    e.kind ≠ .corruptData := by
  by_cases hv : isValidCompressInput codec opts input = true
  · have := (validateCompressOptions_true_implies_ok codec opts input hv).1
    rw [this] at h
    cases h
  · have hfalse : isValidCompressInput codec opts input = false := by
      cases hc : isValidCompressInput codec opts input <;> simp_all
    rcases validateCompressOptions_false_implies_error codec opts input hfalse with
      ⟨e', hVal, hk, _⟩
    rw [hVal] at h
    injection h with heq
    rw [← heq, hk]
    decide

/-- Formal impossibility proof for `LeanSwe.Compress.compressWith` never returning `.corruptData`. -/
theorem compress_compressWith_never_corruptData (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CompressError.kind .corruptData
      (Compress.compressWith codec opts input) w := by
  unfold Core.NeverErrorKindIO Compress.compressWith Compress.defaultApi Internal.mkApiM
    Internal.compressWith LeanSwe.Process.defaultApi LeanSwe.Process.Internal.mkApiM
  dsimp only
  cases hVal : Internal.validateCompressOptions codec opts input with
  | error e =>
    dsimp only
    rw [io_pure_eq]
    exact validateCompressOptions_error_ne_corruptData codec opts input hVal
  | ok _ =>
    dsimp only
    rw [io_bind_eq]
    rcases processRun_defaultOps_never_throws (Internal.mkCompressRequest codec opts input) w with
      ⟨r, w', hRun⟩
    rw [hRun]
    cases r with
    | error pe =>
      dsimp only
      rw [io_pure_eq]
      dsimp only
      unfold Internal.classifyProcessError
      cases pe.kind with
      | invalidInput =>
        by_cases hRes : Internal.isResourceExhaustedProcessError pe <;> simp [hRes]
      | notFound | permissionDenied | timedOut | outputLimitExceeded | terminatedBySignal | nonZeroExit | ioError => simp
    | ok res =>
      dsimp only
      rw [io_pure_eq]
      dsimp only [Internal.classifyExitResult]
      by_cases hNz : (res.exitCode != 0) = true
      · simp [hNz]
      · simp only [hNz, Bool.false_eq_true, ↓reduceIte]
        by_cases hLim : res.stdout.size > opts.maxOutputBytes
        · simp [hLim]
        · simp [hLim]

/-- Formal impossibility proof for `LeanSwe.Compress.compress` never returning `.corruptData`. -/
theorem compress_compress_never_corruptData (codec : Codec) (input : ByteArray)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CompressError.kind .corruptData
      (Compress.compress codec input) w :=
  compress_compressWith_never_corruptData codec {} input w

private theorem byteArray_get!_push_lt {a : ByteArray} {x : UInt8} {i : Nat} (hi : i < a.size) :
    (a.push x).get! i = a.get! i := by
  have h1 : i < a.data.size := hi
  have h2 : i < (a.data.push x).size := by simp [Array.size_push]; exact Nat.lt_succ_of_lt h1
  change (a.data.push x)[i]! = a.data[i]!
  rw [getElem!_pos (a.data.push x) i h2, getElem!_pos a.data i h1, Array.getElem_push_lt h1]

private theorem byteArray_get!_append_lt {a b : ByteArray} {i : Nat} (hi : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  have h1 : i < a.data.size := hi
  have h2 : i < (a ++ b).data.size := by
    simp [ByteArray.data_append, Array.size_append]
    exact Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)
  have hEq1 : (a ++ b).get! i = (a ++ b).data[i]! := rfl
  have hEq2 : a.get! i = a.data[i]! := rfl
  rw [hEq1, hEq2, getElem!_pos (a ++ b).data i h2, getElem!_pos a.data i h1]
  simp [ByteArray.data_append, Array.getElem_append_left h1]

private theorem pushU16LE_size (a : ByteArray) (v : UInt16) : (pushU16LE a v).size = a.size + 2 := by
  simp [pushU16LE, ByteArray.size_push]

private theorem pushU32LE_size (a : ByteArray) (v : UInt32) : (pushU32LE a v).size = a.size + 4 := by
  simp [pushU32LE, ByteArray.size_push]

private theorem pushU64LE_size (a : ByteArray) (v : UInt64) : (pushU64LE a v).size = a.size + 8 := by
  simp [pushU64LE, pushU32LE_size]

private theorem pushReplicateByte_size (dst : ByteArray) (b : UInt8) (count : Nat) :
    (pushReplicateByte dst b count).size = dst.size + count := by
  unfold pushReplicateByte
  suffices h : ∀ (fuel : Nat) (acc : ByteArray), (pushReplicateByte.go b fuel acc).size = acc.size + fuel by
    exact h count dst
  intro fuel
  induction fuel with
  | zero => intro acc; rfl
  | succ f ih => intro acc; simp [pushReplicateByte.go, ih, ByteArray.size_push]; omega

private theorem pushBytesRange_size_le (dst src : ByteArray) (start stop : Nat) :
    (pushBytesRange dst src start stop).size ≤ dst.size + (stop - start) := by
  unfold pushBytesRange
  dsimp only
  suffices h : ∀ (fuel idx : Nat) (acc : ByteArray),
      (pushBytesRange.go src (min stop src.size) fuel idx acc).size ≤ acc.size + fuel by
    have h1 := h (min stop src.size - start) start dst
    omega
  intro fuel
  induction fuel with
  | zero => intro idx acc; exact Nat.le_refl _
  | succ f ih =>
    intro idx acc
    unfold pushBytesRange.go
    split
    · omega
    · have h2 := ih (idx + 1) (acc.push (src.get! idx))
      simp only [ByteArray.size_push] at h2
      omega

private theorem pushBytesRange_size_ge (dst src : ByteArray) (start stop : Nat) :
    dst.size ≤ (pushBytesRange dst src start stop).size := by
  unfold pushBytesRange
  dsimp only
  suffices h : ∀ (fuel idx : Nat) (acc : ByteArray),
      acc.size ≤ (pushBytesRange.go src (min stop src.size) fuel idx acc).size by
    exact h (min stop src.size - start) start dst
  intro fuel
  induction fuel with
  | zero => intro idx acc; exact Nat.le_refl _
  | succ f ih =>
    intro idx acc
    unfold pushBytesRange.go
    split
    · exact Nat.le_refl _
    · have h2 := ih (idx + 1) (acc.push (src.get! idx))
      simp only [ByteArray.size_push] at h2
      omega

private theorem pushU16LE_get!_lt {a : ByteArray} {v : UInt16} {i : Nat} (hi : i < a.size) :
    (pushU16LE a v).get! i = a.get! i := by
  unfold pushU16LE
  rw [byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega), byteArray_get!_push_lt hi]

private theorem pushU32LE_get!_lt {a : ByteArray} {v : UInt32} {i : Nat} (hi : i < a.size) :
    (pushU32LE a v).get! i = a.get! i := by
  unfold pushU32LE
  rw [byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
    byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
    byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
    byteArray_get!_push_lt hi]

private theorem pushU64LE_get!_lt {a : ByteArray} {v : UInt64} {i : Nat} (hi : i < a.size) :
    (pushU64LE a v).get! i = a.get! i := by
  unfold pushU64LE
  rw [pushU32LE_get!_lt (by rw [pushU32LE_size]; omega), pushU32LE_get!_lt hi]

private theorem pushBytesRange_get!_lt (dst src : ByteArray) (start stop i : Nat) (hi : i < dst.size) :
    (pushBytesRange dst src start stop).get! i = dst.get! i := by
  unfold pushBytesRange
  dsimp only
  suffices h : ∀ (fuel idx : Nat) (acc : ByteArray), i < acc.size →
      (pushBytesRange.go src (min stop src.size) fuel idx acc).get! i = acc.get! i from
    h (min stop src.size - start) start dst hi
  intro fuel
  induction fuel with
  | zero => intro idx acc _; rfl
  | succ f ih =>
    intro idx acc hacc
    unfold pushBytesRange.go
    split
    · rfl
    · rw [ih (idx + 1) (acc.push (src.get! idx)) (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt hacc]

private theorem encodeXzVli_size_le (n : Nat) : (Model.encodeXzVli n).size ≤ 9 := by
  unfold Model.encodeXzVli
  suffices h : ∀ (fuel v : Nat) (acc : ByteArray), (Model.encodeXzVli.go fuel v acc).size ≤ acc.size + fuel by
    have h1 := h 9 n ByteArray.empty
    simpa using h1
  intro fuel
  induction fuel with
  | zero => intro v acc; exact Nat.le_refl _
  | succ f ih =>
    intro v acc
    unfold Model.encodeXzVli.go
    dsimp only
    split
    · simp [ByteArray.size_push]
    · exact Nat.le_trans (ih _ _) (by simp only [ByteArray.size_push]; omega)

private theorem encodeGzipStored_chunkLoop_size (input : ByteArray) :
    ∀ (fuel pos : Nat) (acc : ByteArray),
      pos ≤ input.size →
      acc.size ≤ (Model.encodeGzipStored.chunkLoop input fuel pos acc).size ∧
      (Model.encodeGzipStored.chunkLoop input fuel pos acc).size ≤
        acc.size + (input.size - pos) + fuel * 5
  | 0, _, acc, _ => by simp [Model.encodeGzipStored.chunkLoop]
  | fuel + 1, pos, acc, hpos => by
    unfold Model.encodeGzipStored.chunkLoop
    dsimp only
    have hT : min (input.size - pos) 65535 ≤ input.size - pos := Nat.min_le_left _ _
    split
    · exact ⟨Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
          (pushBytesRange_size_ge _ _ _ _),
        Nat.le_trans (pushBytesRange_size_le _ _ _ _)
          (by simp only [pushU16LE_size, ByteArray.size_push]; omega)⟩
    · refine ⟨Nat.le_trans (Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
            (pushBytesRange_size_ge _ _ _ _))
          (encodeGzipStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65535) _ (by omega)).1,
        Nat.le_trans
          (encodeGzipStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65535) _ (by omega)).2
          (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) _) _)
            (by simp only [pushU16LE_size, ByteArray.size_push]; omega))⟩

private theorem encodeGzipStored_chunkLoop_size_succ (input : ByteArray)
    (fuel pos : Nat) (acc : ByteArray) (hpos : pos ≤ input.size) :
    acc.size + 5 ≤ (Model.encodeGzipStored.chunkLoop input (fuel + 1) pos acc).size := by
  unfold Model.encodeGzipStored.chunkLoop
  dsimp only
  have hT : min (input.size - pos) 65535 ≤ input.size - pos := Nat.min_le_left _ _
  split
  · exact Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
      (pushBytesRange_size_ge _ _ _ _)
  · exact Nat.le_trans (Nat.le_trans (by simp only [pushU16LE_size, ByteArray.size_push]; omega)
        (pushBytesRange_size_ge _ _ _ _))
      (encodeGzipStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65535) _ (by omega)).1

private theorem encodeGzipStored_chunkLoop_get!_lt (input : ByteArray) (i : Nat) :
    ∀ (fuel pos : Nat) (acc : ByteArray), i < acc.size →
      (Model.encodeGzipStored.chunkLoop input fuel pos acc).get! i = acc.get! i
  | 0, _, _, _ => rfl
  | fuel + 1, pos, acc, hacc => by
    unfold Model.encodeGzipStored.chunkLoop
    dsimp only
    have hAcc2 (b : UInt8) (u1 u2 : UInt16) :
        i < (pushBytesRange (pushU16LE (pushU16LE (acc.push b) u1) u2) input pos (pos + min (input.size - pos) 65535)).size := by
      have h1 := pushBytesRange_size_ge (pushU16LE (pushU16LE (acc.push b) u1) u2) input pos (pos + min (input.size - pos) 65535)
      simp only [pushU16LE_size, ByteArray.size_push] at h1
      omega
    have hStep (b : UInt8) (u1 u2 : UInt16) :
        (pushBytesRange (pushU16LE (pushU16LE (acc.push b) u1) u2) input pos (pos + min (input.size - pos) 65535)).get! i = acc.get! i := by
      rw [pushBytesRange_get!_lt _ _ _ _ i (by simp [pushU16LE_size, ByteArray.size_push]; omega),
        pushU16LE_get!_lt (by simp [pushU16LE_size, ByteArray.size_push]; omega),
        pushU16LE_get!_lt (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt hacc]
    split
    · exact hStep _ _ _
    · rw [encodeGzipStored_chunkLoop_get!_lt input i fuel (pos + min (input.size - pos) 65535) _ (hAcc2 _ _ _)]
      exact hStep _ _ _

private theorem encodeZstdStored_chunkLoop_size (input : ByteArray) :
    ∀ (fuel pos : Nat) (acc : ByteArray),
      pos ≤ input.size →
      acc.size ≤ (Model.encodeZstdStored.chunkLoop input fuel pos acc).size ∧
      (Model.encodeZstdStored.chunkLoop input fuel pos acc).size ≤
        acc.size + (input.size - pos) + fuel * 3
  | 0, _, acc, _ => by simp [Model.encodeZstdStored.chunkLoop]
  | fuel + 1, pos, acc, hpos => by
    unfold Model.encodeZstdStored.chunkLoop
    dsimp only
    have hT : min (input.size - pos) 131072 ≤ input.size - pos := Nat.min_le_left _ _
    split
    · exact ⟨Nat.le_trans (by simp only [ByteArray.size_push]; omega)
          (pushBytesRange_size_ge _ _ _ _),
        Nat.le_trans (pushBytesRange_size_le _ _ _ _)
          (by simp only [ByteArray.size_push]; omega)⟩
    · refine ⟨Nat.le_trans (Nat.le_trans (by simp only [ByteArray.size_push]; omega)
            (pushBytesRange_size_ge _ _ _ _))
          (encodeZstdStored_chunkLoop_size input fuel (pos + min (input.size - pos) 131072) _ (by omega)).1,
        Nat.le_trans
          (encodeZstdStored_chunkLoop_size input fuel (pos + min (input.size - pos) 131072) _ (by omega)).2
          (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) _) _)
            (by simp only [ByteArray.size_push]; omega))⟩

private theorem encodeZstdStored_chunkLoop_get!_lt (input : ByteArray) (i : Nat) :
    ∀ (fuel pos : Nat) (acc : ByteArray), i < acc.size →
      (Model.encodeZstdStored.chunkLoop input fuel pos acc).get! i = acc.get! i
  | 0, _, _, _ => rfl
  | fuel + 1, pos, acc, hacc => by
    unfold Model.encodeZstdStored.chunkLoop
    dsimp only
    have hAcc2 (b0 b1 b2 : UInt8) :
        i < (pushBytesRange (((acc.push b0).push b1).push b2) input pos (pos + min (input.size - pos) 131072)).size := by
      have h1 := pushBytesRange_size_ge (((acc.push b0).push b1).push b2) input pos (pos + min (input.size - pos) 131072)
      simp only [ByteArray.size_push] at h1
      omega
    have hStep (b0 b1 b2 : UInt8) :
        (pushBytesRange (((acc.push b0).push b1).push b2) input pos (pos + min (input.size - pos) 131072)).get! i = acc.get! i := by
      rw [pushBytesRange_get!_lt _ _ _ _ i (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt (by simp [ByteArray.size_push]; omega),
        byteArray_get!_push_lt hacc]
    split
    · exact hStep _ _ _
    · rw [encodeZstdStored_chunkLoop_get!_lt input i fuel (pos + min (input.size - pos) 131072) _ (hAcc2 _ _ _)]
      exact hStep _ _ _

private theorem encodeXzStored_chunkLoop_size (input : ByteArray) :
    ∀ (fuel pos : Nat) (first : Bool) (acc : ByteArray),
      pos ≤ input.size →
      (Model.encodeXzStored.chunkLoop input fuel pos first acc).size ≤
        acc.size + (input.size - pos) + fuel * 3 + 1
  | 0, _, _, acc, _ => by simp [Model.encodeXzStored.chunkLoop]; omega
  | fuel + 1, pos, first, acc, hpos => by
    unfold Model.encodeXzStored.chunkLoop
    dsimp only
    have hT : min (input.size - pos) 65536 ≤ input.size - pos := Nat.min_le_left _ _
    split
    · simp only [ByteArray.size_push]
      exact Nat.le_trans (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) 1)
        (by simp only [ByteArray.size_push]; omega)
    · exact Nat.le_trans
        (encodeXzStored_chunkLoop_size input fuel (pos + min (input.size - pos) 65536) false _ (by omega))
        (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (pushBytesRange_size_le _ _ _ _) _) _) 1)
          (by simp only [ByteArray.size_push]; omega))

private theorem encodeStored_size_le_maxCompressedBound (codec : Codec) (input : ByteArray) :
    (Model.encodeStored codec input).size ≤ Model.maxCompressedBound codec input.size := by
  unfold Model.encodeStored Model.maxCompressedBound
  cases codec with
  | gzip =>
    unfold Model.encodeGzipStored
    dsimp only
    have h10 : (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]).size = 10 := rfl
    have h5 : (ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]).size = 5 := rfl
    have hBodyLe :
        (if input.isEmpty then (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]) ++ ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]
         else Model.encodeGzipStored.chunkLoop input (input.size / 65535 + 2) 0
           (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03])).size ≤
        10 + input.size + (input.size / 65535 + 2) * 5 := by
      split
      · simp only [ByteArray.size_append]; rw [h10, h5]; omega
      · have h := (encodeGzipStored_chunkLoop_size input (input.size / 65535 + 2) 0
          (ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]) (Nat.zero_le _)).2
        rw [h10] at h; exact h
    simp only [pushU32LE_size]
    omega
  | zstd =>
    unfold Model.encodeZstdStored
    dsimp only
    have h4 : (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).size = 4 := rfl
    have h3 : (ByteArray.mk #[0x01, 0x00, 0x00]).size = 3 := rfl
    let hdr :=
      if input.size >= 4294967296 then
        pushU64LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push (if input.size >= 4294967296 then 0xC4 else 0x84) |>.push 0x38) (UInt64.ofNat input.size)
      else
        pushU32LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push (if input.size >= 4294967296 then 0xC4 else 0x84) |>.push 0x38) (UInt32.ofNat input.size)
    have hHdrSize : hdr.size ≤ 14 := by
      dsimp only [hdr]
      split <;> simp only [pushU64LE_size, pushU32LE_size, ByteArray.size_push, h4] <;> omega
    have hBodyLe :
        (if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
         else Model.encodeZstdStored.chunkLoop input (input.size / 131072 + 2) 0 hdr).size ≤
        14 + input.size + (input.size / 131072 + 2) * 3 := by
      split
      · simp only [ByteArray.size_append, h3]; omega
      · have h := (encodeZstdStored_chunkLoop_size input (input.size / 131072 + 2) 0 hdr (Nat.zero_le _)).2
        omega
    simp only [pushU32LE_size]
    change (if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
            else Model.encodeZstdStored.chunkLoop input (input.size / 131072 + 2) 0 hdr).size + 4 ≤ _
    omega
  | xz =>
    unfold Model.encodeXzStored
    dsimp only
    have h8s : (ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]).size = 8 := rfl
    have h8b : (ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00]).size = 8 := rfl
    have hEmptySz : ByteArray.empty.size = 0 := rfl
    have h2 : (ByteArray.mk #[0x00, 0x04]).size = 2 := rfl
    have h2yz : (ByteArray.mk #[0x59, 0x5A]).size = 2 := rfl
    simp only [ByteArray.size_append, pushU32LE_size, pushReplicateByte_size]
    rw [h8s, h8b, hEmptySz, h2, h2yz]
    let blkPair :=
      if input.isEmpty = true then (ByteArray.empty, (#[] : Array (Nat × Nat)))
      else
        (pushU32LE (ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00])
            (crc32 (ByteArray.mk #[0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00]) 0 8) ++
          pushReplicateByte (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty) 0x00
            ((4 - (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty).size % 4) % 4) ++
          pushU64LE ByteArray.empty (crc64Xz input 0 input.size),
          #[(8 + 4 + (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty).size + 8, input.size)])
    have hIfBlk : blkPair.1.size ≤ 24 + input.size + (input.size / 65536 + 2) * 3 := by
      dsimp only [blkPair]
      split
      · simp only [hEmptySz]; omega
      · dsimp only
        have hL2 := encodeXzStored_chunkLoop_size input (input.size / 65536 + 2) 0 true ByteArray.empty (Nat.zero_le _)
        have hPad := pushReplicateByte_size (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty) 0x00
          ((4 - (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty).size % 4) % 4)
        have hPadLt : (4 - (Model.encodeXzStored.chunkLoop input (input.size / 65536 + 2) 0 true ByteArray.empty).size % 4) % 4 ≤ 3 := by omega
        simp only [ByteArray.size_append, pushU32LE_size, pushU64LE_size]
        rw [hEmptySz, h8b, hPad]
        rw [hEmptySz] at hL2
        omega
    have hBuildIdx : ∀ (recs : Array (Nat × Nat)) (fuel i : Nat) (buf : ByteArray),
        (Model.encodeXzStored.buildIdx recs fuel i buf).size ≤ buf.size + fuel * 18 := by
      intro recs fuel
      induction fuel with
      | zero => intro i buf; simp only [Model.encodeXzStored.buildIdx]; omega
      | succ f ih =>
        intro i buf
        unfold Model.encodeXzStored.buildIdx
        dsimp only
        split
        · omega
        · have h1 := ih (i + 1) (buf ++ Model.encodeXzVli recs[i]!.1 ++ Model.encodeXzVli recs[i]!.2)
          simp only [ByteArray.size_append] at h1
          have hv1 := encodeXzVli_size_le recs[i]!.1
          have hv2 := encodeXzVli_size_le recs[i]!.2
          omega
    have hRecsLen : blkPair.2.size ≤ 1 := by
      dsimp only [blkPair]; split <;> simp
    have hBuf1 : ∀ (recs : Array (Nat × Nat)), recs.size ≤ 1 →
        (Model.encodeXzStored.buildIdx recs recs.size 0
          ((ByteArray.empty.push 0x00) ++ Model.encodeXzVli recs.size)).size ≤ 28 := by
      intro recs hR
      have hB := hBuildIdx recs recs.size 0 ((ByteArray.empty.push 0x00) ++ Model.encodeXzVli recs.size)
      have hV := encodeXzVli_size_le recs.size
      simp only [ByteArray.size_append, ByteArray.size_push] at hB
      rw [hEmptySz] at hB
      omega
    have hBuf1App := hBuf1 blkPair.2 hRecsLen
    have hDiv : input.size / 65536 ≤ input.size / 1024 := Nat.div_le_div_left (by decide) (by decide)
    change 8 + 4 + blkPair.1.size +
      ((Model.encodeXzStored.buildIdx blkPair.2 blkPair.2.size 0
          (ByteArray.empty.push 0x00 ++ Model.encodeXzVli blkPair.2.size)).size +
        (4 - (Model.encodeXzStored.buildIdx blkPair.2 blkPair.2.size 0
          (ByteArray.empty.push 0x00 ++ Model.encodeXzVli blkPair.2.size)).size % 4) % 4 + 4) +
      (4 + (0 + 4 + 2) + 2) ≤ input.size + (input.size / 1024 + 1) * 64 + 256
    omega

private theorem byteArray_push_eq_append (a : ByteArray) (b : UInt8) :
    a.push b = a ++ ByteArray.mk #[b] := by
  apply ByteArray.ext
  simp only [ByteArray.data_push, ByteArray.data_append]
  exact Array.push_eq_append

private theorem xz_shdr_split (c : UInt32) :
    ∃ tail : ByteArray,
      pushU32LE (ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]) c =
        ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ tail := by
  dsimp only [pushU32LE]
  simp only [byteArray_push_eq_append]
  have hBodyEq : ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04] =
      ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ ByteArray.mk #[0x00, 0x04] := rfl
  rw [hBodyEq]
  simp only [ByteArray.append_assoc]
  exact ⟨_, rfl⟩

private theorem hasCanonicalCompressedFraming_xz_parts (shdr tail blocks idx ftrBody : ByteArray) (c : UInt32)
    (hSh : shdr = ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ tail)
    (hShSz : shdr.size ≥ 12) (hIdx : idx.size ≥ 8) (hFtrSz : ftrBody.size = 6) :
    Model.hasCanonicalCompressedFraming .xz
      (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])) = true := by
  unfold Model.hasCanonicalCompressedFraming
  have hEmpty : ByteArray.empty.size = 0 := rfl
  have h2 : (ByteArray.mk #[0x59, 0x5A]).size = 2 := rfl
  have hSfx : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size =
      ((shdr ++ blocks ++ idx) ++ (pushU32LE ByteArray.empty c ++ ftrBody)).size + 2 := by
    simp only [ByteArray.size_append, h2]
    omega
  have hTotSz : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size ≥ 32 := by
    simp only [ByteArray.size_append, pushU32LE_size, hEmpty, hFtrSz, h2]
    omega
  have hPfx : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).extract 0 6 =
      ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] := by
    rw [hSh]
    simp only [ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left rfl
  have hSfxEq : (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).extract
      ((shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size - 2)
      (shdr ++ blocks ++ idx ++ (pushU32LE ByteArray.empty c ++ ftrBody ++ ByteArray.mk #[0x59, 0x5A])).size =
      ByteArray.mk #[0x59, 0x5A] := by
    rw [hSfx, Nat.add_sub_cancel, ← ByteArray.append_assoc (a := shdr ++ blocks ++ idx)]
    exact ByteArray.extract_append_eq_right rfl (by simp only [ByteArray.size_append, h2])
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hTotSz, hPfx⟩, hSfxEq⟩

private theorem hasCanonicalCompressedFraming_encodeStored (codec : Codec) (input : ByteArray) :
    Model.hasCanonicalCompressedFraming codec (Model.encodeStored codec input) = true := by
  unfold Model.hasCanonicalCompressedFraming Model.encodeStored
  cases codec with
  | gzip =>
    unfold Model.encodeGzipStored
    dsimp only
    let hdr := ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0x03]
    let body :=
      if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]
      else Model.encodeGzipStored.chunkLoop input (input.size / 65535 + 2) 0 hdr
    let enc := pushU32LE (pushU32LE body (crc32 input 0 input.size)) (UInt32.ofNat (input.size % 4294967296))
    have hHdrSize : hdr.size = 10 := rfl
    have h5 : (ByteArray.mk #[0x01, 0x00, 0x00, 0xFF, 0xFF]).size = 5 := rfl
    have hBodyGe : 10 ≤ body.size := by
      simp only [body]; split
      · simp only [ByteArray.size_append]; rw [hHdrSize]; omega
      · have h := (encodeGzipStored_chunkLoop_size input (input.size / 65535 + 2) 0 hdr (Nat.zero_le _)).1
        rw [hHdrSize] at h; exact h
    have hSz : 20 ≤ enc.size := by
      dsimp only [enc]; simp only [pushU32LE_size]
      simp only [body]; split
      · simp only [ByteArray.size_append]; rw [hHdrSize, h5]; omega
      · have h : hdr.size + 5 ≤ (Model.encodeGzipStored.chunkLoop input (input.size / 65535 + 2) 0 hdr).size :=
          encodeGzipStored_chunkLoop_size_succ input (input.size / 65535 + 1) 0 hdr (Nat.zero_le _)
        rw [hHdrSize] at h; omega
    have hGet : ∀ i : Nat, i < 10 → enc.get! i = hdr.get! i := by
      intro i hi
      dsimp only [enc]
      rw [pushU32LE_get!_lt (by rw [pushU32LE_size]; omega),
        pushU32LE_get!_lt (by omega)]
      simp only [body]; split
      · exact byteArray_get!_append_lt (by rw [hHdrSize]; exact hi)
      · exact encodeGzipStored_chunkLoop_get!_lt input i (input.size / 65535 + 2) 0 hdr (by rw [hHdrSize]; exact hi)
    have hb0 : enc.get! 0 = (0x1F : UInt8) := by rw [hGet 0 (by omega)]; rfl
    have hb1 : enc.get! 1 = (0x8B : UInt8) := by rw [hGet 1 (by omega)]; rfl
    have hb2 : enc.get! 2 = (0x08 : UInt8) := by rw [hGet 2 (by omega)]; rfl
    have hb3 : enc.get! 3 = (0x00 : UInt8) := by rw [hGet 3 (by omega)]; rfl
    have hb4 : enc.get! 4 = (0x00 : UInt8) := by rw [hGet 4 (by omega)]; rfl
    have hb5 : enc.get! 5 = (0x00 : UInt8) := by rw [hGet 5 (by omega)]; rfl
    have hb6 : enc.get! 6 = (0x00 : UInt8) := by rw [hGet 6 (by omega)]; rfl
    have hb7 : enc.get! 7 = (0x00 : UInt8) := by rw [hGet 7 (by omega)]; rfl
    change (decide (enc.size ≥ 20) && (enc.get! 0 == 0x1F) && (enc.get! 1 == 0x8B) && (enc.get! 2 == 0x08) &&
      (enc.get! 3 == 0x00) && (enc.get! 4 == 0x00) && (enc.get! 5 == 0x00) && (enc.get! 6 == 0x00) && (enc.get! 7 == 0x00)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hSz, hb0⟩, hb1⟩, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hb6⟩, hb7⟩
  | zstd =>
    unfold Model.encodeZstdStored
    dsimp only
    let fhd : UInt8 := if input.size >= 4294967296 then 0xC4 else 0x84
    let hdr :=
      if input.size >= 4294967296 then
        pushU64LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push fhd |>.push 0x38) (UInt64.ofNat input.size)
      else
        pushU32LE ((ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).push fhd |>.push 0x38) (UInt32.ofNat input.size)
    have hMSize : (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).size = 4 := rfl
    have hHdrSize : 10 ≤ hdr.size := by
      simp only [hdr]; split <;> simp only [pushU64LE_size, pushU32LE_size, ByteArray.size_push, hMSize] <;> omega
    have hHdrGet : ∀ i : Nat, i < 4 → hdr.get! i = (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).get! i := by
      intro i hi
      simp only [hdr]; split
      · rw [pushU64LE_get!_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by rw [hMSize]; exact hi)]
      · rw [pushU32LE_get!_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by simp only [ByteArray.size_push, hMSize]; omega),
          byteArray_get!_push_lt (by rw [hMSize]; exact hi)]
    let body :=
      if input.isEmpty then hdr ++ ByteArray.mk #[0x01, 0x00, 0x00]
      else Model.encodeZstdStored.chunkLoop input (input.size / 131072 + 2) 0 hdr
    have hBodyGe : 10 ≤ body.size := by
      simp only [body]; split
      · simp only [ByteArray.size_append]; omega
      · exact Nat.le_trans hHdrSize (encodeZstdStored_chunkLoop_size input (input.size / 131072 + 2) 0 hdr (Nat.zero_le _)).1
    let enc := pushU32LE body (xxh64Low32 input)
    have hSz : 9 ≤ enc.size := by
      dsimp only [enc]; simp only [pushU32LE_size]; omega
    have hGet : ∀ i : Nat, i < 4 → enc.get! i = (ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD]).get! i := by
      intro i hi
      dsimp only [enc]
      rw [pushU32LE_get!_lt (by omega)]
      simp only [body]; split
      · rw [byteArray_get!_append_lt (by omega)]; exact hHdrGet i hi
      · rw [encodeZstdStored_chunkLoop_get!_lt input i (input.size / 131072 + 2) 0 hdr (by omega)]; exact hHdrGet i hi
    have hb0 : enc.get! 0 = (0x28 : UInt8) := by rw [hGet 0 (by omega)]; rfl
    have hb1 : enc.get! 1 = (0xB5 : UInt8) := by rw [hGet 1 (by omega)]; rfl
    have hb2 : enc.get! 2 = (0x2F : UInt8) := by rw [hGet 2 (by omega)]; rfl
    have hb3 : enc.get! 3 = (0xFD : UInt8) := by rw [hGet 3 (by omega)]; rfl
    change (decide (enc.size ≥ 9) && (enc.get! 0 == 0x28) && (enc.get! 1 == 0xB5) && (enc.get! 2 == 0x2F) && (enc.get! 3 == 0xFD)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨hSz, hb0⟩, hb1⟩, hb2⟩, hb3⟩
  | xz =>
    unfold Model.encodeXzStored
    rcases xz_shdr_split (crc32 (ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04]) 6 8) with ⟨tail, hSh⟩
    refine hasCanonicalCompressedFraming_xz_parts _ tail _ _ _ _ hSh ?_ ?_ ?_
    · simp only [pushU32LE_size]; decide
    · have hBuf1Ge : ∀ (recs : Array (Nat × Nat)) (fuel i : Nat) (buf : ByteArray),
          buf.size ≤ (Model.encodeXzStored.buildIdx recs fuel i buf).size := by
        intro recs fuel
        induction fuel with
        | zero => intro i buf; simp only [Model.encodeXzStored.buildIdx]; exact Nat.le_refl _
        | succ f ih =>
          intro i buf
          unfold Model.encodeXzStored.buildIdx
          dsimp only
          split
          · exact Nat.le_refl _
          · have := ih (i + 1) (buf ++ Model.encodeXzVli recs[i]!.1 ++ Model.encodeXzVli recs[i]!.2)
            simp only [ByteArray.size_append] at this
            omega
      have hPad8 : ∀ (b : ByteArray) (c : UInt32), 1 ≤ b.size →
          8 ≤ (pushU32LE (pushReplicateByte b 0x00 ((4 - b.size % 4) % 4)) c).size := by
        intro b c hb; simp only [pushU32LE_size, pushReplicateByte_size]; omega
      apply hPad8
      exact Nat.le_trans (by have hE : ByteArray.empty.size = 0 := rfl; simp only [ByteArray.size_append, ByteArray.size_push, hE]; omega)
        (hBuf1Ge _ _ _ _)
    · have hEmptySz : ByteArray.empty.size = 0 := rfl
      have h2 : (ByteArray.mk #[0x00, 0x04]).size = 2 := rfl
      simp only [ByteArray.size_append, pushU32LE_size, hEmptySz, h2]

set_option maxRecDepth 8192 in
/-- Proof of `test_compress_model_framingRejectsCrossCodecAndLegacy` for `Model.encodeStored` and `Model.hasGzipHeader`. -/
theorem proof_compress_model_framingRejectsCrossCodecAndLegacy :
    AllPass (test_compress_model_framingRejectsCrossCodecAndLegacy Model.encodeStored Model.hasGzipHeader) := by
  dsimp only [test_compress_model_framingRejectsCrossCodecAndLegacy, bind, pure, assert]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_model_framingRejectsCrossCodecAndLegacy`. -/
theorem reach_compress_model_framingRejectsCrossCodecAndLegacy :
    CanReach (test_compress_model_framingRejectsCrossCodecAndLegacy Model.encodeStored Model.hasGzipHeader) :=
  proof_compress_model_framingRejectsCrossCodecAndLegacy

/-- Proof of `test_compress_model_boundsAndCanonicalFraming_tight` for `Model.maxCompressedBound` and `Model.hasCanonicalCompressedFraming`. -/
theorem proof_compress_model_boundsAndCanonicalFraming_tight :
    AllPass (test_compress_model_boundsAndCanonicalFraming_tight
      Model.maxCompressedBound Model.hasCanonicalCompressedFraming) := by
  intro codec
  dsimp only [test_compress_model_boundsAndCanonicalFraming_tight, bind, pure, assert]
  cases codec <;> exact ⟨⟨by decide, by decide, by decide⟩, rfl, rfl, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_model_boundsAndCanonicalFraming_tight`. -/
theorem reach_compress_model_boundsAndCanonicalFraming_tight :
    CanReach (test_compress_model_boundsAndCanonicalFraming_tight
      Model.maxCompressedBound Model.hasCanonicalCompressedFraming) :=
  ⟨.zstd, proof_compress_model_boundsAndCanonicalFraming_tight .zstd⟩

set_option maxRecDepth 8192 in
/-- Proof of `test_compress_model_statefulRoundTrip_andContracts_tight` for `Model.minCompressedSize`, `Model.allowedCompressStep`, `Model.allowedDecompressStep`, `Model.State.record`, and `Model.State.lookup`. -/
theorem proof_compress_model_statefulRoundTrip_andContracts_tight :
    AllPass (test_compress_model_statefulRoundTrip_andContracts_tight
      Model.minCompressedSize
      Model.allowedCompressStep Model.allowedDecompressStep
      Model.State.record Model.State.lookup) := by
  intro codec
  dsimp only [test_compress_model_statefulRoundTrip_andContracts_tight, bind, pure, assert]
  cases codec <;> exact ⟨⟨rfl, rfl, rfl, by decide⟩, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_model_statefulRoundTrip_andContracts_tight`. -/
theorem reach_compress_model_statefulRoundTrip_andContracts_tight :
    CanReach (test_compress_model_statefulRoundTrip_andContracts_tight
      Model.minCompressedSize
      Model.allowedCompressStep Model.allowedDecompressStep
      Model.State.record Model.State.lookup) :=
  ⟨.zstd, proof_compress_model_statefulRoundTrip_andContracts_tight .zstd⟩

private theorem isWellFormedCompressError_simple (codec : Codec) (kind : CompressErrorKind)
    (msg : String) (hne : msg.isEmpty = false)
    (hk : kind = .invalidInput ∨ kind = .toolNotFound ∨ kind = .ioError ∨
      kind = .outputLimitExceeded ∨ kind = .corruptData) :
    Model.isWellFormedCompressError codec { kind := kind, codec := some codec, message := msg } = true := by
  unfold Model.isWellFormedCompressError
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    cases codec <;> simp [hne] <;> decide

private theorem state_lookup_record_empty (codec : Codec) (comp plain : ByteArray) :
    (Model.State.empty.record codec comp plain).lookup codec comp = some plain := by
  unfold Model.State.record Model.State.lookup Model.State.empty
  have hC : (codec == codec) = true := by cases codec <;> rfl
  simp [hC]

private theorem kind_beq_self (k : CompressErrorKind) : (k == k) = true := by
  cases k <;> rfl

private theorem state_beq_self (st : Model.State) : (st == st) = true := by
  cases st with
  | mk l =>
    change List.beq l l = true
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rcases x with ⟨⟨c, k⟩, v⟩
      have hc : (c == c) = true := by cases c <;> rfl
      change (((c == c && k == k) && v == v) && List.beq xs xs) = true
      simp [hc, ih]

private theorem modelApi_run_compressWith (codec : Codec) (opts : CompressOptions) (input : ByteArray)
    (st₀ : Model.State) (env : Model.CompressEnv) :
    ((Model.modelApi.compressWith codec opts input).run st₀).run env =
      if !Model.isValidCompressInput codec opts input then
        (.error { kind := .invalidInput, codec := some codec, message := "invalid compress options or input size" }, st₀)
      else
        match Model.envPrecheckError env codec with
        | some e => (.error e, st₀)
        | none =>
          let comp := Model.encodeStored codec input
          if comp.size > opts.maxOutputBytes then
            (.error { kind := .outputLimitExceeded, codec := some codec, message := Model.codecProgram codec ++ " output exceeded maxOutputBytes" }, st₀)
          else
            (.ok comp, st₀.record codec comp input) := by
  unfold Model.modelApi
  dsimp only [StateT.run, ReaderT.run, bind, Bind.bind, pure, Pure.pure,
    read, readThe, MonadReaderOf.read, ReaderT.read,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
    StateT.bind, StateT.pure, ReaderT.bind, ReaderT.pure,
    liftM, monadLift, MonadLift.monadLift, StateT.lift,
    Monad.toBind, Applicative.toPure]
  try unfold StateT.lift
  try unfold StateT.bind
  try unfold StateT.pure
  try unfold StateT.get
  try unfold StateT.set
  dsimp only [bind, Bind.bind, pure, Pure.pure, Monad.toBind, Applicative.toPure]
  try unfold ReaderT.bind
  try unfold ReaderT.pure
  try unfold ReaderT.read
  dsimp only [bind, Bind.bind, pure, Pure.pure, Monad.toBind, Applicative.toPure]
  by_cases hv : Model.isValidCompressInput codec opts input = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases Model.envPrecheckError env codec with
    | some e => simp
    | none =>
      by_cases hl : (Model.encodeStored codec input).size > opts.maxOutputBytes <;> simp [hl]
  · simp only [hv, Bool.not_false, ↓reduceIte]

private theorem modelApi_run_decompressWith (codec : Codec) (opts : DecompressOptions) (input : ByteArray)
    (st₀ : Model.State) (env : Model.CompressEnv) :
    ((Model.modelApi.decompressWith codec opts input).run st₀).run env =
      if !Model.isValidDecompressInput opts input then
        (.error { kind := .invalidInput, codec := some codec, message := "invalid decompress options or input size" }, st₀)
      else
        match Model.envPrecheckError env codec with
        | some e => (.error e, st₀)
        | none =>
          match st₀.lookup codec input with
          | some expected =>
            if expected.size > opts.maxOutputBytes then
              (.error { kind := .outputLimitExceeded, codec := some codec, message := Model.codecProgram codec ++ " output exceeded maxOutputBytes" }, st₀)
            else
              (.ok expected, st₀)
          | none =>
            (.error { kind := .corruptData, codec := some codec, message := Model.codecProgram codec ++ " corrupt compressed stream" }, st₀) := by
  unfold Model.modelApi
  dsimp only [StateT.run, ReaderT.run, bind, Bind.bind, pure, Pure.pure,
    read, readThe, MonadReaderOf.read, ReaderT.read,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
    StateT.bind, StateT.pure, ReaderT.bind, ReaderT.pure,
    liftM, monadLift, MonadLift.monadLift, StateT.lift,
    Monad.toBind, Applicative.toPure]
  try unfold StateT.lift
  try unfold StateT.bind
  try unfold StateT.pure
  try unfold StateT.get
  try unfold StateT.set
  dsimp only [bind, Bind.bind, pure, Pure.pure, Monad.toBind, Applicative.toPure]
  try unfold ReaderT.bind
  try unfold ReaderT.pure
  try unfold ReaderT.read
  dsimp only [bind, Bind.bind, pure, Pure.pure, Monad.toBind, Applicative.toPure]
  by_cases hv : Model.isValidDecompressInput opts input = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases Model.envPrecheckError env codec with
    | some e => simp
    | none =>
      dsimp only
      cases st₀.lookup codec input with
      | none => rfl
      | some expected =>
        by_cases hl : expected.size > opts.maxOutputBytes <;> simp [hl]
  · simp only [hv, Bool.not_false, ↓reduceIte]

private theorem modelApi_compressWith_step_sound (env : Model.CompressEnv) (st₀ : Model.State)
    (codec : Codec) (opts : CompressOptions) (input : ByteArray)
    (hFresh : (st₀.lookup codec (Model.encodeStored codec input)).all (· == input) = true) :
    let r := ((Model.modelApi.compressWith codec opts input).run st₀).run env
    Model.allowedCompressStep env st₀ codec opts input r.1 r.2 = true := by
  dsimp only
  rw [modelApi_run_compressWith]
  unfold Model.allowedCompressStep
  by_cases hv : Model.isValidCompressInput codec opts input = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hst : env.toolStatus codec with
    | missingOrNonExec =>
      have hw : Model.isWellFormedCompressError codec
          { kind := .toolNotFound, codec := some codec, message := Model.codecProgram codec ++ " not found or not executable" } = true :=
        isWellFormedCompressError_simple codec .toolNotFound _ (by cases codec <;> decide) (Or.inr (Or.inl rfl))
      simp [Model.envPrecheckError, hst, hw, state_beq_self, kind_beq_self]
    | pathSymlinkLoop =>
      have hw : Model.isWellFormedCompressError codec
          { kind := .invalidInput, codec := some codec, message := Model.codecProgram codec ++ " PATH symlink loop" } = true :=
        isWellFormedCompressError_simple codec .invalidInput _ (by cases codec <;> decide) (Or.inl rfl)
      simp [Model.envPrecheckError, hst, hw, state_beq_self, kind_beq_self]
    | pathOrPipeIoError =>
      have hw : Model.isWellFormedCompressError codec
          { kind := .ioError, codec := some codec, message := Model.codecProgram codec ++ " PATH or pipe I/O error" } = true :=
        isWellFormedCompressError_simple codec .ioError _ (by cases codec <;> decide) (Or.inr (Or.inr (Or.inl rfl)))
      simp [Model.envPrecheckError, hst, hw, state_beq_self, kind_beq_self]
    | available =>
      simp only [Model.envPrecheckError, hst]
      by_cases hlim : (Model.encodeStored codec input).size > opts.maxOutputBytes
      · have hBnd := encodeStored_size_le_maxCompressedBound codec input
        have hLt : opts.maxOutputBytes < Model.maxCompressedBound codec input.size := by omega
        have hw : Model.isWellFormedCompressError codec
            { kind := .outputLimitExceeded, codec := some codec, message := Model.codecProgram codec ++ " output exceeded maxOutputBytes" } = true :=
          isWellFormedCompressError_simple codec .outputLimitExceeded _ (by cases codec <;> decide)
            (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        simp [hlim, hw, hLt, state_beq_self, kind_beq_self]
      · have hLe : (Model.encodeStored codec input).size ≤ opts.maxOutputBytes := by omega
        simp [hlim, hLe, state_beq_self,
          show (Model.ToolEnvStatus.available == Model.ToolEnvStatus.available) = true from rfl,
          hasCanonicalCompressedFraming_encodeStored codec input]
        cases h : st₀.lookup codec (Model.encodeStored codec input) with
        | none => rfl
        | some prev => simp [h] at hFresh; rw [beq_iff_eq]; exact hFresh
  · have hf : Model.isValidCompressInput codec opts input = false := Bool.eq_false_iff.mpr hv
    have hw : Model.isWellFormedCompressError codec
        { kind := .invalidInput, codec := some codec, message := "invalid compress options or input size" } = true :=
      isWellFormedCompressError_simple codec .invalidInput _ (by decide) (Or.inl rfl)
    simp [hf, hw, state_beq_self, kind_beq_self]

private theorem modelApi_decompressWith_step_sound (env : Model.CompressEnv) (st₀ : Model.State)
    (codec : Codec) (opts : DecompressOptions) (input : ByteArray) :
    let r := ((Model.modelApi.decompressWith codec opts input).run st₀).run env
    Model.allowedDecompressStep env st₀ codec opts input r.1 r.2 = true := by
  dsimp only
  rw [modelApi_run_decompressWith]
  unfold Model.allowedDecompressStep
  by_cases hv : Model.isValidDecompressInput opts input = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hst : env.toolStatus codec with
    | missingOrNonExec =>
      have hw : Model.isWellFormedCompressError codec
          { kind := .toolNotFound, codec := some codec, message := Model.codecProgram codec ++ " not found or not executable" } = true :=
        isWellFormedCompressError_simple codec .toolNotFound _ (by cases codec <;> decide) (Or.inr (Or.inl rfl))
      simp [Model.envPrecheckError, hst, hw, state_beq_self, kind_beq_self]
    | pathSymlinkLoop =>
      have hw : Model.isWellFormedCompressError codec
          { kind := .invalidInput, codec := some codec, message := Model.codecProgram codec ++ " PATH symlink loop" } = true :=
        isWellFormedCompressError_simple codec .invalidInput _ (by cases codec <;> decide) (Or.inl rfl)
      simp [Model.envPrecheckError, hst, hw, state_beq_self, kind_beq_self]
    | pathOrPipeIoError =>
      have hw : Model.isWellFormedCompressError codec
          { kind := .ioError, codec := some codec, message := Model.codecProgram codec ++ " PATH or pipe I/O error" } = true :=
        isWellFormedCompressError_simple codec .ioError _ (by cases codec <;> decide) (Or.inr (Or.inr (Or.inl rfl)))
      simp [Model.envPrecheckError, hst, hw, state_beq_self, kind_beq_self]
    | available =>
      simp only [Model.envPrecheckError, hst]
      cases hlk : st₀.lookup codec input with
      | none =>
        have hw : Model.isWellFormedCompressError codec
            { kind := .corruptData, codec := some codec, message := Model.codecProgram codec ++ " corrupt compressed stream" } = true :=
          isWellFormedCompressError_simple codec .corruptData _ (by cases codec <;> decide)
            (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        simp [hw, state_beq_self, kind_beq_self]
      | some expected =>
        by_cases hlim : expected.size > opts.maxOutputBytes
        · have hw : Model.isWellFormedCompressError codec
              { kind := .outputLimitExceeded, codec := some codec, message := Model.codecProgram codec ++ " output exceeded maxOutputBytes" } = true :=
            isWellFormedCompressError_simple codec .outputLimitExceeded _ (by cases codec <;> decide)
              (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          simp [hlim, hw, state_beq_self, kind_beq_self]
        · have hLe : expected.size ≤ opts.maxOutputBytes := by omega
          simp [hlim, hLe, state_beq_self]
  · have hf : Model.isValidDecompressInput opts input = false := Bool.eq_false_iff.mpr hv
    have hw : Model.isWellFormedCompressError codec
        { kind := .invalidInput, codec := some codec, message := "invalid decompress options or input size" } = true :=
      isWellFormedCompressError_simple codec .invalidInput _ (by decide) (Or.inl rfl)
    simp [hf, hw, state_beq_self, kind_beq_self]

/-- Formal soundness proof of stateful `Model.modelApi` against `allowedCompressStep`, `allowedDecompressStep`, `allowedIsToolAvailable`, and multi-step round-trip replay. -/
theorem proof_compress_modelApi_soundAgainstAllowedOutcome :
    AllPass (test_compress_modelApi_soundAgainstAllowedOutcome Model.modelApi) := by
  intro env codec copts dopts input rawBytes
  dsimp only [test_compress_modelApi_soundAgainstAllowedOutcome, bind, pure, assert]
  have hc0 := modelApi_compressWith_step_sound env Model.State.empty codec {} input (by simp [Model.State.empty, Model.State.lookup])
  have hc1 := modelApi_compressWith_step_sound env Model.State.empty codec copts input (by simp [Model.State.empty, Model.State.lookup])
  have hd0 := modelApi_decompressWith_step_sound env Model.State.empty codec {} rawBytes
  let stD0 := ((Model.modelApi.decompress codec rawBytes).run Model.State.empty).run env |>.2
  have hd1 := modelApi_decompressWith_step_sound env stD0 codec dopts rawBytes
  have ha :
      Model.allowedIsToolAvailable env codec (((Model.modelApi.isToolAvailable codec).run Model.State.empty).run env).1 = true ∧
      (((Model.modelApi.isToolAvailable codec).run Model.State.empty).run env).2 = Model.State.empty := by
    change Model.allowedIsToolAvailable env codec (env.toolStatus codec == Model.ToolEnvStatus.available) = true ∧
      Model.State.empty = Model.State.empty
    unfold Model.allowedIsToolAvailable
    constructor
    · cases hst : env.toolStatus codec <;> simp
      · cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> simp <;> rfl
      all_goals rfl
    · rfl
  refine ⟨hc0, ?_, hc1, ?_, hd0, hd1, ha, trivial⟩
  · cases hFst : (Model.modelApi.1 codec input Model.State.empty env).fst with
    | error _ => rfl
    | ok comp0 =>
      let stC0 := (Model.modelApi.1 codec input Model.State.empty env).snd
      have hr1 : Model.allowedDecompressStep env stC0 codec {} comp0
          (ReaderT.run ((Model.modelApi.decompress codec comp0).run stC0) env).1
          (ReaderT.run ((Model.modelApi.decompress codec comp0).run stC0) env).2 = true :=
        modelApi_decompressWith_step_sound env stC0 codec {} comp0
      let stRt0 := (ReaderT.run ((Model.modelApi.decompress codec comp0).run stC0) env).2
      have hr2 : Model.allowedDecompressStep env stRt0 codec dopts comp0
          (ReaderT.run ((Model.modelApi.decompressWith codec dopts comp0).run stRt0) env).1
          (ReaderT.run ((Model.modelApi.decompressWith codec dopts comp0).run stRt0) env).2 = true :=
        modelApi_decompressWith_step_sound env stRt0 codec dopts comp0
      exact (Bool.and_eq_true _ _).mpr ⟨hr1, hr2⟩
  · cases hFst : (Model.modelApi.3 codec copts input Model.State.empty env).fst with
    | error _ => rfl
    | ok comp =>
      exact modelApi_decompressWith_step_sound env (Model.modelApi.3 codec copts input Model.State.empty env).snd codec dopts comp

/-- Non-vacuity `CanReach` witness for `test_compress_modelApi_soundAgainstAllowedOutcome`. -/
theorem reach_compress_modelApi_soundAgainstAllowedOutcome :
    CanReach (test_compress_modelApi_soundAgainstAllowedOutcome Model.modelApi) :=
  ⟨{}, .zstd, {}, {}, ByteArray.empty, ByteArray.empty,
    proof_compress_modelApi_soundAgainstAllowedOutcome {} .zstd {} {} ByteArray.empty ByteArray.empty⟩

private theorem decodeStderr_isEmpty_false (bs : ByteArray) (s : String)
    (h : Internal.decodeStderr bs = some s) : s.isEmpty = false := by
  unfold Internal.decodeStderr at h
  by_cases hem : bs.isEmpty = true
  · simp [hem] at h
  · have hne : bs.isEmpty = false := Bool.eq_false_iff.mpr hem
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    unfold String.fromUTF8? at h
    split at h
    · cases h; exact hne
    · cases h

private theorem string_ne_empty_iff_isEmpty_false (s : String) (hne : s ≠ "") :
    s.isEmpty = false := by
  cases hs : s.isEmpty with
  | false => rfl
  | true =>
    exfalso
    apply hne
    simp [String.isEmpty] at hs
    exact hs

private theorem toolStatus_eq_of_beq {a b : Model.ToolEnvStatus} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem classifyProcessError_wellFormed (codec : Codec) (pe : ProcessError) :
    Model.isWellFormedCompressError codec (Internal.classifyProcessError codec pe) = true := by
  have hSpec := classifyProcessError_spec codec pe
  rcases hSpec with ⟨hk, hc, hex, herr, hne, _⟩
  let e := Internal.classifyProcessError codec pe
  have hStderrOk : (match e.stderr with | some s => !s.isEmpty | none => true) = true := by
    change (match (Internal.classifyProcessError codec pe).stderr with | some s => !s.isEmpty | none => true) = true
    rw [herr]
    cases expectedProcessErrorKindFor pe with
    | toolNotFound => rfl
    | invalidInput => rfl
    | corruptData | outputLimitExceeded | timedOut | commandFailed | ioError =>
      cases hps : pe.stderr with
      | none => rfl
      | some bs =>
        change (match expectedStderr bs with | some s => !s.isEmpty | none => true) = true
        cases hds : expectedStderr bs with
        | none => rfl
        | some s =>
          have hsf : s.isEmpty = false := decodeStderr_isEmpty_false bs s hds
          simp [hsf]
  have hKindOk :
      (match e.kind with
      | .toolNotFound => e.exitCode.isNone && e.stderr.isNone
      | .invalidInput => e.exitCode.isNone && e.stderr.isNone
      | .outputLimitExceeded => e.exitCode.isNone
      | .timedOut => e.exitCode.isNone
      | .ioError => e.exitCode.isNone
      | .corruptData =>
        (match e.exitCode with
        | some c => c != 0
        | none => true)
      | .commandFailed =>
        (match e.exitCode with
        | some c => c != 0
        | none => true)) = true := by
    change (match e.kind with
      | .toolNotFound => e.exitCode.isNone && e.stderr.isNone
      | .invalidInput => e.exitCode.isNone && e.stderr.isNone
      | .outputLimitExceeded => e.exitCode.isNone
      | .timedOut => e.exitCode.isNone
      | .ioError => e.exitCode.isNone
      | .corruptData => (match e.exitCode with | some c => c != 0 | none => true)
      | .commandFailed => (match e.exitCode with | some c => c != 0 | none => true)) = true
    rw [hk, hex, herr]
    cases hpk : pe.kind with
    | notFound =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
    | permissionDenied =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
    | invalidInput =>
      by_cases hRes : isResourceExhaustedProcessError pe <;>
        simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hRes]
    | timedOut =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
    | outputLimitExceeded =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
    | ioError =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
    | terminatedBySignal =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      cases hpc : pe.exitCode with
      | none => simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
      | some c =>
        simp only [expectedProcessErrorKindFor, hResF, Bool.false_eq_true, ↓reduceIte,
          expectedProcessErrorKind, expectedProcessErrorExitCode, hpk]
        by_cases hc0 : (c != 0) = true <;> simp [hc0]
    | nonZeroExit =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      cases hpc : pe.exitCode with
      | none => simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
      | some c =>
        simp only [expectedProcessErrorKindFor, hResF, Bool.false_eq_true, ↓reduceIte,
          expectedProcessErrorKind, expectedProcessErrorExitCode, hpk]
        by_cases hc0 : (c != 0) = true <;> simp [hc0]
  have hMsgOk : e.message.isEmpty = false := string_ne_empty_iff_isEmpty_false e.message hne
  unfold Model.isWellFormedCompressError
  change (e.codec == some codec && !e.message.isEmpty &&
    (match e.stderr with | some s => !s.isEmpty | none => true) &&
    (match e.kind with
    | .toolNotFound => e.exitCode.isNone && e.stderr.isNone
    | .invalidInput => e.exitCode.isNone && e.stderr.isNone
    | .outputLimitExceeded => e.exitCode.isNone
    | .timedOut => e.exitCode.isNone
    | .ioError => e.exitCode.isNone
    | .corruptData => (match e.exitCode with | some c => c != 0 | none => true)
    | .commandFailed => (match e.exitCode with | some c => c != 0 | none => true))) = true
  rw [hc, hMsgOk, hStderrOk, hKindOk]
  have hCod : (some codec == some codec) = true := by cases codec <;> rfl
  simp [hCod]

private theorem classifyExitResult_wellFormed_of_err (codec : Codec) (isDecompress : Bool)
    (maxOut : Nat) (input : ByteArray) (res : ExecResult) {e : CompressError}
    (h : Internal.classifyExitResult codec isDecompress maxOut input res = .error e) :
    Model.isWellFormedCompressError codec e = true := by
  have hCod : (some codec == some codec) = true := by cases codec <;> rfl
  have hSerr : (match Internal.decodeStderr res.stderr with | some s => !s.isEmpty | none => true) = true := by
    cases hds : Internal.decodeStderr res.stderr with
    | none => rfl
    | some s =>
      have hsf := decodeStderr_isEmpty_false res.stderr s hds
      simp [hsf]
  unfold Internal.classifyExitResult at h
  by_cases hNz : (res.exitCode != 0) = true
  · simp only [hNz, ↓reduceIte] at h
    cases h
    unfold Model.isWellFormedCompressError
    have hMsg :
        (match Internal.decodeStderr res.stderr with
        | some s => Internal.nonEmptyMsg
            (if isDecompress then Internal.codecProgram codec ++ " decompression failed with exit code " ++ toString res.exitCode
             else Internal.codecProgram codec ++ " compression failed with exit code " ++ toString res.exitCode) s
        | none =>
            if isDecompress then Internal.codecProgram codec ++ " decompression failed with exit code " ++ toString res.exitCode
            else Internal.codecProgram codec ++ " compression failed with exit code " ++ toString res.exitCode).isEmpty = false :=
      string_ne_empty_iff_isEmpty_false _ (classifyExitResult_nonzero_msg codec isDecompress res)
    dsimp only
    change ((some codec == some codec &&
      !(match Internal.decodeStderr res.stderr with
        | some s => Internal.nonEmptyMsg
            (if isDecompress then Internal.codecProgram codec ++ " decompression failed with exit code " ++ toString res.exitCode
             else Internal.codecProgram codec ++ " compression failed with exit code " ++ toString res.exitCode) s
        | none =>
            if isDecompress then Internal.codecProgram codec ++ " decompression failed with exit code " ++ toString res.exitCode
            else Internal.codecProgram codec ++ " compression failed with exit code " ++ toString res.exitCode).isEmpty) &&
      (match Internal.decodeStderr res.stderr with | some s => !s.isEmpty | none => true) &&
      (match (if isDecompress then CompressErrorKind.corruptData else .commandFailed) with
      | .toolNotFound => false
      | .invalidInput => false
      | .outputLimitExceeded => false
      | .timedOut => false
      | .ioError => false
      | .corruptData => res.exitCode != 0
      | .commandFailed => res.exitCode != 0)) = true
    rw [hCod, hMsg, hSerr]
    cases isDecompress <;> simp [hNz]
  · simp only [hNz, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hOut : res.stdout.size > maxOut
    · simp only [hOut, ↓reduceIte] at h
      by_cases hGh : (isDecompress && codec == .gzip && !Internal.hasGzipHeader input) = true
      · simp only [hGh, ↓reduceIte] at h
        cases h
        exact isWellFormedCompressError_simple codec .corruptData _ (by cases codec <;> decide)
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · have hGhF : (isDecompress && codec == .gzip && !Internal.hasGzipHeader input) = false :=
          Bool.eq_false_iff.mpr hGh
        simp only [hGhF, Bool.false_eq_true, ↓reduceIte] at h
        cases h
        unfold Model.isWellFormedCompressError
        have hMsg : (Internal.codecProgram codec ++ " output exceeded maxOutputBytes").isEmpty = false :=
          string_ne_empty_iff_isEmpty_false _ (append_head_ne_empty _ _ (codecProgram_ne_empty codec))
        dsimp only
        rw [hMsg]
        simp only [hCod, Option.isNone_none, Bool.and_true, Bool.true_and]
        exact hSerr
    · simp only [hOut, ↓reduceIte] at h
      by_cases hGh : (isDecompress && codec == .gzip && !Internal.hasGzipHeader input) = true
      · simp only [hGh, ↓reduceIte] at h
        cases h
        exact isWellFormedCompressError_simple codec .corruptData _ (by cases codec <;> decide)
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · have hGhF : (isDecompress && codec == .gzip && !Internal.hasGzipHeader input) = false :=
          Bool.eq_false_iff.mpr hGh
        simp only [hGhF, Bool.false_eq_true, ↓reduceIte] at h
        cases h

/-- Wiring theorem: `Compress.defaultApi` is `Internal.mkApiM LeanSwe.Process.defaultApi`. -/
theorem compress_defaultApi_eq :
    Compress.defaultApi = Internal.mkApiM LeanSwe.Process.defaultApi := rfl

/-- Wiring theorem: `Compress.compressWith` delegates to `Internal.compressWith LeanSwe.Process.defaultApi`. -/
theorem compress_compressWith_eq (codec : Codec) (opts : CompressOptions) (input : ByteArray) :
    Compress.compressWith codec opts input =
      Internal.compressWith LeanSwe.Process.defaultApi codec opts input := rfl

/-- Wiring theorem: `Compress.decompressWith` delegates to `Internal.decompressWith LeanSwe.Process.defaultApi`. -/
theorem compress_decompressWith_eq (codec : Codec) (opts : DecompressOptions) (input : ByteArray) :
    Compress.decompressWith codec opts input =
      Internal.decompressWith LeanSwe.Process.defaultApi codec opts input := rfl

/-- Wiring theorem: `Compress.compress` delegates to `Compress.compressWith codec {}`. -/
theorem compress_compress_eq (codec : Codec) (input : ByteArray) :
    Compress.compress codec input = Compress.compressWith codec {} input := rfl

/-- Wiring theorem: `Compress.decompress` delegates to `Compress.decompressWith codec {}`. -/
theorem compress_decompress_eq (codec : Codec) (input : ByteArray) :
    Compress.decompress codec input = Compress.decompressWith codec {} input := rfl

/-- Wiring theorem: `Compress.isToolAvailable` delegates to `Internal.isToolAvailable LeanSwe.Process.defaultApi`. -/
theorem compress_isToolAvailable_eq (codec : Codec) :
    Compress.isToolAvailable codec = Internal.isToolAvailable LeanSwe.Process.defaultApi codec := rfl

private theorem framingErr_wellFormed (codec : Codec) (err? : Option ByteArray) :
    Model.isWellFormedCompressError codec
      { kind := .corruptData, codec := some codec, exitCode := none,
        stderr := err?.bind Internal.decodeStderr,
        message := Internal.codecProgram codec ++ " compressed stream failed gzip header check" } = true := by
  unfold Model.isWellFormedCompressError
  have hCod : (some codec == some codec) = true := by cases codec <;> rfl
  have hMsg : (Internal.codecProgram codec ++ " compressed stream failed gzip header check").isEmpty = false :=
    string_ne_empty_iff_isEmpty_false _ (append_head_ne_empty _ _ (codecProgram_ne_empty codec))
  have hSerr : (match err?.bind Internal.decodeStderr with | some s => !s.isEmpty | none => true) = true := by
    cases err? with
    | none => rfl
    | some bs =>
      change (match Internal.decodeStderr bs with | some s => !s.isEmpty | none => true) = true
      cases hds : Internal.decodeStderr bs with
      | none => rfl
      | some s =>
        have hsf := decodeStderr_isEmpty_false bs s hds
        simp [hsf]
  dsimp only
  rw [hMsg]
  simp only [hCod, Bool.not_false, Bool.and_true, Bool.true_and]
  exact hSerr

private theorem internalApi_compressWith_sound (env : Model.CompressEnv) (st₀ : Model.State)
    (codec : Codec) (opts : CompressOptions) (input : ByteArray)
    (rawC : Except ProcessError ExecResult)
    (hConf : rawCompressCallConforms env st₀ codec opts input rawC = true) :
    let res := (Internal.mkApiM (scriptedProcessApiId rawC)).compressWith codec opts input
    let st₁ := match res with | .ok c => st₀.record codec c input | .error _ => st₀
    Model.allowedCompressStep env st₀ codec opts input res st₁ = true := by
  unfold Internal.mkApiM Internal.compressWith Model.allowedCompressStep
  dsimp only
  by_cases hv : isValidCompressInput codec opts input = true
  · rcases validateCompressOptions_true_implies_ok codec opts input hv with ⟨hVal, _⟩
    have hvM : Model.isValidCompressInput codec opts input = true := hv
    simp only [hvM, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hVal]
    dsimp only [scriptedProcessApiId, bind, pure, Id.run]
    cases rawC with
    | error pe =>
      dsimp only
      have hWf := classifyProcessError_wellFormed codec pe
      have hSpec := classifyProcessError_spec codec pe
      dsimp only [rawCompressCallConforms] at hConf
      rcases (Bool.and_eq_true _ _).mp hConf with ⟨_, hCond⟩
      simp only [state_beq_self, Bool.true_and]
      cases hpk : pe.kind <;> simp only [hpk] at hCond hSpec
      · have hS := toolStatus_eq_of_beq hCond
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .toolNotFound := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        simp only [Model.allowedTransientError, hk, hS, hWf]
        cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> rfl
      · have hS := toolStatus_eq_of_beq hCond
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .toolNotFound := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        simp only [Model.allowedTransientError, hk, hS, hWf]
        cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> rfl
      · by_cases hRes : isResourceExhaustedProcessError pe = true
        · have hk : (Internal.classifyProcessError codec pe).kind = .ioError := by
            simpa [expectedProcessErrorKindFor, hRes] using hSpec.1
          simp only [hRes, ↓reduceIte] at hCond
          rcases (Bool.or_eq_true _ _).mp hCond with hSt | hIo
          · have hS := toolStatus_eq_of_beq hSt
            simp only [Model.allowedTransientError, hk, hS, hWf]
            cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> simp <;>
              first | rfl | exact Or.inl rfl | exact Or.inr rfl | decide
          · simp [Model.allowedTransientError, hk, hWf, hIo,
              show (CompressErrorKind.ioError == CompressErrorKind.ioError) = true from rfl]
        · have hResF : isResourceExhaustedProcessError pe = false := Bool.eq_false_iff.mpr hRes
          simp only [hResF, Bool.false_eq_true, ↓reduceIte] at hCond
          have hS := toolStatus_eq_of_beq hCond
          have hk : (Internal.classifyProcessError codec pe).kind = .invalidInput := by
            simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
          simp only [Model.allowedTransientError, hk, hS, hWf]
          cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> rfl
      · rcases (Bool.and_eq_true _ _).mp hCond with ⟨_, hT⟩
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .timedOut := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        simp [Model.allowedTransientError, hk, hWf, hT,
          show (CompressErrorKind.timedOut == CompressErrorKind.timedOut) = true from rfl]
      · rcases (Bool.and_eq_true _ _).mp hCond with ⟨hSt, hLt⟩
        have hS := toolStatus_eq_of_beq hSt
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .outputLimitExceeded := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        simp only [Model.allowedTransientError, hk, hS, hWf, decide_eq_true_eq.mp hLt]
        cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> simp <;>
          first | rfl | exact Or.inl rfl | exact Or.inr rfl | decide
      · rcases (Bool.and_eq_true _ _).mp hCond with ⟨_, hSig⟩
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .commandFailed := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        simp [Model.allowedTransientError, hk, hWf, hSig,
          show (CompressErrorKind.commandFailed == CompressErrorKind.commandFailed) = true from rfl]
      · simp at hCond
      · have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .ioError := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        rcases (Bool.or_eq_true _ _).mp hCond with hSt | hIo
        · have hS := toolStatus_eq_of_beq hSt
          simp only [Model.allowedTransientError, hk, hS, hWf]
          cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> simp <;>
            first | rfl | exact Or.inl rfl | exact Or.inr rfl | decide
        · simp [Model.allowedTransientError, hk, hWf, hIo,
            show (CompressErrorKind.ioError == CompressErrorKind.ioError) = true from rfl]
    | ok res =>
      dsimp only [rawCompressCallConforms] at hConf ⊢
      by_cases hNz : (res.exitCode != 0) = true
      · simp only [hNz, ↓reduceIte] at hConf
        rcases (Bool.and_eq_true _ _).mp hConf with ⟨_, hBr⟩
        have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec false opts.maxOutputBytes input res = .error e ∧
            e.kind = .commandFailed := by
          unfold Internal.classifyExitResult; simp only [hNz, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
        have hWf := classifyExitResult_wellFormed_of_err codec false opts.maxOutputBytes input res hEq
        rw [hEq]
        simp [state_beq_self, Model.allowedTransientError, hk, hWf, hBr,
          show (CompressErrorKind.commandFailed == CompressErrorKind.commandFailed) = true from rfl]
      · simp only [hNz, Bool.false_eq_true, ↓reduceIte] at hConf
        by_cases hOut : res.stdout.size > opts.maxOutputBytes
        · simp only [hOut, ↓reduceIte] at hConf
          rcases (Bool.and_eq_true _ _).mp hConf with ⟨hSt, hLt⟩
          have hS := toolStatus_eq_of_beq hSt
          have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec false opts.maxOutputBytes input res = .error e ∧
              e.kind = .outputLimitExceeded := by
            unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut]; exact ⟨_, rfl, rfl⟩
          have hWf := classifyExitResult_wellFormed_of_err codec false opts.maxOutputBytes input res hEq
          rw [hEq]
          simp only [state_beq_self, Bool.true_and, Model.allowedTransientError, hk, hWf, hS, decide_eq_true_eq.mp hLt]
          cases env.allowTimeout <;> cases env.allowResourceIoError <;> cases env.allowExternalSignal <;> simp <;>
            first | rfl | exact Or.inl rfl | exact Or.inr rfl | decide
        · simp only [hOut, ↓reduceIte] at hConf
          rcases (Bool.and_eq_true _ _).mp hConf with ⟨hAnd1, hLk⟩
          rcases (Bool.and_eq_true _ _).mp hAnd1 with ⟨hSt, hFrm⟩
          have hLe : res.stdout.size ≤ opts.maxOutputBytes := by omega
          have hOk : Internal.classifyExitResult codec false opts.maxOutputBytes input res = .ok res.stdout := by
            unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.false_and]
          rw [hOk]
          simp [state_beq_self, hSt, hLe, hFrm]
          exact hLk
  · have hf : isValidCompressInput codec opts input = false := Bool.eq_false_iff.mpr hv
    rcases validateCompressOptions_false_implies_error codec opts input hf with
      ⟨e, hVal, hKind, hCodec, hExit, hErr, hMsg⟩
    have hfM : Model.isValidCompressInput codec opts input = false := hf
    simp only [hfM, Bool.not_false, ↓reduceIte]
    rw [hVal]
    dsimp only [bind, pure, Id.run]
    have hWf : Model.isWellFormedCompressError codec e = true := by
      unfold Model.isWellFormedCompressError
      have hCod : (some codec == some codec) = true := by cases codec <;> rfl
      have hMsgE : e.message.isEmpty = false := string_ne_empty_iff_isEmpty_false e.message hMsg
      simp [hCodec, hCod, hMsgE, hErr, hKind, hExit]
    simp [state_beq_self, hKind, hWf, show (CompressErrorKind.invalidInput == CompressErrorKind.invalidInput) = true from rfl]

private theorem not_gzip_and_not_header_of_ok {codec : Codec} {input : ByteArray}
    (h : (codec != .gzip || Model.hasGzipHeader input) = true) :
    (codec == .gzip && !Internal.hasGzipHeader input) = false := by
  cases codec with
  | zstd | xz => rfl
  | gzip =>
    change (false || Model.hasGzipHeader input) = true at h
    rw [Bool.false_or] at h
    change (true && !Model.hasGzipHeader input) = false
    rw [Bool.true_and, Bool.not_eq_false']; exact h

private theorem gzip_or_header_of_not_err {codec : Codec} {input : ByteArray}
    (h : (codec == .gzip && !Internal.hasGzipHeader input) = false) :
    (codec != .gzip || Model.hasGzipHeader input) = true := by
  cases codec with
  | zstd | xz => rfl
  | gzip =>
    change (true && !Model.hasGzipHeader input) = false at h
    rw [Bool.true_and, Bool.not_eq_false'] at h
    change (false || Model.hasGzipHeader input) = true
    rw [Bool.false_or]; exact h

private theorem internalApi_decompressWith_sound (env : Model.CompressEnv) (st₀ : Model.State)
    (codec : Codec) (opts : DecompressOptions) (input : ByteArray)
    (rawD : Except ProcessError ExecResult)
    (hConf : rawDecompressCallConforms env st₀ codec opts input rawD = true) :
    let res := (Internal.mkApiM (scriptedProcessApiId rawD)).decompressWith codec opts input
    let st₁ := match res with | .ok o => st₀.record codec input o | .error _ => st₀
    Model.allowedDecompressStep env st₀ codec opts input res st₁ = true := by
  unfold Internal.mkApiM Internal.decompressWith Model.allowedDecompressStep
  dsimp only
  by_cases hv : isValidDecompressInput opts input = true
  · rcases validateDecompressOptions_true_implies_ok codec opts input hv with ⟨hVal, _⟩
    have hvM : Model.isValidDecompressInput opts input = true := hv
    simp only [hvM, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hVal]
    dsimp only [scriptedProcessApiId, bind, pure, Id.run]
    cases rawD with
    | error pe =>
      dsimp only
      have hWf := classifyProcessError_wellFormed codec pe
      have hSpec := classifyProcessError_spec codec pe
      dsimp only [rawDecompressCallConforms] at hConf
      rcases (Bool.and_eq_true _ _).mp hConf with ⟨_, hCond⟩
      cases hpk : pe.kind <;> simp only [hpk] at hCond hSpec
      · have hS := toolStatus_eq_of_beq hCond
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .toolNotFound := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        have hF : (ProcessErrorKind.notFound == .outputLimitExceeded ||
            ProcessErrorKind.notFound == .timedOut) = false := rfl
        simp [state_beq_self, hF, hS, hk, hWf, Model.allowedTransientError,
          show (CompressErrorKind.toolNotFound == CompressErrorKind.toolNotFound) = true from rfl]
      · have hS := toolStatus_eq_of_beq hCond
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .toolNotFound := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        have hF : (ProcessErrorKind.permissionDenied == .outputLimitExceeded ||
            ProcessErrorKind.permissionDenied == .timedOut) = false := rfl
        simp [state_beq_self, hF, hS, hk, hWf, Model.allowedTransientError,
          show (CompressErrorKind.toolNotFound == CompressErrorKind.toolNotFound) = true from rfl]
      · have hF : (ProcessErrorKind.invalidInput == .outputLimitExceeded ||
            ProcessErrorKind.invalidInput == .timedOut) = false := rfl
        simp only [hF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        by_cases hRes : isResourceExhaustedProcessError pe = true
        · simp only [hRes, ↓reduceIte] at hCond
          have hk : (Internal.classifyProcessError codec pe).kind = .ioError := by
            simpa [expectedProcessErrorKindFor, hRes] using hSpec.1
          rcases Bool.or_eq_true _ _ |>.mp hCond with hSt | hIo
          · have hS := toolStatus_eq_of_beq hSt
            simp only [hS, state_beq_self, Bool.true_and]
            simp [Model.allowedTransientError, hk, hWf]; exact Or.inr rfl
          · cases hTs : env.toolStatus codec
            · cases hLk : st₀.lookup codec input <;>
                simp [state_beq_self, Model.allowedTransientError, hk, hWf, hIo, kind_beq_self]
            all_goals
              (simp [state_beq_self, Model.allowedTransientError, hk, hWf, hIo, kind_beq_self];
               try exact Or.inl (Or.inl (Or.inr rfl)))
        · have hResF : isResourceExhaustedProcessError pe = false := Bool.eq_false_iff.mpr hRes
          simp only [hResF, Bool.false_eq_true, ↓reduceIte] at hCond
          have hS := toolStatus_eq_of_beq hCond
          have hk : (Internal.classifyProcessError codec pe).kind = .invalidInput := by
            simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
          simp [state_beq_self, hS, hk, hWf, Model.allowedTransientError,
            show (CompressErrorKind.invalidInput == CompressErrorKind.invalidInput) = true from rfl]
      · dsimp only [rawTimedOutDecompressConforms] at hCond
        rcases (Bool.and_eq_true _ _).mp hCond with ⟨hAnd1, hLkFrm⟩
        rcases (Bool.and_eq_true _ _).mp hAnd1 with ⟨hSt, hT⟩
        have hS := toolStatus_eq_of_beq hSt
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .timedOut := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        have hTrm : (ProcessErrorKind.timedOut == .outputLimitExceeded ||
            ProcessErrorKind.timedOut == .timedOut) = true := rfl
        cases hLk : st₀.lookup codec input with
        | some expected =>
          simp only [hLk] at hLkFrm
          have hGhF := not_gzip_and_not_header_of_ok hLkFrm
          simp only [hTrm, Bool.true_and, hGhF, Bool.false_eq_true, ↓reduceIte, hS]
          simp [state_beq_self, Model.allowedTransientError, hk, hWf, hT, kind_beq_self]
        | none =>
          by_cases hGh : (codec == .gzip && !Internal.hasGzipHeader input) = true
          · have hWfF := framingErr_wellFormed codec pe.stderr
            simp only [hTrm, Bool.true_and, hGh, ↓reduceIte, hS]
            simp [state_beq_self, Model.allowedTransientError, hWfF, kind_beq_self]
          · have hGhF : (codec == .gzip && !Internal.hasGzipHeader input) = false :=
              Bool.eq_false_iff.mpr hGh
            simp only [hTrm, Bool.true_and, hGhF, Bool.false_eq_true, ↓reduceIte, hS]
            simp [state_beq_self, Model.allowedTransientError, hk, hWf, hT, kind_beq_self]
      · rcases (Bool.and_eq_true _ _).mp hCond with ⟨hSt, hLkCond⟩
        have hS := toolStatus_eq_of_beq hSt
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .outputLimitExceeded := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        have hTrm : (ProcessErrorKind.outputLimitExceeded == .outputLimitExceeded ||
            ProcessErrorKind.outputLimitExceeded == .timedOut) = true := rfl
        cases hLk : st₀.lookup codec input with
        | some expected =>
          simp only [hLk] at hLkCond
          rcases (Bool.and_eq_true _ _).mp hLkCond with ⟨hGt, hFrm⟩
          have hGhF := not_gzip_and_not_header_of_ok hFrm
          simp only [hTrm, Bool.true_and, hGhF, Bool.false_eq_true, ↓reduceIte, hS]
          simp [state_beq_self, Model.allowedTransientError, hk, hWf, hGt, kind_beq_self]
        | none =>
          by_cases hGh : (codec == .gzip && !Internal.hasGzipHeader input) = true
          · have hWfF := framingErr_wellFormed codec pe.stderr
            simp only [hTrm, Bool.true_and, hGh, ↓reduceIte, hS]
            simp [state_beq_self, Model.allowedTransientError, hWfF, kind_beq_self]
          · have hGhF : (codec == .gzip && !Internal.hasGzipHeader input) = false :=
              Bool.eq_false_iff.mpr hGh
            simp only [hTrm, Bool.true_and, hGhF, Bool.false_eq_true, ↓reduceIte, hS]
            simp [state_beq_self, Model.allowedTransientError, hk, hWf, kind_beq_self]
      · rcases (Bool.and_eq_true _ _).mp hCond with ⟨hSt, hSig⟩
        have hS := toolStatus_eq_of_beq hSt
        have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .commandFailed := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        have hF : (ProcessErrorKind.terminatedBySignal == .outputLimitExceeded ||
            ProcessErrorKind.terminatedBySignal == .timedOut) = false := rfl
        simp only [hF, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hS]
        cases hLk : st₀.lookup codec input <;>
          simp [state_beq_self, Model.allowedTransientError, hk, hWf, hSig, kind_beq_self]
      · simp at hCond
      · have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
        have hk : (Internal.classifyProcessError codec pe).kind = .ioError := by
          simpa [expectedProcessErrorKindFor, hResF, expectedProcessErrorKind, hpk] using hSpec.1
        have hF : (ProcessErrorKind.ioError == .outputLimitExceeded ||
            ProcessErrorKind.ioError == .timedOut) = false := rfl
        simp only [hF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rcases Bool.or_eq_true _ _ |>.mp hCond with hSt | hIo
        · have hS := toolStatus_eq_of_beq hSt
          simp only [hS]
          simp [state_beq_self, Model.allowedTransientError, hk, hWf, kind_beq_self]
        · cases hTs : env.toolStatus codec
          · cases hLk : st₀.lookup codec input <;>
              simp [state_beq_self, Model.allowedTransientError, hk, hWf, hIo, kind_beq_self]
          all_goals
            (simp [state_beq_self, Model.allowedTransientError, hk, hWf, hIo, kind_beq_self];
             try exact Or.inl (Or.inl (Or.inr rfl)))
    | ok res =>
      dsimp only [rawDecompressCallConforms] at hConf ⊢
      rcases (Bool.and_eq_true _ _).mp hConf with ⟨hSt, hLkCond⟩
      have hS := toolStatus_eq_of_beq hSt
      cases hLk : st₀.lookup codec input with
      | some expected =>
        simp only [hLk] at hLkCond
        by_cases hNz : (res.exitCode != 0) = true
        · simp [hNz] at hLkCond
        · simp only [hNz, Bool.false_eq_true, ↓reduceIte] at hLkCond
          by_cases hOut : res.stdout.size > opts.maxOutputBytes
          · simp only [hOut, ↓reduceIte] at hLkCond
            rcases (Bool.and_eq_true _ _).mp hLkCond with ⟨hGt, hFrm⟩
            have hGhF := not_gzip_and_not_header_of_ok hFrm
            have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec true opts.maxOutputBytes input res = .error e ∧
                e.kind = .outputLimitExceeded := by
              unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.true_and, hGhF]; exact ⟨_, rfl, rfl⟩
            have hWf := classifyExitResult_wellFormed_of_err codec true opts.maxOutputBytes input res hEq
            rw [hEq]
            simp [state_beq_self, hS, Model.allowedTransientError, hk, hWf, hGt, kind_beq_self]
          · simp only [hOut, ↓reduceIte] at hLkCond
            rcases (Bool.and_eq_true _ _).mp hLkCond with ⟨hAnd1, hFrm⟩
            rcases (Bool.and_eq_true _ _).mp hAnd1 with ⟨hLe, hEqOut⟩
            have hGhF := not_gzip_and_not_header_of_ok hFrm
            have hOk : Internal.classifyExitResult codec true opts.maxOutputBytes input res = .ok res.stdout := by
              unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.true_and, hGhF]
            rw [hOk]
            unfold Model.State.record
            simp [state_beq_self, hS, hLk, hLe, hEqOut]
      | none =>
        by_cases hNz : (res.exitCode != 0) = true
        · have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec true opts.maxOutputBytes input res = .error e ∧
              e.kind = .corruptData := by
            unfold Internal.classifyExitResult; simp only [hNz, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
          have hWf := classifyExitResult_wellFormed_of_err codec true opts.maxOutputBytes input res hEq
          rw [hEq]
          simp [state_beq_self, hS, Model.allowedTransientError, hk, hWf, kind_beq_self]
        · by_cases hOut : res.stdout.size > opts.maxOutputBytes
          · by_cases hGh : (codec == .gzip && !Internal.hasGzipHeader input) = true
            · have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec true opts.maxOutputBytes input res = .error e ∧
                  e.kind = .corruptData := by
                unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.true_and, hGh]; exact ⟨_, rfl, rfl⟩
              have hWf := classifyExitResult_wellFormed_of_err codec true opts.maxOutputBytes input res hEq
              rw [hEq]
              simp [state_beq_self, hS, Model.allowedTransientError, hk, hWf, kind_beq_self]
            · have hGhF : (codec == .gzip && !Internal.hasGzipHeader input) = false :=
                Bool.eq_false_iff.mpr hGh
              have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec true opts.maxOutputBytes input res = .error e ∧
                  e.kind = .outputLimitExceeded := by
                unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.true_and, hGhF]; exact ⟨_, rfl, rfl⟩
              have hWf := classifyExitResult_wellFormed_of_err codec true opts.maxOutputBytes input res hEq
              rw [hEq]
              simp [state_beq_self, hS, Model.allowedTransientError, hk, hWf, kind_beq_self]
          · by_cases hGh : (codec == .gzip && !Internal.hasGzipHeader input) = true
            · have ⟨e, hEq, hk⟩ : ∃ e, Internal.classifyExitResult codec true opts.maxOutputBytes input res = .error e ∧
                  e.kind = .corruptData := by
                unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.true_and, hGh]; exact ⟨_, rfl, rfl⟩
              have hWf := classifyExitResult_wellFormed_of_err codec true opts.maxOutputBytes input res hEq
              rw [hEq]
              simp [state_beq_self, hS, Model.allowedTransientError, hk, hWf, kind_beq_self]
            · have hGhF : (codec == .gzip && !Internal.hasGzipHeader input) = false :=
                Bool.eq_false_iff.mpr hGh
              have hGhM := gzip_or_header_of_not_err hGhF
              have hLe : res.stdout.size ≤ opts.maxOutputBytes := by omega
              have hRes : Internal.classifyExitResult codec true opts.maxOutputBytes input res = .ok res.stdout := by
                unfold Internal.classifyExitResult; simp only [hNz, Bool.false_eq_true, ↓reduceIte, hOut, Bool.true_and, hGhF]
              rw [hRes]
              simp [state_beq_self, hS, hLe, hGhM]
  · have hf : isValidDecompressInput opts input = false := Bool.eq_false_iff.mpr hv
    rcases validateDecompressOptions_false_implies_error codec opts input hf with
      ⟨e, hVal, hKind, hCodec, hExit, hErr, hMsg⟩
    have hfM : Model.isValidDecompressInput opts input = false := hf
    simp only [hfM, Bool.not_false, ↓reduceIte]
    rw [hVal]
    dsimp only [bind, pure, Id.run]
    have hWf : Model.isWellFormedCompressError codec e = true := by
      unfold Model.isWellFormedCompressError
      have hCod : (some codec == some codec) = true := by cases codec <;> rfl
      have hMsgE : e.message.isEmpty = false := string_ne_empty_iff_isEmpty_false e.message hMsg
      simp [hCodec, hCod, hMsgE, hErr, hKind, hExit]
    simp [state_beq_self, hKind, hWf, show (CompressErrorKind.invalidInput == CompressErrorKind.invalidInput) = true from rfl]

private theorem internalApi_isToolAvailable_sound (env : Model.CompressEnv) (codec : Codec)
    (rawV : Except ProcessError ExecResult)
    (hConf : rawVersionCallConforms env codec rawV = true) :
    Model.allowedIsToolAvailable env codec
      ((Internal.mkApiM (scriptedProcessApiId rawV)).isToolAvailable codec) = true := by
  unfold Internal.mkApiM Internal.isToolAvailable Model.allowedIsToolAvailable
  dsimp only [scriptedProcessApiId, bind, pure, Id.run]
  cases rawV with
  | error _ =>
    dsimp only [rawVersionCallConforms] at hConf
    cases hTs : env.toolStatus codec <;> simp [hTs] at hConf ⊢
    exact hConf
  | ok res =>
    dsimp only [rawVersionCallConforms] at hConf ⊢
    cases hTs : env.toolStatus codec <;> simp [hTs] at hConf ⊢
    · by_cases hZ : res.exitCode = 0
      · simp [hZ]
      · simp [hZ] at hConf ⊢
        exact hConf
    · exact hConf
    · exact hConf
    · exact hConf

/-- Formal bridge soundness proof of `Internal.mkApiM (scriptedProcessApiId raw)` against stateful `Model.allowedCompressStep`, `Model.allowedDecompressStep`, and `Model.allowedIsToolAvailable`. -/
theorem proof_compress_internalApi_soundAgainstAllowedOutcome :
    AllPass (test_compress_internalApi_soundAgainstAllowedOutcome Internal.mkApiM) := by
  intro env st₀ codec copts dopts input rawC rawC0 rawD rawD0 rawV hC hC0 hD hD0 hV
  dsimp only [test_compress_internalApi_soundAgainstAllowedOutcome, bind, pure, assume, assert]
  exact ⟨internalApi_compressWith_sound env st₀ codec copts input rawC hC,
    internalApi_compressWith_sound env st₀ codec {} input rawC0 hC0,
    internalApi_decompressWith_sound env st₀ codec dopts input rawD hD,
    internalApi_decompressWith_sound env st₀ codec {} input rawD0 hD0,
    internalApi_isToolAvailable_sound env codec rawV hV, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_internalApi_soundAgainstAllowedOutcome`. -/
theorem reach_compress_internalApi_soundAgainstAllowedOutcome :
    CanReach (test_compress_internalApi_soundAgainstAllowedOutcome Internal.mkApiM) :=
  ⟨{ toolStatus := fun _ => .available }, Model.State.empty, .zstd, {}, {}, ByteArray.empty,
    .ok { exitCode := 0, stdout := Model.encodeStored .zstd ByteArray.empty, stderr := ByteArray.empty },
    .ok { exitCode := 0, stdout := Model.encodeStored .zstd ByteArray.empty, stderr := ByteArray.empty },
    .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
    .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
    .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty },
    by decide, by decide, by decide, by decide, by decide,
    proof_compress_internalApi_soundAgainstAllowedOutcome
      { toolStatus := fun _ => .available } Model.State.empty .zstd {} {} ByteArray.empty _ _ _ _ _
      (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- Proof of `test_compress_publicApi_matchesDefaultOps` anchoring all public `Compress.*` entry points to `Internal.mkApiM LeanSwe.Process.defaultApi`. -/
theorem proof_compress_publicApi_matchesDefaultOps :
    AllPass (test_compress_publicApi_matchesDefaultOps Internal.mkApiM
      Compress.defaultApi Compress.compress Compress.decompress
      Compress.compressWith Compress.decompressWith Compress.isToolAvailable
      LeanSwe.Process.defaultApi) := by
  intro codec copts dopts input
  dsimp only [test_compress_publicApi_matchesDefaultOps, bind, pure, assert]
  exact ⟨compress_defaultApi_eq, compress_compressWith_eq codec copts input,
    compress_decompressWith_eq codec dopts input, compress_compress_eq codec input,
    compress_decompress_eq codec input, compress_isToolAvailable_eq codec, trivial⟩

end LeanSwe.Compress.Proofs
