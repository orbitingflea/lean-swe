import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSwe.Compress.Impl
import LeanSweProofs.Compress.SpecTests
import LeanSweProofs.Compress.Proofs.SharedHelpers

/-!
Request-formation, option-rejection, and error-mapping `AllPass` / `CanReach` proofs for `LeanSwe.Compress`.
-/

namespace LeanSwe.Compress.Proofs

open Core
open Core.NondetTest
open LeanSwe.Process
open LeanSwe.Compress

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

end LeanSwe.Compress.Proofs
