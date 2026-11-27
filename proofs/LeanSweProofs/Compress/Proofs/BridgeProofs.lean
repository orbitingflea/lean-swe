import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSweProofs.Compress.SpecTests
import LeanSweProofs.Compress.Proofs.SharedHelpers
import LeanSweProofs.Compress.Proofs.StoredBoundsProofs

/-!
Bridge soundness (`Internal.mkApiM (scriptedProcessApiId _)`) and public `Interface` wiring proofs for `LeanSwe.Compress`.
-/

namespace LeanSwe.Compress.Proofs

open Core
open Core.NondetTest
open LeanSwe.Process
open LeanSwe.Compress

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

/-- Bridge soundness for `compressWith` against `Model.allowedCompressStep` given `rawCompressCallConforms`. -/
theorem internalApi_compressWith_sound (env : Model.CompressEnv) (st₀ : Model.State)
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

/-- Bridge soundness for `decompressWith` against `Model.allowedDecompressStep` given `rawDecompressCallConforms`. -/
theorem internalApi_decompressWith_sound (env : Model.CompressEnv) (st₀ : Model.State)
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
        | some _ =>
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
        | some _ =>
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
      | some _ =>
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

/-- Bridge soundness for `isToolAvailable` against `Model.allowedIsToolAvailable` given `rawVersionCallConforms`. -/
theorem internalApi_isToolAvailable_sound (env : Model.CompressEnv) (codec : Codec)
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
