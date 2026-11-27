import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSwe.Compress.Impl
import LeanSweProofs.Compress.SpecTests

/-!
Shared option-validation, error-normalization, and state equality lemmas for `LeanSwe.Compress.Proofs`.
-/

namespace LeanSwe.Compress.Proofs

open LeanSwe.Process
open LeanSwe.Compress

/-- Invalid `CompressOptions` or oversized `input` produces a normalized `.invalidInput` `CompressError`. -/
theorem validateCompressOptions_false_implies_error (codec : Codec) (opts : CompressOptions)
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

/-- Valid `CompressOptions` and `input` pass `Internal.validateCompressOptions` with `opts.timeoutMs ≠ 0`. -/
theorem validateCompressOptions_true_implies_ok (codec : Codec) (opts : CompressOptions)
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

/-- Invalid `DecompressOptions` or oversized `input` produces a normalized `.invalidInput` `CompressError`. -/
theorem validateDecompressOptions_false_implies_error (codec : Codec) (opts : DecompressOptions)
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

/-- Valid `DecompressOptions` and `input` pass `Internal.validateDecompressOptions` with `opts.timeoutMs ≠ 0`. -/
theorem validateDecompressOptions_true_implies_ok (codec : Codec) (opts : DecompressOptions)
    (input : ByteArray) (h : isValidDecompressInput opts input = true) :
    Internal.validateDecompressOptions codec opts input = .ok () ∧ opts.timeoutMs ≠ 0 := by
  simp only [isValidDecompressInput, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨ht, ho⟩, hIn⟩
  have htout : (opts.timeoutMs == 0) = false := beq_false_of_ne (by omega)
  have hout : (opts.maxOutputBytes == 0) = false := beq_false_of_ne (by omega)
  refine ⟨?_, by omega⟩
  unfold Internal.validateDecompressOptions
  cases hmax : opts.maxInputBytes <;> simp_all

/-- `Internal.nonEmptyMsg` produces a non-empty string whenever `fallback` is non-empty. -/
theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

/-- `Internal.nonEmptyMsg` returns `msg` unchanged when `msg` is non-empty. -/
theorem nonEmptyMsg_eq_of_ne_empty (fallback msg : String) (hm : msg ≠ "") :
    Internal.nonEmptyMsg fallback msg = msg := by
  unfold Internal.nonEmptyMsg
  have hem : msg.isEmpty = false := by
    simp [String.isEmpty, hm]
  simp [hem]

/-- Appending any suffix to a non-empty prefix yields a non-empty string. -/
theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

/-- `Internal.codecProgram` is non-empty for every `Codec`. -/
theorem codecProgram_ne_empty (codec : Codec) :
    Internal.codecProgram codec ≠ "" := by
  cases codec <;> decide

/-- `Internal.mkCompressArgs` agrees with `expectedCompressArgs`. -/
theorem mkCompressArgs_eq_expected (codec : Codec) (opts : CompressOptions) :
    Internal.mkCompressArgs codec opts = expectedCompressArgs codec opts := by
  cases codec <;> cases opts.level <;> cases opts.threads <;> rfl

/-- `Internal.mkDecompressArgs` agrees with `expectedDecompressArgs`. -/
theorem mkDecompressArgs_eq_expected (codec : Codec) :
    Internal.mkDecompressArgs codec = expectedDecompressArgs codec := by
  cases codec <;> rfl

/-- `Internal.codecProgram` agrees with `codecProgram`. -/
theorem codecProgram_eq_expected (codec : Codec) :
    Internal.codecProgram codec = codecProgram codec := by
  cases codec <;> rfl

/-- `Internal.codecSanitizedEnv` agrees with `expectedSanitizedEnv`. -/
theorem codecSanitizedEnv_eq_expected (codec : Codec) :
    Internal.codecSanitizedEnv = expectedSanitizedEnv codec := rfl

/-- `Internal.stderrPipeSlack` agrees with `expectedStderrPipeSlack`. -/
theorem stderrPipeSlack_eq_expected :
    Internal.stderrPipeSlack = expectedStderrPipeSlack := rfl

/-- `Internal.decodeStderr` agrees with `expectedStderr`. -/
theorem decodeStderr_eq_expected (bs : ByteArray) :
    Internal.decodeStderr bs = expectedStderr bs := rfl

/-- `isResourceExhaustedProcessError` is `false` whenever `pe.kind ≠ .invalidInput`. -/
theorem isResourceExhausted_of_kind {pe : ProcessError} (h : pe.kind ≠ .invalidInput) :
    isResourceExhaustedProcessError pe = false := by
  unfold isResourceExhaustedProcessError
  cases hpk : pe.kind with
  | invalidInput => exact absurd hpk h
  | notFound | permissionDenied | timedOut | outputLimitExceeded | terminatedBySignal | nonZeroExit | ioError => rfl

/-- Full field characterization of `Internal.classifyProcessError`. -/
theorem classifyProcessError_spec (codec : Codec) (pe : ProcessError) :
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

/-- Non-zero exit message produced by `Internal.classifyExitResult` is always non-empty. -/
theorem classifyExitResult_nonzero_msg (codec : Codec) (isDecompress : Bool)
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

/-- Well-formedness helper for `CompressError` values without `exitCode` or `stderr`. -/
theorem isWellFormedCompressError_simple (codec : Codec) (kind : CompressErrorKind)
    (msg : String) (hne : msg.isEmpty = false)
    (hk : kind = .invalidInput ∨ kind = .toolNotFound ∨ kind = .ioError ∨
      kind = .outputLimitExceeded ∨ kind = .corruptData) :
    Model.isWellFormedCompressError codec { kind := kind, codec := some codec, message := msg } = true := by
  unfold Model.isWellFormedCompressError
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    cases codec <;> simp [hne] <;> decide

/-- Reflexivity of `BEq` on `CompressErrorKind`. -/
theorem kind_beq_self (k : CompressErrorKind) : (k == k) = true := by
  cases k <;> rfl

/-- Reflexivity of `BEq` on `Model.State`. -/
theorem state_beq_self (st : Model.State) : (st == st) = true := by
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

/-- `Internal.decodeStderr` never returns `some ""`. -/
theorem decodeStderr_isEmpty_false (bs : ByteArray) (s : String)
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

/-- `s.isEmpty = false` whenever `s ≠ ""`. -/
theorem string_ne_empty_iff_isEmpty_false (s : String) (hne : s ≠ "") :
    s.isEmpty = false := by
  cases hs : s.isEmpty with
  | false => rfl
  | true =>
    exfalso
    apply hne
    simp [String.isEmpty] at hs
    exact hs

/-- Propositional equality from `BEq` on `Model.ToolEnvStatus`. -/
theorem toolStatus_eq_of_beq {a b : Model.ToolEnvStatus} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- `Internal.classifyProcessError` always produces a well-formed `CompressError`. -/
theorem classifyProcessError_wellFormed (codec : Codec) (pe : ProcessError) :
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
      | .corruptData => (match e.exitCode with | some c => c != 0 | none => true)
      | .commandFailed => (match e.exitCode with | some c => c != 0 | none => true)) = true := by
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
    | notFound | permissionDenied | timedOut | outputLimitExceeded | ioError =>
      have hResF : isResourceExhaustedProcessError pe = false := isResourceExhausted_of_kind (by rw [hpk]; intro hc; cases hc)
      simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hResF]
    | invalidInput =>
      by_cases hRes : isResourceExhaustedProcessError pe <;>
        simp [expectedProcessErrorKindFor, expectedProcessErrorKind, expectedProcessErrorExitCode, hpk, hRes]
    | terminatedBySignal | nonZeroExit =>
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

/-- Every `.error` returned by `Internal.classifyExitResult` satisfies `Model.isWellFormedCompressError`. -/
theorem classifyExitResult_wellFormed_of_err (codec : Codec) (isDecompress : Bool)
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
      | .toolNotFound | .invalidInput | .outputLimitExceeded | .timedOut | .ioError => false
      | .corruptData | .commandFailed => res.exitCode != 0)) = true
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

/-- Well-formedness of the `.corruptData` error emitted when `.gzip` header check fails on abnormal exit. -/
theorem framingErr_wellFormed (codec : Codec) (err? : Option ByteArray) :
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

/-- Convert `(codec != .gzip || Model.hasGzipHeader input) = true` into `(codec == .gzip && !Internal.hasGzipHeader input) = false`. -/
theorem not_gzip_and_not_header_of_ok {codec : Codec} {input : ByteArray}
    (h : (codec != .gzip || Model.hasGzipHeader input) = true) :
    (codec == .gzip && !Internal.hasGzipHeader input) = false := by
  cases codec with
  | zstd | xz => rfl
  | gzip =>
    change (false || Model.hasGzipHeader input) = true at h
    rw [Bool.false_or] at h
    change (true && !Model.hasGzipHeader input) = false
    rw [Bool.true_and, Bool.not_eq_false']; exact h

/-- Convert `(codec == .gzip && !Internal.hasGzipHeader input) = false` into `(codec != .gzip || Model.hasGzipHeader input) = true`. -/
theorem gzip_or_header_of_not_err {codec : Codec} {input : ByteArray}
    (h : (codec == .gzip && !Internal.hasGzipHeader input) = false) :
    (codec != .gzip || Model.hasGzipHeader input) = true := by
  cases codec with
  | zstd | xz => rfl
  | gzip =>
    change (true && !Model.hasGzipHeader input) = false at h
    rw [Bool.true_and, Bool.not_eq_false'] at h
    change (false || Model.hasGzipHeader input) = true
    rw [Bool.false_or]; exact h

end LeanSwe.Compress.Proofs
