import LeanSwe.Compress.Types
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSwe.Compress.SpecTests

namespace LeanSwe.Compress.Proofs

open Core
open Core.NondetTest
open LeanSwe.Process
open LeanSwe.Compress

private theorem digitChar_ne_nul (k : Nat) (hk : k < 10) : Nat.digitChar k ≠ '\x00' := by
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
      k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem toDigitsCore_all_ne_nul (fuel n : Nat) (acc : List Char)
    (hacc : acc.all (fun c => c != '\x00') = true) :
    (Nat.toDigitsCore 10 fuel n acc).all (fun c => c != '\x00') = true := by
  induction fuel generalizing n acc with
  | zero => exact hacc
  | succ f ih =>
    unfold Nat.toDigitsCore
    dsimp only
    have hlt : n % 10 < 10 := Nat.mod_lt n (by decide)
    have hne : (Nat.digitChar (n % 10) != '\x00') = true :=
      bne_iff_ne.mpr (digitChar_ne_nul (n % 10) hlt)
    split
    · simp [List.all_cons, hne, hacc]
    · exact ih (n / 10) (Nat.digitChar (n % 10) :: acc) (by simp [List.all_cons, hne, hacc])

private theorem toString_nat_hasNul_false (n : Nat) :
    LeanSwe.Process.Internal.hasNul (toString n) = false := by
  have hall : (Nat.toDigits 10 n).all (fun c => c != '\x00') = true :=
    toDigitsCore_all_ne_nul (n + 1) n [] rfl
  have hmem : ∀ c ∈ (Nat.repr n).toList, c ≠ '\x00' := by
    intro c hc
    rw [Nat.repr, String.toList_ofList] at hc
    have hc' := List.all_eq_true.mp hall c hc
    exact bne_iff_ne.mp hc'
  change (toString n).toList.contains '\x00' = false
  cases h : (toString n).toList.contains '\x00'
  · rfl
  · exact absurd (hmem '\x00' (List.elem_iff.mp h)) (fun h0 => h0 rfl)

private theorem hasNul_append (a b : String)
    (ha : LeanSwe.Process.Internal.hasNul a = false)
    (hb : LeanSwe.Process.Internal.hasNul b = false) :
    LeanSwe.Process.Internal.hasNul (a ++ b) = false := by
  simp only [LeanSwe.Process.Internal.hasNul] at ha hb ⊢
  rw [String.toList_append]
  cases h : (a.toList ++ b.toList).contains '\x00'
  · rfl
  · rcases List.mem_append.mp (List.elem_iff.mp h) with h1 | h2
    · have : a.toList.contains '\x00' = true := List.elem_iff.mpr h1
      rw [this] at ha; cases ha
    · have : b.toList.contains '\x00' = true := List.elem_iff.mpr h2
      rw [this] at hb; cases hb

private theorem hasNul_dash_repr (n : Nat) :
    LeanSwe.Process.Internal.hasNul (toString "-" ++ Nat.repr n) = false :=
  hasNul_append (toString "-") (Nat.repr n) (by decide) (toString_nat_hasNul_false n)

private theorem hasNul_dashT_repr (n : Nat) :
    LeanSwe.Process.Internal.hasNul (toString "-T" ++ Nat.repr n) = false :=
  hasNul_append (toString "-T") (Nat.repr n) (by decide) (toString_nat_hasNul_false n)

private theorem mkCompressArgs_any_hasNul_false (codec : Codec) (opts : CompressOptions) :
    (Internal.mkCompressArgs codec opts).toList.any LeanSwe.Process.Internal.hasNul = false := by
  unfold Internal.mkCompressArgs
  cases codec <;> cases opts.level <;> cases opts.threads <;>
    simp [hasNul_dash_repr, hasNul_dashT_repr] <;>
    decide

private theorem validateRequest_mkCompressRequest (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) (ht : opts.timeoutMs ≠ 0) :
    LeanSwe.Process.Internal.validateRequest (Internal.mkCompressRequest codec opts input) =
      .ok (Internal.mkCompressRequest codec opts input) := by
  have hArgs : (Internal.mkCompressArgs codec opts).toList.any LeanSwe.Process.Internal.hasNul = false :=
    mkCompressArgs_any_hasNul_false codec opts
  have hProg : (Internal.codecProgram codec).isEmpty = false ∧
      LeanSwe.Process.Internal.hasNul (Internal.codecProgram codec) = false := by
    cases codec <;> exact ⟨rfl, rfl⟩
  have hEnv : Internal.codecSanitizedEnv.toList.any LeanSwe.Process.Internal.isInvalidEnvEntry = false := by
    decide
  have hDedup : (LeanSwe.Process.Internal.dedupEnvList Internal.codecSanitizedEnv.toList).toArray =
      Internal.codecSanitizedEnv := by
    decide
  have hTout : (some opts.timeoutMs == some 0) = false := by
    cases h : opts.timeoutMs with
    | zero => exact absurd h ht
    | succ _ => rfl
  simp only [LeanSwe.Process.Internal.validateRequest, Internal.mkCompressRequest,
    hProg.1, hProg.2, hArgs, hEnv, hDedup, hTout, Bool.false_eq_true, ↓reduceIte]

private theorem validateRequest_mkDecompressRequest (codec : Codec) (opts : DecompressOptions)
    (input : ByteArray) (ht : opts.timeoutMs ≠ 0) :
    LeanSwe.Process.Internal.validateRequest (Internal.mkDecompressRequest codec opts input) =
      .ok (Internal.mkDecompressRequest codec opts input) := by
  have hArgs : (Internal.mkDecompressArgs codec).toList.any LeanSwe.Process.Internal.hasNul = false := by
    cases codec <;> decide
  have hProg : (Internal.codecProgram codec).isEmpty = false ∧
      LeanSwe.Process.Internal.hasNul (Internal.codecProgram codec) = false := by
    cases codec <;> exact ⟨rfl, rfl⟩
  have hEnv : Internal.codecSanitizedEnv.toList.any LeanSwe.Process.Internal.isInvalidEnvEntry = false := by
    decide
  have hDedup : (LeanSwe.Process.Internal.dedupEnvList Internal.codecSanitizedEnv.toList).toArray =
      Internal.codecSanitizedEnv := by
    decide
  have hTout : (some opts.timeoutMs == some 0) = false := by
    cases h : opts.timeoutMs with
    | zero => exact absurd h ht
    | succ _ => rfl
  simp only [LeanSwe.Process.Internal.validateRequest, Internal.mkDecompressRequest,
    hProg.1, hProg.2, hArgs, hEnv, hDedup, hTout, Bool.false_eq_true, ↓reduceIte]

private theorem validateRequest_mkToolVersionRequest (codec : Codec) :
    LeanSwe.Process.Internal.validateRequest (Internal.mkToolVersionRequest codec) =
      .ok (Internal.mkToolVersionRequest codec) := by
  cases codec <;> rfl

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

private theorem codecSanitizedEnv_eq_expected :
    Internal.codecSanitizedEnv = codecSanitizedEnv := rfl

private theorem decodeStderr_eq_expected (bs : ByteArray) :
    Internal.decodeStderr bs = expectedStderr bs := rfl

private theorem classifyProcessError_spec (codec : Codec) (pe : ProcessError) :
    let e := Internal.classifyProcessError codec pe
    e.kind = expectedProcessErrorKind pe.kind ∧
    e.codec = some codec ∧
    e.exitCode = pe.exitCode ∧
    e.stderr = (pe.stderr.bind expectedStderr) ∧
    e.message ≠ "" ∧
    (pe.message = "" ∨ e.message = pe.message) := by
  unfold Internal.classifyProcessError
  have hk : (match pe.kind with
      | .notFound => CompressErrorKind.toolNotFound
      | .permissionDenied => .toolNotFound
      | .invalidInput => .invalidInput
      | .timedOut => .timedOut
      | .outputLimitExceeded => .outputLimitExceeded
      | .terminatedBySignal => .commandFailed
      | .nonZeroExit => .commandFailed
      | .ioError => .ioError) = expectedProcessErrorKind pe.kind := by
    cases pe.kind <;> rfl
  have hf : Internal.codecProgram codec ++ " process invocation failed" ≠ "" :=
    append_head_ne_empty _ _ (codecProgram_ne_empty codec)
  refine ⟨hk, rfl, rfl, ?_, nonEmptyMsg_ne_empty _ _ hf, ?_⟩
  · cases pe.stderr <;> rfl
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
    {S : Type} (raw : RawProcessOpsM (StateM S)) :
    AllPass (test_compress_compressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM raw) := by
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
    CanReach (test_compress_compressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM mockRawOps) := by
  refine ⟨{}, .gzip, { threads := some 2 }, ByteArray.empty, by decide, ?_⟩
  exact proof_compress_compressWith_invalidOptionsRejectWithoutSpawn mockRawOps
    {} .gzip { threads := some 2 } ByteArray.empty (by decide)

/-- Proof of `test_compress_decompressWith_invalidOptionsRejectWithoutSpawn` for `Internal.mkApiM`. -/
theorem proof_compress_decompressWith_invalidOptionsRejectWithoutSpawn
    {S : Type} (raw : RawProcessOpsM (StateM S)) :
    AllPass (test_compress_decompressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM raw) := by
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
    CanReach (test_compress_decompressWith_invalidOptionsRejectWithoutSpawn Internal.mkApiM mockRawOps) := by
  refine ⟨{}, .zstd, { timeoutMs := 0 }, ByteArray.empty, by decide, ?_⟩
  exact proof_compress_decompressWith_invalidOptionsRejectWithoutSpawn mockRawOps
    {} .zstd { timeoutMs := 0 } ByteArray.empty (by decide)

/-- Proof of `test_compress_compressWith_buildsExactExecRequest` for `Internal.mkApiM`. -/
theorem proof_compress_compressWith_buildsExactExecRequest :
    AllPass (test_compress_compressWith_buildsExactExecRequest Internal.mkApiM) := by
  intro codec opts input outBytes active₀ hValid
  rcases validateCompressOptions_true_implies_ok codec opts input hValid with ⟨hVal, hTout⟩
  have hReqVal := validateRequest_mkCompressRequest codec opts input hTout
  dsimp only [test_compress_compressWith_buildsExactExecRequest, Internal.mkApiM,
    Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
  rw [hVal]
  dsimp only
  rw [LeanSwe.Process.Internal.run, hReqVal]
  dsimp only [mockRawOps, Internal.classifyExitResult, StateT.run, bind, StateT.bind,
    pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set,
    StateT.get, StateT.set, Internal.mkCompressRequest]
  dsimp
  simp only [mkCompressArgs_eq_expected, codecProgram_eq_expected, codecSanitizedEnv_eq_expected]
  exact ⟨trivial, ⟨trivial, trivial, trivial⟩, trivial, trivial, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_compressWith_buildsExactExecRequest`. -/
theorem reach_compress_compressWith_buildsExactExecRequest :
    CanReach (test_compress_compressWith_buildsExactExecRequest Internal.mkApiM) := by
  refine ⟨.zstd, { level := some 3, threads := some 0 }, ByteArray.empty, ByteArray.empty, 0, by decide, ?_⟩
  exact proof_compress_compressWith_buildsExactExecRequest
    .zstd { level := some 3, threads := some 0 } ByteArray.empty ByteArray.empty 0 (by decide)

/-- Proof of `test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit` for `Internal.mkApiM`. -/
theorem proof_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit :
    AllPass (test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit Internal.mkApiM) := by
  intro codec opts input exitCode outBytes errBytes active₀ hValid
  rcases validateDecompressOptions_true_implies_ok codec opts input hValid with ⟨hVal, hTout⟩
  have hReqVal := validateRequest_mkDecompressRequest codec opts input hTout
  dsimp only [test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit, Internal.mkApiM,
    Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
  rw [hVal]
  dsimp only
  rw [LeanSwe.Process.Internal.run, hReqVal]
  dsimp only [mockRawOps, Internal.classifyExitResult, StateT.run, bind, StateT.bind,
    pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set,
    StateT.get, StateT.set, Internal.mkDecompressRequest]
  dsimp
  simp only [mkDecompressArgs_eq_expected, codecProgram_eq_expected, codecSanitizedEnv_eq_expected]
  by_cases heq : (exitCode == 0) = true
  · simp [heq]
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨trivial, trivial, trivial⟩, trivial, trivial,
      ⟨_, rfl, rfl, rfl, rfl, decodeStderr_eq_expected errBytes,
        classifyExitResult_nonzero_msg codec true { exitCode := exitCode, stdout := outBytes, stderr := errBytes }⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit`. -/
theorem reach_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit :
    CanReach (test_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit Internal.mkApiM) := by
  refine ⟨.gzip, {}, ByteArray.empty, 2, ByteArray.empty, "trailing".toUTF8, 0, by decide, ?_⟩
  exact proof_compress_decompressWith_buildsExactExecRequest_noEmptyShortCircuit
    .gzip {} ByteArray.empty 2 ByteArray.empty "trailing".toUTF8 0 (by decide)

/-- Proof of `test_compress_defaults_matchWithDefaultOptions` for `Internal.mkApiM`. -/
theorem proof_compress_defaults_matchWithDefaultOptions
    {S : Type} (raw : RawProcessOpsM (StateM S)) :
    AllPass (test_compress_defaults_matchWithDefaultOptions Internal.mkApiM raw) := by
  intro s₀ codec input
  dsimp only [test_compress_defaults_matchWithDefaultOptions, Internal.mkApiM,
    bind, pure, assert]
  exact ⟨rfl, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_defaults_matchWithDefaultOptions`. -/
theorem reach_compress_defaults_matchWithDefaultOptions :
    CanReach (test_compress_defaults_matchWithDefaultOptions Internal.mkApiM mockRawOps) :=
  ⟨{}, .zstd, ByteArray.empty, proof_compress_defaults_matchWithDefaultOptions mockRawOps {} .zstd ByteArray.empty⟩

/-- Proof of `test_compress_spawnErrors_mappedCorrectly` for `Internal.mkApiM`. -/
theorem proof_compress_spawnErrors_mappedCorrectly :
    AllPass (test_compress_spawnErrors_mappedCorrectly Internal.mkApiM) := by
  intro codec isDecompress pe input active₀
  let pe' := LeanSwe.Process.Internal.ensureNonEmptyMsg "process spawn failed" pe
  have hSpec := classifyProcessError_spec codec pe'
  have hPeSpec :
      (Internal.classifyProcessError codec pe').kind = expectedProcessErrorKind pe.kind ∧
      (Internal.classifyProcessError codec pe').codec = some codec ∧
      (Internal.classifyProcessError codec pe').exitCode = pe.exitCode ∧
      (Internal.classifyProcessError codec pe').stderr = (pe.stderr.bind expectedStderr) ∧
      (Internal.classifyProcessError codec pe').message ≠ "" ∧
      (pe.message = "" ∨ (Internal.classifyProcessError codec pe').message = pe.message) := by
    rcases hSpec with ⟨hk, hc, hex, herr, hne, hmsg⟩
    have hkind : pe'.kind = pe.kind := by
      unfold pe' LeanSwe.Process.Internal.ensureNonEmptyMsg
      split <;> rfl
    have hexc : pe'.exitCode = pe.exitCode := by
      unfold pe' LeanSwe.Process.Internal.ensureNonEmptyMsg
      split <;> rfl
    have hserr : pe'.stderr = pe.stderr := by
      unfold pe' LeanSwe.Process.Internal.ensureNonEmptyMsg
      split <;> rfl
    refine ⟨by simpa [hkind] using hk, hc, by simpa [hexc] using hex, by simpa [hserr] using herr, hne, ?_⟩
    by_cases hm : pe.message = ""
    · exact Or.inl hm
    · have hpe : pe'.message = pe.message := by
        simp [pe', LeanSwe.Process.Internal.ensureNonEmptyMsg, hm]
      rcases hmsg with h0 | h1
      · exact absurd (by simpa [hpe] using h0) hm
      · exact Or.inr (h1.trans hpe)
  cases isDecompress with
  | false =>
    have hVal : Internal.validateCompressOptions codec {} input = .ok () := by
      cases codec <;> rfl
    have hReqVal := validateRequest_mkCompressRequest codec {} input (by decide)
    dsimp only [test_compress_spawnErrors_mappedCorrectly, Internal.mkApiM,
      Internal.compressWith, bind, StateT.bind, pure, StateT.pure, assert]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hVal]
    dsimp only
    rw [LeanSwe.Process.Internal.run, hReqVal]
    dsimp only [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
    dsimp
    exact ⟨⟨rfl, rfl⟩, ⟨Internal.classifyProcessError codec pe', rfl, hPeSpec⟩, trivial⟩
  | true =>
    have hVal : Internal.validateDecompressOptions codec {} input = .ok () := by
      cases codec <;> rfl
    have hReqVal := validateRequest_mkDecompressRequest codec {} input (by decide)
    dsimp only [test_compress_spawnErrors_mappedCorrectly, Internal.mkApiM,
      Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
    simp only [↓reduceIte]
    rw [hVal]
    dsimp only
    rw [LeanSwe.Process.Internal.run, hReqVal]
    dsimp only [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
    dsimp
    exact ⟨⟨rfl, rfl⟩, ⟨Internal.classifyProcessError codec pe', rfl, hPeSpec⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_compress_spawnErrors_mappedCorrectly`. -/
theorem reach_compress_spawnErrors_mappedCorrectly :
    CanReach (test_compress_spawnErrors_mappedCorrectly Internal.mkApiM) :=
  ⟨.xz, false, { kind := .permissionDenied, program := some "xz", message := "eacces" },
    ByteArray.empty, 0,
    proof_compress_spawnErrors_mappedCorrectly .xz false
      { kind := .permissionDenied, program := some "xz", message := "eacces" } ByteArray.empty 0⟩

/-- Proof of `test_compress_awaitOutcomes_cleanedUpAndClassified` for `Internal.mkApiM`. -/
theorem proof_compress_awaitOutcomes_cleanedUpAndClassified :
    AllPass (test_compress_awaitOutcomes_cleanedUpAndClassified Internal.mkApiM) := by
  intro codec isDecompress input outBytes errBytes sig active₀ outcomeKind hKind
  have hCases : outcomeKind = 0 ∨ outcomeKind = 1 ∨ outcomeKind = 2 ∨ outcomeKind = 3 := by omega
  have hValC : Internal.validateCompressOptions codec {} input = .ok () := by
    cases codec <;> rfl
  have hValD : Internal.validateDecompressOptions codec {} input = .ok () := by
    cases codec <;> rfl
  have hReqC := validateRequest_mkCompressRequest codec {} input (by decide)
  have hReqD := validateRequest_mkDecompressRequest codec {} input (by decide)
  have hf : Internal.codecProgram codec ++ " process invocation failed" ≠ "" :=
    append_head_ne_empty _ _ (codecProgram_ne_empty codec)
  rcases hCases with rfl | rfl | rfl | rfl <;>
    cases isDecompress <;>
      · dsimp only [test_compress_awaitOutcomes_cleanedUpAndClassified, Internal.mkApiM,
          Internal.compressWith, Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
        simp only [Bool.false_eq_true, ↓reduceIte]
        try (rw [hValC]; dsimp only; rw [LeanSwe.Process.Internal.run, hReqC])
        try (rw [hValD]; dsimp only; rw [LeanSwe.Process.Internal.run, hReqD])
        dsimp only [mockRawOps, Internal.classifyProcessError, StateT.run, bind, StateT.bind,
          pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
        dsimp
        refine ⟨⟨rfl, rfl, rfl⟩, ?_, ⟨_, rfl, rfl, rfl, ?_⟩, trivial⟩
        · exact Nat.add_sub_cancel active₀ 1
        · dsimp only
          exact nonEmptyMsg_ne_empty _ _ hf

/-- Non-vacuity `CanReach` witness for `test_compress_awaitOutcomes_cleanedUpAndClassified`. -/
theorem reach_compress_awaitOutcomes_cleanedUpAndClassified :
    CanReach (test_compress_awaitOutcomes_cleanedUpAndClassified Internal.mkApiM) :=
  ⟨.zstd, true, ByteArray.empty, ByteArray.empty, ByteArray.empty, 9, 0, 0, by decide,
    proof_compress_awaitOutcomes_cleanedUpAndClassified
      .zstd true ByteArray.empty ByteArray.empty ByteArray.empty 9 0 0 (by decide)⟩

/-- Proof of `test_compress_exitCodes_compressVsDecompress_andStderr` for `Internal.mkApiM`. -/
theorem proof_compress_exitCodes_compressVsDecompress_andStderr :
    AllPass (test_compress_exitCodes_compressVsDecompress_andStderr Internal.mkApiM) := by
  intro codec exitCode input errBytes hnz
  have hbeq : (exitCode == 0) = false := beq_false_of_ne hnz
  have hValC : Internal.validateCompressOptions codec {} input = .ok () := by
    cases codec <;> rfl
  have hValD : Internal.validateDecompressOptions codec {} input = .ok () := by
    cases codec <;> rfl
  have hReqC := validateRequest_mkCompressRequest codec {} input (by decide)
  have hReqD := validateRequest_mkDecompressRequest codec {} input (by decide)
  dsimp only [test_compress_exitCodes_compressVsDecompress_andStderr, Internal.mkApiM,
    Internal.compressWith, Internal.decompressWith, bind, StateT.bind, pure, StateT.pure, assert]
  rw [hValC, hValD]
  dsimp only
  simp only [LeanSwe.Process.Internal.run, hReqC, hReqD]
  dsimp only [mockRawOps, Internal.classifyExitResult, StateT.run, bind, StateT.bind,
    pure, StateT.pure, get, set, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
  dsimp
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
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

/-- Proof of `test_compress_isToolAvailable_checksVersionAndCleansUp` for `Internal.mkApiM`. -/
theorem proof_compress_isToolAvailable_checksVersionAndCleansUp :
    AllPass (test_compress_isToolAvailable_checksVersionAndCleansUp Internal.mkApiM) := by
  intro codec spawnOk exitCode active₀
  have hReqVal := validateRequest_mkToolVersionRequest codec
  dsimp only [test_compress_isToolAvailable_checksVersionAndCleansUp, Internal.mkApiM,
    Internal.isToolAvailable, bind, StateT.bind, pure, StateT.pure, assert]
  rw [LeanSwe.Process.Internal.run, hReqVal]
  cases spawnOk with
  | false =>
    dsimp only [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set,
      Internal.mkToolVersionRequest]
    dsimp
    simp only [codecProgram_eq_expected, codecSanitizedEnv_eq_expected]
    exact ⟨⟨rfl, rfl⟩, rfl, rfl, trivial⟩
  | true =>
    dsimp only [mockRawOps, StateT.run, bind, StateT.bind, pure, StateT.pure,
      get, set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set,
      Internal.mkToolVersionRequest]
    dsimp
    simp only [codecProgram_eq_expected, codecSanitizedEnv_eq_expected]
    refine ⟨⟨rfl, ?_⟩, rfl, rfl, rfl, trivial⟩
    exact Nat.add_sub_cancel active₀ 1

/-- Non-vacuity `CanReach` witness for `test_compress_isToolAvailable_checksVersionAndCleansUp`. -/
theorem reach_compress_isToolAvailable_checksVersionAndCleansUp :
    CanReach (test_compress_isToolAvailable_checksVersionAndCleansUp Internal.mkApiM) :=
  ⟨.zstd, true, 0, 0, proof_compress_isToolAvailable_checksVersionAndCleansUp .zstd true 0 0⟩

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

private theorem catchProc_never_throws {α : Type} (prog? : Option String) (act : IO α)
    (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Raw.Internal.catchProc prog? act w = EST.Out.ok r w' := by
  unfold LeanSwe.Process.Raw.Internal.catchProc
  rw [io_bind_eq]
  cases h : act w with
  | ok a w' =>
    refine ⟨Except.ok a, w', ?_⟩
    rw [io_tryCatch_eq, io_bind_eq, h]
    rfl
  | error err w' =>
    refine ⟨Except.error (LeanSwe.Process.Raw.Internal.mapIoError prog? err), w', ?_⟩
    rw [io_tryCatch_eq, io_bind_eq, h]
    rfl

private theorem defaultOps_spawn_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Raw.defaultOps.spawn req w = EST.Out.ok r w' := by
  unfold LeanSwe.Process.Raw.defaultOps LeanSwe.Process.Raw.Internal.mkRawOps
  dsimp only
  split
  · rw [io_pure_eq]; exact ⟨_, _, rfl⟩
  · exact catchProc_never_throws _ _ w

private theorem defaultOps_awaitOutput_never_throws (h : LeanSwe.Process.Raw.ProcessHandle)
    (stdin : ByteArray) (timeoutMs maxOut : Option Nat) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Raw.defaultOps.awaitOutput h stdin timeoutMs maxOut w = EST.Out.ok r w' := by
  unfold LeanSwe.Process.Raw.defaultOps LeanSwe.Process.Raw.Internal.mkRawOps
  dsimp only
  exact catchProc_never_throws _ _ w

private theorem defaultOps_killProcessGroup_never_throws (h : LeanSwe.Process.Raw.ProcessHandle)
    (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Raw.defaultOps.killProcessGroup h w = EST.Out.ok r w' := by
  unfold LeanSwe.Process.Raw.defaultOps LeanSwe.Process.Raw.Internal.mkRawOps
  dsimp only
  exact catchProc_never_throws _ _ w

private theorem defaultOps_reap_never_throws (h : LeanSwe.Process.Raw.ProcessHandle)
    (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Raw.defaultOps.reap h w = EST.Out.ok r w' := by
  unfold LeanSwe.Process.Raw.defaultOps LeanSwe.Process.Raw.Internal.mkRawOps
  dsimp only
  exact catchProc_never_throws _ _ w

private theorem processRun_defaultOps_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Internal.run LeanSwe.Process.Raw.defaultOps req w = EST.Out.ok r w' := by
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
    Internal.compressWith
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
      cases pe.kind <;> simp
    | ok res =>
      dsimp only
      rw [io_pure_eq]
      dsimp only [Internal.classifyExitResult]
      cases hZero : (res.exitCode == 0)
      · simp
      · simp

/-- Formal impossibility proof for `LeanSwe.Compress.compress` never returning `.corruptData`. -/
theorem compress_compress_never_corruptData (codec : Codec) (input : ByteArray)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CompressError.kind .corruptData
      (Compress.compress codec input) w :=
  compress_compressWith_never_corruptData codec {} input w

end LeanSwe.Compress.Proofs
