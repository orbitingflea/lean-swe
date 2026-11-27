import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model
import LeanSweProofs.Compress.SpecTests
import LeanSweProofs.Compress.Proofs.SharedHelpers
import LeanSweProofs.Compress.Proofs.StoredBoundsProofs

/-!
Model framing, bounds, and `Model.modelApi` soundness proofs (`AllPass` / `CanReach`) for `LeanSwe.Compress`.
-/

namespace LeanSwe.Compress.Proofs

open Core
open Core.NondetTest
open LeanSwe.Compress

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
    | some _ => simp
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
    | some _ => simp
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
        | some _ => simp [h] at hFresh; rw [beq_iff_eq]; exact hFresh
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

end LeanSwe.Compress.Proofs
