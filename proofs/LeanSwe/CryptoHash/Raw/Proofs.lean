import Core.Assumptions
import Core.Obeys
import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Model
import LeanSwe.CryptoHash.Raw.Model.Refines
import LeanSwe.CryptoHash.Raw.Impl
import LeanSwe.CryptoHash.Raw.Interface
import LeanSwe.CryptoHash.Raw.SpecTests
import LeanSwe.CryptoHash.Raw.Proofs.Sha256Vectors
import LeanSwe.CryptoHash.Raw.Proofs.Sha512Vectors
import LeanSwe.CryptoHash.Raw.Proofs.HmacVectors
import LeanSwe.CryptoHash.Raw.Proofs.HmacTc1
import LeanSwe.CryptoHash.Raw.Proofs.HmacTc2
import LeanSwe.CryptoHash.Raw.Proofs.HmacTc6

namespace LeanSwe.CryptoHash.Raw.Proofs

open Core (AllPass CanReach)
open LeanSwe.CryptoHash.Raw

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hfb : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hfb
  · rename_i hne
    intro hemp
    apply hne
    simp [hemp]

/-- `defaultOps.mapRawError` satisfies `test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage`. -/
theorem raw_mapRawError_mapsKindsAndNonEmptyMessage :
    AllPass (test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage defaultOps) := by
  intro raw
  cases raw with
  | invalidArgument detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid cryptohash argument" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | invalidHexInput detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid hex input" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | lengthError expected got detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty s!"length mismatch: expected {expected} bytes, got {got}" detail (by
        intro h
        have hlen := congrArg String.length h
        simp [String.length] at hlen)
    · exact ⟨rfl, rfl⟩
    · trivial
  | opensslError code detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "openssl crypto error" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | userError detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "cryptohash error" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial

private theorem digestBytesModel_size (alg : HashAlg) (msg : ByteArray) :
    (Model.digestBytesModel alg msg).size = digestLen alg := by
  cases alg <;> rfl

private theorem hmacSha256Bytes_size (key msg : ByteArray) :
    (Model.hmacSha256Bytes key msg).size = 32 := rfl

/-- `Model.modelStateRawOps` satisfies `test_cryptohashraw_digestRaw_returnsExpectedLengthOrError`. -/
theorem raw_digestRaw_returnsExpectedLengthOrError :
    AllPass (test_cryptohashraw_digestRaw_returnsExpectedLengthOrError (Model.modelStateRawOps (S := Unit))) := by
  intro _ alg msg
  dsimp [test_cryptohashraw_digestRaw_returnsExpectedLengthOrError, Model.modelStateRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  exact ⟨digestBytesModel_size alg msg, trivial⟩

/-- `Model.modelStateRawOps` satisfies `test_cryptohashraw_hmacSha256Raw_returns32BytesOrError`. -/
theorem raw_hmacSha256Raw_returns32BytesOrError :
    AllPass (test_cryptohashraw_hmacSha256Raw_returns32BytesOrError (Model.modelStateRawOps (S := Unit))) := by
  intro _ key msg
  dsimp [test_cryptohashraw_hmacSha256Raw_returns32BytesOrError, Model.modelStateRawOps,
    StateT.run, pure, StateT.pure, Core.NondetTest.assert, Bind.bind]
  exact ⟨hmacSha256Bytes_size key msg, trivial⟩

/-- `Model.modelStateRawOps` satisfies `test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch`. -/
theorem raw_ctEqualRaw_unequalLengths_returnsLengthMismatch :
    AllPass (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch (Model.modelStateRawOps (S := Unit))) := by
  intro _ a b hne
  dsimp [test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch, Model.modelStateRawOps,
    Model.ctEqualRawModel, StateT.run, Core.NondetTest.assert, Bind.bind,
    Core.NondetTest.assume]
  have hneB : (a.size != b.size) = true := bne_iff_ne.mpr hne
  simp only [hneB, ↓reduceIte, Pure.pure, Model.mapRawErrorModel]
  refine ⟨⟨trivial, ?_⟩, trivial⟩
  unfold Model.nonEmptyMsgModel
  split
  · intro h
    have hlen := congrArg String.length h
    simp [String.length] at hlen
  · rename_i hne_s
    intro hemp
    have hlen := congrArg String.length hemp
    simp [String.length] at hlen

/-- Non-vacuity witness for `test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch`. -/
theorem raw_ctEqualRaw_unequalLengths_canReach :
    CanReach (test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch (Model.modelStateRawOps (S := Unit))) := by
  refine ⟨(), ByteArray.empty, ByteArray.mk #[1], by decide, ?_⟩
  dsimp [test_cryptohashraw_ctEqualRaw_unequalLengths_returnsLengthMismatch, Model.modelStateRawOps,
    Model.ctEqualRawModel, StateT.run, Core.NondetTest.assert, Bind.bind]
  simp only [ByteArray.size, bne, Pure.pure, Model.mapRawErrorModel, Model.nonEmptyMsgModel]
  exact ⟨⟨rfl, by decide⟩, trivial⟩

/-- `Model.modelStateRawOps` satisfies `test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError`. -/
theorem raw_ctEqualRaw_equalLengths_returnsBoolOrError :
    AllPass (test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError (Model.modelStateRawOps (S := Unit))) := by
  intro _ a b heq
  dsimp [test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError, Model.modelStateRawOps,
    Model.ctEqualRawModel, StateT.run, Core.NondetTest.assert, Bind.bind]
  have hfalse : (a.size != b.size) = false := by simp [heq]
  simp [hfalse, Pure.pure]

/-- Non-vacuity witness for `test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError`. -/
theorem raw_ctEqualRaw_equalLengths_canReach :
    CanReach (test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError (Model.modelStateRawOps (S := Unit))) := by
  refine ⟨(), ByteArray.empty, ByteArray.empty, rfl, ?_⟩
  dsimp [test_cryptohashraw_ctEqualRaw_equalLengths_returnsBoolOrError, Model.modelStateRawOps,
    Model.ctEqualRawModel, StateT.run, Core.NondetTest.assert, Bind.bind]
  simp [Pure.pure]

private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = .ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem io_bind_baseIO {α β : Type} (act : BaseIO α) (k : α → IO β) (w : Void IO.RealWorld) :
    ((liftM act : IO α) >>= k) w = k (act w).val (act w).state := by
  rcases baseIO_liftM_never_throws act w with ⟨v, w', hv⟩
  have hst : act w = .mk v w' := by
    simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO] at hv
    cases h : act w with
    | mk a s =>
      rw [h] at hv
      have ha : a = v := by injection hv
      have hs : s = w' := by injection hv
      subst ha hs
      rfl
  rw [hst]
  have hbind : ((liftM act : IO α) >>= k) w =
      match (liftM act : IO α) w with
      | EST.Out.ok a s => k a s
      | EST.Out.error e s => EST.Out.error e s := rfl
  rw [hbind, hv]

private theorem decodeShimError_ne_invalidHex (status : UInt32) (code : UInt64) (detail : String) :
    (Internal.decodeShimError status code detail).kind ≠ .invalidHex := by
  unfold Internal.decodeShimError Internal.decodeOpenSslError Internal.mapRawError
  split
  · simp
  · split <;> simp

/-- Exact outcome characterization of `Raw.defaultOps.digestRaw`: either `.ok bs` of length `digestLen alg` or `.error` whose kind is never `.invalidHex`. -/
theorem defaultOps_digestRaw_outcome (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (defaultOps.digestRaw alg data) w = .ok (.ok bs) w' ∧ bs.size = digestLen alg) ∨
    (∃ e w', (defaultOps.digestRaw alg data) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != digestLen alg) = true
    · simp only [hlen, ↓reduceIte]
      rw [io_pure_eq]
      exact Or.inr ⟨_, _, rfl, by simp [Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [io_pure_eq]
      have heq : bs.size = digestLen alg := by
        cases hsz : (bs.size == digestLen alg)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

/-- Exact outcome characterization of `Raw.defaultOps.hmacSha256Raw`: either `.ok bs` of length `32` or `.error` whose kind is never `.invalidHex`. -/
theorem defaultOps_hmacSha256Raw_outcome (key msg : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (defaultOps.hmacSha256Raw key msg) w = .ok (.ok bs) w' ∧ bs.size = 32) ∨
    (∃ e w', (defaultOps.hmacSha256Raw key msg) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != 32) = true
    · simp only [hlen, ↓reduceIte]
      rw [io_pure_eq]
      exact Or.inr ⟨_, _, rfl, by simp [Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [io_pure_eq]
      have heq : bs.size = 32 := by
        cases hsz : (bs.size == 32)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

/-- Exact outcome characterization of `Raw.defaultOps.ctEqualRaw`: `.error` with `.lengthMismatch` when sizes differ, else `.ok eq`. -/
theorem defaultOps_ctEqualRaw_outcome (a b : ByteArray) (w : Void IO.RealWorld) :
    (a.size ≠ b.size ∧ ∃ e w', (defaultOps.ctEqualRaw a b) w = .ok (.error e) w' ∧ e.kind = .lengthMismatch) ∨
    (a.size = b.size ∧ ∃ eq w', (defaultOps.ctEqualRaw a b) w = .ok (.ok eq) w') := by
  dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM]
  by_cases hne : (a.size != b.size) = true
  · simp only [hne, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inl ⟨bne_iff_ne.mp hne, _, _, rfl, rfl⟩
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_baseIO]
    rw [io_pure_eq]
    have heq : a.size = b.size := by
      cases hsz : (a.size == b.size)
      · simp [bne, hsz] at hne
      · exact beq_iff_eq.mp hsz
    exact Or.inr ⟨heq, _, _, rfl⟩

private theorem ctEqualRaw_never (k : CryptoHashErrorKind) (hk : k ≠ .lengthMismatch)
    (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind k (ctEqualRaw a b) w := by
  unfold Core.NeverErrorKindIO ctEqualRaw
  rcases defaultOps_ctEqualRaw_outcome a b w with ⟨_, e, w', herr, hek⟩ | ⟨_, eq, w', hok⟩
  · rw [herr]; simp [hek, hk.symm]
  · rw [hok]; trivial

/-- `Raw.digestRaw` never returns `.invalidHex`. -/
theorem raw_digestRaw_never_invalidHex (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (digestRaw alg data) w := by
  unfold Core.NeverErrorKindIO digestRaw
  rcases defaultOps_digestRaw_outcome alg data w with ⟨bs, w', hok, _⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]; trivial
  · rw [herr]; exact hek

/-- `Raw.hmacSha256Raw` never returns `.invalidHex`. -/
theorem raw_hmacSha256Raw_never_invalidHex (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (hmacSha256Raw key msg) w := by
  unfold Core.NeverErrorKindIO hmacSha256Raw
  rcases defaultOps_hmacSha256Raw_outcome key msg w with ⟨bs, w', hok, _⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]; trivial
  · rw [herr]; exact hek

/-- `Raw.ctEqualRaw` never returns `.invalidInput`. -/
theorem raw_ctEqualRaw_never_invalidInput (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidInput (ctEqualRaw a b) w :=
  ctEqualRaw_never .invalidInput (by decide) a b w

/-- `Raw.ctEqualRaw` never returns `.invalidHex`. -/
theorem raw_ctEqualRaw_never_invalidHex (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (ctEqualRaw a b) w :=
  ctEqualRaw_never .invalidHex (by decide) a b w

/-- `Raw.ctEqualRaw` never returns `.cryptoError`. -/
theorem raw_ctEqualRaw_never_cryptoError (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .cryptoError (ctEqualRaw a b) w :=
  ctEqualRaw_never .cryptoError (by decide) a b w

/-- `Model.modelRawOps` satisfies `test_cryptohashraw_modelDigestsValidLengthsAndVectors`. -/
theorem raw_modelDigestsValidLengthsAndVectors :
    AllPass (test_cryptohashraw_modelDigestsValidLengthsAndVectors Model.modelRawOps) := by
  intro alg key msg
  dsimp only [test_cryptohashraw_modelDigestsValidLengthsAndVectors, Model.modelRawOps,
    Core.NondetTest.assert, Bind.bind, Pure.pure]
  exact ⟨rfl, digestBytesModel_size alg msg, rfl, hmacSha256Bytes_size key msg,
    sha256_empty_vec, sha256_abc_vec, sha512_empty_vec, sha512_abc_vec,
    hmac_tc1_vec, hmac_tc2_vec, hmac_tc6_vec, hmac_empty_vec, trivial⟩

private theorem internal_mapRawError_eq_model (err : CryptoHashRawError) :
    Internal.mapRawError err = Model.mapRawErrorModel err := by
  cases err <;> rfl

private theorem mapRawError_obeys :
    Core.ObeysPureEq mapRawError Model.mapRawErrorModel := by
  intro err
  exact internal_mapRawError_eq_model err

private theorem stateM_map_run {W α β : Type} (f : α → β) (m : StateM W α) (w : W) :
    (f <$> m).run w = (f (m.run w).1, (m.run w).2) := rfl

private theorem stateM_bind_run {W α β : Type} (m : StateM W α) (k : α → StateM W β) (w : W) :
    (m >>= k).run w = (k (m.run w).1).run (m.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

private theorem mkRawOpsM_obeys :
    Core.ObeysStepFrom id Model.rawStepWf
      Model.execFfiStep Model.allowedFfiStep Model.rawStepWf
      Internal.mkRawOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj ffi hFfi w req _
  cases req with
  | digestRaw alg data =>
    cases alg with
    | sha256 =>
      have hStep := hFfi w (.digestRaw 0 data) rfl
      have hOut : ((ffi.digestRaw 0 data).run w).1 = (0, 0, "", Model.sha256Bytes data) := hStep.2
      have hSz : (Model.sha256Bytes data).size = 32 := digestBytesModel_size .sha256 data
      simp only [Model.execPkgStep, Internal.mkRawOpsM, Model.allowedPkgStep,
        Model.digestBytesModel, Function.comp, id,
        stateM_map_run, stateM_bind_run, hOut, digestLen, hSz,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
      trivial
    | sha512 =>
      have hStep := hFfi w (.digestRaw 1 data) rfl
      have hOut : ((ffi.digestRaw 1 data).run w).1 = (0, 0, "", Model.sha512Bytes data) := hStep.2
      have hSz : (Model.sha512Bytes data).size = 64 := digestBytesModel_size .sha512 data
      simp only [Model.execPkgStep, Internal.mkRawOpsM, Model.allowedPkgStep,
        Model.digestBytesModel, Function.comp, id,
        stateM_map_run, stateM_bind_run, hOut, digestLen, hSz,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
      trivial
  | hmacSha256Raw key msg =>
    have hStep := hFfi w (.hmacSha256Raw key msg) rfl
    have hOut : ((ffi.hmacSha256Raw key msg).run w).1 = (0, 0, "", Model.hmacSha256Bytes key msg) :=
      hStep.2
    have hSz : (Model.hmacSha256Bytes key msg).size = 32 := hmacSha256Bytes_size key msg
    simp only [Model.execPkgStep, Internal.mkRawOpsM, Model.allowedPkgStep, Function.comp, id,
      stateM_map_run, stateM_bind_run, hOut, hSz,
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
    trivial
  | ctEqualRaw a b =>
    by_cases hne : (a.size != b.size) = true
    · simp only [Model.execPkgStep, Internal.mkRawOpsM, Model.allowedPkgStep,
        Model.ctEqualRawModel, Function.comp, id,
        hne, ↓reduceIte, stateM_map_run, stateM_pure_run, internal_mapRawError_eq_model]
      trivial
    · have hFalse : (a.size != b.size) = false := Bool.eq_false_iff.mpr hne
      have hStep := hFfi w (.ctEqualRaw a b) rfl
      have hOut : ((ffi.ctEqualRaw a b).run w).1 = (a == b) := hStep.2
      simp only [Model.execPkgStep, Internal.mkRawOpsM, Model.allowedPkgStep,
        Model.ctEqualRawModel, Function.comp, id,
        hFalse, Bool.false_eq_true, ↓reduceIte,
        stateM_map_run, stateM_bind_run, hOut, stateM_pure_run]
      trivial

/-- Canonical `Core.Obeys*` specification theorem for `LeanSwe.CryptoHash.Raw`. -/
theorem obeys_model :
    Core.ObeysPureEq mapRawError Model.mapRawErrorModel ∧
    Core.ObeysStepFrom id Model.rawStepWf
      Model.execFfiStep Model.allowedFfiStep Model.rawStepWf
      Internal.mkRawOpsM Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_obeys, mkRawOpsM_obeys⟩

private theorem modelStateFfiOps_obeys :
    Core.ObeysStepId Model.rawStepWf
      (Model.execFfiStep Model.modelStateFfiOps) Model.allowedFfiStep := by
  intro s req _
  cases req <;> exact ⟨rfl, rfl⟩

/-- Concrete non-vacuity witness instantiating `obeys_model` over `Model.modelStateFfiOps`. -/
theorem obeys_model_nonvacuous :
    Core.ObeysStepId Model.rawStepWf
      (Model.execPkgStep (Internal.mkRawOpsM Model.modelStateFfiOps)) Model.allowedPkgStep :=
  obeys_model.2 id Model.modelStateFfiOps modelStateFfiOps_obeys

end LeanSwe.CryptoHash.Raw.Proofs
