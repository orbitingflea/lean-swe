import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Model
import LeanSwe.CryptoHash.Raw.Impl
import LeanSwe.CryptoHash.Raw.Interface
import LeanSwe.CryptoHash.Raw.SpecTests
import LeanSwe.CryptoHash.Raw.Sha256Vectors
import LeanSwe.CryptoHash.Raw.Sha512Vectors
import LeanSwe.CryptoHash.Raw.HmacVectors
import LeanSwe.CryptoHash.Raw.HmacTc1
import LeanSwe.CryptoHash.Raw.HmacTc2
import LeanSwe.CryptoHash.Raw.HmacTc6

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
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid cryptohash argument" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | invalidHexInput detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "invalid hex input" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | lengthError expected got detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty s!"length mismatch: expected {expected} bytes, got {got}" detail (by
        intro h
        have hlen := congrArg String.length h
        simp [String.length] at hlen)
    · exact ⟨rfl, rfl⟩
    · trivial
  | opensslError code detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨?_, ?_, ?_⟩
    · exact nonEmptyMsg_ne_empty "openssl crypto error" detail (by decide)
    · exact ⟨rfl, rfl⟩
    · trivial
  | userError detail =>
    dsimp [test_cryptohashraw_mapRawError_mapsKindsAndNonEmptyMessage, defaultOps,
      Internal.mkRawOps, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
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
  dsimp [defaultOps, Internal.mkRawOps]
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
  dsimp [defaultOps, Internal.mkRawOps]
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
  dsimp [defaultOps, Internal.mkRawOps]
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

end LeanSwe.CryptoHash.Raw.Proofs
