import Core.Assumptions
import Core.Obeys
import LeanSweProofs.CryptoHash.Model
import LeanSweProofs.CryptoHash.Model.Refines
import LeanSwe.CryptoHash.Interface
import LeanSweProofs.CryptoHash.SpecTests
import LeanSweProofs.CryptoHash.Proofs.HexHelpers
import LeanSweProofs.CryptoHash.Proofs.MockApiProofs
import LeanSweProofs.CryptoHash.Proofs.HexSpecProofs
import LeanSweProofs.CryptoHash.Proofs.Sha256Vectors
import LeanSweProofs.CryptoHash.Proofs.Sha512Vectors
import LeanSweProofs.CryptoHash.Proofs.HmacVectors
import LeanSweProofs.CryptoHash.Proofs.HmacTc1
import LeanSweProofs.CryptoHash.Proofs.HmacTc2
import LeanSweProofs.CryptoHash.Proofs.HmacTc6

namespace LeanSwe.CryptoHash.Proofs

open Core
open Core.NondetTest
open LeanSwe.CryptoHash

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hfb : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hfb
  · rename_i hne
    intro hemp
    apply hne
    simp [hemp]

/-- `defaultApi.mapRawError` satisfies `test_cryptohash_mapRawError_preservesContract`. -/
theorem cryptohash_mapRawError_preservesContract :
    AllPass (test_cryptohash_mapRawError_preservesContract defaultApi) := by
  intro raw
  cases raw with
  | invalidArgument detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiFromFfiM,
      Internal.mkApiM, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "invalid cryptohash argument" detail (by decide), ⟨rfl, rfl⟩, trivial⟩
  | invalidHexInput detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiFromFfiM,
      Internal.mkApiM, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "invalid hex input" detail (by decide), ⟨rfl, rfl⟩, trivial⟩
  | lengthError expected got detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiFromFfiM,
      Internal.mkApiM, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    refine ⟨nonEmptyMsg_ne_empty s!"length mismatch: expected {expected} bytes, got {got}" detail ?_, ⟨rfl, rfl⟩, trivial⟩
    intro h
    have hlen := congrArg String.length h
    simp [String.length] at hlen
  | opensslError code detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiFromFfiM,
      Internal.mkApiM, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "openssl crypto error" detail (by decide), ⟨rfl, rfl⟩, trivial⟩
  | userError detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiFromFfiM,
      Internal.mkApiM, Internal.mkRawOpsM, Internal.mapRawError, Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "cryptohash error" detail (by decide), ⟨rfl, rfl⟩, trivial⟩

private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = .ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem io_bind_eq {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld) :
    (act >>= k) w =
      match act w with
      | EST.Out.ok a s => k a s
      | EST.Out.error e s => EST.Out.error e s := by
  dsimp only [Bind.bind, Monad.toBind, instMonadEIO, instMonadEIO._aux_13, EST.bind]
  cases act w <;> rfl

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
  rw [hst, io_bind_eq, hv]

private theorem decodeShimError_ne_invalidHex (status : UInt32) (code : UInt64) (detail : String) :
    (Internal.decodeShimError status code detail).kind ≠ .invalidHex := by
  unfold Internal.decodeShimError Internal.decodeOpenSslError Internal.mapRawError
  split
  · simp
  · split <;> simp

private theorem mkRawOpsM_baseIO_digestRaw_outcome
    (rawD : UInt8 → ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray))
    (rawH : ByteArray → ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray))
    (rawC : ByteArray → ByteArray → BaseIO Bool)
    (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    let ops : RawCryptoHashOps := Internal.mkRawOpsM
      { digestRaw := fun tag d => liftM (rawD tag d)
        hmacSha256Raw := fun k m => liftM (rawH k m)
        ctEqualRaw := fun a b => liftM (rawC a b) }
    (∃ bs w', (ops.digestRaw alg data) w = .ok (.ok bs) w') ∨
    (∃ e w', (ops.digestRaw alg data) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inl ⟨bs, _, rfl⟩

private theorem mkRawOpsM_baseIO_hmacSha256Raw_outcome
    (rawD : UInt8 → ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray))
    (rawH : ByteArray → ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray))
    (rawC : ByteArray → ByteArray → BaseIO Bool)
    (key msg : ByteArray) (w : Void IO.RealWorld) :
    let ops : RawCryptoHashOps := Internal.mkRawOpsM
      { digestRaw := fun tag d => liftM (rawD tag d)
        hmacSha256Raw := fun k m => liftM (rawH k m)
        ctEqualRaw := fun a b => liftM (rawC a b) }
    (∃ bs w', (ops.hmacSha256Raw key msg) w = .ok (.ok bs) w') ∨
    (∃ e w', (ops.hmacSha256Raw key msg) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    rw [io_pure_eq]
    exact Or.inl ⟨bs, _, rfl⟩

private theorem mkRawOpsM_baseIO_ctEqualRaw_outcome
    (rawD : UInt8 → ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray))
    (rawH : ByteArray → ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray))
    (rawC : ByteArray → ByteArray → BaseIO Bool)
    (a b : ByteArray) (w : Void IO.RealWorld) :
    let ops : RawCryptoHashOps := Internal.mkRawOpsM
      { digestRaw := fun tag d => liftM (rawD tag d)
        hmacSha256Raw := fun k m => liftM (rawH k m)
        ctEqualRaw := fun a b => liftM (rawC a b) }
    ∃ eq w', (ops.ctEqualRaw a b) w = .ok (.ok eq) w' := by
  dsimp [Internal.mkRawOpsM]
  rw [io_bind_baseIO, io_pure_eq]
  exact ⟨_, _, rfl⟩

private theorem hash_never_invalidHex
    (alg : HashAlg) (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (LeanSwe.CryptoHash.hash alg msg) w := by
  unfold Core.NeverErrorKindIO LeanSwe.CryptoHash.hash defaultApi Internal.mkApiFromFfiM Internal.mkApiM Internal.hashM
  dsimp only
  rw [io_bind_eq]
  rcases mkRawOpsM_baseIO_digestRaw_outcome _ _ _ alg msg w with ⟨bs, w', hok⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]
    dsimp only
    by_cases hlen : (bs.size != digestLen alg) = true
    · simp only [hlen, ↓reduceIte]
      rw [io_pure_eq]
      intro h; cases h
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [io_pure_eq]
      trivial
  · rw [herr]
    dsimp only
    rw [io_pure_eq]
    exact hek

private theorem hmacSha256_never_invalidHex
    (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (hmacSha256 key msg) w := by
  unfold Core.NeverErrorKindIO hmacSha256 defaultApi Internal.mkApiFromFfiM Internal.mkApiM Internal.hmacSha256M
  dsimp only
  rw [io_bind_eq]
  rcases mkRawOpsM_baseIO_hmacSha256Raw_outcome _ _ _ key msg w with ⟨bs, w', hok⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]
    dsimp only
    by_cases hlen : (bs.size != 32) = true
    · simp only [hlen, ↓reduceIte]
      rw [io_pure_eq]
      intro h; cases h
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [io_pure_eq]
      trivial
  · rw [herr]
    dsimp only
    rw [io_pure_eq]
    exact hek

private theorem ctEq_never (k : CryptoHashErrorKind)
    (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind k (ctEq a b) w := by
  unfold Core.NeverErrorKindIO ctEq defaultApi Internal.mkApiFromFfiM Internal.mkApiM Internal.ctEqM
  by_cases hne : (a.size != b.size) = true
  · simp only [hne, ↓reduceIte]
    rw [io_pure_eq]
    trivial
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rcases mkRawOpsM_baseIO_ctEqualRaw_outcome _ _ _ a b w with ⟨eq, w', hok⟩
    rw [hok]
    trivial

/-- `CryptoHash.hash` never returns `.invalidHex`. -/
theorem cryptohash_hash_never_invalidHex (alg : HashAlg) (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (LeanSwe.CryptoHash.hash alg msg) w :=
  hash_never_invalidHex alg msg w

/-- `CryptoHash.sha256` never returns `.invalidHex`. -/
theorem cryptohash_sha256_never_invalidHex (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (sha256 msg) w :=
  hash_never_invalidHex .sha256 msg w

/-- `CryptoHash.sha512` never returns `.invalidHex`. -/
theorem cryptohash_sha512_never_invalidHex (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (sha512 msg) w :=
  hash_never_invalidHex .sha512 msg w

/-- `CryptoHash.hmacSha256` never returns `.invalidHex`. -/
theorem cryptohash_hmacSha256_never_invalidHex (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (hmacSha256 key msg) w :=
  hmacSha256_never_invalidHex key msg w

/-- `CryptoHash.verifyHmacSha256` never returns `.invalidHex`. -/
theorem cryptohash_verifyHmacSha256_never_invalidHex
    (key msg : ByteArray) (expected : Digest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (verifyHmacSha256 key msg expected) w := by
  unfold Core.NeverErrorKindIO verifyHmacSha256 defaultApi Internal.mkApiFromFfiM Internal.mkApiM Internal.verifyHmacSha256M
  by_cases halg : (expected.alg != .sha256) = true
  · simp only [halg, ↓reduceIte]
    rw [io_pure_eq]
    intro h; cases h
  · simp only [halg, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (expected.bytes.size != 32) = true
    · simp only [hlen, ↓reduceIte]
      rw [io_pure_eq]
      intro h; cases h
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [io_bind_eq]
      dsimp only [Internal.hmacSha256M]
      rw [io_bind_eq]
      rcases mkRawOpsM_baseIO_hmacSha256Raw_outcome _ _ _ key msg w with ⟨bs, w', hok⟩ | ⟨e, w', herr, hek⟩
      · rw [hok]
        dsimp only
        by_cases hbs : (bs.size != 32) = true
        · simp only [hbs, ↓reduceIte]
          rw [io_pure_eq]
          dsimp only
          rw [io_pure_eq]
          intro h; cases h
        · simp only [hbs, Bool.false_eq_true, ↓reduceIte]
          rw [io_pure_eq]
          dsimp only [Internal.ctEqM]
          by_cases hne : (bs.size != expected.bytes.size) = true
          · simp only [hne, ↓reduceIte]
            rw [io_pure_eq]
            trivial
          · simp only [hne, Bool.false_eq_true, ↓reduceIte]
            rcases mkRawOpsM_baseIO_ctEqualRaw_outcome _ _ _ bs expected.bytes w' with ⟨eq, w'', hct⟩
            rw [hct]
            trivial
      · rw [herr]
        dsimp only
        rw [io_pure_eq]
        dsimp only
        rw [io_pure_eq]
        dsimp only
        exact hek

private theorem fromHex_never (k : CryptoHashErrorKind)
    (hk1 : k ≠ .invalidHex) (hk2 : k ≠ .lengthMismatch)
    (alg : HashAlg) (s : String) :
    Core.NeverErrorKindPure CryptoHashError.kind k (fromHex alg s) := by
  unfold Core.NeverErrorKindPure fromHex defaultApi Internal.mkApiFromFfiM Internal.mkApiM Internal.fromHex
  dsimp only
  rw [decodeHexPairsAcc_nil]
  cases decodeHexPairs s.toList with
  | none => dsimp only; exact hk1.symm
  | some bs =>
    dsimp only
    by_cases hlen : ((ByteArray.mk bs.toArray).size != digestLen alg) = true
    · simp only [hlen, ↓reduceIte]; exact hk2.symm
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]

/-- `CryptoHash.fromHex` never returns `.invalidInput`. -/
theorem cryptohash_fromHex_never_invalidInput (alg : HashAlg) (s : String) :
    Core.NeverErrorKindPure CryptoHashError.kind .invalidInput (fromHex alg s) :=
  fromHex_never .invalidInput (by decide) (by decide) alg s

/-- `CryptoHash.fromHex` never returns `.cryptoError`. -/
theorem cryptohash_fromHex_never_cryptoError (alg : HashAlg) (s : String) :
    Core.NeverErrorKindPure CryptoHashError.kind .cryptoError (fromHex alg s) :=
  fromHex_never .cryptoError (by decide) (by decide) alg s

/-- `CryptoHash.ctEq` never returns `.invalidInput`. -/
theorem cryptohash_ctEq_never_invalidInput (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidInput (ctEq a b) w :=
  ctEq_never .invalidInput a b w

/-- `CryptoHash.ctEq` never returns `.invalidHex`. -/
theorem cryptohash_ctEq_never_invalidHex (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .invalidHex (ctEq a b) w :=
  ctEq_never .invalidHex a b w

/-- `CryptoHash.ctEq` never returns `.lengthMismatch`. -/
theorem cryptohash_ctEq_never_lengthMismatch (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .lengthMismatch (ctEq a b) w :=
  ctEq_never .lengthMismatch a b w

/-- `CryptoHash.ctEq` never returns `.cryptoError`. -/
theorem cryptohash_ctEq_never_cryptoError (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CryptoHashError.kind .cryptoError (ctEq a b) w :=
  ctEq_never .cryptoError a b w

private theorem byteToHexCharsModel_eq : Model.byteToHexCharsModel = Internal.byteToHexChars := by
  funext b
  rfl

private theorem hexCharsToByteModel_eq : Model.hexCharsToByteModel = Internal.hexCharsToByte := by
  funext hi lo
  rfl

private theorem decodeHexPairsAccModel_eq (accRev : List UInt8) (cs : List Char) :
    Model.decodeHexPairsAccModel accRev cs = Internal.decodeHexPairsAcc accRev cs := by
  match cs with
  | [] => rfl
  | [_] => rfl
  | hi :: lo :: rest =>
    simp only [Model.decodeHexPairsAccModel, Internal.decodeHexPairsAcc, hexCharsToByteModel_eq]
    cases Internal.hexCharsToByte hi lo with
    | none => rfl
    | some b => exact decodeHexPairsAccModel_eq (b :: accRev) rest

private theorem toHexModel_eq : Model.toHexModel = Internal.toHex := by
  funext d
  simp [Model.toHexModel, Internal.toHex, Internal.formatHexList, byteToHexCharsModel_eq]

private theorem fromHexModel_eq : Model.fromHexModel = Internal.fromHex := by
  funext alg s
  dsimp only [Model.fromHexModel, Internal.fromHex]
  rw [decodeHexPairsAccModel_eq]
  rfl

private theorem digestBytesModel_size (alg : HashAlg) (msg : ByteArray) :
    (Model.digestBytesModel alg msg).size = digestLen alg := by
  cases alg <;> rfl

private theorem hmacSha256Bytes_size (key msg : ByteArray) :
    (Model.hmacSha256Bytes key msg).size = 32 := rfl

/-- `Model.modelRawOps` satisfies `test_cryptohash_modelDigestsValidLengthsAndVectors`. -/
theorem cryptohash_modelDigestsValidLengthsAndVectors :
    AllPass (test_cryptohash_modelDigestsValidLengthsAndVectors Model.modelRawOps) := by
  intro alg key msg
  dsimp only [test_cryptohash_modelDigestsValidLengthsAndVectors, Model.modelRawOps,
    Core.NondetTest.assert, Bind.bind, Pure.pure]
  exact ⟨rfl, digestBytesModel_size alg msg, rfl, hmacSha256Bytes_size key msg,
    sha256_empty_vec, sha256_abc_vec, sha512_empty_vec, sha512_abc_vec,
    hmac_tc1_vec, hmac_tc2_vec, hmac_tc6_vec, hmac_empty_vec, trivial⟩

/-- `Internal.mkApiM` satisfies `test_cryptohash_mkApi_matchesModel`. -/
theorem cryptohash_mkApi_matchesModel :
    AllPass (test_cryptohash_mkApi_matchesModel Internal.mkApiM) := by
  intro alg key msg expected hexStr a b rawErr
  dsimp only [test_cryptohash_mkApi_matchesModel]
  simp only [Internal.mkApiM, Model.modelApi, Model.modelRawOps,
    Internal.hashM, Internal.hmacSha256M, Internal.verifyHmacSha256M, Internal.ctEqM,
    Model.hashModel, Model.sha256Model, Model.sha512Model, Model.hmacSha256Model,
    Model.verifyHmacSha256Model, Model.ctEqModel, Model.ctEqualRawModel,
    toHexModel_eq, fromHexModel_eq, Bind.bind, bind, pure, Core.NondetTest.assert]
  have hd : ((Model.digestBytesModel alg msg).size != digestLen alg) = false :=
    bne_eq_false_iff_eq.mpr (digestBytesModel_size alg msg)
  have hd256 : ((Model.digestBytesModel .sha256 msg).size != digestLen .sha256) = false :=
    bne_eq_false_iff_eq.mpr (digestBytesModel_size .sha256 msg)
  have hd512 : ((Model.digestBytesModel .sha512 msg).size != digestLen .sha512) = false :=
    bne_eq_false_iff_eq.mpr (digestBytesModel_size .sha512 msg)
  have hh : ((Model.hmacSha256Bytes key msg).size != 32) = false :=
    bne_eq_false_iff_eq.mpr (hmacSha256Bytes_size key msg)
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, trivial, trivial, ?_, trivial⟩
  · simp [hd]
  · simp [hd256]
  · simp [hd512]
  · simp [hh]
  · cases halg : expected.alg
    · have hfa : (HashAlg.sha256 != HashAlg.sha256) = false := rfl
      simp only [hfa, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : expected.bytes.size = 32
      · have hfl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
        have hfl2 : ((Model.hmacSha256Bytes key msg).size != expected.bytes.size) = false := by
          rw [hmacSha256Bytes_size, hlen]; rfl
        simp [hfl, hh, hfl2]
      · have htl : (expected.bytes.size != 32) = true := bne_iff_ne.mpr hlen
        simp [htl]
    · have hta : (HashAlg.sha512 != HashAlg.sha256) = true := rfl
      simp [hta]
  · by_cases hsz : a.size = b.size
    · have hf : (a.size != b.size) = false := bne_eq_false_iff_eq.mpr hsz
      simp [hf]
    · have hne : (a == b) = false := by
        cases hab : a == b
        · rfl
        · have heq := eq_of_beq hab; subst heq; exact absurd rfl hsz
      rw [hne]
      have ht : (a.size != b.size) = true := bne_iff_ne.mpr hsz
      simp [ht]

/-- Non-vacuity witness for `test_cryptohash_mkApi_matchesModel`. -/
theorem reach_cryptohash_mkApi_matchesModel :
    CanReach (test_cryptohash_mkApi_matchesModel Internal.mkApiM) := by
  let d : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  exact ⟨.sha256, ByteArray.empty, ByteArray.empty, d, "", ByteArray.empty, ByteArray.empty,
    .invalidArgument "",
    cryptohash_mkApi_matchesModel .sha256 ByteArray.empty ByteArray.empty d "" ByteArray.empty ByteArray.empty (.invalidArgument "")⟩

private theorem mapRawError_eq_model (err : CryptoHashRawError) :
    LeanSwe.CryptoHash.mapRawError err = Model.mapRawErrorModel err := by
  cases err <;> rfl

private theorem stateM_map_run {W α β : Type} (f : α → β) (m : StateM W α) (w : W) :
    (f <$> m).run w = (f (m.run w).1, (m.run w).2) := rfl

private theorem stateM_bind_run {W α β : Type} (m : StateM W α) (k : α → StateM W β) (w : W) :
    (m >>= k).run w = (k (m.run w).1).run (m.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

private theorem hashM_mkRawOpsM_obeys {W : Type} {proj : W → Unit} {ffi : CryptoHashFfiOpsM (StateM W)}
    (hFfi : Core.ObeysStep proj Model.rawStepWf (Model.execFfiStep ffi) Model.allowedFfiStep)
    (w : W) (alg : HashAlg) (msg : ByteArray) :
    ((Internal.hashM (Internal.mkRawOpsM ffi) alg msg).run w).1 = Model.hashModel alg msg := by
  cases alg with
  | sha256 =>
    have hOut : ((ffi.digestRaw 0 msg).run w).1 = (0, 0, "", Model.sha256Bytes msg) :=
      (hFfi w (.digestRaw 0 msg) rfl).2
    have hSz : (Model.sha256Bytes msg).size = 32 := digestBytesModel_size .sha256 msg
    simp only [Internal.hashM, Internal.mkRawOpsM, Model.hashModel, Model.digestBytesModel,
      stateM_bind_run, hOut, digestLen, hSz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      stateM_pure_run]
  | sha512 =>
    have hOut : ((ffi.digestRaw 1 msg).run w).1 = (0, 0, "", Model.sha512Bytes msg) :=
      (hFfi w (.digestRaw 1 msg) rfl).2
    have hSz : (Model.sha512Bytes msg).size = 64 := digestBytesModel_size .sha512 msg
    simp only [Internal.hashM, Internal.mkRawOpsM, Model.hashModel, Model.digestBytesModel,
      stateM_bind_run, hOut, digestLen, hSz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      stateM_pure_run]

private theorem obeysStepFrom_mkApiFromFfiM :
    Core.ObeysStepFrom id Model.rawStepWf Model.execFfiStep Model.allowedFfiStep
      Model.rawStepWf Internal.mkApiFromFfiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj ffi hFfi w req _
  cases req with
  | hash alg msg =>
    simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM, Model.allowedPkgStep,
      stateM_map_run]
    exact ⟨trivial, hashM_mkRawOpsM_obeys hFfi w alg msg⟩
  | sha256 msg =>
    simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM, Model.allowedPkgStep,
      Model.sha256Model, stateM_map_run]
    exact ⟨trivial, hashM_mkRawOpsM_obeys hFfi w .sha256 msg⟩
  | sha512 msg =>
    simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM, Model.allowedPkgStep,
      Model.sha512Model, stateM_map_run]
    exact ⟨trivial, hashM_mkRawOpsM_obeys hFfi w .sha512 msg⟩
  | hmacSha256 key msg =>
    have hOut : ((ffi.hmacSha256Raw key msg).run w).1 = (0, 0, "", Model.hmacSha256Bytes key msg) :=
      (hFfi w (.hmacSha256Raw key msg) rfl).2
    have hSz : (Model.hmacSha256Bytes key msg).size = 32 := hmacSha256Bytes_size key msg
    simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM, Internal.hmacSha256M,
      Internal.mkRawOpsM, Model.allowedPkgStep, Model.hmacSha256Model,
      stateM_map_run, stateM_bind_run, hOut, hSz, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, stateM_pure_run]
    trivial
  | verifyHmacSha256 key msg expected =>
    cases halg : expected.alg with
    | sha512 =>
      have hta : (HashAlg.sha512 != HashAlg.sha256) = true := rfl
      simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM,
        Internal.verifyHmacSha256M, Model.allowedPkgStep, Model.verifyHmacSha256Model,
        halg, hta, ↓reduceIte, stateM_map_run, stateM_pure_run]
      trivial
    | sha256 =>
      have hfa : (HashAlg.sha256 != HashAlg.sha256) = false := rfl
      by_cases hlen : expected.bytes.size = 32
      · have hOut1 : ((ffi.hmacSha256Raw key msg).run w).1 =
            (0, 0, "", Model.hmacSha256Bytes key msg) :=
          (hFfi w (.hmacSha256Raw key msg) rfl).2
        let w1 := ((ffi.hmacSha256Raw key msg).run w).2
        have hOut2 : ((ffi.ctEqualRaw (Model.hmacSha256Bytes key msg) expected.bytes).run w1).1 =
            (Model.hmacSha256Bytes key msg == expected.bytes) :=
          (hFfi w1 (.ctEqualRaw (Model.hmacSha256Bytes key msg) expected.bytes) rfl).2
        have hSz : (Model.hmacSha256Bytes key msg).size = 32 := hmacSha256Bytes_size key msg
        simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM,
          Internal.verifyHmacSha256M, Internal.hmacSha256M, Internal.ctEqM, Internal.mkRawOpsM,
          Model.allowedPkgStep, Model.verifyHmacSha256Model,
          halg, hfa, Bool.false_eq_true, ↓reduceIte,
          stateM_map_run, stateM_bind_run, hOut1, hSz, hlen, bne_self_eq_false, stateM_pure_run,
          w1] at hOut2 ⊢
        rw [hOut2]
        trivial
      · have htl : (expected.bytes.size != 32) = true := bne_iff_ne.mpr hlen
        simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM,
          Internal.verifyHmacSha256M, Model.allowedPkgStep, Model.verifyHmacSha256Model,
          halg, hfa, htl, Bool.false_eq_true, ↓reduceIte, stateM_map_run, stateM_pure_run]
        trivial
  | ctEq a b =>
    by_cases hsz : a.size = b.size
    · have hf : (a.size != b.size) = false := bne_eq_false_iff_eq.mpr hsz
      have hOut : ((ffi.ctEqualRaw a b).run w).1 = (a == b) :=
        (hFfi w (.ctEqualRaw a b) rfl).2
      simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM, Internal.ctEqM,
        Internal.mkRawOpsM, Model.allowedPkgStep, Model.ctEqModel,
        hf, Bool.false_eq_true, ↓reduceIte, stateM_map_run, stateM_bind_run, hOut, stateM_pure_run]
      trivial
    · have ht : (a.size != b.size) = true := bne_iff_ne.mpr hsz
      have hne : (a == b) = false := by
        cases hab : a == b
        · rfl
        · exact absurd (congrArg ByteArray.size (eq_of_beq hab)) hsz
      simp only [Model.execPkgStep, Internal.mkApiFromFfiM, Internal.mkApiM, Internal.ctEqM,
        Model.allowedPkgStep, Model.ctEqModel,
        ht, ↓reduceIte, stateM_map_run, stateM_pure_run, hne]
      trivial

/-- Full public `Interface` obedience of `LeanSwe.CryptoHash` against `LeanSwe.CryptoHash.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.CryptoHash.mapRawError Model.mapRawErrorModel ∧
    Core.ObeysPureEq LeanSwe.CryptoHash.toHex Model.toHexModel ∧
    Core.ObeysPureEq2 LeanSwe.CryptoHash.fromHex Model.fromHexModel ∧
    Core.ObeysStepFrom id Model.rawStepWf Model.execFfiStep Model.allowedFfiStep
      Model.rawStepWf Internal.mkApiFromFfiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_eq_model,
   fun _ => (toHexModel_eq ▸ rfl),
   fun _ _ => (fromHexModel_eq ▸ rfl),
   obeysStepFrom_mkApiFromFfiM⟩

private theorem modelStateFfiOps_obeys :
    Core.ObeysStepId Model.rawStepWf
      (Model.execFfiStep Model.modelStateFfiOps) Model.allowedFfiStep := by
  intro s req _
  cases req <;> exact ⟨rfl, rfl⟩

/-- Concrete non-vacuity witness instantiating `obeys_model` over `Model.modelStateFfiOps`. -/
theorem obeys_model_nonvacuous :
    Core.ObeysStepId Model.rawStepWf
      (Model.execPkgStep (Internal.mkApiFromFfiM Model.modelStateFfiOps)) Model.allowedPkgStep :=
  obeys_model.2.2.2 id Model.modelStateFfiOps modelStateFfiOps_obeys

end LeanSwe.CryptoHash.Proofs
