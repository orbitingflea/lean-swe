import Core.Assumptions
import Core.Obeys
import LeanSwe.CryptoHash.Model
import LeanSwe.CryptoHash.Interface
import LeanSwe.CryptoHash.SpecTests
import LeanSwe.CryptoHash.Proofs.HexHelpers
import LeanSwe.CryptoHash.Proofs.MockApiProofs
import LeanSwe.CryptoHash.Proofs.HexSpecProofs

namespace LeanSwe.CryptoHash.Proofs

open Core
open Core.NondetTest
open LeanSwe.CryptoHash

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hfb : fallback ≠ "") :
    Raw.Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Raw.Internal.nonEmptyMsg
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
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiM,
      Raw.defaultOps, Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM, Raw.Internal.mapRawError,
      Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "invalid cryptohash argument" detail (by decide), ⟨rfl, rfl⟩, trivial⟩
  | invalidHexInput detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiM,
      Raw.defaultOps, Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM, Raw.Internal.mapRawError,
      Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "invalid hex input" detail (by decide), ⟨rfl, rfl⟩, trivial⟩
  | lengthError expected got detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiM,
      Raw.defaultOps, Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM, Raw.Internal.mapRawError,
      Core.NondetTest.assert, Bind.bind]
    refine ⟨nonEmptyMsg_ne_empty s!"length mismatch: expected {expected} bytes, got {got}" detail ?_,
      ⟨rfl, rfl⟩, trivial⟩
    intro h
    have hlen := congrArg String.length h
    simp [String.length] at hlen
  | opensslError code detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiM,
      Raw.defaultOps, Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM, Raw.Internal.mapRawError,
      Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "openssl crypto error" detail (by decide), ⟨rfl, rfl⟩, trivial⟩
  | userError detail =>
    dsimp [test_cryptohash_mapRawError_preservesContract, defaultApi, Internal.mkApiM,
      Raw.defaultOps, Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM, Raw.Internal.mapRawError,
      Core.NondetTest.assert, Bind.bind]
    exact ⟨nonEmptyMsg_ne_empty "cryptohash error" detail (by decide), ⟨rfl, rfl⟩, trivial⟩

private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = .ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

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
    (Raw.Internal.decodeShimError status code detail).kind ≠ .invalidHex := by
  unfold Raw.Internal.decodeShimError Raw.Internal.decodeOpenSslError Raw.Internal.mapRawError
  split
  · simp
  · split <;> simp

private theorem mkRawOps_digestRaw_outcome (ffi : Raw.CryptoHashFfiOps)
    (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', ((Raw.Internal.mkRawOps ffi).digestRaw alg data) w = .ok (.ok bs) w' ∧ bs.size = digestLen alg) ∨
    (∃ e w', ((Raw.Internal.mkRawOps ffi).digestRaw alg data) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != digestLen alg) = true
    · simp only [hlen, ↓reduceIte]
      exact Or.inr ⟨_, _, rfl, by simp [Raw.Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      have heq : bs.size = digestLen alg := by
        cases hsz : (bs.size == digestLen alg)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

private theorem defaultOps_digestRaw_outcome (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (Raw.defaultOps.digestRaw alg data) w = .ok (.ok bs) w' ∧ bs.size = digestLen alg) ∨
    (∃ e w', (Raw.defaultOps.digestRaw alg data) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  apply mkRawOps_digestRaw_outcome

private theorem mkRawOps_hmacSha256Raw_outcome (ffi : Raw.CryptoHashFfiOps)
    (key msg : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', ((Raw.Internal.mkRawOps ffi).hmacSha256Raw key msg) w = .ok (.ok bs) w' ∧ bs.size = 32) ∨
    (∃ e w', ((Raw.Internal.mkRawOps ffi).hmacSha256Raw key msg) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != 32) = true
    · simp only [hlen, ↓reduceIte]
      exact Or.inr ⟨_, _, rfl, by simp [Raw.Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      have heq : bs.size = 32 := by
        cases hsz : (bs.size == 32)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

private theorem defaultOps_hmacSha256Raw_outcome (key msg : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (Raw.defaultOps.hmacSha256Raw key msg) w = .ok (.ok bs) w' ∧ bs.size = 32) ∨
    (∃ e w', (Raw.defaultOps.hmacSha256Raw key msg) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  apply mkRawOps_hmacSha256Raw_outcome

private theorem mkRawOps_ctEqualRaw_outcome (ffi : Raw.CryptoHashFfiOps)
    (a b : ByteArray) (w : Void IO.RealWorld) :
    (a.size ≠ b.size ∧ ∃ e w', ((Raw.Internal.mkRawOps ffi).ctEqualRaw a b) w = .ok (.error e) w' ∧ e.kind = .lengthMismatch) ∨
    (a.size = b.size ∧ ∃ eq w', ((Raw.Internal.mkRawOps ffi).ctEqualRaw a b) w = .ok (.ok eq) w') := by
  dsimp [Raw.Internal.mkRawOps, Raw.Internal.mkRawOpsM]
  by_cases hne : (a.size != b.size) = true
  · simp only [hne, ↓reduceIte]
    exact Or.inl ⟨bne_iff_ne.mp hne, _, _, rfl, rfl⟩
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_baseIO]
    have heq : a.size = b.size := by
      cases hsz : (a.size == b.size)
      · simp [bne, hsz] at hne
      · exact beq_iff_eq.mp hsz
    exact Or.inr ⟨heq, _, _, rfl⟩

private theorem defaultOps_ctEqualRaw_outcome (a b : ByteArray) (w : Void IO.RealWorld) :
    (a.size ≠ b.size ∧ ∃ e w', (Raw.defaultOps.ctEqualRaw a b) w = .ok (.error e) w' ∧ e.kind = .lengthMismatch) ∨
    (a.size = b.size ∧ ∃ eq w', (Raw.defaultOps.ctEqualRaw a b) w = .ok (.ok eq) w') := by
  apply mkRawOps_ctEqualRaw_outcome

private theorem io_bind_eq {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld) :
    (act >>= k) w =
      match act w with
      | EST.Out.ok a s => k a s
      | EST.Out.error e s => EST.Out.error e s := by
  dsimp only [Bind.bind, Monad.toBind, instMonadEIO, instMonadEIO._aux_13, EST.bind]
  cases act w <;> rfl

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem hash_never_invalidHex
    (alg : HashAlg) (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (LeanSwe.CryptoHash.hash alg msg) w := by
  unfold Core.NeverErrorKindIO LeanSwe.CryptoHash.hash defaultApi Internal.mkApiM Internal.hashM
  dsimp only
  rw [io_bind_eq]
  rcases defaultOps_digestRaw_outcome alg msg w with ⟨bs, w', hok, hsz⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]
    have hf : (bs.size != Raw.digestLen alg) = false := bne_eq_false_iff_eq.mpr hsz
    dsimp only
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [io_pure_eq]
    trivial
  · rw [herr]
    dsimp only
    rw [io_pure_eq]
    exact hek

private theorem hmacSha256_never_invalidHex
    (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (hmacSha256 key msg) w := by
  unfold Core.NeverErrorKindIO hmacSha256 defaultApi Internal.mkApiM Internal.hmacSha256M
  dsimp only
  rw [io_bind_eq]
  rcases defaultOps_hmacSha256Raw_outcome key msg w with ⟨bs, w', hok, hsz⟩ | ⟨e, w', herr, hek⟩
  · rw [hok]
    have hf : (bs.size != 32) = false := bne_eq_false_iff_eq.mpr hsz
    dsimp only
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [io_pure_eq]
    trivial
  · rw [herr]
    dsimp only
    rw [io_pure_eq]
    exact hek

private theorem ctEq_never (k : CryptoHashErrorKind)
    (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind k (ctEq a b) w := by
  unfold Core.NeverErrorKindIO ctEq defaultApi Internal.mkApiM Internal.ctEqM
  by_cases hne : (a.size != b.size) = true
  · simp only [hne, ↓reduceIte]
    rw [io_pure_eq]
    trivial
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have heq : a.size = b.size := by
      cases hsz : (a.size == b.size)
      · simp [bne, hsz] at hne
      · exact beq_iff_eq.mp hsz
    rcases defaultOps_ctEqualRaw_outcome a b w with ⟨hdiff, _⟩ | ⟨_, eq, w', hok⟩
    · exact absurd heq hdiff
    · rw [hok]; trivial

/-- `CryptoHash.hash` never returns `.invalidHex`. -/
theorem cryptohash_hash_never_invalidHex (alg : HashAlg) (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (LeanSwe.CryptoHash.hash alg msg) w :=
  hash_never_invalidHex alg msg w

/-- `CryptoHash.sha256` never returns `.invalidHex`. -/
theorem cryptohash_sha256_never_invalidHex (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (sha256 msg) w :=
  hash_never_invalidHex .sha256 msg w

/-- `CryptoHash.sha512` never returns `.invalidHex`. -/
theorem cryptohash_sha512_never_invalidHex (msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (sha512 msg) w :=
  hash_never_invalidHex .sha512 msg w

/-- `CryptoHash.hmacSha256` never returns `.invalidHex`. -/
theorem cryptohash_hmacSha256_never_invalidHex (key msg : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (hmacSha256 key msg) w :=
  hmacSha256_never_invalidHex key msg w

/-- `CryptoHash.verifyHmacSha256` never returns `.invalidHex`. -/
theorem cryptohash_verifyHmacSha256_never_invalidHex
    (key msg : ByteArray) (expected : Digest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (verifyHmacSha256 key msg expected) w := by
  unfold Core.NeverErrorKindIO verifyHmacSha256 defaultApi Internal.mkApiM Internal.verifyHmacSha256M
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
      have hexp : expected.bytes.size = 32 := by
        cases hsz : (expected.bytes.size == 32)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      rw [io_bind_eq]
      dsimp only [Internal.hmacSha256M]
      rw [io_bind_eq]
      rcases defaultOps_hmacSha256Raw_outcome key msg w with ⟨bs, w', hok, hbs⟩ | ⟨e, w', herr, hek⟩
      · rw [hok]
        have hf : (bs.size != 32) = false := bne_eq_false_iff_eq.mpr hbs
        dsimp only
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        rw [io_pure_eq]
        dsimp only [Internal.ctEqM]
        have hszEq : bs.size = expected.bytes.size := by rw [hbs, hexp]
        have hne : (bs.size != expected.bytes.size) = false := bne_eq_false_iff_eq.mpr hszEq
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        rcases defaultOps_ctEqualRaw_outcome bs expected.bytes w' with ⟨hdiff, _⟩ | ⟨_, eq, w'', hct⟩
        · exact absurd hszEq hdiff
        · rw [hct]; trivial
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
    Core.NeverErrorKindPure Raw.CryptoHashError.kind k (fromHex alg s) := by
  unfold Core.NeverErrorKindPure fromHex defaultApi Internal.mkApiM Internal.fromHex
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
    Core.NeverErrorKindPure Raw.CryptoHashError.kind .invalidInput (fromHex alg s) :=
  fromHex_never .invalidInput (by decide) (by decide) alg s

/-- `CryptoHash.fromHex` never returns `.cryptoError`. -/
theorem cryptohash_fromHex_never_cryptoError (alg : HashAlg) (s : String) :
    Core.NeverErrorKindPure Raw.CryptoHashError.kind .cryptoError (fromHex alg s) :=
  fromHex_never .cryptoError (by decide) (by decide) alg s

/-- `CryptoHash.ctEq` never returns `.invalidInput`. -/
theorem cryptohash_ctEq_never_invalidInput (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidInput (ctEq a b) w :=
  ctEq_never .invalidInput a b w

/-- `CryptoHash.ctEq` never returns `.invalidHex`. -/
theorem cryptohash_ctEq_never_invalidHex (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .invalidHex (ctEq a b) w :=
  ctEq_never .invalidHex a b w

/-- `CryptoHash.ctEq` never returns `.lengthMismatch`. -/
theorem cryptohash_ctEq_never_lengthMismatch (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .lengthMismatch (ctEq a b) w :=
  ctEq_never .lengthMismatch a b w

/-- `CryptoHash.ctEq` never returns `.cryptoError`. -/
theorem cryptohash_ctEq_never_cryptoError (a b : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO Raw.CryptoHashError.kind .cryptoError (ctEq a b) w :=
  ctEq_never .cryptoError a b w

private theorem lowerHexDigitModel_eq : Model.lowerHexDigitModel = Internal.lowerHexDigit := by
  funext n
  rfl

private theorem hexCharToNibbleModel_eq : Model.hexCharToNibbleModel = Internal.hexCharToNibble := by
  funext c
  rfl

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
    (Raw.Model.digestBytesModel alg msg).size = digestLen alg := by
  cases alg <;> rfl

private theorem hmacSha256Bytes_size (key msg : ByteArray) :
    (Raw.Model.hmacSha256Bytes key msg).size = 32 := rfl

/-- `Internal.mkApiM` satisfies `test_cryptohash_mkApi_matchesModel`. -/
theorem cryptohash_mkApi_matchesModel :
    AllPass (test_cryptohash_mkApi_matchesModel Internal.mkApiM) := by
  intro alg key msg expected hexStr a b rawErr
  dsimp only [test_cryptohash_mkApi_matchesModel]
  simp only [Internal.mkApiM, Model.modelApi, Raw.Model.modelRawOps,
    Internal.hashM, Internal.hmacSha256M, Internal.verifyHmacSha256M, Internal.ctEqM,
    Model.hashModel, Model.sha256Model, Model.sha512Model, Model.hmacSha256Model,
    Model.verifyHmacSha256Model, Model.ctEqModel, Raw.Model.ctEqualRawModel,
    toHexModel_eq, fromHexModel_eq, Bind.bind, bind, pure, Core.NondetTest.assert]
  have hd : ((Raw.Model.digestBytesModel alg msg).size != digestLen alg) = false :=
    bne_eq_false_iff_eq.mpr (digestBytesModel_size alg msg)
  have hd256 : ((Raw.Model.digestBytesModel .sha256 msg).size != digestLen .sha256) = false :=
    bne_eq_false_iff_eq.mpr (digestBytesModel_size .sha256 msg)
  have hd512 : ((Raw.Model.digestBytesModel .sha512 msg).size != digestLen .sha512) = false :=
    bne_eq_false_iff_eq.mpr (digestBytesModel_size .sha512 msg)
  have hh : ((Raw.Model.hmacSha256Bytes key msg).size != 32) = false :=
    bne_eq_false_iff_eq.mpr (hmacSha256Bytes_size key msg)
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, trivial, trivial, ?_, trivial⟩
  · simp [hd]
  · simp [hd256]
  · simp [hd512]
  · simp [hh]
  · cases halg : expected.alg
    · have hfa : (Raw.HashAlg.sha256 != Raw.HashAlg.sha256) = false := rfl
      simp only [hfa, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : expected.bytes.size = 32
      · have hfl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
        have hfl2 : ((Raw.Model.hmacSha256Bytes key msg).size != expected.bytes.size) = false := by
          rw [hmacSha256Bytes_size, hlen]; rfl
        simp [hfl, hh, hfl2]
      · have htl : (expected.bytes.size != 32) = true := bne_iff_ne.mpr hlen
        simp [htl]
    · have hta : (Raw.HashAlg.sha512 != Raw.HashAlg.sha256) = true := rfl
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

private theorem obeysStepFrom_mkApiM :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req _
  cases req with
  | hash alg msg =>
    have hStep := hRaw w (.digestRaw alg msg) rfl
    dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
      StateT.bind, Pure.pure, StateT.pure, StateT.run] at hStep
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.hashM, Functor.map, StateT.map,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp]
    cases hd : raw.digestRaw alg msg w with
    | mk res w' =>
      simp only [hd] at hStep ⊢
      rcases hStep with ⟨_, rfl⟩
      have hsz : ((Raw.Model.digestBytesModel alg msg).size != digestLen alg) = false :=
        bne_eq_false_iff_eq.mpr (digestBytesModel_size alg msg)
      simp [Model.allowedPkgStep, Model.hashModel, Pure.pure, StateT.pure, hsz]
  | sha256 msg =>
    have hStep := hRaw w (.digestRaw .sha256 msg) rfl
    dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
      StateT.bind, Pure.pure, StateT.pure, StateT.run] at hStep
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.hashM, Functor.map, StateT.map,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp]
    cases hd : raw.digestRaw .sha256 msg w with
    | mk res w' =>
      simp only [hd] at hStep ⊢
      rcases hStep with ⟨_, rfl⟩
      have hsz : ((Raw.Model.digestBytesModel .sha256 msg).size != digestLen .sha256) = false :=
        bne_eq_false_iff_eq.mpr (digestBytesModel_size .sha256 msg)
      simp [Model.allowedPkgStep, Model.sha256Model, Model.hashModel, Pure.pure, StateT.pure, hsz]
  | sha512 msg =>
    have hStep := hRaw w (.digestRaw .sha512 msg) rfl
    dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
      StateT.bind, Pure.pure, StateT.pure, StateT.run] at hStep
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.hashM, Functor.map, StateT.map,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp]
    cases hd : raw.digestRaw .sha512 msg w with
    | mk res w' =>
      simp only [hd] at hStep ⊢
      rcases hStep with ⟨_, rfl⟩
      have hsz : ((Raw.Model.digestBytesModel .sha512 msg).size != digestLen .sha512) = false :=
        bne_eq_false_iff_eq.mpr (digestBytesModel_size .sha512 msg)
      simp [Model.allowedPkgStep, Model.sha512Model, Model.hashModel, Pure.pure, StateT.pure, hsz]
  | hmacSha256 key msg =>
    have hStep := hRaw w (.hmacSha256Raw key msg) rfl
    dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
      StateT.bind, Pure.pure, StateT.pure, StateT.run] at hStep
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.hmacSha256M, Functor.map, StateT.map,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Function.comp]
    cases hh : raw.hmacSha256Raw key msg w with
    | mk res w' =>
      simp only [hh] at hStep ⊢
      rcases hStep with ⟨_, rfl⟩
      have hsz : ((Raw.Model.hmacSha256Bytes key msg).size != 32) = false :=
        bne_eq_false_iff_eq.mpr (hmacSha256Bytes_size key msg)
      simp [Model.allowedPkgStep, Model.hmacSha256Model, Pure.pure, StateT.pure, hsz]
  | verifyHmacSha256 key msg expected =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.verifyHmacSha256M, Internal.hmacSha256M,
      Internal.ctEqM, Functor.map, StateT.map, Bind.bind, StateT.bind, Pure.pure, StateT.pure,
      Id.instMonad, StateT.run, Function.comp]
    cases halg : expected.alg with
    | sha512 =>
      have hta : (Raw.HashAlg.sha512 != Raw.HashAlg.sha256) = true := rfl
      simp only [hta, ↓reduceIte, StateT.pure, Pure.pure, Model.allowedPkgStep,
        Model.verifyHmacSha256Model, id]
      rw [halg]
      simp [hta]
    | sha256 =>
      have hfa : (Raw.HashAlg.sha256 != Raw.HashAlg.sha256) = false := rfl
      simp only [hfa, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : expected.bytes.size = 32
      · have hfl : (expected.bytes.size != 32) = false := bne_eq_false_iff_eq.mpr hlen
        simp only [hfl, Bool.false_eq_true, ↓reduceIte, StateT.bind]
        have hStep1 := hRaw w (.hmacSha256Raw key msg) rfl
        dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
          StateT.bind, Pure.pure, StateT.pure, StateT.run] at hStep1
        cases hh : raw.hmacSha256Raw key msg w with
        | mk res1 w1 =>
          simp only [hh] at hStep1 ⊢
          rcases hStep1 with ⟨_, rfl⟩
          have hsz : ((Raw.Model.hmacSha256Bytes key msg).size != 32) = false :=
            bne_eq_false_iff_eq.mpr (hmacSha256Bytes_size key msg)
          have hsz2 : ((Raw.Model.hmacSha256Bytes key msg).size != expected.bytes.size) = false := by
            rw [hmacSha256Bytes_size, hlen]; rfl
          simp only [hsz, hsz2, Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.pure, Pure.pure]
          have hStep2 := hRaw w1 (.ctEqualRaw (Raw.Model.hmacSha256Bytes key msg) expected.bytes) rfl
          dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
            StateT.bind, Pure.pure, StateT.pure, StateT.run] at hStep2
          cases hc : raw.ctEqualRaw (Raw.Model.hmacSha256Bytes key msg) expected.bytes w1 with
          | mk res2 w2 =>
            simp only [hc] at hStep2 ⊢
            rcases hStep2 with ⟨_, rfl⟩
            simp only [Model.allowedPkgStep, Model.verifyHmacSha256Model, Raw.Model.ctEqualRawModel, id]
            rw [halg]
            simp [hfa, hfl]
            exact (hmacSha256Bytes_size key msg).trans hlen.symm
      · have htl : (expected.bytes.size != 32) = true := bne_iff_ne.mpr hlen
        simp only [htl, ↓reduceIte, StateT.pure, Pure.pure, Model.allowedPkgStep,
          Model.verifyHmacSha256Model, id]
        rw [halg]
        simp [hfa]
  | ctEq a b =>
    dsimp only [Model.execPkgStep, Internal.mkApiM, Internal.ctEqM, Functor.map, StateT.map,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, Id.instMonad, StateT.run, Function.comp]
    by_cases hsz : a.size = b.size
    · have hf : (a.size != b.size) = false := bne_eq_false_iff_eq.mpr hsz
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      have hStep := hRaw w (.ctEqualRaw a b) rfl
      dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, StateT.run] at hStep
      cases hc : raw.ctEqualRaw a b w with
      | mk res w' =>
        simp only [hc] at hStep ⊢
        rcases hStep with ⟨_, rfl⟩
        simp [Model.allowedPkgStep, Model.ctEqModel, Raw.Model.ctEqualRawModel, hf]
    · have ht : (a.size != b.size) = true := bne_iff_ne.mpr hsz
      have hne : (a == b) = false := by
        cases hab : a == b
        · rfl
        · exact absurd (congrArg ByteArray.size (eq_of_beq hab)) hsz
      simp only [ht, ↓reduceIte, StateT.pure, Pure.pure, Model.allowedPkgStep, Model.ctEqModel, id]
      simp [hne]

/-- Full public `Interface` obedience of `LeanSwe.CryptoHash` against `LeanSwe.CryptoHash.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.CryptoHash.mapRawError Model.mapRawErrorModel ∧
    Core.ObeysPureEq LeanSwe.CryptoHash.toHex Model.toHexModel ∧
    Core.ObeysPureEq2 LeanSwe.CryptoHash.fromHex Model.fromHexModel ∧
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨mapRawError_eq_model,
   fun _ => (toHexModel_eq ▸ rfl),
   fun _ _ => (fromHexModel_eq ▸ rfl),
   obeysStepFrom_mkApiM⟩

end LeanSwe.CryptoHash.Proofs
