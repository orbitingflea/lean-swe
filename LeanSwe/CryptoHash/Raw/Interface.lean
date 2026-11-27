import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Impl

namespace LeanSwe.CryptoHash.Raw

@[extern "leanswe_cryptohash_digest"]
private opaque rawDigest : UInt8 → @& ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray)

@[extern "leanswe_cryptohash_hmac_sha256"]
private opaque rawHmacSha256 : @& ByteArray → @& ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray)

@[extern "leanswe_cryptohash_ct_equal"]
private opaque rawCtEqual : @& ByteArray → @& ByteArray → BaseIO Bool

/-- Default OpenSSL 3 `libcrypto` primitive bundle backed by `c/cryptohash_shim.c`. -/
def defaultOps : RawCryptoHashOps :=
  Internal.mkRawOps
    { digestRaw := rawDigest
      hmacSha256Raw := rawHmacSha256
      ctEqualRaw := rawCtEqual }

/-- Convert a raw error record into a normalized `CryptoHashError` with a non-empty message. -/
@[inline] def mapRawError (err : CryptoHashRawError) : CryptoHashError :=
  defaultOps.mapRawError err

/-- Compute raw digest bytes for `HashAlg` over arbitrary input bytes. -/
@[inline] def digestRaw (alg : HashAlg) (data : ByteArray) : IO (Except CryptoHashError ByteArray) :=
  defaultOps.digestRaw alg data

/-- Compute raw 32-byte RFC 2104 HMAC-SHA256 tag over arbitrary `key` and `msg`. -/
@[inline] def hmacSha256Raw (key msg : ByteArray) : IO (Except CryptoHashError ByteArray) :=
  defaultOps.hmacSha256Raw key msg

/-- Compare two `ByteArray` values in constant time via OpenSSL `CRYPTO_memcmp`. -/
@[inline] def ctEqualRaw (a b : ByteArray) : IO (Except CryptoHashError Bool) :=
  defaultOps.ctEqualRaw a b

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hfb : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hfb
  · rename_i hne
    intro hemp
    apply hne
    simp [hemp]

/-- `defaultOps.mapRawError` returns a non-empty message, normalized `kind`, and matching `opensslCode`. -/
theorem defaultOps_mapRawError_spec (raw : CryptoHashRawError) :
    let e := defaultOps.mapRawError raw
    e.message ≠ "" ∧
      match raw with
      | .invalidArgument _ => e.kind = .invalidInput ∧ e.opensslCode = none
      | .invalidHexInput _ => e.kind = .invalidHex ∧ e.opensslCode = none
      | .lengthError _ _ _ => e.kind = .lengthMismatch ∧ e.opensslCode = none
      | .opensslError code _ => e.kind = .cryptoError ∧ e.opensslCode = code
      | .userError _ => e.kind = .cryptoError ∧ e.opensslCode = none := by
  cases raw with
  | invalidArgument detail =>
    dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError]
    exact ⟨nonEmptyMsg_ne_empty "invalid cryptohash argument" detail (by decide), rfl, rfl⟩
  | invalidHexInput detail =>
    dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError]
    exact ⟨nonEmptyMsg_ne_empty "invalid hex input" detail (by decide), rfl, rfl⟩
  | lengthError expected got detail =>
    dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError]
    refine ⟨nonEmptyMsg_ne_empty s!"length mismatch: expected {expected} bytes, got {got}" detail ?_, rfl, rfl⟩
    intro h
    have hlen := congrArg String.length h
    simp [String.length] at hlen
  | opensslError code detail =>
    dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError]
    exact ⟨nonEmptyMsg_ne_empty "openssl crypto error" detail (by decide), rfl, rfl⟩
  | userError detail =>
    dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM, Internal.mapRawError]
    exact ⟨nonEmptyMsg_ne_empty "cryptohash error" detail (by decide), rfl, rfl⟩

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
    (Internal.decodeShimError status code detail).kind ≠ .invalidHex := by
  unfold Internal.decodeShimError Internal.decodeOpenSslError Internal.mapRawError
  split
  · simp
  · split <;> simp

/-- `defaultOps.digestRaw` never throws an `IO.Error`, returns `digestLen alg` bytes on success, and never reports `.invalidHex`. -/
theorem defaultOps_digestRaw_outcome (alg : HashAlg) (data : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (defaultOps.digestRaw alg data) w = .ok (.ok bs) w' ∧ bs.size = digestLen alg) ∨
    (∃ e w', (defaultOps.digestRaw alg data) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != digestLen alg) = true
    · simp only [hlen, ↓reduceIte]
      exact Or.inr ⟨_, _, rfl, by simp [Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      have heq : bs.size = digestLen alg := by
        cases hsz : (bs.size == digestLen alg)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

/-- `defaultOps.hmacSha256Raw` never throws an `IO.Error`, returns 32 bytes on success, and never reports `.invalidHex`. -/
theorem defaultOps_hmacSha256Raw_outcome (key msg : ByteArray) (w : Void IO.RealWorld) :
    (∃ bs w', (defaultOps.hmacSha256Raw key msg) w = .ok (.ok bs) w' ∧ bs.size = 32) ∨
    (∃ e w', (defaultOps.hmacSha256Raw key msg) w = .ok (.error e) w' ∧ e.kind ≠ .invalidHex) := by
  dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM]
  rw [io_bind_baseIO]
  rcases hres : ((_ : BaseIO _) w).val with ⟨status, code, detail, bs⟩
  dsimp only
  by_cases hs : (status != 0) = true
  · simp only [hs, ↓reduceIte]
    exact Or.inr ⟨_, _, rfl, decodeShimError_ne_invalidHex status code detail⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (bs.size != 32) = true
    · simp only [hlen, ↓reduceIte]
      exact Or.inr ⟨_, _, rfl, by simp [Internal.mapRawError]⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      have heq : bs.size = 32 := by
        cases hsz : (bs.size == 32)
        · simp [bne, hsz] at hlen
        · exact beq_iff_eq.mp hsz
      exact Or.inl ⟨bs, _, rfl, heq⟩

/-- `defaultOps.ctEqualRaw` never throws an `IO.Error` and reports `.lengthMismatch` iff sizes differ. -/
theorem defaultOps_ctEqualRaw_outcome (a b : ByteArray) (w : Void IO.RealWorld) :
    (a.size ≠ b.size ∧ ∃ e w', (defaultOps.ctEqualRaw a b) w = .ok (.error e) w' ∧ e.kind = .lengthMismatch) ∨
    (a.size = b.size ∧ ∃ eq w', (defaultOps.ctEqualRaw a b) w = .ok (.ok eq) w') := by
  dsimp [defaultOps, Internal.mkRawOps, Internal.mkRawOpsM]
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

end LeanSwe.CryptoHash.Raw
