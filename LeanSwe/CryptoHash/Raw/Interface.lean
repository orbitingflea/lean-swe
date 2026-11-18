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

end LeanSwe.CryptoHash.Raw
