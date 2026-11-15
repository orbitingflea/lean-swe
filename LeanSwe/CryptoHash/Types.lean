import LeanSwe.CryptoHash.Raw.Types

namespace LeanSwe.CryptoHash

export LeanSwe.CryptoHash.Raw
  (HashAlg digestLen CryptoHashErrorKind CryptoHashError CryptoHashRawError
   RawCryptoHashOpsM RawCryptoHashOps)

/-- Cryptographic digest tagged by its `HashAlg`. -/
structure Digest where
  /-- Hash algorithm that produced or owns this digest. -/
  alg : HashAlg
  /-- Raw digest bytes (expected length `digestLen alg`). -/
  bytes : ByteArray
  deriving BEq, DecidableEq, Inhabited

instance : Repr Digest where
  reprPrec d prec :=
    Repr.addAppParen ("Digest.mk " ++ repr d.alg ++ " " ++ repr d.bytes.data) prec

/-- Proposition asserting `d.bytes` has the exact length required by `d.alg`. -/
def ValidDigest (d : Digest) : Prop :=
  d.bytes.size = digestLen d.alg

/-- Boolean check that `d.bytes` has the exact length required by `d.alg`. -/
def Digest.isValid (d : Digest) : Bool :=
  d.bytes.size == digestLen d.alg

/-- Deterministic mock state for testing and proofs over `RawCryptoHashOpsM (StateM MockCryptoHashState)`. -/
structure MockCryptoHashState where
  /-- Number of `digestRaw` calls observed. -/
  digestCalls : Nat := 0
  /-- Number of `hmacSha256Raw` calls observed. -/
  hmacCalls : Nat := 0
  /-- Number of `ctEqualRaw` calls observed. -/
  ctEqCalls : Nat := 0
  /-- Optional injected error returned by `digestRaw`. -/
  failDigestWith : Option CryptoHashError := none
  /-- Optional injected error returned by `hmacSha256Raw`. -/
  failHmacWith : Option CryptoHashError := none
  /-- Optional injected error returned by `ctEqualRaw`. -/
  failCtEqWith : Option CryptoHashError := none
  /-- Optional corrupted byte length returned by `digestRaw` instead of `digestLen alg`. -/
  corruptDigestLen : Option Nat := none
  /-- Optional corrupted byte length returned by `hmacSha256Raw` instead of `32`. -/
  corruptHmacLen : Option Nat := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Public cryptographic hash and HMAC API exported by `LeanSwe.CryptoHash`, parameterized over `m`. -/
structure CryptoHashApiM (m : Type → Type) where
  /-- Convert a raw error record into a normalized `CryptoHashError` with a non-empty message. -/
  mapRawError : CryptoHashRawError → CryptoHashError
  /-- Compute a digest for `HashAlg` over arbitrary input bytes. -/
  hash : HashAlg → ByteArray → m (Except CryptoHashError Digest)
  /-- Compute a SHA-256 digest over arbitrary input bytes. -/
  sha256 : ByteArray → m (Except CryptoHashError Digest)
  /-- Compute a SHA-512 digest over arbitrary input bytes. -/
  sha512 : ByteArray → m (Except CryptoHashError Digest)
  /-- Compute an RFC 2104 HMAC-SHA256 digest over arbitrary `key` and `msg`. -/
  hmacSha256 : ByteArray → ByteArray → m (Except CryptoHashError Digest)
  /-- Verify an expected HMAC-SHA256 `Digest` in constant time. -/
  verifyHmacSha256 : ByteArray → ByteArray → Digest → m (Except CryptoHashError Bool)
  /-- Encode `Digest` bytes as lowercase ASCII hexadecimal characters. -/
  toHex : Digest → String
  /-- Decode case-insensitive ASCII hexadecimal characters into a length-checked `Digest`. -/
  fromHex : HashAlg → String → Except CryptoHashError Digest
  /-- Compare two byte slices in constant time, returning `false` on unequal lengths. -/
  ctEq : ByteArray → ByteArray → m (Except CryptoHashError Bool)

/-- Concrete `IO` cryptographic hash API bundle exported by `LeanSwe.CryptoHash`. -/
abbrev CryptoHashApi := CryptoHashApiM IO

end LeanSwe.CryptoHash
