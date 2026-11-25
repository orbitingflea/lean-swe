import LeanSwe.CryptoHash.Raw.Types

namespace LeanSwe.CryptoHash.Raw.Internal

open LeanSwe.CryptoHash.Raw
  (HashAlg digestLen CryptoHashErrorKind CryptoHashError CryptoHashRawError
   RawCryptoHashOpsM RawCryptoHashOps CryptoHashFfiOpsM CryptoHashFfiOps)

/-- Alias of `LeanSwe.CryptoHash.Raw.CryptoHashFfiOpsM` in `Internal`. -/
abbrev InternalCryptoHashFfiOpsM := CryptoHashFfiOpsM

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Convert a pure `CryptoHashRawError` record into a normalized `CryptoHashError` with non-empty message. -/
def mapRawError : CryptoHashRawError → CryptoHashError
  | .invalidArgument detail =>
    { kind := .invalidInput
      opensslCode := none
      message := nonEmptyMsg "invalid cryptohash argument" detail }
  | .invalidHexInput detail =>
    { kind := .invalidHex
      opensslCode := none
      message := nonEmptyMsg "invalid hex input" detail }
  | .lengthError expected got detail =>
    { kind := .lengthMismatch
      opensslCode := none
      message := nonEmptyMsg s!"length mismatch: expected {expected} bytes, got {got}" detail }
  | .opensslError code detail =>
    { kind := .cryptoError
      opensslCode := code
      message := nonEmptyMsg "openssl crypto error" detail }
  | .userError detail =>
    { kind := .cryptoError
      opensslCode := none
      message := nonEmptyMsg "cryptohash error" detail }

/-- Decode a non-zero C-shim `(code, detail)` OpenSSL failure into a normalized `CryptoHashError`. -/
def decodeOpenSslError (code : UInt64) (detail : String) : CryptoHashError :=
  mapRawError (.opensslError (if code == 0 then none else some code) detail)

/-- Decode a non-zero C-shim `(status, code, detail)` failure into a normalized `CryptoHashError`. -/
def decodeShimError (status : UInt32) (code : UInt64) (detail : String) : CryptoHashError :=
  if status == 1 then
    mapRawError (.invalidArgument detail)
  else if status == 2 then
    { kind := .lengthMismatch
      opensslCode := none
      message := nonEmptyMsg "cryptohash length mismatch" detail }
  else
    decodeOpenSslError code detail

/-- Build a polymorphic `RawCryptoHashOpsM m` bundle from injected OpenSSL C-ABI hooks. -/
def mkRawOpsM {m : Type → Type} [Monad m] (ffi : CryptoHashFfiOpsM m) : RawCryptoHashOpsM m :=
  { mapRawError := mapRawError
    digestRaw := fun alg data => do
      let tag : UInt8 := match alg with | .sha256 => 0 | .sha512 => 1
      let (status, code, detail, bs) ← ffi.digestRaw tag data
      if status != 0 then
        return .error (decodeShimError status code detail)
      if bs.size != digestLen alg then
        return .error (mapRawError (.lengthError (digestLen alg) bs.size
          s!"digest length mismatch: expected {digestLen alg} bytes, got {bs.size}"))
      return .ok bs
    hmacSha256Raw := fun key msg => do
      let (status, code, detail, bs) ← ffi.hmacSha256Raw key msg
      if status != 0 then
        return .error (decodeShimError status code detail)
      if bs.size != 32 then
        return .error (mapRawError (.lengthError 32 bs.size
          s!"HMAC-SHA256 length mismatch: expected 32 bytes, got {bs.size}"))
      return .ok bs
    ctEqualRaw := fun a b => do
      if a.size != b.size then
        return .error (mapRawError (.lengthError a.size b.size
          s!"length mismatch: expected {a.size} bytes, got {b.size}"))
      let eq ← ffi.ctEqualRaw a b
      return .ok eq }

/-- Build the concrete `RawCryptoHashOps` bundle from the injected `BaseIO` OpenSSL hooks. -/
def mkRawOps (ffi : CryptoHashFfiOps) : RawCryptoHashOps :=
  mkRawOpsM
    { digestRaw := fun tag data => liftM (ffi.digestRaw tag data)
      hmacSha256Raw := fun key msg => liftM (ffi.hmacSha256Raw key msg)
      ctEqualRaw := fun a b => liftM (ffi.ctEqualRaw a b) }

end LeanSwe.CryptoHash.Raw.Internal
