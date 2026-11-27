import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Model

namespace LeanSwe.CryptoHash.Raw.Model

/-- Request algebra for injected OpenSSL `CryptoHashFfiOpsM` calls. -/
inductive FfiStepReq where
  /-- Raw digest call `(tag, data)` (`0 = SHA-256`, `1 = SHA-512`). -/
  | digestRaw (tag : UInt8) (data : ByteArray)
  /-- Raw HMAC-SHA256 call `(key, msg)`. -/
  | hmacSha256Raw (key msg : ByteArray)
  /-- Raw constant-time slice comparison `(a, b)`. -/
  | ctEqualRaw (a b : ByteArray)
  deriving BEq, DecidableEq, Inhabited

/-- Output algebra for injected OpenSSL `CryptoHashFfiOpsM` calls. -/
inductive FfiStepOut where
  /-- `(status, opensslCode, detail, digestBytes)` tuple from `digestRaw` or `hmacSha256Raw`. -/
  | shimBytes (res : UInt32 × UInt64 × String × ByteArray)
  /-- Boolean comparison flag from `ctEqualRaw`. -/
  | flag (eq : Bool)
  deriving BEq, DecidableEq, Inhabited

/-- Request algebra for effectful `RawCryptoHashOpsM` operations. -/
inductive PkgStepReq where
  /-- Raw digest request `(alg, data)`. -/
  | digestRaw (alg : HashAlg) (data : ByteArray)
  /-- Raw HMAC-SHA256 request `(key, msg)`. -/
  | hmacSha256Raw (key msg : ByteArray)
  /-- Raw constant-time equality request `(a, b)`. -/
  | ctEqualRaw (a b : ByteArray)
  deriving BEq, DecidableEq, Inhabited

/-- Output algebra for effectful `RawCryptoHashOpsM` operations. -/
inductive PkgStepOut where
  /-- Fallible digest or HMAC byte-array result. -/
  | bytes (res : Except CryptoHashError ByteArray)
  /-- Fallible boolean equality result. -/
  | flag (res : Except CryptoHashError Bool)
  deriving Inhabited

/-- Well-formedness guard on the stateless `Unit` state for `CryptoHash.Raw`. -/
def rawStepWf (_ : Unit) : Bool := true

/-- Pure model of a single `CryptoHashFfiOpsM` digest call. -/
def ffiDigestRawModel (tag : UInt8) (data : ByteArray) : UInt32 × UInt64 × String × ByteArray :=
  if tag == 0 then
    (0, 0, "", sha256Bytes data)
  else if tag == 1 then
    (0, 0, "", sha512Bytes data)
  else
    (1, 0, "invalid algorithm tag", ByteArray.empty)

/-- Pure `CryptoHashFfiOpsM (StateM S)` behavior model parameterized over state `S`. -/
def modelStateFfiOps {S : Type} : CryptoHashFfiOpsM (StateM S) :=
  { digestRaw := fun tag data => pure (ffiDigestRawModel tag data)
    hmacSha256Raw := fun key msg => pure (0, 0, "", hmacSha256Bytes key msg)
    ctEqualRaw := fun a b => pure (a == b) }

/-- Execute one `FfiStepReq` against an arbitrary `CryptoHashFfiOpsM (StateM W)`. -/
def execFfiStep {W : Type} (ffi : CryptoHashFfiOpsM (StateM W)) : FfiStepReq → StateM W FfiStepOut
  | .digestRaw tag data => .shimBytes <$> ffi.digestRaw tag data
  | .hmacSha256Raw key msg => .shimBytes <$> ffi.hmacSha256Raw key msg
  | .ctEqualRaw a b => .flag <$> ffi.ctEqualRaw a b

/-- Allowed single-step transition relation for `CryptoHashFfiOpsM`. -/
def allowedFfiStep (s : Unit) (req : FfiStepReq) (out : FfiStepOut) (s' : Unit) : Prop :=
  s' = s ∧
    match req, out with
    | .digestRaw tag data, .shimBytes res => res = ffiDigestRawModel tag data
    | .hmacSha256Raw key msg, .shimBytes res => res = (0, 0, "", hmacSha256Bytes key msg)
    | .ctEqualRaw a b, .flag eq => eq = (a == b)
    | _, _ => False

/-- Execute one `PkgStepReq` against an arbitrary `RawCryptoHashOpsM (StateM W)`. -/
def execPkgStep {W : Type} (ops : RawCryptoHashOpsM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .digestRaw alg data => .bytes <$> ops.digestRaw alg data
  | .hmacSha256Raw key msg => .bytes <$> ops.hmacSha256Raw key msg
  | .ctEqualRaw a b => .flag <$> ops.ctEqualRaw a b

/-- Allowed single-step transition relation for `RawCryptoHashOpsM`. -/
def allowedPkgStep (s : Unit) (req : PkgStepReq) (out : PkgStepOut) (s' : Unit) : Prop :=
  s' = s ∧
    match req, out with
    | .digestRaw alg data, .bytes res => res = .ok (digestBytesModel alg data)
    | .hmacSha256Raw key msg, .bytes res => res = .ok (hmacSha256Bytes key msg)
    | .ctEqualRaw a b, .flag res => res = ctEqualRawModel a b
    | _, _ => False

end LeanSwe.CryptoHash.Raw.Model
