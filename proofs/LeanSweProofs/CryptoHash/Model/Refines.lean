import LeanSwe.CryptoHash.Types
import LeanSweProofs.CryptoHash.Model

namespace LeanSwe.CryptoHash.Model

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

/-- Well-formedness guard on the stateless `Unit` state for `Core.ObeysStepFrom`. -/
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

/-- Request sum covering all effectful `CryptoHashApiM` operations. -/
inductive PkgStepReq where
  /-- `CryptoHashApiM.hash` request. -/
  | hash (alg : HashAlg) (msg : ByteArray)
  /-- `CryptoHashApiM.sha256` request. -/
  | sha256 (msg : ByteArray)
  /-- `CryptoHashApiM.sha512` request. -/
  | sha512 (msg : ByteArray)
  /-- `CryptoHashApiM.hmacSha256` request. -/
  | hmacSha256 (key msg : ByteArray)
  /-- `CryptoHashApiM.verifyHmacSha256` request. -/
  | verifyHmacSha256 (key msg : ByteArray) (expected : Digest)
  /-- `CryptoHashApiM.ctEq` request. -/
  | ctEq (a b : ByteArray)
  deriving BEq, DecidableEq, Inhabited

/-- Output sum for effectful `CryptoHashApiM` transitions. -/
inductive PkgStepOut where
  /-- Digest result of `hash`, `sha256`, `sha512`, or `hmacSha256`. -/
  | digest (res : Except CryptoHashError Digest)
  /-- Boolean result of `verifyHmacSha256` or `ctEq`. -/
  | flag (res : Except CryptoHashError Bool)
  deriving Inhabited

/-- Execute one `PkgStepReq` against a `CryptoHashApiM (StateM W)` bundle. -/
def execPkgStep {W : Type} (api : CryptoHashApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .hash alg msg => .digest <$> api.hash alg msg
  | .sha256 msg => .digest <$> api.sha256 msg
  | .sha512 msg => .digest <$> api.sha512 msg
  | .hmacSha256 key msg => .digest <$> api.hmacSha256 key msg
  | .verifyHmacSha256 key msg expected => .flag <$> api.verifyHmacSha256 key msg expected
  | .ctEq a b => .flag <$> api.ctEq a b

/-- Allowed package-level single-step relation against `LeanSwe.CryptoHash.Model`. -/
def allowedPkgStep (s : Unit) (req : PkgStepReq) (out : PkgStepOut) (s' : Unit) : Prop :=
  s' = s ∧
    match req, out with
    | .hash alg msg, .digest res => res = hashModel alg msg
    | .sha256 msg, .digest res => res = sha256Model msg
    | .sha512 msg, .digest res => res = sha512Model msg
    | .hmacSha256 key msg, .digest res => res = hmacSha256Model key msg
    | .verifyHmacSha256 key msg expected, .flag res => res = verifyHmacSha256Model key msg expected
    | .ctEq a b, .flag res => res = ctEqModel a b
    | _, _ => False

end LeanSwe.CryptoHash.Model
