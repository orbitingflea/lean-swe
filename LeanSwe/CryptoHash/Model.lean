import LeanSwe.CryptoHash.Types
import LeanSwe.CryptoHash.Raw.Model

namespace LeanSwe.CryptoHash.Model

/-- Pure model of `LeanSwe.CryptoHash.hash`. -/
def hashModel (alg : HashAlg) (msg : ByteArray) : Except CryptoHashError Digest :=
  .ok { alg, bytes := Raw.Model.digestBytesModel alg msg }

/-- Pure model of `LeanSwe.CryptoHash.sha256`. -/
def sha256Model (msg : ByteArray) : Except CryptoHashError Digest :=
  hashModel .sha256 msg

/-- Pure model of `LeanSwe.CryptoHash.sha512`. -/
def sha512Model (msg : ByteArray) : Except CryptoHashError Digest :=
  hashModel .sha512 msg

/-- Pure model of `LeanSwe.CryptoHash.hmacSha256`. -/
def hmacSha256Model (key msg : ByteArray) : Except CryptoHashError Digest :=
  .ok { alg := .sha256, bytes := Raw.Model.hmacSha256Bytes key msg }

/-- Pure model of `LeanSwe.CryptoHash.verifyHmacSha256`. -/
def verifyHmacSha256Model (key msg : ByteArray) (expected : Digest) : Except CryptoHashError Bool :=
  if expected.alg != .sha256 then
    .error { kind := .invalidInput, message := "expected HMAC-SHA256 digest algorithm" }
  else if expected.bytes.size != 32 then
    .error { kind := .lengthMismatch, message := s!"HMAC-SHA256 length mismatch: expected 32 bytes, got {expected.bytes.size}" }
  else
    .ok (Raw.Model.hmacSha256Bytes key msg == expected.bytes)

/-- Convert a nibble `0..15` to its lowercase ASCII hexadecimal character. -/
def lowerHexDigitModel (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Parse an ASCII hexadecimal character (`0-9`, `a-f`, `A-F`) into a nibble `0..15`. -/
def hexCharToNibbleModel (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (10 + (c.toNat - 'a'.toNat)))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (10 + (c.toNat - 'A'.toNat)))
  else none

/-- Encode a single byte into big-endian high and low lowercase hexadecimal characters. -/
def byteToHexCharsModel (b : UInt8) : List Char :=
  [lowerHexDigitModel (b.toNat / 16), lowerHexDigitModel (b.toNat % 16)]

/-- Decode two ASCII hexadecimal characters (high nibble, low nibble) into a byte. -/
def hexCharsToByteModel (hi lo : Char) : Option UInt8 :=
  match hexCharToNibbleModel hi, hexCharToNibbleModel lo with
  | some h, some l => some (UInt8.ofNat (h.toNat * 16 + l.toNat))
  | _, _ => none

/-- Pure model of `LeanSwe.CryptoHash.toHex`. -/
def toHexModel (d : Digest) : String :=
  String.ofList (d.bytes.data.toList.flatMap byteToHexCharsModel)

/-- Tail-recursive hex pair decoder model. -/
def decodeHexPairsAccModel (accRev : List UInt8) : List Char → Option (List UInt8)
  | [] => some accRev.reverse
  | hi :: lo :: rest =>
    match hexCharsToByteModel hi lo with
    | some b => decodeHexPairsAccModel (b :: accRev) rest
    | none => none
  | _ => none

/-- Pure model of `LeanSwe.CryptoHash.fromHex`. -/
def fromHexModel (alg : HashAlg) (s : String) : Except CryptoHashError Digest :=
  match decodeHexPairsAccModel [] s.toList with
  | none =>
    .error { kind := .invalidHex, message := "hex string must have even length and contain only ASCII hex digits" }
  | some bs =>
    let ba := ByteArray.mk bs.toArray
    if ba.size != digestLen alg then
      .error { kind := .lengthMismatch, message := s!"expected {digestLen alg} digest bytes, got {ba.size}" }
    else
      .ok { alg, bytes := ba }

/-- Pure model of `LeanSwe.CryptoHash.ctEq`. -/
def ctEqModel (a b : ByteArray) : Except CryptoHashError Bool :=
  .ok (a == b)

/-- Pure `CryptoHashApiM Id` behavior model. -/
def modelApi : CryptoHashApiM Id :=
  { mapRawError := Raw.Model.mapRawErrorModel
    hash := hashModel
    sha256 := sha256Model
    sha512 := sha512Model
    hmacSha256 := hmacSha256Model
    verifyHmacSha256 := verifyHmacSha256Model
    toHex := toHexModel
    fromHex := fromHexModel
    ctEq := ctEqModel }

/-- Pure behavior model of `LeanSwe.CryptoHash.mapRawError`. -/
def mapRawErrorModel (err : CryptoHashRawError) : CryptoHashError :=
  Raw.Model.mapRawErrorModel err

/-- Request sum for raw `RawCryptoHashOpsM` transitions in `Core.RefinesStepFrom`. -/
inductive RawStepReq where
  /-- Normalize a raw error record. -/
  | mapRawError (err : CryptoHashRawError)
  /-- Compute raw digest bytes for `(alg, msg)`. -/
  | digestRaw (alg : HashAlg) (msg : ByteArray)
  /-- Compute raw 32-byte HMAC-SHA256 bytes for `(key, msg)`. -/
  | hmacSha256Raw (key msg : ByteArray)
  /-- Compare equal-length byte slices in constant time. -/
  | ctEqualRaw (a b : ByteArray)

/-- Output sum for raw `RawCryptoHashOpsM` transitions in `Core.RefinesStepFrom`. -/
inductive RawStepOut where
  /-- Result of `RawCryptoHashOpsM.mapRawError`. -/
  | mapped (err : CryptoHashError)
  /-- Result of `RawCryptoHashOpsM.digestRaw` or `hmacSha256Raw`. -/
  | bytes (res : Except CryptoHashError ByteArray)
  /-- Result of `RawCryptoHashOpsM.ctEqualRaw`. -/
  | eqRes (res : Except CryptoHashError Bool)

/-- Total well-formedness guard on `Unit` state for `Core.RefinesStepFrom`. -/
def rawStepWf (_ : Unit) : Bool := true

/-- Execute one `RawStepReq` against an arbitrary `RawCryptoHashOpsM (StateM W)`. -/
def execRawStep {W : Type} (raw : RawCryptoHashOpsM (StateM W)) : RawStepReq → StateM W RawStepOut
  | .mapRawError err => pure (.mapped (raw.mapRawError err))
  | .digestRaw alg msg => .bytes <$> raw.digestRaw alg msg
  | .hmacSha256Raw key msg => .bytes <$> raw.hmacSha256Raw key msg
  | .ctEqualRaw a b => .eqRes <$> raw.ctEqualRaw a b

/-- Allowed raw single-step relation over `Unit` state. -/
def allowedRawStep (s : Unit) (req : RawStepReq) (out : RawStepOut) (s' : Unit) : Prop :=
  s' = s ∧
    match req, out with
    | .mapRawError err, .mapped res => res = Raw.Model.mapRawErrorModel err
    | .digestRaw alg msg, .bytes res => res = .ok (Raw.Model.digestBytesModel alg msg)
    | .hmacSha256Raw key msg, .bytes res => res = .ok (Raw.Model.hmacSha256Bytes key msg)
    | .ctEqualRaw a b, .eqRes res => res = Raw.Model.ctEqualRawModel a b
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

/-- Output sum for effectful `CryptoHashApiM` transitions. -/
inductive PkgStepOut where
  /-- Digest result of `hash`, `sha256`, `sha512`, or `hmacSha256`. -/
  | digest (res : Except CryptoHashError Digest)
  /-- Boolean result of `verifyHmacSha256` or `ctEq`. -/
  | flag (res : Except CryptoHashError Bool)

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