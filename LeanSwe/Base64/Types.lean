namespace LeanSwe.Base64

/-- Base64 alphabet variant defined by RFC 4648. -/
inductive Alphabet where
  /-- Standard RFC 4648 §4 alphabet using `'+'` (62) and `'/'` (63). -/
  | standard
  /-- URL-safe and filename-safe RFC 4648 §5 alphabet using `'-'` (62) and `'_'` (63). -/
  | urlSafe
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Policy governing trailing `'='` padding characters during Base64 decoding. -/
inductive PaddingMode where
  /-- Trailing `'='` padding is mandatory whenever input byte length is not a multiple of 3. -/
  | required
  /-- Trailing `'='` padding may be either present (4-char aligned) or omitted. -/
  | optional
  /-- Trailing `'='` padding characters are forbidden. -/
  | forbidden
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Configuration options for Base64 encoding. -/
structure EncodeOptions where
  /-- Target Base64 alphabet (`standard` or `urlSafe`). -/
  alphabet : Alphabet := .standard
  /-- Whether to emit trailing `'='` padding characters to align output length to a multiple of 4. -/
  pad : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Configuration options for Base64 decoding. -/
structure DecodeOptions where
  /-- Expected Base64 alphabet (`standard` or `urlSafe`). -/
  alphabet : Alphabet := .standard
  /-- Padding policy enforced on trailing `'='` characters. -/
  padding : PaddingMode := .optional
  /-- Whether RFC 4648 §3.5 zero trailing unused pad bits are enforced on final 2- or 3-sextet quanta. -/
  strictCanonicalBits : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Classification of Base64 decoding failures. -/
inductive Base64ErrorKind where
  /-- Input contained a character outside the active alphabet and not equal to `'='`. -/
  | invalidCharacter
  /-- Unpadded data length had remainder 1 modulo 4, which cannot represent integral bytes. -/
  | invalidLength
  /-- Padding `'='` placement, count, or presence violated the configured `PaddingMode` or 4-char alignment. -/
  | invalidPadding
  /-- Unused low bits in a final 2- or 3-sextet quantum were non-zero under `strictCanonicalBits`. -/
  | nonCanonicalEncoding
  deriving Repr, BEq, DecidableEq

/-- Typed error returned by `LeanSwe.Base64` decoding operations. -/
structure Base64Error where
  /-- Machine-checkable error category. -/
  kind : Base64ErrorKind
  /-- Zero-based `Char` index into `s.toList` where the error was detected. -/
  offset : Nat
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq

/-- Public pure operations exported by `LeanSwe.Base64`. -/
structure Base64Api where
  /-- Encode bytes using standard RFC 4648 §4 alphabet with `'='` padding. -/
  encode : ByteArray → String
  /-- Encode bytes using URL-safe RFC 4648 §5 alphabet without `'='` padding. -/
  encodeUrl : ByteArray → String
  /-- Encode bytes using explicit `EncodeOptions`. -/
  encodeWith : EncodeOptions → ByteArray → String
  /-- Decode standard RFC 4648 §4 Base64 text requiring `'='` padding and canonical trailing bits. -/
  decode : String → Except Base64Error ByteArray
  /-- Decode URL-safe RFC 4648 §5 Base64 text with optional padding and canonical trailing bits. -/
  decodeUrl : String → Except Base64Error ByteArray
  /-- Decode Base64 text using explicit `DecodeOptions`. -/
  decodeWith : DecodeOptions → String → Except Base64Error ByteArray

end LeanSwe.Base64
