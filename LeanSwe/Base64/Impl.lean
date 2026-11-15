import LeanSwe.Base64.Types

namespace LeanSwe.Base64.Internal

/-- Human-readable label prefix for each `Base64ErrorKind`. -/
def errorKindLabel : Base64ErrorKind → String
  | .invalidCharacter => "invalid base64 character"
  | .invalidLength => "invalid base64 length"
  | .invalidPadding => "invalid base64 padding"
  | .nonCanonicalEncoding => "non-canonical trailing base64 bits"

/-- Construct a `Base64Error` guaranteed to have a non-empty diagnostic message. -/
def makeError (kind : Base64ErrorKind) (offset : Nat) (detail : String) : Base64Error :=
  { kind := kind
  , offset := offset
  , message := errorKindLabel kind ++ " at offset " ++ toString offset ++ ": " ++ detail
  }

/-- Map a 6-bit sextet value (`0 ≤ s < 64`) to its Base64 character in `Alphabet`. -/
def encodeSextet (a : Alphabet) (s : Nat) : Char :=
  if s < 26 then Char.ofNat ('A'.toNat + s)
  else if s < 52 then Char.ofNat ('a'.toNat + (s - 26))
  else if s < 62 then Char.ofNat ('0'.toNat + (s - 52))
  else if s == 62 then
    match a with
    | .standard => '+'
    | .urlSafe => '-'
  else
    match a with
    | .standard => '/'
    | .urlSafe => '_'

/-- Decode a single character in `Alphabet` to its 6-bit value (`0..63`), or `none` if outside `Alphabet`. -/
def decodeChar? (a : Alphabet) (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else
    match a with
    | .standard =>
      if c == '+' then some 62
      else if c == '/' then some 63
      else none
    | .urlSafe =>
      if c == '-' then some 62
      else if c == '_' then some 63
      else none

/-- Predicate checking whether `c` belongs to the given Base64 `Alphabet` (excluding `'='`). -/
def isAlphabetChar (a : Alphabet) (c : Char) : Bool :=
  (decodeChar? a c).isSome

/-- Encode a list of bytes into Base64 characters in `Alphabet` with optional `'='` padding. -/
def encodeBytesList (a : Alphabet) (pad : Bool) : List UInt8 → List Char
  | [] => []
  | [b0] =>
    let s0 := b0.toNat >>> 2
    let s1 := (b0.toNat &&& 0x03) <<< 4
    let tail := if pad then ['=', '='] else []
    encodeSextet a s0 :: encodeSextet a s1 :: tail
  | [b0, b1] =>
    let s0 := b0.toNat >>> 2
    let s1 := ((b0.toNat &&& 0x03) <<< 4) ||| (b1.toNat >>> 4)
    let s2 := (b1.toNat &&& 0x0F) <<< 2
    let tail := if pad then ['='] else []
    encodeSextet a s0 :: encodeSextet a s1 :: encodeSextet a s2 :: tail
  | b0 :: b1 :: b2 :: rest =>
    let s0 := b0.toNat >>> 2
    let s1 := ((b0.toNat &&& 0x03) <<< 4) ||| (b1.toNat >>> 4)
    let s2 := ((b1.toNat &&& 0x0F) <<< 2) ||| (b2.toNat >>> 6)
    let s3 := b2.toNat &&& 0x3F
    encodeSextet a s0 :: encodeSextet a s1 :: encodeSextet a s2 :: encodeSextet a s3 ::
      encodeBytesList a pad rest

/-- Encode bytes using explicit `EncodeOptions`. -/
def encodeWith (opts : EncodeOptions) (bs : ByteArray) : String :=
  String.ofList (encodeBytesList opts.alphabet opts.pad bs.data.toList)

/-- Encode bytes using standard RFC 4648 §4 alphabet with `'='` padding. -/
def encode (bs : ByteArray) : String :=
  encodeWith { alphabet := .standard, pad := true } bs

/-- Encode bytes using URL-safe RFC 4648 §5 alphabet without `'='` padding. -/
def encodeUrl (bs : ByteArray) : String :=
  encodeWith { alphabet := .urlSafe, pad := false } bs

/-- Scan left-to-right for the earliest character not in `Alphabet` and not equal to `'='`. -/
def scanInvalidChar (a : Alphabet) (idx : Nat) : List Char → Option Nat
  | [] => none
  | c :: cs =>
    if isAlphabetChar a c || c == '=' then scanInvalidChar a (idx + 1) cs
    else some idx

/-- Scan left-to-right for the index of the earliest `'='` character, if any. -/
def findFirstEq (idx : Nat) : List Char → Option Nat
  | [] => none
  | c :: cs =>
    if c == '=' then some idx
    else findFirstEq (idx + 1) cs

/-- Decode validated alphabet-only Base64 characters (without `'='`) into bytes, enforcing canonical trailing bits when `strict = true`. -/
def decodeDataChars (a : Alphabet) (strict : Bool) (offset : Nat) :
    List Char → Except Base64Error (List UInt8)
  | [] => .ok []
  | [_] => .error (makeError .invalidLength offset "dangling 1-character quantum")
  | [c0, c1] =>
    match decodeChar? a c0, decodeChar? a c1 with
    | some s0, some s1 =>
      if strict && (s1 &&& 0x0F) ≠ 0 then
        .error (makeError .nonCanonicalEncoding (offset + 1) "non-zero trailing bits in 2-character quantum")
      else
        .ok [UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))]
    | none, _ => .error (makeError .invalidCharacter offset "unexpected character")
    | _, none => .error (makeError .invalidCharacter (offset + 1) "unexpected character")
  | [c0, c1, c2] =>
    match decodeChar? a c0, decodeChar? a c1, decodeChar? a c2 with
    | some s0, some s1, some s2 =>
      if strict && (s2 &&& 0x03) ≠ 0 then
        .error (makeError .nonCanonicalEncoding (offset + 2) "non-zero trailing bits in 3-character quantum")
      else
        let b0 := UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))
        let b1 := UInt8.ofNat (((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2))
        .ok [b0, b1]
    | none, _, _ => .error (makeError .invalidCharacter offset "unexpected character")
    | _, none, _ => .error (makeError .invalidCharacter (offset + 1) "unexpected character")
    | _, _, none => .error (makeError .invalidCharacter (offset + 2) "unexpected character")
  | c0 :: c1 :: c2 :: c3 :: rest =>
    match decodeChar? a c0, decodeChar? a c1, decodeChar? a c2, decodeChar? a c3 with
    | some s0, some s1, some s2, some s3 =>
      let b0 := UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))
      let b1 := UInt8.ofNat (((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2))
      let b2 := UInt8.ofNat (((s2 &&& 0x03) <<< 6) ||| s3)
      match decodeDataChars a strict (offset + 4) rest with
      | .ok bs => .ok (b0 :: b1 :: b2 :: bs)
      | .error e => .error e
    | none, _, _, _ => .error (makeError .invalidCharacter offset "unexpected character")
    | _, none, _, _ => .error (makeError .invalidCharacter (offset + 1) "unexpected character")
    | _, _, none, _ => .error (makeError .invalidCharacter (offset + 2) "unexpected character")
    | _, _, _, none => .error (makeError .invalidCharacter (offset + 3) "unexpected character")

/-- Decode Base64 character list using explicit `DecodeOptions`. -/
def decodeChars (opts : DecodeOptions) (chars : List Char) : Except Base64Error (List UInt8) :=
  match scanInvalidChar opts.alphabet 0 chars with
  | some idx => .error (makeError .invalidCharacter idx "character outside base64 alphabet")
  | none =>
    let n := chars.length
    match findFirstEq 0 chars with
    | some p =>
      if opts.padding = .forbidden then
        .error (makeError .invalidPadding p "padding '=' is forbidden")
      else if !(chars.drop p).all (· == '=') then
        .error (makeError .invalidPadding p "non-trailing padding '='")
      else if n % 4 ≠ 0 then
        .error (makeError .invalidPadding p "padded base64 length must be a multiple of 4")
      else if n - p > 2 then
        .error (makeError .invalidPadding p "too many '=' padding characters")
      else
        decodeDataChars opts.alphabet opts.strictCanonicalBits 0 (chars.take p)
    | none =>
      if n % 4 == 1 then
        .error (makeError .invalidLength (n - 1) "base64 length modulo 4 cannot be 1")
      else if opts.padding = .required && n % 4 ≠ 0 then
        .error (makeError .invalidPadding n "missing required '=' padding")
      else
        decodeDataChars opts.alphabet opts.strictCanonicalBits 0 chars

/-- Decode Base64 text using explicit `DecodeOptions`. -/
def decodeWith (opts : DecodeOptions) (s : String) : Except Base64Error ByteArray :=
  (decodeChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray)

/-- Decode standard RFC 4648 §4 Base64 text requiring `'='` padding and canonical trailing bits. -/
def decode (s : String) : Except Base64Error ByteArray :=
  decodeWith { alphabet := .standard, padding := .required, strictCanonicalBits := true } s

/-- Decode URL-safe RFC 4648 §5 Base64 text with optional padding and canonical trailing bits. -/
def decodeUrl (s : String) : Except Base64Error ByteArray :=
  decodeWith { alphabet := .urlSafe, padding := .optional, strictCanonicalBits := true } s

/-- Default `Base64Api` bundling the concrete `LeanSwe.Base64` pure operations. -/
def defaultApi : Base64Api :=
  { encode := encode
  , encodeUrl := encodeUrl
  , encodeWith := encodeWith
  , decode := decode
  , decodeUrl := decodeUrl
  , decodeWith := decodeWith
  }

end LeanSwe.Base64.Internal
