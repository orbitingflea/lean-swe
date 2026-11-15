import LeanSwe.Base64.Types

namespace LeanSwe.Base64.Model

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

/-- Pure RFC 4648 encoding specification over `ByteArray`. -/
def encodeModel (opts : EncodeOptions) (bs : ByteArray) : String :=
  String.ofList (encodeBytesList opts.alphabet opts.pad bs.data.toList)

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
    List Char → Except (Base64ErrorKind × Nat) (List UInt8)
  | [] => .ok []
  | [_] => .error (.invalidLength, offset)
  | [c0, c1] =>
    match decodeChar? a c0, decodeChar? a c1 with
    | some s0, some s1 =>
      if strict && (s1 &&& 0x0F) ≠ 0 then
        .error (.nonCanonicalEncoding, offset + 1)
      else
        .ok [UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))]
    | none, _ => .error (.invalidCharacter, offset)
    | _, none => .error (.invalidCharacter, offset + 1)
  | [c0, c1, c2] =>
    match decodeChar? a c0, decodeChar? a c1, decodeChar? a c2 with
    | some s0, some s1, some s2 =>
      if strict && (s2 &&& 0x03) ≠ 0 then
        .error (.nonCanonicalEncoding, offset + 2)
      else
        let b0 := UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))
        let b1 := UInt8.ofNat (((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2))
        .ok [b0, b1]
    | none, _, _ => .error (.invalidCharacter, offset)
    | _, none, _ => .error (.invalidCharacter, offset + 1)
    | _, _, none => .error (.invalidCharacter, offset + 2)
  | c0 :: c1 :: c2 :: c3 :: rest =>
    match decodeChar? a c0, decodeChar? a c1, decodeChar? a c2, decodeChar? a c3 with
    | some s0, some s1, some s2, some s3 =>
      let b0 := UInt8.ofNat ((s0 <<< 2) ||| (s1 >>> 4))
      let b1 := UInt8.ofNat (((s1 &&& 0x0F) <<< 4) ||| (s2 >>> 2))
      let b2 := UInt8.ofNat (((s2 &&& 0x03) <<< 6) ||| s3)
      match decodeDataChars a strict (offset + 4) rest with
      | .ok bs => .ok (b0 :: b1 :: b2 :: bs)
      | .error e => .error e
    | none, _, _, _ => .error (.invalidCharacter, offset)
    | _, none, _, _ => .error (.invalidCharacter, offset + 1)
    | _, _, none, _ => .error (.invalidCharacter, offset + 2)
    | _, _, _, none => .error (.invalidCharacter, offset + 3)

/-- Pure RFC 4648 decoding specification over `List Char` with deterministic error precedence and offset. -/
def decodeModelChars (opts : DecodeOptions) (chars : List Char) :
    Except (Base64ErrorKind × Nat) (List UInt8) :=
  match scanInvalidChar opts.alphabet 0 chars with
  | some idx => .error (.invalidCharacter, idx)
  | none =>
    let n := chars.length
    match findFirstEq 0 chars with
    | some p =>
      if opts.padding = .forbidden then
        .error (.invalidPadding, p)
      else if !(chars.drop p).all (· == '=') then
        .error (.invalidPadding, p)
      else if n % 4 ≠ 0 then
        .error (.invalidPadding, p)
      else if n - p > 2 then
        .error (.invalidPadding, p)
      else
        decodeDataChars opts.alphabet opts.strictCanonicalBits 0 (chars.take p)
    | none =>
      if n % 4 == 1 then
        .error (.invalidLength, n - 1)
      else if opts.padding = .required && n % 4 ≠ 0 then
        .error (.invalidPadding, n)
      else
        decodeDataChars opts.alphabet opts.strictCanonicalBits 0 chars

/-- Pure RFC 4648 decoding specification over `String`. -/
def decodeModel (opts : DecodeOptions) (s : String) :
    Except (Base64ErrorKind × Nat) ByteArray :=
  (decodeModelChars opts s.toList).map (fun bs => ByteArray.mk bs.toArray)

/-- Predicate asserting that `s` is a valid Base64 encoding under `opts`. -/
def ValidEncoded (opts : DecodeOptions) (s : String) : Prop :=
  (decodeModel opts s).isOk = true

/-- Structural characterization of `ValidEncoded` for a character list under `DecodeOptions`. -/
def ValidEncodedChars (opts : DecodeOptions) (chars : List Char) : Prop :=
  scanInvalidChar opts.alphabet 0 chars = none ∧
  match findFirstEq 0 chars with
  | some p =>
    opts.padding ≠ .forbidden ∧
    (chars.drop p).all (· == '=') = true ∧
    chars.length % 4 = 0 ∧
    chars.length - p ≤ 2 ∧
    (decodeDataChars opts.alphabet opts.strictCanonicalBits 0 (chars.take p)).isOk = true
  | none =>
    chars.length % 4 ≠ 1 ∧
    (opts.padding ≠ .required ∨ chars.length % 4 = 0) ∧
    (decodeDataChars opts.alphabet opts.strictCanonicalBits 0 chars).isOk = true

/-- `ValidEncoded` holds iff `decodeModel` returns `.ok` for some `ByteArray`. -/
theorem validEncoded_iff_exists (opts : DecodeOptions) (s : String) :
    ValidEncoded opts s ↔ ∃ bs, decodeModel opts s = .ok bs := by
  unfold ValidEncoded
  cases h : decodeModel opts s with
  | ok bs => exact ⟨fun _ => ⟨bs, rfl⟩, fun _ => rfl⟩
  | error e =>
    constructor
    · intro hOk; simp [Except.isOk, Except.toBool] at hOk
    · rintro ⟨bs, hEq⟩; cases hEq

/-- Standard `encode` default option record. -/
def defaultEncodeOptions : EncodeOptions :=
  { alphabet := .standard, pad := true }

/-- URL-safe `encodeUrl` default option record. -/
def urlEncodeOptions : EncodeOptions :=
  { alphabet := .urlSafe, pad := false }

/-- Standard `decode` default option record. -/
def defaultDecodeOptions : DecodeOptions :=
  { alphabet := .standard, padding := .required, strictCanonicalBits := true }

/-- URL-safe `decodeUrl` default option record. -/
def urlDecodeOptions : DecodeOptions :=
  { alphabet := .urlSafe, padding := .optional, strictCanonicalBits := true }

/-- Expected output length of `encodeWith opts bs`. -/
def expectedEncodedLength (opts : EncodeOptions) (byteLen : Nat) : Nat :=
  if opts.pad then ((byteLen + 2) / 3) * 4 else (byteLen * 4 + 2) / 3

/-- Expected trailing `'='` padding character count of `encodeWith opts bs`. -/
def expectedPaddingCount (opts : EncodeOptions) (byteLen : Nat) : Nat :=
  if opts.pad then (3 - byteLen % 3) % 3 else 0

end LeanSwe.Base64.Model
