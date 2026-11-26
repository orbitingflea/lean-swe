import LeanSwe.Uuid.Types

/-!
# Pure Behavior Model for `LeanSwe.Uuid`

Defines the pure RFC 4122 UUIDv4 codec specification (`mapRawError`,
`fromRandomBytes`, `toString`, `toHex`, `parse`, `parseHex`, `isValid`) and the
caller-facing stateful step contract (`UuidModelState`, `pkgWf`, `PkgStepReq`,
`PkgStepOut`, `execPkgStep`, `allowedPkgStep`).
-/

namespace LeanSwe.Uuid.Model

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Pure behavior model of `LeanSwe.Uuid.mapRawError`. -/
def mapRawError : UuidRawError → UuidError
  | .osError code detail =>
    { kind := .entropyFailed
      errnoCode := some code
      message := nonEmptyMsg s!"os entropy error {code}" detail }
  | .shortRead gotBytes detail =>
    { kind := .entropyFailed
      errnoCode := none
      message := nonEmptyMsg s!"entropy short read: expected 16 bytes, got {gotBytes}" detail }
  | .userError detail =>
    { kind := .entropyFailed
      errnoCode := none
      message := nonEmptyMsg "os entropy error" detail }

/-- Return `true` iff `u` is a 16-byte RFC 4122 version 4 UUID. -/
def isValidV4Uuid (u : Uuid) : Bool :=
  u.bytes.size == 16 &&
  (u.bytes[6]! &&& (0xF0 : UInt8)) == (0x40 : UInt8) &&
  (u.bytes[8]! &&& (0xC0 : UInt8)) == (0x80 : UInt8)

/-- Pure behavior model of `LeanSwe.Uuid.fromRandomBytes`. -/
def fromRandomBytes (bs : ByteArray) : Except UuidError Uuid :=
  if bs.size != 16 then
    .error { kind := .invalidLength, message := s!"expected 16 bytes for UUIDv4, got {bs.size}" }
  else
    let b6 := (bs[6]! &&& (0x0F : UInt8)) ||| (0x40 : UInt8)
    let b8 := (bs[8]! &&& (0x3F : UInt8)) ||| (0x80 : UInt8)
    .ok { bytes := (bs.set! 6 b6).set! 8 b8 }

/-- Convert a nibble `0..15` to its lowercase ASCII hex character. -/
def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Parse an ASCII hex character (`0-9`, `a-f`, `A-F`) into a nibble `0..15`. -/
def hexCharToNibble (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (10 + (c.toNat - 'a'.toNat)))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (10 + (c.toNat - 'A'.toNat)))
  else none

/-- Encode a single byte into big-endian high and low lowercase hex characters. -/
def byteToHexChars (b : UInt8) : List Char :=
  [lowerHexDigit (b.toNat / 16), lowerHexDigit (b.toNat % 16)]

/-- Decode two ASCII hex characters (high nibble, low nibble) into a byte. -/
def hexCharsToByte (hi lo : Char) : Option UInt8 :=
  match hexCharToNibble hi, hexCharToNibble lo with
  | some h, some l => some (UInt8.ofNat (h.toNat * 16 + l.toNat))
  | _, _ => none

/-- Format a list of bytes as compact lowercase hex characters. -/
def formatHexList (bs : List UInt8) : List Char :=
  bs.flatMap byteToHexChars

/-- Insert canonical `8-4-4-4-12` hyphens into a 32-character hex list. -/
def insertHyphens (cs : List Char) : List Char :=
  cs.take 8 ++ ['-'] ++
  (cs.drop 8).take 4 ++ ['-'] ++
  (cs.drop 12).take 4 ++ ['-'] ++
  (cs.drop 16).take 4 ++ ['-'] ++
  cs.drop 20

/-- Pure behavior model of `LeanSwe.Uuid.toString`. -/
def toString (u : Uuid) : String :=
  let hex := formatHexList u.bytes.data.toList
  if u.bytes.size == 16 then String.ofList (insertHyphens hex)
  else String.ofList hex

/-- Pure behavior model of `LeanSwe.Uuid.toHex`. -/
def toHex (u : Uuid) : String :=
  String.ofList (formatHexList u.bytes.data.toList)

/-- Decode a list of hex character pairs into bytes, returning `none` on odd length or non-hex input. -/
def decodeHexPairs : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest =>
    match hexCharsToByte hi lo, decodeHexPairs rest with
    | some b, some bs => some (b :: bs)
    | _, _ => none
  | _ => none

/-- Validate 16 decoded bytes for RFC 4122 version 4 and variant `10xx` bits. -/
def validateV4BytesList (bs : List UInt8) : Except UuidError Uuid :=
  let ba := ByteArray.mk bs.toArray
  if ba.size != 16 then
    .error { kind := .invalidFormat, message := s!"expected 16 bytes for UUID, got {ba.size}" }
  else if (ba[6]! &&& (0xF0 : UInt8)) != (0x40 : UInt8) then
    .error { kind := .invalidVersion, message := "UUID version nibble must be 4" }
  else if (ba[8]! &&& (0xC0 : UInt8)) != (0x80 : UInt8) then
    .error { kind := .invalidVersion, message := "UUID variant bits must be RFC 4122 (10xx)" }
  else
    .ok { bytes := ba }

/-- Parse 32 ASCII hex characters into a validated RFC 4122 UUIDv4. -/
def parseHexChars (cs : List Char) : Except UuidError Uuid :=
  if cs.length != 32 then
    .error { kind := .invalidFormat, message := s!"expected 32 hex characters for UUID, got {cs.length}" }
  else
    match decodeHexPairs cs with
    | none => .error { kind := .invalidFormat, message := "UUID hex string contains non-hex characters" }
    | some bs => validateV4BytesList bs

/-- Strip canonical hyphens at indices 8, 13, 18, 23 from a 36-character list. -/
def stripCanonicalHyphens (cs : List Char) : Option (List Char) :=
  if cs.length != 36 then
    none
  else if cs[8]? != some '-' || cs[13]? != some '-' || cs[18]? != some '-' || cs[23]? != some '-' then
    none
  else
    some (cs.take 8 ++ (cs.drop 9).take 4 ++ (cs.drop 14).take 4 ++ (cs.drop 19).take 4 ++ cs.drop 24)

/-- Parse a strict canonical `8-4-4-4-12` character list into a validated RFC 4122 UUIDv4. -/
def parseCanonicalChars (cs : List Char) : Except UuidError Uuid :=
  if cs.length != 36 then
    .error { kind := .invalidFormat, message := s!"expected 36 characters for canonical UUID, got {cs.length}" }
  else
    match stripCanonicalHyphens cs with
    | none => .error { kind := .invalidFormat, message := "UUID must use canonical 8-4-4-4-12 hyphen separators" }
    | some hex => parseHexChars hex

/-- Pure behavior model of `LeanSwe.Uuid.parse`. -/
def parse (s : String) : Except UuidError Uuid :=
  parseCanonicalChars s.toList

/-- Pure behavior model of `LeanSwe.Uuid.parseHex`. -/
def parseHex (s : String) : Except UuidError Uuid :=
  parseHexChars s.toList

/-- Pure behavior model of `LeanSwe.Uuid.isValid`. -/
def isValid (s : String) : Bool :=
  (parse s).isOk

/-- Total number of distinct RFC 4122 version 4 UUID values (`2 ^ 122`). -/
def maxValidV4Uuids : Nat := 2 ^ 122

/-- Caller-facing abstract state for `LeanSwe.Uuid`, tracking the list of already-issued UUIDs. -/
structure UuidModelState where
  /-- UUIDs already issued in this execution; future `getUuid` calls must never repeat any entry. -/
  seen : List Uuid := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Well-formedness guard on `UuidModelState`: at least one unseen RFC 4122 v4 UUID remains available. -/
def pkgWf (s : UuidModelState) : Bool :=
  decide (s.seen.length < maxValidV4Uuids)

/-- Public effectful request sum for `UuidApiM` single-step refinement. -/
inductive PkgStepReq where
  /-- Generate a fresh RFC 4122 UUIDv4 via `UuidApiM.getUuid`. -/
  | getUuid
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Public effectful output sum for `UuidApiM` single-step refinement. -/
inductive PkgStepOut where
  /-- Outcome of `UuidApiM.getUuid`. -/
  | getUuid (res : Except UuidError Uuid)
  deriving Repr, Inhabited

/-- Execute one `PkgStepReq` against an arbitrary `UuidApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : UuidApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .getUuid => .getUuid <$> api.getUuid

/-- Allowed `UuidApiM` single-step relation over `UuidModelState`.
    On a healthy machine, `getUuid` must succeed with a valid RFC 4122 v4 UUID
    absent from `s.seen`, and record it at the head of `s'.seen`. -/
def allowedPkgStep (s : UuidModelState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : UuidModelState) : Prop :=
  match req, out with
  | .getUuid, .getUuid (.ok u) =>
    isValidV4Uuid u = true ∧
    u ∉ s.seen ∧
    s'.seen = u :: s.seen
  | .getUuid, .getUuid (.error _) => False

end LeanSwe.Uuid.Model
