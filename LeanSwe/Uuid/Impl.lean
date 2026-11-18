import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.Uuid.Types

namespace LeanSwe.Uuid.Internal

open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM)
open LeanSwe.Uuid (UuidErrorKind UuidError UuidRawError Uuid UuidApiM)

/-- Alias of `LeanSwe.Uuid.MAX_GETRANDOM_ATTEMPTS` (`32`). -/
abbrev MAX_GETRANDOM_ATTEMPTS : Nat := LeanSwe.Uuid.MAX_GETRANDOM_ATTEMPTS

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Convert a pure `UuidRawError` record into a normalized `UuidError` with kind `.entropyFailed` and a non-empty message. -/
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

/-- Map a Linux `Errno` returned by `TimeRand.getrandom` into a normalized `.entropyFailed` `UuidError`. -/
def mapErrnoToUuidError (e : Errno) : UuidError :=
  mapRawError (.osError e s!"getrandom failed with {Errno.name e} ({e})")

/-- Kernel-reducible `ByteArray` concatenation helper avoiding opaque `@[extern] ByteArray.copySlice` in proofs. -/
def appendBytes (a b : ByteArray) : ByteArray :=
  if a.size == 0 then b
  else ByteArray.mk (a.data.toList ++ b.data.toList).toArray

/-- Classify a single `getrandom` outcome when `need = 16 - acc.size` bytes remain: `.error err` aborts, `.ok (.inl full16)` finishes, and `.ok (.inr (nextAcc, nextLast))` continues. -/
def stepRandomBytes16 (need : Nat) (acc : ByteArray)
    (res : Except Errno ByteArray) :
    Except UuidError (Sum ByteArray (ByteArray × Option Errno)) :=
  match res with
  | .error e =>
    if e == Errno.EINTR then
      .ok (.inr (acc, some e))
    else
      .error (mapErrnoToUuidError e)
  | .ok chunk =>
    if chunk.size == 0 || decide (chunk.size > need) then
      .error (mapRawError (.shortRead (acc.size + chunk.size)
        s!"unexpected getrandom chunk length {chunk.size} (expected 1..{need})"))
    else
      let nextAcc := appendBytes acc chunk
      if nextAcc.size == 16 then
        .ok (.inl nextAcc)
      else
        .ok (.inr (nextAcc, none))

/-- Structurally bounded loop gathering exactly 16 random bytes from `sys.getrandom`, retrying `Errno.EINTR` and accumulating partial reads while failing immediately on non-`EINTR` errnos or invalid chunk sizes. -/
def gatherRandomBytes16 {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (fuel : Nat) (acc : ByteArray) (lastErrno? : Option Errno := none) :
    m (Except UuidError ByteArray) :=
  if acc.size == 16 then
    pure (.ok acc)
  else if decide (acc.size > 16) then
    pure (.error (mapRawError (.shortRead acc.size s!"entropy accumulator exceeded 16 bytes ({acc.size})")))
  else
    match fuel with
    | 0 =>
      match lastErrno? with
      | some e => pure (.error (mapErrnoToUuidError e))
      | none =>
        pure (.error (mapRawError (.shortRead acc.size
          s!"getrandom retry budget exhausted after {acc.size} of 16 bytes")))
    | fuel' + 1 => do
      let need : Nat := 16 - acc.size
      let r ← sys.getrandom (UInt32.ofNat need) {}
      match stepRandomBytes16 need acc r with
      | .error err => pure (.error err)
      | .ok (.inl doneBytes) => pure (.ok doneBytes)
      | .ok (.inr (nextAcc, nextLast)) => gatherRandomBytes16 sys fuel' nextAcc nextLast

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

/-- Construct a UUIDv4 from 16 raw random bytes, setting RFC 4122 version (`0x40`) and variant (`0x80`) bits. -/
def fromRandomBytes (bs : ByteArray) : Except UuidError Uuid :=
  if bs.size != 16 then
    .error { kind := .invalidLength, message := s!"expected 16 bytes for UUIDv4, got {bs.size}" }
  else
    let b6 := (bs[6]! &&& (0x0F : UInt8)) ||| (0x40 : UInt8)
    let b8 := (bs[8]! &&& (0x3F : UInt8)) ||| (0x80 : UInt8)
    .ok { bytes := (bs.set! 6 b6).set! 8 b8 }

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

/-- Format `Uuid` as canonical lowercase `8-4-4-4-12` (36 characters). -/
def toString (u : Uuid) : String :=
  let hex := formatHexList u.bytes.data.toList
  if u.bytes.size == 16 then String.ofList (insertHyphens hex)
  else String.ofList hex

/-- Format `Uuid` as compact lowercase 32-character hex. -/
def toHex (u : Uuid) : String :=
  String.ofList (formatHexList u.bytes.data.toList)

/-- Decode a list of hex character pairs into bytes, returning `none` if odd-length or any character is non-hex. -/
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

/-- Parse a strict canonical `8-4-4-4-12` UUIDv4 string. -/
def parse (s : String) : Except UuidError Uuid :=
  parseCanonicalChars s.toList

/-- Parse a compact 32-character hex UUIDv4 string. -/
def parseHex (s : String) : Except UuidError Uuid :=
  parseHexChars s.toList

/-- Return `true` iff `s` is a valid strict canonical `8-4-4-4-12` UUIDv4 string. -/
def isValid (s : String) : Bool :=
  (parse s).isOk

/-- Build the generic `UuidApiM m` bundle purely over an injected `TimeRandOpsM m` Linux syscall bundle. -/
def mkApi {m : Type → Type} [Monad m] (sys : TimeRandOpsM m) : UuidApiM m :=
  { mapRawError := mapRawError
    fromRandomBytes := fromRandomBytes
    toString := toString
    toHex := toHex
    parse := parse
    parseHex := parseHex
    isValid := isValid
    getUuid := do
      match ← gatherRandomBytes16 sys MAX_GETRANDOM_ATTEMPTS ByteArray.empty none with
      | .error err => return .error err
      | .ok bs => return fromRandomBytes bs }

/-- Alias of `mkApi` for uniformity across capability-parameterized packages. -/
abbrev mkApiM {m : Type → Type} [Monad m] (sys : TimeRandOpsM m) : UuidApiM m :=
  mkApi sys

end LeanSwe.Uuid.Internal
