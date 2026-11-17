import Core.NondetTest
import LeanSwe.Uuid.Types

namespace LeanSwe.Uuid

open Core (NondetTest)
open Core.NondetTest

private def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def isHexChar (c : Char) : Bool :=
  isLowerHexChar c || ('A' ≤ c && c ≤ 'F')

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def mockCounterRawOps : RawUuidOpsM (StateM MockRngState) :=
  { mapRawError := fun
      | .osError code _ => { kind := .entropyFailed, errnoCode := some code, message := "mock os error" }
      | .shortRead _ _ => { kind := .entropyFailed, message := "mock short read" }
      | .userError _ => { kind := .entropyFailed, message := "mock entropy error" }
    randomBytes16 := do
      let s ← get
      match s.failWith with
      | some err =>
        set { s with draws := s.draws + 1 }
        return .error err
      | none =>
        let c := s.counter
        set { s with counter := c + 1, draws := s.draws + 1 }
        let bs := ByteArray.mk #[
          UInt8.ofNat (c % 256),
          UInt8.ofNat ((c / 256) % 256),
          UInt8.ofNat ((c / 65536) % 256),
          UInt8.ofNat ((c / 16777216) % 256),
          0x11, 0x22, 0x03, 0x44,
          0x05, 0x66, 0x77, 0x88,
          0x99, 0xaa, 0xbb, 0xcc
        ]
        return .ok bs }

/-- Every error returned by `api.mapRawError` has kind `.entropyFailed` and a non-empty diagnostic message, preserving `errno` on `.osError`. -/
def test_uuid_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let raw ← nondet UuidRawError
  let err := api.mapRawError raw
  NondetTest.assert (err.kind = .entropyFailed ∧ err.message ≠ "")
  match raw with
  | .osError code _ => NondetTest.assert (err.errnoCode = some code)
  | .shortRead _ _ => NondetTest.assert True
  | .userError _ => NondetTest.assert True

/-- `api.fromRandomBytes` accepts any 16-byte input, enforces RFC 4122 v4 version (`0x40`) and variant (`0x80`) bits, and preserves all remaining bits verbatim. -/
def test_uuid_fromRandomBytes_validLen_setsV4BitsAndPreservesPayload
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  match api.fromRandomBytes bs with
  | .error _ => NondetTest.assert False
  | .ok u =>
    NondetTest.assert (u.bytes.size = 16)
    NondetTest.assert ((u.bytes[6]! &&& (0xF0 : UInt8)) = (0x40 : UInt8))
    NondetTest.assert ((u.bytes[8]! &&& (0xC0 : UInt8)) = (0x80 : UInt8))
    NondetTest.assert ((u.bytes[6]! &&& (0x0F : UInt8)) = (bs[6]! &&& (0x0F : UInt8)))
    NondetTest.assert ((u.bytes[8]! &&& (0x3F : UInt8)) = (bs[8]! &&& (0x3F : UInt8)))
    let i ← nondet Nat
    assume (i < 16 ∧ i ≠ 6 ∧ i ≠ 8)
    NondetTest.assert (u.bytes[i]! = bs[i]!)

/-- `api.fromRandomBytes` rejects byte arrays whose length is not 16 with `.invalidLength` and a non-empty message. -/
def test_uuid_fromRandomBytes_invalidLen_returnsError
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size ≠ 16)
  match api.fromRandomBytes bs with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidLength ∧ e.message ≠ "")

/-- `api.toString` emits canonical lowercase `8-4-4-4-12` (36 chars) with v4 version/variant nibbles and round-trips through `api.parse` and `api.isValid`. -/
def test_uuid_toString_formatAndRoundTrip
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  match api.fromRandomBytes bs with
  | .error _ => assume False
  | .ok u =>
    let s := api.toString u
    NondetTest.assert (s.length = 36)
    NondetTest.assert (s.toList[8]? = some '-' ∧ s.toList[13]? = some '-' ∧ s.toList[18]? = some '-' ∧ s.toList[23]? = some '-')
    NondetTest.assert (s.toList.all (fun c => c == '-' || isLowerHexChar c) = true)
    NondetTest.assert (s.toList[14]? = some '4')
    NondetTest.assert (s.toList[19]? = some '8' ∨ s.toList[19]? = some '9' ∨ s.toList[19]? = some 'a' ∨ s.toList[19]? = some 'b')
    NondetTest.assert (api.parse s = .ok u)
    NondetTest.assert (api.isValid s = true)

/-- `api.toHex` emits 32 lowercase hex chars matching `api.toString` without hyphens, round-trips through `api.parseHex`, and is rejected by strict canonical `api.isValid`. -/
def test_uuid_toHex_formatAndRoundTrip
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  match api.fromRandomBytes bs with
  | .error _ => assume False
  | .ok u =>
    let h := api.toHex u
    let s := api.toString u
    NondetTest.assert (h.length = 32)
    NondetTest.assert (h.toList.all isLowerHexChar = true)
    NondetTest.assert (h.toList = s.toList.filter (fun c => c != '-'))
    NondetTest.assert (api.parseHex h = .ok u)
    NondetTest.assert (api.isValid h = false)
    match api.parse h with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "")

/-- `api.toHex` encodes the 16 UUID bytes in RFC 4122 big-endian byte and high/low nibble order. -/
def test_uuid_toHex_bigEndianNibbleOrder
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  match api.fromRandomBytes bs with
  | .error _ => assume False
  | .ok u =>
    let cs := (api.toHex u).toList
    let i ← nondet Nat
    assume (i < 16)
    let b := u.bytes[i]!.toNat
    NondetTest.assert (cs[2 * i]? = some (lowerHexDigit (b / 16)))
    NondetTest.assert (cs[2 * i + 1]? = some (lowerHexDigit (b % 16)))

/-- `api.parse` and `api.parseHex` accept uppercase hex input and recover the exact `Uuid`. -/
def test_uuid_parse_acceptsUppercaseHex
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  match api.fromRandomBytes bs with
  | .error _ => assume False
  | .ok u =>
    let upperStr := String.ofList ((api.toString u).toList.map Char.toUpper)
    let upperHex := String.ofList ((api.toHex u).toList.map Char.toUpper)
    NondetTest.assert (api.parse upperStr = .ok u)
    NondetTest.assert (api.isValid upperStr = true)
    NondetTest.assert (api.parseHex upperHex = .ok u)

/-- Every accepted `api.parse s = .ok u` yields valid 16-byte v4 bits, `api.isValid s = true`, and lowercased canonical `api.toString u`. -/
def test_uuid_parse_acceptedImpliesV4AndNormalizedRoundTrip
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let s ← nondet String
  match api.parse s with
  | .error e => NondetTest.assert (e.message ≠ "" ∧ api.isValid s = false)
  | .ok u =>
    NondetTest.assert (api.isValid s = true)
    NondetTest.assert (u.bytes.size = 16)
    NondetTest.assert ((u.bytes[6]! &&& (0xF0 : UInt8)) = (0x40 : UInt8))
    NondetTest.assert ((u.bytes[8]! &&& (0xC0 : UInt8)) = (0x80 : UInt8))
    NondetTest.assert ((api.toString u).toList = s.toList.map Char.toLower)

/-- Every accepted `api.parseHex s = .ok u` yields valid 16-byte v4 bits and lowercased compact `api.toHex u`. -/
def test_uuid_parseHex_acceptedImpliesV4AndNormalizedRoundTrip
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let s ← nondet String
  match api.parseHex s with
  | .error e => NondetTest.assert (e.message ≠ "")
  | .ok u =>
    NondetTest.assert (u.bytes.size = 16)
    NondetTest.assert ((u.bytes[6]! &&& (0xF0 : UInt8)) = (0x40 : UInt8))
    NondetTest.assert ((u.bytes[8]! &&& (0xC0 : UInt8)) = (0x80 : UInt8))
    NondetTest.assert ((api.toHex u).toList = s.toList.map Char.toLower)

/-- `api.parse` rejects any string whose length is not 36 with `.invalidFormat` and `api.isValid s = false`. -/
def test_uuid_parse_rejectsInvalidLength
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let s ← nondet String
  assume (s.length ≠ 36)
  match api.parse s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "" ∧ api.isValid s = false)

/-- `api.parse` rejects any 36-char string with a non-hex character in a hex position. -/
def test_uuid_parse_rejectsNonHexChar
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let s ← nondet String
  assume (s.length = 36)
  let idx ← nondet Nat
  assume (idx < 36 ∧ idx ≠ 8 ∧ idx ≠ 13 ∧ idx ≠ 18 ∧ idx ≠ 23)
  assume (isHexChar s.toList[idx]! = false)
  match api.parse s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "" ∧ api.isValid s = false)

/-- `api.parse` rejects any 36-char string missing a hyphen at index 8, 13, 18, or 23. -/
def test_uuid_parse_rejectsMissingHyphen
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let s ← nondet String
  assume (s.length = 36)
  assume (s.toList[8]? ≠ some '-' ∨ s.toList[13]? ≠ some '-' ∨ s.toList[18]? ≠ some '-' ∨ s.toList[23]? ≠ some '-')
  match api.parse s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "" ∧ api.isValid s = false)

/-- `api.parse` rejects canonical 36-char UUIDs whose version nibble is not `4` or whose variant nibble is not RFC 4122 (`8`/`9`/`a`/`b`) with `.invalidVersion`. -/
def test_uuid_parse_rejectsNonV4VersionOrVariant
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  let badVer ← nondet Char
  assume (isHexChar badVer = true ∧ badVer ≠ '4')
  let badVar ← nondet Char
  assume (isHexChar badVar = true ∧ badVar ≠ '8' ∧ badVar ≠ '9' ∧ badVar ≠ 'a' ∧ badVar ≠ 'b' ∧ badVar ≠ 'A' ∧ badVar ≠ 'B')
  match api.fromRandomBytes bs with
  | .error _ => assume False
  | .ok u =>
    let cs := (api.toString u).toList
    let sBadVer := String.ofList (cs.set 14 badVer)
    let sBadVar := String.ofList (cs.set 19 badVar)
    match api.parse sBadVer with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = .invalidVersion ∧ e.message ≠ "" ∧ api.isValid sBadVer = false)
    match api.parse sBadVar with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = .invalidVersion ∧ e.message ≠ "" ∧ api.isValid sBadVar = false)

/-- `api.parseHex` rejects any string whose length is not 32 with `.invalidFormat`. -/
def test_uuid_parseHex_rejectsInvalidLength
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let s ← nondet String
  assume (s.length ≠ 32)
  match api.parseHex s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "")

/-- `api.parseHex` rejects any 32-char string containing a non-hex character (including hyphens) with `.invalidFormat`. -/
def test_uuid_parseHex_rejectsNonHexChar
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let s ← nondet String
  assume (s.length = 32)
  let idx ← nondet Nat
  assume (idx < 32 ∧ isHexChar s.toList[idx]! = false)
  match api.parseHex s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidFormat ∧ e.message ≠ "")

/-- `api.parseHex` rejects 32-char hex UUIDs whose version nibble is not `4` or whose variant nibble is not RFC 4122 (`8`/`9`/`a`/`b`) with `.invalidVersion`. -/
def test_uuid_parseHex_rejectsNonV4VersionOrVariant
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  let badVer ← nondet Char
  assume (isHexChar badVer = true ∧ badVer ≠ '4')
  let badVar ← nondet Char
  assume (isHexChar badVar = true ∧ badVar ≠ '8' ∧ badVar ≠ '9' ∧ badVar ≠ 'a' ∧ badVar ≠ 'b' ∧ badVar ≠ 'A' ∧ badVar ≠ 'B')
  match api.fromRandomBytes bs with
  | .error _ => assume False
  | .ok u =>
    let cs := (api.toHex u).toList
    let hBadVer := String.ofList (cs.set 12 badVer)
    let hBadVar := String.ofList (cs.set 16 badVar)
    match api.parseHex hBadVer with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = .invalidVersion ∧ e.message ≠ "")
    match api.parseHex hBadVar with
    | .ok _ => NondetTest.assert False
    | .error e => NondetTest.assert (e.kind = .invalidVersion ∧ e.message ≠ "")

/-- Two consecutive `getUuid` calls over `StateM MockRngState` yield distinct valid v4 UUIDs, advance state monotonically, and leave zero state leak across independent runs. -/
def test_uuid_getUuid_consecutiveDistinctValidAndDeterministic
    {runner} [NondetTest runner]
    (mkApi : RawUuidOpsM (StateM MockRngState) → UuidApiM (StateM MockRngState)) : runner Unit := do
  let api := mkApi mockCounterRawOps
  let s₀ ← nondet MockRngState
  assume (s₀.failWith = none)
  let ((r1, r2), s₁) := (do
    let r1 ← api.getUuid
    let r2 ← api.getUuid
    pure (r1, r2)).run s₀
  let ((r1b, r2b), s₁b) := (do
    let r1 ← api.getUuid
    let r2 ← api.getUuid
    pure (r1, r2)).run s₀
  NondetTest.assert (r1 = r1b ∧ r2 = r2b ∧ s₁ = s₁b)
  NondetTest.assert (s₁.counter = s₀.counter + 2 ∧ s₁.draws = s₀.draws + 2)
  match r1, r2 with
  | .ok u1, .ok u2 =>
    NondetTest.assert (u1 ≠ u2)
    NondetTest.assert (api.toString u1 ≠ api.toString u2)
    NondetTest.assert (api.toHex u1 ≠ api.toHex u2)
    NondetTest.assert (u1.bytes.size = 16 ∧ (u1.bytes[6]! &&& (0xF0 : UInt8)) = (0x40 : UInt8) ∧ (u1.bytes[8]! &&& (0xC0 : UInt8)) = (0x80 : UInt8))
    NondetTest.assert (u2.bytes.size = 16 ∧ (u2.bytes[6]! &&& (0xF0 : UInt8)) = (0x40 : UInt8) ∧ (u2.bytes[8]! &&& (0xC0 : UInt8)) = (0x80 : UInt8))
    NondetTest.assert (api.isValid (api.toString u1) = true ∧ api.isValid (api.toString u2) = true)
  | _, _ => NondetTest.assert False

/-- When the underlying `RawUuidOpsM` entropy source fails, `getUuid` propagates the exact error without mutating `counter`. -/
def test_uuid_getUuid_propagatesEntropyError
    {runner} [NondetTest runner]
    (mkApi : RawUuidOpsM (StateM MockRngState) → UuidApiM (StateM MockRngState)) : runner Unit := do
  let api := mkApi mockCounterRawOps
  let s₀ ← nondet MockRngState
  let err ← nondet UuidError
  assume (err.message ≠ "")
  assume (s₀.failWith = some err)
  let (res, s₁) := api.getUuid.run s₀
  NondetTest.assert (res = .error err ∧ s₁.counter = s₀.counter ∧ s₁.draws = s₀.draws + 1)

/-- If `RawUuidOpsM.randomBytes16` returns `.ok` with a byte count other than 16, `getUuid` rejects it with `.invalidLength` and a non-empty message. -/
def test_uuid_getUuid_rejectsWrongRawByteCount
    {runner} [NondetTest runner]
    (mkApi : RawUuidOpsM (StateM MockRngState) → UuidApiM (StateM MockRngState)) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size ≠ 16)
  let badLenOps : RawUuidOpsM (StateM MockRngState) :=
    { mockCounterRawOps with randomBytes16 := pure (.ok bs) }
  let api := mkApi badLenOps
  let s₀ ← nondet MockRngState
  let (res, s₁) := api.getUuid.run s₀
  NondetTest.assert (s₁ = s₀)
  match res with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidLength ∧ e.message ≠ "")

/-- `getUuid` constructs its `Uuid` directly from the 16 payload bytes returned by `RawUuidOpsM.randomBytes16` via `fromRandomBytes`. -/
def test_uuid_getUuid_usesRawRandomBytes
    {runner} [NondetTest runner]
    (mkApi : RawUuidOpsM (StateM MockRngState) → UuidApiM (StateM MockRngState)) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  let fixedOps : RawUuidOpsM (StateM MockRngState) :=
    { mockCounterRawOps with randomBytes16 := pure (.ok bs) }
  let api := mkApi fixedOps
  let s₀ ← nondet MockRngState
  let (res, s₁) := api.getUuid.run s₀
  NondetTest.assert (s₁ = s₀)
  NondetTest.assert (res = api.fromRandomBytes bs)

end LeanSwe.Uuid
