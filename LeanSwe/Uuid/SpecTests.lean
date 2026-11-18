import Core.NondetTest
import Core.Assumptions
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.Uuid.Types

namespace LeanSwe.Uuid

open Core (NondetTest ErrorObligation)
open Core.NondetTest
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM TimeRandState GrndFlags)

/-- Return `true` iff `c` is a lowercase ASCII hexadecimal digit (`'0'..'9'` or `'a'..'f'`). -/
def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Return `true` iff `c` is an ASCII hexadecimal digit (`'0'..'9'`, `'a'..'f'`, or `'A'..'F'`). -/
def isHexChar (c : Char) : Bool :=
  isLowerHexChar c || ('A' ≤ c && c ≤ 'F')

/-- Convert a nibble `0..15` into its lowercase ASCII hexadecimal character. -/
def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Scripted `TimeRandOpsM` popping queued `getrandom` responses from `List (Except Errno ByteArray)` (returning `EIO` once empty). -/
def scriptedGetrandomOps : TimeRandOpsM (StateM (List (Except Errno ByteArray))) :=
  { clock_gettime := fun _ => pure (.error Errno.ENOSYS)
    clock_nanosleep := fun _ _ _ => pure (.error Errno.ENOSYS)
    getrandom := fun _ _ => do
      let q ← get
      let r := match q with
        | [] => .error Errno.EIO
        | x :: _ => x
      set q.tail
      return r }

/-- Counting `TimeRandOpsM` incrementing `StateM Nat` on each `getrandom` call and returning `fixed`. -/
def countingFixedGetrandomOps (fixed : Except Errno ByteArray) : TimeRandOpsM (StateM Nat) :=
  { clock_gettime := fun _ => pure (.error Errno.ENOSYS)
    clock_nanosleep := fun _ _ _ => pure (.error Errno.ENOSYS)
    getrandom := fun _ _ => do
      modify (· + 1)
      return fixed }

/-- Every error returned by `api.mapRawError` has kind `.entropyFailed` and a non-empty diagnostic message, preserving `errno` on `.osError`. -/
def test_uuid_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : UuidApi) : runner Unit := do
  let raw ← nondet UuidRawError
  let err := api.mapRawError raw
  NondetTest.assert (err.kind = .entropyFailed ∧ err.message ≠ "")
  match raw with
  | .osError code _ => NondetTest.assert (err.errnoCode = some code)
  | .shortRead _ _ => NondetTest.assert (err.errnoCode = none)
  | .userError _ => NondetTest.assert (err.errnoCode = none)

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

/-- Two consecutive `getUuid` calls over `TimeRand.modelOps` (`StateM TimeRandState`) yield distinct valid RFC 4122 v4 UUIDs, mark CRNG ready, advance `entropyDraws` by 2, and replay deterministically. -/
def test_uuid_getUuid_overTimeRandModel_consecutiveDistinctValid
    {runner} [NondetTest runner]
    (mkApiFn : TimeRandOpsM (StateM TimeRandState) → UuidApiM (StateM TimeRandState)) : runner Unit := do
  let api := mkApiFn LeanSwe.LinuxSyscall.TimeRand.modelOps
  let s₀ ← nondet TimeRandState
  let ((r1, r2), s₁) := (do
    let r1 ← api.getUuid
    let r2 ← api.getUuid
    pure (r1, r2)).run s₀
  let ((r1b, r2b), s₁b) := (do
    let r1 ← api.getUuid
    let r2 ← api.getUuid
    pure (r1, r2)).run s₀
  NondetTest.assert (r1 = r1b ∧ r2 = r2b ∧ s₁ = s₁b)
  NondetTest.assert (s₁.entropyDraws = s₀.entropyDraws + 2 ∧ s₁.crngReady = true)
  match r1, r2 with
  | .ok u1, .ok u2 =>
    NondetTest.assert (u1 ≠ u2)
    NondetTest.assert (api.toString u1 ≠ api.toString u2)
    NondetTest.assert (api.toHex u1 ≠ api.toHex u2)
    NondetTest.assert (u1.bytes.size = 16 ∧ (u1.bytes[6]! &&& (0xF0 : UInt8)) = (0x40 : UInt8) ∧ (u1.bytes[8]! &&& (0xC0 : UInt8)) = (0x80 : UInt8))
    NondetTest.assert (u2.bytes.size = 16 ∧ (u2.bytes[6]! &&& (0xF0 : UInt8)) = (0x40 : UInt8) ∧ (u2.bytes[8]! &&& (0xC0 : UInt8)) = (0x80 : UInt8))
    NondetTest.assert (api.isValid (api.toString u1) = true ∧ api.isValid (api.toString u2) = true)
  | _, _ => NondetTest.assert False

/-- When `sys.getrandom` returns 16 bytes on the first call, `(mkApiFn sys).getUuid` requests `(16, {})` once and constructs its `Uuid` via `fromRandomBytes`. -/
def test_uuid_getUuid_usesExact16BytesFromGetrandom
    {runner} [NondetTest runner]
    (mkApiFn : TimeRandOpsM (StateM (List (UInt32 × GrndFlags))) →
      UuidApiM (StateM (List (UInt32 × GrndFlags)))) : runner Unit := do
  let bs ← nondet ByteArray
  assume (bs.size = 16)
  let recOps : TimeRandOpsM (StateM (List (UInt32 × GrndFlags))) :=
    { clock_gettime := fun _ => pure (.error Errno.ENOSYS)
      clock_nanosleep := fun _ _ _ => pure (.error Errno.ENOSYS)
      getrandom := fun len flags => do
        modify (fun xs => xs ++ [(len, flags)])
        return .ok bs }
  let api := mkApiFn recOps
  let (res, log) := api.getUuid.run []
  NondetTest.assert (log = [(16, {})] ∧ res = api.fromRandomBytes bs)

/-- `(mkApiFn sys).getUuid` accumulates partial `getrandom` reads across arbitrary `Errno.EINTR` interruptions without losing prefix bytes and stamps RFC 4122 v4 bits on the assembled 16-byte buffer. -/
def test_uuid_getUuid_accumulatesPartialReadsAndRetriesEintr
    {runner} [NondetTest runner]
    (mkApiFn : TimeRandOpsM (StateM (List (Except Errno ByteArray))) →
      UuidApiM (StateM (List (Except Errno ByteArray)))) : runner Unit := do
  let b1 ← nondet ByteArray
  let b2 ← nondet ByteArray
  let eintrCount ← nondet Nat
  assume (0 < b1.size ∧ 0 < b2.size ∧ b1.size + b2.size = 16)
  assume (eintrCount ≤ 8)
  let script : List (Except Errno ByteArray) :=
    [.ok b1] ++ List.replicate eintrCount (.error Errno.EINTR) ++ [.ok b2]
  let api := mkApiFn scriptedGetrandomOps
  let (res, rem) := api.getUuid.run script
  let combined := ByteArray.mk (b1.data.toList ++ b2.data.toList).toArray
  NondetTest.assert (rem = [] ∧ res = api.fromRandomBytes combined)

/-- When `sys.getrandom` fails with any non-`EINTR` `Errno`, `(mkApiFn sys).getUuid` stops immediately after 1 call and returns `.entropyFailed` with `errnoCode = some e` and non-empty message. -/
def test_uuid_getUuid_mapsNonEintrErrnoWithoutRetry
    {runner} [NondetTest runner]
    (mkApiFn : TimeRandOpsM (StateM Nat) → UuidApiM (StateM Nat)) : runner Unit := do
  let e ← nondet Errno
  assume (e ≠ Errno.EINTR)
  let api := mkApiFn (countingFixedGetrandomOps (.error e))
  let (res, calls) := api.getUuid.run 0
  NondetTest.assert (calls = 1)
  NondetTest.assert (∃ err, res = .error err ∧ err.kind = .entropyFailed ∧
    err.errnoCode = some e ∧ err.message ≠ "")

/-- Persistent `Errno.EINTR` terminates within `MAX_GETRANDOM_ATTEMPTS` returning `.entropyFailed` (`errnoCode = some EINTR`), and anomalous `0`-byte or oversized (`> 16`-byte) `getrandom` chunks stop after 1 call returning `.entropyFailed` (`errnoCode = none`). -/
def test_uuid_getUuid_persistentEintrAndInvalidChunkReturnEntropyFailed
    {runner} [NondetTest runner]
    (mkApiFn : TimeRandOpsM (StateM Nat) → UuidApiM (StateM Nat)) : runner Unit := do
  let bigChunk ← nondet ByteArray
  assume (bigChunk.size > 16)
  let (rEintr, callsEintr) := (mkApiFn (countingFixedGetrandomOps (.error Errno.EINTR))).getUuid.run 0
  NondetTest.assert (callsEintr = MAX_GETRANDOM_ATTEMPTS ∧
    ∃ err, rEintr = .error err ∧ err.kind = .entropyFailed ∧
      err.errnoCode = some Errno.EINTR ∧ err.message ≠ "")
  let (rEmpty, callsEmpty) := (mkApiFn (countingFixedGetrandomOps (.ok ByteArray.empty))).getUuid.run 0
  NondetTest.assert (callsEmpty = 1 ∧
    ∃ err, rEmpty = .error err ∧ err.kind = .entropyFailed ∧
      err.errnoCode = none ∧ err.message ≠ "")
  let (rBig, callsBig) := (mkApiFn (countingFixedGetrandomOps (.ok bigChunk))).getUuid.run 0
  NondetTest.assert (callsBig = 1 ∧
    ∃ err, rBig = .error err ∧ err.kind = .entropyFailed ∧
      err.errnoCode = none ∧ err.message ≠ "")

/-- Declared error-coverage matrix for pure helper package `LeanSwe.Uuid` (`UuidErrorKind`, `20` obligations across `fromRandomBytes`, `parse`, `parseHex`, `getUuid`, and `v4`). -/
def errorCoverage : List (ErrorObligation UuidErrorKind) :=
  [ { request := "LeanSwe.Uuid.fromRandomBytes"
      errorKind := .entropyFailed
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_fromRandomBytes_never_entropyFailed" }
  , { request := "LeanSwe.Uuid.fromRandomBytes"
      errorKind := .invalidLength
      justification := .tested "LeanSwe.Uuid.RuntimeTests.err_uuid_fromRandomBytes_invalidLength" .real }
  , { request := "LeanSwe.Uuid.fromRandomBytes"
      errorKind := .invalidFormat
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_fromRandomBytes_never_invalidFormat" }
  , { request := "LeanSwe.Uuid.fromRandomBytes"
      errorKind := .invalidVersion
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_fromRandomBytes_never_invalidVersion" }

  , { request := "LeanSwe.Uuid.parse"
      errorKind := .entropyFailed
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_parse_never_entropyFailed" }
  , { request := "LeanSwe.Uuid.parse"
      errorKind := .invalidLength
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_parse_never_invalidLength" }
  , { request := "LeanSwe.Uuid.parse"
      errorKind := .invalidFormat
      justification := .tested "LeanSwe.Uuid.RuntimeTests.err_uuid_parse_invalidFormat" .real }
  , { request := "LeanSwe.Uuid.parse"
      errorKind := .invalidVersion
      justification := .tested "LeanSwe.Uuid.RuntimeTests.err_uuid_parse_invalidVersion" .real }

  , { request := "LeanSwe.Uuid.parseHex"
      errorKind := .entropyFailed
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_parseHex_never_entropyFailed" }
  , { request := "LeanSwe.Uuid.parseHex"
      errorKind := .invalidLength
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_parseHex_never_invalidLength" }
  , { request := "LeanSwe.Uuid.parseHex"
      errorKind := .invalidFormat
      justification := .tested "LeanSwe.Uuid.RuntimeTests.err_uuid_parseHex_invalidFormat" .real }
  , { request := "LeanSwe.Uuid.parseHex"
      errorKind := .invalidVersion
      justification := .tested "LeanSwe.Uuid.RuntimeTests.err_uuid_parseHex_invalidVersion" .real }

  , { request := "LeanSwe.Uuid.getUuid"
      errorKind := .entropyFailed
      justification := .tested "LeanSwe.Uuid.RuntimeTests.err_uuid_getUuid_entropyFailed" .mocked }
  , { request := "LeanSwe.Uuid.getUuid"
      errorKind := .invalidLength
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_getUuid_never_invalidLength" }
  , { request := "LeanSwe.Uuid.getUuid"
      errorKind := .invalidFormat
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_getUuid_never_invalidFormat" }
  , { request := "LeanSwe.Uuid.getUuid"
      errorKind := .invalidVersion
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_getUuid_never_invalidVersion" }

  , { request := "LeanSwe.Uuid.v4"
      errorKind := .entropyFailed
      justification := .tested "LeanSwe.Uuid.RuntimeTests.err_uuid_v4_entropyFailed" .mocked }
  , { request := "LeanSwe.Uuid.v4"
      errorKind := .invalidLength
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_v4_never_invalidLength" }
  , { request := "LeanSwe.Uuid.v4"
      errorKind := .invalidFormat
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_v4_never_invalidFormat" }
  , { request := "LeanSwe.Uuid.v4"
      errorKind := .invalidVersion
      justification := .provedImpossible "LeanSwe.Uuid.Proofs.uuid_v4_never_invalidVersion" } ]

end LeanSwe.Uuid
