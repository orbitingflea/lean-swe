import Core.NondetTest
import Core.Assumptions
import LeanSwe.CryptoHash.Types
import LeanSwe.CryptoHash.Model

namespace LeanSwe.CryptoHash

open Core (NondetTest ErrorObligation)
open Core.NondetTest

private def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def isHexChar (c : Char) : Bool :=
  isLowerHexChar c || ('A' ≤ c && c ≤ 'F')

private def lowerHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def foldMockBytes (init : UInt64) (bs : List UInt8) : UInt64 :=
  bs.foldl (fun h b => h * 1315423911 + b.toUInt64 + 1) init

private def expandMockBytes : Nat → UInt64 → Array UInt8 → Array UInt8
  | 0, _, acc => acc
  | n + 1, h, acc =>
    let h' := h * 6364136223846793005 + 1442695040888963407
    expandMockBytes n h' (acc.push (UInt8.ofNat ((h'.toNat / 256 + n) % 256)))

private def mockDigestBytes (alg : HashAlg) (msg : ByteArray) : ByteArray :=
  let algTag : UInt64 := match alg with | .sha256 => 0x53484132 | .sha512 => 0x53484135
  let seed := foldMockBytes (algTag + msg.size.toUInt64 * 2654435761) msg.data.toList
  ByteArray.mk (expandMockBytes (digestLen alg) seed #[])

private def mockHmacBytes (key msg : ByteArray) : ByteArray :=
  let keySeed := foldMockBytes (0x484d4143 + key.size.toUInt64 * 2654435761) key.data.toList
  let msgSeed := foldMockBytes (keySeed ^^^ 0x5c5c5c5c5c5c5c5c + msg.size.toUInt64 * 11400714819323198485) msg.data.toList
  ByteArray.mk (expandMockBytes 32 msgSeed #[])

private def mockMapRawError : CryptoHashRawError → CryptoHashError
  | .invalidArgument detail =>
    { kind := .invalidInput
      opensslCode := none
      message := if detail.isEmpty then "invalid cryptohash argument" else detail }
  | .invalidHexInput detail =>
    { kind := .invalidHex
      opensslCode := none
      message := if detail.isEmpty then "invalid hex input" else detail }
  | .lengthError exp got detail =>
    { kind := .lengthMismatch
      opensslCode := none
      message := if detail.isEmpty then s!"length mismatch: expected {exp} bytes, got {got}" else detail }
  | .opensslError code detail =>
    { kind := .cryptoError
      opensslCode := code
      message := if detail.isEmpty then "openssl crypto error" else detail }
  | .userError detail =>
    { kind := .cryptoError
      opensslCode := none
      message := if detail.isEmpty then "cryptohash error" else detail }

private def mockRawOps : RawCryptoHashOpsM (StateM MockCryptoHashState) :=
  { mapRawError := mockMapRawError
    digestRaw := fun alg msg s =>
      let s' := { s with digestCalls := s.digestCalls + 1 }
      match s.failDigestWith with
      | some err => (.error err, s')
      | none =>
        match s.corruptDigestLen with
        | some n => (.ok (ByteArray.mk (Array.replicate n 0)), s')
        | none => (.ok (mockDigestBytes alg msg), s')
    hmacSha256Raw := fun key msg s =>
      let s' := { s with hmacCalls := s.hmacCalls + 1 }
      match s.failHmacWith with
      | some err => (.error err, s')
      | none =>
        match s.corruptHmacLen with
        | some n => (.ok (ByteArray.mk (Array.replicate n 0)), s')
        | none => (.ok (mockHmacBytes key msg), s')
    ctEqualRaw := fun a b s =>
      let s' := { s with ctEqCalls := s.ctEqCalls + 1 }
      if a.size != b.size then
        (.error { kind := .lengthMismatch, message := "length mismatch" }, s')
      else
        match s.failCtEqWith with
        | some err => (.error err, s')
        | none => (.ok (a == b), s') }

/-- Every error returned by `api.mapRawError` maps to the expected `CryptoHashErrorKind`, preserves `opensslCode` on `.opensslError`, and has a non-empty message. -/
def test_cryptohash_mapRawError_preservesContract
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let raw ← nondet CryptoHashRawError
  let err := api.mapRawError raw
  NondetTest.assert (err.message ≠ "")
  match raw with
  | .invalidArgument _ => NondetTest.assert (err.kind = .invalidInput ∧ err.opensslCode = none)
  | .invalidHexInput _ => NondetTest.assert (err.kind = .invalidHex ∧ err.opensslCode = none)
  | .lengthError _ _ _ => NondetTest.assert (err.kind = .lengthMismatch ∧ err.opensslCode = none)
  | .opensslError code _ => NondetTest.assert (err.kind = .cryptoError ∧ err.opensslCode = code)
  | .userError _ => NondetTest.assert (err.kind = .cryptoError ∧ err.opensslCode = none)

/-- `hash`, `sha256`, and `sha512` delegate to `raw.digestRaw`, agree with `hash .sha256` / `hash .sha512`, and return `ValidDigest` outputs. -/
def test_cryptohash_hash_delegatesAndChecksLength
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failDigestWith = none ∧ s₀.corruptDigestLen = none)
  let alg ← nondet HashAlg
  let msg ← nondet ByteArray
  let (res, s₁) := (api.hash alg msg).run s₀
  NondetTest.assert (s₁.digestCalls = s₀.digestCalls + 1 ∧ s₁.hmacCalls = s₀.hmacCalls ∧ s₁.ctEqCalls = s₀.ctEqCalls)
  match res with
  | .error _ => NondetTest.assert False
  | .ok d =>
    NondetTest.assert (d.alg = alg ∧ d.bytes.size = digestLen alg ∧ ValidDigest d ∧ d.isValid = true)
  NondetTest.assert ((api.sha256 msg).run s₀ = (api.hash .sha256 msg).run s₀)
  NondetTest.assert ((api.sha512 msg).run s₀ = (api.hash .sha512 msg).run s₀)

/-- `hash`, `sha256`, and `sha512` propagate raw `digestRaw` errors verbatim while advancing `digestCalls` by 1. -/
def test_cryptohash_hash_propagatesRawError
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let err ← nondet CryptoHashError
  assume (err.message ≠ "")
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failDigestWith = some err)
  let alg ← nondet HashAlg
  let msg ← nondet ByteArray
  let (res, s₁) := (api.hash alg msg).run s₀
  NondetTest.assert (res = .error err ∧ s₁.digestCalls = s₀.digestCalls + 1)
  NondetTest.assert ((api.sha256 msg).run s₀ = (api.hash .sha256 msg).run s₀)
  NondetTest.assert ((api.sha512 msg).run s₀ = (api.hash .sha512 msg).run s₀)

/-- If `raw.digestRaw` returns `.ok` with a byte count other than `digestLen alg`, `hash` rejects it with `.lengthMismatch` and a non-empty message. -/
def test_cryptohash_hash_rejectsWrongRawLength
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let alg ← nondet HashAlg
  let badLen ← nondet Nat
  assume (badLen ≠ digestLen alg)
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failDigestWith = none ∧ s₀.corruptDigestLen = some badLen)
  let msg ← nondet ByteArray
  let (res, s₁) := (api.hash alg msg).run s₀
  NondetTest.assert (s₁.digestCalls = s₀.digestCalls + 1)
  match res with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .lengthMismatch ∧ e.message ≠ "")

/-- `hmacSha256` delegates to `raw.hmacSha256Raw` for arbitrary keys (including empty and > 64 bytes) and returns a 32-byte `.sha256` `Digest`. -/
def test_cryptohash_hmacSha256_delegatesAndChecksLength
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failHmacWith = none ∧ s₀.corruptHmacLen = none)
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let (res, s₁) := (api.hmacSha256 key msg).run s₀
  NondetTest.assert (s₁.hmacCalls = s₀.hmacCalls + 1 ∧ s₁.digestCalls = s₀.digestCalls ∧ s₁.ctEqCalls = s₀.ctEqCalls)
  match res with
  | .error _ => NondetTest.assert False
  | .ok d =>
    NondetTest.assert (d.alg = .sha256 ∧ d.bytes.size = 32 ∧ ValidDigest d ∧ d.isValid = true)

/-- `hmacSha256` propagates raw `hmacSha256Raw` errors verbatim while advancing `hmacCalls` by 1. -/
def test_cryptohash_hmacSha256_propagatesRawError
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let err ← nondet CryptoHashError
  assume (err.message ≠ "")
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failHmacWith = some err)
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let (res, s₁) := (api.hmacSha256 key msg).run s₀
  NondetTest.assert (res = .error err ∧ s₁.hmacCalls = s₀.hmacCalls + 1)

/-- If `raw.hmacSha256Raw` returns `.ok` with a byte count other than 32, `hmacSha256` rejects it with `.lengthMismatch` and a non-empty message. -/
def test_cryptohash_hmacSha256_rejectsWrongRawLength
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let badLen ← nondet Nat
  assume (badLen ≠ 32)
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failHmacWith = none ∧ s₀.corruptHmacLen = some badLen)
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let (res, s₁) := (api.hmacSha256 key msg).run s₀
  NondetTest.assert (s₁.hmacCalls = s₀.hmacCalls + 1)
  match res with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .lengthMismatch ∧ e.message ≠ "")

/-- `ctEq` returns `.ok false` on unequal-length slices without calling `raw.ctEqualRaw`. -/
def test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockCryptoHashState
  let a ← nondet ByteArray
  let b ← nondet ByteArray
  assume (a.size ≠ b.size)
  let (res, s₁) := (api.ctEq a b).run s₀
  NondetTest.assert (res = .ok false ∧ s₁.ctEqCalls = s₀.ctEqCalls)

/-- On equal-length slices without raw errors, `ctEq` delegates to `raw.ctEqualRaw`, matches byte equality, and is reflexive and symmetric. -/
def test_cryptohash_ctEq_equalLengthsDelegates
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failCtEqWith = none)
  let a ← nondet ByteArray
  let b ← nondet ByteArray
  assume (a.size = b.size)
  let (res, s₁) := (api.ctEq a b).run s₀
  let (resRev, _) := (api.ctEq b a).run s₀
  let (resRefl, _) := (api.ctEq a a).run s₀
  NondetTest.assert (res = .ok (a == b) ∧ s₁.ctEqCalls = s₀.ctEqCalls + 1)
  NondetTest.assert (res = resRev ∧ resRefl = .ok true)

/-- On equal-length slices, `ctEq` propagates `raw.ctEqualRaw` errors verbatim while advancing `ctEqCalls` by 1. -/
def test_cryptohash_ctEq_equalLengthsPropagatesRawError
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let err ← nondet CryptoHashError
  assume (err.message ≠ "")
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failCtEqWith = some err)
  let a ← nondet ByteArray
  let b ← nondet ByteArray
  assume (a.size = b.size)
  let (res, s₁) := (api.ctEq a b).run s₀
  NondetTest.assert (res = .error err ∧ s₁.ctEqCalls = s₀.ctEqCalls + 1)

/-- `verifyHmacSha256` rejects non-`.sha256` expected digests with `.invalidInput` before checking `bytes.size` or invoking `hmacSha256Raw`/`ctEqualRaw`. -/
def test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockCryptoHashState
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let expected ← nondet Digest
  assume (expected.alg ≠ .sha256)
  let (res, s₁) := (api.verifyHmacSha256 key msg expected).run s₀
  NondetTest.assert (s₁.hmacCalls = s₀.hmacCalls ∧ s₁.ctEqCalls = s₀.ctEqCalls)
  match res with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidInput ∧ e.message ≠ "")

/-- `verifyHmacSha256` rejects `.sha256` expected digests whose length is not 32 with `.lengthMismatch` before invoking `hmacSha256Raw`/`ctEqualRaw`. -/
def test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockCryptoHashState
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let expected ← nondet Digest
  assume (expected.alg = .sha256 ∧ expected.bytes.size ≠ 32)
  let (res, s₁) := (api.verifyHmacSha256 key msg expected).run s₀
  NondetTest.assert (s₁.hmacCalls = s₀.hmacCalls ∧ s₁.ctEqCalls = s₀.ctEqCalls)
  match res with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .lengthMismatch ∧ e.message ≠ "")

/-- `verifyHmacSha256` propagates `hmacSha256Raw` errors without invoking `ctEqualRaw`. -/
def test_cryptohash_verifyHmacSha256_propagatesHmacError
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let err ← nondet CryptoHashError
  assume (err.message ≠ "")
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failHmacWith = some err)
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let expected ← nondet Digest
  assume (expected.alg = .sha256 ∧ expected.bytes.size = 32)
  let (res, s₁) := (api.verifyHmacSha256 key msg expected).run s₀
  NondetTest.assert (res = .error err ∧ s₁.hmacCalls = s₀.hmacCalls + 1 ∧ s₁.ctEqCalls = s₀.ctEqCalls)

/-- `verifyHmacSha256` propagates `ctEqualRaw` errors when verifying a valid-length `.sha256` digest. -/
def test_cryptohash_verifyHmacSha256_propagatesCtEqError
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let err ← nondet CryptoHashError
  assume (err.message ≠ "")
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failHmacWith = none ∧ s₀.corruptHmacLen = none ∧ s₀.failCtEqWith = some err)
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let expected ← nondet Digest
  assume (expected.alg = .sha256 ∧ expected.bytes.size = 32)
  let (res, s₁) := (api.verifyHmacSha256 key msg expected).run s₀
  NondetTest.assert (res = .error err ∧ s₁.hmacCalls = s₀.hmacCalls + 1 ∧ s₁.ctEqCalls = s₀.ctEqCalls + 1)

/-- `verifyHmacSha256` returns `.ok true` for the computed tag, `.ok false` for a tampered tag byte or wrong key/message, and `.ok (tag.bytes == expected.bytes)` generally. -/
def test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered
    {runner} [NondetTest runner]
    (mkApi : RawCryptoHashOpsM (StateM MockCryptoHashState) → CryptoHashApiM (StateM MockCryptoHashState)) : runner Unit := do
  let api := mkApi mockRawOps
  let s₀ ← nondet MockCryptoHashState
  assume (s₀.failHmacWith = none ∧ s₀.corruptHmacLen = none ∧ s₀.failCtEqWith = none)
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let expected ← nondet Digest
  assume (expected.alg = .sha256 ∧ expected.bytes.size = 32)
  let (tagRes, _) := (api.hmacSha256 key msg).run s₀
  let (verRes, s₁) := (api.verifyHmacSha256 key msg expected).run s₀
  NondetTest.assert (s₁.hmacCalls = s₀.hmacCalls + 1 ∧ s₁.ctEqCalls = s₀.ctEqCalls + 1)
  match tagRes with
  | .error _ => NondetTest.assert False
  | .ok tag =>
    NondetTest.assert (verRes = .ok (tag.bytes == expected.bytes))
    NondetTest.assert (((api.verifyHmacSha256 key msg tag).run s₀).1 = .ok true)
    let tampered : Digest := { alg := .sha256, bytes := tag.bytes.set! 0 (tag.bytes[0]! ^^^ 1) }
    NondetTest.assert (((api.verifyHmacSha256 key msg tampered).run s₀).1 = .ok false)
  let (tagK1, _) := (api.hmacSha256 "k1".toUTF8 "m1".toUTF8).run s₀
  match tagK1 with
  | .error _ => NondetTest.assert False
  | .ok t1 =>
    NondetTest.assert (((api.verifyHmacSha256 "k2".toUTF8 "m1".toUTF8 t1).run s₀).1 = .ok false)
    NondetTest.assert (((api.verifyHmacSha256 "k1".toUTF8 "m2".toUTF8 t1).run s₀).1 = .ok false)

/-- `api.toHex` encodes valid digests as lowercase big-endian nibble pairs and round-trips through `api.fromHex`. -/
def test_cryptohash_toHex_formatAndRoundTrip
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let d ← nondet Digest
  assume (d.bytes.size = digestLen d.alg)
  let h := api.toHex d
  NondetTest.assert (h.length = 2 * digestLen d.alg)
  NondetTest.assert (h.toList.all isLowerHexChar = true)
  NondetTest.assert (api.fromHex d.alg h = .ok d)
  let cs := h.toList
  let i ← nondet Nat
  assume (i < digestLen d.alg)
  let b := d.bytes[i]!.toNat
  NondetTest.assert (cs[2 * i]? = some (lowerHexDigit (b / 16)))
  NondetTest.assert (cs[2 * i + 1]? = some (lowerHexDigit (b % 16)))

/-- `api.fromHex` accepts uppercase hex characters and recovers the exact valid `Digest`. -/
def test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let d ← nondet Digest
  assume (d.bytes.size = digestLen d.alg)
  let upper := String.ofList ((api.toHex d).toList.map Char.toUpper)
  NondetTest.assert (api.fromHex d.alg upper = .ok d)

/-- Every accepted `api.fromHex alg s = .ok d` yields a valid `Digest` whose `api.toHex d` equals lowercased `s`. -/
def test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let alg ← nondet HashAlg
  let s ← nondet String
  match api.fromHex alg s with
  | .error e => NondetTest.assert (e.message ≠ "")
  | .ok d =>
    NondetTest.assert (d.alg = alg ∧ d.bytes.size = digestLen alg ∧ ValidDigest d ∧ d.isValid = true)
    NondetTest.assert ((api.toHex d).toList = s.toList.map Char.toLower)

/-- `api.fromHex` rejects any string containing a non-hex character with `.invalidHex`, taking precedence over length mismatch. -/
def test_cryptohash_fromHex_rejectsNonHexChar
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let alg ← nondet HashAlg
  let s ← nondet String
  let idx ← nondet Nat
  assume (idx < s.length ∧ isHexChar s.toList[idx]! = false)
  match api.fromHex alg s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidHex ∧ e.message ≠ "")

/-- `api.fromHex` rejects any odd-length hex string with `.invalidHex`, taking precedence over length mismatch. -/
def test_cryptohash_fromHex_rejectsOddLengthHex
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let alg ← nondet HashAlg
  let s ← nondet String
  assume (s.length % 2 = 1 ∧ s.toList.all isHexChar = true)
  match api.fromHex alg s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidHex ∧ e.message ≠ "")

/-- `api.fromHex` rejects any even-length all-hex string whose length differs from `2 * digestLen alg` with `.lengthMismatch`. -/
def test_cryptohash_fromHex_rejectsWrongEvenHexLength
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let alg ← nondet HashAlg
  let s ← nondet String
  assume (s.length % 2 = 0 ∧ s.length ≠ 2 * digestLen alg ∧ s.toList.all isHexChar = true)
  match api.fromHex alg s with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .lengthMismatch ∧ e.message ≠ "")

/-- `api.fromHex` and `api.toHex` normalize and round-trip NIST FIPS 180-4 and RFC 4231 hex vectors. -/
def test_cryptohash_vectorHexRoundTrip
    {runner} [NondetTest runner] (api : CryptoHashApi) : runner Unit := do
  let sha256Empty := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  let sha512Empty := "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
  let rfc4231Case6 := "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
  match api.fromHex .sha256 sha256Empty with
  | .error _ => NondetTest.assert False
  | .ok d1 => NondetTest.assert (api.toHex d1 = sha256Empty)
  match api.fromHex .sha512 sha512Empty with
  | .error _ => NondetTest.assert False
  | .ok d2 => NondetTest.assert (api.toHex d2 = sha512Empty)
  match api.fromHex .sha256 (String.ofList (rfc4231Case6.toList.map Char.toUpper)) with
  | .error _ => NondetTest.assert False
  | .ok d3 => NondetTest.assert (api.toHex d3 = rfc4231Case6)

/-- Declared error-coverage matrix for pure upper-layer `LeanSwe.CryptoHash` fallible requests (`CryptoHashErrorKind`). -/
def errorCoverage : List (ErrorObligation CryptoHashErrorKind) :=
  [ { request := "LeanSwe.CryptoHash.hash"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hash_invalidInput" .mocked }
  , { request := "LeanSwe.CryptoHash.hash"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_hash_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.hash"
      errorKind := .lengthMismatch
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hash_lengthMismatch" .mocked }
  , { request := "LeanSwe.CryptoHash.hash"
      errorKind := .cryptoError
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hash_cryptoError" .mocked }
  , { request := "LeanSwe.CryptoHash.sha256"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha256_invalidInput" .mocked }
  , { request := "LeanSwe.CryptoHash.sha256"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_sha256_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.sha256"
      errorKind := .lengthMismatch
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha256_lengthMismatch" .mocked }
  , { request := "LeanSwe.CryptoHash.sha256"
      errorKind := .cryptoError
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha256_cryptoError" .mocked }
  , { request := "LeanSwe.CryptoHash.sha512"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha512_invalidInput" .mocked }
  , { request := "LeanSwe.CryptoHash.sha512"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_sha512_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.sha512"
      errorKind := .lengthMismatch
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha512_lengthMismatch" .mocked }
  , { request := "LeanSwe.CryptoHash.sha512"
      errorKind := .cryptoError
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha512_cryptoError" .mocked }
  , { request := "LeanSwe.CryptoHash.hmacSha256"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hmacSha256_invalidInput" .mocked }
  , { request := "LeanSwe.CryptoHash.hmacSha256"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_hmacSha256_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.hmacSha256"
      errorKind := .lengthMismatch
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hmacSha256_lengthMismatch" .mocked }
  , { request := "LeanSwe.CryptoHash.hmacSha256"
      errorKind := .cryptoError
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hmacSha256_cryptoError" .mocked }
  , { request := "LeanSwe.CryptoHash.verifyHmacSha256"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_verifyHmacSha256_invalidInput" .real }
  , { request := "LeanSwe.CryptoHash.verifyHmacSha256"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_verifyHmacSha256_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.verifyHmacSha256"
      errorKind := .lengthMismatch
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_verifyHmacSha256_lengthMismatch" .real }
  , { request := "LeanSwe.CryptoHash.verifyHmacSha256"
      errorKind := .cryptoError
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_verifyHmacSha256_cryptoError" .mocked }
  , { request := "LeanSwe.CryptoHash.fromHex"
      errorKind := .invalidInput
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_fromHex_never_invalidInput" }
  , { request := "LeanSwe.CryptoHash.fromHex"
      errorKind := .invalidHex
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_fromHex_invalidHex" .real }
  , { request := "LeanSwe.CryptoHash.fromHex"
      errorKind := .lengthMismatch
      justification := .tested "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_fromHex_lengthMismatch" .real }
  , { request := "LeanSwe.CryptoHash.fromHex"
      errorKind := .cryptoError
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_fromHex_never_cryptoError" }
  , { request := "LeanSwe.CryptoHash.ctEq"
      errorKind := .invalidInput
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_ctEq_never_invalidInput" }
  , { request := "LeanSwe.CryptoHash.ctEq"
      errorKind := .invalidHex
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_ctEq_never_invalidHex" }
  , { request := "LeanSwe.CryptoHash.ctEq"
      errorKind := .lengthMismatch
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_ctEq_never_lengthMismatch" }
  , { request := "LeanSwe.CryptoHash.ctEq"
      errorKind := .cryptoError
      justification := .provedImpossible "LeanSwe.CryptoHash.Proofs.cryptohash_ctEq_never_cryptoError" } ]

/-- `mkApi Raw.Model.modelRawOps` agrees identically with `Model.modelApi` across all 9 `CryptoHashApiM` methods. -/
def test_cryptohash_mkApi_matchesModel
    {runner} [NondetTest runner] (mkApi : RawCryptoHashOpsM Id → CryptoHashApiM Id) : runner Unit := do
  let alg ← nondet HashAlg
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  let expected ← nondet Digest
  let hexStr ← nondet String
  let a ← nondet ByteArray
  let b ← nondet ByteArray
  let rawErr ← nondet CryptoHashRawError
  let implApi := mkApi Raw.Model.modelRawOps
  let refApi := Model.modelApi
  NondetTest.assert (implApi.mapRawError rawErr = refApi.mapRawError rawErr)
  NondetTest.assert (implApi.hash alg msg = refApi.hash alg msg)
  NondetTest.assert (implApi.sha256 msg = refApi.sha256 msg)
  NondetTest.assert (implApi.sha512 msg = refApi.sha512 msg)
  NondetTest.assert (implApi.hmacSha256 key msg = refApi.hmacSha256 key msg)
  NondetTest.assert (implApi.verifyHmacSha256 key msg expected = refApi.verifyHmacSha256 key msg expected)
  NondetTest.assert (implApi.toHex expected = refApi.toHex expected)
  NondetTest.assert (implApi.fromHex alg hexStr = refApi.fromHex alg hexStr)
  NondetTest.assert (implApi.ctEq a b = refApi.ctEq a b)

end LeanSwe.CryptoHash
