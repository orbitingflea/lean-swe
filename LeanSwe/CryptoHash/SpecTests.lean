import Core.NondetTest
import LeanSwe.CryptoHash.Types

namespace LeanSwe.CryptoHash

open Core (NondetTest)
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

/-- External trust boundary assumptions for the OpenSSL 3 `libcrypto` C shim (`c/cryptohash_shim.c`), grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- `sha256` matches NIST FIPS 180-4 test vectors (`""`, `"abc"`, `"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"`). -/
  sha256NistFips180_4 : Prop
  /-- `sha512` matches NIST FIPS 180-4 test vectors (`""`, `"abc"`). -/
  sha512NistFips180_4 : Prop
  /-- `hmacSha256` matches RFC 4231 Test Cases 1–4, 6, and 7 (including 131-byte key > 64 bytes) plus empty key (`ByteArray.empty`). -/
  hmacSha256Rfc4231AndEmptyKey : Prop
  /-- `digestRaw` and `hmacSha256Raw` preserve embedded `0x00` bytes in both keys and payloads without C `strlen` truncation. -/
  embeddedNulBytesPreserved : Prop
  /-- `ctEqualRaw` returns `.ok (a == b)` on equal-length arrays (including empty arrays) and `.error` with `.lengthMismatch` on unequal lengths. -/
  ctEqualRawMatchesBeqAndRejectsMismatch : Prop
  /-- Differential equivalence with Python `hashlib.sha256`, `hashlib.sha512`, and `hmac.new(..., hashlib.sha256)` across empty, small, block-boundary (63/64/65/128 bytes), and large multi-MB buffers. -/
  differentialPythonHashlibAndHmac : Prop

/-- Empirical hex contract (grounded in `RuntimeTests.lean`): `api.fromHex` and `api.toHex` normalize and round-trip NIST FIPS 180-4 and RFC 4231 hex vectors. -/
def empirical_cryptohash_vectorHexRoundTrip
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

private def zeros32 : ByteArray :=
  ByteArray.mk (Array.replicate 32 0)

private def validDigest32 : Digest :=
  { alg := .sha256, bytes := zeros32 }

private def zeros64Hex : String :=
  String.ofList (List.replicate 64 '0')

private def stubCryptoHashApi : CryptoHashApi :=
  { mapRawError := mockMapRawError
    hash := fun alg _ => pure (.ok { alg, bytes := ByteArray.mk (Array.replicate (digestLen alg) 0) })
    sha256 := fun _ => pure (.ok validDigest32)
    sha512 := fun _ => pure (.ok { alg := .sha512, bytes := ByteArray.mk (Array.replicate 64 0) })
    hmacSha256 := fun _ _ => pure (.ok validDigest32)
    verifyHmacSha256 := fun _ _ _ => pure (.ok true)
    toHex := fun _ => zeros64Hex
    fromHex := fun alg s =>
      if s.length == 2 * digestLen alg then
        .ok { alg, bytes := ByteArray.mk (Array.replicate (digestLen alg) 0) }
      else
        .error { kind := .lengthMismatch, message := "bad" }
    ctEq := fun a b => pure (.ok (a == b)) }

private def stubMkApi (ops : RawCryptoHashOpsM (StateM MockCryptoHashState)) :
    CryptoHashApiM (StateM MockCryptoHashState) :=
  { mapRawError := ops.mapRawError
    hash := fun alg msg => do
      match ← ops.digestRaw alg msg with
      | .error e => return .error e
      | .ok bs =>
        if bs.size != digestLen alg then
          return .error { kind := .lengthMismatch, message := "bad digest len" }
        else
          return .ok { alg, bytes := bs }
    sha256 := fun msg => do
      match ← ops.digestRaw .sha256 msg with
      | .error e => return .error e
      | .ok bs =>
        if bs.size != 32 then
          return .error { kind := .lengthMismatch, message := "bad digest len" }
        else
          return .ok { alg := .sha256, bytes := bs }
    sha512 := fun msg => do
      match ← ops.digestRaw .sha512 msg with
      | .error e => return .error e
      | .ok bs =>
        if bs.size != 64 then
          return .error { kind := .lengthMismatch, message := "bad digest len" }
        else
          return .ok { alg := .sha512, bytes := bs }
    hmacSha256 := fun key msg => do
      match ← ops.hmacSha256Raw key msg with
      | .error e => return .error e
      | .ok bs =>
        if bs.size != 32 then
          return .error { kind := .lengthMismatch, message := "bad hmac len" }
        else
          return .ok { alg := .sha256, bytes := bs }
    verifyHmacSha256 := fun key msg expected => do
      if expected.alg != .sha256 then
        return .error { kind := .invalidInput, message := "expected sha256" }
      if expected.bytes.size != 32 then
        return .error { kind := .lengthMismatch, message := "expected 32 bytes" }
      match ← ops.hmacSha256Raw key msg with
      | .error e => return .error e
      | .ok bs =>
        if bs.size != 32 then
          return .error { kind := .lengthMismatch, message := "bad hmac len" }
        else
          ops.ctEqualRaw bs expected.bytes
    toHex := stubCryptoHashApi.toHex
    fromHex := stubCryptoHashApi.fromHex
    ctEq := fun a b =>
      if a.size != b.size then
        pure (.ok false)
      else
        ops.ctEqualRaw a b }

example : ¬ Core.AllPass (test_cryptohash_mapRawError_preservesContract
    { stubCryptoHashApi with mapRawError := fun _ => { kind := .cryptoError, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  dsimp [test_cryptohash_mapRawError_preservesContract, Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_cryptohash_hash_delegatesAndChecksLength
    (fun ops => { stubMkApi ops with sha256 := fun _ => pure (.ok { alg := .sha512, bytes := zeros32 }) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩ .sha256 ByteArray.empty
  simp [stubMkApi, mockRawOps, mockDigestBytes, foldMockBytes, zeros32,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, pure, StateT.pure] at h0
  cases h0.2.2.1

example : ¬ Core.AllPass (test_cryptohash_hash_propagatesRawError
    (fun ops => { stubMkApi ops with hash := fun _ _ => pure (.ok validDigest32) })) := by
  intro h
  let err : CryptoHashError := { kind := .cryptoError, message := "ossl" }
  have h0 := h err (by decide) { failDigestWith := some err } rfl .sha256 ByteArray.empty
  dsimp [test_cryptohash_hash_propagatesRawError, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_cryptohash_hash_rejectsWrongRawLength
    (fun ops => { stubMkApi ops with
      hash := fun alg msg => do
        match ← ops.digestRaw alg msg with
        | .error e => return .error e
        | .ok bs => return .ok { alg, bytes := bs } })) := by
  intro h
  have h0 := h .sha256 3 (by decide) { corruptDigestLen := some 3 } ⟨rfl, rfl⟩ ByteArray.empty
  dsimp [test_cryptohash_hash_rejectsWrongRawLength, stubMkApi, mockRawOps,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, StateT.get, StateT.set, pure, StateT.pure] at h0
  exact h0.2.1

example : ¬ Core.AllPass (test_cryptohash_hmacSha256_delegatesAndChecksLength
    (fun ops => { stubMkApi ops with hmacSha256 := fun _ _ => pure (.ok validDigest32) })) := by
  intro h
  have h0 := h {} ⟨rfl, rfl⟩ ByteArray.empty ByteArray.empty
  dsimp [test_cryptohash_hmacSha256_delegatesAndChecksLength, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_cryptohash_hmacSha256_propagatesRawError
    (fun ops => { stubMkApi ops with hmacSha256 := fun _ _ => pure (.ok validDigest32) })) := by
  intro h
  let err : CryptoHashError := { kind := .cryptoError, message := "hmac fail" }
  have h0 := h err (by decide) { failHmacWith := some err } rfl ByteArray.empty ByteArray.empty
  dsimp [test_cryptohash_hmacSha256_propagatesRawError, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_cryptohash_hmacSha256_rejectsWrongRawLength
    (fun ops => { stubMkApi ops with
      hmacSha256 := fun key msg => do
        match ← ops.hmacSha256Raw key msg with
        | .error e => return .error e
        | .ok bs => return .ok { alg := .sha256, bytes := bs } })) := by
  intro h
  have h0 := h 3 (by decide) { corruptHmacLen := some 3 } ⟨rfl, rfl⟩ ByteArray.empty ByteArray.empty
  dsimp [test_cryptohash_hmacSha256_rejectsWrongRawLength, stubMkApi, mockRawOps,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, StateT.get, StateT.set, pure, StateT.pure] at h0
  exact h0.2.1

example : ¬ Core.AllPass (test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall
    (fun ops => { stubMkApi ops with ctEq := fun a b => ops.ctEqualRaw a b })) := by
  intro h
  have h0 := h {} ByteArray.empty (ByteArray.mk #[1]) (by decide)
  dsimp [test_cryptohash_ctEq_unequalLengthsReturnsFalseWithoutRawCall, stubMkApi, mockRawOps,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, StateT.get, StateT.set, pure, StateT.pure] at h0
  exact absurd h0.1.2 (by decide)

example : ¬ Core.AllPass (test_cryptohash_ctEq_equalLengthsDelegates
    (fun ops => { stubMkApi ops with ctEq := fun _ _ => pure (.ok false) })) := by
  intro h
  have h0 := h {} rfl ByteArray.empty ByteArray.empty rfl
  dsimp [test_cryptohash_ctEq_equalLengthsDelegates, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  have h1 := h0.1.1
  injection h1 with h2
  exact absurd h2 (by decide)

example : ¬ Core.AllPass (test_cryptohash_ctEq_equalLengthsPropagatesRawError
    (fun ops => { stubMkApi ops with ctEq := fun _ _ => pure (.ok true) })) := by
  intro h
  let err : CryptoHashError := { kind := .cryptoError, message := "cteq fail" }
  have h0 := h err (by decide) { failCtEqWith := some err } rfl ByteArray.empty ByteArray.empty rfl
  dsimp [test_cryptohash_ctEq_equalLengthsPropagatesRawError, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls
    (fun ops => { stubMkApi ops with
      verifyHmacSha256 := fun _ _ expected =>
        if expected.bytes.size != 32 then pure (.error { kind := .lengthMismatch, message := "bad len" })
        else pure (.error { kind := .invalidInput, message := "bad alg" }) })) := by
  intro h
  have h0 := h {} ByteArray.empty ByteArray.empty { alg := .sha512, bytes := ByteArray.empty } (by decide)
  dsimp [test_cryptohash_verifyHmacSha256_rejectsWrongAlgBeforeCalls, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  exact absurd h0.2.1 (by decide)

example : ¬ Core.AllPass (test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls
    (fun ops => { stubMkApi ops with
      verifyHmacSha256 := fun _ _ _ => pure (.ok false) })) := by
  intro h
  have h0 := h {} ByteArray.empty ByteArray.empty { alg := .sha256, bytes := ByteArray.empty } (by decide)
  dsimp [test_cryptohash_verifyHmacSha256_rejectsWrongLenBeforeCalls, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  exact h0.2.1

example : ¬ Core.AllPass (test_cryptohash_verifyHmacSha256_propagatesHmacError
    (fun ops => { stubMkApi ops with verifyHmacSha256 := fun _ _ _ => pure (.ok false) })) := by
  intro h
  let err : CryptoHashError := { kind := .cryptoError, message := "hmac fail" }
  have h0 := h err (by decide) { failHmacWith := some err } rfl ByteArray.empty ByteArray.empty validDigest32 (by decide)
  dsimp [test_cryptohash_verifyHmacSha256_propagatesHmacError, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_cryptohash_verifyHmacSha256_propagatesCtEqError
    (fun ops => { stubMkApi ops with verifyHmacSha256 := fun _ _ _ => pure (.ok false) })) := by
  intro h
  let err : CryptoHashError := { kind := .cryptoError, message := "cteq fail" }
  have h0 := h err (by decide) { failCtEqWith := some err } (by decide) ByteArray.empty ByteArray.empty validDigest32 (by decide)
  dsimp [test_cryptohash_verifyHmacSha256_propagatesCtEqError, stubMkApi,
    Core.NondetTest.assert, Bind.bind, StateT.run, pure, StateT.pure] at h0
  cases h0.1.1

example : ¬ Core.AllPass (test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered
    (fun ops => { stubMkApi ops with verifyHmacSha256 := fun _ _ _ => pure (.ok true) })) := by
  intro h
  have h0 := h {} (by decide) ByteArray.empty ByteArray.empty validDigest32 (by decide)
  dsimp [test_cryptohash_verifyHmacSha256_matchesTagAndRejectsTampered, stubMkApi, mockRawOps,
    Core.NondetTest.assert, Bind.bind, StateT.run, StateT.bind, StateT.get, StateT.set, pure, StateT.pure] at h0
  exact absurd h0.1.1 (by decide)

example : ¬ Core.AllPass (test_cryptohash_toHex_formatAndRoundTrip
    { stubCryptoHashApi with toHex := fun _ => "BAD" }) := by
  intro h
  have h0 := h validDigest32 (by decide)
  dsimp [test_cryptohash_toHex_formatAndRoundTrip, validDigest32, zeros32,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1 (by decide)

example : ¬ Core.AllPass (test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips
    { stubCryptoHashApi with
      toHex := fun _ => String.ofList (List.replicate 64 'a')
      fromHex := fun alg s =>
        if s == String.ofList (List.replicate 64 'a') then .ok { alg, bytes := zeros32 }
        else .error { kind := .invalidHex, message := "lowercase only" } }) := by
  intro h
  have h0 := h validDigest32 (by decide)
  dsimp [test_cryptohash_fromHex_acceptsUppercaseAndRoundTrips, validDigest32, zeros32,
    Core.NondetTest.assert, Bind.bind] at h0
  cases h0.1

example : ¬ Core.AllPass (test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip
    { stubCryptoHashApi with
      fromHex := fun _ _ => .ok { alg := .sha256, bytes := ByteArray.empty } }) := by
  intro h
  have h0 := h .sha256 zeros64Hex
  dsimp [test_cryptohash_fromHex_acceptedImpliesValidAndNormalizedRoundTrip, zeros64Hex,
    Core.NondetTest.assert, Bind.bind] at h0
  exact absurd h0.1.2.1 (by decide)

example : ¬ Core.AllPass (test_cryptohash_fromHex_rejectsNonHexChar
    { stubCryptoHashApi with
      fromHex := fun _ _ => .error { kind := .lengthMismatch, message := "wrong order" } }) := by
  intro h
  have h0 := h .sha256 "zz" 0 (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_cryptohash_fromHex_rejectsOddLengthHex
    { stubCryptoHashApi with
      fromHex := fun _ _ => .error { kind := .lengthMismatch, message := "wrong order" } }) := by
  intro h
  have h0 := h .sha256 "abc" (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_cryptohash_fromHex_rejectsWrongEvenHexLength
    { stubCryptoHashApi with
      fromHex := fun _ _ => .ok validDigest32 }) := by
  intro h
  have h0 := h .sha256 "abcd" (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (empirical_cryptohash_vectorHexRoundTrip
    { stubCryptoHashApi with toHex := fun _ => "0000" }) := by
  intro h
  have hlen : ("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855".length ==
      2 * digestLen .sha256) = true := by decide
  dsimp [empirical_cryptohash_vectorHexRoundTrip, stubCryptoHashApi,
    Core.NondetTest.assert, Bind.bind] at h
  simp [hlen] at h
  exact h

end LeanSwe.CryptoHash
