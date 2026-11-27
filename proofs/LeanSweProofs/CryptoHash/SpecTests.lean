import Core.NondetTest
import LeanSwe.CryptoHash.Types
import LeanSweProofs.CryptoHash.Model

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

/-- Deterministic mock state for testing and proofs over `RawCryptoHashOpsM (StateM MockCryptoHashState)`. -/
structure MockCryptoHashState where
  /-- Number of `digestRaw` calls observed. -/
  digestCalls : Nat := 0
  /-- Number of `hmacSha256Raw` calls observed. -/
  hmacCalls : Nat := 0
  /-- Number of `ctEqualRaw` calls observed. -/
  ctEqCalls : Nat := 0
  /-- Optional injected error returned by `digestRaw`. -/
  failDigestWith : Option CryptoHashError := none
  /-- Optional injected error returned by `hmacSha256Raw`. -/
  failHmacWith : Option CryptoHashError := none
  /-- Optional injected error returned by `ctEqualRaw`. -/
  failCtEqWith : Option CryptoHashError := none
  /-- Optional corrupted byte length returned by `digestRaw` instead of `digestLen alg`. -/
  corruptDigestLen : Option Nat := none
  /-- Optional corrupted byte length returned by `hmacSha256Raw` instead of `32`. -/
  corruptHmacLen : Option Nat := none
  deriving Repr, BEq, DecidableEq, Inhabited

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

/-- `mkApi Model.modelRawOps` agrees identically with `Model.modelApi` across all 9 `CryptoHashApiM` methods. -/
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
  let implApi := mkApi Model.modelRawOps
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

/-- Pure `ops` (`Model.modelRawOps`) produces `digestLen alg`-byte digests, 32-byte HMAC tags, and matches NIST FIPS 180-4 / RFC 4231 vectors. -/
def test_cryptohash_modelDigestsValidLengthsAndVectors
    {runner} [NondetTest runner] (ops : RawCryptoHashOpsM Id) : runner Unit := do
  let alg ← nondet HashAlg
  let key ← nondet ByteArray
  let msg ← nondet ByteArray
  NondetTest.assert (ops.digestRaw alg msg = .ok (Model.digestBytesModel alg msg))
  NondetTest.assert ((Model.digestBytesModel alg msg).size = digestLen alg)
  NondetTest.assert (ops.hmacSha256Raw key msg = .ok (Model.hmacSha256Bytes key msg))
  NondetTest.assert ((Model.hmacSha256Bytes key msg).size = 32)
  NondetTest.assert (Model.sha256Bytes ByteArray.empty = ByteArray.mk #[
    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
    0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
    0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
    0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55])
  NondetTest.assert (Model.sha256Bytes "abc".toUTF8 = ByteArray.mk #[
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
    0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
    0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
    0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad])
  NondetTest.assert (Model.sha512Bytes ByteArray.empty = ByteArray.mk #[
    0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd,
    0xf1, 0x54, 0x28, 0x50, 0xd6, 0x6d, 0x80, 0x07,
    0xd6, 0x20, 0xe4, 0x05, 0x0b, 0x57, 0x15, 0xdc,
    0x83, 0xf4, 0xa9, 0x21, 0xd3, 0x6c, 0xe9, 0xce,
    0x47, 0xd0, 0xd1, 0x3c, 0x5d, 0x85, 0xf2, 0xb0,
    0xff, 0x83, 0x18, 0xd2, 0x87, 0x7e, 0xec, 0x2f,
    0x63, 0xb9, 0x31, 0xbd, 0x47, 0x41, 0x7a, 0x81,
    0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e])
  NondetTest.assert (Model.sha512Bytes "abc".toUTF8 = ByteArray.mk #[
    0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba,
    0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
    0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2,
    0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
    0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8,
    0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
    0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e,
    0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f])
  NondetTest.assert (Model.hmacSha256Bytes (ByteArray.mk (Array.replicate 20 0x0b)) "Hi There".toUTF8 = ByteArray.mk #[
    0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53,
    0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b, 0xf1, 0x2b,
    0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7,
    0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7])
  NondetTest.assert (Model.hmacSha256Bytes "Jefe".toUTF8 "what do ya want for nothing?".toUTF8 = ByteArray.mk #[
    0x5b, 0xdc, 0xc1, 0x46, 0xbf, 0x60, 0x75, 0x4e,
    0x6a, 0x04, 0x24, 0x26, 0x08, 0x95, 0x75, 0xc7,
    0x5a, 0x00, 0x3f, 0x08, 0x9d, 0x27, 0x39, 0x83,
    0x9d, 0xec, 0x58, 0xb9, 0x64, 0xec, 0x38, 0x43])
  NondetTest.assert (Model.hmacSha256Bytes (ByteArray.mk (Array.replicate 131 0xaa)) "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8 = ByteArray.mk #[
    0x60, 0xe4, 0x31, 0x59, 0x1e, 0xe0, 0xb6, 0x7f,
    0x0d, 0x8a, 0x26, 0xaa, 0xcb, 0xf5, 0xb7, 0x7f,
    0x8e, 0x0b, 0xc6, 0x21, 0x37, 0x28, 0xc5, 0x14,
    0x05, 0x46, 0x04, 0x0f, 0x0e, 0xe3, 0x7f, 0x54])
  NondetTest.assert (Model.hmacSha256Bytes ByteArray.empty ByteArray.empty = ByteArray.mk #[
    0xb6, 0x13, 0x67, 0x9a, 0x08, 0x14, 0xd9, 0xec,
    0x77, 0x2f, 0x95, 0xd7, 0x78, 0xc3, 0x5f, 0xc5,
    0xff, 0x16, 0x97, 0xc4, 0x93, 0x71, 0x56, 0x53,
    0xc6, 0xc7, 0x12, 0x14, 0x42, 0x92, 0xc5, 0xad])

end LeanSwe.CryptoHash
