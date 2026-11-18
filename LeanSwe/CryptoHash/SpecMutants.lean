import Core.NondetTest
import LeanSwe.CryptoHash.Types
import LeanSwe.CryptoHash.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.CryptoHash`. -/

namespace LeanSwe.CryptoHash

open Core (NondetTest)
open Core.NondetTest

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
  simp [stubMkApi, zeros32,
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

example : ¬ Core.AllPass (test_cryptohash_vectorHexRoundTrip
    { stubCryptoHashApi with toHex := fun _ => "0000" }) := by
  intro h
  have hlen : ("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855".length ==
      2 * digestLen .sha256) = true := by decide
  dsimp [test_cryptohash_vectorHexRoundTrip, stubCryptoHashApi,
    Core.NondetTest.assert, Bind.bind] at h
  simp [hlen] at h
  exact h

end LeanSwe.CryptoHash
