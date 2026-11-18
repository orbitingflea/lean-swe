import Core.Assumptions
import LeanSwe.CryptoHash.Interface
import LeanSwe.CryptoHash.Raw.Interface

namespace LeanSwe.CryptoHash.RuntimeTests

open LeanSwe.CryptoHash

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"CryptoHash runtime test failed: {msg}")

private def expectOk {α : Type} (res : Except CryptoHashError α) (label : String) : IO α := do
  match res with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"CryptoHash runtime test failed ({label}): {e.message}")

private def hexOfBytes (bs : ByteArray) : String :=
  toHex { alg := if bs.size == 64 then .sha512 else .sha256, bytes := bs }

private def mkPatternBytes (len : Nat) (mul add : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.emptyWithCapacity len
  for i in [:len] do
    arr := arr.push (UInt8.ofNat ((i * mul + add) % 256))
  pure arr

private def repeatByte (len : Nat) (b : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate len b)

private def seqBytes (start count : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.emptyWithCapacity count
  for i in [:count] do
    arr := arr.push (UInt8.ofNat (start + i))
  pure arr

private def runKnownVectors : IO Unit := do
  let s256Empty ← expectOk (← sha256 ByteArray.empty) "sha256 empty"
  assertTrue (s256Empty.bytes.size == 32 && s256Empty.isValid) "sha256 empty valid"
  assertTrue (toHex s256Empty == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    "sha256 empty NIST vector"

  let s256Abc ← expectOk (← sha256 "abc".toUTF8) "sha256 abc"
  assertTrue (toHex s256Abc == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    "sha256 abc NIST vector"
  let h256Abc ← expectOk (← hash .sha256 "abc".toUTF8) "hash .sha256 abc"
  assertTrue (h256Abc == s256Abc) "hash .sha256 agrees with sha256"

  let s256Long ← expectOk (← sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8)
    "sha256 448-bit NIST vector"
  assertTrue (toHex s256Long == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
    "sha256 448-bit NIST vector hex"

  let s512Empty ← expectOk (← sha512 ByteArray.empty) "sha512 empty"
  assertTrue (s512Empty.bytes.size == 64 && s512Empty.isValid) "sha512 empty valid"
  assertTrue (toHex s512Empty == "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
    "sha512 empty NIST vector"

  let s512Abc ← expectOk (← sha512 "abc".toUTF8) "sha512 abc"
  assertTrue (toHex s512Abc == "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
    "sha512 abc NIST vector"
  let h512Abc ← expectOk (← hash .sha512 "abc".toUTF8) "hash .sha512 abc"
  assertTrue (h512Abc == s512Abc) "hash .sha512 agrees with sha512"

  let rfc1 ← expectOk (← hmacSha256 (repeatByte 20 0x0b) "Hi There".toUTF8) "RFC 4231 #1"
  assertTrue (toHex rfc1 == "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
    "RFC 4231 Test Case 1"

  let rfc2 ← expectOk (← hmacSha256 "Jefe".toUTF8 "what do ya want for nothing?".toUTF8) "RFC 4231 #2"
  assertTrue (toHex rfc2 == "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
    "RFC 4231 Test Case 2"

  let rfc3 ← expectOk (← hmacSha256 (repeatByte 20 0xaa) (repeatByte 50 0xdd)) "RFC 4231 #3"
  assertTrue (toHex rfc3 == "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe")
    "RFC 4231 Test Case 3"

  let rfc4 ← expectOk (← hmacSha256 (seqBytes 1 25) (repeatByte 50 0xcd)) "RFC 4231 #4"
  assertTrue (toHex rfc4 == "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b")
    "RFC 4231 Test Case 4"

  let rfc6 ← expectOk
    (← hmacSha256 (repeatByte 131 0xaa) "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8)
    "RFC 4231 #6"
  assertTrue (toHex rfc6 == "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")
    "RFC 4231 Test Case 6"

  let rfc7 ← expectOk
    (← hmacSha256 (repeatByte 131 0xaa)
      "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.".toUTF8)
    "RFC 4231 #7"
  assertTrue (toHex rfc7 == "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2")
    "RFC 4231 Test Case 7"

  let emptyKeyMac ← expectOk (← hmacSha256 ByteArray.empty "abc".toUTF8) "hmac empty key"
  assertTrue (toHex emptyKeyMac == "fd7adb152c05ef80dccf50a1fa4c05d5a3ec6da95575fc312ae7c5d091836351")
    "hmac empty key vector"

  let nulKey := ByteArray.mk #[0x00, 0x61, 0x00]
  let nulMsg := ByteArray.mk #[0x00, 0x62, 0x00]
  let nulMac ← expectOk (← hmacSha256 nulKey nulMsg) "hmac embedded NUL"
  assertTrue (toHex nulMac == "43f367b3c132da89ed42e46efad479ef7a6da8fca69f800c987c6da459cb83f9")
    "hmac embedded NUL vector"
  let truncMac ← expectOk (← hmacSha256 ByteArray.empty ByteArray.empty) "hmac empty/empty"
  assertTrue (nulMac != truncMac) "embedded NUL key/msg not truncated at byte 0"
  let nulHash1 ← expectOk (← sha256 nulMsg) "sha256 embedded NUL"
  let nulHash2 ← expectOk (← sha256 (ByteArray.mk #[0x00, 0x62, 0x01])) "sha256 embedded NUL diff"
  assertTrue (nulHash1 != nulHash2) "sha256 embedded NUL preserved past NUL byte"

private def runVerifyCtAndHexTests : IO Unit := do
  let key := "super-secret-key".toUTF8
  let msg := "payload-with-mac".toUTF8
  let tag ← expectOk (← hmacSha256 key msg) "hmac for verify"
  assertTrue (← expectOk (← verifyHmacSha256 key msg tag) "verify ok") "verifyHmacSha256 accepts valid tag"

  let tampered : Digest := { alg := .sha256, bytes := tag.bytes.set! 0 (tag.bytes[0]! ^^^ 1) }
  assertTrue (!(← expectOk (← verifyHmacSha256 key msg tampered) "verify tampered"))
    "verifyHmacSha256 rejects tampered tag"
  assertTrue (!(← expectOk (← verifyHmacSha256 "wrong-key".toUTF8 msg tag) "verify wrong key"))
    "verifyHmacSha256 rejects wrong key"
  assertTrue (!(← expectOk (← verifyHmacSha256 key "wrong-msg".toUTF8 tag) "verify wrong msg"))
    "verifyHmacSha256 rejects wrong msg"

  let s512Tag ← expectOk (← sha512 msg) "sha512 tag for invalid alg"
  match ← verifyHmacSha256 key msg s512Tag with
  | .ok _ => throw (IO.userError "verifyHmacSha256 accepted .sha512 digest")
  | .error e => assertTrue (e.kind == .invalidInput && !e.message.isEmpty) "verifyHmacSha256 rejects .sha512"

  let shortTag : Digest := { alg := .sha256, bytes := tag.bytes.extract 0 31 }
  match ← verifyHmacSha256 key msg shortTag with
  | .ok _ => throw (IO.userError "verifyHmacSha256 accepted 31-byte digest")
  | .error e => assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty) "verifyHmacSha256 rejects 31-byte tag"

  assertTrue (← expectOk (← ctEq ByteArray.empty ByteArray.empty) "ctEq empty") "ctEq empty == empty"
  assertTrue (← expectOk (← ctEq msg msg) "ctEq refl") "ctEq msg == msg"
  assertTrue (!(← expectOk (← ctEq msg ("payload-with-mad".toUTF8)) "ctEq diff")) "ctEq unequal bytes"
  assertTrue (!(← expectOk (← ctEq msg ("short".toUTF8)) "ctEq diff len")) "ctEq unequal lengths"

  let upperHex := String.ofList ((toHex tag).toList.map Char.toUpper)
  let decoded ← expectOk (fromHex .sha256 upperHex) "fromHex uppercase"
  assertTrue (decoded == tag) "fromHex uppercase roundtrips"

  match fromHex .sha256 "zzzz" with
  | .ok _ => throw (IO.userError "fromHex accepted non-hex")
  | .error e => assertTrue (e.kind == .invalidHex && !e.message.isEmpty) "fromHex non-hex precedence"

  match fromHex .sha256 "abc" with
  | .ok _ => throw (IO.userError "fromHex accepted odd length")
  | .error e => assertTrue (e.kind == .invalidHex && !e.message.isEmpty) "fromHex odd length"

  match fromHex .sha256 "abcd" with
  | .ok _ => throw (IO.userError "fromHex accepted short even hex")
  | .error e => assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty) "fromHex wrong even length"

private def pushUInt32BE (buf : ByteArray) (n : Nat) : ByteArray :=
  buf
    |>.push (UInt8.ofNat ((n / 16777216) % 256))
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat (n % 256))

private def pythonDiffScript : String :=
  "import sys, struct, hashlib, hmac\n" ++
  "data = sys.stdin.buffer.read()\n" ++
  "pos = 0\n" ++
  "while pos < len(data):\n" ++
  "  klen, mlen = struct.unpack('>II', data[pos:pos+8])\n" ++
  "  pos += 8\n" ++
  "  key = data[pos:pos+klen]; pos += klen\n" ++
  "  msg = data[pos:pos+mlen]; pos += mlen\n" ++
  "  s256 = hashlib.sha256(msg).hexdigest()\n" ++
  "  s512 = hashlib.sha512(msg).hexdigest()\n" ++
  "  mac = hmac.new(key, msg, hashlib.sha256).hexdigest()\n" ++
  "  print(f'{s256} {s512} {mac}')\n"

private def runPythonDifferential : IO Unit := do
  let cases : Array (ByteArray × ByteArray) := #[
    (ByteArray.empty, ByteArray.empty),
    ("k".toUTF8, ByteArray.empty),
    (ByteArray.empty, "a".toUTF8),
    (mkPatternBytes 16 7 3, mkPatternBytes 63 13 5),
    (mkPatternBytes 64 11 1, mkPatternBytes 64 17 9),
    (mkPatternBytes 65 19 2, mkPatternBytes 65 23 4),
    (mkPatternBytes 128 29 8, mkPatternBytes 128 31 6),
    (mkPatternBytes 131 37 0, mkPatternBytes 4096 41 13),
    (mkPatternBytes 97 53 11, mkPatternBytes 2097152 67 19)
  ]
  let mut payload := ByteArray.empty
  for (k, m) in cases do
    payload := pushUInt32BE (pushUInt32BE payload k.size) m.size
    payload := payload ++ k ++ m
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-c", pythonDiffScript]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  child.stdin.write payload
  let (_, child) ← child.takeStdin
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let exitCode ← child.wait
  assertTrue (exitCode == 0) s!"python3 differential exited {exitCode}: {err}"
  let lines := out.trimAscii.toString.splitOn "\n" |>.toArray
  assertTrue (lines.size == cases.size) s!"python3 line count mismatch: {lines.size} vs {cases.size}"
  for idx in [:cases.size] do
    let (k, m) := cases[idx]!
    let parts := lines[idx]!.splitOn " "
    assertTrue (parts.length == 3) s!"malformed python output at index {idx}"
    let d256 ← expectOk (← sha256 m) s!"diff sha256 idx {idx}"
    let d512 ← expectOk (← sha512 m) s!"diff sha512 idx {idx}"
    let dmac ← expectOk (← hmacSha256 k m) s!"diff hmac idx {idx}"
    assertTrue (toHex d256 == parts[0]!) s!"diff sha256 mismatch at idx {idx} (len {m.size})"
    assertTrue (toHex d512 == parts[1]!) s!"diff sha512 mismatch at idx {idx} (len {m.size})"
    assertTrue (toHex dmac == parts[2]!) s!"diff hmac mismatch at idx {idx} (len {k.size}/{m.size})"

private def mkFailingCryptoOps : RawCryptoHashOps :=
  let err : CryptoHashError :=
    { kind := .cryptoError, opensslCode := some 789, message := "mocked OpenSSL failure" }
  { mapRawError := Raw.mapRawError
    digestRaw := fun _ _ => pure (.error err)
    hmacSha256Raw := fun _ _ => pure (.error err)
    ctEqualRaw := fun _ _ => pure (.error err) }

/-- Verify mocked OpenSSL failure in `hash` produces `.cryptoError`. -/
def err_cryptohash_hash_cryptoError : IO Unit := do
  let api := Internal.mkApiM mkFailingCryptoOps
  match ← api.hash .sha256 ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked hash should fail")
  | .error e =>
    assertTrue (e.kind == .cryptoError && !e.message.isEmpty) "mocked hash returns .cryptoError"

/-- Verify mocked OpenSSL failure in `sha256` produces `.cryptoError`. -/
def err_cryptohash_sha256_cryptoError : IO Unit := do
  let api := Internal.mkApiM mkFailingCryptoOps
  match ← api.sha256 ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked sha256 should fail")
  | .error e =>
    assertTrue (e.kind == .cryptoError && !e.message.isEmpty) "mocked sha256 returns .cryptoError"

/-- Verify mocked OpenSSL failure in `sha512` produces `.cryptoError`. -/
def err_cryptohash_sha512_cryptoError : IO Unit := do
  let api := Internal.mkApiM mkFailingCryptoOps
  match ← api.sha512 ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked sha512 should fail")
  | .error e =>
    assertTrue (e.kind == .cryptoError && !e.message.isEmpty) "mocked sha512 returns .cryptoError"

/-- Verify mocked OpenSSL failure in `hmacSha256` produces `.cryptoError`. -/
def err_cryptohash_hmacSha256_cryptoError : IO Unit := do
  let api := Internal.mkApiM mkFailingCryptoOps
  match ← api.hmacSha256 ByteArray.empty ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked hmacSha256 should fail")
  | .error e =>
    assertTrue (e.kind == .cryptoError && !e.message.isEmpty) "mocked hmacSha256 returns .cryptoError"

/-- Verify `verifyHmacSha256` rejects non-SHA256 expected digest with `.invalidInput`. -/
def err_cryptohash_verifyHmacSha256_invalidInput : IO Unit := do
  let badAlg : Digest := { alg := .sha512, bytes := repeatByte 64 0x00 }
  match ← verifyHmacSha256 "k".toUTF8 "m".toUTF8 badAlg with
  | .ok _ => throw (IO.userError "verifyHmacSha256 should reject sha512 digest")
  | .error e =>
    assertTrue (e.kind == .invalidInput && !e.message.isEmpty)
      "verifyHmacSha256 non-sha256 returns .invalidInput"

/-- Verify `verifyHmacSha256` rejects non-32-byte expected digest with `.lengthMismatch`. -/
def err_cryptohash_verifyHmacSha256_lengthMismatch : IO Unit := do
  let badLen : Digest := { alg := .sha256, bytes := repeatByte 31 0x00 }
  match ← verifyHmacSha256 "k".toUTF8 "m".toUTF8 badLen with
  | .ok _ => throw (IO.userError "verifyHmacSha256 should reject 31-byte digest")
  | .error e =>
    assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty)
      "verifyHmacSha256 short digest returns .lengthMismatch"

/-- Verify mocked OpenSSL failure in `verifyHmacSha256` produces `.cryptoError`. -/
def err_cryptohash_verifyHmacSha256_cryptoError : IO Unit := do
  let api := Internal.mkApiM mkFailingCryptoOps
  let expected : Digest := { alg := .sha256, bytes := repeatByte 32 0x00 }
  match ← api.verifyHmacSha256 ByteArray.empty ByteArray.empty expected with
  | .ok _ => throw (IO.userError "mocked verifyHmacSha256 should fail")
  | .error e =>
    assertTrue (e.kind == .cryptoError && !e.message.isEmpty)
      "mocked verifyHmacSha256 returns .cryptoError"

/-- Verify `fromHex` rejects non-hex and odd-length strings with `.invalidHex`. -/
def err_cryptohash_fromHex_invalidHex : IO Unit := do
  match fromHex .sha256 "zzzz" with
  | .ok _ => throw (IO.userError "fromHex should reject non-hex characters")
  | .error e =>
    assertTrue (e.kind == .invalidHex && !e.message.isEmpty) "fromHex non-hex returns .invalidHex"
  match fromHex .sha256 "abc" with
  | .ok _ => throw (IO.userError "fromHex should reject odd-length hex")
  | .error e =>
    assertTrue (e.kind == .invalidHex && !e.message.isEmpty) "fromHex odd-length returns .invalidHex"

/-- Verify `fromHex` rejects wrong decoded byte count with `.lengthMismatch`. -/
def err_cryptohash_fromHex_lengthMismatch : IO Unit := do
  match fromHex .sha256 "0011" with
  | .ok _ => throw (IO.userError "fromHex should reject wrong digest byte length")
  | .error e =>
    assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty)
      "fromHex wrong length returns .lengthMismatch"

/-- Registered error-coverage tests for `LeanSwe.CryptoHash`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hash_cryptoError"
       mode := .mocked
       run := err_cryptohash_hash_cryptoError }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha256_cryptoError"
       mode := .mocked
       run := err_cryptohash_sha256_cryptoError }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_sha512_cryptoError"
       mode := .mocked
       run := err_cryptohash_sha512_cryptoError }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_hmacSha256_cryptoError"
       mode := .mocked
       run := err_cryptohash_hmacSha256_cryptoError }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_verifyHmacSha256_invalidInput"
       mode := .real
       run := err_cryptohash_verifyHmacSha256_invalidInput }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_verifyHmacSha256_lengthMismatch"
       mode := .real
       run := err_cryptohash_verifyHmacSha256_lengthMismatch }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_verifyHmacSha256_cryptoError"
       mode := .mocked
       run := err_cryptohash_verifyHmacSha256_cryptoError }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_fromHex_invalidHex"
       mode := .real
       run := err_cryptohash_fromHex_invalidHex }
   , { testName := "LeanSwe.CryptoHash.RuntimeTests.err_cryptohash_fromHex_lengthMismatch"
       mode := .real
       run := err_cryptohash_fromHex_lengthMismatch } ]

/-- Run all runtime verification tests for `LeanSwe.CryptoHash`. -/
def runAll : IO Unit := do
  runKnownVectors
  runVerifyCtAndHexTests
  runPythonDifferential
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.CryptoHash runtime tests"

end LeanSwe.CryptoHash.RuntimeTests
