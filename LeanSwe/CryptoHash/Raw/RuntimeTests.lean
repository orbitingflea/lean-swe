import Core.Assumptions
import LeanSwe.CryptoHash.Raw.Types
import LeanSwe.CryptoHash.Raw.Interface

namespace LeanSwe.CryptoHash.Raw.RuntimeTests

open LeanSwe.CryptoHash.Raw

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"CryptoHash.Raw runtime test failed: {msg}")

private def byteToHex (b : UInt8) : String :=
  let digits := #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  let hi := digits[(b.toNat >>> 4) &&& 0xF]!
  let lo := digits[b.toNat &&& 0xF]!
  String.ofList [hi, lo]

private def bytesToHex (bs : ByteArray) : String :=
  bs.data.foldl (fun acc b => acc ++ byteToHex b) ""

private def checkDigestHex (alg : HashAlg) (msg : ByteArray) (expectedHex : String) (label : String) : IO Unit := do
  match ← digestRaw alg msg with
  | .error e => throw (IO.userError s!"{label} failed: {e.message}")
  | .ok bs =>
    let got := bytesToHex bs
    assertTrue (got == expectedHex) s!"{label}: expected {expectedHex}, got {got}"

private def checkHmacHex (key msg : ByteArray) (expectedHex : String) (label : String) : IO Unit := do
  match ← hmacSha256Raw key msg with
  | .error e => throw (IO.userError s!"{label} failed: {e.message}")
  | .ok bs =>
    let got := bytesToHex bs
    assertTrue (got == expectedHex) s!"{label}: expected {expectedHex}, got {got}"

/-- Verify `digestRaw .sha256` against FIPS 180-4 test vectors. -/
def assume_cryptohashraw_digestRaw_sha256MatchesFips180Vectors : IO Unit := do
  checkDigestHex .sha256 ByteArray.empty
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    "SHA-256 empty"
  checkDigestHex .sha256 "abc".toUTF8
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    "SHA-256 abc"
  checkDigestHex .sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    "SHA-256 448-bit"

/-- Verify `digestRaw .sha512` against FIPS 180-4 test vectors. -/
def assume_cryptohashraw_digestRaw_sha512MatchesFips180Vectors : IO Unit := do
  checkDigestHex .sha512 ByteArray.empty
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
    "SHA-512 empty"
  checkDigestHex .sha512 "abc".toUTF8
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    "SHA-512 abc"

/-- Verify `hmacSha256Raw` against RFC 4231 vectors and empty-key semantics. -/
def assume_cryptohashraw_hmacSha256Raw_matchesRfc4231AndEmptyKey : IO Unit := do
  checkHmacHex (ByteArray.mk (Array.replicate 20 0x0b)) "Hi There".toUTF8
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
    "RFC 4231 TC1"
  checkHmacHex "Jefe".toUTF8 "what do ya want for nothing?".toUTF8
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
    "RFC 4231 TC2"
  checkHmacHex (ByteArray.mk (Array.replicate 131 0xaa))
    "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
    "RFC 4231 TC6"
  checkHmacHex ByteArray.empty "abc".toUTF8
    "fd7adb152c05ef80dccf50a1fa4c05d5a3ec6da95575fc312ae7c5d091836351"
    "HMAC empty key"

/-- Verify `digestRaw` and `hmacSha256Raw` preserve embedded NUL bytes in keys and messages. -/
def assume_cryptohashraw_digestAndHmac_preserveEmbeddedNulBytes : IO Unit := do
  let m1 := ByteArray.mk #[0x00, 0x61, 0x00]
  let m2 := ByteArray.mk #[0x00, 0x61, 0x01]
  match ← digestRaw .sha256 m1, ← digestRaw .sha256 m2, ← digestRaw .sha256 ByteArray.empty with
  | .ok d1, .ok d2, .ok dEmpty =>
    assertTrue (d1.size == 32 && d1 != d2 && d1 != dEmpty) "digestRaw NUL preservation"
  | _, _, _ => throw (IO.userError "digestRaw failed during NUL preservation check")

  match ← hmacSha256Raw m1 m2, ← hmacSha256Raw m2 m2, ← hmacSha256Raw m1 m1 with
  | .ok h1, .ok h2, .ok h3 =>
    assertTrue (h1.size == 32 && h1 != h2 && h1 != h3) "hmacSha256Raw NUL preservation"
  | _, _, _ => throw (IO.userError "hmacSha256Raw failed during NUL preservation check")

/-- Verify `ctEqualRaw` matches exact byte equality including embedded NUL bytes. -/
def assume_cryptohashraw_ctEqualRaw_matchesByteEquality : IO Unit := do
  let nulMsg := ByteArray.mk #[0x00, 0x61, 0x00]
  match ← ctEqualRaw ByteArray.empty ByteArray.empty with
  | .error e => throw (IO.userError s!"ctEqualRaw empty failed: {e.message}")
  | .ok eq => assertTrue eq "ctEqualRaw empty == empty"
  match ← ctEqualRaw nulMsg nulMsg with
  | .error e => throw (IO.userError s!"ctEqualRaw equal failed: {e.message}")
  | .ok eq => assertTrue eq "ctEqualRaw equal arrays"
  match ← ctEqualRaw nulMsg (ByteArray.mk #[0x00, 0x61, 0x01]) with
  | .error e => throw (IO.userError s!"ctEqualRaw unequal bytes failed: {e.message}")
  | .ok eq => assertTrue (!eq) "ctEqualRaw unequal bytes after NUL"

/-- Verify `digestRaw` and `hmacSha256Raw` match Python `hashlib` and `hmac` over differential inputs. -/
def assume_cryptohashraw_differentialMatchesPythonHashlibAndHmac : IO Unit := do
  let key := ByteArray.mk #[0x00, 0x11, 0x22, 0x00, 0xff]
  let msg := ByteArray.mk #[0x00, 0x61, 0x00, 0x62, 0x00]
  let script :=
    "import hashlib, hmac; " ++
    "k = bytes.fromhex('00112200ff'); " ++
    "m = bytes.fromhex('0061006200'); " ++
    "print(hashlib.sha256(m).hexdigest()); " ++
    "print(hashlib.sha512(m).hexdigest()); " ++
    "print(hmac.new(k, m, hashlib.sha256).hexdigest())"
  let out ← IO.Process.output { cmd := "python3", args := #["-c", script] }
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 differential check failed: {out.stderr}")
  let lines := out.stdout.trimAscii.toString.splitOn "\n" |>.map (fun s => s.trimAscii.toString)
  match lines with
  | [exp256, exp512, expHmac] =>
    checkDigestHex .sha256 msg exp256 "differential SHA-256"
    checkDigestHex .sha512 msg exp512 "differential SHA-512"
    checkHmacHex key msg expHmac "differential HMAC-SHA256"
  | _ => throw (IO.userError s!"unexpected python3 output: {out.stdout}")

/-- Registered assumption verification entries for `LeanSwe.CryptoHash.Raw`. -/
def registeredAssumptions : Array Core.RegisteredAssumption :=
  #[ { specName := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_digestRaw_sha256MatchesFips180Vectors"
       run := assume_cryptohashraw_digestRaw_sha256MatchesFips180Vectors }
   , { specName := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_digestRaw_sha512MatchesFips180Vectors"
       run := assume_cryptohashraw_digestRaw_sha512MatchesFips180Vectors }
   , { specName := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_hmacSha256Raw_matchesRfc4231AndEmptyKey"
       run := assume_cryptohashraw_hmacSha256Raw_matchesRfc4231AndEmptyKey }
   , { specName := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_digestAndHmac_preserveEmbeddedNulBytes"
       run := assume_cryptohashraw_digestAndHmac_preserveEmbeddedNulBytes }
   , { specName := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_ctEqualRaw_matchesByteEquality"
       run := assume_cryptohashraw_ctEqualRaw_matchesByteEquality }
   , { specName := "LeanSwe.CryptoHash.Raw.assume_cryptohashraw_differentialMatchesPythonHashlibAndHmac"
       run := assume_cryptohashraw_differentialMatchesPythonHashlibAndHmac } ]

/-- Verify mocked FFI failure in `digestRaw` produces `.cryptoError` with non-empty message. -/
def err_cryptohashraw_digestRaw_cryptoError : IO Unit := do
  let ops := Internal.mkRawOps
    { digestRaw := fun _ _ => pure (3, 123, "mocked EVP_Q_digest error", ByteArray.empty)
      hmacSha256Raw := fun _ _ => pure (0, 0, "", ByteArray.empty)
      ctEqualRaw := fun _ _ => pure false }
  match ← ops.digestRaw .sha256 ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked digestRaw should fail")
  | .error e =>
    assertTrue (e.kind == .cryptoError && e.opensslCode == some 123 && !e.message.isEmpty)
      "mocked digestRaw returns .cryptoError"

/-- Verify mocked FFI failure in `hmacSha256Raw` produces `.cryptoError` with non-empty message. -/
def err_cryptohashraw_hmacSha256Raw_cryptoError : IO Unit := do
  let ops := Internal.mkRawOps
    { digestRaw := fun _ _ => pure (0, 0, "", ByteArray.empty)
      hmacSha256Raw := fun _ _ => pure (3, 456, "mocked EVP_MAC error", ByteArray.empty)
      ctEqualRaw := fun _ _ => pure false }
  match ← ops.hmacSha256Raw ByteArray.empty ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked hmacSha256Raw should fail")
  | .error e =>
    assertTrue (e.kind == .cryptoError && e.opensslCode == some 456 && !e.message.isEmpty)
      "mocked hmacSha256Raw returns .cryptoError"

/-- Verify `ctEqualRaw` on unequal lengths produces `.lengthMismatch` with non-empty message. -/
def err_cryptohashraw_ctEqualRaw_lengthMismatch : IO Unit := do
  let nulMsg := ByteArray.mk #[0x00, 0x61, 0x00]
  match ← ctEqualRaw nulMsg (ByteArray.mk #[0x00, 0x61]) with
  | .ok _ => throw (IO.userError "ctEqualRaw should reject unequal length")
  | .error e =>
    assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty)
      "ctEqualRaw unequal length rejects with .lengthMismatch"

/-- Registered error-coverage tests for `LeanSwe.CryptoHash.Raw`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_digestRaw_cryptoError"
       mode := .mocked
       run := err_cryptohashraw_digestRaw_cryptoError }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_hmacSha256Raw_cryptoError"
       mode := .mocked
       run := err_cryptohashraw_hmacSha256Raw_cryptoError }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_ctEqualRaw_lengthMismatch"
       mode := .real
       run := err_cryptohashraw_ctEqualRaw_lengthMismatch } ]

/-- Run all runtime verification tests for `LeanSwe.CryptoHash.Raw`. -/
def runAll : IO Unit := do
  let err1 := mapRawError (.invalidArgument "")
  assertTrue (err1.kind == .invalidInput && !err1.message.isEmpty && err1.opensslCode == none)
    "mapRawError invalidArgument"
  let err2 := mapRawError (.opensslError (some 123) "")
  assertTrue (err2.kind == .cryptoError && !err2.message.isEmpty && err2.opensslCode == some 123)
    "mapRawError opensslError"

  let longKey := ByteArray.mk (Array.replicate 131 0xAA)
  match ← hmacSha256Raw longKey "msg".toUTF8 with
  | .error e => throw (IO.userError s!"hmacSha256Raw long key failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "hmacSha256Raw 131-byte key size 32"

  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.CryptoHash.Raw runtime tests"

end LeanSwe.CryptoHash.Raw.RuntimeTests
