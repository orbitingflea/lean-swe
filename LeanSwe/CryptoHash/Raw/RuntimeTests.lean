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
  let out ← IO.Process.output {
    cmd := "/usr/bin/python3"
    args := #["-I", "-c", script]
    env := #[("OPENSSL_CONF", some "/dev/null"), ("OPENSSL_MODULES", none), ("PYTHONPATH", none)]
  }
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

/-- Verify mocked invalid-tag status in `digestRaw` produces `.invalidInput`. -/
def err_cryptohashraw_digestRaw_invalidInput : IO Unit := do
  let ops := Internal.mkRawOps
    { digestRaw := fun _ _ => pure (1, 0, "unknown digest algorithm tag", ByteArray.empty)
      hmacSha256Raw := fun _ _ => pure (0, 0, "", ByteArray.empty)
      ctEqualRaw := fun _ _ => pure false }
  match ← ops.digestRaw .sha256 ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked digestRaw invalidInput should fail")
  | .error e =>
    assertTrue (e.kind == .invalidInput && e.opensslCode == none && !e.message.isEmpty)
      "mocked digestRaw returns .invalidInput"

/-- Verify mocked wrong-length digest in `digestRaw` produces `.lengthMismatch`. -/
def err_cryptohashraw_digestRaw_lengthMismatch : IO Unit := do
  let ops := Internal.mkRawOps
    { digestRaw := fun _ _ => pure (0, 0, "", ByteArray.mk #[1, 2, 3])
      hmacSha256Raw := fun _ _ => pure (0, 0, "", ByteArray.empty)
      ctEqualRaw := fun _ _ => pure false }
  match ← ops.digestRaw .sha256 ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked digestRaw lengthMismatch should fail")
  | .error e =>
    assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty)
      "mocked digestRaw returns .lengthMismatch"

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

/-- Verify mocked invalid-input status in `hmacSha256Raw` produces `.invalidInput`. -/
def err_cryptohashraw_hmacSha256Raw_invalidInput : IO Unit := do
  let ops := Internal.mkRawOps
    { digestRaw := fun _ _ => pure (0, 0, "", ByteArray.empty)
      hmacSha256Raw := fun _ _ => pure (1, 0, "invalid hmac argument", ByteArray.empty)
      ctEqualRaw := fun _ _ => pure false }
  match ← ops.hmacSha256Raw ByteArray.empty ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked hmacSha256Raw invalidInput should fail")
  | .error e =>
    assertTrue (e.kind == .invalidInput && e.opensslCode == none && !e.message.isEmpty)
      "mocked hmacSha256Raw returns .invalidInput"

/-- Verify mocked wrong-length tag in `hmacSha256Raw` produces `.lengthMismatch`. -/
def err_cryptohashraw_hmacSha256Raw_lengthMismatch : IO Unit := do
  let ops := Internal.mkRawOps
    { digestRaw := fun _ _ => pure (0, 0, "", ByteArray.empty)
      hmacSha256Raw := fun _ _ => pure (0, 0, "", ByteArray.mk #[1, 2, 3])
      ctEqualRaw := fun _ _ => pure false }
  match ← ops.hmacSha256Raw ByteArray.empty ByteArray.empty with
  | .ok _ => throw (IO.userError "mocked hmacSha256Raw lengthMismatch should fail")
  | .error e =>
    assertTrue (e.kind == .lengthMismatch && !e.message.isEmpty)
      "mocked hmacSha256Raw returns .lengthMismatch"

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
  #[ { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_digestRaw_invalidInput"
       mode := .mocked
       run := err_cryptohashraw_digestRaw_invalidInput }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_digestRaw_lengthMismatch"
       mode := .mocked
       run := err_cryptohashraw_digestRaw_lengthMismatch }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_digestRaw_cryptoError"
       mode := .mocked
       run := err_cryptohashraw_digestRaw_cryptoError }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_hmacSha256Raw_invalidInput"
       mode := .mocked
       run := err_cryptohashraw_hmacSha256Raw_invalidInput }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_hmacSha256Raw_lengthMismatch"
       mode := .mocked
       run := err_cryptohashraw_hmacSha256Raw_lengthMismatch }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_hmacSha256Raw_cryptoError"
       mode := .mocked
       run := err_cryptohashraw_hmacSha256Raw_cryptoError }
   , { testName := "LeanSwe.CryptoHash.Raw.RuntimeTests.err_cryptohashraw_ctEqualRaw_lengthMismatch"
       mode := .real
       run := err_cryptohashraw_ctEqualRaw_lengthMismatch } ]

@[extern "leanswe_cryptohash_digest"]
private opaque rawDirectDigestProbe (algTag : UInt8) (data : @& ByteArray) :
    BaseIO (UInt32 × UInt64 × String × ByteArray)

@[extern "EVP_MD_CTX_copy_ex"]
private opaque osslPushNullErr : USize → USize → BaseIO UInt32

@[extern "ERR_set_mark"]
private opaque osslErrSetMark : BaseIO UInt32

@[extern "ERR_pop_to_mark"]
private opaque osslErrPopToMark : BaseIO UInt32

@[extern "ERR_peek_last_error"]
private opaque osslErrPeekLastError : BaseIO UInt64

@[extern "ERR_peek_error"]
private opaque osslErrPeekError : BaseIO UInt64

@[extern "ERR_get_error"]
private opaque osslErrGetError : BaseIO UInt64

private def drainOsslErrs : IO Unit := do
  for _ in List.range 64 do
    if (← osslErrGetError) == 0 then
      break

private def checkOsslErrQueueIsolation : IO Unit := do
  drainOsslErrs
  match ← digestRaw .sha256 "abc".toUTF8 with
  | .error e => throw (IO.userError s!"digestRaw on empty queue failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "digestRaw empty queue output len"
  assertTrue ((← osslErrPeekError) == 0 && (← osslErrPopToMark) == 0)
    "digestRaw leaves empty queue without mark"

  let rNoMark ← osslPushNullErr 0 0
  assertTrue (rNoMark == 0) "osslPushNullErr no-mark failed as expected"
  let eNoMark ← osslErrPeekLastError
  match ← hmacSha256Raw (ByteArray.mk (Array.replicate 70 0x42)) "msg".toUTF8 with
  | .error e =>
    drainOsslErrs
    throw (IO.userError s!"hmacSha256Raw with no-mark caller err failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "hmacSha256Raw no-mark output len"
  let peekNoMark ← osslErrPeekLastError
  let popNoMark ← osslErrPopToMark
  let remNoMark ← osslErrPeekError
  drainOsslErrs
  assertTrue (peekNoMark == eNoMark && eNoMark != 0 && popNoMark == 0 && remNoMark == 0)
    "hmacSha256Raw preserved unmarked caller error without adding stray mark"

  let r1 ← osslPushNullErr 0 0
  assertTrue (r1 == 0) "osslPushNullErr 1 failed as expected"
  let e1 ← osslErrPeekLastError
  let mkOk ← osslErrSetMark
  assertTrue (mkOk == 1) "ERR_set_mark succeeded"
  let r2 ← osslPushNullErr 0 0
  assertTrue (r2 == 0) "osslPushNullErr 2 failed as expected"
  let e2 ← osslErrPeekLastError
  match ← digestRaw .sha256 "abc".toUTF8 with
  | .error e =>
    drainOsslErrs
    throw (IO.userError s!"digestRaw with caller err queue failed: {e.message}")
  | .ok bs =>
    assertTrue (bs.size == 32) "digestRaw sha256 output len"
  let lastAfter ← osslErrPeekLastError
  if lastAfter != e2 then
    drainOsslErrs
    throw (IO.userError s!"OpenSSL caller mark/queue corrupted across digestRaw: last={lastAfter} expected={e2}")
  let pOk ← osslErrPopToMark
  let eBase ← osslErrGetError
  let rem ← osslErrPeekError
  drainOsslErrs
  assertTrue (pOk == 1 && eBase == e1 && eBase != 0 && rem == 0)
    "OpenSSL caller errors and mark preserved across digestRaw"

  let mut expectedTop : UInt64 := 0
  for _ in List.range 17 do
    let rm ← osslPushNullErr 0 0
    assertTrue (rm == 0) "osslPushNullErr seg failed"
    let mOk ← osslErrSetMark
    assertTrue (mOk == 1) "ERR_set_mark seg succeeded"
  let rTop ← osslPushNullErr 0 0
  assertTrue (rTop == 0) "osslPushNullErr top failed"
  expectedTop ← osslErrPeekLastError
  match ← digestRaw .sha512 "xyz".toUTF8 with
  | .error e =>
    drainOsslErrs
    throw (IO.userError s!"digestRaw with 17+ marks failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 64) "digestRaw 17+ marks output len"
  let topAfter ← osslErrPeekLastError
  let popTop ← osslErrPopToMark
  let mut drainedCount := 0
  for _ in List.range 32 do
    if (← osslErrGetError) == 0 then
      break
    drainedCount := drainedCount + 1
  drainOsslErrs
  assertTrue (topAfter == expectedTop && popTop == 1 && drainedCount == 14)
    "OpenSSL multi-mark queue (max 15 ring entries) preserved across digestRaw"

/-- Run all runtime verification tests for `LeanSwe.CryptoHash.Raw`. -/
def runAll : IO Unit := do
  let err1 := mapRawError (.invalidArgument "")
  assertTrue (err1.kind == .invalidInput && !err1.message.isEmpty && err1.opensslCode == none)
    "mapRawError invalidArgument"
  let err2 := mapRawError (.opensslError (some 123) "")
  assertTrue (err2.kind == .cryptoError && !err2.message.isEmpty && err2.opensslCode == some 123)
    "mapRawError opensslError"

  let (oobSt, oobCode, oobMsg, oobBytes) ← rawDirectDigestProbe 2 ByteArray.empty
  assertTrue (oobSt == 1 && oobCode == 0 && oobBytes.isEmpty && oobMsg == "unknown digest algorithm tag")
    "direct C shim digest rejects algTag=2"
  checkOsslErrQueueIsolation

  let longKey := ByteArray.mk (Array.replicate 131 0xAA)
  match ← hmacSha256Raw longKey "msg".toUTF8 with
  | .error e => throw (IO.userError s!"hmacSha256Raw long key failed: {e.message}")
  | .ok bs => assertTrue (bs.size == 32) "hmacSha256Raw 131-byte key size 32"

  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.CryptoHash.Raw runtime tests"

end LeanSwe.CryptoHash.Raw.RuntimeTests
