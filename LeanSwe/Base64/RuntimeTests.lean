import Core.Assumptions
import LeanSwe.Base64.Interface

namespace LeanSwe.Base64.RuntimeTests

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except Base64Error α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertOkEq
    (actual : Except Base64Error ByteArray) (expected : ByteArray) (msg : String) : IO Unit := do
  let v ← assertOk actual msg
  if !(v == expected) then
    throw (IO.userError
      s!"ASSERTION FAILED: {msg} (got {repr v.data.toList}, expected {repr expected.data.toList})")

private def assertErr (res : Except Base64Error ByteArray)
    (expectedKind : Base64ErrorKind) (expectedOffset : Nat) (msg : String) : IO Unit := do
  match res with
  | .ok v =>
    throw (IO.userError
      s!"ASSERTION FAILED: {msg} (expected error {repr expectedKind}@{expectedOffset}, got {repr v.data.toList})")
  | .error e =>
    if e.kind != expectedKind || e.offset != expectedOffset || e.message == "" then
      throw (IO.userError
        s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expectedKind}@{expectedOffset})")

private def runPython3 (script : String) (stdinData : String) : IO String := do
  let out ← IO.Process.output
    { cmd := "python3"
    , args := #["-c", script]
    }
    (some stdinData)
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 failed (exit={out.exitCode}): {out.stderr}")
  return out.stdout

private def bytesToHex (bs : ByteArray) : String :=
  let hexDigit (n : UInt8) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n.toNat)
    else Char.ofNat ('a'.toNat + (n.toNat - 10))
  String.ofList <| bs.data.toList.flatMap fun b =>
    [hexDigit (UInt8.ofNat (b.toNat >>> 4)), hexDigit (UInt8.ofNat (b.toNat &&& 0x0f))]

private def hexDigitVal? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

private def hexToBytes (s : String) : IO ByteArray := do
  let rec go : List Char → List UInt8 → IO (List UInt8)
    | [], acc => return acc.reverse
    | c1 :: c2 :: rest, acc =>
      match hexDigitVal? c1, hexDigitVal? c2 with
      | some hi, some lo => go rest ((hi * 16 + lo) :: acc)
      | _, _ => throw (IO.userError s!"invalid hex pair: {c1}{c2}")
    | _, _ => throw (IO.userError s!"odd hex length: {s}")
  let bytes ← go s.toList []
  return ByteArray.mk bytes.toArray

private def genBytes (len : Nat) (seed : UInt64) : ByteArray := Id.run do
  let mut state := seed + 1
  let mut out := ByteArray.emptyWithCapacity len
  for _ in [0:len] do
    state := state * 6364136223846793005 + 1442695040888963407
    out := out.push (UInt8.ofNat ((state >>> 24) &&& 0xff).toNat)
  return out

private def testRfc4648Vectors : IO Unit := do
  let vectors : List (String × String) :=
    [ ("", "")
    , ("f", "Zg==")
    , ("fo", "Zm8=")
    , ("foo", "Zm9v")
    , ("foob", "Zm9vYg==")
    , ("fooba", "Zm9vYmE=")
    , ("foobar", "Zm9vYmFy")
    ]
  for (plain, expected) in vectors do
    let bs := plain.toUTF8
    let enc := encode bs
    assertTrue (enc == expected) s!"RFC 4648 encode({repr plain}) got {enc}, expected {expected}"
    assertOkEq (decode expected) bs s!"RFC 4648 decode({repr expected})"
    let encUrl := encodeUrl bs
    assertOkEq (decodeUrl encUrl) bs s!"RFC 4648 url roundtrip({repr plain})"

private def testUrlSafeAndJwtPayloads : IO Unit := do
  let highBytes := ByteArray.mk #[0xfb, 0xff, 0xbe, 0xef, 0x00, 0x3f]
  assertTrue (encode highBytes == "+/++7wA/") s!"standard alphabet mismatch: {encode highBytes}"
  assertTrue (encodeUrl highBytes == "-_--7wA_") s!"urlSafe alphabet mismatch: {encodeUrl highBytes}"
  assertOkEq (decodeUrl "-_--7wA_") highBytes "decodeUrl highBytes"
  assertOkEq (decode "+/++7wA/") highBytes "decode highBytes"

  let jwtHeader := "{\"alg\":\"HS256\",\"typ\":\"JWT\"}".toUTF8
  let jwtPayload := "{\"sub\":\"1234567890\",\"name\":\"John Doe\",\"admin\":true}".toUTF8
  let hdrEnc := encodeUrl jwtHeader
  let payEnc := encodeUrl jwtPayload
  assertTrue (!(hdrEnc.contains '=')) s!"JWT header must not contain '=': {hdrEnc}"
  assertTrue (!(payEnc.contains '=')) s!"JWT payload must not contain '=': {payEnc}"
  assertOkEq (decodeUrl hdrEnc) jwtHeader "decodeUrl JWT header"
  assertOkEq (decodeUrl payEnc) jwtPayload "decodeUrl JWT payload"

private def testStrictAndMalformedCases : IO Unit := do
  assertErr (decode "A") .invalidLength 0 "len % 4 == 1 single char"
  assertErr (decode "AAAAA") .invalidLength 4 "len % 4 == 1 five chars"
  assertErr (decode "A===") .invalidPadding 1 "A=== has 3 padding chars"
  assertErr (decode "Q===") .invalidPadding 1 "Q=== has 3 padding chars"
  assertErr (decode "QQ=A") .invalidPadding 2 "data after padding"
  assertOkEq (decode "QQ==") (ByteArray.mk #[0x41]) "QQ== decodes A"
  assertErr (decode "QQ") .invalidPadding 2 "decode requires padding"
  assertErr (decode "QQ=") .invalidPadding 2 "decode rejects single '=' on 2 data chars"
  assertErr (decode "Qm==") .nonCanonicalEncoding 1 "non-canonical bits on Qm=="
  assertErr (decodeWith { padding := .forbidden } "QQ==") .invalidPadding 2 "forbidden rejects padding"
  assertErr (decodeWith { padding := .optional } "QQ=") .invalidPadding 2 "optional rejects 1 pad on 2 data chars"
  assertOkEq (decodeWith { padding := .optional } "QQ") (ByteArray.mk #[0x41]) "optional accepts unpadded QQ"
  assertOkEq (decodeWith { padding := .forbidden } "QQ") (ByteArray.mk #[0x41]) "forbidden accepts unpadded QQ"
  assertOkEq (decodeUrl "QQ==") (ByteArray.mk #[0x41]) "decodeUrl accepts optional padding"
  assertErr (decode "AR==") .nonCanonicalEncoding 1 "strict AR=="
  assertErr (decodeWith { padding := .optional } "AR") .nonCanonicalEncoding 1 "strict unpadded AR"
  assertErr (decode "QUJ=") .nonCanonicalEncoding 2 "strict QUJ="
  assertErr (decodeWith { padding := .optional } "QUJ") .nonCanonicalEncoding 2 "strict unpadded QUJ"
  assertOkEq (decodeWith { strictCanonicalBits := false } "AR==") (ByteArray.mk #[0x01]) "lax AR=="
  assertOkEq (decodeWith { padding := .optional, strictCanonicalBits := false } "AR") (ByteArray.mk #[0x01]) "lax AR"
  assertOkEq (decodeWith { strictCanonicalBits := false } "QUJ=") (ByteArray.mk #[0x41, 0x42]) "lax QUJ="
  assertOkEq (decodeWith { padding := .optional, strictCanonicalBits := false } "QUJ") (ByteArray.mk #[0x41, 0x42]) "lax QUJ"
  assertErr (decode "ab-_") .invalidCharacter 2 "standard rejects '-'"
  assertErr (decodeUrl "ab+/") .invalidCharacter 2 "urlSafe rejects '+'"
  assertErr (decode "Zm 9v") .invalidCharacter 2 "rejects space"
  assertErr (decode "Zm\n9v") .invalidCharacter 2 "rejects newline"
  assertErr (decode "Zm\x009v") .invalidCharacter 2 "rejects NUL"
  assertErr (decode "Zmé=") .invalidCharacter 2 "rejects non-ASCII"
  assertErr (decode "Zm==9") .invalidPadding 2 "rejects non-trailing padding before invalid length"

private def testDifferentialPython : IO Unit := do
  let mut samples : List ByteArray := []
  for len in [0:65] do
    samples := samples ++ [genBytes len (UInt64.ofNat (len * 131 + 7))]
  samples := samples ++
    [ ByteArray.mk #[0x00]
    , ByteArray.mk #[0xff]
    , ByteArray.mk #[0x00, 0xff]
    , ByteArray.mk #[0xfb, 0xff, 0xbf]
    , genBytes 512 99991
    ]

  let hexLines := samples.map bytesToHex
  let pyEncScript :=
    "import sys, base64\n" ++
    "for line in sys.stdin.read().splitlines():\n" ++
    "  raw = bytes.fromhex(line)\n" ++
    "  std = base64.b64encode(raw).decode('ascii')\n" ++
    "  url = base64.urlsafe_b64encode(raw).decode('ascii').rstrip('=')\n" ++
    "  print(std + ' ' + url)\n"
  let pyEncOut ← runPython3 pyEncScript (String.intercalate "\n" hexLines ++ "\n")
  let pyEncLines := pyEncOut.splitOn "\n" |>.filter (!·.isEmpty)
  assertTrue (pyEncLines.length == samples.length) "python encode line count mismatch"
  for (bs, pyLine) in samples.zip pyEncLines do
    let parts := pyLine.splitOn " "
    assertTrue (parts.length == 2) s!"unexpected python line: {pyLine}"
    let pyStd := parts[0]!
    let pyUrl := parts[1]!
    let leanStd := encode bs
    let leanUrl := encodeUrl bs
    assertTrue (leanStd == pyStd) s!"differential encode mismatch: lean={leanStd} py={pyStd}"
    assertTrue (leanUrl == pyUrl) s!"differential encodeUrl mismatch: lean={leanUrl} py={pyUrl}"
    assertOkEq (decode leanStd) bs "decode(encode(bs)) differential roundtrip"
    assertOkEq (decodeUrl leanUrl) bs "decodeUrl(encodeUrl(bs)) differential roundtrip"
    let paddedUrl := encodeWith { alphabet := .urlSafe, pad := true } bs
    assertOkEq (decodeWith { alphabet := .urlSafe, padding := .optional } paddedUrl) bs
      "decodeWith optional padded url roundtrip"
    assertOkEq (decodeWith { alphabet := .standard, padding := .optional } (encodeWith { pad := false } bs)) bs
      "decodeWith optional unpadded standard roundtrip"

  let malformedAndLaxInputs : List String :=
    [ "", "Zg==", "Zm8=", "Zm9v", "AR==", "QUJ=", "A", "A===", "QQ=A", "Zm 9v"
    , "Zm\t9v", "ab-_", "QQ=", "Q===", "===="
    ]
  assertErr (decodeWith { alphabet := .standard, padding := .required, strictCanonicalBits := false } "Zm9v====")
    .invalidPadding 4
    "RFC 4648 padding: lax decode must reject excess '====' padding after full quantum"
  let pyDecScript :=
    "import sys, base64, binascii, json\n" ++
    "for line in sys.stdin.read().splitlines():\n" ++
    "  s = json.loads(line)\n" ++
    "  try:\n" ++
    "    raw = base64.b64decode(s.encode('ascii'), validate=True)\n" ++
    "    print('OK ' + raw.hex())\n" ++
    "  except (binascii.Error, ValueError):\n" ++
    "    print('ERR')\n"
  let jsonInputs := malformedAndLaxInputs.map fun s =>
    "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\t" "\\t") ++ "\""
  let pyDecOut ← runPython3 pyDecScript (String.intercalate "\n" jsonInputs ++ "\n")
  let pyDecLines := pyDecOut.splitOn "\n" |>.filter (!·.isEmpty)
  assertTrue (pyDecLines.length == malformedAndLaxInputs.length) "python decode line count mismatch"
  let laxOpts : DecodeOptions := { alphabet := .standard, padding := .required, strictCanonicalBits := false }
  for (s, pyRes) in malformedAndLaxInputs.zip pyDecLines do
    let leanRes := decodeWith laxOpts s
    if pyRes.startsWith "OK " then
      let expectedHex := (pyRes.drop 3).toString
      let expectedBytes ← hexToBytes expectedHex
      assertOkEq leanRes expectedBytes s!"differential lax decode({repr s})"
    else
      match leanRes with
      | .error _ => pure ()
      | .ok v =>
        throw (IO.userError s!"differential expected error for {repr s}, got {repr v.data.toList}")

/-- Error test for `decode` returning `.invalidCharacter`. -/
def err_base64_decode_invalidCharacter : IO Unit :=
  assertErr (decode "ab-_") .invalidCharacter 2 "decode rejects '-'"

/-- Error test for `decode` returning `.invalidLength`. -/
def err_base64_decode_invalidLength : IO Unit :=
  assertErr (decode "A") .invalidLength 0 "decode rejects length % 4 == 1"

/-- Error test for `decode` returning `.invalidPadding`. -/
def err_base64_decode_invalidPadding : IO Unit :=
  assertErr (decode "QQ=A") .invalidPadding 2 "decode rejects data after padding"

/-- Error test for `decode` returning `.nonCanonicalEncoding`. -/
def err_base64_decode_nonCanonicalEncoding : IO Unit :=
  assertErr (decode "Qm==") .nonCanonicalEncoding 1 "decode rejects non-canonical padding bits"

/-- Error test for `decodeUrl` returning `.invalidCharacter`. -/
def err_base64_decodeUrl_invalidCharacter : IO Unit :=
  assertErr (decodeUrl "ab+/") .invalidCharacter 2 "decodeUrl rejects '+'"

/-- Error test for `decodeUrl` returning `.invalidLength`. -/
def err_base64_decodeUrl_invalidLength : IO Unit :=
  assertErr (decodeUrl "A") .invalidLength 0 "decodeUrl rejects length % 4 == 1"

/-- Error test for `decodeUrl` returning `.invalidPadding`. -/
def err_base64_decodeUrl_invalidPadding : IO Unit :=
  assertErr (decodeUrl "QQ=A") .invalidPadding 2 "decodeUrl rejects data after padding"

/-- Error test for `decodeUrl` returning `.nonCanonicalEncoding`. -/
def err_base64_decodeUrl_nonCanonicalEncoding : IO Unit :=
  assertErr (decodeUrl "Qm==") .nonCanonicalEncoding 1 "decodeUrl rejects non-canonical padding bits"

/-- Error test for `decodeWith` returning `.invalidCharacter`. -/
def err_base64_decodeWith_invalidCharacter : IO Unit :=
  assertErr (decodeWith { alphabet := .standard } "ab-_") .invalidCharacter 2 "decodeWith rejects '-'"

/-- Error test for `decodeWith` returning `.invalidLength`. -/
def err_base64_decodeWith_invalidLength : IO Unit :=
  assertErr (decodeWith {} "A") .invalidLength 0 "decodeWith rejects length % 4 == 1"

/-- Error test for `decodeWith` returning `.invalidPadding`. -/
def err_base64_decodeWith_invalidPadding : IO Unit :=
  assertErr (decodeWith { padding := .forbidden } "QQ==") .invalidPadding 2 "decodeWith forbidden padding"

/-- Error test for `decodeWith` returning `.nonCanonicalEncoding`. -/
def err_base64_decodeWith_nonCanonicalEncoding : IO Unit :=
  assertErr (decodeWith {} "Qm==") .nonCanonicalEncoding 1 "decodeWith rejects non-canonical padding bits"

/-- Registered error-coverage tests for `LeanSwe.Base64`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decode_invalidCharacter"
     , mode := .real
     , run := err_base64_decode_invalidCharacter }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decode_invalidLength"
     , mode := .real
     , run := err_base64_decode_invalidLength }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decode_invalidPadding"
     , mode := .real
     , run := err_base64_decode_invalidPadding }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decode_nonCanonicalEncoding"
     , mode := .real
     , run := err_base64_decode_nonCanonicalEncoding }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_invalidCharacter"
     , mode := .real
     , run := err_base64_decodeUrl_invalidCharacter }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_invalidLength"
     , mode := .real
     , run := err_base64_decodeUrl_invalidLength }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_invalidPadding"
     , mode := .real
     , run := err_base64_decodeUrl_invalidPadding }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeUrl_nonCanonicalEncoding"
     , mode := .real
     , run := err_base64_decodeUrl_nonCanonicalEncoding }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_invalidCharacter"
     , mode := .real
     , run := err_base64_decodeWith_invalidCharacter }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_invalidLength"
     , mode := .real
     , run := err_base64_decodeWith_invalidLength }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_invalidPadding"
     , mode := .real
     , run := err_base64_decodeWith_invalidPadding }
   , { testName := "LeanSwe.Base64.RuntimeTests.err_base64_decodeWith_nonCanonicalEncoding"
     , mode := .real
     , run := err_base64_decodeWith_nonCanonicalEncoding }
   ]

/-- Run all `LeanSwe.Base64` RFC 4648, edge-case, and Python differential runtime tests. -/
def runAll : IO Unit := do
  testRfc4648Vectors
  testUrlSafeAndJwtPayloads
  testStrictAndMalformedCases
  testDifferentialPython
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Base64 runtime tests"

end LeanSwe.Base64.RuntimeTests
