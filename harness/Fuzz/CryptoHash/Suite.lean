import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import LeanSwe.CryptoHash.Types
import LeanSweProofs.CryptoHash.Model
import LeanSwe.CryptoHash.Interface

namespace Fuzz.CryptoHash

open Fuzz.Common
open LeanSwe.CryptoHash

@[extern "leanswe_cryptohash_digest"]
private opaque rawDigestDirect : UInt8 → @& ByteArray → BaseIO (UInt32 × UInt64 × String × ByteArray)

private def formatByteArrayRepr (bs : ByteArray) : String :=
  let lim := min bs.size 16
  let hex := (bs.extract 0 lim).data.toList.map fun b =>
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let d := fun n : Nat => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [d hi, d lo]
  let suffix := if bs.size > lim then "..." else ""
  s!"bytes[{bs.size}:0x{String.intercalate "" hex}{suffix}]"

private def exceptEq {ε α : Type} [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

private structure CryptoCase where
  key : ByteArray
  msg : ByteArray
  chunks : Array ByteArray
  ctOther : ByteArray
  extraHex : String
  rawErr : CryptoHashRawError
  oobTag : UInt8
  checkPython : Bool
  deriving BEq, DecidableEq

private def reprCryptoCase (c : CryptoCase) : String :=
  let hexLim := min c.extraHex.length 48
  let hexPreview := String.ofList (c.extraHex.toList.take hexLim) ++ (if c.extraHex.length > hexLim then "..." else "")
  let chunkLens := c.chunks.toList.map (·.size)
  s!"CryptoCase(key={formatByteArrayRepr c.key}, msg={formatByteArrayRepr c.msg}, chunks={chunkLens}, ctOther={formatByteArrayRepr c.ctOther}, extraHex={repr hexPreview}, hexLen={c.extraHex.length}, rawErr={repr c.rawErr}, oobTag={c.oobTag})"

private def pyStreamingOracleScript : String :=
  "import sys, struct, hashlib, hmac\n" ++
  "def read_exact(n):\n" ++
  "  buf = bytearray()\n" ++
  "  while len(buf) < n:\n" ++
  "    chunk = sys.stdin.buffer.read(n - len(buf))\n" ++
  "    if not chunk:\n" ++
  "      return None\n" ++
  "    buf.extend(chunk)\n" ++
  "  return bytes(buf)\n" ++
  "def must_read(n):\n" ++
  "  b = read_exact(n)\n" ++
  "  if b is None:\n" ++
  "    sys.exit(0)\n" ++
  "  return b\n" ++
  "def is_ascii_hex(bs):\n" ++
  "  return (len(bs) % 2 == 0) and all((48 <= b <= 57) or (65 <= b <= 70) or (97 <= b <= 102) for b in bs)\n" ++
  "while True:\n" ++
  "  hdr = read_exact(4)\n" ++
  "  if hdr is None:\n" ++
  "    break\n" ++
  "  (klen,) = struct.unpack('>I', hdr)\n" ++
  "  if klen == 0xFFFFFFFF:\n" ++
  "    break\n" ++
  "  key = must_read(klen)\n" ++
  "  nchunks = struct.unpack('>I', must_read(4))[0]\n" ++
  "  h256 = hashlib.sha256()\n" ++
  "  h512 = hashlib.sha512()\n" ++
  "  mac = hmac.new(key, b'', hashlib.sha256)\n" ++
  "  for _ in range(nchunks):\n" ++
  "    clen = struct.unpack('>I', must_read(4))[0]\n" ++
  "    c = must_read(clen)\n" ++
  "    h256.update(c)\n" ++
  "    h512.update(c)\n" ++
  "    mac.update(c)\n" ++
  "  ct_len = struct.unpack('>I', must_read(4))[0]\n" ++
  "  ct_bytes = must_read(ct_len)\n" ++
  "  ct_hex = ct_bytes.hex().encode('ascii')\n" ++
  "  hex_len = struct.unpack('>I', must_read(4))[0]\n" ++
  "  hex_bytes = must_read(hex_len)\n" ++
  "  out = bytearray(h256.digest() + h512.digest() + mac.digest())\n" ++
  "  out.extend(struct.pack('>I', len(ct_hex)))\n" ++
  "  out.extend(ct_hex)\n" ++
  "  if is_ascii_hex(hex_bytes):\n" ++
  "    dec = bytes.fromhex(hex_bytes.decode('ascii'))\n" ++
  "    out.append(1)\n" ++
  "    out.extend(struct.pack('>I', len(dec)))\n" ++
  "    out.extend(dec)\n" ++
  "  else:\n" ++
  "    out.append(0)\n" ++
  "  sys.stdout.buffer.write(out)\n" ++
  "  sys.stdout.buffer.flush()\n"

private def encodeU32BE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((n >>> 24) % 256),
    UInt8.ofNat ((n >>> 16) % 256),
    UInt8.ofNat ((n >>> 8) % 256),
    UInt8.ofNat (n % 256)
  ]

private def decodeU32BE (bs : ByteArray) : Nat :=
  (bs.get! 0).toNat <<< 24 |||
  (bs.get! 1).toNat <<< 16 |||
  (bs.get! 2).toNat <<< 8 |||
  (bs.get! 3).toNat

private def readExact (h : IO.FS.Handle) (need : Nat) : IO ByteArray := do
  let mut acc := ByteArray.empty
  while acc.size < need do
    let rem := need - acc.size
    let part ← h.read (USize.ofNat rem)
    if part.isEmpty then
      return acc
    acc := acc ++ part
  return acc

private structure PyOracle where
  procRef : IO.Ref (Option (IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }))

private structure PyOracleReply where
  sha256 : ByteArray
  sha512 : ByteArray
  hmac : ByteArray
  ctHex : String
  hexDecoded : Option ByteArray

private def spawnPyOracle : IO PyOracle := do
  let proc ← IO.Process.spawn {
    cmd := "/usr/bin/python3"
    args := #["-I", "-u", "-c", pyStreamingOracleScript]
    env := #[("OPENSSL_CONF", some "/dev/null"), ("OPENSSL_MODULES", none), ("PYTHONPATH", none)]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let procRef ← IO.mkRef (some proc)
  return { procRef }

private def reapProc (proc : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }) :
    IO (String × String) := do
  let (_, child) ← proc.takeStdin
  let outTask ← IO.asTask (try let _ ← child.stdout.readToEnd; pure () catch _ => pure ())
  let errTask ← IO.asTask (try child.stderr.readToEnd catch _ => pure "")
  let _ := outTask.get
  let errText ← match errTask.get with
    | .ok s => pure s
    | .error _ => pure ""
  let rc ← try child.wait |>.map (s!"{·}") catch _ => pure "?"
  return (rc, errText)

private def writePyOracleQuery (hIn : IO.FS.Handle) (key : ByteArray) (chunks : Array ByteArray)
    (ctOther : ByteArray) (hexBytes : ByteArray) : IO (Option String) := do
  try
    hIn.write (encodeU32BE key.size)
    if key.size > 0 then
      hIn.write key
    hIn.write (encodeU32BE chunks.size)
    for c in chunks do
      hIn.write (encodeU32BE c.size)
      if c.size > 0 then
        hIn.write c
    hIn.write (encodeU32BE ctOther.size)
    if ctOther.size > 0 then
      hIn.write ctOther
    hIn.write (encodeU32BE hexBytes.size)
    if hexBytes.size > 0 then
      hIn.write hexBytes
    hIn.flush
    pure none
  catch e =>
    pure (some s!"{e}")

private def readPyOracleReply (hOut : IO.FS.Handle) (ctOtherSize hexBytesSize : Nat) :
    IO (Except String PyOracleReply) := do
  let fixed ← readExact hOut 132
  if fixed.size != 132 then
    return .error s!"expected 132 bytes got {fixed.size}"
  let ctHexLen := decodeU32BE (fixed.extract 128 132)
  let expectedCtHexLen := ctOtherSize * 2
  if ctHexLen != expectedCtHexLen then
    return .error s!"ctHexLen={ctHexLen} != expected {expectedCtHexLen}"
  let ctHexBytes ← readExact hOut (ctHexLen + 1)
  if ctHexBytes.size != ctHexLen + 1 then
    return .error s!"expected {ctHexLen + 1} hex bytes got {ctHexBytes.size}"
  let some ctHex := String.fromUTF8? (ctHexBytes.extract 0 ctHexLen)
    | return .error "invalid UTF-8 in ctHex"
  let hexOk := ctHexBytes.get! ctHexLen
  if hexOk != 0 && hexOk != 1 then
    return .error s!"invalid hexOk tag byte {hexOk}"
  let hexDecoded ←
    if hexOk == 1 then
      let hdr4 ← readExact hOut 4
      if hdr4.size != 4 then
        return .error "expected 4-byte decLen"
      let decLen := decodeU32BE hdr4
      let expectedDecLen := hexBytesSize / 2
      if decLen != expectedDecLen then
        return .error s!"decLen={decLen} != expected {expectedDecLen}"
      let decBytes ← readExact hOut decLen
      if decBytes.size != decLen then
        return .error s!"expected {decLen} decoded bytes got {decBytes.size}"
      pure (some decBytes)
    else
      pure none
  return .ok {
    sha256 := fixed.extract 0 32
    sha512 := fixed.extract 32 96
    hmac := fixed.extract 96 128
    ctHex := ctHex
    hexDecoded := hexDecoded
  }

private def queryPyOracle (oracle : PyOracle) (key : ByteArray) (chunks : Array ByteArray)
    (ctOther : ByteArray) (extraHex : String) : IO (Except String PyOracleReply) := do
  let some proc ← oracle.procRef.swap none
    | return .error "PYTHON_ORACLE_EOF: already_reaped"
  let hexBytes := extraHex.toUTF8
  let writeTask ← IO.asTask (writePyOracleQuery proc.stdin key chunks ctOther hexBytes)
  let readRes ← readPyOracleReply proc.stdout ctOther.size hexBytes.size
  let writeErr? ← match writeTask.get with
    | .ok we => pure we
    | .error e => pure (some s!"{e}")
  if let some we := writeErr? then
    let (rcStr, errText) ← reapProc proc
    return .error s!"PYTHON_ORACLE_EOF: write failed ({we}); exit={rcStr} stderr={errText}"
  match readRes with
  | .error detail =>
    let (rcStr, errText) ← reapProc proc
    return .error s!"PYTHON_ORACLE_EOF: {detail}; exit={rcStr} stderr={errText}"
  | .ok rep =>
    oracle.procRef.set (some proc)
    return .ok rep

private def sendOracleShutdown (hIn : IO.FS.Handle) : IO Unit := do
  try
    hIn.write (encodeU32BE 0xFFFFFFFF)
    hIn.flush
  catch _ =>
    pure ()

private def closePyOracleQuiet (oracle : PyOracle) : IO Unit := do
  let some proc ← oracle.procRef.swap none
    | return ()
  sendOracleShutdown proc.stdin
  let _ ← reapProc proc

private def closePyOracle (oracle : PyOracle) : IO Unit := do
  let some proc ← oracle.procRef.swap none
    | return ()
  sendOracleShutdown proc.stdin
  let (rcStr, errText) ← reapProc proc
  if rcStr != "0" then
    throw (IO.userError s!"PYTHON_ORACLE_EXIT rc={rcStr} stderr={errText}")

private def concatChunks (chunks : Array ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) ByteArray.empty

private def containsZeroByte (bs : ByteArray) : Bool := Id.run do
  for i in List.range bs.size do
    if bs.get! i == 0 then
      return true
  return false

private def xorBitAt (bs : ByteArray) (idx : Nat) : ByteArray :=
  if idx < bs.size then
    bs.set! idx (bs.get! idx ^^^ 0x01)
  else
    bs

private def repeatString (unit : String) (count : Nat) : String :=
  String.intercalate "" (List.replicate count unit)

private def asciiSwapCase (s : String) : String := Id.run do
  let mut out : List Char := []
  let mut flip := false
  for c in s.toList do
    if 'a' ≤ c && c ≤ 'f' && flip then
      out := Char.ofNat (c.toNat - 32) :: out
    else
      out := c :: out
    flip := !flip
  return String.ofList out.reverse

private def isAsciiHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def requiredBuckets : Array CoverageBucket := #[
  bucket "sha256" "empty",
  bucket "sha256" "pad_55",
  bucket "sha256" "pad_56",
  bucket "sha256" "pad_64",
  bucket "sha256" "streaming_split",
  bucket "sha256" "embedded_nul",
  bucket "sha256" "large",
  bucket "sha512" "empty",
  bucket "sha512" "pad_111",
  bucket "sha512" "pad_112",
  bucket "sha512" "pad_128",
  bucket "sha512" "streaming_split",
  bucket "sha512" "embedded_nul",
  bucket "sha512" "large",
  bucket "hmacSha256" "empty_key",
  bucket "hmacSha256" "key_le_64",
  bucket "hmacSha256" "key_gt_64",
  bucket "hmacSha256" "streaming_split",
  bucket "hmacSha256" "embedded_nul_key",
  bucket "hmacSha256" "embedded_nul_msg",
  bucket "verifyHmacSha256" "ok_true",
  bucket "verifyHmacSha256" "ok_false",
  bucket "verifyHmacSha256" "err_invalidInput",
  bucket "verifyHmacSha256" "err_lengthMismatch",
  bucket "ctEq" "true_empty",
  bucket "ctEq" "true_nonempty",
  bucket "ctEq" "false_same_len",
  bucket "ctEq" "false_diff_len",
  bucket "raw_digest" "err_alg_tag_oob",
  bucket "fromHex" "ok_roundtrip",
  bucket "fromHex" "ok_mixed_case",
  bucket "fromHex" "err_invalidHex_odd",
  bucket "fromHex" "err_invalidHex_char",
  bucket "fromHex" "err_lengthMismatch",
  bucket "fromHex" "err_large_stack_safe",
  bucket "toHex" "nonstandard_len",
  bucket "mapRawError" "invalidArgument",
  bucket "mapRawError" "invalidHexInput",
  bucket "mapRawError" "lengthError",
  bucket "mapRawError" "opensslError",
  bucket "mapRawError" "userError",
  bucket "python_oracle" "verified"
]

private def cryptoErrKindTag : CryptoHashErrorKind → String
  | .invalidInput => "invalidInput"
  | .invalidHex => "invalidHex"
  | .lengthMismatch => "lengthMismatch"
  | .cryptoError => "cryptoError"

private def logCryptoErr {α : Type} (emitErrHits : Bool) (qualOp : String)
    (res : Except CryptoHashError α) : IO Unit := do
  if emitErrHits then
    if let .error e := res then
      Fuzz.Common.logErrHit qualOp s!"LeanSwe.CryptoHash.CryptoHashErrorKind.{cryptoErrKindTag e.kind}" "real"

private def exceptClass {α : Type} : Except CryptoHashError α → String
  | .ok _ => "ok"
  | .error e => "err." ++ cryptoErrKindTag e.kind

private def expectOkEq {α : Type} [BEq α] (label : String)
    (actual expected : Except CryptoHashError α) : IO (Except String Unit) := do
  match actual, expected with
  | .ok a, .ok b =>
    if a == b then
      return .ok ()
    else
      return .error s!"{label}:ok:ok:.ok value mismatch"
  | .error e1, .error e2 =>
    if e1 == e2 then
      return .ok ()
    else
      return .error s!"{label}:err.{cryptoErrKindTag e2.kind}:err.{cryptoErrKindTag e1.kind}:{repr e1} vs {repr e2}"
  | .ok _, .error e2 =>
    return .error s!"{label}:err.{cryptoErrKindTag e2.kind}:ok:got .ok, expected .error {repr e2}"
  | .error e1, .ok _ =>
    return .error s!"{label}:ok:err.{cryptoErrKindTag e1.kind}:got .error {repr e1}, expected .ok"

private def checkDigestAndOracle (c : CryptoCase) (oracle? : Option PyOracle)
    (tr : CoverageTracker) (emitErrHits : Bool := false) : IO (Except String (CoverageTracker × Option PyOracleReply)) := do
  let mut cov := tr
  let msg := c.msg
  let key := c.key
  let chunks := c.chunks
  let exp256One := Model.digestBytesModel .sha256 msg
  let exp256Stream := Model.sha256Chunks chunks
  if exp256One != exp256Stream then
    return .error s!"sha256 one-shot model != streaming model at len={msg.size}"
  let exp512One := Model.digestBytesModel .sha512 msg
  let exp512Stream := Model.sha512Chunks chunks
  if exp512One != exp512Stream then
    return .error s!"sha512 one-shot model != streaming model at len={msg.size}"
  let expHmacOne := Model.hmacSha256Bytes key msg
  let expHmacStream := Model.hmacSha256Chunks key chunks
  if expHmacOne != expHmacStream then
    return .error s!"hmac one-shot model != streaming model at keyLen={key.size} msgLen={msg.size}"
  let mut pyReply? : Option PyOracleReply := none
  if let some oracle := oracle? then
    let rep ← match ← queryPyOracle oracle key chunks c.ctOther c.extraHex with
      | .error msg => return .error msg
      | .ok r => pure r
    if rep.sha256 != exp256One then
      return .error s!"sha256 Python oracle mismatch at len={msg.size}"
    if rep.sha512 != exp512One then
      return .error s!"sha512 Python oracle mismatch at len={msg.size}"
    if rep.hmac != expHmacOne then
      return .error s!"hmac Python oracle mismatch at keyLen={key.size} msgLen={msg.size}"
    pyReply? := some rep
    cov := cov.record "python_oracle" "verified"
  let h256 ← LeanSwe.CryptoHash.hash .sha256 msg
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.hash" h256
  if let .error e := ← expectOkEq "CryptoHash.hash sha256" h256 (Model.hashModel .sha256 msg) then
    return .error e
  let s256 ← LeanSwe.CryptoHash.sha256 msg
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.sha256" s256
  if let .error e := ← expectOkEq "CryptoHash.sha256" s256 (Model.sha256Model msg) then
    return .error e
  let h512 ← LeanSwe.CryptoHash.hash .sha512 msg
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.hash" h512
  if let .error e := ← expectOkEq "CryptoHash.hash sha512" h512 (Model.hashModel .sha512 msg) then
    return .error e
  let s512 ← LeanSwe.CryptoHash.sha512 msg
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.sha512" s512
  if let .error e := ← expectOkEq "CryptoHash.sha512" s512 (Model.sha512Model msg) then
    return .error e
  let cMac ← LeanSwe.CryptoHash.hmacSha256 key msg
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.hmacSha256" cMac
  if let .error e := ← expectOkEq "CryptoHash.hmacSha256" cMac (Model.hmacSha256Model key msg) then
    return .error e
  let (oobStatus, oobCode, oobMsg, oobBytes) ← rawDigestDirect c.oobTag msg
  if oobStatus != 1 || oobCode != 0 || !oobBytes.isEmpty || oobMsg != "unknown digest algorithm tag" then
    let codeTag := if oobCode == 0 then "code0" else "codeNZ"
    return .error s!"rawDigestDirect:{oobStatus}:{codeTag}:bytes={oobBytes.size} oobTag={c.oobTag} oobCode={oobCode} msg={repr oobMsg}"
  cov := cov.record "raw_digest" "err_alg_tag_oob"
  if msg.size == 0 then
    cov := cov.record "sha256" "empty"
    cov := cov.record "sha512" "empty"
  if msg.size == 55 then cov := cov.record "sha256" "pad_55"
  if msg.size == 56 then cov := cov.record "sha256" "pad_56"
  if msg.size == 64 then cov := cov.record "sha256" "pad_64"
  if msg.size == 111 then cov := cov.record "sha512" "pad_111"
  if msg.size == 112 then cov := cov.record "sha512" "pad_112"
  if msg.size == 128 then cov := cov.record "sha512" "pad_128"
  if (chunks.filter (!·.isEmpty)).size ≥ 2 then
    cov := cov.record "sha256" "streaming_split"
    cov := cov.record "sha512" "streaming_split"
    cov := cov.record "hmacSha256" "streaming_split"
  if containsZeroByte msg then
    cov := cov.record "sha256" "embedded_nul"
    cov := cov.record "sha512" "embedded_nul"
    cov := cov.record "hmacSha256" "embedded_nul_msg"
  if containsZeroByte key then
    cov := cov.record "hmacSha256" "embedded_nul_key"
  if msg.size ≥ 65536 then
    cov := cov.record "sha256" "large"
    cov := cov.record "sha512" "large"
  if key.size == 0 then
    cov := cov.record "hmacSha256" "empty_key"
  else if key.size ≤ 64 then
    cov := cov.record "hmacSha256" "key_le_64"
  else
    cov := cov.record "hmacSha256" "key_gt_64"
  return .ok (cov, pyReply?)

private def checkVerifyAndCtAndHex (c : CryptoCase) (pyReply? : Option PyOracleReply)
    (tr : CoverageTracker) (emitErrHits : Bool := false) : IO (Except String CoverageTracker) := do
  let mut cov := tr
  let tag := Model.hmacSha256Bytes c.key c.msg
  let validDig : Digest := { alg := .sha256, bytes := tag }
  let resValid ← LeanSwe.CryptoHash.verifyHmacSha256 c.key c.msg validDig
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.verifyHmacSha256" resValid
  if let .error e := ← expectOkEq "verify valid" resValid (Model.verifyHmacSha256Model c.key c.msg validDig) then
    return .error e
  if exceptEq resValid (.ok true) then
    cov := cov.record "verifyHmacSha256" "ok_true"
  let tampered0 : Digest := { alg := .sha256, bytes := xorBitAt tag 0 }
  let tamperedMid : Digest := { alg := .sha256, bytes := xorBitAt tag 15 }
  let tamperedEnd : Digest := { alg := .sha256, bytes := xorBitAt tag 31 }
  for (lbl, td) in [("tamper0", tampered0), ("tamperMid", tamperedMid), ("tamperEnd", tamperedEnd)] do
    let rt ← LeanSwe.CryptoHash.verifyHmacSha256 c.key c.msg td
    logCryptoErr emitErrHits "LeanSwe.CryptoHash.verifyHmacSha256" rt
    if let .error e := ← expectOkEq s!"verify {lbl}" rt (Model.verifyHmacSha256Model c.key c.msg td) then
      return .error e
    if exceptEq rt (.ok false) then
      cov := cov.record "verifyHmacSha256" "ok_false"
  let wrongAlg64 : Digest := { alg := .sha512, bytes := ByteArray.mk (Array.replicate 64 0x41) }
  let wrongAlg31 : Digest := { alg := .sha512, bytes := ByteArray.mk (Array.replicate 31 0x41) }
  for (lbl, wd) in [("wrongAlg64", wrongAlg64), ("wrongAlg31", wrongAlg31)] do
    let rw ← LeanSwe.CryptoHash.verifyHmacSha256 c.key c.msg wd
    logCryptoErr emitErrHits "LeanSwe.CryptoHash.verifyHmacSha256" rw
    if let .error e := ← expectOkEq s!"verify {lbl}" rw (Model.verifyHmacSha256Model c.key c.msg wd) then
      return .error e
    if let .error err := rw then
      if err.kind == .invalidInput then
        cov := cov.record "verifyHmacSha256" "err_invalidInput"
  for badSz in [0, 1, 31, 33, 64] do
    let badLenDig : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate badSz 0x42) }
    let rbl ← LeanSwe.CryptoHash.verifyHmacSha256 c.key c.msg badLenDig
    logCryptoErr emitErrHits "LeanSwe.CryptoHash.verifyHmacSha256" rbl
    if let .error e := ← expectOkEq "verify badLen" rbl (Model.verifyHmacSha256Model c.key c.msg badLenDig) then
      return .error e
    if let .error err := rbl then
      if err.kind == .lengthMismatch then
        cov := cov.record "verifyHmacSha256" "err_lengthMismatch"
  let ctPairs : List (ByteArray × ByteArray) := [
    (ByteArray.empty, ByteArray.empty),
    (c.msg, c.msg),
    (c.msg, xorBitAt c.msg 0),
    (c.msg, if c.msg.size > 0 then xorBitAt c.msg (c.msg.size / 2) else ByteArray.mk #[0]),
    (c.msg, if c.msg.size > 0 then xorBitAt c.msg (c.msg.size - 1) else ByteArray.mk #[1, 2]),
    (c.msg, c.ctOther)
  ]
  for (a, b) in ctPairs do
    let rCt ← LeanSwe.CryptoHash.ctEq a b
    logCryptoErr emitErrHits "LeanSwe.CryptoHash.ctEq" rCt
    if let .error e := ← expectOkEq "ctEq" rCt (Model.ctEqModel a b) then
      return .error e
    if a.size == b.size then
      if a == b then
        if a.size == 0 then
          cov := cov.record "ctEq" "true_empty"
        else
          cov := cov.record "ctEq" "true_nonempty"
      else
        cov := cov.record "ctEq" "false_same_len"
    else
      cov := cov.record "ctEq" "false_diff_len"
  let dig512 : Digest := { alg := .sha512, bytes := Model.digestBytesModel .sha512 c.msg }
  for dig in [validDig, dig512] do
    let hex := LeanSwe.CryptoHash.toHex dig
    if hex != Model.toHexModel dig then
      return .error "toHex != toHexModel"
    let rt := LeanSwe.CryptoHash.fromHex dig.alg hex
    logCryptoErr emitErrHits "LeanSwe.CryptoHash.fromHex" rt
    if !exceptEq rt (Model.fromHexModel dig.alg hex) || !exceptEq rt (.ok dig) then
      return .error s!"fromHex roundtrip mismatch for alg={repr dig.alg}"
    cov := cov.record "fromHex" "ok_roundtrip"
    let mixed := asciiSwapCase hex
    let rMix := LeanSwe.CryptoHash.fromHex dig.alg mixed
    logCryptoErr emitErrHits "LeanSwe.CryptoHash.fromHex" rMix
    if !exceptEq rMix (Model.fromHexModel dig.alg mixed) || !exceptEq rMix (.ok dig) then
      return .error s!"fromHex mixed-case mismatch for alg={repr dig.alg}"
    cov := cov.record "fromHex" "ok_mixed_case"
  let nonStdDig : Digest := { alg := .sha256, bytes := c.ctOther }
  let nonStdHex := LeanSwe.CryptoHash.toHex nonStdDig
  if nonStdHex != Model.toHexModel nonStdDig then
    return .error "toHex non-standard digest != toHexModel"
  let keyAs512 : Digest := { alg := .sha512, bytes := c.key }
  if LeanSwe.CryptoHash.toHex keyAs512 != Model.toHexModel keyAs512 then
    return .error "toHex key-length digest != toHexModel"
  if c.ctOther.size != 32 then
    cov := cov.record "toHex" "nonstandard_len"
  if let some pyRep := pyReply? then
    if nonStdHex != pyRep.ctHex then
      return .error s!"toHex Python mismatch: got {nonStdHex} vs {pyRep.ctHex}"
  let rExtra256 := LeanSwe.CryptoHash.fromHex .sha256 c.extraHex
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.fromHex" rExtra256
  let mExtra256 := Model.fromHexModel .sha256 c.extraHex
  if !exceptEq rExtra256 mExtra256 then
    return .error s!"fromHex sha256 extraHex:{exceptClass mExtra256}:{exceptClass rExtra256}:len={c.extraHex.length}"
  let rExtra512 := LeanSwe.CryptoHash.fromHex .sha512 c.extraHex
  logCryptoErr emitErrHits "LeanSwe.CryptoHash.fromHex" rExtra512
  let mExtra512 := Model.fromHexModel .sha512 c.extraHex
  if !exceptEq rExtra512 mExtra512 then
    return .error s!"fromHex sha512 extraHex:{exceptClass mExtra512}:{exceptClass rExtra512}:len={c.extraHex.length}"
  if let some pyRep := pyReply? then
    for (alg, res) in [(.sha256, rExtra256), (.sha512, rExtra512)] do
      let needLen := digestLen alg
      match pyRep.hexDecoded, res with
      | none, .error e =>
        if e.kind != .invalidHex then
          return .error s!"fromHex_Py_invalidHex.{repr alg}:err.invalidHex:err.{cryptoErrKindTag e.kind}: got {repr e.kind}"
      | some pyDec, .ok dig =>
        if dig.bytes != pyDec || pyDec.size != needLen then
          return .error s!"fromHex_Py_ok.{repr alg}:ok:ok: decoded bytes mismatch"
      | some pyDec, .error e =>
        if pyDec.size == needLen || e.kind != .lengthMismatch then
          return .error s!"fromHex_Py_len.{repr alg}:lengthMismatch:err.{cryptoErrKindTag e.kind}: decLen={pyDec.size} got {repr e}"
      | none, .ok _ =>
        return .error s!"fromHex_Py_invalidHex.{repr alg}:err.invalidHex:ok: succeeded when Python rejected non-hex"
  for res in [rExtra256, rExtra512] do
    match res with
    | .error e =>
      if e.kind == .invalidHex then
        if c.extraHex.length % 2 == 1 && c.extraHex.toList.all isAsciiHexChar then
          cov := cov.record "fromHex" "err_invalidHex_odd"
        else
          cov := cov.record "fromHex" "err_invalidHex_char"
      else if e.kind == .lengthMismatch then
        cov := cov.record "fromHex" "err_lengthMismatch"
        if c.extraHex.length ≥ 250000 then
          cov := cov.record "fromHex" "err_large_stack_safe"
    | .ok _ => pure ()
  let mapBucket := match c.rawErr with
    | .invalidArgument _ => "invalidArgument"
    | .invalidHexInput _ => "invalidHexInput"
    | .lengthError _ _ _ => "lengthError"
    | .opensslError _ _ => "opensslError"
    | .userError _ => "userError"
  let rMap := LeanSwe.CryptoHash.mapRawError c.rawErr
  if rMap != Model.mapRawErrorModel c.rawErr then
    return .error s!"mapRawError.{mapBucket}:ok:ok: mismatch on {repr c.rawErr}"
  cov := cov.record "mapRawError" mapBucket
  return .ok cov

private def execCase (oracle? : Option PyOracle) (injectBug : Option (CryptoCase → Bool))
    (c : CryptoCase) (tr : CoverageTracker) (emitErrHits : Bool := false) : IO (Except String CoverageTracker) := do
  if let some pred := injectBug then
    if pred c then
      return .error "INJECTED_CRYPTO_FAULT"
  let pyArg := if c.checkPython then oracle? else none
  match ← checkDigestAndOracle c pyArg tr emitErrHits with
  | .error msg => return .error msg
  | .ok (tr1, pyRep?) => checkVerifyAndCtAndHex c pyRep? tr1 emitErrHits

private def execBatch (oracle? : Option PyOracle) (injectBug : Option (CryptoCase → Bool))
    (cases : Array CryptoCase) (emitErrHits : Bool := false) : IO (Except String CoverageTracker) := do
  let mut tr := CoverageTracker.empty
  for c in cases do
    match ← execCase oracle? injectBug c tr emitErrHits with
    | .error msg => return .error msg
    | .ok nextTr => tr := nextTr
  return .ok tr

private def genByteArrayPattern (rng : Rng) (len : Nat) : ByteArray × Rng := Id.run do
  let (mode, r1) := rng.nextRange 0 7
  if len == 0 then
    return (ByteArray.empty, r1)
  if mode == 0 then
    return (ByteArray.mk (Array.replicate len 0), r1)
  if mode == 1 then
    return (ByteArray.mk (Array.replicate len 0xff), r1)
  if mode == 2 then
    return (ByteArray.mk (Array.replicate len 0x80), r1)
  if mode == 3 then
    let (bs, r2) := r1.nextBytes len
    let mid := bs.size / 2
    let bs1 := (bs.set! 0 0).set! (bs.size - 1) 0
    return (bs1.set! mid 0, r2)
  return r1.nextBytes len

private def splitIntoChunks (rng : Rng) (msg : ByteArray) : Array ByteArray × Rng := Id.run do
  let (mode, r1) := rng.nextNat 5
  if mode == 0 then
    return (#[msg], r1)
  if mode == 1 then
    return (#[ByteArray.empty, msg, ByteArray.empty], r1)
  if mode == 2 && msg.size ≤ 32 then
    let mut out := #[ByteArray.empty]
    for i in List.range msg.size do
      out := out.push (msg.extract i (i + 1))
    out := out.push ByteArray.empty
    return (out, r1)
  if mode == 3 then
    let cuts : Array Nat := #[0, 55, 56, 63, 64, 111, 112, 127, 128]
    let mut out : Array ByteArray := #[]
    let mut prev := 0
    for cut in cuts do
      if prev < cut && cut < msg.size then
        out := out.push (msg.extract prev cut)
        prev := cut
    out := out.push (msg.extract prev msg.size)
    return (out, r1)
  let (nSplits, r2) := r1.nextRange 1 16
  let mut cur := r2
  let mut out : Array ByteArray := Array.mkEmpty (nSplits + 1)
  let mut off := 0
  for i in List.range nSplits do
    let rem := msg.size - off
    if rem == 0 then
      out := out.push ByteArray.empty
    else
      let (take, nxt) := cur.nextRange 0 rem
      cur := nxt
      out := out.push (msg.extract off (off + take))
      off := off + take
    let _ := i
  out := out.push (msg.extract off msg.size)
  return (out, cur)

private def padBoundaryLengths : Array Nat := #[55, 56, 64, 111, 112, 128]

private def boundaryLengths : Array Nat := #[
  0, 1, 31, 32, 33, 54, 55, 56, 57, 62, 63, 64, 65,
  110, 111, 112, 113, 119, 120, 126, 127, 128, 129, 131,
  239, 240, 255, 256, 257
]

private def hexAlphabet : Array Char := #[
  '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
  'a', 'b', 'c', 'd', 'e', 'f', 'A', 'B', 'C', 'D', 'E', 'F'
]

private def nonHexChars : Array Char := #[
  'g', 'G', 'z', '/', ':', '@', '[', '`', '{', ' ', '\t', '\n', '\x00', '０'
]

private def genRandomHexChars (rng : Rng) (len : Nat) : Array Char × Rng := Id.run do
  let mut cur := rng
  let mut cs := Array.mkEmpty len
  for _ in List.range len do
    let (ch, nxt) := cur.choose hexAlphabet '0'
    cur := nxt
    cs := cs.push ch
  return (cs, cur)

private def genRandomUtf8String (rng : Rng) (maxBytes : Nat) : String × Rng := Id.run do
  let (len, r1) := rng.nextRange 0 maxBytes
  let (bs, r2) := r1.nextBytes len
  match String.fromUTF8? bs with
  | some s => return (s, r2)
  | none =>
    let ascii := ByteArray.mk (bs.data.map fun b => UInt8.ofNat (32 + (b.toNat % 95)))
    return (String.fromUTF8! ascii, r2)

private def genHexString (rng : Rng) : String × Rng := Id.run do
  let (pick, r1) := rng.nextNat 1000
  if pick ≥ 980 then
    return (repeatString "ab" 150000, r1)
  let (lenPick, r2) := r1.nextNat 100
  let (len, r3) :=
    if lenPick < 50 then
      r2.choose #[0, 1, 2, 3, 62, 63, 64, 65, 66, 126, 127, 128, 129, 130] 64
    else
      r2.nextRange 0 144
  if pick < 300 then
    let (cs, r4) := genRandomHexChars r3 len
    return (String.ofList cs.toList, r4)
  else if pick < 550 then
    let oddLen := if len % 2 == 1 then len else len + 1
    let (cs, r4) := genRandomHexChars r3 oddLen
    return (String.ofList cs.toList, r4)
  else if pick < 850 then
    let evenLen := max 2 (if len % 2 == 0 then len else len + 1)
    let (cs, r4) := genRandomHexChars r3 evenLen
    let (pos, r5) := r4.nextNat cs.size
    let (badCh, r6) := r5.choose nonHexChars 'g'
    return (String.ofList (cs.set! pos badCh).toList, r6)
  else
    return genRandomUtf8String r3 96

private def genCryptoRawError (rng : Rng) : CryptoHashRawError × Rng := Id.run do
  let (kindIdx, r1) := rng.nextNat 5
  let (useEmpty, r2) := r1.chance 1 3
  let (detail, r3) := if useEmpty then ("", r2) else genRandomUtf8String r2 40
  if kindIdx == 0 then
    return (.invalidArgument detail, r3)
  if kindIdx == 1 then
    return (.invalidHexInput detail, r3)
  if kindIdx == 2 then
    let (exp, r4) := r3.nextRange 0 128
    let (got, r5) := r4.nextRange 0 128
    return (.lengthError exp got detail, r5)
  if kindIdx == 3 then
    let (hasCode, r4) := r3.nextBool
    let (code, r5) := r4.nextU64
    return (.opensslError (if hasCode then some code else none) detail, r5)
  return (.userError detail, r3)

private def genCryptoCase (rng : Rng) (allowHuge : Bool) : CryptoCase × Rng := Id.run do
  let (pickLen, r1) := rng.nextNat 10000
  let (msgLen, r2) :=
    if pickLen < 6800 then
      r1.choose boundaryLengths 0
    else if pickLen < 8600 then
      r1.choose padBoundaryLengths 55
    else if allowHuge && pickLen ≥ 9994 then
      r1.choose #[524288, 1048576] 524288
    else if pickLen ≥ 9800 then
      (65536, r1)
    else if pickLen ≥ 9750 then
      r1.nextRange 4096 65535
    else if pickLen ≥ 9700 then
      (4096, r1)
    else
      r1.nextRange 0 512
  let (msg, r3) := genByteArrayPattern r2 msgLen
  let (chunks, r4) := splitIntoChunks r3 msg
  let (keyPick, r5) := r4.nextNat 100
  let (keyLen, r6) :=
    if keyPick < 15 then (0, r5)
    else if keyPick < 55 then r5.choose #[1, 20, 32, 63, 64] 32
    else if keyPick < 88 then r5.choose #[65, 128, 131, 256, 512, 1024] 65
    else r5.nextRange 0 2048
  let (key, r7) := genByteArrayPattern r6 keyLen
  let (ctLen, r8) := r7.choose #[0, 1, 31, 32, 33, 64, 65, 96, 128, 256] 31
  let (ctOther, r9) := genByteArrayPattern r8 ctLen
  let (extraHex, r10) := genHexString r9
  let (rawErr, r11) := genCryptoRawError r10
  let (oobNat, r12) := r11.nextRange 2 255
  let checkPython := msg.size ≤ 65536 || (allowHuge && pickLen ≥ 9994)
  let c : CryptoCase := {
    key := key
    msg := msg
    chunks := chunks
    ctOther := ctOther
    extraHex := extraHex
    rawErr := rawErr
    oobTag := UInt8.ofNat oobNat
    checkPython := checkPython
  }
  return (c, r12)

private def warmupCases : Array CryptoCase := #[
  { key := ByteArray.empty
    msg := ByteArray.empty
    chunks := #[ByteArray.empty, ByteArray.empty]
    ctOther := ByteArray.mk #[1]
    extraHex := "abc"
    rawErr := .invalidArgument ""
    oobTag := 2
    checkPython := true },
  { key := "Jefe".toUTF8
    msg := ByteArray.mk (Array.replicate 55 0x61)
    chunks := #[ByteArray.mk (Array.replicate 27 0x61), ByteArray.empty, ByteArray.mk (Array.replicate 28 0x61)]
    ctOther := ByteArray.mk (Array.replicate 32 0x61)
    extraHex := "0g" ++ repeatString "0" 62
    rawErr := .invalidHexInput "bad"
    oobTag := 3
    checkPython := true },
  { key := ByteArray.mk (Array.replicate 64 0x5a)
    msg := ByteArray.mk (#[0x00] ++ Array.replicate 55 0x80)
    chunks := #[ByteArray.mk #[0x00], ByteArray.mk (Array.replicate 55 0x80)]
    ctOther := ByteArray.empty
    extraHex := repeatString "00" 31
    rawErr := .lengthError 32 31 ""
    oobTag := 7
    checkPython := true },
  { key := ByteArray.mk (#[0x00] ++ Array.replicate 64 0x5b)
    msg := ByteArray.mk (Array.replicate 64 0x63)
    chunks := #[ByteArray.mk (Array.replicate 32 0x63), ByteArray.mk (Array.replicate 32 0x63)]
    ctOther := ByteArray.mk #[0xab, 0xcd]
    extraHex := repeatString "00" 64
    rawErr := .invalidArgument "ok"
    oobTag := 5
    checkPython := true },
  { key := ByteArray.mk (Array.replicate 131 0xaa)
    msg := ByteArray.mk (Array.replicate 111 0x42)
    chunks := #[ByteArray.mk (Array.replicate 64 0x42), ByteArray.mk (Array.replicate 47 0x42)]
    ctOther := ByteArray.mk (Array.replicate 64 0x42)
    extraHex := String.ofList ['a', '\x00'] ++ repeatString "0" 62
    rawErr := .opensslError (some 42) "err"
    oobTag := 64
    checkPython := true },
  { key := ByteArray.mk #[0x00, 0xff, 0x00]
    msg := ByteArray.mk (Array.replicate 112 0x00)
    chunks := #[ByteArray.mk (Array.replicate 56 0x00), ByteArray.mk (Array.replicate 56 0x00)]
    ctOther := ByteArray.mk (Array.replicate 33 0x00)
    extraHex := repeatString "00" 65
    rawErr := .userError "x"
    oobTag := 128
    checkPython := true },
  { key := ByteArray.mk (Array.replicate 20 0x0b)
    msg := ByteArray.mk (Array.replicate 128 0xff)
    chunks := #[ByteArray.mk (Array.replicate 64 0xff), ByteArray.mk (Array.replicate 64 0xff)]
    ctOther := ByteArray.empty
    extraHex := repeatString "ab" 250000
    rawErr := .userError ""
    oobTag := 255
    checkPython := true },
  { key := ByteArray.mk (Array.replicate 32 0x11)
    msg := ByteArray.mk (Array.replicate 65536 0x33)
    chunks := #[ByteArray.mk (Array.replicate 32768 0x33), ByteArray.mk (Array.replicate 32768 0x33)]
    ctOther := ByteArray.mk #[0]
    extraHex := "0"
    rawErr := .opensslError none ""
    oobTag := 9
    checkPython := true }
]

private def shrinkStepSizes (n : Nat) : List Nat := Id.run do
  if n == 0 then
    return []
  let mut steps : Array Nat := #[]
  let mut step := n / 2
  while step > 1 do
    steps := steps.push step
    if n % 2 == 0 && step % 2 == 1 && step + 1 < n then
      steps := steps.push (step + 1)
    step := step / 2
  if n > 2 then
    steps := steps.push 2
  steps := steps.push 1
  return steps.toList.eraseDups

private def shrinkDeleteIntervals (n : Nat) : Array (Nat × Nat) := Id.run do
  let mut ivs : Array (Nat × Nat) := #[]
  if n <= 1 then
    return ivs
  let half := n / 2
  ivs := ivs.push (half, n)
  ivs := ivs.push (0, half)
  if n % 2 == 0 && half % 2 == 1 && half + 1 < n then
    ivs := ivs.push (half + 1, n)
    ivs := ivs.push (0, half - 1)
  if n > 128 then
    for k in [8, 16] do
      for ci in List.range k do
        let s0 := (ci * n) / k
        let e0 := ((ci + 1) * n) / k
        let sEven := s0 - (s0 % 2)
        let eEven := e0 - (e0 % 2)
        if sEven < eEven && eEven - sEven < n then
          ivs := ivs.push (sEven, eEven)
        if s0 < e0 && e0 - s0 < n then
          ivs := ivs.push (s0, e0)
  for step in shrinkStepSizes n do
    if step < n then
      ivs := ivs.push (n - step, n)
      ivs := ivs.push (0, step)
      if step + 1 < n then
        if n ≤ 256 && step == 2 then
          let mut p := 2
          while p + 2 < n do
            ivs := ivs.push (p, p + 2)
            p := p + 2
          for pos in [1 : n - 2] do
            if pos % 2 == 1 then
              ivs := ivs.push (pos, pos + 2)
        else if n ≤ 256 && step == 1 then
          for pos in [1 : n - 1] do
            ivs := ivs.push (pos, pos + 1)
        else
          for qi in [1 : 8] do
            let rawPos := (qi * (n - step)) / 8
            let pos := if step % 2 == 0 then rawPos - (rawPos % 2) else rawPos
            if pos > 0 && pos + step < n then
              ivs := ivs.push (pos, pos + step)
          if step % 2 == 1 then
            ivs := ivs.push (1, 1 + step)
            ivs := ivs.push (n - 1 - step, n - 1)
          else
            if 2 + step < n then
              ivs := ivs.push (2, 2 + step)
            if n - step >= 2 then
              ivs := ivs.push (n - 2 - step, n - 2)
            if n - step >= 4 then
              ivs := ivs.push (n - 4 - step, n - 4)
  return ivs

private def shrinkBytes (bs : ByteArray) : List ByteArray := Id.run do
  let n := bs.size
  if n == 0 then
    return []
  let mut out : Array ByteArray := #[ByteArray.empty]
  if n > 1 then
    for (s, e) in shrinkDeleteIntervals n do
      out := out.push (bs.extract 0 s ++ bs.extract e n)
    if bs.data.any (· != 0) then
      let half := n / 2
      out := out.push (ByteArray.mk (Array.replicate n 0))
      if (bs.extract 0 half).data.any (· != 0) then
        out := out.push (ByteArray.mk (Array.replicate half 0) ++ bs.extract half n)
      if (bs.extract half n).data.any (· != 0) then
        out := out.push (bs.extract 0 half ++ ByteArray.mk (Array.replicate (n - half) 0))
      if n > 64 then
        for ci in List.range 8 do
          let cs := (ci * n) / 8
          let ce := ((ci + 1) * n) / 8
          if cs < ce && (bs.extract cs ce).data.any (· != 0) then
            out := out.push (bs.extract 0 cs ++ ByteArray.mk (Array.replicate (ce - cs) 0) ++ bs.extract ce n)
      if n ≤ 128 then
        for i in List.range n do
          if bs.get! i != 0 then
            out := out.push (bs.set! i 0)
  else if bs.get! 0 != 0 then
    out := out.push (ByteArray.mk #[0])
  return out.toList.eraseDups.filter (· != bs)

private def shrinkString (s : String) : List String := Id.run do
  let bs := s.toUTF8
  if bs.size == s.length then
    let n := bs.size
    if n == 0 then
      return []
    let mut out : Array String := #[""]
    if n > 1 then
      for (st, en) in shrinkDeleteIntervals n do
        if let some str := String.fromUTF8? (bs.extract 0 st ++ bs.extract en n) then
          out := out.push str
    return out.toList.eraseDups.filter (·.length < n)
  let cs := s.toList.toArray
  let n := cs.size
  if n == 0 then
    return []
  let mut out : Array String := #[""]
  if n > 1 then
    for (st, en) in shrinkDeleteIntervals n do
      out := out.push (String.ofList ((cs.extract 0 st).toList ++ (cs.extract en n).toList))
  return out.toList.eraseDups.filter (·.length < n)

private def shrinkChunks (chunks : Array ByteArray) : List (Array ByteArray) := Id.run do
  let mut out : Array (Array ByteArray) := #[]
  if chunks.size > 1 then
    let half := chunks.size / 2
    out := out.push (chunks.extract 0 half)
    out := out.push (chunks.extract half chunks.size)
    let nonEmpty := chunks.filter (!·.isEmpty)
    if nonEmpty.size < chunks.size && nonEmpty.size > 0 then
      out := out.push nonEmpty
    for i in List.range chunks.size do
      out := out.push (chunks.extract 0 i ++ chunks.extract (i + 1) chunks.size)
    for i in List.range (chunks.size - 1) do
      let merged := chunks.extract 0 i ++ #[chunks[i]! ++ chunks[i + 1]!] ++ chunks.extract (i + 2) chunks.size
      out := out.push merged
  for i in List.range chunks.size do
    for b' in shrinkBytes chunks[i]! do
      out := out.push (chunks.set! i b')
  return out.toList

private def shrinkRawErr : CryptoHashRawError → List CryptoHashRawError
  | .invalidArgument d => (shrinkString d).map .invalidArgument
  | .invalidHexInput d => (shrinkString d).map .invalidHexInput
  | .lengthError exp got d =>
    let dCands := (shrinkString d).map (.lengthError exp got)
    let nCands :=
      (if exp > 0 then [.lengthError 0 got d] else []) ++
      (if got > 0 then [.lengthError exp 0 d] else [])
    nCands ++ dCands
  | .opensslError c d =>
    let dCands := (shrinkString d).map (.opensslError c)
    (if c.isSome then [.opensslError none d] else []) ++ dCands
  | .userError d => (shrinkString d).map .userError

private def deleteRangeInChunks (chunks : Array ByteArray) (st en : Nat) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := Array.mkEmpty chunks.size
  let mut pos := 0
  for ch in chunks do
    let chEnd := pos + ch.size
    if en <= pos || st >= chEnd then
      out := out.push ch
    else
      let keepL := if st > pos then st - pos else 0
      let dropR := if en < chEnd then en - pos else ch.size
      out := out.push (ch.extract 0 keepL ++ ch.extract dropR ch.size)
    pos := chEnd
  let nonEmpty := out.filter (!·.isEmpty)
  if chunks.size >= 2 && nonEmpty.size >= 2 then
    return nonEmpty
  if chunks.size >= 2 then
    return out
  return #[concatChunks out]

private def zeroByteInChunks (chunks : Array ByteArray) (idx : Nat) : Array ByteArray := Id.run do
  let mut pos := 0
  for i in List.range chunks.size do
    let ch := chunks[i]!
    if idx < pos + ch.size then
      return chunks.set! i (ch.set! (idx - pos) 0)
    pos := pos + ch.size
  return chunks

private def shrinkCryptoCase (c : CryptoCase) : List CryptoCase :=
  let pyCands := if c.checkPython then [{ c with checkPython := false }] else []
  let keyCands := (shrinkBytes c.key).map fun k => { c with key := k }
  let chunkCands := (shrinkChunks c.chunks).map fun chs =>
    { c with chunks := chs, msg := concatChunks chs }
  let coupledCtCands : List CryptoCase := Id.run do
    if c.msg.size != c.ctOther.size || c.msg.size == 0 then
      return []
    let n := c.msg.size
    let mut out : Array CryptoCase := #[]
    let pushSlice (m ct : ByteArray) (chs : Array ByteArray) (arr : Array CryptoCase) : Array CryptoCase :=
      arr.push { c with msg := m, chunks := chs, ctOther := ct }
    let pushDel (st en : Nat) (arr : Array CryptoCase) : Array CryptoCase :=
      let m := c.msg.extract 0 st ++ c.msg.extract en n
      let ct := c.ctOther.extract 0 st ++ c.ctOther.extract en n
      let chs := if c.chunks.size >= 2 then deleteRangeInChunks c.chunks st en else #[m]
      pushSlice m ct chs arr
    out := pushSlice ByteArray.empty ByteArray.empty (if c.chunks.size >= 2 then #[ByteArray.empty, ByteArray.empty] else #[ByteArray.empty]) out
    if n > 1 then
      for (st, en) in shrinkDeleteIntervals n do
        out := pushDel st en out
      if c.msg.data.any (· != 0) || c.ctOther.data.any (· != 0) then
        let z := ByteArray.mk (Array.replicate n 0)
        let zChs := if c.chunks.size >= 2 then c.chunks.map (fun ch => ByteArray.mk (Array.replicate ch.size 0)) else #[z]
        out := pushSlice z z zChs out
        if n ≤ 128 then
          for i in List.range n do
            if c.msg.get! i != 0 || c.ctOther.get! i != 0 then
              let chs' := if c.chunks.size >= 2 then zeroByteInChunks c.chunks i else #[c.msg.set! i 0]
              out := pushSlice (c.msg.set! i 0) (c.ctOther.set! i 0) chs' out
    else if c.msg.get! 0 != 0 || c.ctOther.get! 0 != 0 then
      let z := ByteArray.mk #[0]
      let chs' := if c.chunks.size >= 2 then zeroByteInChunks c.chunks 0 else #[z]
      out := pushSlice z z chs' out
    return (out.toList.filter (· != c)).eraseDups
  let msgCands :=
    if c.chunks.size <= 1 then []
    else (shrinkBytes c.msg).map fun m => { c with msg := m, chunks := #[m] }
  let ctCands := (shrinkBytes c.ctOther).map fun ct => { c with ctOther := ct }
  let hexCands := (shrinkString c.extraHex).map fun hx => { c with extraHex := hx }
  let rawErrCands := (shrinkRawErr c.rawErr).map fun re => { c with rawErr := re }
  let oobCands := if c.oobTag > 2 then [{ c with oobTag := 2 }] else []
  pyCands ++ keyCands ++ coupledCtCands ++ chunkCands ++ msgCands ++ ctCands ++ hexCands ++ rawErrCands ++ oobCands

private def mismatchKindTag (s : String) : String :=
  let sClean := (s.splitOn " decLen=").headD s
  let parts := sClean.splitOn ":"
  let head :=
    if parts.length >= 4 then
      s!"{parts[0]!}:{parts[1]!}:{parts[2]!}"
    else
      parts.headD sClean
  let s2 := (head.splitOn " at ").headD head
  let s3 := (s2.splitOn " on ").headD s2
  (s3.splitOn " oobTag=").headD s3

private def shrinkCryptoBatchWith (execFn : Array CryptoCase → IO (Except String CoverageTracker))
    (cases : Array CryptoCase) (origMsg : String) : IO (Array CryptoCase × String) := do
  let targetTag := mismatchKindTag origMsg
  let lastErrRef ← IO.mkRef origMsg
  let fails (cand : Array CryptoCase) : IO Bool := do
    match ← execFn cand with
    | .ok _ => return false
    | .error errMsg =>
      if errMsg.startsWith "PYTHON_ORACLE_EOF:" then
        throw (IO.userError s!"CRYPTOHASH_FUZZ_MISMATCH: {errMsg}; original_err={origMsg}")
      if mismatchKindTag errMsg == targetTag then
        lastErrRef.set errMsg
        return true
      return false
  let mut cur ← shrinkTrace fails cases
  for _ in List.range 4 do
    let s1 ← shrinkElements shrinkCryptoCase fails cur
    let s2 ← shrinkTrace fails s1
    if s2 == cur then
      break
    cur := s2
  let finalMsg ← lastErrRef.get
  return (cur, finalMsg)

private def runBatchAndShrink (oracle? : Option PyOracle) (cases : Array CryptoCase) :
    IO CoverageTracker := do
  match ← execBatch oracle? none cases true with
  | .ok tr => return tr
  | .error msg =>
    if msg.startsWith "PYTHON_ORACLE_EOF:" then
      throw (IO.userError s!"CRYPTOHASH_FUZZ_MISMATCH: {msg}")
    let (shrunk, finalMsg) ← shrinkCryptoBatchWith (fun cs => execBatch oracle? none cs false) cases msg
    let labels := shrunk.toList.map reprCryptoCase
    throw (IO.userError s!"CRYPTOHASH_FUZZ_MISMATCH: {finalMsg}; shrunk({shrunk.size})=[{String.intercalate "; " labels}]")

private def smokeRandomBuckets : Array CoverageBucket := #[
  bucket "ctEq" "true_empty",
  bucket "ctEq" "true_nonempty",
  bucket "ctEq" "false_same_len",
  bucket "ctEq" "false_diff_len",
  bucket "raw_digest" "err_alg_tag_oob",
  bucket "verifyHmacSha256" "ok_true",
  bucket "verifyHmacSha256" "ok_false",
  bucket "verifyHmacSha256" "err_invalidInput",
  bucket "verifyHmacSha256" "err_lengthMismatch",
  bucket "python_oracle" "verified",
  bucket "fromHex" "ok_roundtrip",
  bucket "fromHex" "ok_mixed_case"
]

private def checkMockErr {α : Type} (qualOp : String) (expected : CryptoHashErrorKind)
    (res : Except CryptoHashError α) : IO Unit := do
  match res with
  | .error e =>
    if e.kind != expected || e.message.isEmpty then
      throw (IO.userError s!"CRYPTOHASH_MOCK_PROBE_MISMATCH: {qualOp} expected {repr expected}, got {repr e}")
    Fuzz.Common.logErrHit qualOp
      s!"LeanSwe.CryptoHash.CryptoHashErrorKind.{cryptoErrKindTag e.kind}" "mocked"
  | .ok _ =>
    throw (IO.userError s!"CRYPTOHASH_MOCK_PROBE_UNEXPECTED_OK: {qualOp} expected {repr expected}")

private def runMockedRawErrorProbes : IO Unit := do
  let cases : Array (CryptoHashErrorKind × (UInt32 × UInt64 × String × ByteArray)) := #[
    (.invalidInput, (1, 0, "mock invalid argument", ByteArray.empty)),
    (.lengthMismatch, (0, 0, "", ByteArray.mk #[1, 2, 3])),
    (.cryptoError, (3, 123, "mock crypto error", ByteArray.empty))
  ]
  let okTuple : UInt32 × UInt64 × String × ByteArray := (0, 0, "", ByteArray.empty)
  let dummyTag : Digest := { alg := .sha256, bytes := ByteArray.mk (Array.replicate 32 0) }
  for (expected, rawTuple) in cases do
    let dApi := Internal.mkApiFromFfiM
      { digestRaw := fun _ _ => pure rawTuple
        hmacSha256Raw := fun _ _ => pure okTuple
        ctEqualRaw := fun _ _ => pure false }
    checkMockErr "LeanSwe.CryptoHash.hash" expected (← dApi.hash .sha256 ByteArray.empty)
    checkMockErr "LeanSwe.CryptoHash.sha256" expected (← dApi.sha256 ByteArray.empty)
    checkMockErr "LeanSwe.CryptoHash.sha512" expected (← dApi.sha512 ByteArray.empty)
    let hApi := Internal.mkApiFromFfiM
      { digestRaw := fun _ _ => pure okTuple
        hmacSha256Raw := fun _ _ => pure rawTuple
        ctEqualRaw := fun _ _ => pure false }
    checkMockErr "LeanSwe.CryptoHash.hmacSha256" expected (← hApi.hmacSha256 ByteArray.empty ByteArray.empty)
    checkMockErr "LeanSwe.CryptoHash.verifyHmacSha256" expected
      (← hApi.verifyHmacSha256 ByteArray.empty ByteArray.empty dummyTag)

private def runCryptoHashLoop (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
  runMockedRawErrorProbes
  let oracle ← spawnPyOracle
  try
    let smokeTr ← runBatchAndShrink (some oracle) warmupCases
    if isSmoke then
      assertCoverage "cryptohash-warmup" smokeTr requiredBuckets
    let mut randTr := CoverageTracker.empty
    let mut rng := Rng.seed seedVal
    let mut done := 0
    while done < steps do
      let batchLen := min 64 (steps - done)
      let mut batch := Array.mkEmpty batchLen
      for _ in List.range batchLen do
        let (c, nxt) := genCryptoCase rng (!isSmoke)
        rng := nxt
        batch := batch.push c
      let bTr ← runBatchAndShrink (some oracle) batch
      randTr := randTr.merge bTr
      done := done + batchLen
    if isSmoke then
      assertCoverage "cryptohash-smoke-random" randTr smokeRandomBuckets
    let reportTr := if isSmoke then smokeTr.merge randTr else randTr
    if isSmoke || steps ≥ 5000 then
      assertCoverage "cryptohash" reportTr requiredBuckets
    IO.println (reportTr.formatReport "cryptohash")
    IO.println s!"FUZZ_SUMMARY suite=cryptohash steps={steps} seed={seedVal}"
  catch e =>
    closePyOracleQuiet oracle
    throw e
  closePyOracle oracle

/-- Verify trace, byte-suffix/prefix, chunk, hex, and O(log N) >N/2 shrinking on synthetic faults. -/
def runSelfTestShrink (seedVal : UInt64) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x43525950544f5f53)
  let mut batch := Array.mkEmpty 16
  for i in List.range 16 do
    let (c, nxt) := genCryptoCase rng false
    rng := nxt
    if i == 7 then
      let faultKey := ByteArray.mk (Array.replicate 96 0x4b)
      let faultMsg := ByteArray.mk (Array.replicate 131 0x4d)
      batch := batch.push { c with key := faultKey, msg := faultMsg, chunks := #[faultMsg] }
    else
      let safeMsg := ByteArray.mk (Array.replicate (min c.msg.size 32) 0x01)
      batch := batch.push { c with msg := safeMsg, chunks := #[safeMsg] }
  let pred1 (c : CryptoCase) : Bool := c.msg.size ≥ 65 && c.key.size ≥ 65
  let fails1 (cand : Array CryptoCase) : IO Bool := do
    match ← execBatch none (some pred1) cand with
    | .ok _ => return false
    | .error _ => return true
  let shrunkA ← match ← verifyShrinker fails1 batch 1 with
    | .error msg => throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_FAILED: {msg}")
    | .ok s0 => shrinkElements shrinkCryptoCase fails1 s0
  match shrunkA.toList with
  | [c0] =>
    if c0.key.size != 65 || c0.msg.size != 65 then
      throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_FAILED: expected (65, 65) got ({c0.key.size}, {c0.msg.size})")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_FAILED: expected size 1 got {shrunkA.size}")

  let suffixFault : CryptoCase := {
    key := ByteArray.mk #[0x41, 0x42, 0x43, 0x99]
    msg := ByteArray.mk #[0x01, 0x02, 0x03]
    chunks := #[ByteArray.mk #[0x01], ByteArray.mk #[0x02], ByteArray.mk #[0x03]]
    ctOther := ByteArray.empty
    extraHex := "abcdefg"
    rawErr := .userError ""
    oobTag := 2
    checkPython := false
  }
  let pred2 (c : CryptoCase) : Bool :=
    c.key.size ≥ 1 && c.key.get! (c.key.size - 1) == 0x99 &&
    c.chunks.size ≥ 2 && c.extraHex.toList.any (· == 'g')
  let fails2 (cand : Array CryptoCase) : IO Bool := do
    match ← execBatch none (some pred2) cand with
    | .ok _ => return false
    | .error _ => return true
  let shrunkB ← shrinkElements shrinkCryptoCase fails2 #[suffixFault]
  match shrunkB.toList with
  | [c1] =>
    if c1.key != ByteArray.mk #[0x99] || c1.chunks.size != 2 || c1.extraHex != "g" then
      throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_2_FAILED: got key={formatByteArrayRepr c1.key} chunks={c1.chunks.size} hex={repr c1.extraHex}")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_2_FAILED: expected size 1 got {shrunkB.size}")

  let bigChunkA := ByteArray.mk (Array.replicate 32768 0x11)
  let bigChunkB := ByteArray.mk (Array.replicate 32768 0x22)
  let streamFault : CryptoCase := {
    key := ByteArray.empty
    msg := bigChunkA ++ bigChunkB
    chunks := #[bigChunkA, bigChunkB]
    ctOther := ByteArray.empty
    extraHex := ""
    rawErr := .userError ""
    oobTag := 2
    checkPython := false
  }
  let pred3 (c : CryptoCase) : Bool :=
    c.chunks.size ≥ 2 && c.chunks[0]!.size ≥ 1 && c.msg.size ≥ 64
  let trialsRef ← IO.mkRef 0
  let fails3 (cand : Array CryptoCase) : IO Bool := do
    trialsRef.modify (· + 1)
    match ← execBatch none (some pred3) cand with
    | .ok _ => return false
    | .error _ => return true
  let shrunkC ← shrinkElements shrinkCryptoCase fails3 #[streamFault]
  let trials3 ← trialsRef.get
  if trials3 ≥ 1000 then
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_3_FAILED: expected < 1000 trials got {trials3}")
  match shrunkC.toList with
  | [c2] =>
    if c2.chunks.size != 2 || c2.msg.size != 64 then
      throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_3_FAILED: got chunks={c2.chunks.size} msgLen={c2.msg.size}")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_3_FAILED: expected size 1 got {shrunkC.size}")

  let nonPow2Msg := ByteArray.mk (Array.replicate 32768 0x44)
  let nonPow2Fault : CryptoCase := {
    key := ByteArray.empty
    msg := nonPow2Msg
    chunks := #[nonPow2Msg]
    ctOther := ByteArray.empty
    extraHex := ""
    rawErr := .userError ""
    oobTag := 2
    checkPython := false
  }
  let pred4 (c : CryptoCase) : Bool := c.msg.size ≥ 16385
  let trials4Ref ← IO.mkRef 0
  let fails4 (cand : Array CryptoCase) : IO Bool := do
    trials4Ref.modify (· + 1)
    match ← execBatch none (some pred4) cand with
    | .ok _ => return false
    | .error _ => return true
  let shrunkD ← shrinkElements shrinkCryptoCase fails4 #[nonPow2Fault]
  let trials4 ← trials4Ref.get
  if trials4 ≥ 500 then
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_4_FAILED: expected < 500 trials got {trials4}")
  match shrunkD.toList with
  | [c3] =>
    if c3.msg.size != 16385 then
      throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_4_FAILED: expected msgLen=16385 got {c3.msg.size}")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_4_FAILED: expected size 1 got {shrunkD.size}")

  let ctBig := ByteArray.mk (#[0xaa] ++ Array.replicate 1022 0x55 ++ #[0xbb])
  let ctFault : CryptoCase := {
    key := ByteArray.empty
    msg := ctBig
    chunks := #[ctBig]
    ctOther := ctBig
    extraHex := "a" ++ String.ofList (List.replicate 1022 '0') ++ "g"
    rawErr := .userError ""
    oobTag := 2
    checkPython := true
  }
  let decoyHook (cand : Array CryptoCase) : IO (Except String CoverageTracker) := do
    match ← execBatch none none cand with
    | .error msg => return .error msg
    | .ok tr =>
      for c in cand do
        if c.msg.size ≥ 2 && c.msg.get! 0 == 0xaa && c.msg.get! (c.msg.size - 1) == 0xbb &&
           c.ctOther.size ≥ 2 && c.ctOther.get! 0 == 0xaa && c.ctOther.get! (c.ctOther.size - 1) == 0xbb &&
           c.extraHex.startsWith "a" && c.extraHex.endsWith "g" then
          return .error "ctEqualRaw:ok:ok:.ok value mismatch"
        if c.msg.size == 1 && c.ctOther.size == 1 then
          return .error "ctEqualRaw:err.lengthMismatch:ok:got .ok, expected .error lengthMismatch"
      return .ok tr
  let (shrunkCt, finalCtErr) ← shrinkCryptoBatchWith decoyHook #[ctFault] "ctEqualRaw:ok:ok:.ok value mismatch"
  if mismatchKindTag finalCtErr != "ctEqualRaw:ok:ok" then
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_5_FAILED: slipped to {finalCtErr}")
  match shrunkCt.toList with
  | [c4] =>
    if c4.msg != ByteArray.mk #[0xaa, 0xbb] || c4.ctOther != ByteArray.mk #[0xaa, 0xbb] ||
       c4.extraHex != "ag" || c4.checkPython then
      throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_5_FAILED: expected (2,2,\"ag\",false) got ({c4.msg.size},{c4.ctOther.size},{repr c4.extraHex},{c4.checkPython})")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_SHRINK_SELFTEST_5_FAILED: expected size 1 got {shrunkCt.size}")

  let even62Hex := String.ofList (List.replicate 62 'f')
  let even62Case : CryptoCase := { ctFault with msg := ByteArray.empty, chunks := #[ByteArray.empty], ctOther := ByteArray.empty, extraHex := even62Hex, checkPython := false }
  let even62Pred (c : CryptoCase) : Bool :=
    c.extraHex.length > 0 && c.extraHex.length % 2 == 0 && c.extraHex.toList.all (· == 'f')
  let shrunkEven62 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some even62Pred) cand with
    | .ok _ => return false
    | .error _ => return true) #[even62Case]
  match shrunkEven62.toList with
  | [ce] =>
    if ce.extraHex != "ff" then
      throw (IO.userError s!"CRYPTOHASH_EVEN62_SHRINK_FAILED: got {repr ce.extraHex}")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_EVEN62_SHRINK_FAILED: expected size 1 got {shrunkEven62.size}")

  let idx2Bytes := ByteArray.mk #[0xaa, 0xbb, 0x55, 0xcc, 0xdd, 0xee, 0xff]
  let idx2Case : CryptoCase := { even62Case with msg := idx2Bytes, chunks := #[idx2Bytes], extraHex := "" }
  let idx2Pred (c : CryptoCase) : Bool :=
    c.msg.size ≥ 6 && c.msg.get! 0 == 0xaa && c.msg.get! 1 == 0xbb &&
    c.msg.get! (c.msg.size - 3) == 0xdd && c.msg.get! (c.msg.size - 2) == 0xee && c.msg.get! (c.msg.size - 1) == 0xff
  let shrunkIdx2 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some idx2Pred) cand with
    | .ok _ => return false
    | .error _ => return true) #[idx2Case]
  match shrunkIdx2.toList with
  | [ci] =>
    if ci.msg.size != 6 then
      throw (IO.userError s!"CRYPTOHASH_INTERIOR_IDX2_SHRINK_FAILED: got size={ci.msg.size}")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_INTERIOR_IDX2_SHRINK_FAILED: expected size 1 got {shrunkIdx2.size}")

  let pyLenErr : CryptoHashError := { kind := .invalidHex, message := "dummy:msg:with:colons" }
  let t1 := mismatchKindTag s!"fromHex_Py_len.HashAlg.sha256:lengthMismatch:err.invalidHex: decLen=31 got {repr pyLenErr}"
  let t2 := mismatchKindTag s!"fromHex_Py_len.HashAlg.sha256:lengthMismatch:err.invalidHex: decLen=1 got {repr pyLenErr}"
  if t1 != t2 || t1 != "fromHex_Py_len.HashAlg.sha256:lengthMismatch:err.invalidHex" then
    throw (IO.userError s!"CRYPTOHASH_PYLEN_PIN_FAILED: t1={repr t1} t2={repr t2}")

  let eqCtMsg := ByteArray.mk (Array.replicate 64 0x11)
  let eqCtOther := ByteArray.mk (Array.replicate 64 0x22)
  let eqCtCase : CryptoCase := { even62Case with msg := eqCtMsg, chunks := #[eqCtMsg], ctOther := eqCtOther }
  let eqCtPred (c : CryptoCase) : Bool := c.msg.size == c.ctOther.size && c.msg != c.ctOther
  let shrunkEqCt ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some eqCtPred) cand with
    | .ok _ => return false
    | .error _ => return true) #[eqCtCase]
  match shrunkEqCt.toList with
  | [ce] =>
    if ce.msg.size != 1 || ce.ctOther.size != 1 then
      throw (IO.userError s!"CRYPTOHASH_COUPLED_CTEQ_SHRINK_FAILED: got ({ce.msg.size}, {ce.ctOther.size})")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_COUPLED_CTEQ_SHRINK_FAILED: expected size 1 got {shrunkEqCt.size}")

  let hex126 := "aabb" ++ String.ofList (List.replicate 120 '0') ++ "ff"
  let hex126Case : CryptoCase := { even62Case with extraHex := hex126 }
  let hex126Pred (c : CryptoCase) : Bool :=
    c.extraHex.length > 0 && c.extraHex.length % 2 == 0 &&
    c.extraHex.startsWith "aabb" && c.extraHex.endsWith "ff"
  let shrunkHex126 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some hex126Pred) cand with
    | .ok _ => return false
    | .error _ => return true) #[hex126Case]
  match shrunkHex126.toList with
  | [ch] =>
    if ch.extraHex != "aabbff" then
      throw (IO.userError s!"CRYPTOHASH_HEX126_SHRINK_FAILED: got {repr ch.extraHex}")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_HEX126_SHRINK_FAILED: expected size 1 got {shrunkHex126.size}")

  let int126Bytes := ByteArray.mk (#[0xaa, 0xbb] ++ Array.replicate 14 0x99 ++ Array.replicate 110 0xcc)
  let int126Case : CryptoCase := { even62Case with msg := int126Bytes, chunks := #[int126Bytes] }
  let int126Pred (c : CryptoCase) : Bool :=
    c.msg.size ≥ 112 && c.msg.extract 0 2 == ByteArray.mk #[0xaa, 0xbb]
  let shrunkInt126 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some int126Pred) cand with
    | .ok _ => return false
    | .error _ => return true) #[int126Case]
  match shrunkInt126.toList with
  | [ci126] =>
    if ci126.msg.size != 112 then
      throw (IO.userError s!"CRYPTOHASH_INT126_SHRINK_FAILED: got size={ci126.msg.size}")
  | _ =>
    throw (IO.userError s!"CRYPTOHASH_INT126_SHRINK_FAILED: expected size 1 got {shrunkInt126.size}")

  let mapTag1 := mismatchKindTag "mapRawError.invalidArgument:ok:ok: mismatch on Foo.on.at:1"
  let mapTag2 := mismatchKindTag "mapRawError.userError:ok:ok: mismatch on Foo.on.at:1"
  if mapTag1 == mapTag2 || mapTag1 != "mapRawError.invalidArgument:ok:ok" then
    throw (IO.userError s!"CRYPTOHASH_MAP_RAW_PIN_FAILED: t1={repr mapTag1} t2={repr mapTag2}")
  let oobTag1 := mismatchKindTag "rawDigestDirect:0:code0:bytes=0 oobTag=9 oobCode=0 msg=\"x\""
  let oobTag2 := mismatchKindTag "rawDigestDirect:0:code0:bytes=0 oobTag=2 oobCode=0 msg=\"x\""
  if oobTag1 != oobTag2 || oobTag1 != "rawDigestDirect:0:code0" then
    throw (IO.userError s!"CRYPTOHASH_OOB_PIN_FAILED: t1={repr oobTag1} t2={repr oobTag2}")

  let b131 := ByteArray.mk (#[0xaa, 0xbb] ++ Array.replicate 62 0x00 ++ #[0x77, 0x88, 0x99] ++ Array.replicate 61 0x00 ++ #[0xdd, 0xee, 0xff])
  let b131Pred (c : CryptoCase) : Bool :=
    c.msg.size >= 128 && c.msg.get! 0 == 0xaa && c.msg.get! 1 == 0xbb &&
    c.msg.get! (c.msg.size - 3) == 0xdd && c.msg.get! (c.msg.size - 2) == 0xee && c.msg.get! (c.msg.size - 1) == 0xff &&
    Id.run do
      for i in List.range (c.msg.size - 2) do
        if c.msg.get! i == 0x77 && c.msg.get! (i + 1) == 0x88 && c.msg.get! (i + 2) == 0x99 then return true
      return false
  let s131 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some b131Pred) cand with | .ok _ => return false | .error _ => return true)
    #[{ even62Case with msg := b131, chunks := #[b131] }]
  if (match s131.toList with | [x] => x.msg.size | _ => 999) != 128 then
    throw (IO.userError "CRYPTOHASH_B131_SHRINK_FAILED")

  let h134 := "aabb" ++ String.intercalate "" (List.replicate 30 "1e") ++ "ccdd" ++ String.intercalate "" (List.replicate 31 "1e") ++ "eeff"
  let h134Pred (c : CryptoCase) : Bool :=
    c.extraHex.length >= 130 && c.extraHex.length % 2 == 0 &&
    c.extraHex.startsWith "aabb" && c.extraHex.endsWith "eeff" && (c.extraHex.splitOn "ccdd").length >= 2
  let sh134 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some h134Pred) cand with | .ok _ => return false | .error _ => return true)
    #[{ even62Case with extraHex := h134 }]
  if (match sh134.toList with | [x] => x.extraHex.length | _ => 999) != 130 then
    throw (IO.userError "CRYPTOHASH_HEX134_SHRINK_FAILED")

  let k65 := ByteArray.mk (Array.replicate 65 0x4b)
  let k65Pred (c : CryptoCase) : Bool := c.key.size >= 65 && c.key.get! 0 != 0 && c.key.get! (c.key.size - 1) != 0
  let sk65 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some k65Pred) cand with | .ok _ => return false | .error _ => return true)
    #[{ even62Case with key := k65 }]
  let nz65 := match sk65.toList with | [x] => x.key.data.foldl (fun a b => if b != 0 then a + 1 else a) 0 | _ => 999
  if nz65 != 2 then
    throw (IO.userError s!"CRYPTOHASH_K65_ZERO_SHRINK_FAILED: nz={nz65}")

  let eq64 := ByteArray.mk (Array.replicate 64 0xff)
  let eq64Case : CryptoCase := { even62Case with msg := eq64, chunks := #[eq64], ctOther := eq64 }
  let sp0 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some fun c => c.msg == c.ctOther) cand with | .ok _ => return false | .error _ => return true) #[eq64Case]
  if (match sp0.toList with | [x] => (x.msg.size, x.ctOther.size) | _ => (99, 99)) != (0, 0) then
    throw (IO.userError "CRYPTOHASH_COUPLED_EMPTY_SHRINK_FAILED")
  let sp1 ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some fun c => c.msg == c.ctOther && c.msg.size >= 1) cand with | .ok _ => return false | .error _ => return true) #[eq64Case]
  if (match sp1.toList with | [x] => (x.msg, x.ctOther) | _ => (ByteArray.empty, ByteArray.empty)) != (ByteArray.mk #[0], ByteArray.mk #[0]) then
    throw (IO.userError "CRYPTOHASH_COUPLED_ZERO1_SHRINK_FAILED")

  let mcMsg1 := ByteArray.mk (Array.replicate 31 0x11)
  let mcMsg2 := ByteArray.mk (Array.replicate 31 0x22)
  let mcCase : CryptoCase := { even62Case with msg := mcMsg1 ++ mcMsg2, chunks := #[mcMsg1, mcMsg2], ctOther := ByteArray.mk (Array.replicate 62 0x33) }
  let smc ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some fun c => c.chunks.size >= 2 && c.msg.size == c.ctOther.size && c.msg != c.ctOther) cand with
    | .ok _ => return false | .error _ => return true) #[mcCase]
  if (match smc.toList with | [x] => (x.msg.size, x.ctOther.size, x.chunks.size >= 2) | _ => (99, 99, false)) != (1, 1, true) then
    let got := match smc.toList with | [x] => s!"({x.msg.size},{x.ctOther.size},chunks={x.chunks.size})" | _ => s!"len={smc.size}"
    throw (IO.userError s!"CRYPTOHASH_MULTICHUNK_COUPLED_SHRINK_FAILED: got {got}")
  let smcNe ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some fun c => c.chunks.size >= 2 && c.chunks.all (!·.isEmpty) && c.msg.size == c.ctOther.size && c.msg != c.ctOther) cand with
    | .ok _ => return false | .error _ => return true) #[mcCase]
  if (match smcNe.toList with | [x] => (x.msg.size, x.ctOther.size, x.chunks.size >= 2) | _ => (99, 99, false)) != (2, 2, true) then
    let got := match smcNe.toList with | [x] => s!"({x.msg.size},{x.ctOther.size},chunks={x.chunks.size})" | _ => s!"len={smcNe.size}"
    throw (IO.userError s!"CRYPTOHASH_MULTICHUNK_NONEMPTY_COUPLED_SHRINK_FAILED: got {got}")

  let odd33 := ByteArray.mk (#[0xaa] ++ Array.replicate 15 0x00 ++ #[0x77] ++ Array.replicate 15 0x00 ++ #[0xbb])
  let odd33Pred (c : CryptoCase) : Bool :=
    c.msg.size % 2 == 1 && c.msg.size >= 3 && c.msg.get! 0 == 0xaa && c.msg.get! (c.msg.size - 1) == 0xbb && c.msg.data.any (· == 0x77)
  let sOdd ← shrinkElements shrinkCryptoCase (fun cand => do
    match ← execBatch none (some odd33Pred) cand with | .ok _ => return false | .error _ => return true)
    #[{ even62Case with msg := odd33, chunks := #[odd33] }]
  if (match sOdd.toList with | [x] => x.msg.size | _ => 999) != 5 then
    let got := match sOdd.toList with | [x] => s!"{x.msg.size}" | _ => "non1"
    throw (IO.userError s!"CRYPTOHASH_ODD33_SHRINK_FAILED: got {got}")

  for oddN in [7, 15, 31, 63] do
    let oddB := ByteArray.mk (#[0xaa, 0xbb] ++ Array.replicate (oddN - 4) 0x55 ++ #[0xdd, 0xee])
    let sOn ← shrinkElements shrinkCryptoCase (fun cand => do
      match ← execBatch none (some fun c =>
        c.msg.size % 2 == 1 && c.msg.size >= 5 &&
        c.msg.extract 0 2 == ByteArray.mk #[0xaa, 0xbb] &&
        c.msg.extract (c.msg.size - 2) c.msg.size == ByteArray.mk #[0xdd, 0xee]) cand with
      | .ok _ => return false | .error _ => return true)
      #[{ even62Case with msg := oddB, chunks := #[oddB] }]
    if (match sOn.toList with | [x] => x.msg.size | _ => 999) != 5 then
      throw (IO.userError s!"CRYPTOHASH_ODD_SHRINK_FAILED: n={oddN}")

  IO.println s!"CRYPTOHASH_SHRINK_SELFTEST_OK: original={batch.size} shrunk=1 lens=(65, 65) suffix_hex_ok=true chunk_bytes=64 chunk_trials={trials3} nonpow2_trials={trials4} interior_ok=true"

/-- Differential fuzzing suite for `LeanSwe.CryptoHash` against pure models and Python `hashlib`/`hmac`. -/
def suite : FuzzSuite := {
  name := "cryptohash"
  description := "OpenSSL 3 SHA-256/SHA-512/HMAC-SHA256 vs pure streaming Lean models & Python hashlib/hmac fuzzer"
  runSmoke := fun cfg => do
    let actual := max 200 (min cfg.steps 300)
    Fuzz.Common.recordSuiteSteps actual
    runCryptoHashLoop actual cfg.seed true
  runFuzz := fun cfg => do
    Fuzz.Common.recordSuiteSteps cfg.steps
    runCryptoHashLoop cfg.steps cfg.seed false
  selfTestShrink := runSelfTestShrink
}

end Fuzz.CryptoHash
