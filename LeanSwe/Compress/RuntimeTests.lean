import Core.Assumptions
import LeanSwe.Fs.Interface
import LeanSwe.Process.Interface
import LeanSwe.Compress.Types
import LeanSwe.Compress.Model
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface

namespace LeanSwe.Compress.RuntimeTests

open LeanSwe.Process
open LeanSwe.Compress

private def assertTrue (msg : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"Compress runtime assertion failed: {msg}")

private def assertBytesEq (msg : String) (actual expected : ByteArray) : IO Unit := do
  if actual != expected then
    throw (IO.userError
      s!"Compress runtime byte mismatch ({msg}): actual size={actual.size}, expected size={expected.size}")

private def expectOk {α : Type} (msg : String) (res : Except CompressError α) : IO α := do
  match res with
  | .ok a => return a
  | .error e =>
    throw (IO.userError s!"Compress runtime expected ok ({msg}), got error {repr e.kind}: {e.message}")

private def expectErrKind {α : Type} (msg : String) (expectedKind : CompressErrorKind)
    (res : Except CompressError α) : IO CompressError := do
  match res with
  | .ok _ =>
    throw (IO.userError s!"Compress runtime expected error {repr expectedKind} ({msg}), got ok")
  | .error e =>
    if e.kind != expectedKind then
      throw (IO.userError
        s!"Compress runtime expected error {repr expectedKind} ({msg}), got {repr e.kind}: {e.message}")
    if e.message.isEmpty then
      throw (IO.userError s!"Compress runtime expected non-empty error message ({msg})")
    let wfOk :=
      match e.codec with
      | some c => Model.isWellFormedCompressError c e
      | none => false
    if !wfOk then
      throw (IO.userError
        s!"Compress runtime malformed CompressError ({msg}): codec={repr e.codec} exitCode={repr e.exitCode} stderr={repr e.stderr}")
    return e

private def mkRepeatedBytes (n : Nat) : ByteArray := Id.run do
  let pattern := "lean-swe-compress-repetitive-block-0123456789abcdef\n".toUTF8
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    out := out.push pattern.data[i % pattern.size]!
  return out

private def mkPseudoRandomBytes (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  let mut state : UInt64 := 0x9e3779b97f4a7c15
  for _ in [0:n] do
    state := state * 6364136223846793005 + 1442695040888963407
    out := out.push ((state >>> 56).toUInt8)
  return out

private def mkZeroBytes (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    out := out.push 0
  return out

private def corruptMiddleByte (bs : ByteArray) : ByteArray := Id.run do
  if bs.isEmpty then
    return bs
  let idx := bs.size / 2
  let mut out := bs
  out := out.set! idx (out.get! idx ^^^ 0xff)
  return out

private def pythonCodecAction (codec : Codec) (isDecompress : Bool) (input : ByteArray) : IO ByteArray := do
  let script :=
    match codec, isDecompress with
    | .zstd, false =>
      "import sys, zstandard; sys.stdout.buffer.write(zstandard.ZstdCompressor().compress(sys.stdin.buffer.read()))"
    | .zstd, true =>
      "import sys, zstandard; sys.stdout.buffer.write(zstandard.ZstdDecompressor().decompressobj().decompress(sys.stdin.buffer.read()))"
    | .xz, false =>
      "import sys, lzma; sys.stdout.buffer.write(lzma.compress(sys.stdin.buffer.read()))"
    | .xz, true =>
      "import sys, lzma; sys.stdout.buffer.write(lzma.decompress(sys.stdin.buffer.read()))"
    | .gzip, false =>
      "import sys, gzip; sys.stdout.buffer.write(gzip.compress(sys.stdin.buffer.read(), mtime=0))"
    | .gzip, true =>
      "import sys, gzip; sys.stdout.buffer.write(gzip.decompress(sys.stdin.buffer.read()))"
  let req : ExecRequest :=
    { program := "python3"
      args := #["-c", script]
      stdin := input
      timeoutMs := some 30000
      maxOutputBytes := some (8 * 1024 * 1024) }
  match ← LeanSwe.Process.run req with
  | .error e =>
    throw (IO.userError s!"python3 interop invocation failed for {repr codec}: {e.message}")
  | .ok res =>
    if res.exitCode != 0 then
      let errStr := String.fromUTF8? res.stderr |>.getD "<binary>"
      throw (IO.userError s!"python3 interop exited {res.exitCode} for {repr codec}: {errStr}")
    return res.stdout

private def testToolAvailability : IO Unit := do
  for codec in #[Codec.zstd, .xz, .gzip] do
    let avail ← isToolAvailable codec
    assertTrue s!"isToolAvailable {repr codec}" avail

private def testRoundTrips : IO Unit := do
  let ascii := "hello lean-swe compress!\nline 2 with UTF-8: λ∀∃\n".toUTF8
  let repeated := mkRepeatedBytes 102400
  let random := mkPseudoRandomBytes 16384
  let payloads : Array (String × ByteArray) :=
    #[("empty", ByteArray.empty), ("ascii", ascii), ("repeated", repeated), ("random", random)]
  for codec in #[Codec.zstd, .xz, .gzip] do
    for (label, payload) in payloads do
      let comp ← expectOk s!"compress {repr codec} {label}" (← compress codec payload)
      assertTrue s!"compressed {repr codec} {label} non-empty" (!comp.isEmpty)
      let dec ← expectOk s!"decompress {repr codec} {label}" (← decompress codec comp)
      assertBytesEq s!"round-trip {repr codec} {label}" dec payload
    let smallComp ← expectOk s!"compress {repr codec} concat-base" (← compress codec ascii)
    let doubledComp := smallComp ++ smallComp
    let decDoubled ← expectOk s!"decompress {repr codec} concat" (← decompress codec doubledComp)
    assertBytesEq s!"concat round-trip {repr codec}" decDoubled (ascii ++ ascii)

private def testCompressionOptionsAndDeterminism : IO Unit := do
  let payload := mkRepeatedBytes 32768
  let optCases : Array (String × Codec × CompressOptions) :=
    #[("zstd-fast", .zstd, { level := some 1, threads := some 0 }),
      ("zstd-max-t2", .zstd, { level := some 19, threads := some 2 }),
      ("xz-l0-t0", .xz, { level := some 0, threads := some 0 }),
      ("xz-l6-t2", .xz, { level := some 6, threads := some 2 }),
      ("gzip-l1", .gzip, { level := some 1 }),
      ("gzip-l9", .gzip, { level := some 9 })]
  for (label, codec, opts) in optCases do
    let comp ← expectOk s!"compressWith {label}" (← compressWith codec opts payload)
    let dec ← expectOk s!"decompress {label}" (← decompress codec comp)
    assertBytesEq s!"options round-trip {label}" dec payload
  let gzEmpty1 ← expectOk "gzip empty det 1" (← compress .gzip ByteArray.empty)
  let gzEmpty2 ← expectOk "gzip empty det 2" (← compress .gzip ByteArray.empty)
  assertBytesEq "gzip -n determinism empty" gzEmpty1 gzEmpty2
  let gzData1 ← expectOk "gzip data det 1" (← compress .gzip payload)
  let gzData2 ← expectOk "gzip data det 2" (← compress .gzip payload)
  assertBytesEq "gzip -n determinism non-empty" gzData1 gzData2

private def testPythonInterop : IO Unit := do
  let ascii := "lean-swe <-> python3 symmetric interop payload\n".toUTF8
  let random := mkPseudoRandomBytes 8192
  for codec in #[Codec.zstd, .xz, .gzip] do
    for (label, payload) in #[("empty", ByteArray.empty), ("ascii", ascii), ("random", random)] do
      let leanComp ← expectOk s!"lean->py compress {repr codec} {label}" (← compress codec payload)
      let pyDec ← pythonCodecAction codec true leanComp
      assertBytesEq s!"lean->py {repr codec} {label}" pyDec payload
      let pyComp ← pythonCodecAction codec false payload
      let leanDec ← expectOk s!"py->lean decompress {repr codec} {label}" (← decompress codec pyComp)
      assertBytesEq s!"py->lean {repr codec} {label}" leanDec payload

private def testCorruptAndTruncatedAndTrailingGarbage : IO Unit := do
  let sample := mkRepeatedBytes 4096
  for codec in #[Codec.zstd, .xz, .gzip] do
    let _ ← expectErrKind s!"empty decompress {repr codec}" .corruptData
      (← decompress codec ByteArray.empty)
    let _ ← expectErrKind s!"invalid magic {repr codec}" .corruptData
      (← decompress codec "not-valid-compressed-magic-header".toUTF8)
    let comp ← expectOk s!"compress for corrupt checks {repr codec}" (← compress codec sample)
    assertTrue s!"compressed size > 8 for {repr codec}" (comp.size > 8)
    let truncated := comp.extract 0 (comp.size / 2)
    let _ ← expectErrKind s!"truncated {repr codec}" .corruptData (← decompress codec truncated)
    let tailTruncated := comp.extract 0 (comp.size - 2)
    let _ ← expectErrKind s!"tail truncated {repr codec}" .corruptData (← decompress codec tailTruncated)
    let flipped := corruptMiddleByte comp
    let _ ← expectErrKind s!"bit-flipped {repr codec}" .corruptData (← decompress codec flipped)
    let withGarbage := comp ++ ByteArray.mk #[0xde, 0xad, 0xbe, 0xef]
    let garbageErr ← expectErrKind s!"trailing non-zero garbage {repr codec}" .corruptData
      (← decompress codec withGarbage)
    if codec == .gzip then
      assertTrue "gzip trailing garbage exits with 2" (garbageErr.exitCode == some 2)

private def testInvalidInputsNoSpawn : IO Unit := do
  let noSpawnOps : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun _ => throw (IO.userError "unexpected spawn during invalidInput test") }
  let api := Internal.mkApiM noSpawnOps
  let threeBytes := "abc".toUTF8
  let invalidCompressCases : Array (String × Codec × CompressOptions × ByteArray) :=
    #[("timeoutMs=0", .zstd, { timeoutMs := 0 }, threeBytes),
      ("maxOutputBytes=0", .xz, { maxOutputBytes := 0 }, threeBytes),
      ("maxInputBytes exceeded", .gzip, { maxInputBytes := some 2 }, threeBytes),
      ("zstd level=0", .zstd, { level := some 0 }, threeBytes),
      ("zstd level=20", .zstd, { level := some 20 }, threeBytes),
      ("xz level=10", .xz, { level := some 10 }, threeBytes),
      ("gzip level=0", .gzip, { level := some 0 }, threeBytes),
      ("gzip level=10", .gzip, { level := some 10 }, threeBytes),
      ("gzip threads=1", .gzip, { threads := some 1 }, threeBytes),
      ("xz threads=16385", .xz, { threads := some 16385 }, threeBytes),
      ("zstd threads=2^32", .zstd, { threads := some 4294967296 }, threeBytes)]
  for (label, codec, opts, inp) in invalidCompressCases do
    let _ ← expectErrKind s!"invalid compress {label}" .invalidInput
      (← api.compressWith codec opts inp)
  let invalidDecompressCases : Array (String × Codec × DecompressOptions × ByteArray) :=
    #[("decomp timeoutMs=0", .zstd, { timeoutMs := 0 }, threeBytes),
      ("decomp maxOutputBytes=0", .xz, { maxOutputBytes := 0 }, threeBytes),
      ("decomp maxInputBytes exceeded", .gzip, { maxInputBytes := some 2 }, threeBytes)]
  for (label, codec, opts, inp) in invalidDecompressCases do
    let _ ← expectErrKind s!"invalid decompress {label}" .invalidInput
      (← api.decompressWith codec opts inp)
  match Internal.validateCompressOptions .zstd { timeoutMs := 0 } threeBytes with
  | .error e => assertTrue "validateCompressOptions timeoutMs=0 kind" (e.kind == .invalidInput)
  | .ok () => throw (IO.userError "validateCompressOptions timeoutMs=0 unexpectedly succeeded")
  match Internal.validateDecompressOptions .zstd { timeoutMs := 0 } threeBytes with
  | .error e => assertTrue "validateDecompressOptions timeoutMs=0 kind" (e.kind == .invalidInput)
  | .ok () => throw (IO.userError "validateDecompressOptions timeoutMs=0 unexpectedly succeeded")
  let spawnedRef ← IO.mkRef (#[] : Array ExecRequest)
  let mockOkOps : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun req => do
        spawnedRef.modify (·.push req)
        return .ok { handleId := 1, pid := 1, pgid := 1 }
      awaitOutput := fun _ _ _ _ =>
        return .ok (.exited { exitCode := 0, stdout := Model.encodeStored .zstd ByteArray.empty, stderr := ByteArray.empty })
      killProcessGroup := fun _ => return .ok ()
      reap := fun _ => return .ok ()
      activeProcessCount := return 0 }
  let mockOkApi := Internal.mkApiM mockOkOps
  let _ ← expectOk "compressWith exact maxInputBytes" (← mockOkApi.compressWith .zstd { maxInputBytes := some threeBytes.size, maxOutputBytes := 2048 } threeBytes)
  let _ ← expectOk "compressWith zstd max threads" (← mockOkApi.compressWith .zstd { threads := some 4294967295 } threeBytes)
  let _ ← expectOk "compressWith xz max threads" (← mockOkApi.compressWith .xz { threads := some 16384 } threeBytes)
  let validZst := Model.encodeStored .zstd threeBytes
  let _ ← expectOk "decompressWith exact maxInputBytes"
    (← mockOkApi.decompressWith .zstd { maxInputBytes := some validZst.size, maxOutputBytes := 1024 } validZst)
  let availOk ← mockOkApi.isToolAvailable .gzip
  assertTrue "mockOkApi isToolAvailable gzip" availOk
  let spawnedReqs ← spawnedRef.get
  assertTrue "mockOkApi spawned 5 requests" (spawnedReqs.size == 5)
  let wantEnv : Array (String × Option String) :=
    #[("XZ_OPT", none),
      ("XZ_DEFAULTS", none),
      ("ZSTD_CLEVEL", none),
      ("ZSTD_NBTHREADS", none),
      ("GZIP", none),
      ("LC_ALL", some "C")]
  assertTrue "zstd compress args include --no-progress and omit --no-asyncio"
    ((spawnedReqs[0]?).any fun req =>
      req.args == #["-c", "-q", "--no-progress"] && req.env == wantEnv &&
      req.inheritEnv && req.maxOutputBytes == some (2048 + 4096))
  assertTrue "zstd decompress args include --no-progress and --format=zstd"
    ((spawnedReqs[3]?).any fun req =>
      req.args == #["-d", "-c", "-q", "--no-progress", "--format=zstd"] && req.env == wantEnv &&
      req.inheritEnv && req.maxOutputBytes == some (1024 + 4096))
  assertTrue "isToolAvailable request sanitized env and limits"
    ((spawnedReqs[4]?).any fun req =>
      req.program == "gzip" && req.args == #["--version"] &&
      req.env == wantEnv && req.inheritEnv &&
      req.timeoutMs == some 5000 && req.maxOutputBytes == some 65536)

private def testToolNotFoundAndNonExecutable : IO Unit := do
  let missingOps : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun req =>
        SysBridge.defaultOps.spawn { req with program := "/nonexistent/lean-swe-missing-compress-tool" } }
  let missingApi := Internal.mkApiM missingOps
  for codec in #[Codec.zstd, .xz, .gzip] do
    let avail ← missingApi.isToolAvailable codec
    assertTrue s!"missing tool isToolAvailable false {repr codec}" (!avail)
    let _ ← expectErrKind s!"missing tool compress {repr codec}" .toolNotFound
      (← missingApi.compress codec "hi".toUTF8)
    let _ ← expectErrKind s!"missing tool decompress {repr codec}" .toolNotFound
      (← missingApi.decompress codec "hi".toUTF8)
  let tmpDir ← IO.FS.createTempDir
  try
    let nonExecPath := tmpDir / "non_executable_tool"
    IO.FS.writeFile nonExecPath "#!/bin/sh\nexit 0\n"
    IO.setAccessRights nonExecPath
      { user := { read := true, write := true, execution := false }
        group := { read := true }
        other := { read := true } }
    let nonExecOps : RawProcessOpsM IO :=
      { SysBridge.defaultOps with
        spawn := fun req =>
          SysBridge.defaultOps.spawn { req with program := nonExecPath.toString } }
    let nonExecApi := Internal.mkApiM nonExecOps
    let avail ← nonExecApi.isToolAvailable .zstd
    assertTrue "non-executable tool isToolAvailable false" (!avail)
    let _ ← expectErrKind "non-executable tool compress" .toolNotFound
      (← nonExecApi.compress .xz "hi".toUTF8)
    let _ ← expectErrKind "non-executable tool decompress" .toolNotFound
      (← nonExecApi.decompress .gzip "hi".toUTF8)
  finally
    IO.FS.removeDirAll tmpDir

private def mkMockAwaitApi (outcome : ExecOutcome) : CompressApi :=
  let ops : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun _ => pure (.ok { handleId := 1, pid := 1, pgid := 1 })
      awaitOutput := fun _ _ _ _ => pure (.ok outcome)
      killProcessGroup := fun _ => pure (.ok ())
      reap := fun _ => pure (.ok ())
      activeProcessCount := pure 0 }
  Internal.mkApiM ops

private def validEmptyZstdFrame : ByteArray :=
  ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x20, 0x00, 0x01, 0x00, 0x00]

private def validEmptyGzipFrame : ByteArray :=
  ByteArray.mk #[0x1F, 0x8B, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x03, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

private def testFramingBeforeOutputLimit : IO Unit := do
  let bad := "not-valid-gzip-stream".toUTF8
  let bigStdoutApi := mkMockAwaitApi
    (.exited { exitCode := 0, stdout := ByteArray.mk #[1, 2, 3, 4, 5], stderr := ByteArray.empty })
  let _ ← expectErrKind "mock exited stdout>limit invalid gzip header" .corruptData
    (← bigStdoutApi.decompressWith .gzip { maxOutputBytes := 2 } bad)
  let _ ← expectErrKind "mock exited stdout>limit valid gzip header" .outputLimitExceeded
    (← bigStdoutApi.decompressWith .gzip { maxOutputBytes := 2 } validEmptyGzipFrame)
  let _ ← expectErrKind "mock exited stdout>limit valid zstd framing" .outputLimitExceeded
    (← bigStdoutApi.decompressWith .zstd { maxOutputBytes := 2 } validEmptyZstdFrame)
  let oomApi := mkMockAwaitApi (.outputLimitExceeded (ByteArray.mk #[1, 2, 3, 4]) ByteArray.empty)
  let _ ← expectErrKind "mock outputLimitExceeded invalid gzip header" .corruptData
    (← oomApi.decompressWith .gzip { maxOutputBytes := 2, timeoutMs := 250 } bad)
  let toApi := mkMockAwaitApi (.timedOut ByteArray.empty ByteArray.empty)
  let _ ← expectErrKind "mock timedOut invalid gzip header" .corruptData
    (← toApi.decompressWith .gzip {} bad)
  let _ ← expectErrKind "mock timedOut non-default opts invalid gzip header" .corruptData
    (← toApi.decompressWith .gzip { maxOutputBytes := 16, timeoutMs := 250 } bad)
  let _ ← expectErrKind "real decompressWith tiny limit invalid gzip header" .corruptData
    (← Compress.decompressWith .gzip { maxOutputBytes := 1 } bad)
  let okExitBadFramingApi := mkMockAwaitApi
    (.exited { exitCode := 0, stdout := ByteArray.mk #[0x41], stderr := ByteArray.empty })
  let errExit0Frm ← expectErrKind "mock exited 0 stdout<=limit invalid gzip header" .corruptData
    (← okExitBadFramingApi.decompressWith .gzip { maxOutputBytes := 16 } bad)
  assertTrue "mock exited 0 invalid gzip header clears exitCode and stderr"
    (errExit0Frm.exitCode.isNone && errExit0Frm.stderr.isNone)
  let lzwLegacy := ByteArray.mk #[0x1F, 0x9D, 0x90, 0x41, 0x00]
  let errLzw ← expectErrKind "real gzip rejects legacy 1f 9d LZW stream" .corruptData
    (← Compress.decompress .gzip lzwLegacy)
  assertTrue "real gzip legacy LZW framing rejection clears exitCode" errLzw.exitCode.isNone
  let pkzipArchive := ByteArray.mk #[
    80, 75, 3, 4, 20, 0, 0, 0, 8, 0, 240, 60, 116, 93, 172, 42, 147, 216,
    4, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 97, 203, 200, 4, 0,
    80, 75, 1, 2, 20, 3, 20, 0, 0, 0, 8, 0, 240, 60, 116, 93, 172, 42, 147, 216,
    4, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 1, 0, 0, 0, 0, 97,
    80, 75, 5, 6, 0, 0, 0, 0, 1, 0, 1, 0, 47, 0, 0, 0, 35, 0, 0, 0, 0, 0]
  let errZip ← expectErrKind "real gzip rejects PKZIP container" .corruptData
    (← Compress.decompress .gzip pkzipArchive)
  assertTrue "real gzip PKZIP framing rejection clears exitCode" errZip.exitCode.isNone
  let gzValid ← expectOk "compress valid gzip for trailing garbage concat" (← Compress.compress .gzip "ok".toUTF8)
  let _ ← expectErrKind "real gzip rejects concatenated valid+trailing garbage" .corruptData
    (← Compress.decompress .gzip (gzValid ++ ByteArray.mk #[0xde, 0xad, 0xbe, 0xef]))

private def testOutputLimitExceeded : IO Unit := do
  testFramingBeforeOutputLimit
  let boundaryPayload := "exact-max-output-bytes-boundary-check-payload".toUTF8
  for codec in #[Codec.zstd, .xz, .gzip] do
    let compExact ← expectOk s!"compress baseline {repr codec}" (← compress codec boundaryPayload)
    let compAtLim ← expectOk s!"compressWith exact maxOutputBytes {repr codec}"
      (← compressWith codec { maxOutputBytes := compExact.size } boundaryPayload)
    assertBytesEq s!"compressWith exact maxOutputBytes bytes {repr codec}" compAtLim compExact
    let _ ← expectErrKind s!"compressWith maxOutputBytes-1 {repr codec}" .outputLimitExceeded
      (← compressWith codec { maxOutputBytes := compExact.size - 1 } boundaryPayload)
    let decAtLim ← expectOk s!"decompressWith exact maxOutputBytes {repr codec}"
      (← decompressWith codec { maxOutputBytes := boundaryPayload.size } compExact)
    assertBytesEq s!"decompressWith exact maxOutputBytes bytes {repr codec}" decAtLim boundaryPayload
    let _ ← expectErrKind s!"decompressWith maxOutputBytes-1 {repr codec}" .outputLimitExceeded
      (← decompressWith codec { maxOutputBytes := boundaryPayload.size - 1 } compExact)
  let zeros := mkZeroBytes (2 * 1024 * 1024)
  for codec in #[Codec.zstd, .xz, .gzip] do
    let comp ← expectOk s!"compress zero bomb {repr codec}" (← compress codec zeros)
    assertTrue s!"zero bomb compressed compactly {repr codec}" (comp.size < 4096)
    let _ ← expectErrKind s!"decompress bomb {repr codec}" .outputLimitExceeded
      (← decompressWith codec { maxOutputBytes := 1024 } comp)

private def testTimedOutAndEnvSanitization : IO Unit := do
  let slowOps : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun req =>
        SysBridge.defaultOps.spawn { req with program := "sleep", args := #["2"] } }
  let slowApi := Internal.mkApiM slowOps
  let _ ← expectErrKind "timeout compress" .timedOut
    (← slowApi.compressWith .zstd { timeoutMs := 50 } ByteArray.empty)
  let poisoned : Array (String × Option String) :=
    #[("XZ_OPT", some "--lean-swe-invalid-xz-flag"),
      ("XZ_DEFAULTS", some "--lean-swe-invalid-xz-defaults"),
      ("ZSTD_CLEVEL", some "19"),
      ("ZSTD_NBTHREADS", some "999"),
      ("GZIP", some "--lean-swe-invalid-gzip-flag"),
      ("LANG", some "de_AT.utf8"),
      ("LANGUAGE", some "de_AT:de")]
  let poisonedOps : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun req =>
        SysBridge.defaultOps.spawn { req with env := poisoned ++ req.env } }
  let poisonedApi := Internal.mkApiM poisonedOps
  let sample := "sanitized-env-check-payload".toUTF8
  for codec in #[Codec.zstd, .xz, .gzip] do
    let avail ← poisonedApi.isToolAvailable codec
    assertTrue s!"poisoned env isToolAvailable {repr codec}" avail
    let comp ← expectOk s!"poisoned env compress {repr codec}" (← poisonedApi.compress codec sample)
    let dec ← expectOk s!"poisoned env decompress {repr codec}" (← poisonedApi.decompress codec comp)
    assertBytesEq s!"poisoned env round-trip {repr codec}" dec sample
  let zstdClean ← expectOk "clean zstd compress" (← Compress.compress .zstd (mkRepeatedBytes 32768))
  let zstdPoisoned ← expectOk "poisoned ZSTD_CLEVEL=19 zstd compress" (← poisonedApi.compress .zstd (mkRepeatedBytes 32768))
  assertBytesEq "ZSTD_CLEVEL=19 stripped matches default level" zstdPoisoned zstdClean
  let xzLocaleErr ← expectErrKind "poisoned LANG/LANGUAGE xz corrupt stderr stays C locale" .corruptData
    (← poisonedApi.decompress .xz "not-valid-xz-stream".toUTF8)
  let errTxt := xzLocaleErr.stderr.getD ""
  assertTrue "poisoned locale xz stderr is English C locale"
    ((errTxt.splitOn "File format not recognized").length > 1 ||
     (errTxt.splitOn "file format not recognized").length > 1)

/-- Verify installed `zstd`, `xz`, and `gzip` binaries report `isToolAvailable = true`. -/
def assume_compress_isToolAvailable_installedCodecsReportTrue : IO Unit :=
  testToolAvailability

/-- Verify real CLI round-trips across payloads and concatenated streams for all codecs. -/
def assume_compress_roundTrip_validAndConcatenatedStreams : IO Unit :=
  testRoundTrips

/-- Verify `compressWith` options round-trip and `gzip -n` outputs are byte-deterministic. -/
def assume_compress_compressWith_gzipDeterministicAndOptionsRoundTrip : IO Unit :=
  testCompressionOptionsAndDeterminism

/-- Verify bidirectional byte-level interoperability against Python reference codecs. -/
def assume_compress_decompress_pythonReferenceInterop : IO Unit :=
  testPythonInterop

/-- Verify `decompress` classifies empty, corrupt, truncated, and trailing-garbage streams as `.corruptData`. -/
def assume_compress_decompress_rejectsCorruptTruncatedAndTrailingGarbage : IO Unit :=
  testCorruptAndTruncatedAndTrailingGarbage

/-- Verify `defaultApi` sanitizes codec environment variables and classifies missing/non-executable binaries as `.toolNotFound`. -/
def assume_compress_defaultApi_sanitizesCodecEnvAndReportsMissingTool : IO Unit := do
  testToolNotFoundAndNonExecutable
  testTimedOutAndEnvSanitization

/-- Verify `decompressWith` enforces `maxOutputBytes` on highly compressible bombs with `.outputLimitExceeded`. -/
def assume_compress_decompressWith_enforcesMaxOutputBytesOnBomb : IO Unit :=
  testOutputLimitExceeded

private def compressErrKindTag : CompressErrorKind → String
  | .toolNotFound => "toolNotFound"
  | .invalidInput => "invalidInput"
  | .corruptData => "corruptData"
  | .outputLimitExceeded => "outputLimitExceeded"
  | .timedOut => "timedOut"
  | .commandFailed => "commandFailed"
  | .ioError => "ioError"

private def runProbeResult (res : Except CompressError ByteArray) : IO UInt32 := do
  match res with
  | .ok _ =>
    IO.println "OK"
    return 1
  | .error e =>
    IO.println s!"ERR:{compressErrKindTag e.kind}:{e.message}"
    return 0

/-- Subprocess probe entrypoint invoked via `--compress-probe` from `Tests.Main`. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["compress"] => runProbeResult (← Compress.compress .zstd "hi".toUTF8)
  | ["decompress"] => runProbeResult (← Compress.decompress .zstd "hi".toUTF8)
  | ["compressWith"] => runProbeResult (← Compress.compressWith .zstd {} "hi".toUTF8)
  | ["decompressWith"] => runProbeResult (← Compress.decompressWith .zstd {} "hi".toUTF8)
  | _ =>
    IO.eprintln s!"unknown compress probe args: {repr args}"
    return 2

private def runCompressProbeWithPath (label opTag pathEnv : String)
    (expectedKind : CompressErrorKind) : IO Unit := do
  let avail ← Compress.isToolAvailable .zstd
  assertTrue s!"{label}: zstd available before probe" avail
  let exe := (← IO.appPath).toString
  let req : ExecRequest :=
    { program := exe
      args := #["--compress-probe", opTag]
      env := #[("PATH", some pathEnv)]
      inheritEnv := false
      timeoutMs := some 10000
      maxOutputBytes := some 65536 }
  match ← LeanSwe.Process.run req with
  | .error e =>
    throw (IO.userError s!"{label}: probe process invocation failed: {e.message}")
  | .ok res =>
    let out := (String.fromUTF8? res.stdout |>.getD "").trimAscii.toString
    let err := (String.fromUTF8? res.stderr |>.getD "").trimAscii.toString
    if res.exitCode != 0 then
      throw (IO.userError s!"{label}: probe exited {res.exitCode} stdout={out} stderr={err}")
    let expectedPrefix := s!"ERR:{compressErrKindTag expectedKind}:"
    if !out.startsWith expectedPrefix || out.length <= expectedPrefix.length then
      throw (IO.userError s!"{label}: expected prefix {expectedPrefix}, got {out}")

private def readUrandomBytes (n : Nat) : IO ByteArray := do
  IO.FS.withFile "/dev/urandom" .read fun h => do
    let mut out := ByteArray.emptyWithCapacity n
    while out.size < n do
      let rem := n - out.size
      let chunk ← h.read (USize.ofNat rem)
      if chunk.isEmpty then
        throw (IO.userError "unexpected EOF reading /dev/urandom")
      out := out ++ chunk
    return out

private def runToolNotFoundProbe (label opTag : String) : IO Unit := do
  let tmpDir ← IO.FS.createTempDir
  try
    runCompressProbeWithPath label opTag tmpDir.toString .toolNotFound
  finally
    IO.FS.removeDirAll tmpDir

private def runEloopProbe (label opTag : String) : IO Unit := do
  let tmpDir ← IO.FS.createTempDir
  try
    let linkPath := (tmpDir / "zstd").toString
    match ← LeanSwe.Fs.symlink "zstd" linkPath with
    | .ok () => pure ()
    | .error fe => throw (IO.userError s!"{label}: symlink failed: {fe.message}")
    runCompressProbeWithPath label opTag tmpDir.toString .invalidInput
  finally
    IO.FS.removeDirAll tmpDir

private def runEnametoolongProbe (label opTag : String) : IO Unit := do
  let compLongPath := "/" ++ String.ofList (List.replicate 300 'a')
  runCompressProbeWithPath (label ++ " ENAMETOOLONG") opTag compLongPath .ioError
  let overPathMax := String.ofList (List.replicate 5000 'a')
  runCompressProbeWithPath (label ++ " >PATH_MAX") opTag overPathMax .ioError

/-- Real error test for `Compress.compress` returning `.toolNotFound`. -/
def err_compress_compress_toolNotFound : IO Unit :=
  runToolNotFoundProbe "compress toolNotFound" "compress"

/-- Real error test for `Compress.compress` returning `.invalidInput`. -/
def err_compress_compress_invalidInput : IO Unit :=
  runEloopProbe "compress invalidInput" "compress"

/-- Real error test for `Compress.compress` returning `.outputLimitExceeded`. -/
def err_compress_compress_outputLimitExceeded : IO Unit := do
  let payload ← readUrandomBytes (64 * 1024 * 1024 + 131072)
  let _ ← expectErrKind "compress outputLimitExceeded" .outputLimitExceeded
    (← Compress.compress .zstd payload)

/-- Mocked error test for `Compress.compress` returning `.timedOut`. -/
def err_compress_compress_timedOut : IO Unit := do
  let api := mkMockAwaitApi (.timedOut ByteArray.empty ByteArray.empty)
  let _ ← expectErrKind "compress timedOut" .timedOut (← api.compress .zstd "hi".toUTF8)

/-- Mocked error test for `Compress.compress` returning `.commandFailed`. -/
def err_compress_compress_commandFailed : IO Unit := do
  let api := mkMockAwaitApi (.exited { exitCode := 2, stdout := ByteArray.empty, stderr := "err".toUTF8 })
  let _ ← expectErrKind "compress commandFailed" .commandFailed (← api.compress .zstd "hi".toUTF8)

/-- Real error test for `Compress.compress` returning `.ioError`. -/
def err_compress_compress_ioError : IO Unit :=
  runEnametoolongProbe "compress ioError" "compress"

/-- Real error test for `Compress.decompress` returning `.toolNotFound`. -/
def err_compress_decompress_toolNotFound : IO Unit :=
  runToolNotFoundProbe "decompress toolNotFound" "decompress"

/-- Real error test for `Compress.decompress` returning `.invalidInput`. -/
def err_compress_decompress_invalidInput : IO Unit :=
  runEloopProbe "decompress invalidInput" "decompress"

/-- Real error test for `Compress.decompress` returning `.corruptData`. -/
def err_compress_decompress_corruptData : IO Unit := do
  let _ ← expectErrKind "decompress corruptData" .corruptData
    (← decompress .zstd "not-valid-zstd-stream".toUTF8)

/-- Real error test for `Compress.decompress` returning `.outputLimitExceeded`. -/
def err_compress_decompress_outputLimitExceeded : IO Unit := do
  let zeros := ByteArray.mk (Array.replicate (65 * 1024 * 1024) 0)
  let comp ← expectOk "compress payload for decompress limit" (← Compress.compress .zstd zeros)
  let _ ← expectErrKind "decompress outputLimitExceeded" .outputLimitExceeded
    (← Compress.decompress .zstd comp)

/-- Mocked error test for `Compress.decompress` returning `.timedOut`. -/
def err_compress_decompress_timedOut : IO Unit := do
  let api := mkMockAwaitApi (.timedOut ByteArray.empty ByteArray.empty)
  let _ ← expectErrKind "decompress timedOut" .timedOut (← api.decompress .zstd validEmptyZstdFrame)

/-- Mocked error test for `Compress.decompress` returning `.commandFailed`. -/
def err_compress_decompress_commandFailed : IO Unit := do
  let api := mkMockAwaitApi (.signaled 15 ByteArray.empty ByteArray.empty)
  let _ ← expectErrKind "decompress commandFailed" .commandFailed (← api.decompress .zstd "hi".toUTF8)

/-- Real error test for `Compress.decompress` returning `.ioError`. -/
def err_compress_decompress_ioError : IO Unit :=
  runEnametoolongProbe "decompress ioError" "decompress"

/-- Real error test for `Compress.compressWith` returning `.toolNotFound`. -/
def err_compress_compressWith_toolNotFound : IO Unit :=
  runToolNotFoundProbe "compressWith toolNotFound" "compressWith"

/-- Real error test for `Compress.compressWith` returning `.invalidInput`. -/
def err_compress_compressWith_invalidInput : IO Unit := do
  let _ ← expectErrKind "compressWith invalidInput" .invalidInput
    (← compressWith .gzip { threads := some 1 } "abc".toUTF8)

/-- Real error test for `Compress.compressWith` returning `.outputLimitExceeded`. -/
def err_compress_compressWith_outputLimitExceeded : IO Unit := do
  let _ ← expectErrKind "compressWith outputLimitExceeded" .outputLimitExceeded
    (← compressWith .gzip { maxOutputBytes := 4 } (mkRepeatedBytes 8192))

/-- Real error test for `Compress.compressWith` returning `.timedOut`. -/
def err_compress_compressWith_timedOut : IO Unit := do
  let payload ← readUrandomBytes (8 * 1024 * 1024)
  let _ ← expectErrKind "compressWith timedOut" .timedOut
    (← Compress.compressWith .xz { level := some 9, timeoutMs := 1 } payload)

/-- Mocked error test for `Compress.compressWith` returning `.commandFailed`. -/
def err_compress_compressWith_commandFailed : IO Unit := do
  let api := mkMockAwaitApi (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := "fail".toUTF8 })
  let _ ← expectErrKind "compressWith commandFailed" .commandFailed (← api.compressWith .zstd {} "hi".toUTF8)
  let emptyErrApi := mkMockAwaitApi (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty })
  let eEmpty ← expectErrKind "compressWith commandFailed empty stderr" .commandFailed
    (← emptyErrApi.compressWith .zstd {} "hi".toUTF8)
  assertTrue "compressWith commandFailed empty stderr fallback message"
    (eEmpty.message == "zstd compression failed with exit code 1")

/-- Real error test for `Compress.compressWith` returning `.ioError`. -/
def err_compress_compressWith_ioError : IO Unit :=
  runEnametoolongProbe "compressWith ioError" "compressWith"

/-- Real error test for `Compress.decompressWith` returning `.toolNotFound`. -/
def err_compress_decompressWith_toolNotFound : IO Unit :=
  runToolNotFoundProbe "decompressWith toolNotFound" "decompressWith"

/-- Real error test for `Compress.decompressWith` returning `.invalidInput`. -/
def err_compress_decompressWith_invalidInput : IO Unit := do
  let _ ← expectErrKind "decompressWith invalidInput" .invalidInput
    (← decompressWith .zstd { timeoutMs := 0 } "abc".toUTF8)

/-- Real error test for `Compress.decompressWith` returning `.corruptData`. -/
def err_compress_decompressWith_corruptData : IO Unit := do
  let _ ← expectErrKind "decompressWith corruptData" .corruptData
    (← decompressWith .gzip {} "not-valid-gzip".toUTF8)
  let emptyErrApi := mkMockAwaitApi (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty })
  let eEmpty ← expectErrKind "decompressWith corruptData empty stderr" .corruptData
    (← emptyErrApi.decompressWith .zstd {} "hi".toUTF8)
  assertTrue "decompressWith corruptData empty stderr fallback message"
    (eEmpty.message == "zstd decompression failed with exit code 1")

/-- Real error test for `Compress.decompressWith` returning `.outputLimitExceeded`. -/
def err_compress_decompressWith_outputLimitExceeded : IO Unit := do
  let comp ← expectOk "compress zero bomb for decompressWith limit" (← compress .zstd (mkZeroBytes (2 * 1024 * 1024)))
  let _ ← expectErrKind "decompressWith outputLimitExceeded" .outputLimitExceeded
    (← decompressWith .zstd { maxOutputBytes := 1024 } comp)

/-- Real error test for `Compress.decompressWith` returning `.timedOut`. -/
def err_compress_decompressWith_timedOut : IO Unit := do
  let payload ← readUrandomBytes (16 * 1024 * 1024)
  let comp ← expectOk "compress xz payload for decompressWith timedOut"
    (← Compress.compressWith .xz { level := some 1, timeoutMs := 30000 } payload)
  let _ ← expectErrKind "decompressWith timedOut" .timedOut
    (← Compress.decompressWith .xz { timeoutMs := 1 } comp)

/-- Mocked error test for `Compress.decompressWith` returning `.commandFailed`. -/
def err_compress_decompressWith_commandFailed : IO Unit := do
  let api := mkMockAwaitApi (.signaled 9 ByteArray.empty ByteArray.empty)
  let _ ← expectErrKind "decompressWith commandFailed" .commandFailed
    (← api.decompressWith .zstd {} "hi".toUTF8)

/-- Real error test for `Compress.decompressWith` returning `.ioError`. -/
def err_compress_decompressWith_ioError : IO Unit :=
  runEnametoolongProbe "decompressWith ioError" "decompressWith"

/-- Registered runtime verification entries for `LeanSwe.Compress.externalAssumptions`. -/
def registeredAssumptions : Array Core.RegisteredAssumption :=
  #[ { specName := "LeanSwe.Compress.assume_compress_isToolAvailable_installedCodecsReportTrue"
       run := assume_compress_isToolAvailable_installedCodecsReportTrue }
   , { specName := "LeanSwe.Compress.assume_compress_roundTrip_validAndConcatenatedStreams"
       run := assume_compress_roundTrip_validAndConcatenatedStreams }
   , { specName := "LeanSwe.Compress.assume_compress_compressWith_gzipDeterministicAndOptionsRoundTrip"
       run := assume_compress_compressWith_gzipDeterministicAndOptionsRoundTrip }
   , { specName := "LeanSwe.Compress.assume_compress_decompress_pythonReferenceInterop"
       run := assume_compress_decompress_pythonReferenceInterop }
   , { specName := "LeanSwe.Compress.assume_compress_decompress_rejectsCorruptTruncatedAndTrailingGarbage"
       run := assume_compress_decompress_rejectsCorruptTruncatedAndTrailingGarbage }
   , { specName := "LeanSwe.Compress.assume_compress_defaultApi_sanitizesCodecEnvAndReportsMissingTool"
       run := assume_compress_defaultApi_sanitizesCodecEnvAndReportsMissingTool }
   , { specName := "LeanSwe.Compress.assume_compress_decompressWith_enforcesMaxOutputBytesOnBomb"
       run := assume_compress_decompressWith_enforcesMaxOutputBytesOnBomb } ]

/-- Registered error-coverage tests for `LeanSwe.Compress.errorCoverage`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compress_toolNotFound"
       mode := .real, run := err_compress_compress_toolNotFound }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compress_invalidInput"
       mode := .real, run := err_compress_compress_invalidInput }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compress_outputLimitExceeded"
       mode := .real, run := err_compress_compress_outputLimitExceeded }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compress_timedOut"
       mode := .mocked, run := err_compress_compress_timedOut }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compress_commandFailed"
       mode := .mocked, run := err_compress_compress_commandFailed }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compress_ioError"
       mode := .real, run := err_compress_compress_ioError }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompress_toolNotFound"
       mode := .real, run := err_compress_decompress_toolNotFound }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompress_invalidInput"
       mode := .real, run := err_compress_decompress_invalidInput }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompress_corruptData"
       mode := .real, run := err_compress_decompress_corruptData }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompress_outputLimitExceeded"
       mode := .real, run := err_compress_decompress_outputLimitExceeded }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompress_timedOut"
       mode := .mocked, run := err_compress_decompress_timedOut }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompress_commandFailed"
       mode := .mocked, run := err_compress_decompress_commandFailed }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompress_ioError"
       mode := .real, run := err_compress_decompress_ioError }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_toolNotFound"
       mode := .real, run := err_compress_compressWith_toolNotFound }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_invalidInput"
       mode := .real, run := err_compress_compressWith_invalidInput }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_outputLimitExceeded"
       mode := .real, run := err_compress_compressWith_outputLimitExceeded }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_timedOut"
       mode := .real, run := err_compress_compressWith_timedOut }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_commandFailed"
       mode := .mocked, run := err_compress_compressWith_commandFailed }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_compressWith_ioError"
       mode := .real, run := err_compress_compressWith_ioError }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_toolNotFound"
       mode := .real, run := err_compress_decompressWith_toolNotFound }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_invalidInput"
       mode := .real, run := err_compress_decompressWith_invalidInput }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_corruptData"
       mode := .real, run := err_compress_decompressWith_corruptData }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_outputLimitExceeded"
       mode := .real, run := err_compress_decompressWith_outputLimitExceeded }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_timedOut"
       mode := .real, run := err_compress_decompressWith_timedOut }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_commandFailed"
       mode := .mocked, run := err_compress_decompressWith_commandFailed }
   , { testName := "LeanSwe.Compress.RuntimeTests.err_compress_decompressWith_ioError"
       mode := .real, run := err_compress_decompressWith_ioError } ]

private def mkMockSpawnErrApi (pe : ProcessError) : CompressApi :=
  let ops : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun _ => pure (.error pe) }
  Internal.mkApiM ops

private def testResourceExhaustedMappedToIoError : IO Unit := do
  let envIo : Model.CompressEnv := { allowResourceIoError := true }
  for (lbl, code) in #[("E2BIG", 7), ("EAGAIN", 11), ("ENOMEM", 12), ("ENFILE", 23),
      ("EMFILE", 24), ("ENOSPC", 28), ("EMLINK", 31), ("ENAMETOOLONG", 36), ("ENOLCK", 37),
      ("ENOSR", 63), ("EMSGSIZE", 90), ("ENOBUFS", 105)] do
    let api := mkMockSpawnErrApi { kind := .invalidInput, errnoCode := some code, message := "spawn failed" }
    let resD ← api.decompress .zstd validEmptyZstdFrame
    let _ ← expectErrKind s!"{lbl} errno maps to ioError" .ioError resD
    assertTrue s!"{lbl} decompress ioError allowed by Model"
      (Model.allowedDecompressWith envIo .zstd {} validEmptyZstdFrame resD)
    let resC ← api.compress .zstd "hi".toUTF8
    let _ ← expectErrKind s!"{lbl} compress errno maps to ioError" .ioError resC
    assertTrue s!"{lbl} compress ioError allowed by Model"
      (Model.allowedCompressWith envIo .zstd {} "hi".toUTF8 resC)
  let noErrnoMsgApi := mkMockSpawnErrApi { kind := .invalidInput, errnoCode := none, message := "cannot allocate memory" }
  let _ ← expectErrKind "errnoCode=none stays invalidInput without message scraping" .invalidInput
    (← noErrnoMsgApi.decompress .zstd validEmptyZstdFrame)
  let einvalApi := mkMockSpawnErrApi
    { kind := .invalidInput, errnoCode := some 22, message := "invalid argument: too many open files" }
  let _ ← expectErrKind "EINVAL errno overrides message substring" .invalidInput
    (← einvalApi.decompress .zstd "hi".toUTF8)
  let eloopApi := mkMockSpawnErrApi
    { kind := .invalidInput, errnoCode := some 40, message := "/tmp/too many open files/zstd: loop",
      stderr := some "leaked-stderr".toUTF8 }
  let errEloop ← expectErrKind "ELOOP errno overrides message substring" .invalidInput
    (← eloopApi.decompress .zstd "hi".toUTF8)
  assertTrue "invalidInput clears stderr and exitCode" (errEloop.stderr.isNone && errEloop.exitCode.isNone)
  let notFoundStderrApi := mkMockSpawnErrApi
    { kind := .notFound, message := "missing binary", exitCode := some 127, stderr := some "leaked-stderr".toUTF8 }
  let errNf ← expectErrKind "notFound clears stderr and exitCode" .toolNotFound
    (← notFoundStderrApi.compress .zstd "hi".toUTF8)
  assertTrue "toolNotFound clears stderr and exitCode" (errNf.stderr.isNone && errNf.exitCode.isNone)
  let cmdZeroExitApi := mkMockSpawnErrApi
    { kind := .nonZeroExit, exitCode := some 0, stderr := some "sig-err".toUTF8, message := "failed" }
  let errCmd0 ← expectErrKind "commandFailed normalizes exitCode=0 to none" .commandFailed
    (← cmdZeroExitApi.compress .zstd "hi".toUTF8)
  assertTrue "commandFailed exitCode=0 normalized to none"
    (errCmd0.exitCode.isNone && errCmd0.stderr == some "sig-err")
  let cmdNonZeroExitApi := mkMockSpawnErrApi
    { kind := .nonZeroExit, exitCode := some 3, stderr := some "sig-err3".toUTF8, message := "failed3" }
  let errCmd3 ← expectErrKind "commandFailed preserves non-zero exitCode" .commandFailed
    (← cmdNonZeroExitApi.compress .zstd "hi".toUTF8)
  assertTrue "commandFailed exitCode=3 preserved"
    (errCmd3.exitCode == some 3 && errCmd3.stderr == some "sig-err3")
  let childStderrApi := mkMockAwaitApi
    (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := "\ngzip: memory_exhausted\n".toUTF8 })
  let errChildDec ← expectErrKind "child nonzero exit classifies structurally as corruptData" .corruptData
    (← childStderrApi.decompress .gzip validEmptyZstdFrame)
  assertTrue "child nonzero exit preserves exitCode on decompress" (errChildDec.exitCode == some 1)
  let errChildComp ← expectErrKind "child nonzero exit classifies structurally as commandFailed" .commandFailed
    (← childStderrApi.compress .gzip "hi".toUTF8)
  assertTrue "child nonzero exit preserves exitCode on compress" (errChildComp.exitCode == some 1)
  let memLimitBombApi := mkMockAwaitApi
    (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := "xz: (stdin): Memory usage limit reached\n".toUTF8 })
  let _ ← expectErrKind "xz memory limit error stays corruptData" .corruptData
    (← memLimitBombApi.decompress .xz "bad".toUTF8)
  let zstdWinBombMockApi := mkMockAwaitApi
    (.exited { exitCode := 1, stdout := ByteArray.empty, stderr :=
      "/*stdin*\\ : Decoding error (36) : Frame requires too much memory for decoding \n".toUTF8 })
  let _ ← expectErrKind "zstd window limit Decoding error (36) stays corruptData" .corruptData
    (← zstdWinBombMockApi.decompress .zstd "bad".toUTF8)
  let zstdWinBombReal := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0xA0, 0x01, 0x00, 0x00, 0x08, 0x01, 0x00, 0x00]
  let errZstdWin ← expectErrKind "real zstd >128MiB window header stays corruptData" .corruptData
    (← Compress.decompress .zstd zstdWinBombReal)
  assertTrue "real zstd window header has non-zero exitCode" (errZstdWin.exitCode == some 1)
  let missingLibApi := mkMockAwaitApi
    (.exited { exitCode := 127, stdout := ByteArray.empty, stderr :=
      "zstd: error while loading shared libraries: libmissing.so: cannot open shared object file: No such file or directory\n".toUTF8 })
  let _ ← expectErrKind "ld.so missing shared library ENOENT stays corruptData on decompress" .corruptData
    (← missingLibApi.decompress .zstd "bad".toUTF8)

private def testIntegrityVectorsAndFlushHorizon : IO Unit := do
  assertTrue "decodeStderr empty is none" (Internal.decodeStderr ByteArray.empty == none)
  assertTrue "decodeStderr invalid UTF-8 is none"
    (Internal.decodeStderr (ByteArray.mk #[0xFF, 0xFE]) == none)
  assertTrue "decodeStderr non-empty UTF-8 is some"
    (Internal.decodeStderr ("err".toUTF8) == some "err")
  for codec in #[Codec.zstd, .xz, .gzip] do
    let eC ← expectErrKind s!"validateCompressOptions codec tag {repr codec}" .invalidInput
      (← Compress.compressWith codec { timeoutMs := 0 } ByteArray.empty)
    assertTrue s!"validateCompressOptions exact codec {repr codec}" (eC.codec == some codec)
    let eD ← expectErrKind s!"validateDecompressOptions codec tag {repr codec}" .invalidInput
      (← Compress.decompressWith codec { maxOutputBytes := 0 } ByteArray.empty)
    assertTrue s!"validateDecompressOptions exact codec {repr codec}" (eD.codec == some codec)
  let gzFhcrcValid := ByteArray.mk #[
    0x1F, 0x8B, 0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03,
    0xA7, 0x77, 0x01, 0x00, 0x00, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let gzFhcrcBad := ByteArray.mk #[
    0x1F, 0x8B, 0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03,
    0xA6, 0x77, 0x01, 0x00, 0x00, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let decGzOk ← expectOk "real gzip accepts valid FHCRC" (← Compress.decompress .gzip gzFhcrcValid)
  assertBytesEq "real gzip FHCRC empty output" decGzOk ByteArray.empty
  let _ ← expectErrKind "real gzip rejects bad FHCRC" .corruptData (← Compress.decompress .gzip gzFhcrcBad)
  let xzCrc32Valid := ByteArray.mk #[
    0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x01, 0x69, 0x22, 0xDE, 0x36,
    0x02, 0x00, 0x21, 0x01, 0x00, 0x00, 0x00, 0x00, 0x37, 0x27, 0x97, 0xD6,
    0x01, 0x00, 0x00, 0x41, 0x00, 0x00, 0x00, 0x00, 0x8B, 0x9E, 0xD9, 0xD3,
    0x00, 0x01, 0x15, 0x01, 0xA9, 0x63, 0x34, 0x60, 0x90, 0x42, 0x99, 0x0D,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0x59, 0x5A]
  let xzCrc32Bad := ByteArray.mk #[
    0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x01, 0x69, 0x22, 0xDE, 0x36,
    0x02, 0x00, 0x21, 0x01, 0x00, 0x00, 0x00, 0x00, 0x37, 0x27, 0x97, 0xD6,
    0x01, 0x00, 0x00, 0x41, 0x00, 0x00, 0x00, 0x00, 0x8A, 0x9E, 0xD9, 0xD3,
    0x00, 0x01, 0x15, 0x01, 0xA9, 0x63, 0x34, 0x60, 0x90, 0x42, 0x99, 0x0D,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0x59, 0x5A]
  let xzSha256Valid := ByteArray.mk #[
    0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x0A, 0xE1, 0xFB, 0x0C, 0xA1,
    0x02, 0x00, 0x21, 0x01, 0x00, 0x00, 0x00, 0x00, 0x37, 0x27, 0x97, 0xD6,
    0x01, 0x00, 0x00, 0x41, 0x00, 0x00, 0x00, 0x00, 0x55, 0x9A, 0xEA, 0xD0,
    0x82, 0x64, 0xD5, 0x79, 0x5D, 0x39, 0x09, 0x71, 0x8C, 0xDD, 0x05, 0xAB,
    0xD4, 0x95, 0x72, 0xE8, 0x4F, 0xE5, 0x55, 0x90, 0xEE, 0xF3, 0x1A, 0x88,
    0xA0, 0x8F, 0xDF, 0xFD, 0x00, 0x01, 0x31, 0x01, 0x0F, 0x82, 0xDC, 0x91,
    0x18, 0x9B, 0x4B, 0x9A, 0x01, 0x00, 0x00, 0x00, 0x00, 0x0A, 0x59, 0x5A]
  let xzSha256Bad := ByteArray.mk #[
    0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x0A, 0xE1, 0xFB, 0x0C, 0xA1,
    0x02, 0x00, 0x21, 0x01, 0x00, 0x00, 0x00, 0x00, 0x37, 0x27, 0x97, 0xD6,
    0x01, 0x00, 0x00, 0x41, 0x00, 0x00, 0x00, 0x00, 0x54, 0x9A, 0xEA, 0xD0,
    0x82, 0x64, 0xD5, 0x79, 0x5D, 0x39, 0x09, 0x71, 0x8C, 0xDD, 0x05, 0xAB,
    0xD4, 0x95, 0x72, 0xE8, 0x4F, 0xE5, 0x55, 0x90, 0xEE, 0xF3, 0x1A, 0x88,
    0xA0, 0x8F, 0xDF, 0xFD, 0x00, 0x01, 0x31, 0x01, 0x0F, 0x82, 0xDC, 0x91,
    0x18, 0x9B, 0x4B, 0x9A, 0x01, 0x00, 0x00, 0x00, 0x00, 0x0A, 0x59, 0x5A]
  let decXzCrcOk ← expectOk "real xz accepts valid CHECK_CRC32" (← Compress.decompress .xz xzCrc32Valid)
  assertBytesEq "real xz CHECK_CRC32 payload" decXzCrcOk ("A".toUTF8)
  let _ ← expectErrKind "real xz rejects bad CHECK_CRC32" .corruptData (← Compress.decompress .xz xzCrc32Bad)
  let decXzShaOk ← expectOk "real xz accepts valid CHECK_SHA256" (← Compress.decompress .xz xzSha256Valid)
  assertBytesEq "real xz CHECK_SHA256 payload" decXzShaOk ("A".toUTF8)
  let _ ← expectErrKind "real xz rejects bad CHECK_SHA256" .corruptData (← Compress.decompress .xz xzSha256Bad)
  let stSha0 := Model.State.empty
  let stSha1 := stSha0.record .xz xzSha256Valid ("A".toUTF8)
  assertTrue "Model.allowedDecompressStep accepts valid CHECK_SHA256 and enforces deterministic replay"
    (Model.allowedDecompressStep { toolStatus := fun _ => .available } stSha0 .xz {} xzSha256Valid (.ok decXzShaOk) stSha1 &&
      Model.allowedDecompressStep { toolStatus := fun _ => .available } stSha1 .xz {} xzSha256Valid (.ok decXzShaOk) stSha1 &&
      Model.allowedDecompressStep { toolStatus := fun _ => .available } stSha0 .xz {} xzSha256Bad
        (.error { kind := .corruptData, codec := some .xz, exitCode := some 1, message := "corrupt" }) stSha0)
  let zstdBufferedFcsOver := ByteArray.mk #[
    0x28, 0xB5, 0x2F, 0xFD, 0x80, 0x40, 0x40, 0x0D, 0x03, 0x00,
    0x02, 0x00, 0x10, 0x41, 0x03, 0x35, 0x0C, 0x42]
  let resZstdFcs ← Compress.decompressWith .zstd { maxOutputBytes := 1024 } zstdBufferedFcsOver
  let _ ← expectErrKind "real zstd buffered 128KiB + FCS overflow stays corruptData" .corruptData resZstdFcs
  assertTrue "Model.allowedDecompressWith accepts real zstd buffered 128KiB FCS overflow"
    (Model.allowedDecompressWith { toolStatus := fun _ => .available } .zstd
      { maxOutputBytes := 1024 } zstdBufferedFcsOver resZstdFcs)
  let mkZstdRawBlk (bs : ByteArray) (last : Nat := 0) : ByteArray :=
    let bh := (bs.size <<< 3) ||| last
    (ByteArray.mk #[UInt8.ofNat (bh &&& 0xFF), UInt8.ofNat ((bh >>> 8) &&& 0xFF),
      UInt8.ofNat ((bh >>> 16) &&& 0xFF)]) ++ bs
  let wrap1k :=
    mkZstdRawBlk (ByteArray.mk (Array.replicate 1024 0x41)) ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 1024 0x42)) ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 1024 0x43))
  let spToStream :=
    ByteArray.mk #[
      0x28, 0xB5, 0x2F, 0xFD, 0x80, 0x38, 0x00, 0x00, 0x02, 0x00,
      0x52, 0xFF, 0x0F, 0x58,
      0x45, 0x00, 0x00, 0x81, 0x51, 0x01, 0x54, 0x10, 0x00, 0x03, 0x02,
      0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x00] ++
    wrap1k ++
    ByteArray.mk #[0x45, 0x00, 0x00, 0x00, 0x01, 0x54, 0x00, 0x0B, 0x0D, 0x03, 0x0C]
  let assertModelDecompressReplay (lbl : String) (codec : Codec) (stream decOut : ByteArray) : IO Unit := do
    let availEnv : Model.CompressEnv := { toolStatus := fun _ => .available }
    let st0 := Model.State.empty
    let st1 := st0.record codec stream decOut
    assertTrue s!"Model.allowedDecompressStep accepts {lbl} and enforces deterministic replay"
      (Model.allowedDecompressStep availEnv st0 codec {} stream (.ok decOut) st1 &&
        Model.allowedDecompressStep availEnv st1 codec {} stream (.ok decOut) st1)
  let decSpStream ← expectOk "real zstd single-pass litBuffer into streaming frame"
    (← Compress.decompress .zstd spToStream)
  assertModelDecompressReplay "real zstd single-pass litBuffer into streaming frame" .zstd spToStream decSpStream
  let extDictStream :=
    ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x00] ++
    wrap1k ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 16 0x23)) ++
    ByteArray.mk #[
      0x3C, 0x00, 0x00, 0x00, 0x01, 0x54, 0x00, 0x06, 0x0E, 0x43,
      0xC5, 0x00, 0x00, 0x80] ++
    ByteArray.mk (Array.replicate 16 0x5F) ++
    ByteArray.mk #[0x01, 0x54, 0x00, 0x0B, 0x1F, 0x03, 0x0C]
  let decExtDict ← expectOk "real zstd ExtDict ring match parity"
    (← Compress.decompress .zstd extDictStream)
  assertModelDecompressReplay "real zstd ExtDict ring match parity" .zstd extDictStream decExtDict
  let fh0 := ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x00, 0x00]
  let priorLit32 :=
    ByteArray.mk #[0x1C, 0x01, 0x00, 0x04, 0x02] ++
    ByteArray.mk (Array.replicate 32 0x5F) ++
    ByteArray.mk #[0x00]
  let wrap3136 :=
    priorLit32 ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 992 0x41)) ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 1024 0x42)) ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 64 0x43)) ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 1024 0x44))
  let reach2112 :=
    mkZstdRawBlk (ByteArray.mk (Array.replicate 1024 0x45)) ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 1024 0x46)) ++
    mkZstdRawBlk (ByteArray.mk (Array.replicate 64 0x47))
  let emptyRawInDstStream :=
    fh0 ++ wrap3136 ++ ByteArray.mk #[
      0xBD, 0x01, 0x00, 0x00, 0x15, 0x00, 0x33, 0x11, 0x98, 0x89, 0xC0, 0x4C, 0x04, 0x66, 0x22,
      0x30, 0x13, 0x81, 0x99, 0x08, 0xCC, 0x44, 0x60, 0x26, 0x02, 0x33, 0x11, 0x98, 0x89, 0xC0,
      0x4C, 0x04, 0x66, 0x22, 0x30, 0x13, 0x81, 0x99, 0x08, 0xCC, 0x44, 0x60, 0x26, 0x02, 0x33,
      0x11, 0x98, 0x89, 0xC0, 0x4C, 0x04, 0x66, 0x22, 0x30, 0x44, 0x04, 0x02, 0x01]
  let decEmptyRaw ← expectOk "real zstd empty raw literals in-dst wildcopy"
    (← Compress.decompress .zstd emptyRawInDstStream)
  assertModelDecompressReplay "real zstd empty raw literals in-dst wildcopy" .zstd emptyRawInDstStream decEmptyRaw
  let ringSeqParityBlks : Array (String × ByteArray) := #[
    ("lit wildcopy gated on oMatchEnd", ByteArray.mk #[
      0xFD, 0x01, 0x00, 0xE9, 0x48, 0x16, 0x00, 0x43, 0x84, 0x04, 0x66, 0xB2, 0xD3, 0xCC, 0x08,
      0x9A, 0x19, 0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33,
      0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19, 0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD,
      0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19, 0x41,
      0x33, 0x23, 0x60, 0x13, 0xCD, 0x31]),
    ("short offset lt8 wildcopy", ByteArray.mk #[
      0xFD, 0x01, 0x00, 0x41, 0x47, 0x16, 0x00, 0x43, 0x84, 0x22, 0xEC, 0x12, 0x68, 0x66, 0x04,
      0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19,
      0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82, 0x66,
      0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19, 0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD, 0x8C, 0xA0,
      0x99, 0x11, 0x68, 0xA2, 0xC9, 0x05]),
    ("mid offset 8..15 step8 wildcopy", ByteArray.mk #[
      0xFD, 0x01, 0x00, 0x41, 0x47, 0x16, 0x00, 0x43, 0x84, 0x22, 0xBC, 0x70, 0xD0, 0xCC, 0x08,
      0x9A, 0x19, 0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33,
      0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19, 0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD,
      0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19, 0x41,
      0x33, 0x23, 0xD0, 0x44, 0x93, 0x0B]),
    ("safecopy oMatchEnd gt oend_w short offset", ByteArray.mk #[
      0xFD, 0x01, 0x00, 0xC1, 0x47, 0x16, 0x00, 0x43, 0x84, 0x0B, 0x56, 0x0A, 0x68, 0x66, 0x04,
      0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19,
      0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82, 0x66,
      0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19, 0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD, 0x8C, 0xA0,
      0x99, 0x11, 0xA0, 0x89, 0xE6, 0x18]),
    ("safecopy oMatchEnd gt oend_w wide offset", ByteArray.mk #[
      0xFD, 0x01, 0x00, 0x39, 0x47, 0x16, 0x00, 0x43, 0x84, 0x0D, 0xCC, 0xB4, 0xA1, 0x99, 0x11,
      0x34, 0x33, 0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A, 0x19, 0x41, 0x33, 0x23, 0x68, 0x66,
      0x04, 0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82, 0x66, 0x46, 0xD0, 0xCC, 0x08, 0x9A,
      0x19, 0x41, 0x33, 0x23, 0x68, 0x66, 0x04, 0xCD, 0x8C, 0xA0, 0x99, 0x11, 0x34, 0x33, 0x82,
      0x66, 0x46, 0xA0, 0x89, 0xA6, 0x11])
  ]
  for (lbl, blkTail) in ringSeqParityBlks do
    let stream := fh0 ++ wrap3136 ++ reach2112 ++ blkTail
    let decOut ← expectOk s!"real zstd {lbl}" (← Compress.decompress .zstd stream)
    assertModelDecompressReplay s!"real zstd {lbl}" .zstd stream decOut
  let xzPartialCopy := ByteArray.mk #[
    0xfd, 0x37, 0x7a, 0x58, 0x5a, 0x00, 0x00, 0x00, 0xff, 0x12, 0xd9, 0x41,
    0x02, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00, 0x74, 0x2f, 0xe5, 0xa3,
    0xe0, 0x00, 0x0a, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x01, 0x18, 0x0b, 0xfa, 0xf4, 0x4f, 0x35, 0x06, 0x72, 0x9e, 0x7a,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x59, 0x5a
  ]
  let resXzPartial ← Compress.decompressWith .xz { maxOutputBytes := 1 } xzPartialCopy
  assertTrue "Model.allowedDecompressWith accepts real xzPartialCopy at maxOutputBytes=1"
    (Model.allowedDecompressWith { toolStatus := fun _ => .available } .xz
      { maxOutputBytes := 1 } xzPartialCopy resXzPartial)
  let mkPartialFlushMock (exitCode : Int) (outSz : Nat) : RawProcessOpsM IO :=
    { SysBridge.defaultOps with
      spawn := fun _ => return .ok { handleId := 1, pid := 1, pgid := 1 }
      awaitOutput := fun _ _ _ _ =>
        return .ok (.exited {
          exitCode := exitCode
          stdout := ByteArray.mk (Array.replicate outSz 0x41)
          stderr := ByteArray.empty })
      killProcessGroup := fun _ => return .ok ()
      reap := fun _ => return .ok ()
      activeProcessCount := return 0 }
  let mockFlushDec ← (Internal.mkApiM (mkPartialFlushMock 1 4)).decompressWith .xz
    { maxOutputBytes := 1 } xzPartialCopy
  assertTrue "decompressWith prioritizes non-zero exit over partial stdout > maxOutputBytes"
    (match mockFlushDec with
    | .error e =>
      e.kind == .corruptData && e.exitCode == some 1 &&
      Model.allowedDecompressWith { toolStatus := fun _ => .available } .xz
        { maxOutputBytes := 1 } xzPartialCopy mockFlushDec
    | .ok _ => false)
  let mockFlushComp ← (Internal.mkApiM (mkPartialFlushMock 1 4)).compressWith .xz
    { maxOutputBytes := 1 } ("hi".toUTF8)
  assertTrue "compressWith prioritizes non-zero exit over partial stdout > maxOutputBytes"
    (match mockFlushComp with | .error e => e.kind == .commandFailed && e.exitCode == some 1 | .ok _ => false)
  let mockZeroOver ← (Internal.mkApiM (mkPartialFlushMock 0 4)).decompressWith .xz
    { maxOutputBytes := 1 } xzPartialCopy
  assertTrue "decompressWith reports outputLimitExceeded when exit=0 and stdout > maxOutputBytes"
    (match mockZeroOver with | .error e => e.kind == .outputLimitExceeded && e.exitCode == none | .ok _ => false)
  let bcjPlain :=
    ByteArray.mk #[
      0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x4C, 0x65, 0x61, 0x6E, 0x53, 0x77, 0x65, 0x20,
      0x78, 0x38, 0x36, 0x20, 0x42, 0x43, 0x4A, 0x20, 0x26, 0x20, 0x64, 0x69, 0x63, 0x74,
      0x3E, 0x36, 0x34, 0x4D, 0x69, 0x42, 0x21, 0x90, 0xE8, 0x00, 0x00, 0x00, 0x00, 0xC3]
  let xzX86Bcj :=
    ByteArray.mk #[
      0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04, 0xE6, 0xD6, 0xB4, 0x46, 0x04, 0xC1,
      0x2E, 0x2A, 0x04, 0x00, 0x21, 0x01, 0x16, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x09, 0x28, 0xE5, 0x84, 0x01, 0x00, 0x29, 0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x4C,
      0x65, 0x61, 0x6E, 0x53, 0x77, 0x65, 0x20, 0x78, 0x38, 0x36, 0x20, 0x42, 0x43, 0x4A,
      0x20, 0x26, 0x20, 0x64, 0x69, 0x63, 0x74, 0x3E, 0x36, 0x34, 0x4D, 0x69, 0x42, 0x21,
      0x90, 0xE8, 0x29, 0x00, 0x00, 0x00, 0xC3, 0x00, 0x00, 0x00, 0xFD, 0x85, 0x57, 0x96,
      0x85, 0xCD, 0xDC, 0xD5, 0x00, 0x01, 0x4A, 0x2A, 0x72, 0xDB, 0xAB, 0xF1, 0x1F, 0xB6,
      0xF3, 0x7D, 0x01, 0x00, 0x00, 0x00, 0x00, 0x04, 0x59, 0x5A]
  let xzDict96MiB :=
    ByteArray.mk #[
      0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, 0x04, 0xE6, 0xD6, 0xB4, 0x46, 0x04, 0xC0,
      0x2E, 0x2A, 0x21, 0x01, 0x1D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x90, 0xCE, 0x62, 0xA3, 0x01, 0x00, 0x29, 0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x4C,
      0x65, 0x61, 0x6E, 0x53, 0x77, 0x65, 0x20, 0x78, 0x38, 0x36, 0x20, 0x42, 0x43, 0x4A,
      0x20, 0x26, 0x20, 0x64, 0x69, 0x63, 0x74, 0x3E, 0x36, 0x34, 0x4D, 0x69, 0x42, 0x21,
      0x90, 0xE8, 0x00, 0x00, 0x00, 0x00, 0xC3, 0x00, 0x00, 0x00, 0xFD, 0x85, 0x57, 0x96,
      0x85, 0xCD, 0xDC, 0xD5, 0x00, 0x01, 0x4A, 0x2A, 0x72, 0xDB, 0xAB, 0xF1, 0x1F, 0xB6,
      0xF3, 0x7D, 0x01, 0x00, 0x00, 0x00, 0x00, 0x04, 0x59, 0x5A]
  let decBcj ← expectOk "real xz x86 BCJ+LZMA2 stream decompresses"
    (← Compress.decompress .xz xzX86Bcj)
  assertTrue "real xz x86 BCJ+LZMA2 plaintext matches" (decBcj == bcjPlain)
  let decDict96 ← expectOk "real xz 96 MiB dictionary stream decompresses"
    (← Compress.decompress .xz xzDict96MiB)
  assertTrue "real xz 96 MiB dictionary plaintext matches" (decDict96 == bcjPlain)
  let decBcjLim ← Compress.decompressWith .xz { maxOutputBytes := 1 } xzX86Bcj
  assertTrue "real xz x86 BCJ stream over maxOutputBytes stays outputLimitExceeded"
    (match decBcjLim with | .error e => e.kind == .outputLimitExceeded | .ok _ => false)
  let availEnv : Model.CompressEnv := { toolStatus := fun _ => .available }
  let stBcj0 := Model.State.empty
  let stBcj1 := stBcj0.record .xz xzX86Bcj bcjPlain
  let stBcj2 := stBcj1.record .xz xzDict96MiB bcjPlain
  assertTrue "Model.allowedDecompressStep accepts BCJ+LZMA2, 96 MiB dict, replay, and limit enforcement"
    (Model.allowedDecompressStep availEnv stBcj0 .xz {} xzX86Bcj (.ok decBcj) stBcj1 &&
     Model.allowedDecompressStep availEnv stBcj1 .xz {} xzX86Bcj (.ok decBcj) stBcj1 &&
     Model.allowedDecompressStep availEnv stBcj1 .xz { maxOutputBytes := 1 } xzX86Bcj decBcjLim stBcj1 &&
     Model.allowedDecompressStep availEnv stBcj1 .xz {} xzDict96MiB (.ok decDict96) stBcj2 &&
     Model.allowedDecompressStep availEnv stBcj2 .xz {} xzDict96MiB (.ok decDict96) stBcj2)

private def testStatefulRelationalContracts : IO Unit := do
  let availEnv : Model.CompressEnv := { toolStatus := fun _ => .available }
  let mut st := Model.State.empty
  for codec in #[Codec.gzip, Codec.zstd, Codec.xz] do
    let sample := s!"LeanSwe.Compress stateful relational check {reprStr codec}\n".toUTF8
    let comp ← expectOk s!"live compress {reprStr codec}" (← Compress.compress codec sample)
    let st1 := st.record codec comp sample
    assertTrue s!"Model.allowedCompressStep accepts live compress {reprStr codec}"
      (Model.allowedCompressStep availEnv st codec {} sample (.ok comp) st1)
    st := st1
    let decExact ← expectOk s!"live decompress exact {reprStr codec}"
      (← Compress.decompressWith codec { maxOutputBytes := sample.size } comp)
    assertBytesEq s!"live round-trip payload {reprStr codec}" decExact sample
    assertTrue s!"Model.allowedDecompressStep enforces exact replay {reprStr codec}"
      (Model.allowedDecompressStep availEnv st codec { maxOutputBytes := sample.size } comp (.ok decExact) st)
    let decTooSmall ← Compress.decompressWith codec { maxOutputBytes := sample.size - 1 } comp
    assertTrue s!"live decompress tighter maxOutputBytes is outputLimitExceeded {reprStr codec}"
      (match decTooSmall with | .error e => e.kind == .outputLimitExceeded | .ok _ => false)
    assertTrue s!"Model.allowedDecompressStep accepts outputLimitExceeded {reprStr codec}"
      (Model.allowedDecompressStep availEnv st codec { maxOutputBytes := sample.size - 1 } comp decTooSmall st)

/-- Run all runtime tests for `LeanSwe.Compress`. -/
def runAll : IO Unit := do
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  testInvalidInputsNoSpawn
  testResourceExhaustedMappedToIoError
  testIntegrityVectorsAndFlushHorizon
  testStatefulRelationalContracts
  IO.println "PASS: LeanSwe.Compress runtime tests"

end LeanSwe.Compress.RuntimeTests
