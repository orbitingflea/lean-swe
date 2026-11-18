import Core.Assumptions
import LeanSwe.Fs.Interface
import LeanSwe.Process.Interface
import LeanSwe.Compress.Types
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
    { Raw.defaultOps with
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

private def testToolNotFoundAndNonExecutable : IO Unit := do
  let missingOps : RawProcessOpsM IO :=
    { Raw.defaultOps with
      spawn := fun req =>
        Raw.defaultOps.spawn { req with program := "/nonexistent/lean-swe-missing-compress-tool" } }
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
      { Raw.defaultOps with
        spawn := fun req =>
          Raw.defaultOps.spawn { req with program := nonExecPath.toString } }
    let nonExecApi := Internal.mkApiM nonExecOps
    let avail ← nonExecApi.isToolAvailable .zstd
    assertTrue "non-executable tool isToolAvailable false" (!avail)
    let _ ← expectErrKind "non-executable tool compress" .toolNotFound
      (← nonExecApi.compress .xz "hi".toUTF8)
    let _ ← expectErrKind "non-executable tool decompress" .toolNotFound
      (← nonExecApi.decompress .gzip "hi".toUTF8)
  finally
    IO.FS.removeDirAll tmpDir

private def testOutputLimitExceeded : IO Unit := do
  let zeros := mkZeroBytes (2 * 1024 * 1024)
  for codec in #[Codec.zstd, .xz, .gzip] do
    let comp ← expectOk s!"compress zero bomb {repr codec}" (← compress codec zeros)
    assertTrue s!"zero bomb compressed compactly {repr codec}" (comp.size < 4096)
    let _ ← expectErrKind s!"decompress bomb {repr codec}" .outputLimitExceeded
      (← decompressWith codec { maxOutputBytes := 1024 } comp)

private def testTimedOutAndEnvSanitization : IO Unit := do
  let slowOps : RawProcessOpsM IO :=
    { Raw.defaultOps with
      spawn := fun req =>
        Raw.defaultOps.spawn { req with program := "sleep", args := #["2"] } }
  let slowApi := Internal.mkApiM slowOps
  let _ ← expectErrKind "timeout compress" .timedOut
    (← slowApi.compressWith .zstd { timeoutMs := 50 } ByteArray.empty)
  let poisoned : Array (String × Option String) :=
    #[("XZ_OPT", some "--lean-swe-invalid-xz-flag"),
      ("XZ_DEFAULTS", some "--lean-swe-invalid-xz-defaults"),
      ("ZSTD_CLEVEL", some "999"),
      ("ZSTD_NBTHREADS", some "999"),
      ("GZIP", some "--lean-swe-invalid-gzip-flag")]
  let poisonedOps : RawProcessOpsM IO :=
    { Raw.defaultOps with
      spawn := fun req =>
        Raw.defaultOps.spawn { req with env := poisoned ++ req.env } }
  let poisonedApi := Internal.mkApiM poisonedOps
  let sample := "sanitized-env-check-payload".toUTF8
  for codec in #[Codec.zstd, .xz, .gzip] do
    let avail ← poisonedApi.isToolAvailable codec
    assertTrue s!"poisoned env isToolAvailable {repr codec}" avail
    let comp ← expectOk s!"poisoned env compress {repr codec}" (← poisonedApi.compress codec sample)
    let dec ← expectOk s!"poisoned env decompress {repr codec}" (← poisonedApi.decompress codec comp)
    assertBytesEq s!"poisoned env round-trip {repr codec}" dec sample

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

private def mkMockAwaitApi (outcome : Raw.ExecOutcome) : CompressApi :=
  let ops : RawProcessOpsM IO :=
    { Raw.defaultOps with
      spawn := fun _ => pure (.ok { handleId := 1, pid := 1, pgid := 1 })
      awaitOutput := fun _ _ _ _ => pure (.ok outcome)
      killProcessGroup := fun _ => pure (.ok ())
      reap := fun _ => pure (.ok ())
      activeProcessCount := pure 0 }
  Internal.mkApiM ops

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

private def runEnametoolongProbe (label opTag : String) : IO Unit :=
  let longPath := String.ofList (List.replicate 5000 'a')
  runCompressProbeWithPath label opTag longPath .ioError

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
  let _ ← expectErrKind "decompress timedOut" .timedOut (← api.decompress .zstd "hi".toUTF8)

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

/-- Run all runtime tests for `LeanSwe.Compress`. -/
def runAll : IO Unit := do
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  testInvalidInputsNoSpawn
  IO.println "PASS: LeanSwe.Compress runtime tests"

end LeanSwe.Compress.RuntimeTests
