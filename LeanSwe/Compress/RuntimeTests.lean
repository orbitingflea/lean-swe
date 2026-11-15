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

/-- Run all runtime tests for `LeanSwe.Compress`. -/
def runAll : IO Unit := do
  testToolAvailability
  testRoundTrips
  testCompressionOptionsAndDeterminism
  testPythonInterop
  testCorruptAndTruncatedAndTrailingGarbage
  testInvalidInputsNoSpawn
  testToolNotFoundAndNonExecutable
  testOutputLimitExceeded
  testTimedOutAndEnvSanitization
  IO.println "PASS: LeanSwe.Compress runtime tests"

end LeanSwe.Compress.RuntimeTests
