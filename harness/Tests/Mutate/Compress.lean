import Tests.Common
import LeanSwe.Compress.RuntimeTests

namespace Tests.Mutate.Compress

open LeanSwe
open Tests.Common

private def runCompressMutateExtra : IO Unit := do
  let checkB (label : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"{label} failed")
  checkB "zstd compress args default"
    (Compress.Internal.mkCompressArgs .zstd {} == #["-c", "-q", "--no-progress"])
  checkB "zstd compress args explicit"
    (Compress.Internal.mkCompressArgs .zstd { level := some 19, threads := some 0 } ==
      #["-c", "-q", "--no-progress", "-19", "-T0"])
  checkB "xz compress args explicit"
    (Compress.Internal.mkCompressArgs .xz { level := some 0, threads := some 4 } ==
      #["-c", "-q", "-0", "-T4"])
  checkB "gzip compress args explicit"
    (Compress.Internal.mkCompressArgs .gzip { level := some 9 } == #["-c", "-n", "-9"])
  checkB "zstd decompress args"
    (Compress.Internal.mkDecompressArgs .zstd ==
      #["-d", "-c", "-q", "--no-progress", "--format=zstd"])
  checkB "xz decompress args"
    (Compress.Internal.mkDecompressArgs .xz ==
      #["-d", "-c", "-q", "-T1", "--format=xz"])
  checkB "gzip decompress args"
    (Compress.Internal.mkDecompressArgs .gzip == #["-d", "-c", "-n"])
  let gzMin20 := ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0x02, 0x03, 0x03, 0x00, 0, 0, 0, 0, 0, 0, 0, 0]
  checkB "hasGzipHeader 19 vs 20 boundary"
    (Compress.Internal.hasGzipHeader gzMin20 == true &&
      Compress.Internal.hasGzipHeader (gzMin20.extract 0 19) == false)
  let cReq := Compress.Internal.mkCompressRequest .zstd { timeoutMs := 77, maxOutputBytes := 128 } ("ab".toUTF8)
  checkB "compress req slack+env"
    (cReq.program == "zstd" && cReq.cwd == none && cReq.env == Compress.codecSanitizedEnv &&
      cReq.inheritEnv == true && cReq.stdin == "ab".toUTF8 && cReq.timeoutMs == some 77 &&
      cReq.maxOutputBytes == some (128 + 4096))
  let dReq := Compress.Internal.mkDecompressRequest .xz { timeoutMs := 88, maxOutputBytes := 256 } ("cd".toUTF8)
  checkB "decompress req slack+env"
    (dReq.program == "xz" && dReq.cwd == none && dReq.env == Compress.codecSanitizedEnv &&
      dReq.inheritEnv == true && dReq.stdin == "cd".toUTF8 && dReq.timeoutMs == some 88 &&
      dReq.maxOutputBytes == some (256 + 4096))
  let vReq := Compress.Internal.mkToolVersionRequest .gzip
  checkB "version req env+limits"
    (vReq.program == "gzip" && vReq.args == #["--version"] && vReq.cwd == none &&
      vReq.env == Compress.codecSanitizedEnv && vReq.inheritEnv == true &&
      vReq.stdin == ByteArray.empty && vReq.timeoutMs == some 5000 && vReq.maxOutputBytes == some 65536)
  let isInvFor (c : Compress.Codec) (r : Except Compress.CompressError Unit) : Bool :=
    match r with
    | .error e =>
      e.kind == .invalidInput && e.codec == some c && e.exitCode == none && e.stderr == none && !e.message.isEmpty
    | .ok () => false
  checkB "validate zstd boundaries+codec"
    (isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { timeoutMs := 0 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { maxOutputBytes := 0 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { maxInputBytes := some 1 } ("ab".toUTF8)) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { level := some 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .zstd { level := some 1, threads := some 0 } ByteArray.empty).isOk &&
      (Compress.Internal.validateCompressOptions .zstd { level := some 19, threads := some 4294967295 } ByteArray.empty).isOk &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { level := some 20 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { threads := some 4294967296 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateDecompressOptions .zstd { timeoutMs := 0 } ByteArray.empty) &&
      isInvFor .xz (Compress.Internal.validateDecompressOptions .xz { maxOutputBytes := 0 } ByteArray.empty))
  checkB "validate xz+gzip+maxInput boundaries+codec"
    (isInvFor .xz (Compress.Internal.validateCompressOptions .xz { timeoutMs := 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .xz { level := some 0, threads := some 16384 } ByteArray.empty).isOk &&
      (Compress.Internal.validateCompressOptions .xz { level := some 9 } ByteArray.empty).isOk &&
      isInvFor .xz (Compress.Internal.validateCompressOptions .xz { level := some 10 } ByteArray.empty) &&
      isInvFor .xz (Compress.Internal.validateCompressOptions .xz { threads := some 16385 } ByteArray.empty) &&
      isInvFor .gzip (Compress.Internal.validateCompressOptions .gzip { level := some 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .gzip { level := some 9 } ByteArray.empty).isOk &&
      isInvFor .gzip (Compress.Internal.validateCompressOptions .gzip { threads := some 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .gzip { maxInputBytes := some 2 } ("ab".toUTF8)).isOk &&
      isInvFor .gzip (Compress.Internal.validateCompressOptions .gzip { maxInputBytes := some 1 } ("ab".toUTF8)) &&
      (Compress.Internal.validateDecompressOptions .gzip { maxInputBytes := some 2 } ("ab".toUTF8)).isOk &&
      isInvFor .gzip (Compress.Internal.validateDecompressOptions .gzip { maxInputBytes := some 1 } ("ab".toUTF8)))
  let badUtf8 := ByteArray.mk #[0xff, 0xfe]
  checkB "decodeStderr empty+invalidUtf8+valid"
    (Compress.Internal.decodeStderr ByteArray.empty == none &&
      Compress.Internal.decodeStderr badUtf8 == none &&
      Compress.Internal.decodeStderr ("ok".toUTF8) == some "ok")
  let errZero := Compress.Internal.classifyProcessError .zstd
    { kind := .nonZeroExit, exitCode := some 0, stderr := some ("e".toUTF8), message := "" }
  let errEmptySerr := Compress.Internal.classifyProcessError .zstd
    { kind := .ioError, stderr := some ByteArray.empty, message := "io" }
  let errBadUtf8Serr := Compress.Internal.classifyProcessError .zstd
    { kind := .ioError, stderr := some badUtf8, message := "io" }
  checkB "classifyProcessError zero exitCode + fallback msg + stderr norm"
    (errZero.kind == .commandFailed && errZero.codec == some .zstd && errZero.exitCode == none &&
      errZero.stderr == some "e" && !errZero.message.isEmpty &&
      errEmptySerr.stderr == none && errBadUtf8Serr.stderr == none)
  let errNf := Compress.Internal.classifyProcessError .xz
    { kind := .notFound, exitCode := some 127, stderr := some ("leak".toUTF8), message := "nf" }
  let errInv := Compress.Internal.classifyProcessError .gzip
    { kind := .invalidInput, errnoCode := some 22, stderr := some ("leak".toUTF8), message := "inv" }
  let errOom := Compress.Internal.classifyProcessError .gzip
    { kind := .invalidInput, errnoCode := some 12, stderr := some ("oom".toUTF8), message := "oom" }
  checkB "classifyProcessError stderr scrub + oom"
    (errNf.kind == .toolNotFound && errNf.codec == some .xz && errNf.exitCode == none && errNf.stderr == none &&
      errInv.kind == .invalidInput && errInv.codec == some .gzip && errInv.exitCode == none && errInv.stderr == none &&
      errOom.kind == .ioError && errOom.codec == some .gzip && errOom.exitCode == none && errOom.stderr == some "oom")
  let okExact := Compress.Internal.classifyExitResult .gzip false 3 ByteArray.empty
    { exitCode := 0, stdout := "abc".toUTF8, stderr := ByteArray.empty }
  let badFraming := Compress.Internal.classifyExitResult .gzip true 16 ("bad".toUTF8)
    { exitCode := 0, stdout := "abc".toUTF8, stderr := ByteArray.empty }
  let overMaxBadFraming := Compress.Internal.classifyExitResult .gzip true 2 ("bad".toUTF8)
    { exitCode := 0, stdout := "abcd".toUTF8, stderr := "leaked".toUTF8 }
  let gzBig ← match ← Compress.compress .gzip (ByteArray.mk (Array.replicate 270000 0)) with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"gzip 270k zero compress failed: {e.message}")
  let calStream := gzBig ++ ByteArray.mk #[0x1F, 0x9D, 0x90, 0x00]
  let overMaxCal := Compress.Internal.classifyExitResult .gzip true 2 calStream
    { exitCode := 0, stdout := "abcd".toUTF8, stderr := "warn".toUTF8 }
  let compFailEmptySerr := Compress.Internal.classifyExitResult .zstd false 16 ByteArray.empty
    { exitCode := 2, stdout := ByteArray.empty, stderr := ByteArray.empty }
  let decFailBadUtf8Serr := Compress.Internal.classifyExitResult .xz true 16 ByteArray.empty
    { exitCode := 1, stdout := ByteArray.empty, stderr := badUtf8 }
  checkB "classifyExitResult exact maxOut + exit0 framing + bounded cal + exitCode/stderr"
    (okExact == .ok ("abc".toUTF8) &&
      (match badFraming with | .error e => e.kind == .corruptData && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match overMaxBadFraming with | .error e => e.kind == .corruptData && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match overMaxCal with | .error e => e.kind == .outputLimitExceeded && e.codec == some .gzip && e.exitCode == none && e.stderr == some "warn" | _ => false) &&
      (match compFailEmptySerr with | .error e => e.kind == .commandFailed && e.codec == some .zstd && e.exitCode == some 2 && e.stderr == none | _ => false) &&
      (match decFailBadUtf8Serr with | .error e => e.kind == .corruptData && e.codec == some .xz && e.exitCode == some 1 && e.stderr == none | _ => false))
  let mkMockRaw (out : Process.ExecOutcome) : Process.RawProcessOpsM Id :=
    { mapRawError := fun _ => { kind := .ioError, message := "mock" }
      spawn := fun _ => .ok { handleId := 1, pid := 1, pgid := 1 }
      awaitOutput := fun _ _ _ _ => .ok out
      killProcessGroup := fun _ => .ok ()
      reap := fun _ => .ok ()
      activeProcessCount := 0 }
  let avail0 : Bool := Compress.Internal.isToolAvailable
    (mkMockRaw (.exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty })) .zstd
  let avail1 : Bool := Compress.Internal.isToolAvailable
    (mkMockRaw (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty })) .zstd
  let avail127 : Bool := Compress.Internal.isToolAvailable
    (mkMockRaw (.exited { exitCode := 127, stdout := ByteArray.empty, stderr := ByteArray.empty })) .xz
  let decOomCal : Except Compress.CompressError ByteArray :=
    Compress.Internal.decompressWith (mkMockRaw (.outputLimitExceeded ("abc".toUTF8) ByteArray.empty)) .gzip { maxOutputBytes := 2 } calStream
  let decToCal : Except Compress.CompressError ByteArray :=
    Compress.Internal.decompressWith (mkMockRaw (.timedOut ByteArray.empty ByteArray.empty)) .gzip { maxOutputBytes := 2 } calStream
  let decNzOver : Except Compress.CompressError ByteArray :=
    Compress.Internal.decompressWith (mkMockRaw (.exited { exitCode := 1, stdout := ByteArray.mk #[0x41, 0x42, 0x43], stderr := ByteArray.empty })) .gzip { maxOutputBytes := 2 } calStream
  let compNzOver : Except Compress.CompressError ByteArray :=
    Compress.Internal.compressWith (mkMockRaw (.exited { exitCode := 1, stdout := ByteArray.mk #[0x41, 0x42, 0x43], stderr := ByteArray.empty })) .gzip { maxOutputBytes := 2 } ("ab".toUTF8)
  checkB "isToolAvailable nonzero exit + decompressWith bounded cal"
    (avail0 == true && avail1 == false && avail127 == false &&
      (match decOomCal with | .error e => e.kind == .outputLimitExceeded && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match decToCal with | .error e => e.kind == .timedOut && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match decNzOver with | .error e => e.kind == .corruptData && e.exitCode == some 1 | _ => false) &&
      (match compNzOver with | .error e => e.kind == .commandFailed && e.exitCode == some 1 | _ => false))

/-- Mutation test suite for `LeanSwe.Compress`. -/
def compressSuite : MutateSuite :=
  { name := "Compress"
    runBase := do Compress.RuntimeTests.runAll; return none
    runExtra := runCompressMutateExtra }

end Tests.Mutate.Compress
