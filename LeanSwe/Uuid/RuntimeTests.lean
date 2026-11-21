import Core.Assumptions
import LeanSwe.LinuxSyscall.TestSupport.Seccomp
import LeanSwe.Uuid.Interface

namespace LeanSwe.Uuid.RuntimeTests

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.TimeRand

private def check (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw <| IO.userError s!"LeanSwe.Uuid.RuntimeTests FAILED: {name}"

private def checkErrKind {α : Type} (name : String) (res : Except UuidError α) (expected : UuidErrorKind) : IO Unit := do
  match res with
  | .ok _ => throw <| IO.userError s!"LeanSwe.Uuid.RuntimeTests FAILED ({name}): expected error {repr expected}, got ok"
  | .error e =>
    if e.kind != expected || e.message.isEmpty then
      throw <| IO.userError s!"LeanSwe.Uuid.RuntimeTests FAILED ({name}): got {repr e}"

private def isOkEq (res : Except UuidError Uuid) (expected : Uuid) : Bool :=
  match res with
  | .ok u => u == expected
  | .error _ => false

private def runBatchTests (count : Nat) : IO Unit := do
  let mut hexes : Array String := Array.mkEmpty count
  for i in [0:count] do
    match ← Uuid.getUuid with
    | .error e =>
      throw <| IO.userError s!"LeanSwe.Uuid.RuntimeTests FAILED (getUuid #{i}): {e.message}"
    | .ok u =>
      check s!"batch #{i} size == 16" (u.bytes.size == 16)
      check s!"batch #{i} v4 version nibble" ((u.bytes[6]! &&& (0xF0 : UInt8)) == (0x40 : UInt8))
      check s!"batch #{i} RFC 4122 variant bits" ((u.bytes[8]! &&& (0xC0 : UInt8)) == (0x80 : UInt8))
      let s := Uuid.toString u
      let sUpper := String.ofList (s.toList.map Char.toUpper)
      check s!"batch #{i} toString length 36" (s.length == 36)
      check s!"batch #{i} isValid" (Uuid.isValid s)
      check s!"batch #{i} isValid upper" (Uuid.isValid sUpper)
      check s!"batch #{i} parse round-trip" (isOkEq (Uuid.parse s) u)
      check s!"batch #{i} parse upper round-trip" (isOkEq (Uuid.parse sUpper) u)
      let h := Uuid.toHex u
      let hUpper := String.ofList (h.toList.map Char.toUpper)
      check s!"batch #{i} toHex length 32" (h.length == 32)
      check s!"batch #{i} isValid rejects compact hex" (!Uuid.isValid h)
      checkErrKind s!"batch #{i} parse rejects compact hex" (Uuid.parse h) .invalidFormat
      check s!"batch #{i} parseHex round-trip" (isOkEq (Uuid.parseHex h) u)
      check s!"batch #{i} parseHex upper round-trip" (isOkEq (Uuid.parseHex hUpper) u)
      hexes := hexes.push h
  let sorted := hexes.qsort (· < ·)
  check "batch count preserved" (sorted.size == count)
  for i in [0:(count - 1)] do
    if sorted[i]! == sorted[i + 1]! then
      throw <| IO.userError s!"LeanSwe.Uuid.RuntimeTests FAILED: collision detected on {sorted[i]!}"

private def runEdgeCaseTests : IO Unit := do
  checkErrKind "fromRandomBytes empty" (Uuid.fromRandomBytes ByteArray.empty) .invalidLength
  checkErrKind "fromRandomBytes 15 bytes" (Uuid.fromRandomBytes (ByteArray.mk (Array.replicate 15 0))) .invalidLength
  checkErrKind "fromRandomBytes 17 bytes" (Uuid.fromRandomBytes (ByteArray.mk (Array.replicate 17 0))) .invalidLength

  match Uuid.fromRandomBytes (ByteArray.mk (Array.replicate 16 0)) with
  | .error e => throw <| IO.userError s!"fromRandomBytes 16 zero bytes failed: {e.message}"
  | .ok uZero =>
    check "zero payload toString" (Uuid.toString uZero == "00000000-0000-4000-8000-000000000000")
    check "zero payload toHex" (Uuid.toHex uZero == "00000000000040008000000000000000")

  let sample := "550e8400-e29b-41d4-a716-446655440000"
  let sampleUpper := "550E8400-E29B-41D4-A716-446655440000"
  let sampleHex := "550e8400e29b41d4a716446655440000"
  check "canonical sample isValid" (Uuid.isValid sample)
  check "uppercase sample isValid" (Uuid.isValid sampleUpper)
  match Uuid.parse sample, Uuid.parse sampleUpper, Uuid.parseHex sampleHex with
  | .ok u1, .ok u2, .ok u3 =>
    check "parse case-insensitive equality" (u1 == u2)
    check "parse vs parseHex equality" (u1 == u3)
    check "toString canonicalization" (Uuid.toString u2 == sample)
    check "toHex canonicalization" (Uuid.toHex u1 == sampleHex)
  | _, _, _ => throw <| IO.userError "LeanSwe.Uuid.RuntimeTests FAILED: sample parse failed"

  checkErrKind "parse empty" (Uuid.parse "") .invalidFormat
  checkErrKind "parse 35 chars" (Uuid.parse "550e8400-e29b-41d4-a716-44665544000") .invalidFormat
  checkErrKind "parse 37 chars" (Uuid.parse "550e8400-e29b-41d4-a716-4466554400000") .invalidFormat
  checkErrKind "parse compact hex" (Uuid.parse sampleHex) .invalidFormat
  checkErrKind "parse misplaced hyphen" (Uuid.parse "550e840-0e29b-41d4-a716-446655440000") .invalidFormat
  checkErrKind "parse extra hyphen" (Uuid.parse "550e8400-e29b-41d4-a716-44665544-000") .invalidFormat
  checkErrKind "parse non-hex char" (Uuid.parse "550e8400-e29b-41d4-a716-44665544000g") .invalidFormat
  checkErrKind "parse v1 rejected" (Uuid.parse "550e8400-e29b-11d4-a716-446655440000") .invalidVersion
  checkErrKind "parse v3 rejected" (Uuid.parse "550e8400-e29b-31d4-a716-446655440000") .invalidVersion
  checkErrKind "parse v5 rejected" (Uuid.parse "550e8400-e29b-51d4-a716-446655440000") .invalidVersion
  checkErrKind "parse v7 rejected" (Uuid.parse "550e8400-e29b-71d4-a716-446655440000") .invalidVersion
  checkErrKind "parse nil rejected" (Uuid.parse "00000000-0000-0000-0000-000000000000") .invalidVersion
  checkErrKind "parse variant 0 rejected" (Uuid.parse "550e8400-e29b-41d4-0716-446655440000") .invalidVersion
  checkErrKind "parse variant 7 rejected" (Uuid.parse "550e8400-e29b-41d4-7716-446655440000") .invalidVersion
  checkErrKind "parse variant c rejected" (Uuid.parse "550e8400-e29b-41d4-c716-446655440000") .invalidVersion
  checkErrKind "parse variant f rejected" (Uuid.parse "550e8400-e29b-41d4-f716-446655440000") .invalidVersion
  check "isValid false on v1" (!Uuid.isValid "550e8400-e29b-11d4-a716-446655440000")
  check "isValid false on variant c" (!Uuid.isValid "550e8400-e29b-41d4-c716-446655440000")

  checkErrKind "parseHex empty" (Uuid.parseHex "") .invalidFormat
  checkErrKind "parseHex 31 chars" (Uuid.parseHex "550e8400e29b41d4a71644665544000") .invalidFormat
  checkErrKind "parseHex 33 chars" (Uuid.parseHex "550e8400e29b41d4a7164466554400000") .invalidFormat
  checkErrKind "parseHex canonical hyphenated" (Uuid.parseHex sample) .invalidFormat
  checkErrKind "parseHex non-hex char" (Uuid.parseHex "550e8400e29b41d4a71644665544000z") .invalidFormat
  checkErrKind "parseHex v1 rejected" (Uuid.parseHex "550e8400e29b11d4a716446655440000") .invalidVersion
  checkErrKind "parseHex v7 rejected" (Uuid.parseHex "550e8400e29b71d4a716446655440000") .invalidVersion
  checkErrKind "parseHex nil rejected" (Uuid.parseHex "00000000000000000000000000000000") .invalidVersion
  checkErrKind "parseHex variant c rejected" (Uuid.parseHex "550e8400e29b41d4c716446655440000") .invalidVersion

private def mkFailingTimeRandOps (e : Errno) : TimeRandOps :=
  { clock_gettime := fun _ => return .error e
    clock_nanosleep := fun _ _ _ => return .error e
    getrandom := fun _ _ => return .error e }

/-- Verify `Uuid.fromRandomBytes` returns `.invalidLength` on wrong byte counts. -/
def err_uuid_fromRandomBytes_invalidLength : IO Unit := do
  checkErrKind "fromRandomBytes empty" (Uuid.fromRandomBytes ByteArray.empty) .invalidLength
  checkErrKind "fromRandomBytes 15" (Uuid.fromRandomBytes (ByteArray.mk (Array.replicate 15 0))) .invalidLength

/-- Verify `Uuid.parse` returns `.invalidFormat` on malformed canonical UUID strings. -/
def err_uuid_parse_invalidFormat : IO Unit := do
  checkErrKind "parse empty" (Uuid.parse "") .invalidFormat
  checkErrKind "parse compact hex" (Uuid.parse "550e8400e29b41d4a716446655440000") .invalidFormat

/-- Verify `Uuid.parse` returns `.invalidVersion` on non-v4 or non-RFC-4122-variant UUIDs. -/
def err_uuid_parse_invalidVersion : IO Unit := do
  checkErrKind "parse v1" (Uuid.parse "550e8400-e29b-11d4-a716-446655440000") .invalidVersion
  checkErrKind "parse variant c" (Uuid.parse "550e8400-e29b-41d4-c716-446655440000") .invalidVersion

/-- Verify `Uuid.parseHex` returns `.invalidFormat` on malformed compact hex UUID strings. -/
def err_uuid_parseHex_invalidFormat : IO Unit := do
  checkErrKind "parseHex empty" (Uuid.parseHex "") .invalidFormat
  checkErrKind "parseHex hyphenated" (Uuid.parseHex "550e8400-e29b-41d4-a716-446655440000") .invalidFormat

/-- Verify `Uuid.parseHex` returns `.invalidVersion` on non-v4 or non-RFC-4122-variant compact hex UUIDs. -/
def err_uuid_parseHex_invalidVersion : IO Unit := do
  checkErrKind "parseHex v1" (Uuid.parseHex "550e8400e29b11d4a716446655440000") .invalidVersion
  checkErrKind "parseHex variant c" (Uuid.parseHex "550e8400e29b41d4c716446655440000") .invalidVersion

/-- Verify mocked `Uuid.mkApi.getUuid` surfaces `.entropyFailed` when `getrandom` fails with `EIO`. -/
def err_uuid_getUuid_entropyFailed : IO Unit := do
  let api := Uuid.mkApi (mkFailingTimeRandOps Errno.EIO)
  checkErrKind "mock getUuid EIO" (← api.getUuid) .entropyFailed

/-- Verify mocked `Uuid.mkApi.getUuid` (`v4` backend) surfaces `.entropyFailed` when `getrandom` fails with `ENOMEM`. -/
def err_uuid_v4_entropyFailed : IO Unit := do
  let api := Uuid.mkApi (mkFailingTimeRandOps Errno.ENOMEM)
  checkErrKind "mock v4 ENOMEM" (← api.getUuid) .entropyFailed

/-- Registered error-coverage tests matching `Uuid/SpecTests.lean`. -/
def registeredErrorTests : Array RegisteredErrorTest :=
  #[ { testName := "LeanSwe.Uuid.RuntimeTests.err_uuid_fromRandomBytes_invalidLength"
       mode := .real
       run := err_uuid_fromRandomBytes_invalidLength }
   , { testName := "LeanSwe.Uuid.RuntimeTests.err_uuid_parse_invalidFormat"
       mode := .real
       run := err_uuid_parse_invalidFormat }
   , { testName := "LeanSwe.Uuid.RuntimeTests.err_uuid_parse_invalidVersion"
       mode := .real
       run := err_uuid_parse_invalidVersion }
   , { testName := "LeanSwe.Uuid.RuntimeTests.err_uuid_parseHex_invalidFormat"
       mode := .real
       run := err_uuid_parseHex_invalidFormat }
   , { testName := "LeanSwe.Uuid.RuntimeTests.err_uuid_parseHex_invalidVersion"
       mode := .real
       run := err_uuid_parseHex_invalidVersion }
   , { testName := "LeanSwe.Uuid.RuntimeTests.err_uuid_getUuid_entropyFailed"
       mode := .mocked
       run := err_uuid_getUuid_entropyFailed }
   , { testName := "LeanSwe.Uuid.RuntimeTests.err_uuid_v4_entropyFailed"
       mode := .mocked
       run := err_uuid_v4_entropyFailed } ]

private def seccompWorker (errName : String) : IO UInt32 := do
  let expected? : Option UInt32 :=
    match errName with
    | "EPERM" => some Errno.EPERM
    | "EINTR" => some Errno.EINTR
    | _ => none
  let some expected := expected?
    | do
        IO.eprintln s!"uuid seccomp-worker: unsupported errno {errName}"
        return 1
  let rc ← LeanSwe.LinuxSyscall.TestSupport.Seccomp.installTimeRandSeccompErrno expected
  if rc != 0 then
    IO.eprintln s!"uuid seccomp-worker: installTimeRandSeccompErrno failed errno={rc}"
    return 1
  match ← Uuid.getUuid with
  | .ok u =>
    IO.eprintln s!"uuid seccomp-worker ({errName}): expected entropyFailed, got {Uuid.toString u}"
    return 2
  | .error e =>
    if e.kind != .entropyFailed || e.errnoCode != some expected || e.message.isEmpty then
      IO.eprintln s!"uuid seccomp-worker ({errName}): unexpected error {repr e}"
      return 3
    return 0

/-- CLI entrypoint for `--uuid-probe`. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["--seccomp-worker", errName] => seccompWorker errName
  | _ =>
    IO.eprintln s!"unknown uuid-probe args: {args}"
    return 1

private def checkLiveSeccomp : IO Unit := do
  let exe ← IO.appPath
  for errName in ["EPERM", "EINTR"] do
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #["--uuid-probe", "--seccomp-worker", errName]
    }
    if out.exitCode != 0 then
      throw <| IO.userError s!"LeanSwe.Uuid.RuntimeTests FAILED (live seccomp {errName} exit={out.exitCode}): {out.stderr}"

/-- Execute the empirical OS-entropy batch, error-coverage, and validation runtime tests for `LeanSwe.Uuid`. -/
def runAll : IO Unit := do
  Core.runRegisteredErrorTests registeredErrorTests
  runBatchTests 1000
  runEdgeCaseTests
  checkLiveSeccomp
  IO.println "PASS: LeanSwe.Uuid runtime tests"

end LeanSwe.Uuid.RuntimeTests
