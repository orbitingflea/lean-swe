import Std.Data.HashSet
import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.Uuid.Types
import LeanSwe.Uuid.Model
import LeanSwe.Uuid.Interface

namespace Fuzz.Uuid

open Fuzz.Common
open LeanSwe.Uuid

private def exceptEq {ε α : Type} [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

private def logUuidErrHit (qualOp : String) (e : UuidError) : IO Unit :=
  let ctor := match e.kind with
    | .entropyFailed => "LeanSwe.Uuid.UuidErrorKind.entropyFailed"
    | .invalidLength => "LeanSwe.Uuid.UuidErrorKind.invalidLength"
    | .invalidFormat => "LeanSwe.Uuid.UuidErrorKind.invalidFormat"
    | .invalidVersion => "LeanSwe.Uuid.UuidErrorKind.invalidVersion"
  logErrHit qualOp ctor "real"

private inductive UuidOp where
  | drawGetUuid
  | drawV4
  | fromBytes (bs : ByteArray)
  | parseStr (s : String)
  | parseHexStr (s : String)
  | formatRaw (bs : ByteArray)
  | mapErr (e : UuidRawError)
  deriving BEq, DecidableEq

private def reprUuidOp : UuidOp → String
  | .drawGetUuid => "drawGetUuid"
  | .drawV4 => "drawV4"
  | .fromBytes bs => s!"fromBytes(len={bs.size})"
  | .parseStr s => s!"parseStr({repr s})"
  | .parseHexStr s => s!"parseHexStr({repr s})"
  | .formatRaw bs => s!"formatRaw(len={bs.size})"
  | .mapErr e => s!"mapErr({repr e})"

private structure UuidRunState where
  seen : Std.HashSet String := {}
  tracker : CoverageTracker := CoverageTracker.empty
  steps : Nat := 0

private def requiredBuckets : Array CoverageBucket := #[
  bucket "getUuid" "ok",
  bucket "v4" "ok",
  bucket "fromRandomBytes" "ok",
  bucket "fromRandomBytes" "err.invalidLength",
  bucket "toString" "canonical16",
  bucket "toString" "non16",
  bucket "toHex" "ok",
  bucket "parse" "ok.lower",
  bucket "parse" "ok.upper",
  bucket "parse" "ok.mixed",
  bucket "parse" "err.invalidFormat.len",
  bucket "parse" "err.invalidFormat.hyphen",
  bucket "parse" "err.invalidFormat.nonhex",
  bucket "parse" "err.invalidVersion.ver",
  bucket "parse" "err.invalidVersion.var",
  bucket "parseHex" "ok.lower",
  bucket "parseHex" "ok.upper",
  bucket "parseHex" "err.invalidFormat.len",
  bucket "parseHex" "err.invalidFormat.nonhex",
  bucket "parseHex" "err.invalidVersion.ver",
  bucket "parseHex" "err.invalidVersion.var",
  bucket "isValid" "true",
  bucket "isValid" "false",
  bucket "mapRawError" "osError.empty",
  bucket "mapRawError" "osError.detail",
  bucket "mapRawError" "shortRead.empty",
  bucket "mapRawError" "shortRead.detail",
  bucket "mapRawError" "userError.empty",
  bucket "mapRawError" "userError.detail",
  bucket "mkApi.scripted" "partialChunks",
  bucket "mkApi.scripted" "eintrRecovery",
  bucket "mkApi.scripted" "invalidChunkLen",
  bucket "mkApi.scripted" "err.entropyFailed"
]

private def classifyCaseBucket (s : String) : String :=
  let hasLower := s.toList.any fun c => 'a' ≤ c && c ≤ 'f'
  let hasUpper := s.toList.any fun c => 'A' ≤ c && c ≤ 'F'
  if hasLower && hasUpper then "ok.mixed"
  else if hasUpper then "ok.upper"
  else "ok.lower"

private def checkValidUuidCodec (u : Uuid) (tag : String) : IO (String × String) := do
  unless Model.isValidV4Uuid u do
    throw (IO.userError s!"UUID_INVALID_V4 ({tag}): {repr u}")
  let canon := toString u
  let hex := toHex u
  unless canon == Model.toString u do
    throw (IO.userError s!"UUID_TOSTRING_MISMATCH ({tag}): got {repr canon}, model {repr (Model.toString u)}")
  unless hex == Model.toHex u do
    throw (IO.userError s!"UUID_TOHEX_MISMATCH ({tag}): got {repr hex}, model {repr (Model.toHex u)}")
  unless canon.length == 36 && hex.length == 32 do
    throw (IO.userError s!"UUID_FORMAT_LEN ({tag}): canon={canon.length} hex={hex.length}")
  unless exceptEq (parse canon) (.ok u) do
    throw (IO.userError s!"UUID_PARSE_ROUNDTRIP ({tag}): {repr canon}")
  unless exceptEq (parse canon.toUpper) (.ok u) do
    throw (IO.userError s!"UUID_PARSE_UPPER_ROUNDTRIP ({tag}): {repr canon.toUpper}")
  unless exceptEq (parseHex hex) (.ok u) do
    throw (IO.userError s!"UUID_PARSEHEX_ROUNDTRIP ({tag}): {repr hex}")
  unless exceptEq (parseHex hex.toUpper) (.ok u) do
    throw (IO.userError s!"UUID_PARSEHEX_UPPER_ROUNDTRIP ({tag}): {repr hex.toUpper}")
  unless isValid canon && isValid canon.toUpper do
    throw (IO.userError s!"UUID_ISVALID_FALSE ({tag}): {repr canon}")
  return (canon, hex)

private def classifyParseErr (s : String) (e : UuidError) : String :=
  match e.kind with
  | .invalidFormat =>
    let cs := s.toList
    if cs.length != 36 then "err.invalidFormat.len"
    else if (Model.stripCanonicalHyphens cs).isNone then "err.invalidFormat.hyphen"
    else "err.invalidFormat.nonhex"
  | .invalidVersion =>
    if e.message.startsWith "UUID version" then "err.invalidVersion.ver"
    else "err.invalidVersion.var"
  | _ => "err.other"

private def classifyParseHexErr (s : String) (e : UuidError) : String :=
  match e.kind with
  | .invalidFormat =>
    if s.toList.length != 32 then "err.invalidFormat.len"
    else "err.invalidFormat.nonhex"
  | .invalidVersion =>
    if e.message.startsWith "UUID version" then "err.invalidVersion.ver"
    else "err.invalidVersion.var"
  | _ => "err.other"

private def execUuidOp (st : UuidRunState) (op : UuidOp) (emitCov : Bool := true) : IO UuidRunState := do
  let mut st := { st with steps := st.steps + 1 }
  match op with
  | .drawGetUuid =>
    match ← getUuid with
    | .error e =>
      throw (IO.userError s!"UUID_GETUUID_FAILED: {repr e}")
    | .ok u =>
      let (_, hex) ← checkValidUuidCodec u "getUuid"
      if st.seen.contains hex then
        throw (IO.userError s!"UUID_DUPLICATE_DETECTED (getUuid): {hex} after {st.seen.size} draws")
      st := { st with
        seen := st.seen.insert hex
        tracker := ((st.tracker.record "getUuid" "ok").record "toString" "canonical16").record "toHex" "ok" }
  | .drawV4 =>
    match ← v4 with
    | .error e =>
      throw (IO.userError s!"UUID_V4_FAILED: {repr e}")
    | .ok u =>
      let (_, hex) ← checkValidUuidCodec u "v4"
      if st.seen.contains hex then
        throw (IO.userError s!"UUID_DUPLICATE_DETECTED (v4): {hex} after {st.seen.size} draws")
      st := { st with
        seen := st.seen.insert hex
        tracker := ((st.tracker.record "v4" "ok").record "toString" "canonical16").record "toHex" "ok" }
  | .fromBytes bs =>
    let actual := fromRandomBytes bs
    let expected := Model.fromRandomBytes bs
    unless exceptEq actual expected do
      throw (IO.userError s!"UUID_FROMBYTES_MISMATCH: len={bs.size} actual={repr actual} expected={repr expected}")
    match actual with
    | .ok u =>
      let _ ← checkValidUuidCodec u "fromRandomBytes"
      st := { st with
        tracker := ((st.tracker.record "fromRandomBytes" "ok").record "toString" "canonical16").record "toHex" "ok" }
    | .error e =>
      if e.message.isEmpty then
        throw (IO.userError s!"UUID_FROMBYTES_EMPTY_MSG: {repr e}")
      if emitCov then
        logUuidErrHit "LeanSwe.Uuid.fromRandomBytes" e
      st := { st with tracker := st.tracker.record "fromRandomBytes" "err.invalidLength" }
  | .parseStr s =>
    let actual := parse s
    let expected := Model.parse s
    unless exceptEq actual expected do
      throw (IO.userError s!"UUID_PARSE_MISMATCH: input={repr s} actual={repr actual} expected={repr expected}")
    let validActual := isValid s
    let validExpected := Model.isValid s
    unless validActual == validExpected && validActual == actual.isOk do
      throw (IO.userError s!"UUID_ISVALID_MISMATCH: input={repr s} actual={validActual} expected={validExpected}")
    let mut tr := st.tracker.record "isValid" (if validActual then "true" else "false")
    match actual with
    | .ok u =>
      let (canon, _) ← checkValidUuidCodec u "parse"
      unless canon == s.toLower do
        throw (IO.userError s!"UUID_PARSE_CANON_MISMATCH: input={repr s} canon={repr canon}")
      tr := tr.record "parse" (classifyCaseBucket s)
    | .error e =>
      if e.message.isEmpty then
        throw (IO.userError s!"UUID_PARSE_EMPTY_MSG: input={repr s} err={repr e}")
      if emitCov then
        logUuidErrHit "LeanSwe.Uuid.parse" e
      tr := tr.record "parse" (classifyParseErr s e)
    st := { st with tracker := tr }
  | .parseHexStr s =>
    let actual := parseHex s
    let expected := Model.parseHex s
    unless exceptEq actual expected do
      throw (IO.userError s!"UUID_PARSEHEX_MISMATCH: input={repr s} actual={repr actual} expected={repr expected}")
    match actual with
    | .ok u =>
      let (_, hex) ← checkValidUuidCodec u "parseHex"
      unless hex == s.toLower do
        throw (IO.userError s!"UUID_PARSEHEX_CANON_MISMATCH: input={repr s} hex={repr hex}")
      let b := if s.toList.any (fun c => 'A' ≤ c && c ≤ 'F') then "ok.upper" else "ok.lower"
      st := { st with tracker := st.tracker.record "parseHex" b }
    | .error e =>
      if e.message.isEmpty then
        throw (IO.userError s!"UUID_PARSEHEX_EMPTY_MSG: input={repr s} err={repr e}")
      if emitCov then
        logUuidErrHit "LeanSwe.Uuid.parseHex" e
      st := { st with tracker := st.tracker.record "parseHex" (classifyParseHexErr s e) }
  | .formatRaw bs =>
    let u : Uuid := { bytes := bs }
    let sActual := toString u
    let sExpected := Model.toString u
    let hActual := toHex u
    let hExpected := Model.toHex u
    unless sActual == sExpected do
      throw (IO.userError s!"UUID_FORMAT_STR_MISMATCH: len={bs.size} actual={repr sActual} expected={repr sExpected}")
    unless hActual == hExpected do
      throw (IO.userError s!"UUID_FORMAT_HEX_MISMATCH: len={bs.size} actual={repr hActual} expected={repr hExpected}")
    let b := if bs.size == 16 then "canonical16" else "non16"
    st := { st with tracker := (st.tracker.record "toString" b).record "toHex" "ok" }
  | .mapErr raw =>
    let actual := mapRawError raw
    let expected := Model.mapRawError raw
    unless actual == expected do
      throw (IO.userError s!"UUID_MAPERR_MISMATCH: raw={repr raw} actual={repr actual} expected={repr expected}")
    if actual.kind != .entropyFailed || actual.message.isEmpty then
      throw (IO.userError s!"UUID_MAPERR_INVARIANT: raw={repr raw} actual={repr actual}")
    let b := match raw with
      | .osError _ d => if d.isEmpty then "osError.empty" else "osError.detail"
      | .shortRead _ d => if d.isEmpty then "shortRead.empty" else "shortRead.detail"
      | .userError d => if d.isEmpty then "userError.empty" else "userError.detail"
    st := { st with tracker := st.tracker.record "mapRawError" b }
  return st

private def curatedCorpus : Array UuidOp := #[
  .fromBytes ByteArray.empty,
  .fromBytes (ByteArray.mk (Array.replicate 15 0xAB)),
  .fromBytes (ByteArray.mk (Array.replicate 16 0x00)),
  .fromBytes (ByteArray.mk (Array.replicate 16 0xFF)),
  .fromBytes (ByteArray.mk (Array.replicate 17 0x5A)),
  .formatRaw ByteArray.empty,
  .formatRaw (ByteArray.mk #[0x01, 0xAF, 0x90]),
  .formatRaw (ByteArray.mk (Array.replicate 15 0x12)),
  .formatRaw (ByteArray.mk (Array.replicate 16 0x34)),
  .formatRaw (ByteArray.mk (Array.replicate 17 0x56)),
  .parseStr "550e8400-e29b-41d4-a716-446655440000",
  .parseStr "550E8400-E29B-41D4-A716-446655440000",
  .parseStr "550e8400-E29B-41d4-A716-446655440000",
  .parseStr "00000000-0000-4000-8000-000000000000",
  .parseStr "ffffffff-ffff-4fff-bfff-ffffffffffff",
  .parseStr "",
  .parseStr "550e8400-e29b-41d4-a716-44665544000",
  .parseStr "550e8400-e29b-41d4-a716-4466554400000",
  .parseStr "550e8400e29b41d4a716446655440000",
  .parseStr "550e8400_e29b-41d4-a716-446655440000",
  .parseStr "550e8400-e29b_41d4-a716-446655440000",
  .parseStr "550e8400-e29b-41d4_a716-446655440000",
  .parseStr "550e8400-e29b-41d4-a716_446655440000",
  .parseStr "550g8400-e29b-41d4-a716-446655440000",
  .parseStr "550e8400-e29b-41d4-a716-44665544000z",
  .parseStr "550e8400-e29b-31d4-a716-446655440000",
  .parseStr "550e8400-e29b-51d4-a716-446655440000",
  .parseStr "550e8400-e29b-41d4-7716-446655440000",
  .parseStr "550e8400-e29b-41d4-c716-446655440000",
  .parseHexStr "550e8400e29b41d4a716446655440000",
  .parseHexStr "550E8400E29B41D4A716446655440000",
  .parseHexStr "00000000000040009000000000000000",
  .parseHexStr "",
  .parseHexStr "550e8400e29b41d4a71644665544000",
  .parseHexStr "550e8400e29b41d4a7164466554400000",
  .parseHexStr "550e8400-e29b-41d4-a716-446655440000",
  .parseHexStr "550e8400e29b41d4a71644665544000g",
  .parseHexStr "550e8400e29b11d4a716446655440000",
  .parseHexStr "550e8400e29b41d40716446655440000",
  .parseHexStr "550e8400e29b41d4f716446655440000",
  .mapErr (.osError 22 ""),
  .mapErr (.osError 11 "EAGAIN"),
  .mapErr (.shortRead 8 ""),
  .mapErr (.shortRead 0 "exhausted"),
  .mapErr (.userError ""),
  .mapErr (.userError "entropy failure")
]

private def genRandomAscii (r : Rng) (minLen maxLen : Nat) : String × Rng := Id.run do
  let (len, r1) := r.nextRange minLen maxLen
  let mut cur := r1
  let mut cs : List Char := []
  let alphabet : Array Char :=
    #['0','1','2','3','4','5','6','7','8','9',
      'a','b','c','d','e','f','A','B','C','D','E','F',
      '-','_','g','G','z',' ','!','/']
  for _ in [:len] do
    let (ch, nxt) := cur.choose alphabet '0'
    cur := nxt
    cs := ch :: cs
  return (String.ofList cs.reverse, cur)

private def mutateUuidString (r : Rng) (canon : String) : String × Rng :=
  let (mode, r1) := r.nextNat 6
  let cs := canon.toList
  match mode with
  | 0 => (canon, r1)
  | 1 => (canon.toUpper, r1)
  | 2 =>
    let (idx, r2) := r1.nextNat cs.length
    let (ch, r3) := r2.choose #['0','3','4','5','7','8','a','c','f','g','-','_','Z'] 'g'
    (String.ofList (cs.set idx ch), r3)
  | 3 =>
    let (n, r2) := r1.nextRange 0 (cs.length - 1)
    (String.ofList (cs.take n), r2)
  | 4 => (canon ++ "0", r1)
  | _ =>
    let mixed := cs.zipIdx.map fun (c, i) => if i % 2 == 0 then c.toUpper else c.toLower
    (String.ofList mixed, r1)

private def genRandomOp (r : Rng) : UuidOp × Rng :=
  let (tag, r1) := r.nextNat 10
  match tag with
  | 0 => (.drawGetUuid, r1)
  | 1 => (.drawV4, r1)
  | 2 =>
    let (lenChoice, r2) := r1.nextNat 4
    let len := if lenChoice < 2 then 16 else if lenChoice == 2 then 15 else 17
    let (bs, r3) := r2.nextBytes len
    (.fromBytes bs, r3)
  | 3 =>
    let (bs, r2) := r1.nextBytesRange 0 32
    (.fromBytes bs, r2)
  | 4 =>
    let (bs, r2) := r1.nextBytes 16
    match Model.fromRandomBytes bs with
    | .ok u =>
      let (s, r3) := mutateUuidString r2 (Model.toString u)
      (.parseStr s, r3)
    | .error _ => (.parseStr "", r2)
  | 5 =>
    let (s, r2) := genRandomAscii r1 0 42
    (.parseStr s, r2)
  | 6 =>
    let (bs, r2) := r1.nextBytes 16
    match Model.fromRandomBytes bs with
    | .ok u =>
      let (s, r3) := mutateUuidString r2 (Model.toHex u)
      (.parseHexStr s, r3)
    | .error _ => (.parseHexStr "", r2)
  | 7 =>
    let (s, r2) := genRandomAscii r1 0 38
    (.parseHexStr s, r2)
  | 8 =>
    let (bs, r2) := r1.nextBytesRange 0 24
    (.formatRaw bs, r2)
  | _ =>
    let (kind, r2) := r1.nextNat 3
    let (code, r3) := r2.nextU32
    let (emptyMsg, r4) := r3.nextBool
    let msg := if emptyMsg then "" else s!"detail-{code}"
    match kind with
    | 0 => (.mapErr (.osError code msg), r4)
    | 1 => (.mapErr (.shortRead (code.toNat % 20) msg), r4)
    | _ => (.mapErr (.userError msg), r4)

private def runTrace (ops : Array UuidOp) (st0 : UuidRunState := {}) (emitCov : Bool := true) :
    IO UuidRunState := do
  let mut st := st0
  for op in ops do
    st ← execUuidOp st op emitCov
  return st

private def runScriptedEntropyChecks (st : UuidRunState) (emitCov : Bool := true) : IO UuidRunState := do
  let runScript (label : String)
      (script : Array (Except LeanSwe.LinuxSyscall.Errno ByteArray)) :
      IO (Except UuidError Uuid × Array Nat) := do
    let idxRef ← IO.mkRef 0
    let reqLensRef ← IO.mkRef (#[] : Array Nat)
    let ops : LeanSwe.LinuxSyscall.TimeRand.TimeRandOpsM IO := {
      clock_gettime := fun _ => pure (.error LeanSwe.LinuxSyscall.Errno.EINVAL)
      clock_nanosleep := fun _ _ _ => pure (.error LeanSwe.LinuxSyscall.Errno.EINVAL)
      getrandom := fun len flags => do
        unless flags == {} do
          throw (IO.userError s!"UUID_SCRIPT_FLAGS ({label}): expected empty GrndFlags")
        reqLensRef.modify (·.push len.toNat)
        let i ← idxRef.get
        idxRef.set (i + 1)
        match script[i]? with
        | some r => pure r
        | none => throw (IO.userError s!"UUID_SCRIPT_OVERREAD ({label}): call #{i}")
    }
    let res ← (mkApi ops).getUuid
    return (res, ← reqLensRef.get)
  let chunks : Array ByteArray := #[
    ByteArray.mk #[0x01],
    ByteArray.mk #[0x02, 0x03, 0x04],
    ByteArray.mk #[0x05, 0x06, 0x07, 0x08, 0x09],
    ByteArray.mk #[0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10]
  ]
  let full16 := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  let (rPartial, lensPartial) ← runScript "partialChunks" (chunks.map .ok)
  unless exceptEq rPartial (Model.fromRandomBytes full16) && lensPartial == #[16, 15, 12, 7] do
    throw (IO.userError s!"UUID_SCRIPT_PARTIAL_MISMATCH: res={repr rPartial} lens={lensPartial}")
  let mut eintrScript : Array (Except LeanSwe.LinuxSyscall.Errno ByteArray) := Array.mkEmpty 32
  for _ in [:16] do
    eintrScript := eintrScript.push (.error LeanSwe.LinuxSyscall.Errno.EINTR)
  for b in [1:17] do
    eintrScript := eintrScript.push (.ok (ByteArray.mk #[UInt8.ofNat b]))
  let (rEintr, lensEintr) ← runScript "eintrRecovery" eintrScript
  unless exceptEq rEintr (Model.fromRandomBytes full16) && lensEintr.size == 32 do
    throw (IO.userError s!"UUID_SCRIPT_EINTR_MISMATCH: res={repr rEintr} calls={lensEintr.size}")
  let (rZero, _) ← runScript "zeroChunk" #[.ok ByteArray.empty]
  let (rOver, _) ← runScript "overChunk" #[.ok (ByteArray.mk (Array.replicate 17 0xAA))]
  let (rOver2, _) ← runScript "overChunk2" #[.ok (ByteArray.mk (Array.replicate 10 0x11)), .ok (ByteArray.mk (Array.replicate 7 0x22))]
  for (lbl, r) in #[("zero", rZero), ("over17", rOver), ("over10+7", rOver2)] do
    match r with
    | .error e =>
      unless e.kind == .entropyFailed && !e.message.isEmpty do
        throw (IO.userError s!"UUID_SCRIPT_CHUNK_ERR ({lbl}): {repr e}")
    | .ok u => throw (IO.userError s!"UUID_SCRIPT_CHUNK_OK ({lbl}): {repr u}")
  let (rEio, _) ← runScript "eio" #[.error LeanSwe.LinuxSyscall.Errno.EIO]
  let (rNomem, _) ← runScript "enomem" #[.error LeanSwe.LinuxSyscall.Errno.ENOMEM]
  let (rExhaust, _) ← runScript "eintrExhaust" (Array.replicate 32 (.error LeanSwe.LinuxSyscall.Errno.EINTR))
  for (lbl, r) in #[("eio", rEio), ("enomem", rNomem), ("exhaust", rExhaust)] do
    match r with
    | .error e =>
      unless e.kind == .entropyFailed && !e.message.isEmpty do
        throw (IO.userError s!"UUID_SCRIPT_ERR ({lbl}): {repr e}")
    | .ok u => throw (IO.userError s!"UUID_SCRIPT_OK ({lbl}): {repr u}")
  if emitCov then
    logErrHit "LeanSwe.Uuid.getUuid" "LeanSwe.Uuid.UuidErrorKind.entropyFailed" "mocked"
    logErrHit "LeanSwe.Uuid.v4" "LeanSwe.Uuid.UuidErrorKind.entropyFailed" "mocked"
  let tr := (((st.tracker.record "mkApi.scripted" "partialChunks")
    |>.record "mkApi.scripted" "eintrRecovery")
    |>.record "mkApi.scripted" "invalidChunkLen")
    |>.record "mkApi.scripted" "err.entropyFailed"
  return { st with tracker := tr, steps := st.steps + 8 }

private def runSmokeImpl (_cfg : FuzzConfig) : IO Unit := do
  let mut st : UuidRunState := {}
  st ← runTrace curatedCorpus st true
  st ← runScriptedEntropyChecks st true
  for _ in [:1000] do
    st ← execUuidOp st .drawGetUuid true
    st ← execUuidOp st .drawV4 true
  recordSuiteSteps st.steps
  IO.println (st.tracker.formatReport "uuid")
  assertCoverage "uuid" st.tracker requiredBuckets
  IO.println s!"UUID_SMOKE_OK steps={st.steps} unique_v4={st.seen.size}"

private def runFuzzImpl (cfg : FuzzConfig) : IO Unit := do
  let mut st : UuidRunState := {}
  st ← runTrace curatedCorpus st true
  st ← runScriptedEntropyChecks st true
  let minDraws := max cfg.steps 2000
  let halfDraws := (minDraws + 1) / 2
  for _ in [:halfDraws] do
    st ← execUuidOp st .drawGetUuid true
    st ← execUuidOp st .drawV4 true
  let mut rng := Rng.seed (cfg.seed ^^^ 0x4f1bbcdcbfa54001)
  for _ in [:cfg.steps] do
    let (op, r') := genRandomOp rng
    rng := r'
    st ← execUuidOp st op true
  recordSuiteSteps st.steps
  IO.println (st.tracker.formatReport "uuid")
  assertCoverage "uuid" st.tracker requiredBuckets
  IO.println s!"UUID_FUZZ_OK steps={st.steps} unique_v4={st.seen.size} seed={cfg.seed}"

private def selfTestShrinkImpl (seedVal : UInt64) : IO Unit := do
  let mut rng := Rng.seed (seedVal ^^^ 0x9e3779b97f4a7c15)
  let mut trace1 : Array UuidOp := Array.mkEmpty 24
  for _ in [:24] do
    let (op, r') := genRandomOp rng
    rng := r'
    trace1 := trace1.push op
  let fault1 : UuidOp := .parseStr "INJECTED-UUID-SINGLE-FAULT-0001"
  let (idx1, r2) := rng.nextNat trace1.size
  rng := r2
  trace1 := trace1.set! idx1 fault1
  let fails1 (xs : Array UuidOp) : IO Bool := do
    let _ ← runTrace xs {} false
    return xs.any (· == fault1)
  match ← verifyShrinker fails1 trace1 1 with
  | .error msg => throw (IO.userError s!"UUID_SHRINK_SINGLE_FAILED: {msg}")
  | .ok shrunk =>
    unless shrunk == #[fault1] do
      let shown := shrunk.toList.map reprUuidOp
      throw (IO.userError s!"UUID_SHRINK_SINGLE_MISMATCH: {shown}")
  let mut trace2 : Array UuidOp := Array.mkEmpty 24
  for _ in [:24] do
    let (op, r') := genRandomOp rng
    rng := r'
    trace2 := trace2.push op
  let faultA : UuidOp := .mapErr (.userError "INJECTED-UUID-PAIR-A")
  let faultB : UuidOp := .mapErr (.userError "INJECTED-UUID-PAIR-B")
  let (idxA, r3) := rng.nextRange 0 11
  let (idxB, _) := r3.nextRange 12 23
  trace2 := trace2.set! idxA faultA
  trace2 := trace2.set! idxB faultB
  let fails2 (xs : Array UuidOp) : IO Bool := do
    let _ ← runTrace xs {} false
    let mut sawA := false
    for x in xs do
      if x == faultA then sawA := true
      else if x == faultB && sawA then return true
    return false
  match ← verifyShrinker fails2 trace2 2 with
  | .error msg => throw (IO.userError s!"UUID_SHRINK_PAIR_FAILED: {msg}")
  | .ok shrunk =>
    unless shrunk == #[faultA, faultB] do
      let shown := shrunk.toList.map reprUuidOp
      throw (IO.userError s!"UUID_SHRINK_PAIR_MISMATCH: {shown}")

/-- Differential fuzz suite for `LeanSwe.Uuid` covering real OS UUIDv4 generation, uniqueness, and pure codec equivalence. -/
def suite : FuzzSuite := {
  name := "uuid"
  description := "Real OS getrandom UUIDv4 generation, uniqueness, and RFC 4122 codec differential fuzzing"
  runSmoke := runSmokeImpl
  runFuzz := runFuzzImpl
  selfTestShrink := selfTestShrinkImpl
}

end Fuzz.Uuid
