import LeanSwe.Process.Types
import LeanSweProofs.Process.Model
import LeanSwe.Compress.Types
import LeanSweProofs.Compress.Model

/-!
Pure capability-refinement specification for `LeanSwe.Compress` over `LeanSwe.Process.Model`
(`ProcessModelState`, `PkgStepReq`, `PkgStepOut`, `execPkgStep`, `allowedPkgStep`) and
`LeanSwe.Compress.Model` (`CompressEnv`, `State`, `allowedCompressStep`, `allowedDecompressStep`,
`allowedIsToolAvailable`).
-/

namespace LeanSwe.Compress.Model

open LeanSwe.Process

/-- Single-step request sum covering all 5 operations of `CompressApiM`. -/
inductive PkgStepReq where
  /-- `api.compress codec input`. -/
  | compress (codec : Codec) (input : ByteArray)
  /-- `api.decompress codec input`. -/
  | decompress (codec : Codec) (input : ByteArray)
  /-- `api.compressWith codec opts input`. -/
  | compressWith (codec : Codec) (opts : CompressOptions) (input : ByteArray)
  /-- `api.decompressWith codec opts input`. -/
  | decompressWith (codec : Codec) (opts : DecompressOptions) (input : ByteArray)
  /-- `api.isToolAvailable codec`. -/
  | isToolAvailable (codec : Codec)
  deriving Inhabited

/-- Single-step output sum for `PkgStepReq` transitions in `Core.ObeysStepFrom`. -/
inductive PkgStepOut where
  /-- Byte-stream outcome returned by `compress`, `decompress`, `compressWith`, or `decompressWith`. -/
  | bytes (res : Except CompressError ByteArray)
  /-- Boolean probe result returned by `isToolAvailable`. -/
  | avail (ok : Bool)
  deriving Inhabited

/-- Execute one `PkgStepReq` against an arbitrary `CompressApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : CompressApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .compress codec input => .bytes <$> api.compress codec input
  | .decompress codec input => .bytes <$> api.decompress codec input
  | .compressWith codec opts input => .bytes <$> api.compressWith codec opts input
  | .decompressWith codec opts input => .bytes <$> api.decompressWith codec opts input
  | .isToolAvailable codec => .avail <$> api.isToolAvailable codec

/-- Well-formedness guard on `LeanSwe.Process.Model.ProcessModelState` for `Core.ObeysStepFrom`. -/
def processStepWf (s : LeanSwe.Process.Model.ProcessModelState) : Bool :=
  LeanSwe.Process.Model.processStateWf s

/-- Execute one `LeanSwe.Process.Model.PkgStepReq` against `proc : ProcessApiM (StateM W)`. -/
def execProcessStep {W : Type} (proc : ProcessApiM (StateM W))
    (req : LeanSwe.Process.Model.PkgStepReq) : StateM W LeanSwe.Process.Model.PkgStepOut :=
  LeanSwe.Process.Model.execPkgStep proc req

/-- Direct `ProcessApiM` single-step contract delegated to `LeanSwe.Process.Model.allowedPkgStep`. -/
def allowedProcessStep (s : LeanSwe.Process.Model.ProcessModelState)
    (req : LeanSwe.Process.Model.PkgStepReq) (out : LeanSwe.Process.Model.PkgStepOut)
    (s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  LeanSwe.Process.Model.allowedPkgStep s req out s'

/-- Handle-conserving `ProcessModelState` transition when `Compress` executes a valid `ProcessApiM.run` call. -/
def allowedProcessHandleStep (s s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  LeanSwe.Process.Model.processStateWf s = true ∧
  LeanSwe.Process.Model.processStateWf s' = true ∧
  s'.activeHandles = s.activeHandles ∧
  (s'.nextHandleId = s.nextHandleId ∨ s'.nextHandleId = s.nextHandleId + 1)

/-- Allowed `compressWith` step over `ProcessModelState` derived solely from `LeanSwe.Process.Model.allowedPkgStep`. -/
def allowedCompressProcessStep (s : LeanSwe.Process.Model.ProcessModelState)
    (codec : Codec) (opts : CompressOptions) (input : ByteArray)
    (res : Except CompressError ByteArray)
    (s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  if !isValidCompressInput codec opts input then
    s' = s ∧
    LeanSwe.Process.Model.processStateWf s = true ∧
    match res with
    | .error e => e.kind = .invalidInput ∧ isWellFormedCompressError codec e = true
    | .ok _ => False
  else
    allowedProcessHandleStep s s' ∧
    match res with
    | .ok comp => comp.size ≤ opts.maxOutputBytes
    | .error e => isWellFormedCompressError codec e = true ∧ e.kind ≠ .corruptData

/-- Allowed `decompressWith` step over `ProcessModelState` derived solely from `LeanSwe.Process.Model.allowedPkgStep`. -/
def allowedDecompressProcessStep (s : LeanSwe.Process.Model.ProcessModelState)
    (codec : Codec) (opts : DecompressOptions) (input : ByteArray)
    (res : Except CompressError ByteArray)
    (s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  if !isValidDecompressInput opts input then
    s' = s ∧
    LeanSwe.Process.Model.processStateWf s = true ∧
    match res with
    | .error e => e.kind = .invalidInput ∧ isWellFormedCompressError codec e = true
    | .ok _ => False
  else
    allowedProcessHandleStep s s' ∧
    match res with
    | .ok out => out.size ≤ opts.maxOutputBytes ∧ (codec != .gzip || hasGzipHeader input) = true
    | .error e => isWellFormedCompressError codec e = true

/-- Relational single-step contract for all 5 `CompressApiM` operations over `ProcessModelState`. -/
def allowedPkgProcessStep (s : LeanSwe.Process.Model.ProcessModelState)
    (req : PkgStepReq) (out : PkgStepOut)
    (s' : LeanSwe.Process.Model.ProcessModelState) : Prop :=
  match req, out with
  | .compress codec input, .bytes res =>
    allowedCompressProcessStep s codec {} input res s'
  | .decompress codec input, .bytes res =>
    allowedDecompressProcessStep s codec {} input res s'
  | .compressWith codec opts input, .bytes res =>
    allowedCompressProcessStep s codec opts input res s'
  | .decompressWith codec opts input, .bytes res =>
    allowedDecompressProcessStep s codec opts input res s'
  | .isToolAvailable _, .avail _ =>
    allowedProcessHandleStep s s'
  | _, _ => False

/-- Fixed 20-byte `.gzip` simulation frame prefix (`OS = 0xFE`, `"LSIM"` tag). -/
def simGzipPrefix : ByteArray :=
  ByteArray.mk #[0x1F, 0x8B, 0x08, 0, 0, 0, 0, 0, 0, 0xFE, 0x4C, 0x53, 0x49, 0x4D, 0, 0, 0, 0, 0, 0]

/-- Fixed 9-byte `.zstd` simulation frame prefix (`"LSIM"` tag). -/
def simZstdPrefix : ByteArray :=
  ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD, 0x4C, 0x53, 0x49, 0x4D, 0]

/-- Fixed 30-byte `.xz` simulation frame prefix (`"LSIM"` tag). -/
def simXzPrefix : ByteArray :=
  ByteArray.mk #[
    0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x4C, 0x53, 0x49, 0x4D,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Fixed 2-byte `.xz` stream footer magic (`"YZ"`). -/
def simXzSuffix : ByteArray :=
  ByteArray.mk #[0x59, 0x5A]

/-- Construct a canonical-framing tagged simulation frame for `(codec, input)`. -/
def mkSimFrame (codec : Codec) (input : ByteArray) : ByteArray :=
  match codec with
  | .gzip => simGzipPrefix ++ input
  | .zstd => simZstdPrefix ++ input
  | .xz => simXzPrefix ++ input ++ simXzSuffix

/-- Extract `input` when `bs` carries the `mkSimFrame` tag for `codec`, or `none` for untagged real streams. -/
def decodeSimFrame? (codec : Codec) (bs : ByteArray) : Option ByteArray :=
  match codec with
  | .gzip =>
    if bs.size ≥ 20 && bs.extract 0 20 == simGzipPrefix then some (bs.extract 20 bs.size) else none
  | .zstd =>
    if bs.size ≥ 9 && bs.extract 0 9 == simZstdPrefix then some (bs.extract 9 bs.size) else none
  | .xz =>
    if bs.size ≥ 32 && bs.extract 0 30 == simXzPrefix && bs.extract (bs.size - 2) bs.size == simXzSuffix then
      some (bs.extract 30 (bs.size - 2))
    else
      none

/-- Return `true` iff a recorded `((codec, comp), plain)` entry satisfies `.gzip` header and `mkSimFrame` consistency. -/
def isConsistentKnownEntry (entry : (Codec × ByteArray) × ByteArray) : Bool :=
  (entry.1.1 != .gzip || hasGzipHeader entry.1.2) &&
  match decodeSimFrame? entry.1.1 entry.1.2 with
  | some p => p == entry.2
  | none => true

/-- Composite abstract world pairing `ProcessModelState` with `CompressEnv` and round-trip `State`. -/
structure CompressWorld where
  /-- Active child-process handle state from `LeanSwe.Process.Model`. -/
  proc : LeanSwe.Process.Model.ProcessModelState := {}
  /-- Host `PATH` and transient-fault environment configuration. -/
  env : CompressEnv := {}
  /-- Observed `(codec, compressed) ↦ plaintext` round-trip table. -/
  codecState : State := State.empty
  deriving Inhabited

/-- Well-formedness guard on `CompressWorld` enforcing `processStateWf` and `isConsistentKnownEntry` on recorded streams. -/
def worldStepWf (w : CompressWorld) : Bool :=
  LeanSwe.Process.Model.processStateWf w.proc &&
  w.codecState.known.all isConsistentKnownEntry

/-- Decoded codec CLI invocation kind extracted from an `ExecRequest`. -/
inductive CodecExecKind where
  /-- Compression subprocess invocation (`-c`) with payload cap `maxOut` and `stdin = input`. -/
  | compress (codec : Codec) (maxOut : Nat) (input : ByteArray)
  /-- Decompression subprocess invocation (`-d`) with payload cap `maxOut` and `stdin = input`. -/
  | decompress (codec : Codec) (maxOut : Nat) (input : ByteArray)
  /-- Tool availability `--version` probe for `codec`. -/
  | version (codec : Codec)
  deriving Inhabited

/-- Parse `"zstd"`, `"xz"`, or `"gzip"` into its `Codec`. -/
def parseCodecProgram? (prog : String) : Option Codec :=
  if prog == "zstd" then some .zstd
  else if prog == "xz" then some .xz
  else if prog == "gzip" then some .gzip
  else none

/-- Decode a `Compress`-issued `ExecRequest` into its `CodecExecKind`, if recognized. -/
def classifyCodecExecRequest? (req : ExecRequest) : Option CodecExecKind :=
  match parseCodecProgram? req.program with
  | none => none
  | some codec =>
    if req.args == #["--version"] then
      some (.version codec)
    else
      match req.args[0]?, req.maxOutputBytes with
      | some "-c", some lim =>
        if lim ≥ 4096 then some (.compress codec (lim - 4096) req.stdin) else none
      | some "-d", some lim =>
        if lim ≥ 4096 then some (.decompress codec (lim - 4096) req.stdin) else none
      | _, _ => none

/-- Return `true` iff `code` is an OS resource-exhaustion or `PATH` `ENAMETOOLONG` `errno` mapped to `.ioError`. -/
def isResourceOrPathErrnoModel (code : UInt32) : Bool :=
  code == 7 || code == 11 || code == 12 || code == 23 || code == 24 ||
  code == 28 || code == 31 || code == 36 || code == 37 || code == 63 ||
  code == 90 || code == 105

/-- Return `true` iff a `.invalidInput` `ProcessError` carries an OS resource/path `errno`. -/
def isResourceProcessErrorModel (pe : ProcessError) : Bool :=
  pe.kind == .invalidInput &&
  match pe.errnoCode with
  | some code => isResourceOrPathErrnoModel code
  | none => false

/-- Codec CLI outcome conformance predicate for a compression `Process.run` call. -/
def rawCompressOutcomeConforms (env : CompressEnv) (st₀ : State) (codec : Codec)
    (maxOut : Nat) (input : ByteArray) (outcome : Except ProcessError ExecResult) : Bool :=
  match outcome with
  | .error pe =>
    !pe.message.isEmpty &&
    match pe.kind with
    | .notFound | .permissionDenied => env.toolStatus codec == .missingOrNonExec
    | .invalidInput =>
      if isResourceProcessErrorModel pe then
        env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
      else
        env.toolStatus codec == .pathSymlinkLoop
    | .ioError => env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
    | .timedOut => env.toolStatus codec == .available && env.allowTimeout
    | .terminatedBySignal => env.toolStatus codec == .available && env.allowExternalSignal
    | .nonZeroExit => false
    | .outputLimitExceeded =>
      env.toolStatus codec == .available && maxOut < maxCompressedBound codec input.size
  | .ok res =>
    if res.exitCode != 0 then
      env.toolStatus codec == .available && env.allowExternalSignal
    else if res.stdout.size > maxOut then
      env.toolStatus codec == .available && maxOut < maxCompressedBound codec input.size
    else
      env.toolStatus codec == .available &&
      hasCanonicalCompressedFraming codec res.stdout &&
      match st₀.lookup codec res.stdout with
      | some prev => prev == input
      | none => true

/-- Codec CLI outcome conformance predicate for a decompression `Process.run` call. -/
def rawDecompressOutcomeConforms (env : CompressEnv) (st₀ : State) (codec : Codec)
    (maxOut : Nat) (input : ByteArray) (outcome : Except ProcessError ExecResult) : Bool :=
  match outcome with
  | .error pe =>
    !pe.message.isEmpty &&
    match pe.kind with
    | .notFound | .permissionDenied => env.toolStatus codec == .missingOrNonExec
    | .invalidInput =>
      if isResourceProcessErrorModel pe then
        env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
      else
        env.toolStatus codec == .pathSymlinkLoop
    | .ioError => env.toolStatus codec == .pathOrPipeIoError || env.allowResourceIoError
    | .timedOut =>
      env.toolStatus codec == .available && env.allowTimeout &&
      match st₀.lookup codec input with
      | some _ => codec != .gzip || hasGzipHeader input
      | none => true
    | .terminatedBySignal => env.toolStatus codec == .available && env.allowExternalSignal
    | .nonZeroExit => false
    | .outputLimitExceeded =>
      env.toolStatus codec == .available &&
      match st₀.lookup codec input with
      | some expected =>
        expected.size > maxOut && (codec != .gzip || hasGzipHeader input)
      | none => true
  | .ok res =>
    env.toolStatus codec == .available &&
    match st₀.lookup codec input with
    | some expected =>
      if res.exitCode != 0 then false
      else if res.stdout.size > maxOut then
        expected.size > maxOut && (codec != .gzip || hasGzipHeader input)
      else
        expected.size ≤ maxOut &&
        res.stdout == expected &&
        (codec != .gzip || hasGzipHeader input)
    | none => true

/-- Codec CLI outcome conformance predicate for a `--version` probe `Process.run` call. -/
def rawVersionOutcomeConforms (env : CompressEnv) (codec : Codec)
    (outcome : Except ProcessError ExecResult) : Bool :=
  match outcome with
  | .error _ =>
    match env.toolStatus codec with
    | .available => env.allowTimeout || env.allowResourceIoError || env.allowExternalSignal
    | _ => true
  | .ok res =>
    match env.toolStatus codec with
    | .available =>
      if res.exitCode == 0 then true
      else env.allowTimeout || env.allowResourceIoError || env.allowExternalSignal
    | _ => res.exitCode != 0

/-- Composite `ProcessApiM` single-step contract over `CompressWorld` combining `Process.Model.allowedPkgStep` with codec CLI conformance. -/
def allowedWorldProcessStep (w : CompressWorld)
    (req : LeanSwe.Process.Model.PkgStepReq) (out : LeanSwe.Process.Model.PkgStepOut)
    (w' : CompressWorld) : Prop :=
  worldStepWf w = true ∧
  worldStepWf w' = true ∧
  LeanSwe.Process.Model.allowedPkgStep w.proc req out w'.proc ∧
  w'.env = w.env ∧
  match req, out with
  | .run execReq, .execRes rawRes =>
    match LeanSwe.Process.Model.validateRequestModel execReq with
    | .error _ => w'.codecState = w.codecState
    | .ok _ =>
      match classifyCodecExecRequest? execReq with
      | none => w'.codecState = w.codecState
      | some (.compress codec maxOut input) =>
        rawCompressOutcomeConforms w.env w.codecState codec maxOut input rawRes = true ∧
        w'.codecState =
          match rawRes with
          | .ok res =>
            if res.exitCode == 0 && res.stdout.size ≤ maxOut then
              w.codecState.record codec res.stdout input
            else
              w.codecState
          | .error _ => w.codecState
      | some (.decompress codec maxOut input) =>
        rawDecompressOutcomeConforms w.env w.codecState codec maxOut input rawRes = true ∧
        w'.codecState =
          match rawRes with
          | .ok res =>
            if res.exitCode == 0 && res.stdout.size ≤ maxOut && (codec != .gzip || hasGzipHeader input) then
              w.codecState.record codec input res.stdout
            else
              w.codecState
          | .error _ => w.codecState
      | some (.version codec) =>
        rawVersionOutcomeConforms w.env codec rawRes = true ∧
        w'.codecState = w.codecState
  | _, _ => w'.codecState = w.codecState

/-- Relational single-step contract for all 5 `CompressApiM` operations over `CompressWorld`. -/
def allowedPkgWorldStep (w : CompressWorld) (req : PkgStepReq) (out : PkgStepOut)
    (w' : CompressWorld) : Prop :=
  worldStepWf w = true ∧
  worldStepWf w' = true ∧
  w'.env = w.env ∧
  match req, out with
  | .compress codec input, .bytes res =>
    allowedCompressProcessStep w.proc codec {} input res w'.proc ∧
    allowedCompressStep w.env w.codecState codec {} input res w'.codecState = true
  | .decompress codec input, .bytes res =>
    allowedDecompressProcessStep w.proc codec {} input res w'.proc ∧
    allowedDecompressStep w.env w.codecState codec {} input res w'.codecState = true
  | .compressWith codec opts input, .bytes res =>
    allowedCompressProcessStep w.proc codec opts input res w'.proc ∧
    allowedCompressStep w.env w.codecState codec opts input res w'.codecState = true
  | .decompressWith codec opts input, .bytes res =>
    allowedDecompressProcessStep w.proc codec opts input res w'.proc ∧
    allowedDecompressStep w.env w.codecState codec opts input res w'.codecState = true
  | .isToolAvailable codec, .avail ok =>
    allowedProcessHandleStep w.proc w'.proc ∧
    w'.codecState = w.codecState ∧
    allowedIsToolAvailable w.env codec ok = true
  | _, _ => False

end LeanSwe.Compress.Model
