import LeanSwe.Process.Types
import LeanSwe.Compress.Types

namespace LeanSwe.Compress.Internal

open LeanSwe.Process
  (ProcessError ExecRequest ExecResult ProcessApiM)

/-- Return the CLI executable name for `codec`. -/
def codecProgram : Codec → String
  | .zstd => "zstd"
  | .xz => "xz"
  | .gzip => "gzip"

/-- Explicit environment removals clearing inherited codec configuration variables and pinning `LC_ALL=C` while keeping `PATH`. -/
def codecSanitizedEnv : Array (String × Option String) :=
  #[("XZ_OPT", none),
    ("XZ_DEFAULTS", none),
    ("ZSTD_CLEVEL", none),
    ("ZSTD_NBTHREADS", none),
    ("GZIP", none),
    ("LC_ALL", some "C")]

/-- Pipe buffer slack beyond `maxOutputBytes` passed to `LeanSwe.Process`. -/
def stderrPipeSlack : Nat := 4096

/-- Return `true` iff `code` is a POSIX `errno` that `LeanSwe.Process.Raw` surfaces as `.invalidInput`
    for OS resource exhaustion (`IO.Error.resourceExhausted`) or `PATH` `ENAMETOOLONG` (`36`). -/
def isResourceOrPathIoErrno (code : UInt32) : Bool :=
  code == 7 || code == 11 || code == 12 || code == 23 || code == 24 ||
  code == 28 || code == 31 || code == 36 || code == 37 || code == 63 ||
  code == 90 || code == 105

/-- O(1) RFC 1952 `.gzip` header check (`1f 8b 08` and at least 20 bytes) so GNU `gzip -d` rejects legacy `.Z`/pack/lzh/PKZIP containers at byte 0. -/
def hasGzipHeader (input : ByteArray) : Bool :=
  input.size ≥ 20 && input.get! 0 == 0x1F && input.get! 1 == 0x8B && input.get! 2 == 0x08

/-- Decode raw stderr bytes as `none` when empty or invalid UTF-8, and `some s` otherwise. -/
def decodeStderr (bs : ByteArray) : Option String :=
  if bs.isEmpty then none else String.fromUTF8? bs

/-- Return a non-empty error message, using `fallback` when `msg` is empty. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Validate compression `opts` and `input` size purely before spawning a subprocess. -/
def validateCompressOptions (codec : Codec) (opts : CompressOptions) (input : ByteArray) :
    Except CompressError Unit :=
  if opts.timeoutMs == 0 then
    .error { kind := .invalidInput, codec := some codec, message := "timeoutMs must be greater than zero" }
  else if opts.maxOutputBytes == 0 then
    .error { kind := .invalidInput, codec := some codec, message := "maxOutputBytes must be greater than zero" }
  else
    let inputOk :=
      match opts.maxInputBytes with
      | none => true
      | some lim => input.size ≤ lim
    if !inputOk then
      .error { kind := .invalidInput, codec := some codec, message := "input size exceeds maxInputBytes" }
    else
      let levelOk :=
        match opts.level with
        | none => true
        | some lvl =>
          match codec with
          | .zstd => 1 ≤ lvl && lvl ≤ 19
          | .xz => lvl ≤ 9
          | .gzip => 1 ≤ lvl && lvl ≤ 9
      if !levelOk then
        .error { kind := .invalidInput, codec := some codec, message := "compression level out of range for codec" }
      else
        let threadsOk :=
          match opts.threads with
          | none => true
          | some t =>
            match codec with
            | .zstd => t ≤ 4294967295
            | .xz => t ≤ 16384
            | .gzip => false
        if !threadsOk then
          .error { kind := .invalidInput, codec := some codec, message := "threads option invalid for codec" }
        else
          .ok ()

/-- Validate decompression `opts` and `input` size purely before spawning a subprocess. -/
def validateDecompressOptions (codec : Codec) (opts : DecompressOptions) (input : ByteArray) :
    Except CompressError Unit :=
  if opts.timeoutMs == 0 then
    .error { kind := .invalidInput, codec := some codec, message := "timeoutMs must be greater than zero" }
  else if opts.maxOutputBytes == 0 then
    .error { kind := .invalidInput, codec := some codec, message := "maxOutputBytes must be greater than zero" }
  else
    let inputOk :=
      match opts.maxInputBytes with
      | none => true
      | some lim => input.size ≤ lim
    if !inputOk then
      .error { kind := .invalidInput, codec := some codec, message := "input size exceeds maxInputBytes" }
    else
      .ok ()

/-- Build the direct `execvp` argument array for compression. -/
def mkCompressArgs (codec : Codec) (opts : CompressOptions) : Array String :=
  let levelArgs : Array String :=
    match opts.level with
    | none => #[]
    | some lvl => #[s!"-{lvl}"]
  let threadArgs : Array String :=
    match opts.threads with
    | none => #[]
    | some t => #[s!"-T{t}"]
  match codec with
  | .zstd => #["-c", "-q", "--no-progress"] ++ levelArgs ++ threadArgs
  | .xz => #["-c", "-q"] ++ levelArgs ++ threadArgs
  | .gzip => #["-c", "-n"] ++ levelArgs

/-- Build the direct `execvp` argument array for decompression. -/
def mkDecompressArgs : Codec → Array String
  | .zstd => #["-d", "-c", "-q", "--no-progress", "--format=zstd"]
  | .xz => #["-d", "-c", "-q", "-T1", "--format=xz"]
  | .gzip => #["-d", "-c", "-n"]

/-- Build the `ExecRequest` for `compressWith`. -/
def mkCompressRequest (codec : Codec) (opts : CompressOptions) (input : ByteArray) : ExecRequest :=
  { program := codecProgram codec
    args := mkCompressArgs codec opts
    cwd := none
    env := codecSanitizedEnv
    inheritEnv := true
    stdin := input
    timeoutMs := some opts.timeoutMs
    maxOutputBytes := some (opts.maxOutputBytes + stderrPipeSlack) }

/-- Build the `ExecRequest` for `decompressWith`. -/
def mkDecompressRequest (codec : Codec) (opts : DecompressOptions) (input : ByteArray) : ExecRequest :=
  { program := codecProgram codec
    args := mkDecompressArgs codec
    cwd := none
    env := codecSanitizedEnv
    inheritEnv := true
    stdin := input
    timeoutMs := some opts.timeoutMs
    maxOutputBytes := some (opts.maxOutputBytes + stderrPipeSlack) }

/-- Build the `ExecRequest` for `isToolAvailable`. -/
def mkToolVersionRequest (codec : Codec) : ExecRequest :=
  { program := codecProgram codec
    args := #["--version"]
    cwd := none
    env := codecSanitizedEnv
    inheritEnv := true
    stdin := ByteArray.empty
    timeoutMs := some 5000
    maxOutputBytes := some 65536 }

/-- Return `true` iff a `.invalidInput` `ProcessError` originated from an OS resource or `PATH` `Errno`. -/
def isResourceExhaustedProcessError (pe : ProcessError) : Bool :=
  pe.kind == .invalidInput &&
  match pe.errnoCode with
  | some code => isResourceOrPathIoErrno code
  | none => false

/-- Map a `ProcessError` from `LeanSwe.Process` into a normalized `CompressError`. -/
def classifyProcessError (codec : Codec) (pe : ProcessError) : CompressError :=
  let kind : CompressErrorKind :=
    match pe.kind with
    | .notFound => .toolNotFound
    | .permissionDenied => .toolNotFound
    | .invalidInput => if isResourceExhaustedProcessError pe then .ioError else .invalidInput
    | .timedOut => .timedOut
    | .outputLimitExceeded => .outputLimitExceeded
    | .terminatedBySignal => .commandFailed
    | .nonZeroExit => .commandFailed
    | .ioError => .ioError
  let exitCode? : Option Int :=
    match kind with
    | .commandFailed =>
      match pe.exitCode with
      | some c => if c != 0 then some c else none
      | none => none
    | _ => none
  let fallback := codecProgram codec ++ " process invocation failed"
  { kind := kind
    codec := some codec
    exitCode := exitCode?
    stderr :=
      match kind with
      | .toolNotFound | .invalidInput => none
      | _ => pe.stderr.bind decodeStderr
    message := nonEmptyMsg fallback pe.message }

/-- Classify a completed `ExecResult` for compression (`isDecompress = false`) or decompression (`isDecompress = true`). -/
def classifyExitResult (codec : Codec) (isDecompress : Bool) (maxOut : Nat) (input : ByteArray)
    (res : ExecResult) : Except CompressError ByteArray :=
  if res.exitCode != 0 then
    let errStr? := decodeStderr res.stderr
    let kind : CompressErrorKind := if isDecompress then .corruptData else .commandFailed
    let fallback :=
      if isDecompress then
        codecProgram codec ++ " decompression failed with exit code " ++ toString res.exitCode
      else
        codecProgram codec ++ " compression failed with exit code " ++ toString res.exitCode
    let msg :=
      match errStr? with
      | some s => nonEmptyMsg fallback s
      | none => fallback
    .error
      { kind := kind
        codec := some codec
        exitCode := some res.exitCode
        stderr := errStr?
        message := msg }
  else if res.stdout.size > maxOut then
    if isDecompress && codec == .gzip && !hasGzipHeader input then
      .error
        { kind := .corruptData
          codec := some codec
          exitCode := none
          stderr := none
          message := codecProgram codec ++ " compressed stream failed gzip header check" }
    else
      .error
        { kind := .outputLimitExceeded
          codec := some codec
          exitCode := none
          stderr := decodeStderr res.stderr
          message := codecProgram codec ++ " output exceeded maxOutputBytes" }
  else if isDecompress && codec == .gzip && !hasGzipHeader input then
    .error
      { kind := .corruptData
        codec := some codec
        exitCode := none
        stderr := none
        message := codecProgram codec ++ " compressed stream failed gzip header check" }
  else
    .ok res.stdout

/-- Compress `input` with `codec` and `opts` via `proc`. -/
def compressWith {m : Type → Type} [Monad m] (proc : ProcessApiM m)
    (codec : Codec) (opts : CompressOptions) (input : ByteArray) :
    m (Except CompressError ByteArray) := do
  match validateCompressOptions codec opts input with
  | .error err => return .error err
  | .ok () =>
    let req := mkCompressRequest codec opts input
    match ← proc.run req with
    | .error pe => return .error (classifyProcessError codec pe)
    | .ok res => return classifyExitResult codec false opts.maxOutputBytes input res

/-- Decompress `input` with `codec` and `opts` via `proc`. -/
def decompressWith {m : Type → Type} [Monad m] (proc : ProcessApiM m)
    (codec : Codec) (opts : DecompressOptions) (input : ByteArray) :
    m (Except CompressError ByteArray) := do
  match validateDecompressOptions codec opts input with
  | .error err => return .error err
  | .ok () =>
    let req := mkDecompressRequest codec opts input
    match ← proc.run req with
    | .error pe =>
      if (pe.kind == .outputLimitExceeded || pe.kind == .timedOut) && codec == .gzip && !hasGzipHeader input then
        return .error
          { kind := .corruptData
            codec := some codec
            exitCode := none
            stderr := pe.stderr.bind decodeStderr
            message := codecProgram codec ++ " compressed stream failed gzip header check" }
      else
        return .error (classifyProcessError codec pe)
    | .ok res => return classifyExitResult codec true opts.maxOutputBytes input res

/-- Return `true` iff the binary for `codec` succeeds on `--version` via `proc`. -/
def isToolAvailable {m : Type → Type} [Monad m] (proc : ProcessApiM m)
    (codec : Codec) : m Bool := do
  match ← proc.run (mkToolVersionRequest codec) with
  | .ok res => return res.exitCode == 0
  | .error _ => return false

/-- Build a generic `CompressApiM m` backed by `proc : ProcessApiM m`. -/
def mkApiM {m : Type → Type} [Monad m] (proc : ProcessApiM m) : CompressApiM m :=
  { compress := fun codec input => compressWith proc codec {} input
    decompress := fun codec input => decompressWith proc codec {} input
    compressWith := compressWith proc
    decompressWith := decompressWith proc
    isToolAvailable := isToolAvailable proc }

end LeanSwe.Compress.Internal
