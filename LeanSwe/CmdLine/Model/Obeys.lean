import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Model
import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Model
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types

namespace LeanSwe.CmdLine.Model

open LeanSwe.CmdLine

/-- Normalize a raw host stdio exception message into a `.ioError` `CmdLineError` with non-empty message. -/
def mkStdioIoError (msg : String) : CmdLineError :=
  { kind := .ioError, message := if msg.isEmpty then "stdio I/O error" else msg }

/-- Pure mapping from a Linux `Errno` returned by `LinuxSyscall.Files` stdio calls to `IO.Error`. -/
def errnoToIoErrorModel (e : LeanSwe.LinuxSyscall.Errno) : IO.Error :=
  match e.toNat with
  | 4 => .interrupted "" 4 "interrupted system call"
  | 5 => .hardwareFault 5 "input/output error"
  | 9 => .invalidArgument none 9 "bad file descriptor"
  | 11 => .resourceExhausted none 11 "resource temporarily unavailable"
  | 21 => .inappropriateType none 21 "is a directory"
  | 24 => .resourceExhausted none 24 "too many open files"
  | 27 => .resourceExhausted none 27 "file too large"
  | 28 => .resourceExhausted none 28 "no space left on device"
  | 32 => .resourceVanished 32 "broken pipe"
  | _ => .otherError e (LeanSwe.LinuxSyscall.Errno.name e)

/-- Pure mapping from `EnvVarsError` to `CmdLineError` (`kind := .ioError`, preserving `message` and `key`). -/
def mapEnvVarsErrorModel (err : LeanSwe.EnvVars.EnvVarsError) : CmdLineError :=
  { kind := .ioError, message := err.message, target := err.key }

/-- Pure `CliOpsM.getEnv` behavior over `EnvVars.Raw.Model.EnvironState`. -/
def lookupHostEnv (s : LeanSwe.EnvVars.Raw.Model.EnvironState) (key : String) :
    Except CmdLineError (Option String) :=
  (LeanSwe.EnvVars.Model.getEnvModel s key).mapError mapEnvVarsErrorModel

/-- Pure capability container bundling `LinuxSyscall.Files` (`RawFd`) and `EnvVars` for `LeanSwe.CmdLine`. -/
structure CmdLineCapsM (m : Type → Type) where
  /-- Unbuffered OS file-descriptor capability (`dupStdio`, `read`, `write`, `close`). -/
  files : LeanSwe.LinuxSyscall.Files.FilesOpsM m LeanSwe.LinuxSyscall.RawFd
  /-- Process environment capability (`getEnv`). -/
  env : LeanSwe.EnvVars.EnvVarsApiM m

/-- Optional fault mode injected on `LinuxSyscall.Files` stdio capability calls. -/
inductive HostStdioFault where
  /-- Normal unbuffered stdio operation with no injected fault. -/
  | none
  /-- `dupStdio` returns `Except.error code`. -/
  | dupErrno (code : LeanSwe.LinuxSyscall.Errno)
  /-- `read` or `write` returns `Except.error code` after `dupStdio` succeeds. -/
  | ioErrno (code : LeanSwe.LinuxSyscall.Errno)
  /-- `read` or `write` throws `IO.userError msg` directly in `m` after `dupStdio` succeeds. -/
  | ioThrow (msg : String)
  deriving Repr, DecidableEq, Inhabited

/-- Combined abstract host state for `LeanSwe.CmdLine` over `LinuxSyscall.Files` and `EnvVars`. -/
structure CmdLineHostState where
  /-- Ambient process environment snapshot (`LeanSwe.EnvVars.Raw.Model.EnvironState`). -/
  env : LeanSwe.EnvVars.Raw.Model.EnvironState := {}
  /-- Unread raw bytes queued on standard input (`fd 0`). -/
  stdinBytes : List UInt8 := []
  /-- Accumulated raw bytes written to standard output (`fd 1`). -/
  stdoutBytes : ByteArray := ByteArray.empty
  /-- Accumulated raw bytes written to standard error (`fd 2`). -/
  stderrBytes : ByteArray := ByteArray.empty
  /-- Stack of currently open duplicated stdio slots (`dupStdio` pushes, `close` pops). -/
  openDups : List LeanSwe.LinuxSyscall.Files.StdioFd := []
  /-- Pending transient `EINTR` count before a normal `read` or `write` succeeds. -/
  eintrCount : Nat := 0
  /-- Active stdio fault injection mode. -/
  fault : HostStdioFault := .none
  deriving Inhabited

/-- Total well-formedness guard on `CmdLineHostState` for `Core.ObeysStepFromExcept`. -/
def hostStepWf (_ : CmdLineHostState) : Bool := true

/-- Single-step lower-layer capability request sum over `CmdLineCapsM`. -/
inductive CmdLineCapsReq where
  /-- Validated `caps.env.getEnv key` lookup. -/
  | envGet (key : String)
  /-- `caps.files.dupStdio slot` duplication. -/
  | dupStdio (slot : LeanSwe.LinuxSyscall.Files.StdioFd)
  /-- `caps.files.read fd maxBytes` unbuffered read. -/
  | read (fd : LeanSwe.LinuxSyscall.RawFd) (maxBytes : UInt32)
  /-- `caps.files.write fd data` unbuffered write. -/
  | write (fd : LeanSwe.LinuxSyscall.RawFd) (data : ByteArray)
  /-- `caps.files.close fd` descriptor close. -/
  | close (fd : LeanSwe.LinuxSyscall.RawFd)

/-- Single-step lower-layer capability output sum over `CmdLineCapsM`. -/
inductive CmdLineCapsOut where
  /-- Outcome of `caps.env.getEnv`. -/
  | envVal (res : Except LeanSwe.EnvVars.EnvVarsError (Option String))
  /-- Outcome of `caps.files.dupStdio`. -/
  | opened (res : Except LeanSwe.LinuxSyscall.Errno LeanSwe.LinuxSyscall.RawFd)
  /-- Outcome of `caps.files.read`. -/
  | bytes (res : Except LeanSwe.LinuxSyscall.Errno ByteArray)
  /-- Outcome of `caps.files.write`. -/
  | written (res : Except LeanSwe.LinuxSyscall.Errno UInt32)
  /-- Outcome of `caps.files.close`. -/
  | closed (res : Except LeanSwe.LinuxSyscall.Errno Unit)

/-- Execute one `CmdLineCapsReq` against an arbitrary `CmdLineCapsM (ExceptT IO.Error (StateM W))`. -/
def execCapsStep {W : Type}
    (caps : CmdLineCapsM (ExceptT IO.Error (StateM W))) :
    CmdLineCapsReq → ExceptT IO.Error (StateM W) CmdLineCapsOut
  | .envGet key => .envVal <$> caps.env.getEnv key
  | .dupStdio slot => .opened <$> caps.files.dupStdio slot
  | .read fd maxBytes => .bytes <$> caps.files.read fd maxBytes
  | .write fd data => .written <$> caps.files.write fd data
  | .close fd => .closed <$> caps.files.close fd

/-- Allowed lower-layer single-step relation over `CmdLineHostState` for `CmdLineCapsM`. -/
def allowedHostCapsStep (s : CmdLineHostState) (req : CmdLineCapsReq)
    (out : Except IO.Error CmdLineCapsOut) (s' : CmdLineHostState) : Prop :=
  match req with
  | .envGet key =>
    out = .ok (.envVal (LeanSwe.EnvVars.Model.getEnvModel s.env key)) ∧ s' = s
  | .dupStdio slot =>
    match s.fault with
    | .dupErrno code => out = .ok (.opened (.error code)) ∧ s' = s
    | .none | .ioErrno _ | .ioThrow _ =>
      ∃ fd : LeanSwe.LinuxSyscall.RawFd,
        out = .ok (.opened (.ok fd)) ∧ s' = { s with openDups := slot :: s.openDups }
  | .read _ maxBytes =>
    match s.openDups with
    | .stdin :: _ =>
      match s.fault with
      | .ioThrow msg => out = .error (IO.userError msg) ∧ s' = s
      | .ioErrno code => out = .ok (.bytes (.error code)) ∧ s' = s
      | .none | .dupErrno _ =>
        if s.eintrCount > 0 then
          out = .ok (.bytes (.error LeanSwe.LinuxSyscall.Errno.EINTR)) ∧
            s' = { s with eintrCount := s.eintrCount - 1 }
        else if maxBytes == 0 then
          out = .ok (.bytes (.ok ByteArray.empty)) ∧ s' = s
        else
          match s.stdinBytes with
          | [] => out = .ok (.bytes (.ok ByteArray.empty)) ∧ s' = s
          | b :: rest =>
            out = .ok (.bytes (.ok (ByteArray.mk #[b]))) ∧ s' = { s with stdinBytes := rest }
    | _ =>
      out = .ok (.bytes (.error LeanSwe.LinuxSyscall.Errno.EBADF)) ∧ s' = s
  | .write _ slice =>
    match s.openDups with
    | .stdout :: _ =>
      match s.fault with
      | .ioThrow msg => out = .error (IO.userError msg) ∧ s' = s
      | .ioErrno code => out = .ok (.written (.error code)) ∧ s' = s
      | .none | .dupErrno _ =>
        if s.eintrCount > 0 then
          out = .ok (.written (.error LeanSwe.LinuxSyscall.Errno.EINTR)) ∧
            s' = { s with eintrCount := s.eintrCount - 1 }
        else
          let k := min slice.size 1048576
          out = .ok (.written (.ok (UInt32.ofNat k))) ∧
            s' = { s with stdoutBytes := s.stdoutBytes ++ slice.extract 0 k }
    | .stderr :: _ =>
      match s.fault with
      | .ioThrow msg => out = .error (IO.userError msg) ∧ s' = s
      | .ioErrno code => out = .ok (.written (.error code)) ∧ s' = s
      | .none | .dupErrno _ =>
        if s.eintrCount > 0 then
          out = .ok (.written (.error LeanSwe.LinuxSyscall.Errno.EINTR)) ∧
            s' = { s with eintrCount := s.eintrCount - 1 }
        else
          let k := min slice.size 1048576
          out = .ok (.written (.ok (UInt32.ofNat k))) ∧
            s' = { s with stderrBytes := s.stderrBytes ++ slice.extract 0 k }
    | _ =>
      out = .ok (.written (.error LeanSwe.LinuxSyscall.Errno.EBADF)) ∧ s' = s
  | .close _ =>
    match s.openDups with
    | _ :: rest => out = .ok (.closed (.ok ())) ∧ s' = { s with openDups := rest }
    | [] => out = .ok (.closed (.error LeanSwe.LinuxSyscall.Errno.EBADF)) ∧ s' = s

/-- Pure byte-by-byte line reader matching `SysBridge.readStdioLineFdLoop` up to `fuel` bytes (`EFBIG` on overflow). -/
def stepHostReadLoop (acc : ByteArray) :
    Nat → List UInt8 → Except LeanSwe.LinuxSyscall.Errno ByteArray × List UInt8
  | 0, rem => (.error LeanSwe.LinuxSyscall.Errno.EFBIG, rem)
  | _ + 1, [] => (.ok acc, [])
  | fuel + 1, b :: rest =>
    let acc' := acc.push b
    if b == (0x0A : UInt8) then
      (.ok acc', rest)
    else
      stepHostReadLoop acc' fuel rest

/-- Pure single-step transition of `defaultOps.readLine` over `CmdLineHostState`. -/
def stepHostReadLine (s : CmdLineHostState) : Except IO.Error (Option String) × CmdLineHostState :=
  match s.fault with
  | .dupErrno code => (.error (errnoToIoErrorModel code), s)
  | .ioThrow msg => (.error (IO.userError msg), s)
  | .ioErrno code => (.error (errnoToIoErrorModel code), s)
  | .none =>
    if s.eintrCount > stdioEintrRetryLimit then
      (.error (errnoToIoErrorModel LeanSwe.LinuxSyscall.Errno.EINTR),
        { s with eintrCount := s.eintrCount - (stdioEintrRetryLimit + 1) })
    else
      let (res, rem) := stepHostReadLoop ByteArray.empty 67108864 s.stdinBytes
      let s' := { s with stdinBytes := rem, eintrCount := 0 }
      match res with
      | .error e => (.error (errnoToIoErrorModel e), s')
      | .ok lineBs =>
        if lineBs.isEmpty then
          (.ok none, s')
        else
          (.ok (some (stripTrailingNewlineModel (decodeUtf8LossyLean lineBs))), s')

/-- Pure single-step transition of `defaultOps.writeOut` (`isStdout = true`) or `writeErr` (`false`) over `CmdLineHostState`. -/
def stepHostWriteSlot (isStdout : Bool) (s : CmdLineHostState) (text : String) :
    Except IO.Error Unit × CmdLineHostState :=
  if text.isEmpty then
    (.ok (), s)
  else
    match s.fault with
    | .dupErrno code => (.error (errnoToIoErrorModel code), s)
    | .ioThrow msg => (.error (IO.userError msg), s)
    | .ioErrno code => (.error (errnoToIoErrorModel code), s)
    | .none =>
      if s.eintrCount > stdioEintrRetryLimit then
        (.error (errnoToIoErrorModel LeanSwe.LinuxSyscall.Errno.EINTR),
          { s with eintrCount := s.eintrCount - (stdioEintrRetryLimit + 1) })
      else
        let bs := text.toUTF8
        let s' :=
          if isStdout then
            { s with stdoutBytes := s.stdoutBytes ++ bs, eintrCount := 0 }
          else
            { s with stderrBytes := s.stderrBytes ++ bs, eintrCount := 0 }
        (.ok (), s')

/-- Pure model of `SysBridge.catchStdioM`, mapping `Except.error err` to `.error (mkStdioIoError err.toString)`. -/
def catchHostStdio {α : Type} (res : Except IO.Error α) : Except CmdLineError α :=
  match res with
  | .ok a => .ok a
  | .error err => .error (mkStdioIoError err.toString)

/-- Pure single-step model of `defaultApi.promptLine` over `CmdLineHostState`. -/
def stepHostPromptLine (s : CmdLineHostState) (prompt : String) (default : Option String) :
    Except CmdLineError String × CmdLineHostState :=
  let (wRes, s1) := stepHostWriteSlot true s prompt
  match catchHostStdio wRes with
  | .error e => (.error e, s1)
  | .ok () =>
    let (rRes, s2) := stepHostReadLine s1
    match catchHostStdio rRes with
    | .error e => (.error e, s2)
    | .ok none => (.error { kind := .eof, message := "unexpected end of input" }, s2)
    | .ok (some line) =>
      let trimmed := trimAscii line
      if trimmed.isEmpty then
        match default with
        | some d => (.ok d, s2)
        | none => (.ok "", s2)
      else
        (.ok trimmed, s2)

/-- Pure single-step model of `defaultApi.confirm` over `CmdLineHostState`. -/
def stepHostConfirm (s : CmdLineHostState) (prompt : String) (default : Option Bool) :
    Nat → Except CmdLineError Bool × CmdLineHostState
  | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, s)
  | n + 1 =>
    let (wRes, s1) := stepHostWriteSlot true s prompt
    match catchHostStdio wRes with
    | .error e => (.error e, s1)
    | .ok () =>
      let (rRes, s2) := stepHostReadLine s1
      match catchHostStdio rRes with
      | .error e => (.error e, s2)
      | .ok none => (.error { kind := .eof, message := "unexpected end of input" }, s2)
      | .ok (some line) =>
        let norm := asciiLower (trimAscii line)
        if norm.isEmpty then
          match default with
          | some b => (.ok b, s2)
          | none =>
            match n with
            | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, s2)
            | _ + 1 =>
              let (eRes, s3) := stepHostWriteSlot false s2 "Please answer yes or no.\n"
              match catchHostStdio eRes with
              | .error e => (.error e, s3)
              | .ok () => stepHostConfirm s3 prompt default n
        else if norm == "y" || norm == "yes" then
          (.ok true, s2)
        else if norm == "n" || norm == "no" then
          (.ok false, s2)
        else
          match n with
          | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, s2)
          | _ + 1 =>
            let (eRes, s3) := stepHostWriteSlot false s2 "Please answer yes or no.\n"
            match catchHostStdio eRes with
            | .error e => (.error e, s3)
            | .ok () => stepHostConfirm s3 prompt default n

/-- Execute one `RawStepReq` against an arbitrary `CliOpsM (ExceptT IO.Error (StateM W))`. -/
def execCliExceptStep {W : Type} (ops : CliOpsM (ExceptT IO.Error (StateM W))) :
    RawStepReq → ExceptT IO.Error (StateM W) RawStepOut
  | .readLine => .line <$> ops.readLine
  | .writeOut text => ops.writeOut text *> pure .unit
  | .writeErr text => ops.writeErr text *> pure .unit
  | .getEnv key => .envVal <$> ops.getEnv key

/-- Allowed single-step relation for `Internal.mkCliOpsFromCapsM` over `CmdLineHostState`. -/
def allowedHostCliStep (s : CmdLineHostState) (req : RawStepReq)
    (out : Except IO.Error RawStepOut) (s' : CmdLineHostState) : Prop :=
  match req with
  | .readLine =>
    (out, s') =
      let (r, st) := stepHostReadLine s
      (r.map RawStepOut.line, st)
  | .writeOut text =>
    (out, s') =
      let (r, st) := stepHostWriteSlot true s text
      (r.map (fun _ => RawStepOut.unit), st)
  | .writeErr text =>
    (out, s') =
      let (r, st) := stepHostWriteSlot false s text
      (r.map (fun _ => RawStepOut.unit), st)
  | .getEnv key =>
    out = .ok (.envVal (lookupHostEnv s.env key)) ∧ s' = s

/-- Execute one `PkgStepReq` against a `CmdLineApiM (ExceptT IO.Error (StateM W))` bundle. -/
def execPkgExceptStep {W : Type} (api : CmdLineApiM (ExceptT IO.Error (StateM W))) :
    PkgStepReq → ExceptT IO.Error (StateM W) PkgStepOut
  | .parseWithEnv spec args validators => .parsed <$> api.parseWithEnv spec args validators
  | .promptLine prompt default => .line <$> api.promptLine prompt default
  | .confirm prompt default maxAttempts => .confirmed <$> api.confirm prompt default maxAttempts
  | .runCli spec args exitCode => .code <$> api.runCli spec args (fun _ => pure exitCode)
  | .runCliWith spec args validators exitCode =>
    .code <$> api.runCliWith spec args validators (fun _ => pure exitCode)

/-- Allowed outcome relation for `runCli` / `runCliWith` over `CmdLineHostState`. -/
def allowedHostRunCliWith (s : CmdLineHostState) (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) (exitCode : UInt32)
    (out : Except IO.Error PkgStepOut) (s' : CmdLineHostState) : Prop :=
  ∃ outcome : Except CmdLineError ParsedCmd,
    AllowedParseOutcome (lookupHostEnv s.env) spec args validators outcome ∧
    match outcome with
    | .ok _ => out = .ok (.code exitCode) ∧ s' = s
    | .error e =>
      match e.kind with
      | .helpRequested | .versionRequested =>
        let (wRes, st) := stepHostWriteSlot true s e.message
        (out, s') = (wRes.map (fun _ => PkgStepOut.code 0), st)
      | _ =>
        let (wRes, st) := stepHostWriteSlot false s (e.message ++ "\n")
        (out, s') = (wRes.map (fun _ => PkgStepOut.code 2), st)

/-- Allowed package-level single-step relation for `Internal.mkApiFromCapsM` over `CmdLineHostState`. -/
def allowedHostPkgStep (s : CmdLineHostState) (req : PkgStepReq)
    (out : Except IO.Error PkgStepOut) (s' : CmdLineHostState) : Prop :=
  match req with
  | .parseWithEnv spec args validators =>
    match out with
    | .ok (.parsed res) =>
      s' = s ∧ AllowedParseOutcome (lookupHostEnv s.env) spec args validators res
    | _ => False
  | .promptLine prompt default =>
    (out, s') =
      let (res, st) := stepHostPromptLine s prompt default
      (.ok (.line res), st)
  | .confirm prompt default maxAttempts =>
    (out, s') =
      let (res, st) := stepHostConfirm s prompt default maxAttempts
      (.ok (.confirmed res), st)
  | .runCli spec args exitCode =>
    allowedHostRunCliWith s spec args [] exitCode out s'
  | .runCliWith spec args validators exitCode =>
    allowedHostRunCliWith s spec args validators exitCode out s'

end LeanSwe.CmdLine.Model
