import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Model

namespace LeanSwe.CmdLine.Model

open LeanSwe.CmdLine

/-- Normalize a raw host stdio exception message into a `.ioError` `CmdLineError` with non-empty message. -/
def mkStdioIoError (msg : String) : CmdLineError :=
  { kind := .ioError, message := if msg.isEmpty then "stdio I/O error" else msg }

/-- Checked stdio and environment capability bundle for `CmdLine.defaultApi`,
    surfacing interactive stdio read/write errors explicitly as `Except CmdLineError`
    while delegating non-prompt operations to `cliOps`. -/
structure CheckedCliOpsM (m : Type → Type) where
  /-- Read one line from interactive input, returning `.ok none` on EOF or `.error` on I/O failure. -/
  readLineChecked : m (Except CmdLineError (Option String))
  /-- Write text to standard output, returning `.error` on I/O failure. -/
  writeOutChecked : String → m (Except CmdLineError Unit)
  /-- Write text to standard error, returning `.error` on I/O failure. -/
  writeErrChecked : String → m (Except CmdLineError Unit)
  /-- Underlying `CliOpsM m` capability bundle for `parseWithEnv`, `runCli`, and `runCliWith`. -/
  cliOps : CliOpsM m

/-- Abstract state for `CheckedCliOpsM` single-step obedience, extending `CliStepState`
    with an optional fault-injected stdio `.ioError` diagnostic. -/
structure CheckedCliStepState where
  /-- Underlying queued stdin, accumulated stdout/stderr, and environment table. -/
  cli : CliStepState := {}
  /-- Optional raw diagnostic triggering `.ioError` on checked interactive stdio steps. -/
  stdioErr? : Option String := none
  deriving Inhabited

/-- Request sum for `CheckedCliOpsM` primitives in `Core.ObeysStepFrom`. -/
inductive CheckedRawStepReq where
  /-- Checked interactive `stdin` line read. -/
  | readLineChecked
  /-- Checked interactive `stdout` write. -/
  | writeOutChecked (text : String)
  /-- Checked interactive `stderr` write. -/
  | writeErrChecked (text : String)
  /-- Underlying `CliOpsM` primitive step. -/
  | raw (req : RawStepReq)
  deriving Inhabited

/-- Output sum for `CheckedCliOpsM` primitives in `Core.ObeysStepFrom`. -/
inductive CheckedRawStepOut where
  /-- Result of `readLineChecked`. -/
  | checkedLine (res : Except CmdLineError (Option String))
  /-- Result of `writeOutChecked` or `writeErrChecked`. -/
  | checkedUnit (res : Except CmdLineError Unit)
  /-- Result of an underlying `CliOpsM` primitive step. -/
  | raw (out : RawStepOut)

/-- Total well-formedness guard on `CheckedCliStepState` for `Core.ObeysStepFrom`. -/
def checkedStepWf (_ : CheckedCliStepState) : Bool := true

/-- Execute one `CheckedRawStepReq` against an arbitrary `CheckedCliOpsM (StateM W)`. -/
def execCheckedRawStep {W : Type} (ops : CheckedCliOpsM (StateM W)) :
    CheckedRawStepReq → StateM W CheckedRawStepOut
  | .readLineChecked => .checkedLine <$> ops.readLineChecked
  | .writeOutChecked text => .checkedUnit <$> ops.writeOutChecked text
  | .writeErrChecked text => .checkedUnit <$> ops.writeErrChecked text
  | .raw req => .raw <$> execRawStep ops.cliOps req

/-- Allowed raw single-step relation over `CheckedCliStepState`. -/
def allowedCheckedRawStep (s : CheckedCliStepState) (req : CheckedRawStepReq)
    (out : CheckedRawStepOut) (s' : CheckedCliStepState) : Prop :=
  match req, out with
  | .readLineChecked, .checkedLine res =>
    match s.stdioErr? with
    | some msg => res = .error (mkStdioIoError msg) ∧ s' = s
    | none =>
      match s.cli.stdinLines with
      | [] => res = .ok none ∧ s' = s
      | hd :: tl => res = .ok (some hd) ∧ s' = { s with cli := { s.cli with stdinLines := tl } }
  | .writeOutChecked text, .checkedUnit res =>
    match s.stdioErr? with
    | some msg => res = .error (mkStdioIoError msg) ∧ s' = s
    | none => res = .ok () ∧ s' = { s with cli := { s.cli with stdout := s.cli.stdout ++ text } }
  | .writeErrChecked text, .checkedUnit res =>
    match s.stdioErr? with
    | some msg => res = .error (mkStdioIoError msg) ∧ s' = s
    | none => res = .ok () ∧ s' = { s with cli := { s.cli with stderr := s.cli.stderr ++ text } }
  | .raw r, .raw o =>
    allowedRawStep s.cli r o s'.cli ∧ s'.stdioErr? = s.stdioErr?
  | _, _ => False

/-- Pure single-step model of checked `promptLine` over `CheckedCliStepState`. -/
def stepCheckedPromptLine (s : CheckedCliStepState) (prompt : String) (default : Option String) :
    Except CmdLineError String × CheckedCliStepState :=
  match s.stdioErr? with
  | some msg => (.error (mkStdioIoError msg), s)
  | none =>
    let (res, c') := stepCliPromptLine s.cli prompt default
    (res, { s with cli := c' })

/-- Pure single-step model of checked `confirm` over `CheckedCliStepState`. -/
def stepCheckedConfirm (s : CheckedCliStepState) (prompt : String) (default : Option Bool) :
    Nat → Except CmdLineError Bool × CheckedCliStepState
  | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, s)
  | n + 1 =>
    match s.stdioErr? with
    | some msg => (.error (mkStdioIoError msg), s)
    | none =>
      let (res, c') := stepCliConfirm s.cli prompt default (n + 1)
      (res, { s with cli := c' })

/-- Allowed package-level single-step relation for `Internal.mkCheckedApiM` over `CheckedCliStepState`. -/
def allowedCheckedPkgStep (s : CheckedCliStepState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : CheckedCliStepState) : Prop :=
  match req, out with
  | .parseWithEnv spec args validators, .parsed res =>
    allowedParseWithEnvStep s.cli spec args validators res s'.cli ∧ s'.stdioErr? = s.stdioErr?
  | .promptLine prompt default, .line res =>
    (res, s') = stepCheckedPromptLine s prompt default
  | .confirm prompt default maxAttempts, .confirmed res =>
    (res, s') = stepCheckedConfirm s prompt default maxAttempts
  | .runCli spec args exitCode, .code code =>
    allowedRunCliWithStep s.cli spec args [] exitCode code s'.cli ∧ s'.stdioErr? = s.stdioErr?
  | .runCliWith spec args validators exitCode, .code code =>
    allowedRunCliWithStep s.cli spec args validators exitCode code s'.cli ∧ s'.stdioErr? = s.stdioErr?
  | _, _ => False

end LeanSwe.CmdLine.Model
