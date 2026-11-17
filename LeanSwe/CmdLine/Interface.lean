import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Model
import LeanSwe.CmdLine.Impl
import LeanSwe.EnvVars.Interface

namespace LeanSwe.CmdLine

/-- Default `CliOps` wired to `IO.getStdin`/`IO.getStdout`/`IO.getStderr` and `LeanSwe.EnvVars.getEnv`. -/
def defaultOps : CliOps :=
  { readLine := do
      let stdin ← IO.getStdin
      let line ← stdin.getLine
      if line.isEmpty then
        return none
      else
        return some (Internal.stripTrailingNewline line)
    writeOut := fun text => do
      let out ← IO.getStdout
      out.putStr text
      out.flush
    writeErr := fun text => do
      let err ← IO.getStderr
      err.putStr text
      err.flush
    getEnv := fun key => do
      match ← LeanSwe.EnvVars.getEnv key with
      | .ok v => return .ok v
      | .error err =>
        return .error
          { kind := .ioError
            message := err.message
            target := err.key } }

private def catchIoAsCmdLineError {α : Type} (act : IO (Except CmdLineError α)) :
    IO (Except CmdLineError α) :=
  BaseIO.toEIO (EIO.catchExceptions act fun err =>
    let msg := err.toString
    pure (.error { kind := .ioError, message := if msg.isEmpty then "stdio I/O error" else msg }))

/-- Default `CmdLineApi` backed by `defaultOps`, catching OS stdio exceptions into `.ioError`. -/
def defaultApi : CmdLineApi :=
  { Internal.mkApiM defaultOps with
    promptLine := fun prompt default =>
      catchIoAsCmdLineError (Internal.promptLine defaultOps prompt default)
    confirm := fun prompt default maxAttempts =>
      catchIoAsCmdLineError (Internal.confirm defaultOps prompt default maxAttempts) }

/-- Return `true` iff `spec` satisfies `ValidSpec`. -/
@[inline] def isValidSpec (spec : CommandSpec) : Bool :=
  defaultApi.isValidSpec spec

/-- Purely parse `args` against `spec` with no environment fallback. -/
@[inline] def parse (spec : CommandSpec) (args : List String) : Except CmdLineError ParsedCmd :=
  defaultApi.parse spec args

/-- Purely parse `args` against `spec` using custom validators and no environment fallback. -/
@[inline] def parseWith (spec : CommandSpec) (args : List String)
    (validators : CustomValidators := []) : Except CmdLineError ParsedCmd :=
  defaultApi.parseWith spec args validators

/-- Parse `args` against `spec` using `defaultOps.getEnv` fallback and optional custom validators. -/
@[inline] def parseWithEnv (spec : CommandSpec) (args : List String)
    (validators : CustomValidators := []) : IO (Except CmdLineError ParsedCmd) :=
  defaultApi.parseWithEnv spec args validators

/-- Render help text for `rootSpec` at `subcommandPath`. -/
@[inline] def renderHelp (rootSpec : CommandSpec) (subcommandPath : List String := []) :
    Except CmdLineError String :=
  defaultApi.renderHelp rootSpec subcommandPath

/-- Render `<name> <version>\n`. -/
@[inline] def renderVersion (name version : String) : String :=
  defaultApi.renderVersion name version

/-- Render a `ParsedCmd` back into canonical CLI argument tokens. -/
@[inline] def renderArgs (spec : CommandSpec) (parsed : ParsedCmd) :
    Except CmdLineError (List String) :=
  defaultApi.renderArgs spec parsed

/-- Prompt for a line of input on `IO` stdio, trimming ASCII whitespace and applying `default`. -/
@[inline] def promptLine (prompt : String) (default : Option String := none) :
    IO (Except CmdLineError String) :=
  defaultApi.promptLine prompt default

/-- Prompt up to `maxAttempts` times on `IO` stdio for `y`/`yes`/`n`/`no` confirmation. -/
@[inline] def confirm (prompt : String) (default : Option Bool := none)
    (maxAttempts : Nat := 100) : IO (Except CmdLineError Bool) :=
  defaultApi.confirm prompt default maxAttempts

/-- Execute a full CLI flow on `IO` stdio and `LeanSwe.EnvVars`. -/
@[inline] def runCli (spec : CommandSpec) (args : List String)
    (handler : ParsedCmd → IO UInt32) : IO UInt32 :=
  defaultApi.runCli spec args handler

/-- Execute a full CLI flow with custom validators on `IO` stdio and `LeanSwe.EnvVars`. -/
@[inline] def runCliWith (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) (handler : ParsedCmd → IO UInt32) : IO UInt32 :=
  defaultApi.runCliWith spec args validators handler

/-- Execute a full CLI flow over a custom `CliOpsM m` backend. -/
@[inline] def runCliM {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec)
    (args : List String) (handler : ParsedCmd → m UInt32) : m UInt32 :=
  Internal.runCli ops spec args handler

/-- Execute a full CLI flow with custom validators over a custom `CliOpsM m` backend. -/
@[inline] def runCliWithM {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec)
    (args : List String) (validators : CustomValidators) (handler : ParsedCmd → m UInt32) : m UInt32 :=
  Internal.runCliWith ops spec args validators handler

/-- Prompt for a line of input over a custom `CliOpsM m` backend. -/
@[inline] def promptLineM {m : Type → Type} [Monad m] (ops : CliOpsM m) (prompt : String)
    (default : Option String := none) : m (Except CmdLineError String) :=
  Internal.promptLine ops prompt default

/-- Prompt for `y`/`yes`/`n`/`no` confirmation over a custom `CliOpsM m` backend. -/
@[inline] def confirmM {m : Type → Type} [Monad m] (ops : CliOpsM m) (prompt : String)
    (default : Option Bool := none) (maxAttempts : Nat := 100) : m (Except CmdLineError Bool) :=
  Internal.confirm ops prompt default maxAttempts

end LeanSwe.CmdLine
