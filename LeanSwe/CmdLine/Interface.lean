import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Impl
import LeanSwe.CmdLine.SysBridge
import LeanSwe.EnvVars.Interface
import LeanSwe.LinuxSyscall.Files.Interface

namespace LeanSwe.CmdLine

namespace Internal

/-- Build `CliOpsM m` directly over a `CmdLineCapsM m` capability bundle (`LinuxSyscall.Files` + `EnvVars`). -/
def mkCliOpsFromCapsM {m : Type → Type} [Monad m] [MonadFinally m] [MonadExceptOf IO.Error m]
    (caps : CmdLineCapsM m) : CliOpsM m :=
  SysBridge.mkFilesCliOpsM caps.files (SysBridge.mapEnvVarsGet caps.env)

/-- Build `CmdLineApiM m` directly over a `CmdLineCapsM m` capability bundle (`LinuxSyscall.Files` + `EnvVars`),
    catching interactive `IO.Error` throws from `promptLine`/`confirm` into `.ioError`. -/
def mkApiFromCapsM {m : Type → Type} [Monad m] [MonadFinally m] [MonadExceptOf IO.Error m]
    (caps : CmdLineCapsM m) : CmdLineApiM m :=
  let ops := mkCliOpsFromCapsM caps
  { Internal.mkApiM ops with
    promptLine := fun prompt default => SysBridge.promptLineCheckedM ops prompt default
    confirm := fun prompt default maxAttempts => SysBridge.confirmCheckedM ops prompt default maxAttempts }

end Internal

/-- Default `CliOps` wired directly to unbuffered OS stdio descriptors `0`/`1`/`2` via
    `LeanSwe.LinuxSyscall.Files.defaultOps` (`dupStdio`/`read`/`write`/`close`) and `LeanSwe.EnvVars.defaultApi`.

    Live I/O intentionally bypasses Lean's host-IO stream handles (`IO.getStdin`/`IO.getStdout`/`IO.getStderr`):
    it does **not** flush C/Lean `IO.FS.Stream` buffers and does **not** honor `IO.withStdin`/`IO.withStdout`/
    `IO.withStderr` redirections. Callers mixing buffered `IO.print`/`IO.println` with `CmdLine` on pipes or
    non-TTYs must flush Lean stdio beforehand; do **not** mix buffered `IO.getStdin` reads with `CmdLine` `stdin`
    reads, because bytes already read ahead into Lean's `stdin` buffer are invisible to descriptor `0` and cannot
    be recovered by flushing. Callers needing redirected or in-memory streams should pass an explicit `CliOpsM m`
    backend to `Internal.mkApiM`, `promptLineM`, `confirmM`, `runCliM`, or `runCliWithM`. -/
def defaultOps : CliOps :=
  Internal.mkCliOpsFromCapsM
    { files := LeanSwe.LinuxSyscall.Files.defaultOps
      env := LeanSwe.EnvVars.defaultApi }

/-- Default `CmdLineApi` wired directly over `LeanSwe.LinuxSyscall.Files.defaultOps` and
    `LeanSwe.EnvVars.defaultApi` (`dupStdio`/`read`/`write`/`close` + `getEnv`), catching `IO.Error` throws
    from `promptLine`/`confirm` into `.ioError`. Does not flush C/Lean `IO.FS.Stream` buffers or honor
    `IO.withStdin`/`IO.withStdout`/`IO.withStderr`; do not mix buffered `IO.getStdin` reads with `CmdLine`
    `stdin` reads (bytes read ahead by `IO.getStdin` are invisible to descriptor `0` and cannot be recovered
    by flushing). -/
def defaultApi : CmdLineApi :=
  Internal.mkApiFromCapsM
    { files := LeanSwe.LinuxSyscall.Files.defaultOps
      env := LeanSwe.EnvVars.defaultApi }

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

/-- Prompt for a line of input on unbuffered OS stdio descriptors (`0`/`1`), trimming ASCII whitespace and applying `default`.
    Does not flush C/Lean `IO.FS.Stream` buffers or honor `IO.withStdin`/`IO.withStdout`. Never mix with buffered
    `IO.getStdin` reads (read-ahead bytes are invisible to descriptor `0` and cannot be recovered by flushing); flush
    buffered Lean output beforehand when mixing with `IO.print`/`IO.println`, or use `promptLineM` for custom/in-memory streams. -/
@[inline] def promptLine (prompt : String) (default : Option String := none) :
    IO (Except CmdLineError String) :=
  defaultApi.promptLine prompt default

/-- Prompt up to `maxAttempts` times on unbuffered OS stdio descriptors (`0`/`1`/`2`) for `y`/`yes`/`n`/`no` confirmation.
    Does not flush C/Lean `IO.FS.Stream` buffers or honor `IO.withStdin`/`IO.withStdout`/`IO.withStderr`. Never mix with
    buffered `IO.getStdin` reads (read-ahead bytes are invisible to descriptor `0` and cannot be recovered by flushing);
    flush buffered Lean output beforehand when mixing with `IO.print`/`IO.println`, or use `confirmM` for custom/in-memory streams. -/
@[inline] def confirm (prompt : String) (default : Option Bool := none)
    (maxAttempts : Nat := 100) : IO (Except CmdLineError Bool) :=
  defaultApi.confirm prompt default maxAttempts

/-- Execute a full CLI flow on unbuffered OS stdio descriptors (`0`/`1`/`2`) and `LeanSwe.EnvVars`.
    Does not flush C/Lean `IO.FS.Stream` buffers or honor `IO.withStdin`/`IO.withStdout`/`IO.withStderr`. Never mix with
    buffered `IO.getStdin` reads (read-ahead bytes are invisible to descriptor `0` and cannot be recovered by flushing);
    flush buffered Lean output beforehand when mixing with `IO.print`/`IO.println`, or use `runCliM` for custom streams. -/
@[inline] def runCli (spec : CommandSpec) (args : List String)
    (handler : ParsedCmd → IO UInt32) : IO UInt32 :=
  defaultApi.runCli spec args handler

/-- Execute a full CLI flow with custom validators on unbuffered OS stdio descriptors (`0`/`1`/`2`) and `LeanSwe.EnvVars`.
    Does not flush C/Lean `IO.FS.Stream` buffers or honor `IO.withStdin`/`IO.withStdout`/`IO.withStderr`. Never mix with
    buffered `IO.getStdin` reads (read-ahead bytes are invisible to descriptor `0` and cannot be recovered by flushing);
    flush buffered Lean output beforehand when mixing with `IO.print`/`IO.println`, or use `runCliWithM` for custom streams. -/
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
