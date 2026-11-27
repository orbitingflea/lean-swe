import Core.NondetTest
import LeanSwe.CmdLine.Types
import LeanSweProofs.CmdLine.Model
import LeanSwe.LinuxSyscall.Files.Types

namespace LeanSwe.CmdLine

open Core (NondetTest)
open Core.NondetTest

/-- Pure `CliOpsM Id` with empty stdin, no-op stdout/stderr, and clean unset environment. -/
def pureIdCliOps : CliOpsM Id :=
  { readLine := pure none
    writeOut := fun _ => pure ()
    writeErr := fun _ => pure ()
    getEnv := fun _ => pure (.ok none) }

/-- Deterministic `CliOpsM (StateM CliMockState)` backed by `CliMockState`. -/
def mockCliOps : CliOpsM (StateM CliMockState) :=
  { readLine := fun s =>
      match s.stdinLines with
      | [] => (none, s)
      | line :: rest => (some line, { s with stdinLines := rest })
    writeOut := fun text s => ((), { s with stdout := s.stdout ++ text })
    writeErr := fun text s => ((), { s with stderr := s.stderr ++ text })
    getEnv := fun key s =>
      match s.env.find? (fun p => p.1 == key) with
      | none => (.ok none, s)
      | some (_, entry) => (entry.toExcept, s) }

/-- `isValidSpec` rejects duplicate long names, duplicate short names, `help`/`version` collisions, auto `-h`/`-V` collisions, and symmetric `no-` collisions. -/
def test_cmdline_validSpec_rejectsFlagCollisions
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let dupLong : CommandSpec :=
    { name := "app"
      options :=
        [ { name := "a", long := some "port" },
          { name := "b", long := some "port" } ] }
  let dupShort : CommandSpec :=
    { name := "app"
      options :=
        [ { name := "a", short := some 'p' },
          { name := "b", short := some 'p' } ] }
  let helpLong : CommandSpec :=
    { name := "app"
      options := [ { name := "h", long := some "help" } ] }
  let verLong : CommandSpec :=
    { name := "app"
      options := [ { name := "v", long := some "version" } ] }
  let shortHCollision : CommandSpec :=
    { name := "app"
      shortHelp := true
      options := [ { name := "host", short := some 'h' } ] }
  let shortVCollision : CommandSpec :=
    { name := "app"
      version := some "1.0.0"
      shortVersion := true
      options := [ { name := "verbose", short := some 'V' } ] }
  let symNoChild : CommandSpec :=
    { name := "app"
      options := [ { name := "cache", long := some "cache", kind := .bool, global := true } ]
      subcommands :=
        [ { name := "run"
            options := [ { name := "nocache", long := some "no-cache" } ] } ] }
  let symNoParent : CommandSpec :=
    { name := "app"
      options := [ { name := "nocache", long := some "no-cache", global := true } ]
      subcommands :=
        [ { name := "run"
            options := [ { name := "cache", long := some "cache", kind := .bool } ] } ] }
  NondetTest.assert (!api.isValidSpec dupLong)
  NondetTest.assert (!api.isValidSpec dupShort)
  NondetTest.assert (!api.isValidSpec helpLong)
  NondetTest.assert (!api.isValidSpec verLong)
  NondetTest.assert (!api.isValidSpec shortHCollision)
  NondetTest.assert (!api.isValidSpec shortVCollision)
  NondetTest.assert (!api.isValidSpec symNoChild)
  NondetTest.assert (!api.isValidSpec symNoParent)

/-- `isValidSpec` rejects parent non-global options, parent positionals with subcommands, bad positional ordering, invalid `.choice`/defaults, and bad `envVar` keys. -/
def test_cmdline_validSpec_rejectsStructuralAndEnvErrors
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let nonGlobalParent : CommandSpec :=
    { name := "app"
      options := [ { name := "cfg", long := some "cfg", global := false } ]
      subcommands := [ { name := "sub" } ] }
  let parentWithArgs : CommandSpec :=
    { name := "app"
      args := [ { name := "file" } ]
      subcommands := [ { name := "sub" } ] }
  let reqAfterOpt : CommandSpec :=
    { name := "app"
      args :=
        [ { name := "opt", required := false },
          { name := "req", required := true } ] }
  let argAfterVar : CommandSpec :=
    { name := "app"
      args :=
        [ { name := "files", variadic := true },
          { name := "extra", required := false } ] }
  let emptyChoice : CommandSpec :=
    { name := "app"
      options := [ { name := "fmt", long := some "fmt", kind := .choice [] } ] }
  let badDefault : CommandSpec :=
    { name := "app"
      options := [ { name := "port", long := some "port", kind := .nat, default := some "abc" } ] }
  let repBoolDefault : CommandSpec :=
    { name := "app"
      options := [ { name := "verb", short := some 'v', kind := .bool, repeatable := true, default := some "false" } ] }
  let badEnvKey : CommandSpec :=
    { name := "app"
      options := [ { name := "port", long := some "port", envVar := some "A=B" } ] }
  let argCollidesGlobal : CommandSpec :=
    { name := "app"
      options := [ { name := "target", long := some "target", global := true } ]
      subcommands :=
        [ { name := "build"
            args := [ { name := "target" } ] } ] }
  NondetTest.assert (!api.isValidSpec nonGlobalParent)
  NondetTest.assert (!api.isValidSpec parentWithArgs)
  NondetTest.assert (!api.isValidSpec reqAfterOpt)
  NondetTest.assert (!api.isValidSpec argAfterVar)
  NondetTest.assert (!api.isValidSpec emptyChoice)
  NondetTest.assert (!api.isValidSpec badDefault)
  NondetTest.assert (!api.isValidSpec repBoolDefault)
  NondetTest.assert (!api.isValidSpec badEnvKey)
  NondetTest.assert (!api.isValidSpec argCollidesGlobal)

/-- Opting out of `shortHelp` / `shortVersion` frees `-h` / `-V` for user options, and `parse` rejects invalid specs with `.invalidSpec`. -/
def test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "ssh"
      version := some "1.0"
      shortHelp := false
      shortVersion := false
      options :=
        [ { name := "host", short := some 'h', kind := .string },
          { name := "vlan", short := some 'V', kind := .nat } ] }
  NondetTest.assert (api.isValidSpec spec)
  match api.parse spec ["-h", "localhost", "-V", "42"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert (parsed.getString "host" = some "localhost" ∧ parsed.getNat "vlan" = some 42)
  let badSpec : CommandSpec := { name := "", options := [] }
  match api.parse badSpec [] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidSpec ∧ e.message ≠ "")

/-- Bundled short flags support `-vvv` counting, `-abp8080` attached values, `-p=8080` preserving `'='`, and reject non-countable `-vv`. -/
def test_cmdline_parse_shortBundlesAndValues
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "app"
      options :=
        [ { name := "a", short := some 'a', kind := .bool },
          { name := "b", short := some 'b', kind := .bool },
          { name := "verb", short := some 'v', kind := .bool, repeatable := true },
          { name := "port", short := some 'p', kind := .nat },
          { name := "raw", short := some 'r', kind := .string } ] }
  match api.parse spec ["-abvvvp8080", "-r=xyz"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert
      (parsed.hasFlag "a" ∧
       parsed.hasFlag "b" ∧
       parsed.getCount "verb" = 3 ∧
       parsed.getNat "port" = some 8080 ∧
       parsed.getString "raw" = some "=xyz")
  let nonCountable : CommandSpec :=
    { name := "app"
      options := [ { name := "verb", short := some 'v', kind := .bool, repeatable := false } ] }
  match api.parse nonCountable ["-vv"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue ∧ e.message ≠ "")

/-- Left-to-right short scanning treats `-oh` as attached value `"h"`, and rejects `-xh` with unknown `-x` before checking `'h'`. -/
def test_cmdline_parse_shortLeftToRightHelpPrecedence
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "app"
      options := [ { name := "out", short := some 'o', kind := .string } ] }
  match api.parse spec ["-oh"] with
  | .error _ => NondetTest.assert False
  | .ok parsed => NondetTest.assert (parsed.getString "out" = some "h")
  match api.parse spec ["-xh"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownOption ∧ e.message ≠ "")

/-- Duplicate single options (`--port 80 --port=90`, `--cache --no-cache`, `-c --no-cache`) fail with `.invalidValue`, while `--no-<flag>` satisfies `required = true` bools and `--flag false` treats `false` as positional. -/
def test_cmdline_parse_duplicatesNegationAndSpaceBool
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "app"
      options :=
        [ { name := "port", long := some "port", kind := .nat },
          { name := "cache", long := some "cache", short := some 'c', kind := .bool, required := true } ]
      args := [ { name := "arg", required := false } ] }
  match api.parse spec ["--port", "80", "--port=90", "--cache"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)
  match api.parse spec ["--cache", "--no-cache"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)
  match api.parse spec ["-c", "--no-cache"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)
  match api.parse spec ["--no-cache"] with
  | .error _ => NondetTest.assert False
  | .ok parsed => NondetTest.assert (parsed.getBool "cache" = some false ∧ parsed.hasFlag "cache" = false)
  match api.parse spec ["--cache", "false"] with
  | .error _ => NondetTest.assert False
  | .ok parsed => NondetTest.assert (parsed.getBool "cache" = some true ∧ parsed.getString "arg" = some "false")

/-- Negative numbers work as option values (`--offset -5`) and after `--` (`-- -5`), while bare `-5` fails as `.unknownOption` and single `"-"` is a literal positional. -/
def test_cmdline_parse_negativeNumbersAndDashDash
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "app"
      options := [ { name := "offset", long := some "offset", kind := .int } ]
      args := [ { name := "items", kind := .string, required := false, variadic := true } ] }
  match api.parse spec ["--offset", "-5", "--", "-5", "-", "--", "--help"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert
      (parsed.getInt "offset" = some (-5) ∧
       parsed.rawPositionals = ["-5", "-", "--", "--help"])
  match api.parse spec ["-5"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownOption)
  match api.parse spec ["-"] with
  | .error _ => NondetTest.assert False
  | .ok parsed => NondetTest.assert (parsed.rawPositionals = ["-"])

/-- Subcommands accept global ancestor options before and after subcommand names, resolve omitted global defaults/envs, avoid consuming `--config subcmd` as a subcommand, and distinguish `tool -- subcmd` vs `tool`. -/
def test_cmdline_parse_subcommandsAndInheritedGlobals
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "tool"
      options :=
        [ { name := "config", long := some "config", kind := .string, default := some "default.conf", global := true },
          { name := "verbose", short := some 'v', long := some "verbose", kind := .bool, global := true } ]
      subcommands :=
        [ { name := "build"
            args := [ { name := "target", required := false } ] } ] }
  match api.parse spec ["--config", "build", "build", "--verbose", "all"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert
      (parsed.subcommandPath = ["build"] ∧
       parsed.getString "config" = some "build" ∧
       parsed.getBool "verbose" = some true ∧
       parsed.getString "target" = some "all")
  match api.parse spec ["build"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert
      (parsed.subcommandPath = ["build"] ∧
       parsed.getString "config" = some "default.conf" ∧
       parsed.getBool "verbose" = some false)
  match api.parse spec ["--", "build"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unexpectedArgument)
  match api.parse spec [] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .missingArgument)

/-- Unknown long options and unknown subcommands emit Levenshtein `"did you mean"` suggestions when within threshold. -/
def test_cmdline_parse_typoSuggestions
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "tool"
      options := [ { name := "verbose", long := some "verbose", kind := .bool, global := true } ]
      subcommands := [ { name := "build" }, { name := "clean" } ] }
  match api.parse spec ["--verbos"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownOption ∧ e.message.contains "did you mean '--verbose'")
  match api.parse spec ["biuld"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownSubcommand ∧ e.message.contains "did you mean 'build'")

/-- Custom validators in `parseWith` reject invalid `.custom` values with `.invalidValue`, while valid ones decode via `ParsedCmd.getCustom`. -/
def test_cmdline_parseWith_customValidatorAndDecoder
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "app"
      options := [ { name := "tag", long := some "tag", kind := .custom "nonempty" } ] }
  let validators : CustomValidators :=
    [("nonempty", fun s => if s.isEmpty then .error "tag must be non-empty" else .ok ())]
  match api.parseWith spec ["--tag="] validators with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue ∧ e.message = "tag must be non-empty")
  match api.parseWith spec ["--tag=v1"] validators with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    let decoded : Except CmdLineError (Option String) := parsed.getCustom "tag" (fun s => .ok s)
    NondetTest.assert (decoded = .ok (some "v1"))

/-- `CLI > env > default` precedence holds for normal and inherited global options: empty env falls back to default, invalid env fails unless overridden by CLI, and `.ioError` propagates. -/
def test_cmdline_env_precedenceAndErrorPropagation
    {runner} [NondetTest runner] (mkApi : CliOpsM (StateM CliMockState) → CmdLineApiM (StateM CliMockState)) : runner Unit := do
  let spec : CommandSpec :=
    { name := "tool"
      options :=
        [ { name := "port", long := some "port", kind := .nat, default := some "8080", envVar := some "PORT", global := true },
          { name := "debug", long := some "debug", kind := .bool, envVar := some "DEBUG", global := true } ]
      subcommands := [ { name := "serve" } ] }
  let api := mkApi mockCliOps
  let stEmpty : CliMockState := { env := [("PORT", .set ""), ("DEBUG", .set "YES")] }
  let (rEmpty, _) := (api.parseWithEnv spec ["serve"] []).run stEmpty
  match rEmpty with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert (parsed.getNat "port" = some 8080 ∧ parsed.getBool "debug" = some true)
  let stBadEnv : CliMockState := { env := [("PORT", .set "abc")] }
  let (rBadEnv, _) := (api.parseWithEnv spec ["serve"] []).run stBadEnv
  match rBadEnv with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)
  let (rCliWins, _) := (api.parseWithEnv spec ["serve", "--port", "9090"] []).run stBadEnv
  match rCliWins with
  | .error _ => NondetTest.assert False
  | .ok parsed => NondetTest.assert (parsed.getNat "port" = some 9090)
  let stIoErr : CliMockState := { env := [("PORT", .error { kind := .ioError, message := "bad utf8" })] }
  let (rIoErr, _) := (api.parseWithEnv spec ["serve"] []).run stIoErr
  match rIoErr with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .ioError ∧ e.message = "bad utf8")

/-- Canonical `renderArgs` handles short-only empty strings (`-s ""`), positionals starting with `-` (after `--`), repeatable options, and round-trips through `parse`. -/
def test_cmdline_renderArgs_roundTripEdgeCases
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "tool"
      options :=
        [ { name := "sep", short := some 's', kind := .string, global := true },
          { name := "verb", short := some 'v', kind := .bool, repeatable := true, global := true },
          { name := "cache", long := some "cache", kind := .bool, default := some "true", global := true } ]
      subcommands :=
        [ { name := "cp"
            args :=
              [ { name := "src", kind := .string },
                { name := "dst", kind := .string } ] } ] }
  match api.parse spec ["cp", "-s", "", "-vv", "--no-cache", "--", "a.txt", "-b.txt"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert
      (parsed.subcommandPath = ["cp"] ∧
       parsed.getString "sep" = some "" ∧
       parsed.getCount "verb" = 2 ∧
       parsed.getBool "cache" = some false ∧
       parsed.rawPositionals = ["a.txt", "-b.txt"])
    match api.renderArgs spec parsed with
    | .error _ => NondetTest.assert False
    | .ok rendered =>
      NondetTest.assert (api.parse spec rendered = .ok parsed)

/-- Every valid `CommandSpec` and `args` that parses and renders via `renderArgs` round-trips back to the exact `ParsedCmd`. -/
def test_cmdline_renderArgs_universalRoundTrip
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec ← nondet CommandSpec
  let args ← nondet (List String)
  assume (Model.isValidSpec spec = true)
  match api.parse spec args with
  | .error _ => assume False
  | .ok parsed =>
    match api.renderArgs spec parsed with
    | .error _ => assume False
    | .ok rendered =>
      NondetTest.assert (api.parse spec rendered = .ok parsed)

/-- `runCli` writes help/version to `stdout` with exit code `0` without calling `handler`, writes errors to `stderr` with exit code `2` without calling `handler`, and returns `handler`'s exact exit code on valid input. -/
def test_cmdline_runCli_routingAndExitCodes
    {runner} [NondetTest runner] (mkApi : CliOpsM (StateM CliMockState) → CmdLineApiM (StateM CliMockState)) : runner Unit := do
  let spec : CommandSpec :=
    { name := "mytool"
      version := some "2.1.0"
      options := [ { name := "port", long := some "port", kind := .nat, envVar := some "PORT" } ] }
  let api := mkApi mockCliOps
  let handlerCalledExit : UInt32 := 7
  let failHandler : ParsedCmd → StateM CliMockState UInt32 := fun _ s =>
    (handlerCalledExit, { s with stdout := s.stdout ++ "HANDLER_CALLED" })
  let (codeHelp, stHelp) := (api.runCli spec ["--help"] failHandler).run {}
  NondetTest.assert (codeHelp = 0 ∧ stHelp.stdout ≠ "" ∧ !stHelp.stdout.contains "HANDLER_CALLED" ∧ stHelp.stderr = "")
  let (codeVer, stVer) := (api.runCli spec ["-V"] failHandler).run {}
  NondetTest.assert (codeVer = 0 ∧ stVer.stdout = "mytool 2.1.0\n" ∧ stVer.stderr = "")
  let (codeErr, stErr) := (api.runCli spec ["--unknown"] failHandler).run {}
  NondetTest.assert (codeErr = 2 ∧ stErr.stdout = "" ∧ stErr.stderr ≠ "")
  let stIoErr : CliMockState := { env := [("PORT", .error { kind := .ioError, message := "utf8" })] }
  let (codeIoErr, stIoOut) := (api.runCli spec [] failHandler).run stIoErr
  NondetTest.assert (codeIoErr = 2 ∧ stIoOut.stdout = "" ∧ stIoOut.stderr.contains "utf8")
  let exitCode ← nondet UInt32
  let (codeOk, stOk) := (api.runCli spec ["--port", "443"] (fun cmd s =>
    (if cmd.getNat "port" = some 443 then exitCode else 99, s))).run {}
  NondetTest.assert (codeOk = exitCode ∧ stOk.stderr = "")

/-- `promptLine` and `confirm` trim ASCII/CRLF whitespace, apply defaults on blank input, emit re-prompt only when `remainingAttempts > 1`, and fail with `.eof` on EOF. -/
def test_cmdline_interactive_promptAndConfirm
    {runner} [NondetTest runner] (mkApi : CliOpsM (StateM CliMockState) → CmdLineApiM (StateM CliMockState)) : runner Unit := do
  let api := mkApi mockCliOps
  let (pOk, stP) := (api.promptLine "Name: " (some "anon")).run { stdinLines := ["  \r\n"] }
  NondetTest.assert (pOk = .ok "anon" ∧ stP.stdout = "Name: ")
  let (pTrim, _) := (api.promptLine "Name: " none).run { stdinLines := ["  alice \t\r\n"] }
  NondetTest.assert (pTrim = .ok "alice")
  let (pEof, _) := (api.promptLine "Name: " (some "anon")).run { stdinLines := [] }
  NondetTest.assert (∃ e, pEof = .error e ∧ e.kind = .eof)
  let (cYes, stCY) := (api.confirm "Ok? " none 3).run { stdinLines := ["maybe\r", "  YES  "] }
  NondetTest.assert (cYes = .ok true ∧ stCY.stderr = "Please answer yes or no.\n")
  let (cOneBad, stC1) := (api.confirm "Ok? " none 1).run { stdinLines := ["maybe"] }
  NondetTest.assert ((∃ e, cOneBad = .error e ∧ e.kind = .invalidValue) ∧ stC1.stderr = "")
  let (cEof, _) := (api.confirm "Ok? " (some true) 3).run { stdinLines := ["invalid"] }
  NondetTest.assert (∃ e, cEof = .error e ∧ e.kind = .eof)

/-- `--help`/`-h`/`--version`/`-V` follow strict left-to-right scanning, respect `version = none`, and use `rootSpec.name` with `effectiveVersion` on subcommands. -/
def test_cmdline_parse_helpAndVersionRouting
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let noVer : CommandSpec := { name := "app", version := none }
  match api.parse noVer ["--version"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownOption)
  match api.parse noVer ["-V"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownOption)
  let withVer : CommandSpec :=
    { name := "tool"
      version := some "1.0"
      options := [ { name := "port", long := some "port", kind := .nat, global := true } ]
      subcommands := [ { name := "sub", version := some "2.0" } ] }
  match api.parse withVer ["--badopt", "--help"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownOption)
  match api.parse withVer ["--help", "--badopt"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .helpRequested ∧ e.message ≠ "")
  match api.parse withVer ["sub", "-V"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .versionRequested ∧ e.message = "tool 2.0\n")
  match api.parse withVer ["--port", "--help"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)

/-- Positional `ArgSpec` resolution handles required/optional/variadic/default arguments and reports `.missingArgument`, `.unexpectedArgument`, and `.invalidValue` accurately. -/
def test_cmdline_parse_positionalArgsAndErrors
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "app"
      options :=
        [ { name := "port", long := some "port", kind := .nat },
          { name := "flag", long := some "flag", kind := .bool },
          { name := "rep", long := some "rep", kind := .bool, repeatable := true } ]
      args :=
        [ { name := "count", kind := .nat, required := true },
          { name := "mode", kind := .choice ["fast", "safe"], required := false, default := some "safe" },
          { name := "rest", kind := .string, required := false, variadic := true } ] }
  match api.parse spec ["10"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert
      (parsed.getNat "count" = some 10 ∧
       parsed.getChoice "mode" = some "safe" ∧
       parsed.getList "rest" = [])
  match api.parse spec ["10", "fast", "a", "b"] with
  | .error _ => NondetTest.assert False
  | .ok parsed =>
    NondetTest.assert
      (parsed.getChoice "mode" = some "fast" ∧
       parsed.getList "rest" = [.string "a", .string "b"])
  match api.parse spec [] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .missingArgument)
  match api.parse spec ["not-nat"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)
  match api.parse spec ["--port"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .missingArgument)
  match api.parse spec ["--no-flag=bar", "1"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)
  match api.parse spec ["--rep=false", "1"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .invalidValue)
  let noVariadic : CommandSpec :=
    { name := "app"
      args := [ { name := "one", kind := .string, required := true } ] }
  match api.parse noVariadic ["a", "b"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unexpectedArgument)

/-- `renderHelp` renders usage, subcommands, args, and inherited global options for root and subcommand paths, rejecting invalid specs and unknown paths; `renderVersion` formats `<name> <ver>\n`. -/
def test_cmdline_renderHelpAndVersion
    {runner} [NondetTest runner] (api : CmdLineApi) : runner Unit := do
  let spec : CommandSpec :=
    { name := "tool"
      version := some "3.0"
      about := "Manage widgets"
      options := [ { name := "cfg", long := some "cfg", help := "Config file", global := true } ]
      subcommands :=
        [ { name := "add"
            about := "Add widget"
            args := [ { name := "widget", help := "Widget name" } ] } ] }
  match api.renderHelp spec [] with
  | .error _ => NondetTest.assert False
  | .ok h =>
    NondetTest.assert (h.contains "tool" ∧ h.contains "add" ∧ h.contains "--cfg" ∧ h.contains "--help" ∧ h.contains "--version")
  match api.renderHelp spec ["add"] with
  | .error _ => NondetTest.assert False
  | .ok h =>
    NondetTest.assert (h.contains "tool add" ∧ h.contains "widget" ∧ h.contains "--cfg")
  match api.renderHelp spec ["missing"] with
  | .ok _ => NondetTest.assert False
  | .error e => NondetTest.assert (e.kind = .unknownSubcommand)
  NondetTest.assert (api.renderVersion "tool" "3.0" = "tool 3.0\n")

/-- `runCliWith` rejects custom validation failures with exit code `2` and `stderr` without calling `handler`, and passes valid values to `handler`. -/
def test_cmdline_runCliWith_customValidator
    {runner} [NondetTest runner] (mkApi : CliOpsM (StateM CliMockState) → CmdLineApiM (StateM CliMockState)) : runner Unit := do
  let spec : CommandSpec :=
    { name := "app"
      options := [ { name := "id", long := some "id", kind := .custom "nonempty" } ] }
  let validators : CustomValidators :=
    [("nonempty", fun s => if s.isEmpty then .error "id empty" else .ok ())]
  let api := mkApi mockCliOps
  let (cBad, stBad) := (api.runCliWith spec ["--id="] validators (fun _ => pure 0)).run {}
  NondetTest.assert (cBad = 2 ∧ stBad.stdout = "" ∧ stBad.stderr.contains "id empty")
  let (cOk, stOk) := (api.runCliWith spec ["--id=ok"] validators (fun cmd =>
    pure (match cmd.getCustom "id" (fun s => .ok s) with | .ok (some "ok") => 5 | _ => 1))).run {}
  NondetTest.assert (cOk = 5 ∧ stOk.stderr = "")

/-- Under `pureIdCliOps` (all environment variables unset), `parseWithEnv` agrees universally with `parseWith`
    for every `CommandSpec`, argument list, and custom validator table. -/
def test_cmdline_parseWithEnv_unsetEnvMatchesParseWith
    {runner} [NondetTest runner]
    (api : CmdLineApi) (mkApi : CliOpsM Id → CmdLineApiM Id) : runner Unit := do
  let spec ← nondet CommandSpec
  let args ← nondet (List String)
  let validators ← nondet CustomValidators
  NondetTest.assert ((mkApi pureIdCliOps).parseWithEnv spec args validators = api.parseWith spec args validators)

/-- Scripted `FilesOpsM` state for verifying `mkFilesCliOpsM` `EINTR` retry, partial writes, EOF, and FD conservation. -/
structure ScriptedStdioState where
  /-- Queued `read` outcomes for `.stdin`. -/
  readQueue : List (Except LeanSwe.LinuxSyscall.Errno ByteArray) := []
  /-- Queued `write` outcomes (`UInt32` byte count or `Errno`) for `.stdout`/`.stderr`. -/
  writeQueue : List (Except LeanSwe.LinuxSyscall.Errno UInt32) := []
  /-- Accumulated bytes actually committed by successful `write` steps. -/
  written : ByteArray := ByteArray.empty
  /-- Currently open duplicated stdio descriptors (`dupStdio` inserts, `close` removes). -/
  openFds : List Nat := []
  /-- Monotonic next descriptor ID and total `dupStdio` call count. -/
  dupCount : Nat := 0
  deriving Inhabited

/-- Pure state+exception monad over `ScriptedStdioState` instantiating `mkFilesCliOpsM`. -/
abbrev ScriptedCliM := ExceptT IO.Error (StateM ScriptedStdioState)

instance : MonadFinally ScriptedCliM where
  tryFinally' x f := show StateM ScriptedStdioState _ from do
    let r ← (x : StateM ScriptedStdioState _)
    let opt := match r with | .ok a => some a | .error _ => none
    let b ← (f opt : StateM ScriptedStdioState _)
    match r, b with
    | _, .error e => return .error e
    | .error e, .ok _ => return .error e
    | .ok a, .ok bVal => return .ok (a, bVal)

/-- Builder signature for `SysBridge.mkFilesCliOpsM` specialized to `ScriptedCliM`. -/
abbrev FilesCliOpsBuilder :=
  LeanSwe.LinuxSyscall.Files.FilesOpsM ScriptedCliM Nat →
  (String → ScriptedCliM (Except CmdLineError (Option String))) →
  CliOpsM ScriptedCliM

private def unimplScripted {α : Type} : ScriptedCliM (Except LeanSwe.LinuxSyscall.Errno α) :=
  pure (.error LeanSwe.LinuxSyscall.Errno.ENOSYS)

/-- Scripted `FilesOpsM ScriptedCliM Nat` tracking `dupStdio`, `close`, `read`, and partial `write` slices. -/
def scriptedStdioFilesOps : LeanSwe.LinuxSyscall.Files.FilesOpsM ScriptedCliM Nat :=
  let liftState {α : Type} (act : StateM ScriptedStdioState α) : ScriptedCliM α :=
    show StateM ScriptedStdioState (Except IO.Error α) from (fun a => .ok a) <$> act
  { openat := fun _ _ _ _ => unimplScripted
    openat2 := fun _ _ _ => unimplScripted
    close := fun fd => liftState do
      let st ← get
      if st.openFds.contains fd then
        set { st with openFds := st.openFds.erase fd }
        return .ok ()
      else
        return .error LeanSwe.LinuxSyscall.Errno.EBADF
    read := fun fd _ => liftState do
      let st ← get
      if !st.openFds.contains fd then
        return .error LeanSwe.LinuxSyscall.Errno.EBADF
      else
        match st.readQueue with
        | [] => return .ok ByteArray.empty
        | r :: rest =>
          set { st with readQueue := rest }
          return r
    write := fun fd slice => liftState do
      let st ← get
      if !st.openFds.contains fd then
        return .error LeanSwe.LinuxSyscall.Errno.EBADF
      else
        match st.writeQueue with
        | [] => return .error LeanSwe.LinuxSyscall.Errno.EIO
        | .error e :: rest =>
          set { st with writeQueue := rest }
          return .error e
        | .ok n :: rest =>
          let k := min slice.size n.toNat
          set { st with writeQueue := rest, written := st.written ++ slice.extract 0 k }
          return .ok (UInt32.ofNat k)
    fstat := fun _ => unimplScripted
    fstatat := fun _ _ _ => unimplScripted
    faccessat := fun _ _ _ _ => unimplScripted
    mkdirat := fun _ _ _ => unimplScripted
    unlinkat := fun _ _ _ => unimplScripted
    renameat2 := fun _ _ _ _ _ => unimplScripted
    symlinkat := fun _ _ _ => unimplScripted
    readlinkat := fun _ _ _ => unimplScripted
    getdents64 := fun _ _ => unimplScripted
    fchmodat := fun _ _ _ => unimplScripted
    fchmod := fun _ _ => unimplScripted
    flock := fun _ _ => unimplScripted
    fcntl := fun _ _ => unimplScripted
    fsync := fun _ => unimplScripted
    getcwd := fun _ => unimplScripted
    lseek := fun _ _ _ => unimplScripted
    reopenReadOnly := fun _ => unimplScripted
    dupStdio := fun _ => liftState do
      let st ← get
      let fd := st.dupCount + 10
      set { st with openFds := fd :: st.openFds, dupCount := st.dupCount + 1 }
      return .ok fd }

/-- `mkFilesCliOpsM` preserves accumulated line prefix bytes across mid-line `EINTR`, handles `0`-byte EOF without over-reading past `\n`, reassembles partial `write` slices across `EINTR` (short-circuiting `""` and rejecting `0`-byte progress as `EIO`), and always closes duplicated FDs on both `.ok` and `.error`. -/
def test_cmdline_mkFilesCliOps_eintrPartialWriteAndEof
    {runner} [NondetTest runner] (mkCliOps : FilesCliOpsBuilder) : runner Unit := do
  let ops := mkCliOps scriptedStdioFilesOps (fun _ => pure (.ok none))
  let eintrCount ← nondet Nat
  assume (eintrCount ≤ 8)
  let sRead : ScriptedStdioState :=
    { readQueue :=
        [.ok (ByteArray.mk #[0x68]), .ok (ByteArray.mk #[0x69])] ++
        List.replicate eintrCount (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++
        [.ok (ByteArray.mk #[0x0D]), .ok (ByteArray.mk #[0x0A]), .ok (ByteArray.mk #[0x5A])] }
  let (rLine, sRead') := (ops.readLine : StateM ScriptedStdioState _).run sRead
  NondetTest.assert ((match rLine with | .ok v => v == some "hi" | .error _ => false) = true)
  NondetTest.assert (sRead'.openFds = [] ∧ sRead'.dupCount = 1 ∧ sRead'.readQueue.length = 1)
  let sEof : ScriptedStdioState := { readQueue := [.ok ByteArray.empty] }
  let (rEof, sEof') := (ops.readLine : StateM ScriptedStdioState _).run sEof
  NondetTest.assert ((match rEof with | .ok v => v == none | .error _ => false) = true ∧ sEof'.openFds = [])
  let sPartialEof : ScriptedStdioState :=
    { readQueue :=
        [.ok (ByteArray.mk #[0x6F]), .error LeanSwe.LinuxSyscall.Errno.EINTR,
         .ok (ByteArray.mk #[0x6B]), .ok ByteArray.empty] }
  let (rPEof, sPEof') := (ops.readLine : StateM ScriptedStdioState _).run sPartialEof
  NondetTest.assert ((match rPEof with | .ok v => v == some "ok" | .error _ => false) = true ∧ sPEof'.openFds = [])
  let sReadErr : ScriptedStdioState :=
    { readQueue := [.ok (ByteArray.mk #[0x61]), .error LeanSwe.LinuxSyscall.Errno.EIO] }
  let (rRErr, sRErr') := (ops.readLine : StateM ScriptedStdioState _).run sReadErr
  NondetTest.assert (rRErr.isOk = false ∧ sRErr'.openFds = [] ∧ sRErr'.dupCount = 1)
  let (rEmptyOut, sEmptyOut) := (ops.writeOut "" : StateM ScriptedStdioState _).run {}
  let (rEmptyErr, sEmptyErr) := (ops.writeErr "" : StateM ScriptedStdioState _).run {}
  NondetTest.assert (rEmptyOut.isOk = true ∧ sEmptyOut.dupCount = 0 ∧ sEmptyOut.openFds = [])
  NondetTest.assert (rEmptyErr.isOk = true ∧ sEmptyErr.dupCount = 0 ∧ sEmptyErr.openFds = [])
  let sWrite : ScriptedStdioState :=
    { writeQueue :=
        [.error LeanSwe.LinuxSyscall.Errno.EINTR, .ok 2,
         .error LeanSwe.LinuxSyscall.Errno.EINTR, .ok 3] }
  let (rWrite, sWrite') := (ops.writeOut "hello" : StateM ScriptedStdioState _).run sWrite
  NondetTest.assert (rWrite.isOk = true ∧ sWrite'.written = "hello".toUTF8 ∧ sWrite'.openFds = [] ∧ sWrite'.dupCount = 1)
  let sWriteZero : ScriptedStdioState :=
    { writeQueue := [.ok 0] }
  let (rWZero, sWZero') := (ops.writeOut "hello" : StateM ScriptedStdioState _).run sWriteZero
  NondetTest.assert (rWZero.isOk = false ∧ sWZero'.openFds = [] ∧ sWZero'.dupCount = 1)
  let sWriteErr : ScriptedStdioState :=
    { writeQueue := [.ok 2, .error LeanSwe.LinuxSyscall.Errno.ENOSPC] }
  let (rWErr, sWErr') := (ops.writeErr "hello" : StateM ScriptedStdioState _).run sWriteErr
  NondetTest.assert (rWErr.isOk = false ∧ sWErr'.openFds = [] ∧ sWErr'.dupCount = 1)

end LeanSwe.CmdLine
