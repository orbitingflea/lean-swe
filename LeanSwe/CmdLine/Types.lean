namespace LeanSwe.CmdLine

/-- Supported typed value schemas for CLI options and positional arguments. -/
inductive ValueKind where
  /-- Arbitrary UTF-8 string value. -/
  | string
  /-- Boolean flag (`1`/`true`/`yes`/`on` vs `0`/`false`/`no`/`off`). -/
  | bool
  /-- Non-negative integer parsed from ASCII digits `[0-9]+`. -/
  | nat
  /-- Signed integer parsed from optional `-` and ASCII digits `[0-9]+`. -/
  | int
  /-- Exact string membership within a non-empty list of allowed choices. -/
  | choice (options : List String)
  /-- Raw string tagged with a custom type name for validator/decoder hooks. -/
  | custom (typeName : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed value stored in a resolved `ParsedCmd`. -/
inductive OptValue where
  /-- Parsed string value. -/
  | string (val : String)
  /-- Parsed boolean value. -/
  | bool (val : Bool)
  /-- Parsed natural number value. -/
  | nat (val : Nat)
  /-- Parsed signed integer value. -/
  | int (val : Int)
  /-- Parsed enumerated choice value. -/
  | choice (val : String)
  /-- Raw string preserved for custom decoding. -/
  | custom (val : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Declarative specification of a CLI option flag. -/
structure OptSpec where
  /-- Canonical lookup key in `ParsedCmd`. -/
  name : String
  /-- Optional long option name without leading `--`. -/
  long : Option String := none
  /-- Optional single-character short option name without leading `-`. -/
  short : Option Char := none
  /-- Expected value schema. -/
  kind : ValueKind := .string
  /-- Description printed in generated help text. -/
  help : String := ""
  /-- Placeholder metavar printed next to value-taking options in help text. -/
  valueName : Option String := none
  /-- Whether at least one value (from CLI, env, or default) is required. -/
  required : Bool := false
  /-- Whether multiple occurrences are allowed (countable for `.bool`, list-valued otherwise). -/
  repeatable : Bool := false
  /-- Optional raw default value string parsed according to `kind`. -/
  default : Option String := none
  /-- Optional environment variable fallback name consulted when omitted on CLI. -/
  envVar : Option String := none
  /-- Whether this option propagates down to nested subcommands. -/
  global : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Declarative specification of a positional CLI argument. -/
structure ArgSpec where
  /-- Canonical lookup key in `ParsedCmd`. -/
  name : String
  /-- Description printed in generated help text. -/
  help : String := ""
  /-- Expected value schema. -/
  kind : ValueKind := .string
  /-- Whether at least one positional value (or default) is required. -/
  required : Bool := true
  /-- Whether this final positional argument consumes all remaining positionals. -/
  variadic : Bool := false
  /-- Optional raw default value string parsed when omitted. -/
  default : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Declarative specification of a command or subcommand. -/
structure CommandSpec where
  /-- Command or subcommand token name. -/
  name : String
  /-- Optional version string printed on `--version` / `-V`. -/
  version : Option String := none
  /-- Short summary printed in help text. -/
  about : String := ""
  /-- Whether `-h` is automatically enabled alongside `--help`. -/
  shortHelp : Bool := true
  /-- Whether `-V` is automatically enabled alongside `--version` when version is present. -/
  shortVersion : Bool := true
  /-- Declared options for this command. -/
  options : List OptSpec := []
  /-- Declared positional arguments for this command. -/
  args : List ArgSpec := []
  /-- Nested subcommands dispatched from this command. -/
  subcommands : List CommandSpec := []
  deriving Repr, BEq, Inhabited

/-- Classification of `LeanSwe.CmdLine` parsing, validation, and runtime errors. -/
inductive CmdLineErrorKind where
  /-- `--help` or `-h` was requested. -/
  | helpRequested
  /-- `--version` or `-V` was requested. -/
  | versionRequested
  /-- Unrecognized option flag was passed. -/
  | unknownOption
  /-- Required option was not provided on CLI, env, or default. -/
  | missingOption
  /-- Required positional argument, option value, or subcommand was missing. -/
  | missingArgument
  /-- Unexpected extra positional argument was supplied. -/
  | unexpectedArgument
  /-- Value failed typed parsing, validation, or duplicate-option rules. -/
  | invalidValue
  /-- Unrecognized subcommand token was supplied. -/
  | unknownSubcommand
  /-- `CommandSpec` failed `ValidSpec` well-formedness checks. -/
  | invalidSpec
  /-- Interactive input stream reached end-of-file before receiving a line. -/
  | eof
  /-- Underlying `CliOpsM` environment or I/O call failed. -/
  | ioError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed diagnostic error returned by `LeanSwe.CmdLine` operations. -/
structure CmdLineError where
  /-- Machine-checkable error category. -/
  kind : CmdLineErrorKind
  /-- Non-empty human-readable message (or formatted help/version text). -/
  message : String
  /-- Optional failing option, argument, subcommand, or env key name. -/
  target : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Result of parsing and resolving a CLI invocation against a `CommandSpec`. -/
structure ParsedCmd where
  /-- Sequence of matched subcommand names from root (`[]` when no subcommand matched). -/
  subcommandPath : List String := []
  /-- Resolved visible options in canonical order, omitting absent non-bools and zero-count repeatables. -/
  options : List (String × List OptValue) := []
  /-- Resolved positional arguments in declaration order, omitting absent optionals. -/
  args : List (String × List OptValue) := []
  /-- Raw positional tokens collected during parsing (preserving exact strings for `renderArgs`). -/
  rawPositionals : List String := []
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ParsedCmd

/-- Look up raw `OptValue` list for `name` in `cmd.options` first, then `cmd.args`. -/
def lookupValues (cmd : ParsedCmd) (name : String) : Option (List OptValue) :=
  match cmd.options.find? (fun p => p.1 == name) with
  | some p => some p.2
  | none => (cmd.args.find? (fun p => p.1 == name)).map (·.2)

/-- Return the last resolved `Bool` value for `name`, or `none` if absent or non-boolean. -/
def getBool (cmd : ParsedCmd) (name : String) : Option Bool :=
  match cmd.lookupValues name with
  | some vals =>
    match vals.getLast? with
    | some (.bool b) => some b
    | _ => none
  | none => none

/-- Count true occurrences for boolean options or total values for repeatable non-boolean entries. -/
def getCount (cmd : ParsedCmd) (name : String) : Nat :=
  match cmd.lookupValues name with
  | none => 0
  | some vals =>
    if vals.any (fun | .bool _ => true | _ => false) then
      (vals.filter (fun | .bool true => true | _ => false)).length
    else
      vals.length

/-- Return `true` iff `cmd.getCount name > 0`. -/
def hasFlag (cmd : ParsedCmd) (name : String) : Bool :=
  cmd.getCount name > 0

/-- Return the resolved `String` value for `name`, or `none` if absent or not `.string`. -/
def getString (cmd : ParsedCmd) (name : String) : Option String :=
  match cmd.lookupValues name with
  | some vals =>
    match vals.getLast? with
    | some (.string s) => some s
    | _ => none
  | none => none

/-- Return the resolved `Nat` value for `name`, or `none` if absent or not `.nat`. -/
def getNat (cmd : ParsedCmd) (name : String) : Option Nat :=
  match cmd.lookupValues name with
  | some vals =>
    match vals.getLast? with
    | some (.nat n) => some n
    | _ => none
  | none => none

/-- Return the resolved `Int` value for `name`, or `none` if absent or not `.int`. -/
def getInt (cmd : ParsedCmd) (name : String) : Option Int :=
  match cmd.lookupValues name with
  | some vals =>
    match vals.getLast? with
    | some (.int i) => some i
    | _ => none
  | none => none

/-- Return the resolved `.choice` value for `name`, or `none` if absent or not `.choice`. -/
def getChoice (cmd : ParsedCmd) (name : String) : Option String :=
  match cmd.lookupValues name with
  | some vals =>
    match vals.getLast? with
    | some (.choice s) => some s
    | _ => none
  | none => none

/-- Return all resolved `OptValue` entries for `name` in order, or `[]` if absent. -/
def getList (cmd : ParsedCmd) (name : String) : List OptValue :=
  (cmd.lookupValues name).getD []

/-- Decode the last `.custom` value for `name` using `parser`, mapping errors to `.invalidValue`. -/
def getCustom {α : Type} (cmd : ParsedCmd) (name : String)
    (parser : String → Except String α) : Except CmdLineError (Option α) :=
  match cmd.lookupValues name with
  | some vals =>
    match vals.getLast? with
    | some (.custom s) =>
      match parser s with
      | .ok v => .ok (some v)
      | .error msg =>
        .error
          { kind := .invalidValue
            message := if msg.isEmpty then s!"invalid custom value for '{name}'" else msg
            target := some name }
    | _ => .ok none
  | none => .ok none

end ParsedCmd

/-- Swappable stdio and environment-variable effect record for `LeanSwe.CmdLine`. -/
structure CliOpsM (m : Type → Type) where
  /-- Read one line from interactive input, returning `none` on EOF. -/
  readLine : m (Option String)
  /-- Write text to standard output. -/
  writeOut : String → m Unit
  /-- Write text to standard error. -/
  writeErr : String → m Unit
  /-- Look up an environment variable, propagating underlying errors as `.ioError`. -/
  getEnv : String → m (Except CmdLineError (Option String))

/-- Concrete `IO` CLI operations bundle. -/
abbrev CliOps := CliOpsM IO

/-- Named custom value validators indexed by `ValueKind.custom` type name. -/
abbrev CustomValidators := List (String × (String → Except String Unit))

/-- Simulated environment variable entry for `CliMockState`. -/
inductive MockEnvValue where
  /-- Environment variable is unset. -/
  | unset
  /-- Environment variable is set to `val`. -/
  | set (val : String)
  /-- Environment lookup fails with `err`. -/
  | error (err : CmdLineError)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Convert a `MockEnvValue` into the `Except CmdLineError (Option String)` returned by `CliOpsM.getEnv`. -/
def MockEnvValue.toExcept : MockEnvValue → Except CmdLineError (Option String)
  | .unset => .ok none
  | .set val => .ok (some val)
  | .error err => .error err

/-- Deterministic in-memory mock state for verifying Layer 2 `CliOpsM (StateM CliMockState)`. -/
structure CliMockState where
  /-- Remaining lines to be returned sequentially by `readLine` (`[]` yields `none`). -/
  stdinLines : List String := []
  /-- Accumulated text written via `writeOut`. -/
  stdout : String := ""
  /-- Accumulated text written via `writeErr`. -/
  stderr : String := ""
  /-- Mock environment table supporting unset, set, and error entries. -/
  env : List (String × MockEnvValue) := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Public operations exported by `LeanSwe.CmdLine`, parameterized over effect monad `m`. -/
structure CmdLineApiM (m : Type → Type) where
  /-- Computable check deciding whether `spec` satisfies `ValidSpec`. -/
  isValidSpec : CommandSpec → Bool
  /-- Purely parse `args` against `spec` with no environment fallback. -/
  parse : CommandSpec → List String → Except CmdLineError ParsedCmd
  /-- Purely parse `args` against `spec` using custom validators and no environment fallback. -/
  parseWith : CommandSpec → List String → CustomValidators → Except CmdLineError ParsedCmd
  /-- Parse `args` against `spec` using `CliOpsM.getEnv` fallback and custom validators. -/
  parseWithEnv : CommandSpec → List String → CustomValidators → m (Except CmdLineError ParsedCmd)
  /-- Render help text for `rootSpec` at the given `subcommandPath`. -/
  renderHelp : CommandSpec → List String → Except CmdLineError String
  /-- Render `<name> <version>\n`. -/
  renderVersion : String → String → String
  /-- Render a `ParsedCmd` back into canonical CLI argument tokens. -/
  renderArgs : CommandSpec → ParsedCmd → Except CmdLineError (List String)
  /-- Prompt for a line of input, trimming ASCII whitespace and optionally applying `default`. -/
  promptLine : String → Option String → m (Except CmdLineError String)
  /-- Prompt repeatedly (up to `maxAttempts`) for `y`/`yes`/`n`/`no` confirmation. -/
  confirm : String → Option Bool → Nat → m (Except CmdLineError Bool)
  /-- Execute a full CLI flow (help/version -> `0`, errors -> `2`, valid -> `handler` code). -/
  runCli : CommandSpec → List String → (ParsedCmd → m UInt32) → m UInt32
  /-- Execute a full CLI flow with custom value validators. -/
  runCliWith : CommandSpec → List String → CustomValidators → (ParsedCmd → m UInt32) → m UInt32

/-- Concrete `IO` CLI API bundle exported by `LeanSwe.CmdLine`. -/
abbrev CmdLineApi := CmdLineApiM IO

end LeanSwe.CmdLine
