import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Model

namespace LeanSwe.CmdLine.Internal

open LeanSwe.CmdLine

/-- Split `s` at the first `'='` character, returning `(before, some after)` or `(s, none)`. -/
def splitFirstEq (s : String) : String × Option String :=
  go [] s.toList
where
  go (revPrefix : List Char) : List Char → String × Option String
    | [] => (s, none)
    | c :: cs =>
      if c == '=' then
        (String.ofList revPrefix.reverse, some (String.ofList cs))
      else
        go (c :: revPrefix) cs

/-- Compute Optimal String Alignment edit distance (with adjacent transpositions) using pure `List Char` DP. -/
def editDistance (a b : String) : Nat :=
  let aChars := a.toList
  let bChars := b.toList
  let initRow := List.range (bChars.length + 1)
  let finalState := aChars.foldl (step bChars) (0, none, initRow, initRow)
  finalState.2.2.2.getLastD 0
where
  nextCells (ca : Char) (prevCa : Option Char) (prevCb : Option Char)
      (prevDiag left ppPrev : Nat) (ppTail : List Nat) : List (Char × Nat) → List Nat
    | [] => []
    | (cb, up) :: rest =>
      let cost := if ca == cb then 0 else 1
      let base := min (min (up + 1) (left + 1)) (prevDiag + cost)
      let cell :=
        match prevCa, prevCb with
        | some pa, some pb =>
          if ca == pb && cb == pa then min base (ppPrev + 1) else base
        | _, _ => base
      let ppHead := ppTail.headD (ppPrev + 1)
      cell :: nextCells ca prevCa (some cb) up cell ppHead (ppTail.drop 1) rest
  step (bChars : List Char) (state : Nat × Option Char × List Nat × List Nat) (ca : Char) :
      Nat × Option Char × List Nat × List Nat :=
    let rowIdx := state.1 + 1
    let prevCa := state.2.1
    let prevPrevRow := state.2.2.1
    let prevRow := state.2.2.2
    let pairs := bChars.zip (prevRow.drop 1)
    let firstPrev := prevRow.headD 0
    let newRow := rowIdx :: nextCells ca prevCa none firstPrev rowIdx 0 prevPrevRow pairs
    (rowIdx, some ca, prevRow, newRow)

/-- Find the closest candidate within `dist ≤ min 2 (max 1 (input.length / 3))`, breaking ties lexicographically. -/
def bestSuggestion (input : String) (candidates : List String) : Option String :=
  let maxDist := min 2 (max 1 (input.length / 3))
  let best := candidates.foldl (fun acc cand =>
    let d := editDistance input cand
    if d ≤ maxDist then
      match acc with
      | none => some (cand, d)
      | some (bestCand, bestDist) =>
        if d < bestDist || (d == bestDist && cand < bestCand) then
          some (cand, d)
        else
          some (bestCand, bestDist)
    else
      acc) none
  best.map (·.1)

/-- Render `<name> <version>\n`. -/
def renderVersion (name version : String) : String :=
  s!"{name} {version}\n"

/-- Render help text for `targetSpec` at `cmdPath` with `visibleOpts` and `effectiveVersion`. -/
def renderHelpNode (cmdPath : List String) (visibleOpts : List OptSpec)
    (effectiveVersion : Option String) (targetSpec : CommandSpec) : String :=
  let fullCmd := String.intercalate " " cmdPath
  let argUsage :=
    if !targetSpec.subcommands.isEmpty then
      " <SUBCOMMAND>"
    else
      String.intercalate "" (targetSpec.args.map fun a =>
        let base := if a.variadic then s!"{a.name}..." else a.name
        if a.required then s!" <{base}>" else s!" [{base}]")
  let usageLine := s!"Usage: {fullCmd} [OPTIONS]{argUsage}"
  let aboutSec :=
    if targetSpec.about.isEmpty then "" else s!"\n\n{targetSpec.about}"
  let subSec :=
    if targetSpec.subcommands.isEmpty then ""
    else
      let lines := targetSpec.subcommands.map fun s =>
        if s.about.isEmpty then s!"  {s.name}" else s!"  {s.name}    {s.about}"
      "\n\nSUBCOMMANDS:\n" ++ String.intercalate "\n" lines
  let argsSec :=
    if targetSpec.args.isEmpty then ""
    else
      let lines := targetSpec.args.map fun a =>
        let tag := if a.variadic then s!"<{a.name}...>" else s!"<{a.name}>"
        if a.help.isEmpty then s!"  {tag}" else s!"  {tag}    {a.help}"
      "\n\nARGS:\n" ++ String.intercalate "\n" lines
  let optLines := visibleOpts.map fun o =>
    let shortStr := match o.short with | some c => s!"-{c}" | none => "  "
    let longStr := match o.long with
      | some l => if o.short.isSome then s!", --{l}" else s!"--{l}"
      | none => ""
    let valStr :=
      if o.kind == .bool then ""
      else
        let vn := o.valueName.getD "VALUE"
        s!" <{vn}>"
    let head := s!"  {shortStr}{longStr}{valStr}"
    if o.help.isEmpty then head else s!"{head}    {o.help}"
  let helpLine :=
    if targetSpec.shortHelp then "  -h, --help    Print help" else "      --help    Print help"
  let verLines :=
    if effectiveVersion.isSome then
      [if targetSpec.shortVersion then "  -V, --version    Print version" else "      --version    Print version"]
    else
      []
  let allOptLines := optLines ++ [helpLine] ++ verLines
  let optsSec := "\n\nOPTIONS:\n" ++ String.intercalate "\n" allOptLines
  usageLine ++ aboutSec ++ subSec ++ argsSec ++ optsSec ++ "\n"

/-- Render help text for `rootSpec` at the given `subcommandPath`. -/
def renderHelp (rootSpec : CommandSpec) (subcommandPath : List String := []) :
    Except CmdLineError String := do
  if !Model.isValidSpec rootSpec then
    .error { kind := .invalidSpec, message := s!"invalid command spec '{rootSpec.name}'" }
  else
    let (globals, effVer, targetSpec) ← Model.findSubcommandPath rootSpec subcommandPath
    .ok (renderHelpNode (rootSpec.name :: subcommandPath) (globals ++ targetSpec.options) effVer targetSpec)

/-- Append a parsed `OptValue` to `cliOpts` under `name`. -/
def recordCliOpt (cliOpts : List (String × List OptValue)) (name : String) (v : OptValue) :
    List (String × List OptValue) :=
  match cliOpts with
  | [] => [(name, [v])]
  | (k, vs) :: rest =>
    if k == name then
      (k, vs ++ [v]) :: rest
    else
      (k, vs) :: recordCliOpt rest name v

/-- Look up a long option or negated boolean `"no-" ++ b` in `visibleOpts`. -/
def lookupLongOpt (visibleOpts : List OptSpec) (namePart : String) :
    Option (OptSpec × Bool) :=
  match visibleOpts.find? (fun o => o.long == some namePart) with
  | some o => some (o, false)
  | none =>
    if Model.startsWithNoDash namePart then
      let base := String.ofList (namePart.toList.drop 3)
      match visibleOpts.find? (fun o => o.kind == .bool && !o.repeatable && o.long == some base) with
      | some o => some (o, true)
      | none => none
    else
      none

/-- Build long-flag typo suggestion candidates for `visibleOpts` and active built-in flags. -/
def longCandidates (visibleOpts : List OptSpec) (effVer : Option String) : List String :=
  let longs := visibleOpts.filterMap (·.long)
  let negs := visibleOpts.filterMap fun o =>
    if o.kind == .bool && !o.repeatable then o.long.map ("no-" ++ ·) else none
  let builtins := "help" :: (if effVer.isSome then ["version"] else [])
  longs ++ negs ++ builtins

/-- Mutable traversal state threaded during left-to-right CLI token parsing. -/
structure ParseState where
  /-- Currently active command or subcommand specification. -/
  curSpec : CommandSpec
  /-- Matched subcommand path relative to root. -/
  subPath : List String := []
  /-- Accumulated global options inherited from ancestors. -/
  inheritedGlobals : List OptSpec := []
  /-- Effective version inherited from ancestors or overridden on `curSpec`. -/
  effectiveVersion : Option String := none
  /-- Whether `--` end-of-options marker has been encountered. -/
  afterDashDash : Bool := false
  /-- Option awaiting its separated value from the next token, if any. -/
  pendingOpt : Option OptSpec := none
  /-- Collected CLI option occurrences keyed by `OptSpec.name`. -/
  cliOpts : List (String × List OptValue) := []
  /-- Collected raw positional arguments in order. -/
  rawPositionals : List String := []

/-- Parse short-option character sequence `cs` left-to-right, returning `(cliOpts, pendingOpt?)`. -/
def parseShortBundle (visibleOpts : List OptSpec) (shortHelp shortVersion : Bool)
    (rootName : String) (subPath : List String) (effVer : Option String)
    (curSpec : CommandSpec) (validators : CustomValidators)
    (cliOpts : List (String × List OptValue)) :
    List Char → Except CmdLineError (List (String × List OptValue) × Option OptSpec)
  | [] => .ok (cliOpts, none)
  | c :: cs =>
    if c == 'h' && shortHelp then
      .error
        { kind := .helpRequested
          message := renderHelpNode (rootName :: subPath) visibleOpts effVer curSpec }
    else if c == 'V' && shortVersion && effVer.isSome then
      match effVer with
      | some v => .error { kind := .versionRequested, message := renderVersion rootName v }
      | none => .error { kind := .unknownOption, message := "unknown option '-V'", target := some "-V" }
    else
      match visibleOpts.find? (fun o => o.short == some c) with
      | none =>
        .error
          { kind := .unknownOption
            message := s!"unknown option '-{c}'"
            target := some s!"-{c}" }
      | some opt =>
        if opt.kind == .bool then
          parseShortBundle visibleOpts shortHelp shortVersion rootName subPath effVer curSpec validators
            (recordCliOpt cliOpts opt.name (.bool true)) cs
        else
          if !cs.isEmpty then do
            let rawVal := String.ofList cs
            let v ← match Model.parseOptValueWith opt.kind rawVal validators with
              | .error e => .error { e with target := some opt.name }
              | .ok v => .ok v
            .ok (recordCliOpt cliOpts opt.name v, none)
          else
            .ok (cliOpts, some opt)

/-- Parse a token list left-to-right via structural recursion, returning the final `ParseState`. -/
def parseTokens (rootName : String) (validators : CustomValidators) (st : ParseState)
    (tokens : List String) : Except CmdLineError ParseState :=
  match tokens with
  | [] =>
    match st.pendingOpt with
    | some opt =>
      .error
        { kind := .missingArgument
          message := s!"option '{opt.name}' requires a value"
          target := some opt.name }
    | none => .ok st
  | tok :: rest =>
    match st.pendingOpt with
    | some opt => do
      let v ← match Model.parseOptValueWith opt.kind tok validators with
        | .error e => .error { e with target := some opt.name }
        | .ok v => .ok v
      parseTokens rootName validators
        { st with pendingOpt := none, cliOpts := recordCliOpt st.cliOpts opt.name v } rest
    | none =>
      if st.afterDashDash then
        parseTokens rootName validators
          { st with rawPositionals := st.rawPositionals ++ [tok] } rest
      else if tok == "--" then
        parseTokens rootName validators { st with afterDashDash := true } rest
      else
        let visibleOpts := st.inheritedGlobals ++ st.curSpec.options
        if tok == "--help" then
          .error
            { kind := .helpRequested
              message := renderHelpNode (rootName :: st.subPath) visibleOpts st.effectiveVersion st.curSpec }
        else if tok == "--version" && st.effectiveVersion.isSome then
          match st.effectiveVersion with
          | some v => .error { kind := .versionRequested, message := renderVersion rootName v }
          | none => .error { kind := .unknownOption, message := "unknown option '--version'", target := some "--version" }
        else
          match tok.toList with
          | '-' :: '-' :: longRest =>
            let (namePart, eqVal?) := splitFirstEq (String.ofList longRest)
            if namePart.isEmpty then
              .error { kind := .unknownOption, message := s!"unknown option '{tok}'", target := some tok }
            else if namePart == "help" || (namePart == "version" && st.effectiveVersion.isSome) then
              .error
                { kind := .invalidValue
                  message := s!"option '--{namePart}' does not take a value"
                  target := some namePart }
            else
              match lookupLongOpt visibleOpts namePart with
              | none =>
                let hint := match bestSuggestion namePart (longCandidates visibleOpts st.effectiveVersion) with
                  | some cand => s!"; did you mean '--{cand}'?"
                  | none => ""
                .error
                  { kind := .unknownOption
                    message := s!"unknown option '--{namePart}'{hint}"
                    target := some namePart }
              | some (opt, isNegated) =>
                if isNegated then
                  match eqVal? with
                  | some _ =>
                    .error
                      { kind := .invalidValue
                        message := s!"option '--{namePart}' does not take a value"
                        target := some opt.name }
                  | none =>
                    parseTokens rootName validators
                      { st with cliOpts := recordCliOpt st.cliOpts opt.name (.bool false) } rest
                else if opt.kind == .bool then
                  match eqVal? with
                  | none =>
                    parseTokens rootName validators
                      { st with cliOpts := recordCliOpt st.cliOpts opt.name (.bool true) } rest
                  | some rawVal =>
                    match Model.parseOptValue .bool rawVal with
                    | .error e => .error { e with target := some opt.name }
                    | .ok (.bool b) =>
                      if opt.repeatable && !b then
                        .error
                          { kind := .invalidValue
                            message := s!"repeatable flag '--{namePart}' cannot be set to false"
                            target := some opt.name }
                      else
                        parseTokens rootName validators
                          { st with cliOpts := recordCliOpt st.cliOpts opt.name (.bool b) } rest
                    | .ok _ => .error { kind := .invalidValue, message := "invalid boolean", target := some opt.name }
                else
                  match eqVal? with
                  | some rawVal => do
                    let v ← match Model.parseOptValueWith opt.kind rawVal validators with
                      | .error e => .error { e with target := some opt.name }
                      | .ok v => .ok v
                    parseTokens rootName validators
                      { st with cliOpts := recordCliOpt st.cliOpts opt.name v } rest
                  | none =>
                    parseTokens rootName validators
                      { st with pendingOpt := some opt } rest
          | '-' :: c :: shortRest => do
            let (nextCliOpts, nextPending) ←
              parseShortBundle visibleOpts st.curSpec.shortHelp st.curSpec.shortVersion
                rootName st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c :: shortRest)
            parseTokens rootName validators
              { st with cliOpts := nextCliOpts, pendingOpt := nextPending } rest
          | _ =>
            if !st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty then
              match st.curSpec.subcommands.find? (fun s => s.name == tok) with
              | some sub =>
                parseTokens rootName validators
                  { curSpec := sub
                    subPath := st.subPath ++ [sub.name]
                    inheritedGlobals := st.inheritedGlobals ++ st.curSpec.options
                    effectiveVersion := sub.version <|> st.effectiveVersion
                    afterDashDash := false
                    pendingOpt := none
                    cliOpts := st.cliOpts
                    rawPositionals := [] } rest
              | none =>
                let hint := match bestSuggestion tok (st.curSpec.subcommands.map (·.name)) with
                  | some cand => s!"; did you mean '{cand}'?"
                  | none => ""
                .error
                  { kind := .unknownSubcommand
                    message := s!"unknown subcommand '{tok}'{hint}"
                    target := some tok }
            else
              parseTokens rootName validators
                { st with rawPositionals := st.rawPositionals ++ [tok] } rest

/-- Parse `args` against `spec` using `ops.getEnv` fallback and `validators`. -/
def parseWithEnvM {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec)
    (args : List String) (validators : CustomValidators := []) :
    m (Except CmdLineError ParsedCmd) := do
  if !Model.isValidSpec spec then
    return .error { kind := .invalidSpec, message := s!"invalid command spec '{spec.name}'" }
  else
    let initState : ParseState :=
      { curSpec := spec
        effectiveVersion := spec.version }
    match parseTokens spec.name validators initState args with
    | .error e => return .error e
    | .ok finalState =>
      if !finalState.curSpec.subcommands.isEmpty then
        if !finalState.rawPositionals.isEmpty then
          let firstPos := finalState.rawPositionals.headD ""
          return .error
            { kind := .unexpectedArgument
              message := s!"unexpected argument '{firstPos}'"
              target := some firstPos }
        else
          return .error
            { kind := .missingArgument
              message := s!"command '{finalState.curSpec.name}' requires a subcommand"
              target := some finalState.curSpec.name }
      else
        let visibleOpts := finalState.inheritedGlobals ++ finalState.curSpec.options
        match ← Model.resolveOptions ops.getEnv visibleOpts finalState.cliOpts validators with
        | .error e => return .error e
        | .ok resolvedOpts =>
          match Model.resolveArgs finalState.curSpec.args finalState.rawPositionals validators with
          | .error e => return .error e
          | .ok resolvedArgs =>
            return .ok
              { subcommandPath := finalState.subPath
                options := resolvedOpts
                args := resolvedArgs
                rawPositionals := finalState.rawPositionals }

/-- Pure `CliOpsM Id` used by `parse` and `parseWith` (no environment fallback). -/
def pureNoEnvOps : CliOpsM Id :=
  { readLine := pure none
    writeOut := fun _ => pure ()
    writeErr := fun _ => pure ()
    getEnv := fun _ => pure (.ok none) }

/-- Purely parse `args` against `spec` using custom `validators` and no environment fallback. -/
def parseWith (spec : CommandSpec) (args : List String) (validators : CustomValidators := []) :
    Except CmdLineError ParsedCmd :=
  parseWithEnvM pureNoEnvOps spec args validators

/-- Purely parse `args` against `spec` with no environment fallback. -/
def parse (spec : CommandSpec) (args : List String) : Except CmdLineError ParsedCmd :=
  parseWith spec args []

/-- Prompt for a line of input via `ops`, trimming ASCII whitespace and applying optional `default` on blank input. -/
def promptLine {m : Type → Type} [Monad m] (ops : CliOpsM m) (prompt : String)
    (default : Option String := none) : m (Except CmdLineError String) := do
  ops.writeOut prompt
  match ← ops.readLine with
  | none => return .error { kind := .eof, message := "unexpected end of input" }
  | some line =>
    let trimmed := Model.trimAscii line
    if trimmed.isEmpty then
      match default with
      | some d => return .ok d
      | none => return .ok ""
    else
      return .ok trimmed

/-- Prompt up to `maxAttempts` times via `ops` for `y`/`yes`/`n`/`no` confirmation (total, zero `partial`). -/
def confirm {m : Type → Type} [Monad m] (ops : CliOpsM m) (prompt : String)
    (default : Option Bool := none) (maxAttempts : Nat := 100) : m (Except CmdLineError Bool) :=
  match maxAttempts with
  | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
  | n + 1 => do
    ops.writeOut prompt
    match ← ops.readLine with
    | none => return .error { kind := .eof, message := "unexpected end of input" }
    | some line =>
      let norm := Model.asciiLower (Model.trimAscii line)
      if norm.isEmpty then
        match default with
        | some b => return .ok b
        | none =>
          match n with
          | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
          | _ + 1 => do
            ops.writeErr "Please answer yes or no.\n"
            confirm ops prompt default n
      else if norm == "y" || norm == "yes" then
        return .ok true
      else if norm == "n" || norm == "no" then
        return .ok false
      else
        match n with
        | 0 => return .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }
        | _ + 1 => do
          ops.writeErr "Please answer yes or no.\n"
          confirm ops prompt default n

/-- Run a CLI command over `ops`, routing help/version to `stdout` (`0`), errors to `stderr` (`2`), and valid runs to `handler`. -/
def runCliWith {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec)
    (args : List String) (validators : CustomValidators) (handler : ParsedCmd → m UInt32) : m UInt32 := do
  match ← parseWithEnvM ops spec args validators with
  | .error e =>
    match e.kind with
    | .helpRequested | .versionRequested =>
      ops.writeOut e.message
      return 0
    | _ =>
      ops.writeErr (e.message ++ "\n")
      return 2
  | .ok parsed => handler parsed

/-- Run a CLI command over `ops` without custom validators. -/
def runCli {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec)
    (args : List String) (handler : ParsedCmd → m UInt32) : m UInt32 :=
  runCliWith ops spec args [] handler

/-- Build `CmdLineApiM m` from a `CliOpsM m` backend with zero `IO` or `@[extern]` dependencies. -/
def mkApiM {m : Type → Type} [Monad m] (ops : CliOpsM m) : CmdLineApiM m :=
  { isValidSpec := Model.isValidSpec
    parse := parse
    parseWith := fun spec args validators => parseWith spec args validators
    parseWithEnv := fun spec args validators => parseWithEnvM ops spec args validators
    renderHelp := fun rootSpec path => renderHelp rootSpec path
    renderVersion := renderVersion
    renderArgs := Model.renderArgs
    promptLine := fun prompt default => promptLine ops prompt default
    confirm := fun prompt default maxAttempts => confirm ops prompt default maxAttempts
    runCli := fun spec args handler => runCli ops spec args handler
    runCliWith := fun spec args validators handler => runCliWith ops spec args validators handler }

/-- Strip trailing `\r` and `\n` characters from a line read via `IO.FS.Stream.getLine`. -/
def stripTrailingNewline (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

end LeanSwe.CmdLine.Internal
