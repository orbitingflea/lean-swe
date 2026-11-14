import LeanSwe.CmdLine.Types

namespace LeanSwe.CmdLine.Model

open LeanSwe.CmdLine

/-- Return `true` iff `c` is an ASCII whitespace character (`' '`, `'\t'`, `'\n'`, `'\r'`). -/
def isAsciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Drop leading ASCII whitespace from a `List Char`. -/
def dropLeadingWhitespace : List Char → List Char
  | [] => []
  | c :: cs => if isAsciiWhitespace c then dropLeadingWhitespace cs else c :: cs

/-- Trim leading and trailing ASCII whitespace from a `List Char`. -/
def trimAsciiChars (cs : List Char) : List Char :=
  (dropLeadingWhitespace (dropLeadingWhitespace cs).reverse).reverse

/-- Trim leading and trailing ASCII whitespace from a `String`. -/
def trimAscii (s : String) : String :=
  String.ofList (trimAsciiChars s.toList)

/-- Lowercase an ASCII uppercase letter `'A'..'Z'`, leaving all other characters unchanged. -/
def asciiLowerChar (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Lowercase all ASCII uppercase letters in a `String`. -/
def asciiLower (s : String) : String :=
  String.ofList (s.toList.map asciiLowerChar)

/-- Return `true` iff every element in `xs` is distinct under `BEq`. -/
def allDistinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && allDistinct xs

/-- Return `true` iff `c` is forbidden in command/option identifiers (`whitespace`, `'='`, NUL). -/
def isForbiddenIdentChar (c : Char) : Bool :=
  isAsciiWhitespace c || c.isWhitespace || c == '=' || c == Char.ofNat 0

/-- Return `true` iff `name` is a valid non-empty command or subcommand name. -/
def isValidCommandName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | '-' :: _ => false
  | cs => cs.all (fun c => !isAsciiWhitespace c && !c.isWhitespace && c != Char.ofNat 0)

/-- Return `true` iff `name` is a valid non-empty canonical option or argument lookup key. -/
def isValidLookupName (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun c => !isAsciiWhitespace c && !c.isWhitespace && c != Char.ofNat 0)

/-- Return `true` iff `l` is a valid long option name (non-empty, no leading `-`, no `=`/whitespace/NUL, not `help`/`version`). -/
def isValidLongName (l : String) : Bool :=
  match l.toList with
  | [] => false
  | '-' :: _ => false
  | cs =>
    cs.all (fun c => !isForbiddenIdentChar c) &&
    l != "help" &&
    l != "version"

/-- Return `true` iff `c` is a valid short option character (not `'-'`, `'='`, whitespace, or NUL). -/
def isValidShortChar (c : Char) : Bool :=
  c != '-' && c != '=' && !isAsciiWhitespace c && !c.isWhitespace && c != Char.ofNat 0

/-- Return `true` iff `key` is a valid POSIX environment variable name (non-empty, no `'='`, no NUL). -/
def isValidEnvKey (key : String) : Bool :=
  !key.isEmpty && key.toList.all (fun c => c != '=' && c != Char.ofNat 0)

/-- Return `true` iff `cs` starts with `"no-"`. -/
def startsWithNoDash (s : String) : Bool :=
  s.toList.take 3 == ['n', 'o', '-']

/-- Return `true` iff `s` starts with `'-'`. -/
def startsWithDash (s : String) : Bool :=
  match s.toList with
  | '-' :: _ => true
  | _ => false

/-- Parse a case-insensitive boolean string (`1`/`true`/`yes`/`on` vs `0`/`false`/`no`/`off`). -/
def parseBoolString (s : String) : Option Bool :=
  match asciiLower s with
  | "1" | "true" | "yes" | "on" => some true
  | "0" | "false" | "no" | "off" => some false
  | _ => none

/-- Parse a non-empty list of ASCII decimal digits `'0'..'9'` into a `Nat`. -/
def parseNatChars (cs : List Char) : Option Nat :=
  if cs.isEmpty then
    none
  else if cs.all (fun c => '0' ≤ c && c ≤ '9') then
    some (cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)
  else
    none

/-- Parse an optional `'-'` followed by non-empty ASCII decimal digits into an `Int`. -/
def parseIntChars (cs : List Char) : Option Int :=
  match cs with
  | '-' :: rest => (parseNatChars rest).map (fun n => -(Int.ofNat n))
  | _ => (parseNatChars cs).map Int.ofNat

/-- Parse a raw string `s` according to `kind` without running external custom validators. -/
def parseOptValue (kind : ValueKind) (s : String) : Except CmdLineError OptValue :=
  match kind with
  | .string => .ok (.string s)
  | .bool =>
    match parseBoolString s with
    | some b => .ok (.bool b)
    | none => .error { kind := .invalidValue, message := s!"invalid boolean value '{s}'" }
  | .nat =>
    match parseNatChars s.toList with
    | some n => .ok (.nat n)
    | none => .error { kind := .invalidValue, message := s!"invalid unsigned integer value '{s}'" }
  | .int =>
    match parseIntChars s.toList with
    | some i => .ok (.int i)
    | none => .error { kind := .invalidValue, message := s!"invalid integer value '{s}'" }
  | .choice opts =>
    if opts.contains s then
      .ok (.choice s)
    else
      .error
        { kind := .invalidValue
          message := s!"invalid choice '{s}'; expected one of: {String.intercalate ", " opts}" }
  | .custom _ => .ok (.custom s)

/-- Run a matching custom validator from `validators` when `kind` is `.custom typeName`. -/
def validateCustomValue (kind : ValueKind) (s : String) (validators : CustomValidators) :
    Except CmdLineError Unit :=
  match kind with
  | .custom typeName =>
    match validators.find? (fun p => p.1 == typeName) with
    | none => .ok ()
    | some (_, check) =>
      match check s with
      | .ok () => .ok ()
      | .error msg =>
        .error
          { kind := .invalidValue
            message := if msg.isEmpty then s!"invalid {typeName} value '{s}'" else msg }
  | _ => .ok ()

/-- Parse a raw string `s` according to `kind` and run any registered custom validator. -/
def parseOptValueWith (kind : ValueKind) (s : String) (validators : CustomValidators := []) :
    Except CmdLineError OptValue := do
  let v ← parseOptValue kind s
  validateCustomValue kind s validators
  pure v

/-- Render an `OptValue` back to its canonical CLI string representation. -/
def optValueToString : OptValue → String
  | .string s => s
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .int i => toString i
  | .choice s => s
  | .custom s => s

/-- Validate a `ValueKind` definition (requiring non-empty, non-`""`, duplicate-free `.choice` lists). -/
def isValidValueKind : ValueKind → Bool
  | .choice opts => !opts.isEmpty && !opts.contains "" && allDistinct opts
  | _ => true

/-- Validate a single `OptSpec` locally (name, flags, kind, default, envVar, required/repeatable rules). -/
def isValidOptLocal (opt : OptSpec) : Bool :=
  isValidLookupName opt.name &&
  (opt.long.isSome || opt.short.isSome) &&
  (match opt.long with
   | none => true
   | some l => isValidLongName l && (if opt.kind == .bool then !startsWithNoDash l else true)) &&
  (match opt.short with
   | none => true
   | some c => isValidShortChar c) &&
  isValidValueKind opt.kind &&
  !(opt.required && opt.default.isSome) &&
  !(opt.repeatable && opt.kind == .bool && opt.default.isSome) &&
  (match opt.default with
   | none => true
   | some d => (parseOptValue opt.kind d).isOk) &&
  (match opt.envVar with
   | none => true
   | some k => isValidEnvKey k)

/-- Validate positional `ArgSpec` ordering (no required after optional/variadic; nothing after variadic). -/
def validArgOrder (seenOptOrVar seenVar : Bool) : List ArgSpec → Bool
  | [] => true
  | a :: rest =>
    if seenVar then false
    else if a.required && seenOptOrVar then false
    else validArgOrder (seenOptOrVar || !a.required || a.variadic) (seenVar || a.variadic) rest

/-- Validate a single `ArgSpec` (name, kind, required/default consistency). -/
def isValidArg (arg : ArgSpec) : Bool :=
  isValidLookupName arg.name &&
  isValidValueKind arg.kind &&
  !(arg.required && arg.default.isSome) &&
  (match arg.default with
   | none => true
   | some d => (parseOptValue arg.kind d).isOk)

/-- Collect all long flag names including auto-generated `"no-" ++ b` for non-repeatable booleans. -/
def collectVisibleLongs (opts : List OptSpec) : List String :=
  opts.foldr (fun opt acc =>
    match opt.long with
    | none => acc
    | some l =>
      if opt.kind == .bool && !opt.repeatable then
        l :: ("no-" ++ l) :: acc
      else
        l :: acc) []

mutual

/-- Check whether `node` and all its subcommands satisfy schema well-formedness under inherited context. -/
def isValidCommandNode (node : CommandSpec) (inheritedGlobals : List OptSpec)
    (inheritedVersion : Option String) : Bool :=
  match node with
  | ⟨name, version, _, shortHelp, shortVersion, options, args, subcommands⟩ =>
    let visibleOpts := inheritedGlobals ++ options
    let effectiveVersion := version <|> inheritedVersion
    let optNames := visibleOpts.map (·.name)
    let argNames := args.map (·.name)
    let shorts := visibleOpts.filterMap (·.short)
    let longs := collectVisibleLongs visibleOpts
    let envKeys := visibleOpts.filterMap (·.envVar)
    let subNames := subcommands.map (·.name)
    isValidCommandName name &&
    options.all isValidOptLocal &&
    allDistinct optNames &&
    allDistinct longs &&
    allDistinct shorts &&
    allDistinct envKeys &&
    (!shortHelp || !shorts.contains 'h') &&
    (!(shortVersion && effectiveVersion.isSome) || !shorts.contains 'V') &&
    args.all isValidArg &&
    allDistinct argNames &&
    argNames.all (fun a => !optNames.contains a) &&
    validArgOrder false false args &&
    (if subcommands.isEmpty then true
     else args.isEmpty && options.all (·.global)) &&
    allDistinct subNames &&
    isValidSubcommandList subcommands visibleOpts effectiveVersion

/-- Check whether every subcommand in `subs` satisfies `isValidCommandNode` under `nextGlobals` and `nextVer`. -/
def isValidSubcommandList (subs : List CommandSpec) (nextGlobals : List OptSpec)
    (nextVer : Option String) : Bool :=
  match subs with
  | [] => true
  | sub :: rest =>
    isValidCommandNode sub nextGlobals nextVer && isValidSubcommandList rest nextGlobals nextVer

end

/-- Computable decision procedure for `ValidSpec`. -/
def isValidSpec (spec : CommandSpec) : Bool :=
  isValidCommandNode spec [] none

/-- Propositional schema well-formedness invariant for `CommandSpec`. -/
def ValidSpec (spec : CommandSpec) : Prop :=
  isValidSpec spec = true

/-- Traverse `subcommandPath` from `spec`, returning `(inheritedGlobals, effectiveVersion, targetSpec)`. -/
def findSubcommandPath (spec : CommandSpec) (path : List String) :
    Except CmdLineError (List OptSpec × Option String × CommandSpec) :=
  go [] none spec path
where
  go (globals : List OptSpec) (ver : Option String) (cur : CommandSpec) :
      List String → Except CmdLineError (List OptSpec × Option String × CommandSpec)
    | [] => .ok (globals, cur.version <|> ver, cur)
    | name :: rest =>
      match cur.subcommands.find? (fun s => s.name == name) with
      | none =>
        .error
          { kind := .unknownSubcommand
            message := s!"unknown subcommand '{name}'"
            target := some name }
      | some sub =>
        go (globals ++ cur.options) (cur.version <|> ver) sub rest

/-- Resolve the default fallback for a single `OptSpec` when neither CLI nor env supplied a value. -/
def resolveOptDefault (opt : OptSpec) (validators : CustomValidators) :
    Except CmdLineError (Option (List OptValue)) :=
  match opt.default with
  | some d =>
    match parseOptValueWith opt.kind d validators with
    | .error e => .error { e with target := some opt.name }
    | .ok v => .ok (some [v])
  | none =>
    if opt.required then
      .error
        { kind := .missingOption
          message := s!"missing required option '{opt.name}'"
          target := some opt.name }
    else if opt.kind == .bool && !opt.repeatable then
      .ok (some [.bool false])
    else
      .ok none

/-- Resolve one `OptSpec` under `CLI > env > default` precedence. -/
def resolveSingleOption {m : Type → Type} [Monad m]
    (getEnv : String → m (Except CmdLineError (Option String)))
    (opt : OptSpec) (cliVals : List OptValue) (validators : CustomValidators := []) :
    m (Except CmdLineError (Option (List OptValue))) := do
  if !cliVals.isEmpty then
    if !opt.repeatable && cliVals.length > 1 then
      return .error
        { kind := .invalidValue
          message := s!"option '{opt.name}' cannot be specified multiple times"
          target := some opt.name }
    else
      return .ok (some cliVals)
  else
    match opt.envVar with
    | none => return resolveOptDefault opt validators
    | some envKey =>
      match ← getEnv envKey with
      | .error e => return .error e
      | .ok none => return resolveOptDefault opt validators
      | .ok (some "") => return resolveOptDefault opt validators
      | .ok (some s) =>
        match parseOptValueWith opt.kind s validators with
        | .error e => return .error { e with target := some opt.name }
        | .ok v =>
          if opt.repeatable && opt.kind == .bool && v == .bool false then
            return .ok none
          else
            return .ok (some [v])

/-- Resolve the full visible option list `visibleOpts` in declaration order. -/
def resolveOptions {m : Type → Type} [Monad m]
    (getEnv : String → m (Except CmdLineError (Option String)))
    (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue))
    (validators : CustomValidators := []) :
    m (Except CmdLineError (List (String × List OptValue))) := do
  match visibleOpts with
  | [] => return .ok []
  | opt :: rest =>
    let cliVals :=
      match cliOpts.find? (fun p => p.1 == opt.name) with
      | some p => p.2
      | none => []
    match ← resolveSingleOption getEnv opt cliVals validators with
    | .error e => return .error e
    | .ok resolved? =>
      match ← resolveOptions getEnv rest cliOpts validators with
      | .error e => return .error e
      | .ok tail =>
        match resolved? with
        | none => return .ok tail
        | some vals => return .ok ((opt.name, vals) :: tail)

/-- Resolve positional argument specifications left-to-right against `rawPos`. -/
def resolveArgs (argSpecs : List ArgSpec) (rawPos : List String)
    (validators : CustomValidators := []) :
    Except CmdLineError (List (String × List OptValue)) :=
  go argSpecs rawPos
where
  parseMany (arg : ArgSpec) : List String → Except CmdLineError (List OptValue)
    | [] => .ok []
    | s :: ss => do
      let v ← match parseOptValueWith arg.kind s validators with
        | .error e => .error { e with target := some arg.name }
        | .ok v => .ok v
      let vs ← parseMany arg ss
      .ok (v :: vs)
  go : List ArgSpec → List String → Except CmdLineError (List (String × List OptValue))
    | [], [] => .ok []
    | [], extra :: _ =>
      .error
        { kind := .unexpectedArgument
          message := s!"unexpected argument '{extra}'"
          target := some extra }
    | arg :: restArgs, pos =>
      if arg.variadic then do
        if pos.isEmpty then
          if arg.required then
            .error
              { kind := .missingArgument
                message := s!"missing required argument '{arg.name}'"
                target := some arg.name }
          else
            match arg.default with
            | some d => do
              let v ← match parseOptValueWith arg.kind d validators with
                | .error e => .error { e with target := some arg.name }
                | .ok v => .ok v
              let tail ← go restArgs []
              .ok ((arg.name, [v]) :: tail)
            | none => go restArgs []
        else do
          let vs ← parseMany arg pos
          let tail ← go restArgs []
          .ok ((arg.name, vs) :: tail)
      else
        match pos with
        | s :: remPos => do
          let v ← match parseOptValueWith arg.kind s validators with
            | .error e => .error { e with target := some arg.name }
            | .ok v => .ok v
          let tail ← go restArgs remPos
          .ok ((arg.name, [v]) :: tail)
        | [] =>
          if arg.required then
            .error
              { kind := .missingArgument
                message := s!"missing required argument '{arg.name}'"
                target := some arg.name }
          else
            match arg.default with
            | some d => do
              let v ← match parseOptValueWith arg.kind d validators with
                | .error e => .error { e with target := some arg.name }
                | .ok v => .ok v
              let tail ← go restArgs []
              .ok ((arg.name, [v]) :: tail)
            | none => go restArgs []

/-- Render a single `OptSpec` and its resolved values into CLI tokens. -/
def renderSingleOpt (opt : OptSpec) (vals : List OptValue) : Except CmdLineError (List String) :=
  if vals.isEmpty then
    .ok []
  else if opt.kind == .bool && !opt.repeatable then
    match vals with
    | [.bool true] =>
      match opt.long with
      | some l => .ok ["--" ++ l]
      | none =>
        match opt.short with
        | some c => .ok ["-" ++ String.singleton c]
        | none => .error { kind := .invalidSpec, message := s!"option '{opt.name}' has neither long nor short flag" }
    | [.bool false] =>
      match opt.long with
      | some l => .ok ["--no-" ++ l]
      | none =>
        let defaultIsTrue :=
          match opt.default with
          | some d => parseBoolString d == some true
          | none => false
        if defaultIsTrue then
          .error
            { kind := .invalidValue
              message := s!"cannot render false value for short-only boolean option '{opt.name}' with true default"
              target := some opt.name }
        else
          .ok []
    | _ =>
      .error
        { kind := .invalidValue
          message := s!"invalid boolean value list for option '{opt.name}'"
          target := some opt.name }
  else
    renderValueList opt vals
where
  renderValueList (opt : OptSpec) : List OptValue → Except CmdLineError (List String)
    | [] => .ok []
    | v :: vs => do
      if opt.kind == .bool && v != .bool true then
        .error
          { kind := .invalidValue
            message := s!"repeatable boolean option '{opt.name}' cannot render false value"
            target := some opt.name }
      else
        let toks ←
          match opt.long with
          | some l =>
            if opt.kind == .bool then
              .ok ["--" ++ l]
            else
              .ok ["--" ++ l ++ "=" ++ optValueToString v]
          | none =>
            match opt.short with
            | some c =>
              if opt.kind == .bool then
                .ok ["-" ++ String.singleton c]
              else
                .ok ["-" ++ String.singleton c, optValueToString v]
            | none =>
              .error { kind := .invalidSpec, message := s!"option '{opt.name}' has neither long nor short flag" }
        let rest ← renderValueList opt vs
        .ok (toks ++ rest)

/-- Render a `ParsedCmd` back into canonical CLI argument tokens suitable for round-trip parsing. -/
def renderArgs (spec : CommandSpec) (parsed : ParsedCmd) : Except CmdLineError (List String) := do
  if !isValidSpec spec then
    .error { kind := .invalidSpec, message := s!"invalid command spec '{spec.name}'" }
  else
    let (globals, _, targetSpec) ← findSubcommandPath spec parsed.subcommandPath
    if !targetSpec.subcommands.isEmpty then
      .error
        { kind := .missingArgument
          message := s!"command '{targetSpec.name}' requires a subcommand"
          target := some targetSpec.name }
    else
      let visibleOpts := globals ++ targetSpec.options
      let optTokens ← renderOpts visibleOpts
      let posTokens :=
        if parsed.rawPositionals.any startsWithDash then
          "--" :: parsed.rawPositionals
        else
          parsed.rawPositionals
      .ok (parsed.subcommandPath ++ optTokens ++ posTokens)
where
  renderOpts : List OptSpec → Except CmdLineError (List String)
    | [] => .ok []
    | opt :: rest =>
      let vals :=
        match parsed.options.find? (fun p => p.1 == opt.name) with
        | some p => p.2
        | none => []
      do
        let headToks ← renderSingleOpt opt vals
        let tailToks ← renderOpts rest
        .ok (headToks ++ tailToks)

end LeanSwe.CmdLine.Model
