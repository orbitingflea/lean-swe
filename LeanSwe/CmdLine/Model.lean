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

/-- Check whether byte `b` is a UTF-8 continuation byte (`0x80..0xBF`). -/
def isUtf8ContinuationByte (b : UInt8) : Bool :=
  0x80 ≤ b && b ≤ 0xBF

/-- Pure model of Lean 4's `validate_utf8_one`: returns `some (cp, width)` iff a valid UTF-8
    codepoint starts at byte offset `i` in `bs`. -/
def validateUtf8OneWidth (bs : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if _ : i < bs.size then
    let b0 := bs[i]
    if b0 < 0x80 then
      some (b0.toNat, 1)
    else if 0xC2 ≤ b0 && b0 ≤ 0xDF then
      if _ : i + 1 < bs.size then
        let b1 := bs[i + 1]
        if isUtf8ContinuationByte b1 then
          some (((b0.toNat &&& 0x1F) <<< 6) ||| (b1.toNat &&& 0x3F), 2)
        else none
      else none
    else if 0xE0 ≤ b0 && b0 ≤ 0xEF then
      if _ : i + 2 < bs.size then
        let b1 := bs[i + 1]
        let b2 := bs[i + 2]
        let b1Ok :=
          if b0 == 0xE0 then 0xA0 ≤ b1 && b1 ≤ 0xBF
          else if b0 == 0xED then 0x80 ≤ b1 && b1 ≤ 0x9F
          else isUtf8ContinuationByte b1
        if b1Ok && isUtf8ContinuationByte b2 then
          let cp := ((b0.toNat &&& 0x0F) <<< 12) ||| ((b1.toNat &&& 0x3F) <<< 6) ||| (b2.toNat &&& 0x3F)
          some (cp, 3)
        else none
      else none
    else if 0xF0 ≤ b0 && b0 ≤ 0xF4 then
      if _ : i + 3 < bs.size then
        let b1 := bs[i + 1]
        let b2 := bs[i + 2]
        let b3 := bs[i + 3]
        let b1Ok :=
          if b0 == 0xF0 then 0x90 ≤ b1 && b1 ≤ 0xBF
          else if b0 == 0xF4 then 0x80 ≤ b1 && b1 ≤ 0x8F
          else isUtf8ContinuationByte b1
        if b1Ok && isUtf8ContinuationByte b2 && isUtf8ContinuationByte b3 then
          let cp := ((b0.toNat &&& 0x07) <<< 18) ||| ((b1.toNat &&& 0x3F) <<< 12) |||
            ((b2.toNat &&& 0x3F) <<< 6) ||| (b3.toNat &&& 0x3F)
          some (cp, 4)
        else none
      else none
    else none
  else none

/-- Advance `i` past all contiguous UTF-8 continuation bytes (`0x80..0xBF`), matching
    Lean 4 `lean_mk_string_lossy_recover`. -/
def skipUtf8ContinuationBytes (bs : ByteArray) (i : Nat) : Nat :=
  go bs i (bs.size - i)
where
  go (bs : ByteArray) (pos : Nat) : Nat → Nat
    | 0 => pos
    | fuel + 1 =>
      if _ : pos < bs.size then
        if isUtf8ContinuationByte bs[pos] then go bs (pos + 1) fuel else pos
      else pos

/-- Pure bit-for-bit model of Lean 4's `lean_mk_string_from_bytes` / `lean_mk_string_lossy_recover`.
    Preserves embedded NUL (`0x00`); replaces each invalid sequence plus all contiguous
    continuation bytes `0x80..0xBF` with a single `U+FFFD`. -/
def decodeUtf8LossyLean (bs : ByteArray) : String :=
  String.ofList (go 0 bs.size []).reverse
where
  go (pos : Nat) (fuel : Nat) (accRev : List Char) : List Char :=
    match fuel with
    | 0 => accRev
    | fuel' + 1 =>
      if pos >= bs.size then accRev
      else
        match validateUtf8OneWidth bs pos with
        | some (cp, w) => go (pos + w) fuel' (Char.ofNat cp :: accRev)
        | none =>
          let nextPos := skipUtf8ContinuationBytes bs (pos + 1)
          go nextPos fuel' (Char.ofNat 0xFFFD :: accRev)

/-- Strict UTF-8 decoder returning `none` on any invalid sequence. -/
def decodeUtf8Strict? (bs : ByteArray) : Option String :=
  (go 0 bs.size []).map (fun rev => String.ofList rev.reverse)
where
  go (pos : Nat) (fuel : Nat) (accRev : List Char) : Option (List Char) :=
    match fuel with
    | 0 => if pos >= bs.size then some accRev else none
    | fuel' + 1 =>
      if pos >= bs.size then some accRev
      else
        match validateUtf8OneWidth bs pos with
        | some (cp, w) => go (pos + w) fuel' (Char.ofNat cp :: accRev)
        | none => none

/-- Pure model of `Internal.stripTrailingNewline`: drop all trailing `'\n'` and `'\r'` chars. -/
def stripTrailingNewlineModel (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

/-- Bounded retry count (`64`) on transient `EINTR` (errno `4`) for single `read(2)` / `write(2)` calls
    (shared with `SysBridge.stdioEintrFuel`). Up to `64` consecutive `EINTR` deliveries are retried
    transparently while preserving accumulated bytes; exceeding this budget propagates `.interrupted`. -/
def stdioEintrRetryLimit : Nat := 64

/-- Pending signal interruption pattern (without `SA_RESTART`) attached to a `StdioChannelState`. -/
inductive PendingInterrupt where
  /-- No pending signal interruption. -/
  | none
  /-- Finite burst of `count` consecutive `EINTR` deliveries (`count ≤ stdioEintrRetryLimit` retries absorb it). -/
  | transient (count : Nat)
  /-- Repeating periodic `EINTR` delivery stream (exhausts all `stdioEintrRetryLimit` retries and throws `.interrupted`). -/
  | repeating
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Return `true` iff `p` exhausts the `stdioEintrRetryLimit` (`64`) retry budget on a blocking syscall. -/
def PendingInterrupt.exhaustsRetries : PendingInterrupt → Bool
  | .none => false
  | .transient count => count > stdioEintrRetryLimit
  | .repeating => true

/-- Physical OS descriptor backing for `stdin`/`stdout`/`stderr`. -/
inductive FdBacking where
  /-- Pipe or FIFO with queued raw byte chunks, EOF/writer-closed status, and `O_NONBLOCK` flag. -/
  | pipe (pending : ByteArray := ByteArray.empty) (writersClosed : Bool := true)
      (nonblock : Bool := false) (readersClosed : Bool := false) (capacity : Nat := 65536)
  /-- Seekable regular file (`memfd` / tmpfile) with optional `RLIMIT_FSIZE` cap. -/
  | regFile (bytes : ByteArray := ByteArray.empty) (pos : Nat := 0) (fsizeLimit? : Option Nat := none)
  /-- `/dev/null`: immediate EOF on read, discards all writes. -/
  | nullDev
  /-- `/dev/full`: reads NUL bytes; writes fail `ENOSPC` (`28`). -/
  | fullDev
  /-- Directory fd (`O_DIRECTORY`): reads fail `EISDIR` (`21`). -/
  | dirFd
  /-- Wrong open access mode (`O_WRONLY` on `stdin` or `O_RDONLY` on `stdout`/`stderr`): `EBADF` (`9`). -/
  | wrongMode
  /-- Closed fd (`close(0/1/2)` in-process): `EBADF` (`9`). -/
  | closedFd
  /-- Canonical PTY slave (`openpty`): queued `read(0)` chunks (`some bs` or `none` for `^D`), `masterOpen`, and buffered partial line before `\n`/`^D`. -/
  | ptySlave (segments : List (Option ByteArray) := []) (masterOpen : Bool := true)
      (pendingLine : ByteArray := ByteArray.empty)
  /-- Hung-up PTY master whose slave fd is closed (`EIO` `5` on read; small writes up to `4096` bytes succeed, larger writes block). -/
  | ptyHungup (written : Nat := 0)
  deriving BEq, DecidableEq, Inhabited

/-- Stateful channel model for one of `stdin` (`0`), `stdout` (`1`), or `stderr` (`2`). -/
structure StdioChannelState where
  /-- Kernel descriptor backing attached to this stdio slot. -/
  backing : FdBacking := .nullDev
  /-- Pending injected `EINTR` signal pattern (without `SA_RESTART`). -/
  pendingInterrupt : PendingInterrupt := .none
  /-- Accumulated bytes actually written to the kernel sink. -/
  writtenBytes : ByteArray := ByteArray.empty
  /-- Whether `SIGXFSZ` is ignored (`SIG_IGN`) rather than terminating with `SIG_DFL` on `RLIMIT_FSIZE`. -/
  sigxfszIgnored : Bool := false
  deriving BEq, DecidableEq, Inhabited

/-- Pure OS-world state for modeling all impure `LeanSwe.CmdLine` entry points. -/
structure StdioWorld where
  /-- Standard input (`fd 0`). -/
  stdin : StdioChannelState := {}
  /-- Standard output (`fd 1`). -/
  stdout : StdioChannelState := { backing := .pipe ByteArray.empty false false false 65536 }
  /-- Standard error (`fd 2`). -/
  stderr : StdioChannelState := { backing := .pipe ByteArray.empty false false false 65536 }
  /-- Raw POSIX `environ` entries (`KEY=VAL` byte arrays, preserving duplicates and invalid UTF-8). -/
  rawEnviron : List ByteArray := []
  /-- Whether `SIGPIPE` is ignored/shielded (`true` under `LinuxSyscall.Files.write`). -/
  sigpipeIgnored : Bool := true
  /-- Last kernel `errno` observed from a failing `IO` step (`0` initially). -/
  lastErrno : UInt32 := 0
  deriving BEq, DecidableEq, Inhabited

/-- Typed errno categories observable across the `CmdLine` `IO` boundary. -/
inductive StdioErrClass where
  /-- `EINTR` (`4`). -/
  | interrupted
  /-- `EIO` (`5`, PTY master hangup). -/
  | hardwareFault
  /-- `EBADF` (`9`: closed fd or wrong `O_RDONLY`/`O_WRONLY` mode). -/
  | badFd
  /-- `EAGAIN` / `EWOULDBLOCK` (`11`: `O_NONBLOCK` empty read pipe or full write pipe). -/
  | wouldBlock
  /-- `EISDIR` (`21`: directory fd on `stdin`). -/
  | isDirectory
  /-- `EFBIG` (`27`: `RLIMIT_FSIZE` exceeded). -/
  | fileTooLarge
  /-- `ENOSPC` (`28`: `/dev/full` or full tmpfs). -/
  | noSpace
  /-- `EPIPE` (`32`: broken pipe with `SIGPIPE` shielded). -/
  | brokenPipe
  /-- Blocking operation in single-threaded state (open empty pipe/PTY or `/dev/full` stream read). -/
  | blocked
  /-- Process terminated by an uncaught signal (e.g., `SIGXFSZ` `25` on `RLIMIT_FSIZE`). -/
  | terminatedBySignal (sig : UInt8)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Map `StdioErrClass` to its Linux `errno` code (`0` if not an `errno`-backed failure). -/
def stdioErrClassToErrno : StdioErrClass → UInt32
  | .interrupted => 4
  | .hardwareFault => 5
  | .badFd => 9
  | .wouldBlock => 11
  | .isDirectory => 21
  | .fileTooLarge => 27
  | .noSpace => 28
  | .brokenPipe => 32
  | _ => 0

/-- Outcome of an `IO` step, explicitly separating normal return values from uncaught `IO.Error` throws. -/
inductive IoStepOutcome (α : Type) where
  /-- Action completed normally and returned `val`. -/
  | returned (val : α)
  /-- Action threw an uncaught `IO.Error` belonging to `errClass`. -/
  | threwIo (errClass : StdioErrClass)
  deriving Repr, BEq, DecidableEq

/-- Look up the first `KEY=VAL` entry in `rawEnviron` matching `key` (pure POSIX `getenv(3)` semantics),
    validating `key` (`isValidEnvKey`) and decoding the value strictly as UTF-8. -/
def stepDefaultGetEnv (w : StdioWorld) (key : String) : Except CmdLineError (Option String) :=
  if !isValidEnvKey key then
    .error { kind := .ioError, message := "invalid environment variable name", target := some key }
  else
    let keyBytes := key.toUTF8
    match findEntry w.rawEnviron keyBytes with
    | none => .ok none
    | some valBytes =>
      match decodeUtf8Strict? valBytes with
      | some s => .ok (some s)
      | none => .error { kind := .ioError, message := "invalid UTF-8 in environment value", target := some key }
where
  hasPrefixEq (entry keyBytes : ByteArray) : Bool :=
    entry.size > keyBytes.size &&
    entry[keyBytes.size]! == 0x3D &&
    (List.range keyBytes.size).all (fun i => entry[i]! == keyBytes[i]!)
  findEntry : List ByteArray → ByteArray → Option ByteArray
    | [], _ => none
    | e :: es, kb =>
      if hasPrefixEq e kb then
        some (e.extract (kb.size + 1) e.size)
      else
        findEntry es kb

/-- Split `bs` at the first newline byte `0x0A`, returning `(lineWithLf, rest)` if found. -/
def splitLineBytes (bs : ByteArray) : Option (ByteArray × ByteArray) :=
  go 0 bs.size
where
  go (pos : Nat) : Nat → Option (ByteArray × ByteArray)
    | 0 => none
    | fuel + 1 =>
      if _ : pos < bs.size then
        if bs[pos] == 0x0A then
          some (bs.extract 0 (pos + 1), bs.extract (pos + 1) bs.size)
        else
          go (pos + 1) fuel
      else
        none

/-- Canonical Linux `n_tty` (`ICANON | ICRNL`) input feeder: translates `0x0D` to `0x0A`,
    splits completed lines, and flushes `partialLine` or emits `none` on `^D` (`0x04`). -/
def ptyFeedBytes (segments : List (Option ByteArray)) (pendingLine : ByteArray) (bs : ByteArray) :
    List (Option ByteArray) × ByteArray :=
  let (addedRev, rem) := go 0 bs.size [] pendingLine
  (segments ++ addedRev.reverse, rem)
where
  go (i fuel : Nat) (accRev : List (Option ByteArray)) (cur : ByteArray) :
      List (Option ByteArray) × ByteArray :=
    match fuel with
    | 0 => (accRev, cur)
    | fuel' + 1 =>
      if _ : i < bs.size then
        let b := bs[i]
        let b' := if b == 0x0D then 0x0A else b
        if b' == 0x0A then
          go (i + 1) fuel' (some (cur.push 0x0A) :: accRev) ByteArray.empty
        else if b' == 0x04 then
          if cur.isEmpty then
            go (i + 1) fuel' (none :: accRev) ByteArray.empty
          else
            go (i + 1) fuel' (some cur :: accRev) ByteArray.empty
        else
          go (i + 1) fuel' accRev (cur.push b')
      else
        (accRev, cur)

/-- Consume canonical PTY slave segments, splitting on interior `0x0A` and stopping on `none` (`^D`). -/
def consumePtySegments (acc : ByteArray) :
    List (Option ByteArray) → Option (ByteArray × List (Option ByteArray))
  | [] => none
  | none :: rest => some (acc, rest)
  | some chunk :: rest =>
    let combined := acc ++ chunk
    match splitLineBytes combined with
    | some (lineBs, rem) =>
      let rest' := if rem.isEmpty then rest else some rem :: rest
      some (lineBs, rest')
    | none =>
      consumePtySegments combined rest

/-- Update `w.lastErrno` when an `IO` step throws a kernel `errno`-backed error. -/
def updateWorldErrno {α : Type} (w : StdioWorld) (out : IoStepOutcome α) : StdioWorld :=
  match out with
  | .returned _ => w
  | .threwIo err =>
    let code := stdioErrClassToErrno err
    if code != 0 then { w with lastErrno := code } else w

/-- Pure transition of reading one raw line from `stdin` on `StdioWorld` via unbuffered `LinuxSyscall.Files`.
    On a blocking open pipe or PTY, transient `EINTR` bursts with `count ≤ stdioEintrRetryLimit` (`64`) are
    absorbed; `repeating` or `transient count` with `count > stdioEintrRetryLimit` throws `.interrupted`.
    This abstract model omits the live 64 MiB line-length cap (`EFBIG` in `SysBridge.readStdioLineM`) and
    `dupStdio` file-descriptor exhaustion (`EMFILE`). -/
def stepRawGetLine (w : StdioWorld) : IoStepOutcome String × StdioWorld :=
  let ch := w.stdin
  match ch.backing with
  | .closedFd | .wrongMode =>
    (.threwIo .badFd, { w with lastErrno := 9 })
  | .dirFd =>
    (.threwIo .isDirectory, { w with lastErrno := 21 })
  | .nullDev =>
    (.returned "", w)
  | .fullDev =>
    (.threwIo .blocked, w)
  | .regFile bytes pos fsizeLimit? =>
    let avail := bytes.extract pos bytes.size
    let (lineBs, newPos) :=
      match splitLineBytes avail with
      | some (l, _) => (l, pos + l.size)
      | none => (avail, max pos bytes.size)
    let ch' := { ch with backing := .regFile bytes newPos fsizeLimit? }
    (.returned (decodeUtf8LossyLean lineBs), { w with stdin := ch' })
  | .pipe pending writersClosed nonblock readersClosed cap =>
    match splitLineBytes pending with
    | some (lineBs, rest) =>
      let ch' := { ch with backing := .pipe rest writersClosed nonblock readersClosed cap }
      (.returned (decodeUtf8LossyLean lineBs), { w with stdin := ch' })
    | none =>
      if writersClosed then
        let ch' := { ch with backing := .pipe ByteArray.empty true nonblock readersClosed cap }
        (.returned (decodeUtf8LossyLean pending), { w with stdin := ch' })
      else if nonblock then
        let ch' := { ch with backing := .pipe ByteArray.empty false true readersClosed cap }
        (.threwIo .wouldBlock, { w with stdin := ch', lastErrno := 11 })
      else if ch.pendingInterrupt.exhaustsRetries then
        let ch' := { ch with backing := .pipe ByteArray.empty false false readersClosed cap, pendingInterrupt := .none }
        (.threwIo .interrupted, { w with stdin := ch', lastErrno := 4 })
      else
        (.threwIo .blocked, { w with stdin := { ch with pendingInterrupt := .none } })
  | .ptySlave segs masterOpen pendingLine =>
    if !masterOpen then
      let ch' := { ch with backing := .ptySlave [] false ByteArray.empty }
      (.returned "", { w with stdin := ch' })
    else
      match consumePtySegments ByteArray.empty segs with
      | some (lineBs, rest) =>
        let ch' := { ch with backing := .ptySlave rest true pendingLine }
        (.returned (decodeUtf8LossyLean lineBs), { w with stdin := ch' })
      | none =>
        if ch.pendingInterrupt.exhaustsRetries then
          let ch' := { ch with backing := .ptySlave [] true pendingLine, pendingInterrupt := .none }
          (.threwIo .interrupted, { w with stdin := ch', lastErrno := 4 })
        else
          (.threwIo .blocked, { w with stdin := { ch with pendingInterrupt := .none } })
  | .ptyHungup _ =>
    (.threwIo .hardwareFault, { w with lastErrno := 5 })

/-- Pure transition of `defaultOps.readLine` on `StdioWorld`. -/
def stepDefaultReadLine (w : StdioWorld) : IoStepOutcome (Option String) × StdioWorld :=
  match stepRawGetLine w with
  | (.threwIo e, w') => (.threwIo e, w')
  | (.returned line, w') =>
    if line.isEmpty then
      (.returned none, w')
    else
      (.returned (some (stripTrailingNewlineModel line)), w')

/-- Valid kernel partial-write bound for an `O_NONBLOCK` pipe. -/
def isValidNonblockPipeWriteBytes (avail bsSize actualWritten : Nat) : Bool :=
  actualWritten ≤ min avail bsSize

/-- Write `chunk` into regular-file `bytes` at `pos`, zero-filling `[bytes.size .. pos)` when `pos > bytes.size`. -/
def writeAtRegFileOffset (bytes : ByteArray) (pos : Nat) (chunk : ByteArray) : ByteArray :=
  if chunk.isEmpty then bytes
  else if pos > bytes.size then
    bytes ++ ByteArray.mk (Array.replicate (pos - bytes.size) 0) ++ chunk
  else if pos == bytes.size then
    bytes ++ chunk
  else
    bytes.extract 0 pos ++ chunk ++ bytes.extract (min (pos + chunk.size) bytes.size) bytes.size

/-- Pure transition of unbuffered `LinuxSyscall.Files` write on a `StdioChannelState`.
    On a blocking full pipe or hung-up PTY write, transient `EINTR` bursts with `count ≤ stdioEintrRetryLimit` (`64`)
    are absorbed; `repeating` or `transient count` with `count > stdioEintrRetryLimit` throws `.interrupted`. -/
def stepChannelWrite (ch : StdioChannelState) (text : String) : IoStepOutcome Unit × StdioChannelState :=
  if text.isEmpty then
    (.returned (), ch)
  else
    let bs := text.toUTF8
    match ch.backing with
    | .closedFd | .wrongMode | .dirFd => (.threwIo .badFd, ch)
    | .fullDev =>
      (.threwIo .noSpace, ch)
    | .nullDev => (.returned (), ch)
    | .pipe pending writersClosed nonblock readersClosed cap =>
      if bs.isEmpty then
        (.returned (), ch)
      else if readersClosed then
        (.threwIo .brokenPipe, ch)
      else if pending.size + bs.size > cap then
        if nonblock then
          let avail := if cap > pending.size then cap - pending.size else 0
          let partialBs := bs.extract 0 (min avail bs.size)
          let ch' :=
            { ch with
              backing := .pipe (pending ++ partialBs) writersClosed nonblock readersClosed cap
              writtenBytes := ch.writtenBytes ++ partialBs
              pendingInterrupt := .none }
          (.threwIo .wouldBlock, ch')
        else if ch.pendingInterrupt.exhaustsRetries then
          (.threwIo .interrupted, { ch with pendingInterrupt := .none })
        else
          (.threwIo .blocked, { ch with pendingInterrupt := .none })
      else
        let ch' :=
          { ch with
            backing := .pipe (pending ++ bs) writersClosed nonblock readersClosed cap
            writtenBytes := ch.writtenBytes ++ bs
            pendingInterrupt := .none }
        (.returned (), ch')
    | .regFile bytes pos fsizeLimit? =>
      if bs.isEmpty then
        (.returned (), ch)
      else
        let avail? : Option Nat :=
          match fsizeLimit? with
          | some lim => if pos + bs.size > lim then some (if lim > pos then lim - pos else 0) else none
          | none => none
        match avail? with
        | some avail =>
          let partialBs := bs.extract 0 (min avail bs.size)
          let newBytes := writeAtRegFileOffset bytes pos partialBs
          let ch' :=
            { ch with
              backing := .regFile newBytes (pos + partialBs.size) fsizeLimit?
              writtenBytes := ch.writtenBytes ++ partialBs }
          let err := if ch.sigxfszIgnored then StdioErrClass.fileTooLarge else StdioErrClass.terminatedBySignal 25
          (.threwIo err, ch')
        | none =>
          let newBytes := writeAtRegFileOffset bytes pos bs
          let ch' :=
            { ch with
              backing := .regFile newBytes (pos + bs.size) fsizeLimit?
              writtenBytes := ch.writtenBytes ++ bs }
          (.returned (), ch')
    | .ptySlave segs masterOpen pendingLine =>
      if !masterOpen then
        (.threwIo .hardwareFault, ch)
      else if bs.isEmpty then
        (.returned (), ch)
      else
        let ch' :=
          { ch with
            backing := .ptySlave segs true pendingLine
            writtenBytes := ch.writtenBytes ++ bs
            pendingInterrupt := .none }
        (.returned (), ch')
    | .ptyHungup written =>
      if written + bs.size > 4096 then
        if ch.pendingInterrupt.exhaustsRetries then
          (.threwIo .interrupted, { ch with pendingInterrupt := .none })
        else
          (.threwIo .blocked, { ch with pendingInterrupt := .none })
      else
        let ch' :=
          { ch with
            backing := .ptyHungup (written + bs.size)
            writtenBytes := ch.writtenBytes ++ bs
            pendingInterrupt := .none }
        (.returned (), ch')

/-- Pure transition of `defaultOps.writeOut` on `StdioWorld`. -/
def stepDefaultWriteOut (w : StdioWorld) (text : String) : IoStepOutcome Unit × StdioWorld :=
  let (out0, ch') := stepChannelWrite w.stdout text
  let out :=
    if out0 == .threwIo .brokenPipe && !w.sigpipeIgnored then
      .threwIo (.terminatedBySignal 13)
    else
      out0
  (out, updateWorldErrno { w with stdout := ch' } out)

/-- Pure transition of `defaultOps.writeErr` on `StdioWorld`. -/
def stepDefaultWriteErr (w : StdioWorld) (text : String) : IoStepOutcome Unit × StdioWorld :=
  let (out0, ch') := stepChannelWrite w.stderr text
  let out :=
    if out0 == .threwIo .brokenPipe && !w.sigpipeIgnored then
      .threwIo (.terminatedBySignal 13)
    else
      out0
  (out, updateWorldErrno { w with stderr := ch' } out)

/-- Pure transition of `defaultApi.promptLine` (catching OS `IO.Error` into `.ioError`). -/
def stepPromptLine (w : StdioWorld) (prompt : String) (default : Option String := none) :
    Except CmdLineError String × StdioWorld :=
  match stepDefaultWriteOut w prompt with
  | (.threwIo _, w1) =>
    (.error { kind := .ioError, message := "stdio I/O error" }, w1)
  | (.returned (), w1) =>
    match stepDefaultReadLine w1 with
    | (.threwIo _, w2) =>
      (.error { kind := .ioError, message := "stdio I/O error" }, w2)
    | (.returned none, w2) =>
      (.error { kind := .eof, message := "unexpected end of input" }, w2)
    | (.returned (some line), w2) =>
      let trimmed := trimAscii line
      if trimmed.isEmpty then
        match default with
        | some d => (.ok d, w2)
        | none => (.ok "", w2)
      else
        (.ok trimmed, w2)

/-- Pure transition of `defaultApi.confirm` (catching OS `IO.Error` into `.ioError`). -/
def stepConfirm (w : StdioWorld) (prompt : String) (default : Option Bool := none)
    (maxAttempts : Nat := 100) : Except CmdLineError Bool × StdioWorld :=
  match maxAttempts with
  | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, w)
  | n + 1 =>
    match stepDefaultWriteOut w prompt with
    | (.threwIo _, w1) =>
      (.error { kind := .ioError, message := "stdio I/O error" }, w1)
    | (.returned (), w1) =>
      match stepDefaultReadLine w1 with
      | (.threwIo _, w2) =>
        (.error { kind := .ioError, message := "stdio I/O error" }, w2)
      | (.returned none, w2) =>
        (.error { kind := .eof, message := "unexpected end of input" }, w2)
      | (.returned (some line), w2) =>
        let norm := asciiLower (trimAscii line)
        if norm.isEmpty then
          match default with
          | some b => (.ok b, w2)
          | none =>
            match n with
            | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, w2)
            | _ + 1 =>
              match stepDefaultWriteErr w2 "Please answer yes or no.\n" with
              | (.threwIo _, w3) =>
                (.error { kind := .ioError, message := "stdio I/O error" }, w3)
              | (.returned (), w3) => stepConfirm w3 prompt default n
        else if norm == "y" || norm == "yes" then
          (.ok true, w2)
        else if norm == "n" || norm == "no" then
          (.ok false, w2)
        else
          match n with
          | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, w2)
          | _ + 1 =>
            match stepDefaultWriteErr w2 "Please answer yes or no.\n" with
            | (.threwIo _, w3) =>
              (.error { kind := .ioError, message := "stdio I/O error" }, w3)
            | (.returned (), w3) => stepConfirm w3 prompt default n

/-- Find index of first `0x3D` (`'='`) byte in `bs`. -/
def findFirstEqByte (bs : ByteArray) : Option Nat :=
  go 0 bs.size
where
  go (i fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if _ : i < bs.size then
        if bs[i] == 0x3D then some i else go (i + 1) fuel'
      else none

/-- Sort tagged `(key, idx, val)` array and keep lowest-index entry per `key`. -/
def dedupSortedFirst {α : Type} (tagged : Array (String × Nat × α)) : Array (String × α) := Id.run do
  let sorted := tagged.qsort (fun a b => if a.1 == b.1 then a.2.1 < b.2.1 else a.1 < b.1)
  let mut out : Array (String × α) := Array.mkEmpty sorted.size
  for entry in sorted do
    let keep := match out.back? with | some prev => prev.1 != entry.1 | none => true
    if keep then
      out := out.push (entry.1, entry.2.2)
  return out

/-- Binary search in a strictly sorted `Array (String × α)`. -/
def bsearchSortedKey {α : Type} (arr : Array (String × α)) (k : String) : Option α :=
  go 0 arr.size (arr.size + 1)
where
  go (lo hi fuel : Nat) : Option α :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match arr[mid]? with
        | none => none
        | some entry =>
          if entry.1 == k then some entry.2
          else if entry.1 < k then go (mid + 1) hi fuel'
          else go lo mid fuel'
      else none

/-- Tail-recursive model of `resolveOptions` in `Id`, `O((M + U + E) log(U + E))` and safe on arbitrarily long option lists under 1 MiB stack. -/
def resolveOptionsModelTR (w : StdioWorld) (visibleOpts : List OptSpec)
    (cliOpts : List (String × List OptValue)) (validators : CustomValidators := []) :
    Except CmdLineError (List (String × List OptValue)) :=
  let cliArr := dedupSortedFirst (indexCli 0 cliOpts #[])
  let envArr := dedupSortedFirst (indexEnv 0 w.rawEnviron #[])
  go cliArr envArr visibleOpts []
where
  indexCli (i : Nat) : List (String × List OptValue) → Array (String × Nat × List OptValue) → Array (String × Nat × List OptValue)
    | [], acc => acc
    | (k, vs) :: rest, acc => indexCli (i + 1) rest (acc.push (k, i, vs))
  indexEnv (i : Nat) : List ByteArray → Array (String × Nat × ByteArray) → Array (String × Nat × ByteArray)
    | [], acc => acc
    | entry :: rest, acc =>
      let acc' :=
        match findFirstEqByte entry with
        | some eqPos =>
          match decodeUtf8Strict? (entry.extract 0 eqPos) with
          | some kStr => acc.push (kStr, i, entry.extract (eqPos + 1) entry.size)
          | none => acc
        | none => acc
      indexEnv (i + 1) rest acc'
  lookupEnvFast (envArr : Array (String × ByteArray)) (key : String) : Except CmdLineError (Option String) :=
    if !isValidEnvKey key then
      .error { kind := .ioError, message := "invalid environment variable name", target := some key }
    else
      match bsearchSortedKey envArr key with
      | none => .ok none
      | some valBytes =>
        match decodeUtf8Strict? valBytes with
        | some s => .ok (some s)
        | none => .error { kind := .ioError, message := "invalid UTF-8 in environment value", target := some key }
  go (cliArr : Array (String × List OptValue)) (envArr : Array (String × ByteArray)) :
      List OptSpec → List (String × List OptValue) → Except CmdLineError (List (String × List OptValue))
    | [], accRev => .ok accRev.reverse
    | opt :: rest, accRev =>
      let cliVals := (bsearchSortedKey cliArr opt.name).getD []
      match resolveSingleOption (m := Id) (fun key => lookupEnvFast envArr key) opt cliVals validators with
      | .error e => .error e
      | .ok none => go cliArr envArr rest accRev
      | .ok (some vals) => go cliArr envArr rest ((opt.name, vals) :: accRev)

/-- Pure transition of `resolveOptions` using `stepDefaultGetEnv` on `StdioWorld`. -/
def stepResolveOptionsWithEnv (w : StdioWorld) (visibleOpts : List OptSpec)
    (cliOpts : List (String × List OptValue)) (validators : CustomValidators := []) :
    Except CmdLineError (List (String × List OptValue)) :=
  resolveOptionsModelTR w visibleOpts cliOpts validators

/-- Pure transition of `defaultApi.runCliWith` routing given a resolved parse outcome. -/
def stepRunCliWithOutcome (w : StdioWorld) (parseOutcome : Except CmdLineError ParsedCmd)
    (handler : ParsedCmd → StdioWorld → IoStepOutcome UInt32 × StdioWorld) :
    IoStepOutcome UInt32 × StdioWorld :=
  match parseOutcome with
  | .error e =>
    match e.kind with
    | .helpRequested | .versionRequested =>
      match stepDefaultWriteOut w e.message with
      | (.threwIo err, w1) => (.threwIo err, w1)
      | (.returned (), w1) => (.returned 0, w1)
    | _ =>
      match stepDefaultWriteErr w (e.message ++ "\n") with
      | (.threwIo err, w1) => (.threwIo err, w1)
      | (.returned (), w1) => (.returned 2, w1)
  | .ok parsed => handler parsed w

/-- Truncate `bs` at its first `0x00` byte, matching C `strlen` / `execve` `argv` C strings. -/
def truncateAtNul (bs : ByteArray) : ByteArray :=
  go 0 bs.size
where
  go (i fuel : Nat) : ByteArray :=
    match fuel with
    | 0 => bs
    | fuel' + 1 =>
      if _ : i < bs.size then
        if bs[i] == 0x00 then bs.extract 0 i else go (i + 1) fuel'
      else bs

/-- Pure model of Lean 4 startup decoding raw OS `argv` C strings (`strlen` NUL-truncation + `decodeUtf8LossyLean`). -/
def decodeArgvModel (rawArgv : List ByteArray) : List String :=
  rawArgv.map (fun bs => decodeUtf8LossyLean (truncateAtNul bs))

/-- Pure model of Linux process exit code (`WEXITSTATUS` or `128 + sig`) observed by a parent process. -/
def osExitCodeModel : IoStepOutcome UInt32 → UInt8
  | .returned code => UInt8.ofNat (code.toNat % 256)
  | .threwIo (.terminatedBySignal sig) => 128 + sig
  | .threwIo _ => 1

/-- Reference model for `CmdLine.renderVersion`. -/
def renderVersionModel (name version : String) : String :=
  s!"{name} {version}\n"

/-- Allowed outcome relation for `CmdLine.renderHelp`. -/
def allowedRenderHelp (rootSpec : CommandSpec) (subcommandPath : List String)
    (out : Except CmdLineError String) : Prop :=
  if !isValidSpec rootSpec then
    out = .error { kind := .invalidSpec, message := s!"invalid command spec '{rootSpec.name}'" }
  else
    match findSubcommandPath rootSpec subcommandPath, out with
    | .error e, .error e' => e' = e
    | .ok _, .ok text => !text.isEmpty = true
    | _, _ => False

/-- Declarative surface phrase in a tokenized CLI argument list. -/
inductive CliPhrase where
  /-- Matched subcommand token `name`. -/
  | subcommand (name : String)
  /-- Positive boolean long flag `--<longName>` yielding `.bool true` for `optName`. -/
  | longBoolTrue (longName optName : String)
  /-- Negated boolean long flag `--no-<baseLong>` yielding `.bool false` for `optName`. -/
  | longBoolNeg (baseLong optName : String)
  /-- Inline boolean long flag `--<longName>=<rawVal>` yielding `.bool val` for `optName`. -/
  | longBoolEq (longName rawVal optName : String) (val : Bool)
  /-- Inline value long option `--<longName>=<rawVal>` yielding `val` for `optName`. -/
  | longValEq (longName rawVal optName : String) (val : OptValue)
  /-- Space-separated value long option `["--" ++ longName, rawVal]` yielding `val` for `optName`. -/
  | longValSep (longName rawVal optName : String) (val : OptValue)
  /-- Pure boolean short-flag cluster `'-' :: chars` yielding `.bool true` for `optNames`. -/
  | shortBoolCluster (chars : List Char) (optNames : List String)
  /-- Attached short option `'-' :: (prefixChars ++ (optChar :: rawVal))`. -/
  | shortAttachedVal (prefixChars : List Char) (prefixOptNames : List String)
      (optChar : Char) (rawVal : List Char) (optName : String) (val : OptValue)
  /-- Space-separated short option `[String.ofList ('-' :: (prefixChars ++ [optChar])), rawVal]`. -/
  | shortSepVal (prefixChars : List Char) (prefixOptNames : List String)
      (optChar : Char) (rawVal optName : String) (val : OptValue)
  /-- Bare positional argument token `tok` before `--`. -/
  | positional (tok : String)
  /-- End-of-options `--` marker followed by literal positional tail `tail`. -/
  | dashDashTail (tail : List String)
  deriving Repr, Inhabited

/-- Surface CLI tokens synthesized by a single `CliPhrase`. -/
def CliPhrase.tokens : CliPhrase → List String
  | .subcommand name => [name]
  | .longBoolTrue l _ => ["--" ++ l]
  | .longBoolNeg b _ => ["--no-" ++ b]
  | .longBoolEq l rv _ _ => ["--" ++ l ++ "=" ++ rv]
  | .longValEq l rv _ _ => ["--" ++ l ++ "=" ++ rv]
  | .longValSep l rv _ _ => ["--" ++ l, rv]
  | .shortBoolCluster cs _ => [String.ofList ('-' :: cs)]
  | .shortAttachedVal pcs _ oc rv _ _ => [String.ofList ('-' :: (pcs ++ (oc :: rv)))]
  | .shortSepVal pcs _ oc rv _ _ => [String.ofList ('-' :: (pcs ++ [oc])), rv]
  | .positional tok => [tok]
  | .dashDashTail tail => "--" :: tail

/-- Optional matched subcommand name contributed by a `CliPhrase`. -/
def CliPhrase.subcmd? : CliPhrase → Option String
  | .subcommand name => some name
  | _ => none

/-- Raw positional argument tokens contributed by a `CliPhrase`. -/
def CliPhrase.posTokens : CliPhrase → List String
  | .positional tok => [tok]
  | .dashDashTail tail => tail
  | _ => []

/-- Forward `(optName, OptValue)` occurrences contributed by a `CliPhrase`. -/
def CliPhrase.optEvents : CliPhrase → List (String × OptValue)
  | .longBoolTrue _ oname => [(oname, .bool true)]
  | .longBoolNeg _ oname => [(oname, .bool false)]
  | .longBoolEq _ _ oname b => [(oname, .bool b)]
  | .longValEq _ _ oname v => [(oname, v)]
  | .longValSep _ _ oname v => [(oname, v)]
  | .shortBoolCluster _ onames => onames.map (fun n => (n, .bool true))
  | .shortAttachedVal _ pnames _ _ oname v => pnames.map (fun n => (n, .bool true)) ++ [(oname, v)]
  | .shortSepVal _ pnames _ _ oname v => pnames.map (fun n => (n, .bool true)) ++ [(oname, v)]
  | _ => []

/-- Return `true` iff `tok` is not a multi-character dash flag (`""`, `"-"`, or non-`'-'` head). -/
def isPlainCliTokenBool (tok : String) : Bool :=
  match tok.toList with
  | '-' :: _ :: _ => false
  | _ => true

/-- Check that `chars` and `optNames` align 1-to-1 with boolean short options in `visibleOpts`. -/
def validShortBoolPrefixBool (visibleOpts : List OptSpec) : List Char → List String → Bool
  | [], [] => true
  | c :: cs, n :: ns =>
    (match visibleOpts.find? (fun o => o.short == some c) with
     | some o => o.kind == .bool && o.name == n
     | none => false) &&
    validShortBoolPrefixBool visibleOpts cs ns
  | _, _ => false

/-- Validate one `CliPhrase` against `(globals, effVer, curSpec, seenPos)`, returning `(nextGlobals, nextVer, nextSpec, nextSeenPos, mustEnd)`. -/
def validSinglePhraseStep (validators : CustomValidators) (globals : List OptSpec)
    (effVer : Option String) (curSpec : CommandSpec) (seenPos : Bool) :
    CliPhrase → Option (List OptSpec × Option String × CommandSpec × Bool × Bool)
  | .subcommand name =>
    if !curSpec.subcommands.isEmpty && !seenPos then
      match curSpec.subcommands.find? (fun s => s.name == name) with
      | some sub => some (globals ++ curSpec.options, sub.version <|> effVer, sub, false, false)
      | none => none
    else
      none
  | .longBoolTrue l oname =>
    match (globals ++ curSpec.options).find? (fun o => o.long == some l) with
    | some o =>
      if o.kind == .bool && o.name == oname then
        some (globals, effVer, curSpec, seenPos, false)
      else
        none
    | none => none
  | .longBoolNeg b oname =>
    match (globals ++ curSpec.options).find? (fun o => o.long == some b) with
    | some o =>
      if o.kind == .bool && !o.repeatable && o.name == oname then
        some (globals, effVer, curSpec, seenPos, false)
      else
        none
    | none => none
  | .longBoolEq l rv oname val =>
    match (globals ++ curSpec.options).find? (fun o => o.long == some l) with
    | some o =>
      if o.kind == .bool && o.name == oname && !(o.repeatable && !val) &&
          parseBoolString rv == some val then
        some (globals, effVer, curSpec, seenPos, false)
      else
        none
    | none => none
  | .longValEq l rv oname val | .longValSep l rv oname val =>
    match (globals ++ curSpec.options).find? (fun o => o.long == some l) with
    | some o =>
      if o.kind != .bool && o.name == oname &&
          (match parseOptValueWith o.kind rv validators with | .ok v => decide (v = val) | .error _ => false) then
        some (globals, effVer, curSpec, seenPos, false)
      else
        none
    | none => none
  | .shortBoolCluster cs onames =>
    if !cs.isEmpty && validShortBoolPrefixBool (globals ++ curSpec.options) cs onames then
      some (globals, effVer, curSpec, seenPos, false)
    else
      none
  | .shortAttachedVal pcs pnames oc rv oname val =>
    if !rv.isEmpty && validShortBoolPrefixBool (globals ++ curSpec.options) pcs pnames then
      match (globals ++ curSpec.options).find? (fun o => o.short == some oc) with
      | some o =>
        if o.kind != .bool && o.name == oname &&
            (match parseOptValueWith o.kind (String.ofList rv) validators with | .ok v => decide (v = val) | .error _ => false) then
          some (globals, effVer, curSpec, seenPos, false)
        else
          none
      | none => none
    else
      none
  | .shortSepVal pcs pnames oc rv oname val =>
    if validShortBoolPrefixBool (globals ++ curSpec.options) pcs pnames then
      match (globals ++ curSpec.options).find? (fun o => o.short == some oc) with
      | some o =>
        if o.kind != .bool && o.name == oname &&
            (match parseOptValueWith o.kind rv validators with | .ok v => decide (v = val) | .error _ => false) then
          some (globals, effVer, curSpec, seenPos, false)
        else
          none
      | none => none
    else
      none
  | .positional tok =>
    if isPlainCliTokenBool tok && (curSpec.subcommands.isEmpty || seenPos) then
      some (globals, effVer, curSpec, true, false)
    else
      none
  | .dashDashTail tail =>
    some (globals, effVer, curSpec, seenPos || !tail.isEmpty, true)

/-- Check a complete `CliPhrase` derivation starting from `(globals, effVer, curSpec, seenPos)`. -/
def checkCliPhrases (validators : CustomValidators) (globals : List OptSpec)
    (effVer : Option String) (curSpec : CommandSpec) (seenPos : Bool) : List CliPhrase → Bool
  | [] => true
  | p :: rest =>
    match validSinglePhraseStep validators globals effVer curSpec seenPos p with
    | none => false
    | some (nextGlobals, nextVer, nextSpec, nextSeenPos, mustEnd) =>
      if mustEnd then rest.isEmpty
      else checkCliPhrases validators nextGlobals nextVer nextSpec nextSeenPos rest

/-- Traverse an open (pre-`--`) sequence of valid `CliPhrase`s, returning the active command context. -/
def runOpenCliPhrases (validators : CustomValidators) (globals : List OptSpec)
    (effVer : Option String) (curSpec : CommandSpec) (seenPos : Bool) :
    List CliPhrase → Option (List OptSpec × Option String × CommandSpec × Bool)
  | [] => some (globals, effVer, curSpec, seenPos)
  | p :: rest =>
    match validSinglePhraseStep validators globals effVer curSpec seenPos p with
    | none => none
    | some (nextGlobals, nextVer, nextSpec, nextSeenPos, mustEnd) =>
      if mustEnd then none
      else runOpenCliPhrases validators nextGlobals nextVer nextSpec nextSeenPos rest

/-- Build per-option forward CLI value lists from `phrases` for `visibleOpts`. -/
def cliOptsOfPhrases (visibleOpts : List OptSpec) (phrases : List CliPhrase) :
    List (String × List OptValue) :=
  let events := phrases.flatMap CliPhrase.optEvents
  visibleOpts.filterMap fun opt =>
    let vs := events.filterMap (fun p => if p.1 == opt.name then some p.2 else none)
    if vs.isEmpty then none else some (opt.name, vs)

/-- Return `true` iff `cs` begins with zero or more boolean short flags in `visibleOpts` followed by `target`. -/
def hasShortPrefixBeforeCharBool (visibleOpts : List OptSpec) (target : Char) : List Char → Bool
  | [] => false
  | ch :: rest =>
    if ch == target then true
    else
      match visibleOpts.find? (fun o => o.short == some ch) with
      | some o => o.kind == .bool && hasShortPrefixBeforeCharBool visibleOpts target rest
      | none => false

/-- Return `true` iff `tok` triggers `--help` or `-h` under `(visibleOpts, shortHelp)`. -/
def isHelpTriggerTokenBool (visibleOpts : List OptSpec) (shortHelp : Bool) (tok : String) : Bool :=
  tok == "--help" ||
  (shortHelp &&
    match tok.toList with
    | '-' :: c :: rest => c != '-' && hasShortPrefixBeforeCharBool visibleOpts 'h' (c :: rest)
    | _ => false)

/-- Return `true` iff `tok` triggers `--version` or `-V` under `(visibleOpts, shortVersion, effVer)`. -/
def isVersionTriggerTokenBool (visibleOpts : List OptSpec) (shortVersion : Bool)
    (effVer : Option String) (tok : String) : Bool :=
  effVer.isSome &&
  (tok == "--version" ||
    (shortVersion &&
      match tok.toList with
      | '-' :: c :: rest => c != '-' && hasShortPrefixBeforeCharBool visibleOpts 'V' (c :: rest)
      | _ => false))

/-- Declarative existence of a valid pre-`--` phrase prefix in `args` ending at a help trigger token. -/
def ExistsHelpInvocation (spec : CommandSpec) (validators : CustomValidators)
    (args : List String) : Prop :=
  ∃ (phrases : List CliPhrase) (triggerTok : String) (tail : List String)
    (globals : List OptSpec) (effVer : Option String) (curSpec : CommandSpec) (seenPos : Bool),
    runOpenCliPhrases validators [] spec.version spec false phrases =
      some (globals, effVer, curSpec, seenPos) ∧
    (phrases.map CliPhrase.tokens).flatten ++ (triggerTok :: tail) = args ∧
    isHelpTriggerTokenBool (globals ++ curSpec.options) curSpec.shortHelp triggerTok = true

/-- Declarative existence of a valid pre-`--` phrase prefix in `args` ending at a version trigger token. -/
def ExistsVersionInvocation (spec : CommandSpec) (validators : CustomValidators)
    (args : List String) : Prop :=
  ∃ (phrases : List CliPhrase) (triggerTok : String) (tail : List String)
    (globals : List OptSpec) (effVer : Option String) (curSpec : CommandSpec) (seenPos : Bool),
    runOpenCliPhrases validators [] spec.version spec false phrases =
      some (globals, effVer, curSpec, seenPos) ∧
    (phrases.map CliPhrase.tokens).flatten ++ (triggerTok :: tail) = args ∧
    isVersionTriggerTokenBool (globals ++ curSpec.options) curSpec.shortVersion effVer triggerTok = true

/-- Declarative phrase-derivation and option/argument resolution relation for a valid `ParsedCmd`. -/
def ValidParsedCmd (getEnv : String → Except CmdLineError (Option String))
    (spec : CommandSpec) (args : List String) (validators : CustomValidators)
    (parsed : ParsedCmd) : Prop :=
  isValidSpec spec = true ∧
  ∃ (globals : List OptSpec) (effVer : Option String) (targetSpec : CommandSpec),
    findSubcommandPath spec parsed.subcommandPath = .ok (globals, effVer, targetSpec) ∧
    targetSpec.subcommands.isEmpty = true ∧
    ∃ phrases : List CliPhrase,
      (phrases.map CliPhrase.tokens).flatten = args ∧
      checkCliPhrases validators [] spec.version spec false phrases = true ∧
      phrases.filterMap CliPhrase.subcmd? = parsed.subcommandPath ∧
      phrases.flatMap CliPhrase.posTokens = parsed.rawPositionals ∧
      resolveOptions (m := Id) getEnv (globals ++ targetSpec.options)
        (cliOptsOfPhrases (globals ++ targetSpec.options) phrases) validators = .ok parsed.options ∧
      resolveArgs targetSpec.args (phrases.flatMap CliPhrase.posTokens) validators = .ok parsed.args

/-- Declarative specification for CLI parsing parameterized by environment lookup `getEnv`. -/
def AllowedParseOutcome (getEnv : String → Except CmdLineError (Option String))
    (spec : CommandSpec) (args : List String) (validators : CustomValidators)
    (out : Except CmdLineError ParsedCmd) : Prop :=
  if !isValidSpec spec then
    out = .error { kind := .invalidSpec, message := s!"invalid command spec '{spec.name}'" }
  else
    match out with
    | .ok parsed =>
      ValidParsedCmd getEnv spec args validators parsed
    | .error e =>
      (¬(∃ parsed, ValidParsedCmd getEnv spec args validators parsed) ∧
        ¬ExistsHelpInvocation spec validators args ∧
        ¬ExistsVersionInvocation spec validators args ∧
        ((∃ envKey : String, getEnv envKey = .error e) ∨
          ((!e.message.isEmpty) = true ∧
            e.kind ≠ .invalidSpec ∧ e.kind ≠ .helpRequested ∧
            e.kind ≠ .versionRequested ∧ e.kind ≠ .eof ∧ e.kind ≠ .ioError))) ∨
      (e.kind = .helpRequested ∧ (!e.message.isEmpty) = true ∧
        ExistsHelpInvocation spec validators args) ∨
      (e.kind = .versionRequested ∧ (!e.message.isEmpty) = true ∧
        ExistsVersionInvocation spec validators args)

/-- Allowed outcome relation for `CmdLine.parseWith` against `AllowedParseOutcome`. -/
def allowedParseWith (spec : CommandSpec) (args : List String) (validators : CustomValidators)
    (out : Except CmdLineError ParsedCmd) : Prop :=
  AllowedParseOutcome (fun _ => .ok none) spec args validators out

/-- Allowed outcome relation for `CmdLine.parse` (defaulting `validators := []`). -/
def allowedParse (spec : CommandSpec) (args : List String)
    (out : Except CmdLineError ParsedCmd) : Prop :=
  allowedParseWith spec args [] out

/-- Pure abstract state for monadic `CliOpsM` step refinement in `Core.RefinesStepFrom`. -/
structure CliStepState where
  /-- Queued input lines returned by `CliOpsM.readLine`. -/
  stdinLines : List String := []
  /-- Accumulated `stdout` text emitted via `CliOpsM.writeOut`. -/
  stdout : String := ""
  /-- Accumulated `stderr` text emitted via `CliOpsM.writeErr`. -/
  stderr : String := ""
  /-- Environment lookup entries queried via `CliOpsM.getEnv`. -/
  env : List (String × Except CmdLineError (Option String)) := []
  deriving Inhabited

/-- Request sum for `CliOpsM` primitives in `Core.RefinesStepFrom`. -/
inductive RawStepReq where
  /-- Pop the next line from `stdin`. -/
  | readLine
  /-- Append text to `stdout`. -/
  | writeOut (text : String)
  /-- Append text to `stderr`. -/
  | writeErr (text : String)
  /-- Query environment variable `key`. -/
  | getEnv (key : String)

/-- Output sum for `CliOpsM` primitives in `Core.RefinesStepFrom`. -/
inductive RawStepOut where
  /-- Result of `CliOpsM.readLine`. -/
  | line (res : Option String)
  /-- Result of `CliOpsM.writeOut` or `writeErr`. -/
  | unit
  /-- Result of `CliOpsM.getEnv`. -/
  | envVal (res : Except CmdLineError (Option String))

/-- Total well-formedness guard on `CliStepState` for `Core.RefinesStepFrom`. -/
def rawStepWf (_ : CliStepState) : Bool := true

/-- Execute one `RawStepReq` against an arbitrary `CliOpsM (StateM W)`. -/
def execRawStep {W : Type} (ops : CliOpsM (StateM W)) : RawStepReq → StateM W RawStepOut
  | .readLine => .line <$> ops.readLine
  | .writeOut text => ops.writeOut text *> pure .unit
  | .writeErr text => ops.writeErr text *> pure .unit
  | .getEnv key => .envVal <$> ops.getEnv key

/-- Pure lookup of `key` in `CliStepState.env`. -/
def lookupCliStepEnv (s : CliStepState) (key : String) : Except CmdLineError (Option String) :=
  match s.env.find? (fun p => p.1 == key) with
  | some p => p.2
  | none => .ok none

/-- Allowed raw single-step relation over `CliStepState`. -/
def allowedRawStep (s : CliStepState) (req : RawStepReq) (out : RawStepOut)
    (s' : CliStepState) : Prop :=
  match req, out with
  | .readLine, .line res =>
    match s.stdinLines with
    | [] => res = none ∧ s' = s
    | hd :: tl => res = some hd ∧ s' = { s with stdinLines := tl }
  | .writeOut text, .unit => s' = { s with stdout := s.stdout ++ text }
  | .writeErr text, .unit => s' = { s with stderr := s.stderr ++ text }
  | .getEnv key, .envVal res => res = lookupCliStepEnv s key ∧ s' = s
  | _, _ => False

/-- Pure single-step model of `CmdLineApiM.promptLine` over `CliStepState`. -/
def stepCliPromptLine (s : CliStepState) (prompt : String) (default : Option String) :
    Except CmdLineError String × CliStepState :=
  let s1 := { s with stdout := s.stdout ++ prompt }
  match s1.stdinLines with
  | [] => (.error { kind := .eof, message := "unexpected end of input" }, s1)
  | line :: rest =>
    let s2 := { s1 with stdinLines := rest }
    let trimmed := trimAscii line
    if trimmed.isEmpty then
      match default with
      | some d => (.ok d, s2)
      | none => (.ok "", s2)
    else
      (.ok trimmed, s2)

/-- Pure single-step model of `CmdLineApiM.confirm` over `CliStepState`. -/
def stepCliConfirm (s : CliStepState) (prompt : String) (default : Option Bool) :
    Nat → Except CmdLineError Bool × CliStepState
  | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, s)
  | n + 1 =>
    let s1 := { s with stdout := s.stdout ++ prompt }
    match s1.stdinLines with
    | [] => (.error { kind := .eof, message := "unexpected end of input" }, s1)
    | line :: rest =>
      let s2 := { s1 with stdinLines := rest }
      let norm := asciiLower (trimAscii line)
      if norm.isEmpty then
        match default with
        | some b => (.ok b, s2)
        | none =>
          match n with
          | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, s2)
          | _ + 1 => stepCliConfirm { s2 with stderr := s2.stderr ++ "Please answer yes or no.\n" } prompt default n
      else if norm == "y" || norm == "yes" then
        (.ok true, s2)
      else if norm == "n" || norm == "no" then
        (.ok false, s2)
      else
        match n with
        | 0 => (.error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" }, s2)
        | _ + 1 => stepCliConfirm { s2 with stderr := s2.stderr ++ "Please answer yes or no.\n" } prompt default n

/-- Request sum covering all effectful `CmdLineApiM` operations (`parseWithEnv`, `promptLine`, `confirm`, `runCli`, `runCliWith`). -/
inductive PkgStepReq where
  /-- `CmdLineApiM.parseWithEnv` request. -/
  | parseWithEnv (spec : CommandSpec) (args : List String) (validators : CustomValidators)
  /-- `CmdLineApiM.promptLine` request. -/
  | promptLine (prompt : String) (default : Option String)
  /-- `CmdLineApiM.confirm` request. -/
  | confirm (prompt : String) (default : Option Bool) (maxAttempts : Nat)
  /-- `CmdLineApiM.runCli` request with pure exit-code callback. -/
  | runCli (spec : CommandSpec) (args : List String) (exitCode : UInt32)
  /-- `CmdLineApiM.runCliWith` request with custom validators and pure exit-code callback. -/
  | runCliWith (spec : CommandSpec) (args : List String) (validators : CustomValidators) (exitCode : UInt32)

/-- Output sum for effectful `CmdLineApiM` transitions. -/
inductive PkgStepOut where
  /-- Result of `CmdLineApiM.parseWithEnv`. -/
  | parsed (res : Except CmdLineError ParsedCmd)
  /-- Result of `CmdLineApiM.promptLine`. -/
  | line (res : Except CmdLineError String)
  /-- Result of `CmdLineApiM.confirm`. -/
  | confirmed (res : Except CmdLineError Bool)
  /-- Result of `CmdLineApiM.runCli` or `runCliWith`. -/
  | code (res : UInt32)

/-- Execute one `PkgStepReq` against a `CmdLineApiM (StateM W)` bundle. -/
def execPkgStep {W : Type} (api : CmdLineApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .parseWithEnv spec args validators => .parsed <$> api.parseWithEnv spec args validators
  | .promptLine prompt default => .line <$> api.promptLine prompt default
  | .confirm prompt default maxAttempts => .confirmed <$> api.confirm prompt default maxAttempts
  | .runCli spec args exitCode => .code <$> api.runCli spec args (fun _ => pure exitCode)
  | .runCliWith spec args validators exitCode =>
    .code <$> api.runCliWith spec args validators (fun _ => pure exitCode)

/-- Allowed outcome relation for `parseWithEnv` on `CliStepState` against `AllowedParseOutcome`. -/
def allowedParseWithEnvStep (s : CliStepState) (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) (res : Except CmdLineError ParsedCmd) (s' : CliStepState) : Prop :=
  s' = s ∧ AllowedParseOutcome (lookupCliStepEnv s) spec args validators res

/-- Allowed outcome relation for `runCliWith` on `CliStepState` against `allowedParseWithEnvStep`. -/
def allowedRunCliWithStep (s : CliStepState) (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) (exitCode code : UInt32) (s' : CliStepState) : Prop :=
  ∃ outcome : Except CmdLineError ParsedCmd,
    allowedParseWithEnvStep s spec args validators outcome s ∧
    match outcome with
    | .ok _ => code = exitCode ∧ s' = s
    | .error e =>
      match e.kind with
      | .helpRequested | .versionRequested =>
        code = 0 ∧ s' = { s with stdout := s.stdout ++ e.message }
      | _ =>
        code = 2 ∧ s' = { s with stderr := s.stderr ++ e.message ++ "\n" }

/-- Allowed package-level single-step relation over `CliStepState`. -/
def allowedPkgStep (s : CliStepState) (req : PkgStepReq) (out : PkgStepOut)
    (s' : CliStepState) : Prop :=
  match req, out with
  | .parseWithEnv spec args validators, .parsed res =>
    allowedParseWithEnvStep s spec args validators res s'
  | .promptLine prompt default, .line res =>
    (res, s') = stepCliPromptLine s prompt default
  | .confirm prompt default maxAttempts, .confirmed res =>
    (res, s') = stepCliConfirm s prompt default maxAttempts
  | .runCli spec args exitCode, .code code =>
    allowedRunCliWithStep s spec args [] exitCode code s'
  | .runCliWith spec args validators exitCode, .code code =>
    allowedRunCliWithStep s spec args validators exitCode code s'
  | _, _ => False

end LeanSwe.CmdLine.Model
