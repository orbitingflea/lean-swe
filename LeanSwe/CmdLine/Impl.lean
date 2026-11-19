import Std.Data.HashSet
import Std.Data.HashMap
import LeanSwe.CmdLine.Types
import LeanSwe.CmdLine.Model

namespace LeanSwe.CmdLine.Internal

open LeanSwe.CmdLine

/-- Tail-recursive pairwise multiplier for decimal chunks `(value, 10^digits)`. -/
def mergeNatChunksTR (accRev : List (Nat × Nat)) : List (Nat × Nat) → List (Nat × Nat)
  | [] => accRev.reverse
  | [p] => (p :: accRev).reverse
  | (v1, b1) :: (v2, b2) :: rest => mergeNatChunksTR ((v1 * b2 + v2, b1 * b2) :: accRev) rest

/-- Balanced pairwise reduction of decimal `(value, radix)` chunks. -/
def reduceNatChunks : Nat → List (Nat × Nat) → Nat
  | _, [] => 0
  | _, [(v, _)] => v
  | 0, ps => ps.foldl (fun acc p => acc * p.2 + p.1) 0
  | fuel + 1, ps => reduceNatChunks fuel (mergeNatChunksTR [] ps)

/-- Parse ASCII decimal digits in `O(N log^2 N)` using 18-digit unboxed `Nat` chunks. -/
def parseNatCharsFast (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else go cs 0 1 0 []
where
  go : List Char → Nat → Nat → Nat → List (Nat × Nat) → Option Nat
    | [], curVal, curBase, _, chunksRev =>
      let allRev := (curVal, curBase) :: chunksRev
      some (reduceNatChunks allRev.length allRev.reverse)
    | c :: rest, curVal, curBase, count, chunksRev =>
      if '0' ≤ c && c ≤ '9' then
        let curVal' := curVal * 10 + (c.toNat - '0'.toNat)
        let curBase' := curBase * 10
        let count' := count + 1
        if count' == 18 then
          go rest 0 1 0 ((curVal', curBase') :: chunksRev)
        else
          go rest curVal' curBase' count' chunksRev
      else
        none

/-- Fast `Int` digit parser matching `Model.parseIntChars`. -/
def parseIntCharsFast (cs : List Char) : Option Int :=
  match cs with
  | '-' :: rest => (parseNatCharsFast rest).map (fun n => -(Int.ofNat n))
  | _ => (parseNatCharsFast cs).map Int.ofNat

/-- Fast `parseOptValue` using `parseNatCharsFast` / `parseIntCharsFast`. -/
def parseOptValueFast (kind : ValueKind) (s : String) : Except CmdLineError OptValue :=
  match kind with
  | .string => .ok (.string s)
  | .bool =>
    match Model.parseBoolString s with
    | some b => .ok (.bool b)
    | none => .error { kind := .invalidValue, message := s!"invalid boolean value '{s}'" }
  | .nat =>
    match parseNatCharsFast s.toList with
    | some n => .ok (.nat n)
    | none => .error { kind := .invalidValue, message := s!"invalid unsigned integer value '{s}'" }
  | .int =>
    match parseIntCharsFast s.toList with
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

/-- Fast `parseOptValueWith` matching `Model.parseOptValueWith`. -/
def parseOptValueWithFast (kind : ValueKind) (s : String) (validators : CustomValidators := []) :
    Except CmdLineError OptValue := do
  let v ← parseOptValueFast kind s
  Model.validateCustomValue kind s validators
  pure v

/-- Fast `Model.resolveOptDefault` using `parseOptValueWithFast`. -/
def resolveOptDefaultFast (opt : OptSpec) (validators : CustomValidators) :
    Except CmdLineError (Option (List OptValue)) :=
  match opt.default with
  | some d =>
    match parseOptValueWithFast opt.kind d validators with
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

/-- Fast `Model.resolveSingleOption` using `parseOptValueWithFast`. -/
def resolveSingleOptionFast {m : Type → Type} [Monad m]
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
    | none => return resolveOptDefaultFast opt validators
    | some envKey =>
      match ← getEnv envKey with
      | .error e => return .error e
      | .ok none => return resolveOptDefaultFast opt validators
      | .ok (some "") => return resolveOptDefaultFast opt validators
      | .ok (some s) =>
        match parseOptValueWithFast opt.kind s validators with
        | .error e => return .error { e with target := some opt.name }
        | .ok v =>
          if opt.repeatable && opt.kind == .bool && v == .bool false then
            return .ok none
          else
            return .ok (some [v])

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

/-- Absolute difference between two natural numbers. -/
def natDiff (a b : Nat) : Nat :=
  if a >= b then a - b else b - a

/-- Compute Optimal String Alignment edit distance (with adjacent transpositions) using pure `List Char` DP. -/
def editDistance (a b : String) : Nat :=
  let aChars := a.toList
  let bChars := b.toList
  let initRow := List.range (bChars.length + 1)
  let finalState := aChars.foldl (step bChars) (0, none, initRow, initRow)
  finalState.2.2.2.getLastD 0
where
  nextCells (ca : Char) (prevCa : Option Char) (prevCb : Option Char)
      (prevDiag left ppPrev : Nat) (ppTail accRev : List Nat) : List (Char × Nat) → List Nat
    | [] => accRev.reverse
    | (cb, up) :: rest =>
      let cost := if ca == cb then 0 else 1
      let base := min (min (up + 1) (left + 1)) (prevDiag + cost)
      let cell :=
        match prevCa, prevCb with
        | some pa, some pb =>
          if ca == pb && cb == pa then min base (ppPrev + 1) else base
        | _, _ => base
      let ppHead := ppTail.headD (ppPrev + 1)
      nextCells ca prevCa (some cb) up cell ppHead (ppTail.drop 1) (cell :: accRev) rest
  step (bChars : List Char) (state : Nat × Option Char × List Nat × List Nat) (ca : Char) :
      Nat × Option Char × List Nat × List Nat :=
    let rowIdx := state.1 + 1
    let prevCa := state.2.1
    let prevPrevRow := state.2.2.1
    let prevRow := state.2.2.2
    let pairs := bChars.zip (prevRow.drop 1)
    let firstPrev := prevRow.headD 0
    let newRow := rowIdx :: nextCells ca prevCa none firstPrev rowIdx 0 prevPrevRow [] pairs
    (rowIdx, some ca, prevRow, newRow)

/-- Banded Optimal String Alignment edit distance clamped at `maxDist + 1` with row-minimum early exit. -/
def editDistanceBounded (maxDist : Nat) (a b : String) : Nat :=
  let aArr := a.toList.toArray
  let bArr := b.toList.toArray
  let m := aArr.size
  let n := bArr.size
  if natDiff m n > maxDist then
    maxDist + 1
  else if m == 0 then
    n
  else if n == 0 then
    m
  else
    let inf := maxDist + 1
    let initArr := (List.range (min n maxDist + 1)).toArray
    rowLoop maxDist aArr bArr m n inf 1 0 #[] 0 initArr
where
  getCell (inf lo : Nat) (arr : Array Nat) (j : Nat) : Nat :=
    if j < lo then inf
    else
      let off := j - lo
      if off < arr.size then arr[off]! else inf
  colLoop (aArr bArr : Array Char) (inf i lo hi ppLo prevLo : Nat)
      (ppArr prevArr : Array Nat) (j : Nat) (curArr : Array Nat) (rowMin : Nat) : Array Nat × Nat :=
    if _ : j ≤ hi then
      let cell :=
        if j == 0 then
          i
        else
          let up := getCell inf prevLo prevArr j + 1
          let left := if curArr.isEmpty then inf else curArr[curArr.size - 1]! + 1
          let cost := if aArr[i - 1]! == bArr[j - 1]! then 0 else 1
          let diag := getCell inf prevLo prevArr (j - 1) + cost
          let base := min (min up left) diag
          if i >= 2 && j >= 2 && aArr[i - 1]! == bArr[j - 2]! && aArr[i - 2]! == bArr[j - 1]! then
            min base (getCell inf ppLo ppArr (j - 2) + 1)
          else
            base
      colLoop aArr bArr inf i lo hi ppLo prevLo ppArr prevArr (j + 1) (curArr.push cell) (min rowMin cell)
    else
      (curArr, rowMin)
  termination_by hi + 1 - j
  rowLoop (maxDist : Nat) (aArr bArr : Array Char) (m n inf i ppLo : Nat)
      (ppArr : Array Nat) (prevLo : Nat) (prevArr : Array Nat) : Nat :=
    if _ : i ≤ m then
      let lo := if i > maxDist then i - maxDist else 0
      let hi := min n (i + maxDist)
      let (curArr, rowMin) := colLoop aArr bArr inf i lo hi ppLo prevLo ppArr prevArr lo (Array.mkEmpty (hi - lo + 1)) inf
      if rowMin > maxDist then
        inf
      else
        rowLoop maxDist aArr bArr m n inf (i + 1) prevLo prevArr lo curArr
    else
      getCell inf prevLo prevArr n
  termination_by m + 1 - i

/-- Find the closest candidate within `dist ≤ min 2 (max 1 (input.length / 3))`, breaking ties lexicographically. -/
def bestSuggestion (input : String) (candidates : List String) : Option String :=
  let maxDist := min 2 (max 1 (input.length / 3))
  let best := candidates.foldl (fun acc cand =>
    if natDiff input.length cand.length > maxDist then
      acc
    else
      let d := editDistanceBounded maxDist input cand
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

/-- Tail-recursive equivalent of `Model.collectVisibleLongs`. -/
def collectLongsTR (opts : List OptSpec) : List String :=
  go [] opts
where
  go (accRev : List String) : List OptSpec → List String
    | [] => accRev.reverse
    | opt :: rest =>
      match opt.long with
      | none => go accRev rest
      | some l =>
        if opt.kind == .bool && !opt.repeatable then
          go (("no-" ++ l) :: l :: accRev) rest
        else
          go (l :: accRev) rest

/-- Insert `xs` into `seen`, returning `none` if any element collides with `seen` or earlier elements of `xs`. -/
def insertDistinctSet {α : Type} [BEq α] [Hashable α]
    (seen : Std.HashSet α) : List α → Option (Std.HashSet α)
  | [] => some seen
  | x :: xs => if seen.contains x then none else insertDistinctSet (seen.insert x) xs

/-- Inherited option distinctness sets and effective version threaded across worklist validation. -/
structure ValidCtx where
  /-- Accumulated distinct canonical option names. -/
  optNames : Std.HashSet String := {}
  /-- Accumulated distinct visible long option names (including `"no-" ++ l` booleans). -/
  longs : Std.HashSet String := {}
  /-- Accumulated distinct short flag characters. -/
  shorts : Std.HashSet Char := {}
  /-- Accumulated distinct environment variable keys. -/
  envKeys : Std.HashSet String := {}
  /-- Inherited effective version string. -/
  effVer : Option String := none

/-- Ghost sum of `sizeOf node` over the remaining worklist items for structural termination. -/
noncomputable def validWorklistMeasure (wl : List (CommandSpec × ValidCtx)) : Nat :=
  wl.foldl (fun acc p => acc + sizeOf p.1) 0

/-- Push child subcommands onto `acc` under inherited context `ctx` without stack recursion. -/
def pushValidChildren (subs : List CommandSpec) (ctx : ValidCtx)
    (acc : List (CommandSpec × ValidCtx)) : List (CommandSpec × ValidCtx) :=
  subs.foldl (fun wl s => (s, ctx) :: wl) acc

/-- Validate one `CommandSpec` node incrementally against `ctx`, returning child `ValidCtx` on success. -/
def checkCommandNodeStep (node : CommandSpec) (ctx : ValidCtx) : Option ValidCtx :=
  match node with
  | ⟨name, version, _, shortHelp, shortVersion, options, args, subcommands⟩ =>
    let effVer := version <|> ctx.effVer
    let optNames? :=
      if options.isEmpty then some ctx.optNames
      else insertDistinctSet ctx.optNames (options.map (·.name))
    let longs? :=
      if options.isEmpty then some ctx.longs
      else insertDistinctSet ctx.longs (collectLongsTR options)
    let shorts? :=
      if options.isEmpty then some ctx.shorts
      else insertDistinctSet ctx.shorts (options.filterMap (·.short))
    let envKeys? :=
      if options.isEmpty then some ctx.envKeys
      else insertDistinctSet ctx.envKeys (options.filterMap (·.envVar))
    match optNames?, longs?, shorts?, envKeys? with
    | some optNames', some longs', some shorts', some envKeys' =>
      let ok :=
        Model.isValidCommandName name &&
        options.all Model.isValidOptLocal &&
        (!shortHelp || !shorts'.contains 'h') &&
        (!(shortVersion && effVer.isSome) || !shorts'.contains 'V') &&
        args.all Model.isValidArg &&
        (insertDistinctSet ({} : Std.HashSet String) (args.map (·.name))).isSome &&
        args.all (fun a => !optNames'.contains a.name) &&
        Model.validArgOrder false false args &&
        (if subcommands.isEmpty then true else args.isEmpty && options.all (·.global)) &&
        (insertDistinctSet ({} : Std.HashSet String) (subcommands.map (·.name))).isSome
      if ok then
        some { optNames := optNames', longs := longs', shorts := shorts', envKeys := envKeys', effVer := effVer }
      else
        none
    | _, _, _, _ => none

/-- Helper identity for `validWorklistMeasure` on cons. -/
theorem validWorklistMeasure_cons (p : CommandSpec × ValidCtx) (wl : List (CommandSpec × ValidCtx)) :
    validWorklistMeasure (p :: wl) = sizeOf p.1 + validWorklistMeasure wl := by
  unfold validWorklistMeasure
  have h : ∀ (xs : List (CommandSpec × ValidCtx)) (n : Nat),
      xs.foldl (fun acc q => acc + sizeOf q.1) n =
      n + xs.foldl (fun acc q => acc + sizeOf q.1) 0 := by
    intro xs
    induction xs with
    | nil => intro n; simp
    | cons x rest ih =>
      intro n
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ih (n + sizeOf x.1), ih (sizeOf x.1), Nat.add_assoc]
  simp only [List.foldl_cons, Nat.zero_add]
  exact h wl (sizeOf p.1)

/-- Helper bound for `validWorklistMeasure` after pushing subcommands. -/
theorem validWorklistMeasure_pushChildren (subs : List CommandSpec) (ctx : ValidCtx)
    (acc : List (CommandSpec × ValidCtx)) :
    validWorklistMeasure (pushValidChildren subs ctx acc) ≤ sizeOf subs + validWorklistMeasure acc := by
  unfold pushValidChildren
  induction subs generalizing acc with
  | nil => simp
  | cons s rest ih =>
    simp only [List.foldl_cons]
    have h1 := ih ((s, ctx) :: acc)
    rw [validWorklistMeasure_cons] at h1
    dsimp only at h1
    have hSize : sizeOf (s :: rest) = 1 + sizeOf s + sizeOf rest := by simp
    omega

/-- Helper bound showing `sizeOf node.subcommands < sizeOf node`. -/
theorem sizeOf_subcommands_lt_node (node : CommandSpec) :
    sizeOf node.subcommands < sizeOf node := by
  cases node
  simp [CommandSpec.mk.sizeOf_spec]
  omega

/-- Iterative stack-safe worklist loop equivalent to `Model.isValidCommandNode`. -/
def isValidSpecWorklist : List (CommandSpec × ValidCtx) → Bool
  | [] => true
  | (node, ctx) :: rest =>
    match checkCommandNodeStep node ctx with
    | none => false
    | some nextCtx =>
      isValidSpecWorklist (pushValidChildren node.subcommands nextCtx rest)
termination_by wl => validWorklistMeasure wl
decreasing_by
  have h1 := validWorklistMeasure_pushChildren node.subcommands nextCtx rest
  have h2 := validWorklistMeasure_cons (node, ctx) rest
  have h3 := sizeOf_subcommands_lt_node node
  dsimp only at h2
  omega

/-- Iterative, stack-safe, incremental-distinctness equivalent of `Model.isValidSpec`. -/
def isValidSpecTR (spec : CommandSpec) : Bool :=
  isValidSpecWorklist [(spec, {})]

/-- Tail-recursive flattening of reversed option chunks `chunksRev` into root-to-child declaration order. -/
def flattenChunksRev (chunksRev : List (List OptSpec)) : List OptSpec :=
  chunksRev.foldl (fun acc xs => xs.reverse.foldl (fun a x => x :: a) acc) []

/-- Stack-safe tail-recursive subcommand path lookup equivalent to `Model.findSubcommandPath`. -/
def findSubcommandPathTR (rootSpec : CommandSpec) (path : List String) :
    Except CmdLineError (List OptSpec × Option String × CommandSpec) :=
  go [] rootSpec.version rootSpec path
where
  go (globalsRev : List (List OptSpec)) (effVer : Option String) (cur : CommandSpec) :
      List String → Except CmdLineError (List OptSpec × Option String × CommandSpec)
    | [] => .ok (flattenChunksRev globalsRev, effVer, cur)
    | name :: rest =>
      match cur.subcommands.find? (fun s => s.name == name) with
      | some sub => go (cur.options :: globalsRev) (sub.version <|> effVer) sub rest
      | none =>
        .error { kind := .unknownSubcommand, message := s!"unknown subcommand '{name}'", target := some name }

/-- Build binary-squared radix ladder `[(10^(18*2^k), 18*2^k), ..., (10^18, 18)]` up to `n`. -/
def buildPow10Ladder (n : Nat) : Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, acc => acc
  | fuel + 1, b, w, acc =>
    if n < b then acc
    else buildPow10Ladder n fuel (b * b) (w + w) ((b, w) :: acc)

/-- Recursively split `n` along `buildPow10Ladder` down to 18-digit `< 10^18` chunks. -/
def pushNatChunks : List (Nat × Nat) → Bool → Nat → String → String
  | [], pad, n, acc =>
    let s := toString n
    if pad && s.length < 18 then
      acc ++ String.ofList (List.replicate (18 - s.length) '0') ++ s
    else
      acc ++ s
  | (bHalf, _) :: rest, pad, n, acc =>
    if !pad && n < bHalf then
      pushNatChunks rest false n acc
    else
      let acc1 := pushNatChunks rest pad (n / bHalf) acc
      pushNatChunks rest true (n % bHalf) acc1

/-- Convert `n` to decimal `String` using balanced `O(N log^2 N)` GMP divisions. -/
def natToStringFast (n : Nat) : String :=
  let base18 := 1000000000000000000
  if n < base18 then
    toString n
  else
    pushNatChunks (buildPow10Ladder n 32 base18 18 []) false n ""

/-- Fast equivalent of `Model.optValueToString` using `natToStringFast`. -/
def optValueToStringFast : OptValue → String
  | .string s => s
  | .bool b => if b then "true" else "false"
  | .nat n => natToStringFast n
  | .int (.ofNat n) => natToStringFast n
  | .int (.negSucc k) => "-" ++ natToStringFast (k + 1)
  | .choice s => s
  | .custom s => s

/-- Tail-recursive value renderer for `Model.renderSingleOpt` on repeatable or non-boolean options. -/
def renderValueListTR (opt : OptSpec) : List OptValue → List String → Except CmdLineError (List String)
  | [], accRev => .ok accRev.reverse
  | v :: vs, accRev =>
    if opt.kind == .bool && v != .bool true then
      .error
        { kind := .invalidValue
          message := s!"repeatable boolean option '{opt.name}' cannot render false value"
          target := some opt.name }
    else
      match opt.long with
      | some l =>
        let tok := if opt.kind == .bool then "--" ++ l else "--" ++ l ++ "=" ++ optValueToStringFast v
        renderValueListTR opt vs (tok :: accRev)
      | none =>
        match opt.short with
        | some c =>
          if opt.kind == .bool then
            renderValueListTR opt vs (("-" ++ String.singleton c) :: accRev)
          else
            renderValueListTR opt vs (optValueToStringFast v :: ("-" ++ String.singleton c) :: accRev)
        | none =>
          .error { kind := .invalidSpec, message := s!"option '{opt.name}' has neither long nor short flag" }

/-- Tail-recursive equivalent of `Model.renderSingleOpt`. -/
def renderSingleOptTR (opt : OptSpec) (vals : List OptValue) : Except CmdLineError (List String) :=
  if vals.isEmpty then
    .ok []
  else if opt.kind == .bool && !opt.repeatable then
    Model.renderSingleOpt opt vals
  else
    renderValueListTR opt vals []

/-- Index `parsed.options` into a hash map preserving first-occurrence lookup semantics. -/
def buildParsedOptMap (opts : List (String × List OptValue)) : Std.HashMap String (List OptValue) :=
  opts.reverse.foldl (fun m p => m.insert p.1 p.2) {}

/-- Tail-recursive option-list token renderer for `renderArgsTR`. -/
def renderOptsTR (optMap : Std.HashMap String (List OptValue)) :
    List OptSpec → List String → Except CmdLineError (List String)
  | [], accRev => .ok accRev.reverse
  | opt :: rest, accRev =>
    let vals := optMap[opt.name]?.getD []
    match renderSingleOptTR opt vals with
    | .error e => .error e
    | .ok headToks => renderOptsTR optMap rest (headToks.reverse ++ accRev)

/-- Stack-safe tail-recursive equivalent of `Model.renderArgs`. -/
def renderArgsTR (spec : CommandSpec) (parsed : ParsedCmd) : Except CmdLineError (List String) := do
  if !isValidSpecTR spec then
    .error { kind := .invalidSpec, message := s!"invalid command spec '{spec.name}'" }
  else
    let (globals, _, targetSpec) ← findSubcommandPathTR spec parsed.subcommandPath
    if !targetSpec.subcommands.isEmpty then
      .error
        { kind := .missingArgument
          message := s!"command '{targetSpec.name}' requires a subcommand"
          target := some targetSpec.name }
    else
      let visibleOpts := globals ++ targetSpec.options
      let optTokens ← renderOptsTR (buildParsedOptMap parsed.options) visibleOpts []
      let posTokens :=
        if parsed.rawPositionals.any Model.startsWithDash then
          "--" :: parsed.rawPositionals
        else
          parsed.rawPositionals
      .ok (parsed.subcommandPath ++ optTokens ++ posTokens)

/-- Render help text for `rootSpec` at the given `subcommandPath`. -/
def renderHelp (rootSpec : CommandSpec) (subcommandPath : List String := []) :
    Except CmdLineError String := do
  if !isValidSpecTR rootSpec then
    .error { kind := .invalidSpec, message := s!"invalid command spec '{rootSpec.name}'" }
  else
    let (globals, effVer, targetSpec) ← findSubcommandPathTR rootSpec subcommandPath
    .ok (renderHelpNode (rootSpec.name :: subcommandPath) (globals ++ targetSpec.options) effVer targetSpec)

/-- Prepend a parsed `OptValue` to `cliOpts` under `name` using a tail-recursive outer walk. -/
def recordCliOpt (cliOpts : List (String × List OptValue)) (name : String) (v : OptValue) :
    List (String × List OptValue) :=
  go [] cliOpts
where
  go (accRev : List (String × List OptValue)) :
      List (String × List OptValue) → List (String × List OptValue)
    | [] => accRev.reverse ++ [(name, [v])]
    | (k, vs) :: rest =>
      if k == name then
        accRev.reverse ++ ((k, v :: vs) :: rest)
      else
        go ((k, vs) :: accRev) rest

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
            let v ← match parseOptValueWithFast opt.kind rawVal validators with
              | .error e => .error { e with target := some opt.name }
              | .ok v => .ok v
            .ok (recordCliOpt cliOpts opt.name v, none)
          else
            .ok (cliOpts, some opt)

/-- Execute one left-to-right token transition on `ParseState` (non-recursive). -/
def stepToken (rootName : String) (validators : CustomValidators) (st : ParseState)
    (tok : String) : Except CmdLineError ParseState :=
  match st.pendingOpt with
  | some opt => do
    let v ← match parseOptValueWithFast opt.kind tok validators with
      | .error e => .error { e with target := some opt.name }
      | .ok v => .ok v
    .ok { st with pendingOpt := none, cliOpts := recordCliOpt st.cliOpts opt.name v }
  | none =>
    if st.afterDashDash then
      .ok { st with rawPositionals := tok :: st.rawPositionals }
    else if tok == "--" then
      .ok { st with afterDashDash := true }
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
                  .ok { st with cliOpts := recordCliOpt st.cliOpts opt.name (.bool false) }
              else if opt.kind == .bool then
                match eqVal? with
                | none =>
                  .ok { st with cliOpts := recordCliOpt st.cliOpts opt.name (.bool true) }
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
                      .ok { st with cliOpts := recordCliOpt st.cliOpts opt.name (.bool b) }
                  | .ok _ => .error { kind := .invalidValue, message := "invalid boolean", target := some opt.name }
              else
                match eqVal? with
                | some rawVal => do
                  let v ← match parseOptValueWithFast opt.kind rawVal validators with
                    | .error e => .error { e with target := some opt.name }
                    | .ok v => .ok v
                  .ok { st with cliOpts := recordCliOpt st.cliOpts opt.name v }
                | none =>
                  .ok { st with pendingOpt := some opt }
        | '-' :: c :: shortRest => do
          let (nextCliOpts, nextPending) ←
            parseShortBundle visibleOpts st.curSpec.shortHelp st.curSpec.shortVersion
              rootName st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c :: shortRest)
          .ok { st with cliOpts := nextCliOpts, pendingOpt := nextPending }
        | _ =>
          if !st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty then
            match st.curSpec.subcommands.find? (fun s => s.name == tok) with
            | some sub =>
              .ok
                { curSpec := sub
                  subPath := st.subPath ++ [sub.name]
                  inheritedGlobals := st.inheritedGlobals ++ st.curSpec.options
                  effectiveVersion := sub.version <|> st.effectiveVersion
                  afterDashDash := false
                  pendingOpt := none
                  cliOpts := st.cliOpts
                  rawPositionals := [] }
            | none =>
              let hint := match bestSuggestion tok (st.curSpec.subcommands.map (·.name)) with
                | some cand => s!"; did you mean '{cand}'?"
                | none => ""
              .error
                { kind := .unknownSubcommand
                  message := s!"unknown subcommand '{tok}'{hint}"
                  target := some tok }
          else
            .ok { st with rawPositionals := tok :: st.rawPositionals }

/-- Fold `stepToken` over `tokens` left-to-right via structural recursion. -/
def parseTokensLoop (rootName : String) (validators : CustomValidators) (st : ParseState) :
    List String → Except CmdLineError ParseState
  | [] => .ok st
  | tok :: rest => do
    let st' ← stepToken rootName validators st tok
    parseTokensLoop rootName validators st' rest

/-- Parse a token list left-to-right, rejecting a dangling `pendingOpt` and restoring forward order. -/
def parseTokens (rootName : String) (validators : CustomValidators) (st : ParseState)
    (tokens : List String) : Except CmdLineError ParseState := do
  let finalSt ← parseTokensLoop rootName validators st tokens
  match finalSt.pendingOpt with
  | some opt =>
    .error
      { kind := .missingArgument
        message := s!"option '{opt.name}' requires a value"
        target := some opt.name }
  | none =>
    .ok
      { finalSt with
        cliOpts := finalSt.cliOpts.map (fun p => (p.1, p.2.reverse))
        rawPositionals := finalSt.rawPositionals.reverse }

/-- Lookup-parameterized tail-recursive option resolution matching `Model.resolveOptions`. -/
def resolveOptionsTRWith {m : Type → Type} [Monad m]
    (getEnv : String → m (Except CmdLineError (Option String)))
    (visibleOpts : List OptSpec) (getCliVals : String → List OptValue)
    (validators : CustomValidators := []) :
    m (Except CmdLineError (List (String × List OptValue))) :=
  go visibleOpts []
where
  go : List OptSpec → List (String × List OptValue) →
      m (Except CmdLineError (List (String × List OptValue)))
    | [], accRev => return .ok accRev.reverse
    | opt :: rest, accRev => do
      match ← resolveSingleOptionFast getEnv opt (getCliVals opt.name) validators with
      | .error e => return .error e
      | .ok resolved? =>
        match resolved? with
        | none => go rest accRev
        | some vals => go rest ((opt.name, vals) :: accRev)

/-- Tail-recursive equivalent of `Model.resolveOptions`. -/
def resolveOptionsTR {m : Type → Type} [Monad m]
    (getEnv : String → m (Except CmdLineError (Option String)))
    (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue))
    (validators : CustomValidators := []) :
    m (Except CmdLineError (List (String × List OptValue))) :=
  go visibleOpts []
where
  go : List OptSpec → List (String × List OptValue) →
      m (Except CmdLineError (List (String × List OptValue)))
    | [], accRev => return .ok accRev.reverse
    | opt :: rest, accRev => do
      let cliVals :=
        match cliOpts.find? (fun p => p.1 == opt.name) with
        | some p => p.2
        | none => []
      match ← resolveSingleOptionFast getEnv opt cliVals validators with
      | .error e => return .error e
      | .ok resolved? =>
        match resolved? with
        | none => go rest accRev
        | some vals => go rest ((opt.name, vals) :: accRev)

/-- Tail-recursive equivalent of `Model.resolveArgs`. -/
def resolveArgsTR (argSpecs : List ArgSpec) (rawPos : List String)
    (validators : CustomValidators := []) :
    Except CmdLineError (List (String × List OptValue)) :=
  go argSpecs rawPos []
where
  parseManyTR (arg : ArgSpec) (accRev : List OptValue) : List String → Except CmdLineError (List OptValue)
    | [] => .ok accRev.reverse
    | s :: ss =>
      match parseOptValueWithFast arg.kind s validators with
      | .error e => .error { e with target := some arg.name }
      | .ok v => parseManyTR arg (v :: accRev) ss
  go : List ArgSpec → List String → List (String × List OptValue) →
      Except CmdLineError (List (String × List OptValue))
    | [], [], accRev => .ok accRev.reverse
    | [], extra :: _, _ =>
      .error
        { kind := .unexpectedArgument
          message := s!"unexpected argument '{extra}'"
          target := some extra }
    | arg :: restArgs, pos, accRev =>
      if arg.variadic then
        if pos.isEmpty then
          if arg.required then
            .error
              { kind := .missingArgument
                message := s!"missing required argument '{arg.name}'"
                target := some arg.name }
          else
            match arg.default with
            | some d =>
              match parseOptValueWithFast arg.kind d validators with
              | .error e => .error { e with target := some arg.name }
              | .ok v => go restArgs [] ((arg.name, [v]) :: accRev)
            | none => go restArgs [] accRev
        else
          match parseManyTR arg [] pos with
          | .error e => .error e
          | .ok vs => go restArgs [] ((arg.name, vs) :: accRev)
      else
        match pos with
        | s :: remPos =>
          match parseOptValueWithFast arg.kind s validators with
          | .error e => .error { e with target := some arg.name }
          | .ok v => go restArgs remPos ((arg.name, [v]) :: accRev)
        | [] =>
          if arg.required then
            .error
              { kind := .missingArgument
                message := s!"missing required argument '{arg.name}'"
                target := some arg.name }
          else
            match arg.default with
            | some d =>
              match parseOptValueWithFast arg.kind d validators with
              | .error e => .error { e with target := some arg.name }
              | .ok v => go restArgs [] ((arg.name, [v]) :: accRev)
            | none => go restArgs [] accRev

/-- Hash-indexed traversal state avoiding quadratic `++` and linear scans on huge specs. -/
structure FastParseState where
  /-- Currently active command or subcommand specification. -/
  curSpec : CommandSpec
  /-- Reversed subcommand path relative to root. -/
  subPathRev : List String := []
  /-- Reversed list of visible option chunks ordered child-to-root. -/
  visibleChunksRev : List (List OptSpec) := []
  /-- Effective version inherited from ancestors or overridden on `curSpec`. -/
  effectiveVersion : Option String := none
  /-- Whether `--` end-of-options marker has been encountered. -/
  afterDashDash : Bool := false
  /-- Option awaiting its separated value from the next token, if any. -/
  pendingOpt : Option OptSpec := none
  /-- Collected CLI option occurrences keyed by `OptSpec.name` (values in reverse). -/
  cliMap : Std.HashMap String (List OptValue) := {}
  /-- Reversed raw positional arguments. -/
  rawPositionalsRev : List String := []
  /-- Pre-indexed long-flag lookup table mapping `l` -> `(opt, false)` and `"no-" ++ l` -> `(opt, true)`. -/
  longMap : Std.HashMap String (OptSpec × Bool) := {}
  /-- Pre-indexed short-flag lookup table mapping `c` -> `opt`. -/
  shortMap : Std.HashMap Char OptSpec := {}

/-- Insert `opts` into `longMap` and `shortMap` in declaration order. -/
def addOptsMaps (longMap : Std.HashMap String (OptSpec × Bool)) (shortMap : Std.HashMap Char OptSpec) :
    List OptSpec → Std.HashMap String (OptSpec × Bool) × Std.HashMap Char OptSpec
  | [] => (longMap, shortMap)
  | opt :: rest =>
    let lm1 :=
      match opt.long with
      | none => longMap
      | some l =>
        let lm0 := longMap.insert l (opt, false)
        if opt.kind == .bool && !opt.repeatable then lm0.insert ("no-" ++ l) (opt, true) else lm0
    let sm1 :=
      match opt.short with
      | none => shortMap
      | some c => shortMap.insert c opt
    addOptsMaps lm1 sm1 rest

/-- Prepend parsed value `v` to `cliMap[name]` in `O(1)` amortized time. -/
def recordCliFast (cliMap : Std.HashMap String (List OptValue)) (name : String) (v : OptValue) :
    Std.HashMap String (List OptValue) :=
  cliMap.alter name fun
    | none => some [v]
    | some vs => some (v :: vs)

/-- Build initial `FastParseState` for `spec`. -/
def initFastState (spec : CommandSpec) : FastParseState :=
  let (lm, sm) := addOptsMaps {} {} spec.options
  { curSpec := spec
    visibleChunksRev := [spec.options]
    effectiveVersion := spec.version
    longMap := lm
    shortMap := sm }

/-- Fast `O(1)`-indexed equivalent of `parseShortBundle`. -/
def parseShortBundleFast (shortMap : Std.HashMap Char OptSpec) (shortHelp shortVersion : Bool)
    (rootName : String) (st : FastParseState) (validators : CustomValidators)
    (cliMap : Std.HashMap String (List OptValue)) :
    List Char → Except CmdLineError (Std.HashMap String (List OptValue) × Option OptSpec)
  | [] => .ok (cliMap, none)
  | c :: cs =>
    if c == 'h' && shortHelp then
      .error
        { kind := .helpRequested
          message := renderHelpNode (rootName :: st.subPathRev.reverse) (flattenChunksRev st.visibleChunksRev) st.effectiveVersion st.curSpec }
    else if c == 'V' && shortVersion && st.effectiveVersion.isSome then
      match st.effectiveVersion with
      | some v => .error { kind := .versionRequested, message := renderVersion rootName v }
      | none => .error { kind := .unknownOption, message := "unknown option '-V'", target := some "-V" }
    else
      match shortMap[c]? with
      | none =>
        .error
          { kind := .unknownOption
            message := s!"unknown option '-{c}'"
            target := some s!"-{c}" }
      | some opt =>
        if opt.kind == .bool then
          parseShortBundleFast shortMap shortHelp shortVersion rootName st validators
            (recordCliFast cliMap opt.name (.bool true)) cs
        else
          if !cs.isEmpty then do
            let rawVal := String.ofList cs
            let v ← match parseOptValueWithFast opt.kind rawVal validators with
              | .error e => .error { e with target := some opt.name }
              | .ok v => .ok v
            .ok (recordCliFast cliMap opt.name v, none)
          else
            .ok (cliMap, some opt)

/-- Fast `O(1)`-indexed single-token transition matching `stepToken`. -/
def stepTokenFast (rootName : String) (validators : CustomValidators) (st : FastParseState)
    (tok : String) : Except CmdLineError FastParseState :=
  match st.pendingOpt with
  | some opt => do
    let v ← match parseOptValueWithFast opt.kind tok validators with
      | .error e => .error { e with target := some opt.name }
      | .ok v => .ok v
    .ok { st with pendingOpt := none, cliMap := recordCliFast st.cliMap opt.name v }
  | none =>
    if st.afterDashDash then
      .ok { st with rawPositionalsRev := tok :: st.rawPositionalsRev }
    else if tok == "--" then
      .ok { st with afterDashDash := true }
    else if tok == "--help" then
      .error
        { kind := .helpRequested
          message := renderHelpNode (rootName :: st.subPathRev.reverse) (flattenChunksRev st.visibleChunksRev) st.effectiveVersion st.curSpec }
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
          match st.longMap[namePart]? with
          | none =>
            let visibleOpts := flattenChunksRev st.visibleChunksRev
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
                .ok { st with cliMap := recordCliFast st.cliMap opt.name (.bool false) }
            else if opt.kind == .bool then
              match eqVal? with
              | none =>
                .ok { st with cliMap := recordCliFast st.cliMap opt.name (.bool true) }
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
                    .ok { st with cliMap := recordCliFast st.cliMap opt.name (.bool b) }
                | .ok _ => .error { kind := .invalidValue, message := "invalid boolean", target := some opt.name }
            else
              match eqVal? with
              | some rawVal => do
                let v ← match parseOptValueWithFast opt.kind rawVal validators with
                  | .error e => .error { e with target := some opt.name }
                  | .ok v => .ok v
                .ok { st with cliMap := recordCliFast st.cliMap opt.name v }
              | none =>
                .ok { st with pendingOpt := some opt }
      | '-' :: c :: shortRest =>
        match parseShortBundleFast st.shortMap st.curSpec.shortHelp st.curSpec.shortVersion
            rootName st validators st.cliMap (c :: shortRest) with
        | .error e => .error e
        | .ok (nextCliMap, nextPending) =>
          .ok { st with cliMap := nextCliMap, pendingOpt := nextPending }
      | _ =>
        if !st.curSpec.subcommands.isEmpty && st.rawPositionalsRev.isEmpty then
          match st.curSpec.subcommands.find? (fun s => s.name == tok) with
          | some sub =>
            let (lm', sm') := addOptsMaps st.longMap st.shortMap sub.options
            .ok
              { curSpec := sub
                subPathRev := sub.name :: st.subPathRev
                visibleChunksRev := sub.options :: st.visibleChunksRev
                effectiveVersion := sub.version <|> st.effectiveVersion
                afterDashDash := false
                pendingOpt := none
                cliMap := st.cliMap
                rawPositionalsRev := []
                longMap := lm'
                shortMap := sm' }
          | none =>
            let hint := match bestSuggestion tok (st.curSpec.subcommands.map (·.name)) with
              | some cand => s!"; did you mean '{cand}'?"
              | none => ""
            .error
              { kind := .unknownSubcommand
                message := s!"unknown subcommand '{tok}'{hint}"
                target := some tok }
        else
          .ok { st with rawPositionalsRev := tok :: st.rawPositionalsRev }

/-- Tail-recursive fast token-list transition loop. -/
def parseTokensLoopFast (rootName : String) (validators : CustomValidators) (st : FastParseState) :
    List String → Except CmdLineError FastParseState
  | [] => .ok st
  | tok :: rest =>
    match stepTokenFast rootName validators st tok with
    | .error e => .error e
    | .ok st' => parseTokensLoopFast rootName validators st' rest

/-- Fast hash-indexed equivalent of `parseTokens`. -/
def parseTokensFast (rootName : String) (validators : CustomValidators) (st : FastParseState)
    (tokens : List String) : Except CmdLineError FastParseState :=
  match parseTokensLoopFast rootName validators st tokens with
  | .error e => .error e
  | .ok finalSt =>
    match finalSt.pendingOpt with
    | some opt =>
      .error
        { kind := .missingArgument
          message := s!"option '{opt.name}' requires a value"
          target := some opt.name }
    | none => .ok finalSt

/-- List-based specification parser used as proof reference for `parseWithEnvM`. -/
def parseWithEnvSpecM {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec)
    (args : List String) (validators : CustomValidators := []) :
    m (Except CmdLineError ParsedCmd) := do
  if !isValidSpecTR spec then
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
        match ← resolveOptionsTR ops.getEnv visibleOpts finalState.cliOpts validators with
        | .error e => return .error e
        | .ok resolvedOpts =>
          match resolveArgsTR finalState.curSpec.args finalState.rawPositionals validators with
          | .error e => return .error e
          | .ok resolvedArgs =>
            return .ok
              { subcommandPath := finalState.subPath
                options := resolvedOpts
                args := resolvedArgs
                rawPositionals := finalState.rawPositionals }

/-- Parse `args` against `spec` using `ops.getEnv` fallback and `validators`. -/
def parseWithEnvM {m : Type → Type} [Monad m] (ops : CliOpsM m) (spec : CommandSpec)
    (args : List String) (validators : CustomValidators := []) :
    m (Except CmdLineError ParsedCmd) := do
  if !isValidSpecTR spec then
    return .error { kind := .invalidSpec, message := s!"invalid command spec '{spec.name}'" }
  else
    match parseTokensFast spec.name validators (initFastState spec) args with
    | .error e => return .error e
    | .ok finalState =>
      let rawPos := finalState.rawPositionalsRev.reverse
      if !finalState.curSpec.subcommands.isEmpty then
        if !rawPos.isEmpty then
          let firstPos := rawPos.headD ""
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
        let visibleOpts := flattenChunksRev finalState.visibleChunksRev
        let getCli := fun name => (finalState.cliMap[name]?.getD []).reverse
        match ← resolveOptionsTRWith ops.getEnv visibleOpts getCli validators with
        | .error e => return .error e
        | .ok resolvedOpts =>
          match resolveArgsTR finalState.curSpec.args rawPos validators with
          | .error e => return .error e
          | .ok resolvedArgs =>
            return .ok
              { subcommandPath := finalState.subPathRev.reverse
                options := resolvedOpts
                args := resolvedArgs
                rawPositionals := rawPos }

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
  { isValidSpec := isValidSpecTR
    parse := parse
    parseWith := fun spec args validators => parseWith spec args validators
    parseWithEnv := fun spec args validators => parseWithEnvM ops spec args validators
    renderHelp := fun rootSpec path => renderHelp rootSpec path
    renderVersion := renderVersion
    renderArgs := renderArgsTR
    promptLine := fun prompt default => promptLine ops prompt default
    confirm := fun prompt default maxAttempts => confirm ops prompt default maxAttempts
    runCli := fun spec args handler => runCli ops spec args handler
    runCliWith := fun spec args validators handler => runCliWith ops spec args validators handler }

/-- Strip trailing `\r` and `\n` characters from a line read via `IO.FS.Stream.getLine`. -/
def stripTrailingNewline (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == '\n' || c == '\r')).reverse

end LeanSwe.CmdLine.Internal
