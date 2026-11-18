import Lean

/-!
Promise coverage audit for `lean-swe` compiled `.olean` artifacts.

Checks:
1. Every `LeanSwe/**/SpecTests.lean` and `LeanSwe/**/SpecMutants.lean` file on disk is
   transitively imported by `LeanSwe`.
2. Zero custom `axiom` declarations exist in `Core` or `LeanSwe`.
3. Every `SpecTests` module has a companion `SpecMutants` module containing at least one
   `Core.AllPass` mutant theorem/example, and no `SpecTests` module contains any theorem,
   `example`, or `Core.AllPass` reference.
4. Every public `test_*` (and non-legacy `empirical_*`) declaration in a `SpecTests` module has
   a public, non-projection theorem outside `SpecTests`, `SpecMutants`, and `RuntimeTests` whose
   conclusion is `Core.AllPass` applied to that promise, plus one with `Core.CanReach` when the
   promise uses `Core.NondetTest.assume`.
5. Qualifying theorems have no hypothesis (`Prop` binder) and all qualifying theorems plus all
   `SpecMutants` declarations/examples use only standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`) with zero `sorry`/`admit`/`native_decide`.
-/

open Lean Meta

private def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4 |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

private def legacyEmpiricalModules : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 0

private def timeRandAuditModules : Array Name := #[
  `LeanSwe.LinuxSyscall.TimeRand.Types,
  `LeanSwe.LinuxSyscall.TimeRand.Model,
  `LeanSwe.LinuxSyscall.TimeRand.Impl,
  `LeanSwe.LinuxSyscall.TimeRand.Interface,
  `LeanSwe.LinuxSyscall.TimeRand.SpecTests,
  `LeanSwe.LinuxSyscall.TimeRand.Proofs
]

private def isProjectModule (m : Name) : Bool :=
  let r := m.getRoot
  r == `Core || r == `LeanSwe

private def nameLastStr (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => ""

private def isAllowedTimeRandClosureModule (m : Name) : Bool :=
  m.getRoot == `Core ||
    m.components.take 3 == [`LeanSwe, `LinuxSyscall, `Common] ||
    timeRandAuditModules.contains m

private def allowedTimeRandExterns : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4
    |>.insert `rawClockGettime
    |>.insert `rawClockNanosleep
    |>.insert `rawGetrandom

private def checkTimeRandTrustedClosure : IO (Array String) := do
  let trEnv ← importModules (timeRandAuditModules.map fun m => { module := m }) {} (loadExts := false)
  let mut errs : Array String := #[]
  for m in trEnv.header.moduleNames do
    if isProjectModule m && !isAllowedTimeRandClosureModule m then
      errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_IMPORT: {m} imported into TimeRand closure"
  let mut visited : Std.HashSet Name := {}
  let mut queue : Array (Name × Name) := #[]
  for h : i in [0 : trEnv.header.moduleNames.size] do
    let m := trEnv.header.moduleNames[i]
    if timeRandAuditModules.contains m then
      let some data := trEnv.header.moduleData[i]? | continue
      for c in data.constants do
        queue := queue.push (m, c.name)
  while !queue.isEmpty do
    let (originMod, cName) := queue.back!
    queue := queue.pop
    if visited.contains cName then
      continue
    visited := visited.insert cName
    let some cinfo := trEnv.find? cName | continue
    if cinfo matches .axiomInfo _ then
      if !allowedAxioms.contains cName then
        errs := errs.push s!"TRUSTED_CLOSURE_AXIOM_FORBIDDEN: {cName} reachable from {originMod}"
      continue
    let cMod := trEnv.getModuleIdxFor? cName |>.bind (trEnv.header.moduleNames[·]?) |>.getD .anonymous
    if isProjectModule cMod then
      if !isAllowedTimeRandClosureModule cMod then
        errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_MODULE: {cName} in {cMod} reachable from {originMod}"
      if cinfo matches .opaqueInfo _ || (getExternAttrData? trEnv cName).isSome then
        let short := Name.mkSimple (nameLastStr cName)
        if cMod != `LeanSwe.LinuxSyscall.TimeRand.Interface || !allowedTimeRandExterns.contains short then
          errs := errs.push s!"TRUSTED_CLOSURE_UNALLOWED_EXTERN: {cName} in {cMod} reachable from {originMod}"
    for u in cinfo.type.getUsedConstants do
      if !visited.contains u then
        queue := queue.push (originMod, u)
    let val? := match cinfo with
      | .defnInfo v => some v.value
      | .thmInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some val := val? then
      for u in val.getUsedConstants do
        if !visited.contains u then
          queue := queue.push (originMod, u)
    let extra : List Name := match cinfo with
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | .inductInfo v => v.all ++ v.ctors
      | _ => []
    for u in extra do
      if !visited.contains u then
        queue := queue.push (originMod, u)
  return errs

private structure AxCache where
  safe : Std.HashSet Name := {}
  bad : Std.HashMap Name Name := {}
  inStack : Std.HashSet Name := {}

private partial def findBadAxiom (env : Environment) (cName : Name) : StateM AxCache (Option Name) := do
  if allowedAxioms.contains cName then return none
  let st ← get
  if st.safe.contains cName || st.inStack.contains cName then return none
  if let some b := st.bad.get? cName then return some b
  let some cinfo := env.find? cName | do
    modify fun s => { s with safe := s.safe.insert cName }
    return none
  if cinfo matches .axiomInfo _ then
    modify fun s => { s with bad := s.bad.insert cName cName }
    return some cName
  modify fun s => { s with inStack := s.inStack.insert cName }
  let mut foundBad : Option Name := none
  for u in cinfo.type.getUsedConstants do
    if let some b ← findBadAxiom env u then
      foundBad := some b
      break
  if foundBad.isNone then
    let val? := match cinfo with
      | .defnInfo v => some v.value
      | .thmInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    if let some val := val? then
      for u in val.getUsedConstants do
        if let some b ← findBadAxiom env u then
          foundBad := some b
          break
  if foundBad.isNone then
    let extra : List Name := match cinfo with
      | .ctorInfo v => [v.induct]
      | .recInfo v => v.all
      | .inductInfo v => v.all ++ v.ctors
      | _ => []
    for u in extra do
      if let some b ← findBadAxiom env u then
        foundBad := some b
        break
  modify fun s => { s with inStack := s.inStack.erase cName }
  if let some b := foundBad then
    modify fun s => { s with bad := s.bad.insert cName b }
    return some b
  modify fun s => { s with safe := s.safe.insert cName }
  return none

private def checkAxiomsOk (cName : Name) : StateT AxCache CoreM (Option String) := do
  let env ← getEnv
  let (b?, st) := (findBadAxiom env cName).run (← get)
  set st
  if b?.isNone then return none
  let axioms ← Lean.collectAxioms cName
  let bad := axioms.filter fun ax => !allowedAxioms.contains ax
  if bad.isEmpty then return none
  else return some (String.intercalate ", " (bad.toList.map (·.toString)))

private def isPrivateOrInternal (n : Name) : Bool :=
  isPrivateName n || n.isInternalOrNum

private def isMutantModule (m : Name) : Bool :=
  nameLastStr m == "SpecMutants" || m.components.contains `SpecMutants

private def isCompilerAuxThm (env : Environment) (n : Name) : Bool :=
  let s := nameLastStr n
  let pref := n.getPrefix
  env.contains pref &&
    (s == "inj" || s == "injEq" || s == "sizeOf_spec" || s == "noConfusion" ||
      s == "noConfusionType" || s == "eq_def" ||
      (s.startsWith "eq_" && (s.drop 3).all Char.isDigit) ||
      (s.startsWith "_proof_" && (s.drop 7).all Char.isDigit))

private def moduleToFilePath (repoDir : System.FilePath) (modName : Name) : System.FilePath :=
  let parts := modName.components.map (·.toString)
  (parts.foldl (fun p seg => p / seg) repoDir).withExtension "lean"

private def moduleToIleanPath (libDir : System.FilePath) (modName : Name) : System.FilePath :=
  let parts := modName.components.map (·.toString)
  (parts.foldl (fun p seg => p / seg) libDir).withExtension "ilean"

private def stripRootPrefix (s : String) : String :=
  if s.startsWith "_root_." then (s.drop 7).toString else s

private partial def hasIdentOrAtom (pred : String → Bool) (stx : Syntax) : Bool :=
  match stx with
  | .ident _ _ val _ =>
    let raw := val.toString
    pred raw || pred (stripRootPrefix raw) || pred (nameLastStr val)
  | .atom _ val => pred val || pred (stripRootPrefix val)
  | .node _ _ args => args.any (hasIdentOrAtom pred)
  | .missing => false

private partial def hasSyntaxKind (k : Name) (stx : Syntax) : Bool :=
  if stx.getKind == k then true
  else match stx with
  | .node _ _ args => args.any (hasSyntaxKind k)
  | _ => false

private partial def findSyntaxKind? (k : Name) (stx : Syntax) : Option Syntax :=
  if stx.getKind == k then some stx
  else match stx with
  | .node _ _ args => args.findSome? (findSyntaxKind? k)
  | _ => none

private def isAllPassToken (s : String) : Bool :=
  s == "AllPass" || s == "Core.AllPass"

private def isForbiddenMutantToken (s : String) : Bool :=
  s == "sorry" || s == "admit" || s == "sorryAx" || s == "native_decide" ||
    s == "Lean.ofReduceBool" || s == "Lean.ofReduceNat" ||
    s == "Lean.trustCompiler" || s == "unsafe"

private def forbiddenIleanMutantRefs : Array String :=
  #["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler",
    "Lean.Parser.Tactic.DecideConfig.native"]

private def forbiddenMetaSyntaxKinds : Array Name :=
  #[``Lean.Parser.Command.macro, ``Lean.Parser.Command.macro_rules,
    ``Lean.Parser.Command.elab, ``Lean.Parser.Command.elab_rules,
    ``Lean.Parser.Command.syntax, ``Lean.Parser.Command.notation,
    ``Lean.Parser.Command.mixfix, ``Lean.Parser.Term.local,
    `Lean.runCmd, `Lean.runElab]

private partial def hasForbiddenAttr (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Attr.extern then true
  else if stx.getKind == ``Lean.Parser.Term.attrInstance then
    hasIdentOrAtom (fun s => s == "extern" || s == "implemented_by" || s == "csimp") stx
  else match stx with
  | .node _ _ args => args.any hasForbiddenAttr
  | _ => false

private partial def hasNativeTacticConfig (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Tactic.posConfigItem || stx.getKind == ``Lean.Parser.Tactic.configItem then
    hasIdentOrAtom (· == "native") stx
  else match stx with
  | .node _ _ args => args.any hasNativeTacticConfig
  | _ => false

private def checkForbiddenMetaOrAttr (path : System.FilePath) (stx : Syntax) : Option String :=
  if forbiddenMetaSyntaxKinds.any (hasSyntaxKind · stx) then
    some s!"FORBIDDEN_SYNTAX_EXT: {path} uses macro/elab/syntax/notation/local/run_cmd"
  else if hasForbiddenAttr stx then
    some s!"FORBIDDEN_ATTRIBUTE: {path} uses extern/implemented_by/csimp attribute"
  else if hasNativeTacticConfig stx then
    some s!"UNALLOWED_AXIOM_IN_MUTANT: {path} uses +native tactic configuration"
  else
    none

private def readIleanRefNames (ileanPath : System.FilePath) : IO (Except String (Array String)) := do
  unless ← ileanPath.pathExists do
    return .error s!"MISSING_ILEAN: {ileanPath}"
  let raw ← IO.FS.readFile ileanPath
  let .ok json := Json.parse raw
    | return .error s!"INVALID_ILEAN_JSON: {ileanPath}"
  let .ok (.obj refs) := json.getObjVal? "references"
    | return .error s!"INVALID_ILEAN_REFS: {ileanPath}"
  let mut names : Array String := #[]
  for (k, _) in refs do
    if let .ok kjson := Json.parse k then
      if let .ok cObj := kjson.getObjVal? "c" then
        if let .ok n := cObj.getObjValAs? String "n" then
          names := names.push n
  return .ok names

private partial def isNegatedAllPassExpr (e : Expr) : Bool :=
  let cur := e.consumeMData
  match cur with
  | .forallE _ dom body _ =>
    if body.consumeMData == .const ``False [] then
      dom.consumeMData.isAppOfArity `Core.AllPass 1
    else
      isNegatedAllPassExpr body
  | .letE _ _ _ body _ => isNegatedAllPassExpr body
  | .app (.const ``Not []) arg => arg.consumeMData.isAppOfArity `Core.AllPass 1
  | _ => false

private def rewriteExampleToAxiom (idx : Nat) (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Lean.Parser.Command.declaration && stx[1].getKind == ``Lean.Parser.Command.example then
    let exStx := stx[1]
    let optSig := exStx[1]
    let typeSpecNull := optSig[1]
    if typeSpecNull.isNone then none
    else
      let tySpec := typeSpecNull[0]
      let declId := Syntax.node .none ``Lean.Parser.Command.declId
        #[mkIdent (Name.mkSimple s!"_sigAudit_{idx}"), Syntax.node .none `null #[]]
      let declSig := Syntax.node .none ``Lean.Parser.Command.declSig #[optSig[0], tySpec]
      let axStx := Syntax.node .none ``Lean.Parser.Command.axiom #[mkAtom "axiom", declId, declSig]
      let privMods := Syntax.node .none ``Lean.Parser.Command.declModifiers #[
        Syntax.node .none `null #[],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[Syntax.node .none ``Lean.Parser.Command.private #[mkAtom "private"]],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[],
        Syntax.node .none `null #[]
      ]
      some (Syntax.node .none ``Lean.Parser.Command.declaration #[privMods, axStx])
  else
    none

private unsafe def countElaboratedNegatedAllPass
    (headEnv : Environment)
    (m : Name)
    (path : System.FilePath) : IO (Except String Nat) := do
  unless ← path.pathExists do
    return .error s!"MISSING_SOURCE_FILE: {path}"
  let input ← IO.FS.readFile path
  let ictx := Parser.mkInputContext input path.toString
  let (_header, pstate0, msgs0) ← Parser.parseHeader ictx
  let mut cmdState := Elab.Command.mkState (headEnv.setMainModule (m ++ `_SigAudit)) msgs0 {}
  let mut pstate := pstate0
  let mut modNeg := 0
  let mut idx := 0
  repeat do
    let scope := cmdState.scopes.head!
    let pmctx : Parser.ParserModuleContext := {
      env := cmdState.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls
    }
    let (stx, nextP, nextMsgs) := Parser.parseCommand ictx pmctx pstate cmdState.messages
    pstate := nextP
    cmdState := { cmdState with messages := nextMsgs }
    if Parser.isTerminalCommand stx then break
    let mut isEx := false
    let mut cmdToRun := stx
    if let some axCmd := rewriteExampleToAxiom (idx + 1) stx then
      idx := idx + 1
      isEx := true
      cmdToRun := axCmd
    else if stx.getKind == ``Lean.Parser.Command.declaration && stx[1].getKind == ``Lean.Parser.Command.theorem then
      let thmStx := stx[1]
      let declId := thmStx[1]
      let optSig := thmStx[2]
      let declSig := Syntax.node .none ``Lean.Parser.Command.declSig #[optSig[0], optSig[1]]
      let axStx := Syntax.node .none ``Lean.Parser.Command.axiom #[mkAtom "axiom", declId, declSig]
      cmdToRun := Syntax.node .none ``Lean.Parser.Command.declaration #[stx[0], axStx]
    let ((), nextCmdState) ←
      ((Elab.Command.elabCommand cmdToRun).run
        { fileName := path.toString, fileMap := ictx.fileMap, snap? := none, cancelTk? := none } |>.run cmdState)
        |>.toIO fun _ => IO.Error.userError s!"ELAB_ERROR in {m}"
    cmdState := nextCmdState
    if isEx then
      let cname := cmdState.scopes.head!.currNamespace ++ Name.mkSimple s!"_sigAudit_{idx}"
      let privName := mkPrivateName cmdState.env cname
      let c? := cmdState.env.find? privName |>.orElse fun _ => cmdState.env.find? cname
      if let some c := c? then
        if isNegatedAllPassExpr c.type then
          modNeg := modNeg + 1
  return .ok modNeg

private def parseModuleCommands (env : Environment) (path : System.FilePath) : IO (Except String (Array Syntax)) := do
  unless ← path.pathExists do
    return .error s!"MISSING_SOURCE_FILE: {path}"
  let input ← IO.FS.readFile path
  let ictx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader ictx
  if messages.hasErrors then
    return .error s!"PARSE_ERROR: header parse error in {path}"
  let mut cmds : Array Syntax := #[header]
  let mut pstate := parserState
  let mut msgs := messages
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  repeat do
    let (stx, nextState, nextMsgs) := Parser.parseCommand ictx pmctx pstate msgs
    pstate := nextState
    msgs := nextMsgs
    if Parser.isTerminalCommand stx then
      break
    cmds := cmds.push stx
  if msgs.hasErrors then
    return .error s!"PARSE_ERROR: command parse error in {path}"
  return .ok cmds

private partial def collectConclusionAtoms (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    collectConclusionAtoms e.appFn!.appArg! ++ collectConclusionAtoms e.appArg!
  else
    #[e]

private def usesAssumeTransitive
    (env : Environment)
    (start : Name) : Bool := Id.run do
  let mut queue : Array Name := #[start]
  let mut seen : Std.HashSet Name := {}
  while !queue.isEmpty do
    let cName := queue.back!
    queue := queue.pop
    if cName == `Core.NondetTest.assume then
      return true
    if seen.contains cName then
      continue
    seen := seen.insert cName
    if !isProjectModule (env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous) then
      continue
    let body? := match env.find? cName with
      | some (.defnInfo dv) => some dv.value
      | some (.opaqueInfo ov) => some ov.value
      | _ => none
    if let some body := body? then
      for u in body.getUsedConstants do
        if !seen.contains u then
          queue := queue.push u
  return false

private partial def extractUnconditionalAtoms (ty : Expr) : MetaM (Option (Array Expr)) := do
  let cur := ty.consumeMData
  if let .forallE n d b bi := cur then
    withLocalDecl n bi d fun x => do
      if ← isProp d then
        return none
      extractUnconditionalAtoms (b.instantiate1 x)
  else if let .letE _ _ v b _ := cur then
    extractUnconditionalAtoms (b.instantiate1 v)
  else
    return some (collectConclusionAtoms cur)

private def moduleNameUnderLeanSwe (leanSweDir entry : System.FilePath) : Name :=
  ((entry.withExtension "").components.drop leanSweDir.components.length).foldl
    (fun acc seg => if seg == "." || seg.isEmpty then acc else Name.str acc seg) `LeanSwe

/-- Audit compiled `.olean` artifacts reachable from `LeanSwe` for promise coverage. -/
unsafe def main (args : List String) : IO UInt32 := do
  let libDir : System.FilePath := args.headD ".lake/build/lib/lean"
  let repoDir : System.FilePath := match args.drop 1 with
    | r :: _ => r
    | [] => "."
  unless ← (libDir / "LeanSwe.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe ({libDir / "LeanSwe.olean"})"
    return 1
  initSearchPath (← findSysroot) [libDir]
  enableInitializersExecution
  let env ← importModules #[{ module := `LeanSwe }] {} (loadExts := true)
  let mut visited : Std.HashSet Name := {}
  for modName in env.header.moduleNames do
    if isProjectModule modName then
      visited := visited.insert modName

  let mut errors : Array String := #[]
  let leanSweDir := repoDir / "LeanSwe"
  if ← leanSweDir.pathExists then
    for entry in (← System.FilePath.walkDir leanSweDir) do
      if !(← entry.isDir) && entry.extension == some "lean" then
        let modName := moduleNameUnderLeanSwe leanSweDir entry
        if entry.fileName == some "SpecTests.lean" then
          if !visited.contains modName then
            errors := errors.push s!"UNIMPORTED_SPECTESTS: {entry} (module {modName} is not imported by LeanSwe)"
        else if isMutantModule modName then
          if !visited.contains modName then
            errors := errors.push s!"UNIMPORTED_SPECMUTANTS: {entry} (module {modName} is not imported by LeanSwe)"

  let mut specModCount := 0
  let mut specMods : Array Name := #[]
  let mut mutantModsWithAllPass : Std.HashSet Name := {}
  let mut sigAuditTasks : Array (Name × Task (Except IO.Error (Except String Nat))) := #[]
  let mut promises : Array (Name × Name) := #[]
  let mut promiseSet : Std.HashSet Name := {}
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if !isProjectModule m then continue
    let some data := env.header.moduleData[i]? | continue
    for c in data.constants do
      if let .axiomInfo _ := c then
        if !allowedAxioms.contains c.name then
          errors := errors.push s!"CUSTOM_AXIOM_FORBIDDEN: {c.name} in {m}"
    if m.getString! == "SpecTests" then
      specModCount := specModCount + 1
      specMods := specMods.push m
      let mut hasBadSpecConst := false
      for c in data.constants do
        let usedInType := c.type.getUsedConstants
        let usedInVal := (c.value?.map (·.getUsedConstants) |>.getD #[])
        let usesGateConst :=
          usedInType.contains `Core.AllPass || usedInType.contains `Core.CanReach ||
            usedInVal.contains `Core.AllPass || usedInVal.contains `Core.CanReach
        if usesGateConst then
          errors := errors.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {c.name} in {m} references Core.AllPass or Core.CanReach"
          hasBadSpecConst := true
        else if c matches .thmInfo _ && !isCompilerAuxThm env c.name then
          errors := errors.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {c.name} in {m} is a theorem or example"
          hasBadSpecConst := true
        if isPrivateOrInternal c.name then continue
        let short := c.name.getString!
        let trackEmpirical := short.startsWith "empirical_" && !legacyEmpiricalModules.contains m
        if short.startsWith "test_" || trackEmpirical then
          promises := promises.push (m, c.name)
          promiseSet := promiseSet.insert c.name
      match ← readIleanRefNames (moduleToIleanPath libDir m) with
      | .error err => errors := errors.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {m} ({err})"
      | .ok refs =>
        for r in refs do
          if r == "Core.AllPass" || r == "Core.CanReach" then
            errors := errors.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {m} .ilean references {r}"
            hasBadSpecConst := true
            break
      let specPath := moduleToFilePath repoDir m
      if !hasBadSpecConst then
        match ← parseModuleCommands env specPath with
        | .error err => errors := errors.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {m} ({err})"
        | .ok cmds =>
          for stx in cmds do
            if hasSyntaxKind ``Lean.Parser.Command.example stx ||
                hasSyntaxKind ``Lean.Parser.Command.theorem stx then
              errors := errors.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {specPath} contains example or theorem"
              break
            if let some sig := findSyntaxKind? ``Lean.Parser.Term.typeSpec stx then
              if hasIdentOrAtom isAllPassToken sig then
                errors := errors.push s!"MUTANT_OR_THEOREM_IN_SPECTESTS: {specPath} references AllPass"
                break
            if let some metaErr := checkForbiddenMetaOrAttr specPath stx then
              errors := errors.push metaErr
              break
    else if isMutantModule m then
      let hasAllPassMutantThm := data.constants.any fun c =>
        match c with
        | .thmInfo v => isNegatedAllPassExpr v.type
        | _ => false
      if hasAllPassMutantThm then
        mutantModsWithAllPass := mutantModsWithAllPass.insert m
      match ← readIleanRefNames (moduleToIleanPath libDir m) with
      | .error err => errors := errors.push s!"UNALLOWED_AXIOM_IN_MUTANT: {m} ({err})"
      | .ok refs =>
        for r in refs do
          if forbiddenIleanMutantRefs.contains r then
            errors := errors.push s!"UNALLOWED_AXIOM_IN_MUTANT: {m} .ilean references {r}"
      let mutPath := moduleToFilePath repoDir m
      match ← parseModuleCommands env mutPath with
      | .error err => errors := errors.push s!"MISSING_SPECMUTANTS: {m} ({err})"
      | .ok cmds =>
        for stx in cmds do
          if hasSyntaxKind ``Lean.Parser.Command.axiom stx then
            errors := errors.push s!"CUSTOM_AXIOM_FORBIDDEN: axiom declaration in {mutPath}"
          if hasIdentOrAtom isForbiddenMutantToken stx then
            errors := errors.push s!"UNALLOWED_AXIOM_IN_MUTANT: {mutPath} uses forbidden sorry/admit/native_decide/unsafe"
          if let some metaErr := checkForbiddenMetaOrAttr mutPath stx then
            errors := errors.push metaErr
      if !hasAllPassMutantThm then
        let t ← IO.asTask (countElaboratedNegatedAllPass env m mutPath)
        sigAuditTasks := sigAuditTasks.push (m, t)

  for (m, t) in sigAuditTasks do
    match t.get with
    | .error e => errors := errors.push s!"MISSING_SPECMUTANTS: {m} ({e})"
    | .ok (.error err) => errors := errors.push s!"MISSING_SPECMUTANTS: {m} ({err})"
    | .ok (.ok negCount) =>
      if negCount > 0 then
        mutantModsWithAllPass := mutantModsWithAllPass.insert m

  for m in specMods do
    let mutMod := m.getPrefix.str "SpecMutants"
    if !mutantModsWithAllPass.contains mutMod then
      errors := errors.push s!"MISSING_SPECMUTANTS: {m} lacks companion {mutMod} with at least 1 negated Core.AllPass mutant"

  promises := promises.qsort (fun a b => a.2.toString < b.2.toString)
  let ctx : Core.Context := { fileName := "<CheckPromises>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let ((headAllPass, headCanReach, axiomErrs), _) ← (Meta.MetaM.run' do
    let mut allPass : Std.HashMap Name (Array Name) := {}
    let mut canReach : Std.HashMap Name (Array Name) := {}
    let mut axErrs : Array String := #[]
    let mut axCache : AxCache := {}
    for h : i in [0 : env.header.moduleNames.size] do
      let m := env.header.moduleNames[i]
      if !isProjectModule m || m.getString! == "SpecTests" || m.getString! == "RuntimeTests" then
        continue
      let some data := env.header.moduleData[i]? | continue
      if isMutantModule m then
        for c in data.constants do
          if c matches .thmInfo _ || c matches .defnInfo _ || c matches .opaqueInfo _ then
            let (badAx?, nextCache) ← (checkAxiomsOk c.name).run axCache
            axCache := nextCache
            if let some badAx := badAx? then
              axErrs := axErrs.push s!"UNALLOWED_AXIOM_IN_MUTANT: {c.name} in {m} uses [{badAx}]"
        continue
      for c in data.constants do
        let .thmInfo v := c | continue
        if isPrivateOrInternal c.name || env.isProjectionFn c.name then continue
        let used := v.type.getUsedConstants
        if !used.any (fun k => k == `Core.AllPass || k == `Core.CanReach) then continue
        let some atoms ← extractUnconditionalAtoms v.type | continue
        let mut hasPromiseAtom := false
        for atom in atoms do
          if atom.isAppOfArity `Core.AllPass 1 || atom.isAppOfArity `Core.CanReach 1 then
            if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
              if promiseSet.contains fn || fn.getString!.startsWith "test_" || fn.getString!.startsWith "empirical_" then
                hasPromiseAtom := true
        if hasPromiseAtom then
          let (badAx?, nextCache) ← (checkAxiomsOk c.name).run axCache
          axCache := nextCache
          if let some badAx := badAx? then
            axErrs := axErrs.push s!"UNALLOWED_AXIOM_IN_THEOREM: {c.name} uses [{badAx}]"
            continue
        for atom in atoms do
          if atom.isAppOfArity `Core.AllPass 1 then
            if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
              if promiseSet.contains fn then
                allPass := allPass.insert fn ((allPass.getD fn #[]).push c.name)
          else if atom.isAppOfArity `Core.CanReach 1 then
            if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
              if promiseSet.contains fn then
                canReach := canReach.insert fn ((canReach.getD fn #[]).push c.name)
    return (allPass, canReach, axErrs)
  ).toIO ctx state

  let trClosureErrs ← checkTimeRandTrustedClosure
  errors := errors ++ axiomErrs ++ trClosureErrs

  let mut modImports : Std.HashMap Name (Array Name) := {}
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if let some data := env.header.moduleData[i]? then
      modImports := modImports.insert m (data.imports.map (·.module))
  let isSandboxClosureAllowed (imp : Name) : Bool :=
    let s := imp.toString
    if !s.startsWith "LeanSwe." then true
    else
      s.startsWith "LeanSwe.LinuxSyscall.Common." ||
        s == "LeanSwe.LinuxSyscall.Sandbox" ||
        s.startsWith "LeanSwe.LinuxSyscall.Sandbox."
  let mut sandboxQueue : Array Name := #[]
  let mut sandboxSeen : Std.HashSet Name := {}
  for m in env.header.moduleNames do
    let s := m.toString
    if (s == "LeanSwe.LinuxSyscall.Sandbox" || s.startsWith "LeanSwe.LinuxSyscall.Sandbox.") &&
        s != "LeanSwe.LinuxSyscall.Sandbox.RuntimeTests" then
      sandboxQueue := sandboxQueue.push m
      sandboxSeen := sandboxSeen.insert m
  let mut qIdx : Nat := 0
  while hq : qIdx < sandboxQueue.size do
    let cur := sandboxQueue[qIdx]
    qIdx := qIdx + 1
    for imp in modImports.getD cur #[] do
      if !isSandboxClosureAllowed imp then
        errors := errors.push s!"TRUSTED_CLOSURE_VIOLATION: {cur} imports forbidden {imp}"
      else if imp.toString.startsWith "LeanSwe." && !sandboxSeen.contains imp then
        sandboxSeen := sandboxSeen.insert imp
        sandboxQueue := sandboxQueue.push imp
  IO.println s!"TRUSTED_CLOSURE: sandbox_modules={sandboxSeen.size} allowlist=Common+Sandbox"

  let mut withAssumeCount := 0
  for (m, pName) in promises do
    let usesAssume := usesAssumeTransitive env pName
    if usesAssume then
      withAssumeCount := withAssumeCount + 1
    if (headAllPass.getD pName #[]).isEmpty then
      errors := errors.push s!"MISSING_ALLPASS: {pName} (defined in {m})"
    if usesAssume && (headCanReach.getD pName #[]).isEmpty then
      errors := errors.push s!"MISSING_CANREACH: {pName} (defined in {m}, uses assume)"

  IO.println s!"PROMISE_CHECK: spec_modules={specModCount} promises={promises.size} with_assume={withAssumeCount} errors={errors.size}"
  if errors.isEmpty then
    return 0
  else
    for err in errors do
      IO.eprintln err
    return 1
