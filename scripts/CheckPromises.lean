import Lean

/-!
Promise coverage audit for `lean-swe` compiled `.olean` artifacts.

Checks:
1. Every `LeanSwe/**/SpecTests.lean` file on disk is transitively imported by `LeanSwe`.
2. Zero custom `axiom` declarations exist in `Core` or `LeanSwe`.
3. Every public `test_*` (and non-legacy `empirical_*`) declaration in a `SpecTests` module has
   a public, non-projection theorem outside `SpecTests` and `RuntimeTests` whose conclusion is
   `Core.AllPass` applied to that promise, plus one with `Core.CanReach` when the promise uses
   `Core.NondetTest.assume`.
4. Qualifying theorems have no hypothesis (`Prop` binder) and use only standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`).
-/

open Lean Meta

private def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4 |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

private def legacyEmpiricalModules : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4
    |>.insert `LeanSwe.Json.SpecTests
    |>.insert `LeanSwe.Time.SpecTests

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

private def isProjectModule (m : Name) : Bool :=
  let r := m.getRoot
  r == `Core || r == `LeanSwe

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
def main (args : List String) : IO UInt32 := do
  let libDir : System.FilePath := args.headD ".lake/build/lib/lean"
  let repoDir : System.FilePath := match args.drop 1 with
    | r :: _ => r
    | [] => "."
  unless ← (libDir / "LeanSwe.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe ({libDir / "LeanSwe.olean"})"
    return 1
  initSearchPath (← findSysroot) [libDir]
  let env ← importModules #[{ module := `LeanSwe }] {}
  let mut visited : Std.HashSet Name := {}
  for modName in env.header.moduleNames do
    if isProjectModule modName then
      visited := visited.insert modName

  let mut errors : Array String := #[]
  let leanSweDir := repoDir / "LeanSwe"
  if ← leanSweDir.pathExists then
    for entry in (← System.FilePath.walkDir leanSweDir) do
      if entry.fileName == some "SpecTests.lean" then
        let modName := moduleNameUnderLeanSwe leanSweDir entry
        if !visited.contains modName then
          errors := errors.push s!"UNIMPORTED_SPECTESTS: {entry} (module {modName} is not imported by LeanSwe)"

  let mut specModCount := 0
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
      for c in data.constants do
        if isPrivateOrInternal c.name then continue
        let short := c.name.getString!
        let trackEmpirical := short.startsWith "empirical_" && !legacyEmpiricalModules.contains m
        if short.startsWith "test_" || trackEmpirical then
          promises := promises.push (m, c.name)
          promiseSet := promiseSet.insert c.name

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

  errors := errors ++ axiomErrs

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
