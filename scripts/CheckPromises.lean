import Lean

/-!
Promise coverage audit for `lean-swe` compiled `.olean` artifacts.

Checks three properties:
1. Every `LeanSwe/**/SpecTests.lean` file on disk is transitively imported by `LeanSwe`.
2. Every public `test_*` declaration in a `SpecTests` module has a public, non-projection
   theorem outside `SpecTests` and `RuntimeTests` whose conclusion is `Core.AllPass` applied
   to that promise, plus one with `Core.CanReach` when the promise uses `Core.NondetTest.assume`.
3. Qualifying theorems have no hypothesis: no binder whose type is a proposition (`Prop`).

A theorem about a stand-in or over a deliberately empty type is not detected here; axiom
verification is handled by `lake build --wfail` and `lake check`.
-/

open Lean Meta

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

private partial def usesAssumeTransitive
    (env : Environment)
    (seen : Std.HashSet Name)
    (cName : Name) : Bool :=
  if cName == `Core.NondetTest.assume then true
  else if seen.contains cName then false
  else if !isProjectModule (env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous) then
    false
  else
    let body? := match env.find? cName with
      | some (.defnInfo dv) => some dv.value
      | some (.opaqueInfo ov) => some ov.value
      | _ => none
    match body? with
    | some body =>
      let seen' := seen.insert cName
      body.getUsedConstants.any (usesAssumeTransitive env seen')
    | none => false

private def extractUnconditionalAtoms (ty : Expr) : MetaM (Option (Array Expr)) :=
  forallTelescope ty fun xs concl => do
    for x in xs do
      if ← isProp (← inferType x) then
        return none
    return some (collectConclusionAtoms concl)

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
    if m.getString! == "SpecTests" then
      specModCount := specModCount + 1
      for c in data.constants do
        if !isPrivateOrInternal c.name && c.name.getString!.startsWith "test_" then
          promises := promises.push (m, c.name)
          promiseSet := promiseSet.insert c.name

  promises := promises.qsort (fun a b => a.2.toString < b.2.toString)
  let ctx : Core.Context := { fileName := "<CheckPromises>", fileMap := default }
  let state : Core.State := { env }
  let ((headAllPass, headCanReach), _) ← (Meta.MetaM.run' do
    let mut allPass : Std.HashMap Name (Array Name) := {}
    let mut canReach : Std.HashMap Name (Array Name) := {}
    for h : i in [0 : env.header.moduleNames.size] do
      let m := env.header.moduleNames[i]
      if !isProjectModule m || m.getString! == "SpecTests" || m.getString! == "RuntimeTests" then
        continue
      let some data := env.header.moduleData[i]? | continue
      for c in data.constants do
        let .thmInfo v := c | continue
        if isPrivateOrInternal c.name || env.isProjectionFn c.name then continue
        let some atoms ← extractUnconditionalAtoms v.type | continue
        for atom in atoms do
          if atom.isAppOfArity `Core.AllPass 1 then
            if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
              if promiseSet.contains fn then
                allPass := allPass.insert fn ((allPass.getD fn #[]).push c.name)
          else if atom.isAppOfArity `Core.CanReach 1 then
            if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
              if promiseSet.contains fn then
                canReach := canReach.insert fn ((canReach.getD fn #[]).push c.name)
    return (allPass, canReach)
  ).toIO ctx state

  let mut withAssumeCount := 0
  for (m, pName) in promises do
    let usesAssume := usesAssumeTransitive env {} pName
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
