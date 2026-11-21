import Lean

/-!
Hardened checkable-assumptions, error-coverage, and `Core.Refines` model-refinement gate audit
for `lean-swe` compiled `.olean` artifacts.

Enforces:
1. Complete module & axiom hygiene:
   - Every `.lean` file under `LeanSwe/` must be transitively imported by `LeanSwe`.
   - Zero custom `axiom` declarations anywhere in `Core`, `LeanSwe`, or `Tests.Main`.
   - Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) on all `assume_*`, `CanReach`,
     upper-layer consumer theorems, `.provedImpossible` theorems, and `refines_model` theorems.
2. Zero prose-only, renamed, or hidden assumptions across non-`Proofs` project modules:
   - No `EmpiricalAssumptions` constant anywhere.
   - No `Prop`-typed inductive/structure field in any non-`Proofs` project module.
   - No standalone `0`-ary `: Prop` declarations across non-`Proofs` `LeanSwe` modules, and no unused `... → Prop`
     predicates or unreferenced public declarations in `SpecTests`.
   - No `String`-carrying data/collection top-level declarations in `SpecTests`.
   - No `empirical_*` or unclassified public `NondetTest`-returning declaration in `SpecTests`.
3. Pure vs External-Boundary separation:
   - Pure modules without `@[extern]`, host `IO` syscalls, or external CLI invocations must declare zero
     `assume_*`, zero `externalAssumptions`, and zero `registeredAssumptions`.
   - External-boundary modules with `RuntimeTests` declare `externalAssumptions : List AssumptionObligation`
     linking each obligation to a real `<pkgNs>.Interface`/`Impl` `subject` and 1-to-1 to a named `RuntimeTests` probe.
   - Formal `assume_*` predicates in `SpecTests` are allowed only when `formalPred? = some name`,
     non-trivial over the boundary parameter (`isMeaningfulBoundaryProp`), satisfiable via `Core.CanReach`,
     and consumed as a used `Prop` hypothesis (after zeta and beta reduction) in an upper-layer `Proofs` theorem.
4. Runtime linking, active execution, non-noop checks, and nonce-log anti-forgery across `Tests.Main` and `RuntimeTests`,
   with clean `RuntimeTests` retirement support when a package provides `<pkgNs>.Model` (and `Fuzz/suites.json`
   coverage for external-boundary or runtime-`Float` packages) while preserving unconditional `errorCoverage`,
   `externalAssumptions` subject/predicate, and axiom checks.
5. Error coverage completeness & canonical `.provedImpossible` shape (`Core.NeverErrorKind{IO,BaseIO,Pure}`).
6. `Core.Refines` model-refinement completeness (`<pkgNs>.Proofs.refines_model` via `RefinesPure*`,
   `RefinesPureEq*`, `RefinesStep*`, `RefinesStepFrom*` with bare-constant pinning and non-trivial `allowed`
   relations across the full public `<pkgNs>.Interface` surface; `deferredRefinesModelPackages` tracks
   `LeanSwe.Tar` and `LeanSwe.SlotPool` pending their dedicated follow-up PR).
7. Supports `--verify-log <path> [--nonce <token>]` and `--allow-legacy [<Csv>]` for phased migration.
-/

open Lean Meta

private def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4 |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

private def legacyExemptionAllowlist : Array Name := #[
  `LeanSwe.ConnectProxy,
  `LeanSwe.ConnectProxy.Raw,
  `LeanSwe.Fs,
  `LeanSwe.Fs.Raw,
  `LeanSwe.Process,
  `LeanSwe.Process.Raw,
  `LeanSwe.ProcessSandbox,
  `LeanSwe.ProcessSandbox.Raw
]

private def deferredRefinesModelPackages : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4
    |>.insert `LeanSwe.Tar
    |>.insert `LeanSwe.SlotPool

private def forbiddenTestMainConsts : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 16
    |>.insert `IO.FS.Handle.mk
    |>.insert `IO.FS.Handle.putStr
    |>.insert `IO.FS.Handle.putStrLn
    |>.insert `IO.FS.Handle.write
    |>.insert `IO.FS.writeFile
    |>.insert `IO.FS.writeBinFile
    |>.insert `IO.FS.withFile
    |>.insert `IO.Process.output
    |>.insert `IO.Process.spawn
    |>.insert `IO.Process.run

private def hostIoEffectConsts : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 32
    |>.insert `IO.getEnv
    |>.insert `IO.getStdin
    |>.insert `IO.getStdout
    |>.insert `IO.getStderr
    |>.insert `IO.monoNanosNow
    |>.insert `IO.sleep
    |>.insert `IO.currentDir
    |>.insert `IO.setCurrentDir
    |>.insert `IO.appPath
    |>.insert `IO.appDir
    |>.insert `IO.getArgs
    |>.insert `Std.Time.Timestamp.now
    |>.insert `IO.FS.Handle.mk
    |>.insert `IO.FS.readFile
    |>.insert `IO.FS.writeFile
    |>.insert `IO.Process.output
    |>.insert `IO.Process.spawn
    |>.insert `IO.Process.run
    |>.insert `System.FilePath.readDir
    |>.insert `System.FilePath.walkDir
    |>.insert `System.FilePath.pathExists
    |>.insert `System.FilePath.isDir
    |>.insert `System.FilePath.metadata
    |>.insert `System.FilePath.symlinkMetadata

private def isHostIoEffect (c : Name) : Bool :=
  hostIoEffectConsts.contains c || c.toString.startsWith "IO.FS."

private def isCompilerAux (n : Name) : Bool :=
  if n.isInternalOrNum then true
  else
    let s := n.getString!
    s.startsWith "_" || s == "rec" || s == "recOn" || s == "casesOn" ||
      s == "ctorIdx" || s == "ctorElim" || s == "toCtorIdx" ||
      s == "noConfusion" || s == "noConfusionType" || s == "below" || s == "brecOn" ||
      s == "sizeOf_spec" || s == "inj" || s == "injEq" ||
      s.startsWith "eq_" || (s.splitOn "match_").length > 1

private def isInductiveElimAux (env : Environment) (n : Name) : Bool :=
  let s := n.getString!
  if s == "ctorElimType" then
    match env.find? n.getPrefix with
    | some (.inductInfo _) => true
    | _ => false
  else if s == "elim" then
    match env.find? n.getPrefix with
    | some (.ctorInfo _) => true
    | _ => false
  else
    false

private def isClassInstanceOrAux (env : Environment) (n : Name) (ty : Expr) : MetaM Bool := do
  let checkType (t : Expr) : MetaM Bool :=
    forallTelescope t fun _ ret => do
      if let .const headName _ := ret.consumeMData.getAppFn.consumeMData then
        return Lean.isClass env headName ||
          headName == ``BEq || headName == ``Repr || headName == ``DecidableEq ||
          headName == ``Hashable || headName == ``Ord || headName == ``ToString ||
          headName == ``Inhabited
      return false
  if ← checkType ty then return true
  if let some pInfo := env.find? n.getPrefix then
    if ← checkType pInfo.type then return true
  return false

private def isProjectModule (m : Name) : Bool :=
  let r := m.getRoot
  r == `Core || r == `LeanSwe

private def isProjectOrTestModule (m : Name) : Bool :=
  isProjectModule m || m == `Tests.Main

private def isProofsModule (m : Name) : Bool :=
  m.components.any (· == `Proofs)

private def isSpecOrRuntimeOrProofsModule (m : Name) : Bool :=
  isProofsModule m || m.getString! == "SpecTests" || m.getString! == "RuntimeTests"

private def moduleOfConst (env : Environment) (cName : Name) : Name :=
  env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous

private def exprUsesPkgImpl (env : Environment) (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    let m := moduleOfConst env c
    m.getRoot == `LeanSwe && !isSpecOrRuntimeOrProofsModule m && m.getString! != "Types"

private partial def collectConclusionAtoms (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    collectConclusionAtoms e.appFn!.appArg! ++ collectConclusionAtoms e.appArg!
  else
    #[e]

private def unfoldMatcherApp? (env : Environment) (e : Expr) : Option Expr :=
  let cur := e.consumeMData
  match cur.getAppFn.consumeMData with
  | .const fnName lvls =>
    if fnName.isStr && (fnName.getString!.splitOn "match_").length > 1 then
      match env.find? fnName with
      | some (.defnInfo dv) =>
        let body := dv.value.instantiateLevelParams dv.levelParams lvls
        some (mkAppN body cur.getAppArgs).headBeta
      | _ => none
    else none
  | _ => none

private partial def unfoldMatcherChain (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  if fuel == 0 then e
  else match unfoldMatcherApp? env e with
    | some e' => unfoldMatcherChain env (fuel - 1) e'
    | none => e

private partial def evalClosedDecidable? (prop decInst : Expr) : MetaM (Option Bool) := do
  let p := prop.consumeMData
  if p.isConstOf ``Bool.true || p.isConstOf ``True then return some true
  if p.isConstOf ``Bool.false || p.isConstOf ``False then return some false
  let d ← withTransparency .all (Meta.reduce decInst (explicitOnly := false) (skipTypes := true) (skipProofs := true))
  let df := d.consumeMData.getAppFn.consumeMData
  if df.isConstOf ``Decidable.isTrue then return some true
  if df.isConstOf ``Decidable.isFalse then return some false
  let pw := (← whnf p).consumeMData
  if pw.isConstOf ``Bool.true || pw.isConstOf ``True then return some true
  if pw.isConstOf ``Bool.false || pw.isConstOf ``False then return some false
  if pw.isAppOfArity ``Not 1 then
    if let some b ← evalClosedDecidable? pw.appArg! decInst then
      return some (!b)
  if pw.isAppOfArity ``Eq 3 then
    let lhs := (← withTransparency .all (Meta.reduce (pw.getArg! 1))).consumeMData
    let rhs := (← withTransparency .all (Meta.reduce (pw.getArg! 2))).consumeMData
    if (lhs.isConstOf ``Bool.true || lhs.isConstOf ``Bool.false) &&
        (rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false) then
      return some (lhs == rhs)
  return none

private partial def classifyBranchNode?
    (env : Environment)
    (rawExpr : Expr) : MetaM (Option (Bool × Array Expr)) := do
  let cur := (unfoldMatcherChain env 8 rawExpr).consumeMData
  let fn := cur.getAppFn.consumeMData
  let args := cur.getAppArgs
  if fn.isConstOf ``ite && args.size >= 5 then
    let prop := args[1]!
    let dec := args[2]!
    let extra := args.extract 5 args.size
    let tB := mkAppN args[3]! extra
    let fB := mkAppN args[4]! extra
    if !prop.hasFVar && !prop.hasLooseBVars && !dec.hasFVar && !dec.hasLooseBVars && !exprUsesPkgImpl env prop then
      match ← evalClosedDecidable? prop dec with
      | some true => return some (true, #[tB])
      | some false => return some (true, #[fB])
      | none => pure ()
    return some (false, #[prop, tB, fB])
  if fn.isConstOf ``dite && args.size >= 5 then
    let prop := args[1]!
    let dec := args[2]!
    let extra := args.extract 5 args.size
    let tB := args[3]!
    let fB := args[4]!
    if !prop.hasFVar && !prop.hasLooseBVars && !dec.hasFVar && !dec.hasLooseBVars && !exprUsesPkgImpl env prop then
      match ← evalClosedDecidable? prop dec with
      | some true => return some (true, #[tB] ++ extra)
      | some false => return some (true, #[fB] ++ extra)
      | none => pure ()
    return some (false, #[prop, tB, fB] ++ extra)
  if fn.isConstOf ``cond && args.size >= 4 then
    let b := args[1]!
    let extra := args.extract 4 args.size
    let tB := mkAppN args[2]! extra
    let fB := mkAppN args[3]! extra
    if !b.hasFVar && !b.hasLooseBVars && !exprUsesPkgImpl env b then
      let bw ← withTransparency .all (whnf b)
      if bw.consumeMData.isConstOf ``Bool.true then return some (true, #[tB])
      if bw.consumeMData.isConstOf ``Bool.false then return some (true, #[fB])
    return some (false, #[b, tB, fB])
  if let .const fnName _ := fn then
    if let .str indName recKind := fnName then
      if recKind == "casesOn" || recKind == "recOn" || recKind == "rec" then
        if let some (.inductInfo ind) := env.find? indName then
          let nCtors := ind.ctors.length
          if nCtors >= 2 then
            let (majorIdx, minorStart, total) :=
              if recKind == "rec" then
                let ms := ind.numParams + 1
                let mj := ms + nCtors + ind.numIndices
                (mj, ms, mj + 1)
              else
                let mj := ind.numParams + 1 + ind.numIndices
                (mj, mj + 1, mj + 1 + nCtors)
            if args.size >= total then
              let major := args[majorIdx]!
              let extra := args.extract total args.size
              if !major.hasFVar && !major.hasLooseBVars && !exprUsesPkgImpl env major then
                let mw ← withTransparency .all (whnf major)
                if let .const ctorName _ := mw.consumeMData.getAppFn.consumeMData then
                  if let some cIdx := ind.ctors.findIdx? (· == ctorName) then
                    let chosen := mkAppN args[minorStart + cIdx]! extra
                    return some (true, #[chosen])
              let mut subs : Array Expr := #[major] ++ extra
              for k in [0 : nCtors] do
                subs := subs.push args[minorStart + k]!
              return some (false, subs)
  return none

private def isSmallClosedExpr (e : Expr) : Bool :=
  !e.hasFVar && !e.hasLooseBVars && e.approxDepth.toNat <= 16

private def runBoundedMeta {α : Type} (fallback : α) (act : MetaM α) : MetaM α :=
  Lean.tryCatchRuntimeEx
    (try
      Core.withCurrHeartbeats <|
        withTheReader Core.Context
          (fun c => { c with maxHeartbeats := 500000, maxRecDepth := min c.maxRecDepth 2048 }) act
    catch _ =>
      pure fallback)
    (fun _ => pure fallback)

private inductive DeadBranchResult where
  | clean
  | hasDeadBranch
  | inconclusive (reason : String)

private partial def hasStaticDeadBranchExprAux
    (env : Environment)
    (bestFuelRef : IO.Ref (Std.HashMap Expr Nat))
    (fuel : Nat)
    (e : Expr) : MetaM DeadBranchResult := do
  if fuel == 0 then return .inconclusive "AST depth budget exhausted"
  let cur := e.consumeMData
  if (← bestFuelRef.get).getD cur 0 >= fuel then return .clean
  bestFuelRef.modify (·.insert cur fuel)
  if cur.isLambda then
    return ← lambdaTelescope cur fun _ body => hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) body
  if let some (isStatic, subs) ← classifyBranchNode? env cur then
    if isStatic then return .hasDeadBranch
    for s in subs do
      match ← hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) s with
      | .clean => pure ()
      | bad => return bad
    return .clean
  match cur with
  | .app f a =>
    match ← hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) f with
    | .clean => hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) a
    | bad => return bad
  | .letE n t v b _ =>
    match ← hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) v with
    | .clean =>
      if isSmallClosedExpr v then
        hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) (b.instantiate1 v)
      else
        withLocalDeclD n t fun x =>
          hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) (b.instantiate1 x)
    | bad => return bad
  | .proj _ _ s => hasStaticDeadBranchExprAux env bestFuelRef (fuel - 1) s
  | _ => return .clean

private def hasStaticDeadBranchExpr (env : Environment) (fuel : Nat) (e : Expr) : MetaM DeadBranchResult :=
  Lean.tryCatchRuntimeEx
    (try
      Core.withCurrHeartbeats <|
        withTheReader Core.Context
          (fun c => { c with maxHeartbeats := 5000000, maxRecDepth := max c.maxRecDepth 4096 }) do
          let bestFuelRef ← IO.mkRef (Std.HashMap.emptyWithCapacity (α := Expr) (β := Nat) 128)
          hasStaticDeadBranchExprAux env bestFuelRef fuel e
    catch ex => do
      return .inconclusive (← ex.toMessageData.toString))
    (fun ex => do
      return .inconclusive (← ex.toMessageData.toString))

private structure DeadBranchCache where
  cleanConsts : Std.HashSet Name := {}
  cleanSubgraphs : Std.HashSet Name := {}

private partial def hasStaticDeadBranchTransitive
    (env : Environment)
    (fuel : Nat)
    (cache : DeadBranchCache)
    (start : Name) : MetaM (DeadBranchResult × DeadBranchCache) := do
  let mut queue : Array Name := #[start]
  let mut qIdx : Nat := 0
  let mut seen : Std.HashSet Name := {}
  let mut cleanConsts := cache.cleanConsts
  let cleanSubgraphs := cache.cleanSubgraphs
  while qIdx < queue.size do
    let cur := queue[qIdx]!
    qIdx := qIdx + 1
    if seen.contains cur || cleanSubgraphs.contains cur then continue
    seen := seen.insert cur
    let modName := moduleOfConst env cur
    if !isProjectOrTestModule modName || modName == `Core.Assumptions then continue
    if isCompilerAux cur && (cur.getString!.splitOn "match_").length <= 1 then continue
    if ← Meta.isInstance cur then continue
    let body? := match env.find? cur with
      | some (.defnInfo dv) => some dv.value
      | some (.opaqueInfo ov) => some ov.value
      | _ => none
    if let some body := body? then
      if (cur.getString!.splitOn "match_").length <= 1 && !cleanConsts.contains cur then
        match ← hasStaticDeadBranchExpr env fuel body with
        | .clean => cleanConsts := cleanConsts.insert cur
        | .hasDeadBranch => return (.hasDeadBranch, { cleanConsts, cleanSubgraphs })
        | .inconclusive reason => return (.inconclusive s!"{cur}: {reason}", { cleanConsts, cleanSubgraphs })
      for u in body.getUsedConstants do
        if !seen.contains u && !cleanSubgraphs.contains u then
          queue := queue.push u
  let nextSubgraphs := seen.fold (init := cleanSubgraphs) fun s v => s.insert v
  return (.clean, { cleanConsts, cleanSubgraphs := nextSubgraphs })

private partial def stripDeadPureLets (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE n t v b nonDep =>
    if !b.hasLooseBVar 0 then
      stripDeadPureLets (b.lowerLooseBVars 1 1)
    else
      let b' := stripDeadPureLets b
      if !b'.hasLooseBVar 0 then
        b'.lowerLooseBVars 1 1
      else
        .letE n t (stripDeadPureLets v) b' nonDep
  | .lam n t b bi => .lam n t (stripDeadPureLets b) bi
  | .app f a => .app (stripDeadPureLets f) (stripDeadPureLets a)
  | .proj tn idx s => .proj tn idx (stripDeadPureLets s)
  | cur => cur

private partial def stripInertBindings (env : Environment) (rtMod : Name) (e : Expr) : Expr :=
  let cur := e.consumeMData
  if cur.getAppFn.consumeMData.isLambda then
    let red := cur.headBeta
    if red != cur then stripInertBindings env rtMod red else cur
  else if cur.isAppOfArity ``Bind.bind 6 || cur.isAppOfArity ``bind 6 then
    let args := cur.getAppArgs
    let act := stripInertBindings env rtMod args[4]!
    let cont := match args[5]!.consumeMData with
      | .lam n t b bi => Expr.lam n t (stripInertBindings env rtMod b) bi
      | other => stripInertBindings env rtMod other
    let actClean := act.consumeMData
    if actClean.isAppOfArity ``Pure.pure 4 || actClean.isAppOfArity ``pure 4 then
      let v := actClean.appArg!
      stripInertBindings env rtMod (mkApp cont v).headBeta
    else if let .lam _ binderTy body _ := cont.consumeMData then
      let bt := binderTy.consumeMData
      let isUnitBinder := bt.isConstOf ``Unit || bt.isConstOf ``PUnit
      let usesRtHelper := actClean.getUsedConstants.any (fun c => moduleOfConst env c == rtMod)
      if !body.hasLooseBVar 0 && !isUnitBinder && !usesRtHelper then
        body
      else
        mkAppN cur.getAppFn (args.set! 4 act |>.set! 5 cont)
    else
      mkAppN cur.getAppFn (args.set! 4 act |>.set! 5 cont)
  else
    match cur with
    | .letE n t v b nonDep =>
      if !b.hasLooseBVar 0 then
        stripInertBindings env rtMod (b.lowerLooseBVars 1 1)
      else if isSmallClosedExpr v then
        stripInertBindings env rtMod (b.instantiate1 v)
      else
        let b' := stripInertBindings env rtMod b
        if !b'.hasLooseBVar 0 then
          b'.lowerLooseBVars 1 1
        else
          .letE n t (stripInertBindings env rtMod v) b' nonDep
    | .lam n t b bi => .lam n t (stripInertBindings env rtMod b) bi
    | .app f a => .app (stripInertBindings env rtMod f) (stripInertBindings env rtMod a)
    | .proj tn idx s => .proj tn idx (stripInertBindings env rtMod s)
    | _ => cur

private structure ActiveCallCache where
  directPlain : Std.HashMap Name (Array Name) := {}
  directStripped : Std.HashMap (Name × Name) (Array Name) := {}
  reachesThrow : Std.HashMap Name Bool := {}

private partial def exprActiveDirectConsts
    (env : Environment)
    (e : Expr) : MetaM (Array Name) :=
  runBoundedMeta #[] do
    let bestFuelRef ← IO.mkRef (Std.HashMap.emptyWithCapacity (α := Expr) (β := Nat) 128)
    let outSetRef ← IO.mkRef (Std.HashSet.emptyWithCapacity (α := Name) 32)
    let rec collect (fuel : Nat) (raw : Expr) : MetaM Unit := do
      if fuel == 0 then return
      let cur := raw.consumeMData
      if (← bestFuelRef.get).getD cur 0 >= fuel then return
      bestFuelRef.modify (·.insert cur fuel)
      if cur.isLambda then
        lambdaTelescope cur fun _ body =>
          collect (fuel - 1) body
        return
      if let some (_, subs) ← classifyBranchNode? env cur then
        for s in subs do
          collect (fuel - 1) s
        return
      match cur with
      | .const c _ => outSetRef.modify (·.insert c)
      | .app f a =>
        collect (fuel - 1) f
        collect (fuel - 1) a
      | .letE n t v b _ =>
        collect (fuel - 1) v
        if isSmallClosedExpr v then
          collect (fuel - 1) (b.instantiate1 v)
        else
          withLocalDeclD n t fun x =>
            collect (fuel - 1) (b.instantiate1 x)
      | .proj _ _ s => collect (fuel - 1) s
      | _ => pure ()
    collect 4096 e
    return (← outSetRef.get).toArray

private def constActiveDirectConsts
    (env : Environment)
    (cacheRef : IO.Ref ActiveCallCache)
    (stripRtMod? : Option Name)
    (cur : Name)
    (rawBody : Expr) : MetaM (Array Name) := do
  let cache ← cacheRef.get
  match stripRtMod? with
  | none =>
    if let some hit := cache.directPlain.get? cur then
      return hit
    let used ← exprActiveDirectConsts env rawBody
    cacheRef.modify fun c => { c with directPlain := c.directPlain.insert cur used }
    return used
  | some rtMod =>
    let keyMod :=
      if rawBody.getUsedConstants.any (fun k => moduleOfConst env k == rtMod) then rtMod
      else Name.anonymous
    let key := (cur, keyMod)
    if let some hit := cache.directStripped.get? key then
      return hit
    let stripped := stripInertBindings env keyMod (stripDeadPureLets rawBody)
    let used ← exprActiveDirectConsts env stripped
    cacheRef.modify fun c => { c with directStripped := c.directStripped.insert key used }
    return used

private partial def usesPredConstActiveCached
    (env : Environment)
    (cacheRef : IO.Ref ActiveCallCache)
    (stripRtMod? : Option Name)
    (pred : Name → Bool)
    (start : Name) : MetaM Bool := do
  let mut queue : Array Name := #[start]
  let mut qIdx : Nat := 0
  let mut seen : Std.HashSet Name := {}
  while qIdx < queue.size do
    let cur := queue[qIdx]!
    qIdx := qIdx + 1
    if cur != start && pred cur then return true
    if seen.contains cur then continue
    seen := seen.insert cur
    let modName := moduleOfConst env cur
    if !isProjectOrTestModule modName then continue
    let body? := match env.find? cur with
      | some (.defnInfo dv) => some dv.value
      | some (.opaqueInfo ov) => some ov.value
      | _ => none
    if let some rawBody := body? then
      let used ← constActiveDirectConsts env cacheRef stripRtMod? cur rawBody
      if used.any pred then return true
      for u in used do
        if !seen.contains u then
          queue := queue.push u
  return false

private def usesAnyConstActiveCached
    (env : Environment)
    (cacheRef : IO.Ref ActiveCallCache)
    (targets : Std.HashSet Name)
    (start : Name) : MetaM Bool :=
  usesPredConstActiveCached env cacheRef none (fun c => targets.contains c) start

private def usesAnyConstActive
    (env : Environment)
    (targets : Std.HashSet Name)
    (start : Name) : MetaM Bool := do
  let cacheRef ← IO.mkRef ({} : ActiveCallCache)
  usesAnyConstActiveCached env cacheRef targets start

private def usesThrowTargetsActive
    (env : Environment)
    (cacheRef : IO.Ref ActiveCallCache)
    (throwTargets : Std.HashSet Name)
    (start : Name) : MetaM Bool := do
  if let some res := (← cacheRef.get).reachesThrow.get? start then
    return res
  let mut queue : Array Name := #[start]
  let mut qIdx : Nat := 0
  let mut seen : Std.HashSet Name := {}
  while qIdx < queue.size do
    let cur := queue[qIdx]!
    qIdx := qIdx + 1
    if cur != start && throwTargets.contains cur then
      cacheRef.modify fun c => { c with reachesThrow := c.reachesThrow.insert start true }
      return true
    if seen.contains cur then continue
    seen := seen.insert cur
    if cur != start then
      if let some cached := (← cacheRef.get).reachesThrow.get? cur then
        if cached then
          cacheRef.modify fun c => { c with reachesThrow := c.reachesThrow.insert start true }
          return true
        else
          continue
    let modName := moduleOfConst env cur
    if !isProjectOrTestModule modName then continue
    let body? := match env.find? cur with
      | some (.defnInfo dv) => some dv.value
      | some (.opaqueInfo ov) => some ov.value
      | _ => none
    if let some rawBody := body? then
      let used ← constActiveDirectConsts env cacheRef none cur rawBody
      if used.any throwTargets.contains then
        cacheRef.modify fun c =>
          { c with reachesThrow := c.reachesThrow.insert cur true |>.insert start true }
        return true
      for u in used do
        if !seen.contains u then
          queue := queue.push u
  cacheRef.modify fun c =>
    let m := seen.fold (init := c.reachesThrow) fun acc v =>
      if throwTargets.contains v then acc else acc.insert v false
    { c with reachesThrow := m }
  return false

private def usesPackageImplConstActiveCached
    (env : Environment)
    (cacheRef : IO.Ref ActiveCallCache)
    (pkgNs rtMod : Name)
    (start : Name) : MetaM Bool :=
  let ifaceMod := Name.str pkgNs "Interface"
  let implMod := Name.str pkgNs "Impl"
  usesPredConstActiveCached env cacheRef (some rtMod)
    (fun c =>
      let m := moduleOfConst env c
      (m == ifaceMod || m == implMod) && !isCompilerAux c)
    start

private partial def exprContainsAnyFVar (fvars : Std.HashSet FVarId) (e : Expr) : Bool :=
  e.hasAnyFVar (fun fv => fvars.contains fv)

private partial def isStaticFalseProp (e : Expr) : MetaM Bool :=
  runBoundedMeta false do
    let p := (← whnf e).consumeMData
    if p.isConstOf ``False then return true
    if p.isAppOfArity ``Not 1 then
      let inner := (← whnf p.appArg!).consumeMData
      if inner.isConstOf ``True then return true
      if inner.isAppOfArity ``Eq 3 then
        let args := inner.getAppArgs
        if args[1]! == args[2]! || (← isDefEq args[1]! args[2]!) then return true
    if !p.hasFVar && !p.hasLooseBVars then
      let decFalse ← runBoundedMeta false <|
        withTheReader Core.Context (fun c => { c with maxRecDepth := min c.maxRecDepth 1024 }) do
          let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
          let b ← withTransparency .all (whnf (mkApp2 (mkConst ``decide) p inst))
          return b.consumeMData.isConstOf ``Bool.false
      if decFalse then return true
    return false

private partial def isStaticTrueProp (e : Expr) : MetaM Bool :=
  runBoundedMeta false do
    let p := (← whnf e).consumeMData
    if p.isConstOf ``True then return true
    if p.isAppOfArity ``And 2 then
      return (← isStaticTrueProp p.appFn!.appArg!) && (← isStaticTrueProp p.appArg!)
    if p.isAppOfArity ``Not 1 then
      return ← isStaticFalseProp p.appArg!
    if p.isAppOfArity ``Eq 3 then
      let args := p.getAppArgs
      if args[1]! == args[2]! || (← isDefEq args[1]! args[2]!) then return true
    if !p.hasFVar && !p.hasLooseBVars then
      let decTrue ← runBoundedMeta false <|
        withTheReader Core.Context (fun c => { c with maxRecDepth := min c.maxRecDepth 1024 }) do
          let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
          let b ← withTransparency .all (whnf (mkApp2 (mkConst ``decide) p inst))
          return b.consumeMData.isConstOf ``Bool.true
      if decTrue then return true
    return false

private def isNegationPair (a b : Expr) : MetaM Bool :=
  runBoundedMeta false do
    let a' := (← whnf a).consumeMData
    let b' := (← whnf b).consumeMData
    if b'.isAppOfArity ``Not 1 then
      if ← isDefEq a' b'.appArg! then return true
    if a'.isAppOfArity ``Not 1 then
      if ← isDefEq b' a'.appArg! then return true
    return false

private partial def isMeaningfulBoundaryProp
    (boundaryFVars assertBoundFVars : Std.HashSet FVarId)
    (e : Expr) : MetaM Bool := do
  let p := (← whnf e).consumeMData
  if ← isStaticTrueProp p then return false
  if ← isStaticFalseProp p then return false
  if !exprContainsAnyFVar boundaryFVars p then return false
  if p.isAppOfArity ``And 2 then
    let lhs := p.appFn!.appArg!
    let rhs := p.appArg!
    if (← isStaticTrueProp lhs) || (← isStaticTrueProp rhs) then return false
    if (← isStaticFalseProp lhs) || (← isStaticFalseProp rhs) then return false
    if lhs.consumeMData.isForall then
      if !(← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs) then return false
    if rhs.consumeMData.isForall then
      if !(← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars rhs) then return false
    return (← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs) ||
           (← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars rhs)
  if p.isAppOfArity ``Or 2 then
    let lhs := p.appFn!.appArg!
    let rhs := p.appArg!
    if ← isNegationPair lhs rhs then return false
    return (← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs) &&
           (← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars rhs)
  if p.isAppOfArity ``Exists 2 then
    let dom := p.appFn!.appArg!
    if ← isProp dom then
      if ← isStaticFalseProp dom then return false
    return ← lambdaBoundedTelescope p.appArg! 1 fun xs body => do
      let bVars := xs.foldl (fun (s : Std.HashSet FVarId) x => s.insert x.fvarId!) assertBoundFVars
      isMeaningfulBoundaryProp boundaryFVars bVars body
  if let .forallE n dom body bi := p then
    if ← isProp dom then
      if (← isStaticFalseProp dom) || (← isStaticTrueProp dom) then return false
      if !body.hasLooseBVar 0 && (← isStaticFalseProp body) then
        return ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars dom
      if !exprContainsAnyFVar assertBoundFVars dom then return false
      if exprContainsAnyFVar boundaryFVars dom then return false
      return ← withLocalDecl n bi dom fun h => do
        let concl := body.instantiate1 h
        if ← isDefEq dom concl then return false
        isMeaningfulBoundaryProp boundaryFVars assertBoundFVars concl
    else
      let dClean := (← whnf dom).consumeMData
      if dClean.isConstOf ``Empty || dClean.isConstOf ``PEmpty then return false
      return ← withLocalDecl n bi dom fun x =>
        isMeaningfulBoundaryProp boundaryFVars (assertBoundFVars.insert x.fvarId!) (body.instantiate1 x)
  if p.isAppOfArity ``Eq 3 then
    let args := p.getAppArgs
    let lhs := args[1]!
    let rhs := args[2]!
    if lhs == rhs || (← isDefEq lhs rhs) then return false
    if lhs.consumeMData.isAppOfArity ``Decidable.decide 2 && rhs.consumeMData.isConstOf ``Bool.true then
      return ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs.consumeMData.appFn!.appArg!
    return exprContainsAnyFVar boundaryFVars lhs || exprContainsAnyFVar boundaryFVars rhs
  if p.isAppOfArity ``Not 1 then
    let inner := (← whnf p.appArg!).consumeMData
    if (← isStaticTrueProp inner) || (← isStaticFalseProp inner) then return false
    return ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars inner
  return exprContainsAnyFVar boundaryFVars p

private partial def validateAssertsInExpr
    (boundaryFVars assertBoundFVars : Std.HashSet FVarId)
    (e : Expr) : MetaM (Bool × Bool) := do
  let cur := e.consumeMData
  if cur.isAppOfArity `Core.NondetTest.assert 3 then
    let ok ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars cur.appArg!
    return (true, ok)
  match cur with
  | .app _ _ =>
    cur.withApp fun fn args => do
      let nonLamHasBoundary := exprContainsAnyFVar boundaryFVars fn ||
        args.any (fun a => !(a.consumeMData matches .lam _ _ _ _) && exprContainsAnyFVar boundaryFVars a)
      let (foundF, okF) ← validateAssertsInExpr boundaryFVars assertBoundFVars fn
      if foundF && !okF then return (true, false)
      let mut anyFound := foundF
      let mut allOk := okF
      for arg in args do
        let aClean := arg.consumeMData
        if aClean.isLambda then
          let (foundA, okA) ← lambdaTelescope aClean fun lxs lbody => do
            let mut nextBoundary := boundaryFVars
            let mut nextBound := assertBoundFVars
            for x in lxs do
              nextBound := nextBound.insert x.fvarId!
              if nonLamHasBoundary && !(← isProp (← inferType x)) then
                nextBoundary := nextBoundary.insert x.fvarId!
            validateAssertsInExpr nextBoundary nextBound lbody
          anyFound := anyFound || foundA
          allOk := allOk && okA
          if anyFound && !allOk then return (true, false)
        else
          let (foundA, okA) ← validateAssertsInExpr boundaryFVars assertBoundFVars arg
          anyFound := anyFound || foundA
          allOk := allOk && okA
          if anyFound && !allOk then return (true, false)
      return (anyFound, allOk)
  | .lam n t b bi =>
    withLocalDecl n bi t fun x =>
      validateAssertsInExpr boundaryFVars (assertBoundFVars.insert x.fvarId!) (b.instantiate1 x)
  | .letE _ _ v b _ =>
    let (foundV, okV) ← validateAssertsInExpr boundaryFVars assertBoundFVars v
    if foundV && !okV then return (true, false)
    let (foundB, okB) ← validateAssertsInExpr boundaryFVars assertBoundFVars (b.instantiate1 v)
    return (foundV || foundB, okV && okB)
  | _ => return (false, true)

private partial def exprHasStringLitMatching (pred : String → Bool) (e : Expr) : Bool :=
  match e with
  | .lit (.strVal s) => pred s
  | .app f a => exprHasStringLitMatching pred f || exprHasStringLitMatching pred a
  | .lam _ t b _ => exprHasStringLitMatching pred t || exprHasStringLitMatching pred b
  | .forallE _ t b _ => exprHasStringLitMatching pred t || exprHasStringLitMatching pred b
  | .letE _ t v b _ => exprHasStringLitMatching pred t || exprHasStringLitMatching pred v || exprHasStringLitMatching pred b
  | .mdata _ b => exprHasStringLitMatching pred b
  | .proj _ _ s => exprHasStringLitMatching pred s
  | _ => false

private def moduleNameUnderLeanSwe (leanSweDir entry : System.FilePath) : Name :=
  ((entry.withExtension "").components.drop leanSweDir.components.length).foldl
    (fun acc seg => if seg == "." || seg.isEmpty then acc else Name.str acc seg) `LeanSwe

private def pkgNamespaceOfSpec (specMod : Name) : Name :=
  let comps := specMod.components
  if let some idx := comps.findIdx? (· == `Proofs) then
    if idx > 0 then
      (comps.take idx).foldl (fun acc seg => Name.str acc seg.getString!) .anonymous
    else specMod
  else
    match specMod with
    | .str p "SpecTests"
    | .str p "Proofs"
    | .str p "RuntimeTests"
    | .str p "Types"
    | .str p "Model"
    | .str p "Interface"
    | .str p "Impl" => p
    | _ => specMod

private def isPrefixComponents (pfx comps : List Name) : Bool :=
  pfx.length <= comps.length && comps.take pfx.length == pfx

private def pkgNamespaceOfSpecWith (knownPkgs : Array Name) (modName : Name) : Name :=
  let comps := modName.components
  let best := knownPkgs.foldl (init := ((0 : Nat), Name.anonymous)) fun (bestLen, bestPkg) pkg =>
    let pComps := pkg.components
    if pComps.length > bestLen && isPrefixComponents pComps comps then
      (pComps.length, pkg)
    else
      (bestLen, bestPkg)
  if best.1 > 0 then
    best.2
  else
    pkgNamespaceOfSpec modName

private def isExternalBoundaryPkg (env : Environment) (knownPkgs : Array Name) (pkgNs : Name) : Bool :=
  let ifaceMod := Name.str pkgNs "Interface"
  let isProcessPkg := pkgNs == `LeanSwe.Process || pkgNs == `LeanSwe.Process.Raw
  match env.header.moduleNames.findIdx? (· == ifaceMod) with
  | none => false
  | some idx =>
    match env.header.moduleData[idx]? with
    | none => false
    | some md => Id.run do
      if !isProcessPkg && md.imports.any (fun imp =>
          imp.module == `LeanSwe.Process.Interface || imp.module == `LeanSwe.Process.Raw.Interface) then
        return true
      let mut modImportsCli : Std.HashMap Name Bool := {}
      for h : mi in [0 : env.header.moduleNames.size] do
        let mName := env.header.moduleNames[mi]
        if let some mData := env.header.moduleData[mi]? then
          let usesProc := mData.imports.any fun imp =>
            imp.module == `LeanSwe.Process.Interface || imp.module == `LeanSwe.Process.Raw.Interface
          modImportsCli := modImportsCli.insert mName usesProc
      let mut worklist : Array Name := #[]
      for c in md.constants do
        if !isPrivateName c.name && !isCompilerAux c.name then
          worklist := worklist.push c.name
      let mut visited : Std.HashSet Name := {}
      while !worklist.isEmpty do
        let cname := worklist.back!
        worklist := worklist.pop
        if visited.contains cname then
          continue
        visited := visited.insert cname
        if isHostIoEffect cname then
          return true
        let cMod := moduleOfConst env cname
        if !isProcessPkg &&
            (cMod == `LeanSwe.Process.Interface || cMod == `LeanSwe.Process.Raw.Interface) then
          return true
        let isOwnedByPkg := cMod == ifaceMod ||
          (pkgNamespaceOfSpecWith knownPkgs cMod == pkgNs && !isSpecOrRuntimeOrProofsModule cMod)
        let isLeanOrStd := cMod.getRoot == `Lean || cMod.getRoot == `Std
        if isLeanOrStd then
          if let some (.opaqueInfo _) := env.find? cname then
            return true
        if isOwnedByPkg || isLeanOrStd then
          if isOwnedByPkg && Lean.isExtern env cname then
            return true
          if isOwnedByPkg && !isProcessPkg && modImportsCli.getD cMod false then
            return true
          if let some cinfo := env.find? cname then
            for u in cinfo.type.getUsedConstants do
              if !visited.contains u then
                worklist := worklist.push u
            let valUsed := match cinfo with
              | .defnInfo dv => dv.value.getUsedConstants
              | .opaqueInfo ov => ov.value.getUsedConstants
              | _ => #[]
            for u in valUsed do
              if !visited.contains u then
                worklist := worklist.push u
      return false

private partial def hasInvalidRunnerCall (modName : Name) (e : Expr) : Bool :=
  let clean := e.consumeMData
  match clean with
  | .const c _ =>
    c == `Core.runRegisteredAssumptions || c == `Core.runRegisteredErrorTests
  | .app f a =>
    match f.consumeMData with
    | .const c _ =>
      if c == `Core.runRegisteredAssumptions then
        !(modName.getString! == "RuntimeTests" &&
          a.consumeMData.isConstOf (Name.str modName "registeredAssumptions"))
      else if c == `Core.runRegisteredErrorTests then
        !(modName.getString! == "RuntimeTests" &&
          a.consumeMData.isConstOf (Name.str modName "registeredErrorTests"))
      else
        hasInvalidRunnerCall modName f || hasInvalidRunnerCall modName a
    | _ => hasInvalidRunnerCall modName f || hasInvalidRunnerCall modName a
  | .lam _ t b _ => hasInvalidRunnerCall modName t || hasInvalidRunnerCall modName b
  | .forallE _ t b _ => hasInvalidRunnerCall modName t || hasInvalidRunnerCall modName b
  | .letE _ t v b _ =>
    hasInvalidRunnerCall modName t || hasInvalidRunnerCall modName v || hasInvalidRunnerCall modName b
  | .proj _ _ s => hasInvalidRunnerCall modName s
  | _ => false

private def wrapperUnfoldConsts : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 12
    |>.insert ``Function.const
    |>.insert ``Function.comp
    |>.insert ``id
    |>.insert ``Prod.fst
    |>.insert ``Prod.snd
    |>.insert ``PProd.fst
    |>.insert ``PProd.snd
    |>.insert ``And.left
    |>.insert ``And.right

private partial def reduceProjsInExpr (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun sub => do
    let c := sub.consumeMData
    if let .proj _ _ _ := c then
      if let some r ← Meta.reduceProj? c then
        return .visit r
    if let some r ← Meta.reduceRecMatcher? c then
      return .visit r
    return .continue)

private def normalizeProofForConsumeCheck (e : Expr) : MetaM Expr := do
  let mut cur := e
  for _ in [:8] do
    let z ← zetaReduce cur
    let d ← Meta.deltaExpand z wrapperUnfoldConsts.contains (allowOpaque := true)
    let b ← Core.betaReduce d
    let p ← reduceProjsInExpr b.headBeta
    let b2 ← Core.betaReduce p.headBeta
    if b2 == cur then
      return b2
    cur := b2
  return cur

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

private def checkAxiomsOk (cache : AxCache) (cName : Name) : CoreM (Option String × AxCache) := do
  let env ← getEnv
  let (b?, nextCache) := (findBadAxiom env cName).run cache
  if b?.isNone then return (none, nextCache)
  let axioms ← Lean.collectAxioms cName
  let bad := axioms.filter fun ax => !allowedAxioms.contains ax
  if bad.isEmpty then return (none, nextCache)
  else return (some (String.intercalate ", " (bad.toList.map (·.toString))), nextCache)

private partial def extractStringLit (e : Expr) : MetaM (Option String) := do
  let e ← whnf e
  match e with
  | .lit (.strVal s) => return some s
  | _ => return none

private partial def extractListElems (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    return some #[]
  else if e.isAppOfArity ``List.cons 3 then
    let hd := e.appFn!.appArg!
    let tl := e.appArg!
    let some rest ← extractListElems tl | return none
    return some (#[hd] ++ rest)
  else
    return none

private partial def extractArrayElems (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``Array.mk 2 then
    extractListElems e.appArg!
  else if e.isAppOfArity ``List.toArray 2 then
    extractListElems e.appArg!
  else if e.isAppOfArity ``Array.emptyWithCapacity 2 then
    return some #[]
  else if e.isAppOf ``Array.mkEmpty then
    return some #[]
  else
    return none

private partial def hasPropField (env : Environment) (structName : Name) : MetaM Bool := do
  let some (.inductInfo ind) := env.find? structName | return false
  for ctorName in ind.ctors do
    let some (.ctorInfo ctor) := env.find? ctorName | continue
    let found ← forallTelescopeReducing ctor.type fun xs _ => do
      for i in [ind.numParams : xs.size] do
        let fTy ← inferType xs[i]!
        if fTy.isSort then
          let .sort lvl := fTy | pure ()
          if lvl == Level.zero then
            return true
      return false
    if found then return true
  return false

private partial def typeCarriesStringProse (ty : Expr) : MetaM Bool := do
  let t := (← whnf ty).consumeMData
  if t.isForall then return false
  if t.isConstOf ``String then return true
  if t.isAppOfArity ``List 1 || t.isAppOfArity ``Array 1 || t.isAppOfArity ``Option 1 then
    return ← typeCarriesStringProse t.appArg!
  if t.isAppOfArity ``Prod 2 then
    return (← typeCarriesStringProse t.appFn!.appArg!) || (← typeCarriesStringProse t.appArg!)
  if t.isAppOfArity ``Sigma 2 || t.isAppOfArity ``PSigma 2 || t.isAppOfArity ``Subtype 2 then
    return ← typeCarriesStringProse t.appFn!.appArg!
  return false

private partial def hasPropCodomain (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ ret => return (← whnf ret).consumeMData.isProp

private partial def collectTransitiveDeps
    (env : Environment)
    (roots : Array Name) : Std.HashSet Name :=
  let rec go (work : List Name) (seen : Std.HashSet Name) : Std.HashSet Name :=
    match work with
    | [] => seen
    | cur :: rest =>
      if seen.contains cur then go rest seen
      else
        let seen' := seen.insert cur
        let modName := moduleOfConst env cur
        if !isProjectModule modName then go rest seen'
        else
          let used := match env.find? cur with
            | some (.defnInfo dv) => (dv.type.getUsedConstants ++ dv.value.getUsedConstants).toList
            | some (.thmInfo tv) => (tv.type.getUsedConstants ++ tv.value.getUsedConstants).toList
            | some (.opaqueInfo ov) => (ov.type.getUsedConstants ++ ov.value.getUsedConstants).toList
            | _ => []
          go (used ++ rest) seen'
  go roots.toList {}

private partial def isNondetUnitSpecType (ty : Expr) : MetaM Bool := do
  forallTelescopeReducing ty fun xs body => do
    let mut hasNondetInst := false
    for x in xs do
      let xTy ← whnf (← inferType x)
      if xTy.isAppOfArity `Core.NondetTest 1 then
        hasNondetInst := true
    if !hasNondetInst then return false
    let body := body.consumeMData
    if let .app f a := body then
      return a.consumeMData.isConstOf ``Unit && f.consumeMData.isFVar
    return false

private partial def isFallibleCodomain (ty : Expr) : MetaM Bool := do
  let rec check (e : Expr) : MetaM Bool := do
    let e := e.consumeMData
    if e.isAppOfArity ``Except 2 then return true
    if e.isAppOfArity ``ExceptT 3 then return true
    if e.isAppOfArity ``IO 1 then return ← check e.appArg!
    if e.isAppOfArity ``BaseIO 1 then return ← check e.appArg!
    if e.isAppOfArity ``EIO 2 then return ← check e.appArg!
    if e.isAppOfArity ``EST 3 then return ← check e.appArg!
    if e.isAppOfArity ``EST.Out 3 then return ← check e.appArg!
    if e.isForall then
      return ← forallTelescope e fun _ inner => check inner
    let e' ← whnf e
    if e' != e then return ← check e'
    return false
  check ty

private partial def hasFallibleSurface
    (env : Environment) (visited : Std.HashSet Name) (ty : Expr) : MetaM Bool := do
  if ← isFallibleCodomain ty then
    return true
  let rec checkStruct (e : Expr) : MetaM Bool := do
    let e := e.consumeMData
    if e.isAppOfArity ``IO 1 then return ← checkStruct e.appArg!
    if e.isAppOfArity ``BaseIO 1 then return ← checkStruct e.appArg!
    if e.isAppOfArity ``EIO 2 then return ← checkStruct e.appArg!
    if e.isAppOfArity ``EST 3 then return ← checkStruct e.appArg!
    if e.isAppOfArity ``EST.Out 3 then return ← checkStruct e.appArg!
    if e.isForall then
      return ← forallTelescope e fun _ inner => checkStruct inner
    let e' ← whnf e
    if e' != e then return ← checkStruct e'
    if let .const structName _ := e.getAppFn.consumeMData then
      if Lean.isStructure env structName &&
          isProjectModule (moduleOfConst env structName) &&
          !visited.contains structName then
        let visited' := visited.insert structName
        let fields := Lean.getStructureFields env structName
        return ← Meta.withLocalDeclD `s e fun fvar => do
          for i in [:fields.size] do
            let proj := mkProj structName i fvar
            let fieldTy ← inferType proj
            if ← hasFallibleSurface env visited' fieldTy then
              return true
          return false
    return false
  checkStruct ty

private def parseAssumptionObligation (e : Expr) : MetaM (Option (String × String × Option String)) := do
  let e ← whnf e
  if !e.isAppOfArity `Core.AssumptionObligation.mk 3 then
    return none
  let args := e.getAppArgs
  let some obName ← extractStringLit args[0]! | return none
  let some subj ← extractStringLit args[1]! | return none
  let fpExpr ← whnf args[2]!
  if fpExpr.isAppOfArity ``Option.none 1 then
    return some (obName, subj, none)
  else if fpExpr.isAppOfArity ``Option.some 2 then
    let some fpStr ← extractStringLit fpExpr.appArg! | return none
    return some (obName, subj, some fpStr)
  else
    return none

private def parseErrorObligation (e : Expr) : MetaM (Option (String × Name × Name × String)) := do
  let e ← whnf e
  if !e.isAppOfArity `Core.ErrorObligation.mk 4 then
    return none
  let args := e.getAppArgs
  let some req ← extractStringLit args[1]! | return none
  let kindExpr ← whnf args[2]!
  let .const kindCtor _ := kindExpr.getAppFn | return none
  let justExpr ← whnf args[3]!
  if justExpr.isAppOfArity `Core.ErrorJustification.provedImpossible 1 then
    let some thmStr ← extractStringLit justExpr.appArg! | return none
    return some (req, kindCtor, `provedImpossible, thmStr)
  else if justExpr.isAppOfArity `Core.ErrorJustification.tested 2 then
    let some testStr ← extractStringLit justExpr.appFn!.appArg! | return none
    let modeExpr ← whnf justExpr.appArg!
    let .const modeCtor _ := modeExpr.getAppFn | return none
    return some (req, kindCtor, modeCtor, testStr)
  else
    return none

private def parseRegisteredAssumption (e : Expr) : MetaM (Option (String × Expr)) := do
  let e ← whnf e
  if !e.isAppOfArity `Core.RegisteredAssumption.mk 2 then
    return none
  let some specName ← extractStringLit e.appFn!.appArg! | return none
  return some (specName, e.appArg!)

private def parseRegisteredErrorTest (e : Expr) : MetaM (Option (String × Name × Expr)) := do
  let e ← whnf e
  if !e.isAppOfArity `Core.RegisteredErrorTest.mk 3 then
    return none
  let args := e.getAppArgs
  let some testName ← extractStringLit args[0]! | return none
  let modeExpr ← whnf args[1]!
  let .const modeCtor _ := modeExpr.getAppFn | return none
  return some (testName, modeCtor, args[2]!)

private def checkKindExtractorValid (env : Environment) (errTypeName enumName : Name) (kindFn : Expr) : MetaM Bool := do
  let kf := kindFn.consumeMData
  let some (.inductInfo errInd) := env.find? errTypeName | return false
  let some (.inductInfo enumInd) := env.find? enumName | return false
  if errInd.ctors.isEmpty || enumInd.ctors.isEmpty then return false
  if Lean.isStructure env errTypeName then
    let .const fnName _ := kf.getAppFn.consumeMData | return false
    if fnName != Name.str errTypeName "kind" || !env.isProjectionFn fnName then
      return false
    let some cName := errInd.ctors.head? | return false
    let some (.ctorInfo ctor) := env.find? cName | return false
    return ← forallTelescopeReducing ctor.type fun xs _ => do
      let ctorConst := mkConst cName (ctor.levelParams.map Level.param)
      let reduced ← whnf (mkApp kf (mkAppN ctorConst xs))
      let rf := reduced.consumeMData
      if !rf.isFVar then return false
      let fTy ← whnf (← inferType rf)
      return fTy.consumeMData.getAppFn.constName? == some enumName
  if errInd.ctors.length != enumInd.ctors.length then return false
  let mut seenCtors : Std.HashSet Name := {}
  for cName in errInd.ctors do
    let some (.ctorInfo ctor) := env.find? cName | return false
    let mapped? ← forallTelescopeReducing ctor.type fun xs _ => do
      let ctorConst := mkConst cName (ctor.levelParams.map Level.param)
      let reduced ← whnf (mkApp kf (mkAppN ctorConst xs))
      let .const kCtor _ := reduced.consumeMData.getAppFn.consumeMData | return none
      if !enumInd.ctors.contains kCtor then return none
      if kCtor.getString! != cName.getString! then return none
      return some kCtor
    let some kCtor := mapped? | return false
    seenCtors := seenCtors.insert kCtor
  return seenCtors.size == errInd.ctors.length

private def checkProvedImpossibleTheorem
    (env : Environment)
    (tv : TheoremVal)
    (reqName kindCtor enumName : Name) : MetaM (Option String) := do
  forallTelescope tv.type fun xs concl => do
    for x in xs do
      if ← isProp (← inferType x) then
        return some "CONDITIONAL_IMPOSSIBLE_THEOREM: has Prop hypothesis"
    let concl := concl.consumeMData
    let verifyActAndArgs (actExpr : Expr) (neededArgs : Array FVarId) : Option String :=
      let fn := actExpr.consumeMData.getAppFn.consumeMData
      if !fn.isConstOf reqName then
        some s!"INVALID_IMPOSSIBLE_THEOREM_TARGET: expected {reqName}, got {fn}"
      else
        let appArgs := actExpr.consumeMData.getAppArgs
        let fvs := appArgs.filterMap (fun a => if a.consumeMData.isFVar then some a.consumeMData.fvarId! else none)
        if fvs.size != appArgs.size then
          some s!"NON_UNIVERSAL_IMPOSSIBLE_THEOREM: {reqName} applied to non-variable arguments"
        else
          let initSet : Std.HashSet FVarId := neededArgs.foldl (fun (s : Std.HashSet FVarId) fv => s.insert fv) {}
          let distinct := fvs.foldl (fun (s : Std.HashSet FVarId) fv => s.insert fv) initSet
          if distinct.size != fvs.size + neededArgs.size then
            some "ALIASED_ARGS_IN_IMPOSSIBLE_THEOREM"
          else none
    if concl.isAppOfArity `Core.NeverErrorKindIO 7 || concl.isAppOfArity `Core.NeverErrorKindBaseIO 7 then
      let args := concl.getAppArgs
      let kindFn := args[3]!
      let forbidden := args[4]!.consumeMData
      let actExpr := args[5]!
      let wExpr := args[6]!.consumeMData
      let errTy := args[0]!.consumeMData
      let some errTypeName := errTy.getAppFn.constName?
        | return some "INVALID_IMPOSSIBLE_THEOREM_ERROR_TYPE"
      unless ← checkKindExtractorValid env errTypeName enumName kindFn do
        return some "INVALID_KIND_EXTRACTOR_IN_THEOREM"
      unless forbidden.isConstOf kindCtor do
        return some s!"WRONG_ERROR_KIND_IN_THEOREM: expected {kindCtor}, got {forbidden}"
      if xs.size == 0 || !wExpr.isFVar || wExpr.fvarId! != xs.back!.fvarId! then
        return some "MISSING_WORLD_BINDER_IN_THEOREM"
      return verifyActAndArgs actExpr #[xs.back!.fvarId!]
    else if concl.isAppOfArity `Core.NeverErrorKindPure 6 then
      let args := concl.getAppArgs
      let kindFn := args[3]!
      let forbidden := args[4]!.consumeMData
      let actExpr := args[5]!
      let errTy := args[0]!.consumeMData
      let some errTypeName := errTy.getAppFn.constName?
        | return some "INVALID_IMPOSSIBLE_THEOREM_ERROR_TYPE"
      unless ← checkKindExtractorValid env errTypeName enumName kindFn do
        return some "INVALID_KIND_EXTRACTOR_IN_THEOREM"
      unless forbidden.isConstOf kindCtor do
        return some s!"WRONG_ERROR_KIND_IN_THEOREM: expected {kindCtor}, got {forbidden}"
      return verifyActAndArgs actExpr #[]
    else
      return some "INVALID_IMPOSSIBLE_THEOREM_SHAPE: must conclude Core.NeverErrorKind{IO,BaseIO,Pure}"

private def parseLogFile (logPath : System.FilePath) (expectedNonce? : Option String) :
    IO (Std.HashSet String × Std.HashSet (String × String) × Nat × Bool × Bool) := do
  let txt ← IO.FS.readFile logPath
  let mut assumpPass : Std.HashSet String := {}
  let mut errPass : Std.HashSet (String × String) := {}
  let mut badLines := 0
  let mut sawInit := false
  let mut sawClose := false
  for line in txt.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    let parts := trimmed.splitOn "|"
    match parts with
    | [nonce, "LOG_INIT"] =>
      if expectedNonce?.all (· == nonce) then
        sawInit := true
      else
        badLines := badLines + 1
    | [nonce, "LOG_CLOSE"] =>
      if expectedNonce?.all (· == nonce) then
        sawClose := true
      else
        badLines := badLines + 1
    | [nonce, "ASSUMP_PASS", name] =>
      if expectedNonce?.all (· == nonce) then
        assumpPass := assumpPass.insert name
      else
        badLines := badLines + 1
    | [nonce, "ERR_PASS", name, mode] =>
      if expectedNonce?.all (· == nonce) then
        errPass := errPass.insert (name, mode)
      else
        badLines := badLines + 1
    | _ =>
      badLines := badLines + 1
  return (assumpPass, errPass, badLines, sawInit, sawClose)


private def suiteCoversPackage (suiteKey : String) (dirPats : Array String) (pkg : Name) : Bool := Id.run do
  let comps := pkg.components.map (·.toString)
  let rest0 := match comps with
    | "LeanSwe" :: tail => tail
    | _ => []
  let rest :=
    if rest0.length >= 2 && rest0.getLast! == "Raw" then rest0.dropLast
    else rest0
  if rest.isEmpty then return false
  let restSlash := "/".intercalate rest
  let restUnder := "_".intercalate rest
  let lastSeg := rest.getLast!
  if !dirPats.contains s!"LeanSwe/{restSlash}/" then
    return false
  let normKey (s : String) : String :=
    ((s.toLower.replace "_" "").replace "-" "")
  let sk := suiteKey.toLower
  let suiteMatchesPkg :=
    sk == lastSeg.toLower ||
    sk == restSlash.toLower ||
    sk == restUnder.toLower ||
    normKey sk == normKey lastSeg ||
    normKey sk == normKey restUnder
  if !suiteMatchesPkg then
    return false
  let wantFuzzRest := s!"fuzz/{restSlash.toLower}/"
  let wantFuzzLast := s!"fuzz/{lastSeg.toLower}/"
  return dirPats.any fun p =>
    let pl := p.toLower
    pl == wantFuzzRest || pl == wantFuzzLast ||
      normKey pl == normKey wantFuzzRest || normKey pl == normKey wantFuzzLast

private def parseFuzzCoveredPackages (repoDir : System.FilePath) (knownPkgs : Array Name) :
    IO (Except String (Std.HashSet Name)) := do
  let manifestPath := repoDir / "Fuzz" / "suites.json"
  if !(← manifestPath.pathExists) then
    return .ok {}
  let raw ← IO.FS.readFile manifestPath
  match Lean.Json.parse raw with
  | .error err => return .error s!"MALFORMED_FUZZ_MANIFEST: {err}"
  | .ok j =>
    let .ok (.obj kvs) := j.getObjVal? "suites"
      | return .error "MALFORMED_FUZZ_MANIFEST: missing 'suites' object"
    let mut covered : Std.HashSet Name := {}
    for p in kvs do
      let .ok (.arr pathElems) := p.2.getObjVal? "paths"
        | return .error s!"MALFORMED_FUZZ_MANIFEST: suite '{p.1}' missing 'paths' array"
      let mut dirPats : Array String := #[]
      for pe in pathElems do
        let .str s := pe
          | return .error s!"MALFORMED_FUZZ_MANIFEST: suite '{p.1}' path entry must be string"
        if s.endsWith "/" then
          dirPats := dirPats.push s
      for pkg in knownPkgs do
        if suiteCoversPackage p.1 dirPats pkg then
          covered := covered.insert pkg
    return .ok covered

private def usesRuntimeFloat (env : Environment) (knownPkgs : Array Name) (pkgNs : Name) : Bool := Id.run do
  for h : mi in [0 : env.header.moduleNames.size] do
    let mName := env.header.moduleNames[mi]
    if mName.getRoot == `LeanSwe && pkgNamespaceOfSpecWith knownPkgs mName == pkgNs &&
        !isSpecOrRuntimeOrProofsModule mName && mName.getString! != "Model" then
      if let some md := env.header.moduleData[mi]? then
        for c in md.constants do
          let used := match c with
            | .defnInfo dv => dv.type.getUsedConstants ++ dv.value.getUsedConstants
            | .opaqueInfo ov => ov.type.getUsedConstants ++ ov.value.getUsedConstants
            | _ => c.type.getUsedConstants
          if used.any fun u =>
              let uMod := moduleOfConst env u
              uMod.getRoot == `Init && !uMod.toString.startsWith "Init.Data.Float.Model" &&
                (u == ``Float || u.toString.startsWith "Float.") &&
                (u == ``Float || Lean.isExtern env u) then
            return true
  return false

private def hasDirectOwnExternInPkg (env : Environment) (knownPkgs : Array Name) (pkgNs : Name) : Bool := Id.run do
  for h : mi in [0 : env.header.moduleNames.size] do
    let mName := env.header.moduleNames[mi]
    if mName.getRoot == `LeanSwe && pkgNamespaceOfSpecWith knownPkgs mName == pkgNs &&
        !isSpecOrRuntimeOrProofsModule mName && mName.getString! != "Model" then
      if let some md := env.header.moduleData[mi]? then
        if md.constants.any (fun c => Lean.isExtern env c.name) then
          return true
  return false

private def buildTransitiveImportFn (env : Environment) : Name → Std.HashSet Name := Id.run do
  let mut adj : Std.HashMap Name (Array Name) := {}
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if let some md := env.header.moduleData[i]? then
      adj := adj.insert m (md.imports.map (·.module))
  return fun root => Id.run do
    let mut work : Array Name := adj.getD root #[]
    let mut seen : Std.HashSet Name := {}
    while !work.isEmpty do
      let cur := work.back!
      work := work.pop
      if seen.contains cur then continue
      seen := seen.insert cur
      for nxt in adj.getD cur #[] do
        if !seen.contains nxt then
          work := work.push nxt
    return seen

private def kernelDefEq (a b : Expr) : MetaM Bool :=
  runBoundedMeta false do
    Meta.withNewMCtxDepth do
      withTheReader Core.Context (fun c => { c with maxRecDepth := min c.maxRecDepth 1024 }) do
        withTransparency .all <| isDefEq a b

private def isDefEqPropAtom (e : Expr) : MetaM Bool := do
  let p := e.consumeMData
  if p.isAppOfArity ``Eq 3 then
    if (p.getArg! 1).consumeMData == (p.getArg! 2).consumeMData then return true
    return ← kernelDefEq (p.getArg! 1) (p.getArg! 2)
  if p.isAppOfArity ``Iff 2 then
    if (p.getArg! 0).consumeMData == (p.getArg! 1).consumeMData then return true
    return ← kernelDefEq (p.getArg! 0) (p.getArg! 1)
  return false

private partial def exprAstNodesAtMost (limit : Nat) (e : Expr) : Option Nat :=
  if limit == 0 then none
  else
    match e with
    | .app f a => do
      let nf ← exprAstNodesAtMost (limit - 1) f
      let na ← exprAstNodesAtMost (limit - 1 - nf) a
      some (1 + nf + na)
    | .lam _ t b _ | .forallE _ t b _ => do
      let nt ← exprAstNodesAtMost (limit - 1) t
      let nb ← exprAstNodesAtMost (limit - 1 - nt) b
      some (1 + nt + nb)
    | .letE _ t v b _ => do
      let nt ← exprAstNodesAtMost (limit - 1) t
      let nv ← exprAstNodesAtMost (limit - 1 - nt) v
      let nb ← exprAstNodesAtMost (limit - 1 - nt - nv) b
      some (1 + nt + nv + nb)
    | .mdata _ b | .proj _ _ b => do
      let nb ← exprAstNodesAtMost (limit - 1) b
      some (1 + nb)
    | _ => some 1

private def stripOptParamType (t : Expr) : Expr :=
  let c := t.consumeMData
  if c.isAppOfArity ``optParam 2 then c.appFn!.appArg! else t

private def constHasTypeToTypeBinder (env : Environment) (fnName : Name) : Bool := Id.run do
  let some (.defnInfo dv) := env.find? fnName | return false
  let isTypeToType (e : Expr) : Bool :=
    match e.consumeMData with
    | .forallE _ (.sort (.succ .zero)) (.sort (.succ .zero)) _ => true
    | _ => false
  let mut t := dv.type.consumeMData
  while t.isForall do
    if let .forallE _ dom body _ := t then
      if isTypeToType dom then return true
      t := body.consumeMData
    else
      break
  return false

private partial def isProvablyInhabitedDataType (env : Environment) (fuel : Nat) (ty : Expr) : MetaM Bool := do
  if fuel == 0 then return false
  if ← isProp ty then return false
  let c := ty.consumeMData
  if c == .sort (.succ .zero) then return true
  if let .forallE _ (.sort (.succ .zero)) (.sort (.succ .zero)) _ := c then return true
  let l0 := [Level.succ Level.zero]
  if (← withLCtx {} #[] (runBoundedMeta none (some <$> synthInstance (mkApp (mkConst ``Inhabited l0) ty)))).isSome then
    return true
  if (← withLCtx {} #[] (runBoundedMeta none (some <$> synthInstance (mkApp (mkConst ``Nonempty l0) ty)))).isSome then
    return true
  let w := (← runBoundedMeta ty (whnf ty)).consumeMData
  if w.isConstOf ``Empty || w.isConstOf ``PEmpty then return false
  if w.isForall then
    return ← forallTelescope w fun _ ret => isProvablyInhabitedDataType env (fuel - 1) ret
  let .const indName lvls := w.getAppFn.consumeMData | return false
  let some (.inductInfo iv) := env.find? indName | return false
  if iv.numIndices > 0 || iv.ctors.isEmpty then return false
  let indArgs := w.getAppArgs
  if indArgs.size < iv.numParams then return false
  let params := indArgs.extract 0 iv.numParams
  for ctorName in iv.ctors do
    if let some (.ctorInfo _) := env.find? ctorName then
      let ctorApp := mkAppN (mkConst ctorName lvls) params
      let ctorTy ← inferType ctorApp
      let okCtor ← forallTelescope ctorTy fun fxs _ => do
        for fx in fxs do
          let fTy ← inferType fx
          if ← isProp fTy then
            if !(← isStaticTrueProp fTy) then return false
          else
            if !(← isProvablyInhabitedDataType env (fuel - 1) fTy) then return false
        return true
      if okCtor then return true
  return false

private def areOuterDataBindersInhabited (env : Environment) (xs : Array Expr) : MetaM Bool := do
  let mut subst : Array (Expr × Expr) := #[]
  for x in xs do
    let xTyRaw ← inferType x
    if ← isProp xTyRaw then continue
    let xTy := if subst.isEmpty then xTyRaw else xTyRaw.replace fun u =>
      (subst.find? (fun (fr, _) => fr == u)).map Prod.snd
    let xc := xTy.consumeMData
    if xc == .sort (.succ .zero) then
      subst := subst.push (x, mkConst ``Nat)
    else if let .const clsName _ := xc.getAppFn.consumeMData then
      if Lean.isClass env clsName then
        match ← withLCtx {} #[] (runBoundedMeta none (some <$> synthInstance xTy)) with
        | some inst => subst := subst.push (x, inst)
        | none => return false
      else if !(← isProvablyInhabitedDataType env 8 xTy) then
        return false
    else if !(← isProvablyInhabitedDataType env 8 xTy) then
      return false
  return true

private def isAllowedImplicitEtaDomain (env : Environment) (dom : Expr) : Bool :=
  let c := dom.consumeMData
  if c == .sort (.succ .zero) then true
  else if let .forallE _ (.sort (.succ .zero)) (.sort (.succ .zero)) _ := c then true
  else
    match c.getAppFn.consumeMData with
    | .const clsName _ => Lean.isClass env clsName
    | _ => false

private def checkBareConstArg
    (env : Environment)
    (outerAllowedFVars : Std.HashSet FVarId)
    (allowId : Bool)
    (rawArg : Expr) : MetaM (Option Name) := do
  let clean := rawArg.consumeMData
  if allowId && clean.isAppOfArity ``id 1 then
    return some ``id
  let checkAppBody (allowedFVars : Std.HashSet FVarId) (body : Expr) : Option Name := Id.run do
    let bc := body.consumeMData
    let .const fn _ := bc.getAppFn.consumeMData | return none
    if isCompilerAux fn then return none
    let mut seenFVs : Std.HashSet FVarId := {}
    for a in bc.getAppArgs do
      let ac := a.consumeMData
      let .fvar fv := ac | return none
      if !allowedFVars.contains fv || seenFVs.contains fv then
        return none
      seenFVs := seenFVs.insert fv
    return some fn
  if clean.isLambda then
    lambdaTelescope clean fun lxs body => do
      let mut allowed := outerAllowedFVars
      for lx in lxs do
        let bi ← lx.fvarId!.getBinderInfo
        if bi == .default then return none
        let dom ← inferType lx
        if !isAllowedImplicitEtaDomain env dom then return none
        allowed := allowed.insert lx.fvarId!
      return checkAppBody allowed body
  else
    return checkAppBody outerAllowedFVars clean

private partial def collectDirectStructFields (env : Environment) (e : Expr) (acc : Std.HashSet (Name × Nat) := {}) :
    Std.HashSet (Name × Nat) :=
  let c := e.consumeMData
  match c with
  | .proj stName idx inner =>
    collectDirectStructFields env inner (acc.insert (stName, idx))
  | .const fn _ =>
    if env.isProjectionFn fn && fn.isStr then
      let stName := fn.getPrefix
      if Lean.isStructure env stName then
        let fldName := Name.mkSimple fn.getString!
        match (Lean.getStructureFields env stName).findIdx? (· == fldName) with
        | some idx => acc.insert (stName, idx)
        | none => acc
      else acc
    else acc
  | .app f a =>
    collectDirectStructFields env a (collectDirectStructFields env f acc)
  | .lam _ t b _ | .forallE _ t b _ =>
    collectDirectStructFields env b (collectDirectStructFields env t acc)
  | .letE _ t v b _ =>
    collectDirectStructFields env b (collectDirectStructFields env v (collectDirectStructFields env t acc))
  | .mdata _ inner =>
    collectDirectStructFields env inner acc
  | _ => acc

private def collectUsedStructFieldsTransitive
    (env : Environment)
    (allowedMods : Std.HashSet Name)
    (skipConsts : Std.HashSet Name)
    (rootFn : Name) : Std.HashSet (Name × Nat) := Id.run do
  let mut work : Array Name := #[rootFn]
  let mut seen : Std.HashSet Name := {}
  let mut fields : Std.HashSet (Name × Nat) := {}
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains cur || skipConsts.contains cur then continue
    seen := seen.insert cur
    if cur != rootFn && !allowedMods.contains (moduleOfConst env cur) then continue
    if let some (.defnInfo dv) := env.find? cur then
      fields := collectDirectStructFields env dv.value fields
      for u in dv.value.getUsedConstants do
        if !seen.contains u && !skipConsts.contains u && allowedMods.contains (moduleOfConst env u) then
          work := work.push u
  return fields

private def collectCoveredMkApiImplHelpers
    (env : Environment)
    (implMod mkApiFn : Name)
    (execFields : Std.HashSet (Name × Nat)) : MetaM (Std.HashSet Name) := do
  let some (.defnInfo dv) := env.find? mkApiFn | return {}
  lambdaTelescope dv.value fun _ body => do
    let bc := body.consumeMData
    let .const ctorName _ := bc.getAppFn.consumeMData | return {}
    let some (.ctorInfo ci) := env.find? ctorName | return {}
    let stName := ci.induct
    let cArgs := bc.getAppArgs
    let mut helpers : Std.HashSet Name := {}
    for fldIdx in [0 : ci.numFields] do
      if execFields.contains (stName, fldIdx) && ci.numParams + fldIdx < cArgs.size then
        for u in cArgs[ci.numParams + fldIdx]!.getUsedConstants do
          if moduleOfConst env u == implMod && !isCompilerAux u then
            helpers := helpers.insert u
    return helpers

private def constTransitivelyTouchesSweImplOrIfaceCached
    (env : Environment)
    (cleanRef : IO.Ref (Std.HashSet Name))
    (start : Name) : IO Bool := do
  let clean0 ← cleanRef.get
  if clean0.contains start then return false
  let mut work : Array Name := #[start]
  let mut seen : Std.HashSet Name := {}
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains cur || clean0.contains cur then continue
    seen := seen.insert cur
    let m := moduleOfConst env cur
    if m.getRoot == `LeanSwe && m.isStr && (m.getString! == "Interface" || m.getString! == "Impl") then
      return true
    if !isProjectModule m then continue
    if let some cinfo := env.find? cur then
      let deps : Array Name := match cinfo with
        | .defnInfo dv => dv.type.getUsedConstants ++ dv.value.getUsedConstants
        | .opaqueInfo ov => ov.type.getUsedConstants ++ ov.value.getUsedConstants
        | _ => cinfo.type.getUsedConstants
      for u in deps do
        if !seen.contains u && !clean0.contains u then
          work := work.push u
  cleanRef.modify fun s => seen.fold (init := s) fun acc v => acc.insert v
  return false

private def isCapabilityBundleConst
    (env : Environment)
    (knownPkgs : Array Name)
    (pkg cName : Name)
    (ty : Expr) : MetaM Bool := do
  if cName != Name.str pkg "defaultApi" && cName != Name.str pkg "defaultOps" then
    return false
  forallTelescope ty fun fxs ret => do
    for fx in fxs do
      if (← fx.fvarId!.getBinderInfo) == .default then return false
    let rc := ret.consumeMData
    if rc.isAppOfArity ``IO 1 || rc.isAppOfArity ``BaseIO 1 || rc.isAppOfArity ``EIO 2 then
      return false
    let rw := (← whnf ret).consumeMData
    let .const stName _ := rw.getAppFn.consumeMData | return false
    if !Lean.isStructure env stName then return false
    return pkgNamespaceOfSpecWith knownPkgs (moduleOfConst env stName) == pkg

private def isEffectfulInterfaceOp (env : Environment) (ty : Expr) (cName : Name) : MetaM Bool := do
  if constHasTypeToTypeBinder env cName then return true
  forallTelescope ty fun fxs ret => do
    let rc := ret.consumeMData
    if rc.isAppOfArity ``IO 1 || rc.isAppOfArity ``BaseIO 1 ||
        rc.isAppOfArity ``EIO 2 || rc.isAppOfArity ``EStateM 3 ||
        rc.isAppOfArity ``StateT 3 || rc.isAppOfArity ``StateM 2 then
      return true
    if let .fvar fv := rc.getAppFn.consumeMData then
      if fxs.any (·.fvarId! == fv) then return true
    let rw := (← whnf ret).consumeMData
    return rw.isAppOfArity ``EIO 2 || rw.isAppOfArity ``EStateM 3

private def checkWfNotVacuous (env : Environment) (sTy : Expr) (wfFn : Name) : MetaM Bool := do
  let some (.defnInfo _) := env.find? wfFn | return false
  if !(← isProvablyInhabitedDataType env 8 sTy) then return false
  withLocalDeclD `_wfState sTy fun s => do
    let app := mkApp (mkConst wfFn) s
    let w ← runBoundedMeta app (withTransparency .all (whnf app))
    if w.consumeMData.isConstOf ``Bool.false then return false
    let eqTrue := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) app (mkConst ``Bool.true)
    if ← isStaticFalseProp eqTrue then return false
    return true

private def isTrivialPayloadType (ty : Expr) : MetaM Bool := do
  if ← isProp ty then return true
  let w := (← runBoundedMeta ty (whnf ty)).consumeMData
  return w.isConstOf ``Unit || w.isConstOf ``PUnit || w.isConstOf ``Empty || w.isConstOf ``PEmpty

private partial def stripSyntacticReflAtoms (e : Expr) : Expr :=
  let c := e.consumeMData
  if c.isAppOfArity ``Eq 3 && (c.getArg! 1).consumeMData == (c.getArg! 2).consumeMData then
    mkConst ``True
  else if c.isAppOfArity ``Iff 2 && (c.getArg! 0).consumeMData == (c.getArg! 1).consumeMData then
    mkConst ``True
  else
    match e with
    | .app f a => .app (stripSyntacticReflAtoms f) (stripSyntacticReflAtoms a)
    | .lam n t b bi => .lam n (stripSyntacticReflAtoms t) (stripSyntacticReflAtoms b) bi
    | .forallE n t b bi => .forallE n (stripSyntacticReflAtoms t) (stripSyntacticReflAtoms b) bi
    | .letE n t v b nd => .letE n (stripSyntacticReflAtoms t) (stripSyntacticReflAtoms v) (stripSyntacticReflAtoms b) nd
    | .mdata md b => .mdata md (stripSyntacticReflAtoms b)
    | .proj tn idx s => .proj tn idx (stripSyntacticReflAtoms s)
    | _ => e

private partial def reduceMatchersBounded (fuel : Nat) (e : Expr) : MetaM Expr := do
  if fuel == 0 then return e
  let b := (← runBoundedMeta e (Core.betaReduce e)).headBeta.consumeMData
  match ← runBoundedMeta ReduceMatcherResult.notMatcher (Meta.reduceMatcher? b) with
  | .reduced b' => reduceMatchersBounded (fuel - 1) b'
  | _ =>
    match b with
    | .app f a =>
      let f' ← reduceMatchersBounded (fuel - 1) f
      let a' ← reduceMatchersBounded (fuel - 1) a
      let appE := (Expr.app f' a').headBeta
      match ← runBoundedMeta ReduceMatcherResult.notMatcher (Meta.reduceMatcher? appE) with
      | .reduced r => reduceMatchersBounded (fuel - 1) r
      | _ => return appE
    | .lam n t body bi =>
      withLocalDecl n bi t fun x => do
        let body' ← reduceMatchersBounded (fuel - 1) (body.instantiate1 x)
        mkLambdaFVars #[x] body'
    | .forallE n t body bi =>
      withLocalDecl n bi t fun x => do
        let body' ← reduceMatchersBounded (fuel - 1) (body.instantiate1 x)
        mkForallFVars #[x] body'
    | .letE _ _ v body _ =>
      if !body.hasLooseBVar 0 then
        reduceMatchersBounded (fuel - 1) (body.lowerLooseBVars 1 1)
      else if isSmallClosedExpr v then
        reduceMatchersBounded (fuel - 1) (body.instantiate1 v)
      else
        return b
    | _ => return b

private def expandModelPropRels (env : Environment) (modelMods : Std.HashSet Name) (extraFn : Name) (e : Expr) : MetaM Expr := do
  let shouldUnfold (fn : Name) : Bool :=
    fn == extraFn ||
      (modelMods.contains (moduleOfConst env fn) && !isCompilerAux fn &&
        match env.find? fn with
        | some (.defnInfo dv) =>
          dv.type.getForallBody.consumeMData == .sort .zero && (exprAstNodesAtMost 4096 dv.value).isSome
        | _ => false)
  let d ← runBoundedMeta e (Meta.deltaExpand e shouldUnfold (allowOpaque := false))
  let r ← reduceMatchersBounded 16 d
  return stripSyntacticReflAtoms r

private def checkWrappedPayloadSensitive
    (env : Environment)
    (modelMods : Std.HashSet Name)
    (mkPred : Expr → MetaM Expr)
    (unfoldFn : Name)
    (ty : Expr) : MetaM Bool := do
  let ow := (← runBoundedMeta ty (whnf ty)).consumeMData
  if ow.isAppOfArity ``Except 2 then
    let lvls := ow.getAppFn.consumeMData.constLevels!
    let errTy := ow.appFn!.appArg!
    let okTy := ow.appArg!
    if !(← isTrivialPayloadType okTy) then
      return ← withLocalDeclD `_refOk1 okTy fun v1 =>
        withLocalDeclD `_refOk2 okTy fun v2 => do
          let pOk1 ← mkPred (mkApp3 (mkConst ``Except.ok lvls) errTy okTy v1)
          let pOk2 ← mkPred (mkApp3 (mkConst ``Except.ok lvls) errTy okTy v2)
          let expOk1 ← expandModelPropRels env modelMods unfoldFn pOk1
          if !expOk1.hasAnyFVar (· == v1.fvarId!) then return false
          if (← isDefEqPropAtom expOk1) || (← isStaticTrueProp expOk1) then return false
          if ← kernelDefEq pOk1 pOk2 then return false
          return true
  else if ow.isAppOfArity ``Option 1 then
    let lvls := ow.getAppFn.consumeMData.constLevels!
    let valTy := ow.appArg!
    if !(← isTrivialPayloadType valTy) then
      return ← withLocalDeclD `_refSome1 valTy fun v1 =>
        withLocalDeclD `_refSome2 valTy fun v2 => do
          let pSm1 ← mkPred (mkApp2 (mkConst ``Option.some lvls) valTy v1)
          let pSm2 ← mkPred (mkApp2 (mkConst ``Option.some lvls) valTy v2)
          let expSm1 ← expandModelPropRels env modelMods unfoldFn pSm1
          if !expSm1.hasAnyFVar (· == v1.fvarId!) then return false
          if (← isDefEqPropAtom expSm1) || (← isStaticTrueProp expSm1) then return false
          if ← kernelDefEq pSm1 pSm2 then return false
          return true
  return true

private partial def hasVacuousInputBranch (fuel : Nat) (outFV : FVarId) (isConjPart : Bool) (e : Expr) : MetaM Bool := do
  if fuel == 0 then return false
  let c := e.consumeMData
  if !c.hasAnyFVar (· == outFV) then
    return true
  if c.isAppOfArity ``And 2 then
    return (← hasVacuousInputBranch (fuel - 1) outFV true c.appFn!.appArg!) ||
      (← hasVacuousInputBranch (fuel - 1) outFV true c.appArg!)
  if c.isAppOfArity ``ite 5 then
    let cond := c.getArg! 1
    let tBr := c.getArg! 3
    let eBr := c.getArg! 4
    if !cond.hasAnyFVar (· == outFV) then
      return (← hasVacuousInputBranch (fuel - 1) outFV isConjPart tBr) ||
        (← hasVacuousInputBranch (fuel - 1) outFV isConjPart eBr)
  if c.isAppOfArity ``dite 5 then
    let cond := c.getArg! 1
    let tLam := c.getArg! 3
    let eLam := c.getArg! 4
    if !cond.hasAnyFVar (· == outFV) then
      let badT ← withLocalDeclD `_ditePos cond fun hp =>
        hasVacuousInputBranch (fuel - 1) outFV isConjPart ((Expr.app tLam hp).headBeta)
      if badT then return true
      let negCond := mkApp (mkConst ``Not) cond
      return ← withLocalDeclD `_diteNeg negCond fun hn =>
        hasVacuousInputBranch (fuel - 1) outFV isConjPart ((Expr.app eLam hn).headBeta)
  if let .forallE n dom body bi := c then
    if !dom.hasAnyFVar (· == outFV) then
      if ← isProp dom then
        if !isConjPart && !(← isStaticTrueProp dom) then
          return true
      return ← withLocalDecl n bi dom fun hx =>
        hasVacuousInputBranch (fuel - 1) outFV isConjPart (body.instantiate1 hx)
  return ← isDefEqPropAtom c

private partial def collectAllInputImplicationGuards (fuel : Nat) (outFV : FVarId) (e : Expr) :
    MetaM (Option (Array Expr)) := do
  if fuel == 0 then return none
  let c := e.consumeMData
  if c.isAppOfArity ``And 2 then
    let some gl ← collectAllInputImplicationGuards (fuel - 1) outFV c.appFn!.appArg! | return none
    let some gr ← collectAllInputImplicationGuards (fuel - 1) outFV c.appArg! | return none
    return some (gl ++ gr)
  if let .forallE _ dom _ _ := c then
    if !dom.hasAnyFVar (· == outFV) && !dom.hasLooseBVars then
      if ← isProp dom then
        return some #[dom]
  return none

private def groundSamplesForType (ty : Expr) : MetaM (Option (Array Expr)) := do
  let w := (← runBoundedMeta ty (whnf ty)).consumeMData
  let mkNatLitTyped (t : Expr) (n : Nat) : MetaM (Option Expr) := do
    let instTy := mkApp2 (mkConst ``OfNat [Level.zero]) t (mkRawNatLit n)
    match ← withLCtx {} #[] (runBoundedMeta none (some <$> synthInstance instTy)) with
    | some inst => pure (some (mkApp3 (mkConst ``OfNat.ofNat [Level.zero]) t (mkRawNatLit n) inst))
    | none => pure none
  if w.isConstOf ``Nat || w.isConstOf ``Int ||
      w.isConstOf ``UInt8 || w.isConstOf ``UInt16 ||
      w.isConstOf ``UInt32 || w.isConstOf ``UInt64 || w.isConstOf ``USize then
    if let some v0 ← mkNatLitTyped w 0 then
      if let some v1 ← mkNatLitTyped w 1 then
        if let some v2 ← mkNatLitTyped w 2 then
          return some #[v0, v1, v2]
  if w.isConstOf ``String then
    return some #[mkStrLit "", mkStrLit "a", mkStrLit "b"]
  if w.isConstOf ``Bool then
    return some #[mkConst ``Bool.false, mkConst ``Bool.true]
  return none

private def checkPureAllowedNonTrivial
    (env : Environment)
    (modelMods : Std.HashSet Name)
    (specSubst : Expr)
    (specFn : Name)
    (inTysSubst : Array Expr)
    (outTySubst : Expr) : MetaM Bool := do
  let mut allGroundSamples : Option (Array (Array Expr)) := some #[]
  for inTy in inTysSubst do
    if let some arr := allGroundSamples then
      match ← groundSamplesForType inTy with
      | some sVals => allGroundSamples := some (arr.push sVals)
      | none => allGroundSamples := none
  let rec withInputs (idx : Nat) (acc : Array Expr) : MetaM Bool := do
    if h : idx < inTysSubst.size then
      withLocalDeclD (Name.num `_refIn idx) inTysSubst[idx] fun v =>
        withInputs (idx + 1) (acc.push v)
    else
      withLocalDeclD `_refOut1 outTySubst fun y1 =>
      withLocalDeclD `_refOut2 outTySubst fun y2 => do
        let p1 := (mkAppN specSubst (acc.push y1)).headBeta
        let p2 := (mkAppN specSubst (acc.push y2)).headBeta
        let exp1 ← expandModelPropRels env modelMods specFn p1
        if !exp1.hasAnyFVar (· == y1.fvarId!) then return false
        if ← hasVacuousInputBranch 32 y1.fvarId! false exp1 then return false
        for k in [0 : inTysSubst.size] do
          if !(← isTrivialPayloadType inTysSubst[k]!) then
            if !exp1.hasAnyFVar (· == acc[k]!.fvarId!) then return false
        if ← kernelDefEq p1 p2 then return false
        let u1 := (← runBoundedMeta p1 (Meta.deltaExpand p1 (· == specFn) (allowOpaque := false))).headBeta
        if (← isDefEqPropAtom p1) || (← isStaticTrueProp p1) ||
            (← isDefEqPropAtom u1) || (← isStaticTrueProp u1) ||
            (← isDefEqPropAtom exp1) || (← isStaticTrueProp exp1) then
          return false
        if let some guards ← collectAllInputImplicationGuards 16 y1.fvarId! exp1 then
          if let some sampleGrid := allGroundSamples then
            if !sampleGrid.isEmpty then
              for si in [0 : 3] do
                let sampleInputs := sampleGrid.map fun sVals => sVals[Nat.min si (sVals.size - 1)]!
                let substIn (g : Expr) : Expr :=
                  g.replace fun u => Id.run do
                    for k in [0 : acc.size] do
                      if u == acc[k]! then return some sampleInputs[k]!
                    return none
                let mut anyGuardPossible := false
                for g in guards do
                  if !(← isStaticFalseProp (substIn g)) then
                    anyGuardPossible := true
                    break
                if !anyGuardPossible then
                  return false
        let u1w := (← runBoundedMeta u1 (whnf u1)).consumeMData
        if u1w.isAppOfArity ``Or 2 then
          if ← isNegationPair u1w.appFn!.appArg! u1w.appArg! then return false
        if outTySubst.consumeMData.isConstOf ``Bool then
          let pT := (mkAppN specSubst (acc.push (mkConst ``Bool.true))).headBeta
          let pF := (mkAppN specSubst (acc.push (mkConst ``Bool.false))).headBeta
          if (← isStaticTrueProp pT) && (← isStaticTrueProp pF) then return false
        if !(← checkWrappedPayloadSensitive env modelMods (fun y => pure (mkAppN specSubst (acc.push y)).headBeta) specFn outTySubst) then
          return false
        return true
  withInputs 0 #[]

private def checkStepAllowedNonTrivial
    (env : Environment)
    (modelMods : Std.HashSet Name)
    (allowedArg : Expr)
    (allowedFn : Name)
    (sTy reqTy outTy : Expr) : MetaM Bool := do
  withLocalDeclD `_stPre sTy fun s =>
  withLocalDeclD `_stReq reqTy fun req =>
  withLocalDeclD `_stOut1 outTy fun o1 =>
  withLocalDeclD `_stOut2 outTy fun o2 =>
  withLocalDeclD `_stPost1 sTy fun s1' =>
  withLocalDeclD `_stPost2 sTy fun s2' => do
    let p1 := (mkApp4 allowedArg s req o1 s1').headBeta
    let p2 := (mkApp4 allowedArg s req o2 s2').headBeta
    let exp1 ← expandModelPropRels env modelMods allowedFn p1
    if !exp1.hasAnyFVar (· == o1.fvarId!) && !exp1.hasAnyFVar (· == s1'.fvarId!) then
      return false
    if !(← isTrivialPayloadType reqTy) then
      if !exp1.hasAnyFVar (· == req.fvarId!) then return false
    if ← kernelDefEq p1 p2 then return false
    let u1 := (← runBoundedMeta p1 (Meta.deltaExpand p1 (· == allowedFn) (allowOpaque := false))).headBeta
    if (← isDefEqPropAtom p1) || (← isStaticTrueProp p1) ||
        (← isDefEqPropAtom u1) || (← isStaticTrueProp u1) ||
        (← isDefEqPropAtom exp1) || (← isStaticTrueProp exp1) then
      return false
    let u1w := (← runBoundedMeta u1 (whnf u1)).consumeMData
    if u1w.isAppOfArity ``Or 2 then
      if ← isNegationPair u1w.appFn!.appArg! u1w.appArg! then return false
    if !(← checkWrappedPayloadSensitive env modelMods (fun o => pure (mkApp4 allowedArg s req o s1').headBeta) allowedFn outTy) then
      return false
    let ow := (← runBoundedMeta outTy (whnf outTy)).consumeMData
    if let .const outIndName outLvls := ow.getAppFn.consumeMData then
      if isProjectModule (moduleOfConst env outIndName) then
        if let some (.inductInfo iv) := env.find? outIndName then
          if iv.numParams == 0 && iv.numIndices == 0 then
            for ctorName in iv.ctors do
              if let some (.ctorInfo ci) := env.find? ctorName then
                if ci.numFields == 1 then
                  let ctorConst := mkConst ctorName outLvls
                  let cTy ← inferType ctorConst
                  if let .forallE _ fldTy _ _ := (← runBoundedMeta cTy (whnf cTy)).consumeMData then
                    if !(← checkWrappedPayloadSensitive env modelMods
                        (fun inner => pure (mkApp4 allowedArg s req (mkApp ctorConst inner) s1').headBeta)
                        allowedFn fldTy) then
                      return false
    return true

private def checkRefinesModelTheorem
    (env : Environment)
    (transImpsOf : Name → Std.HashSet Name)
    (knownPkgs : Array Name)
    (pkg : Name)
    (modelMods : Std.HashSet Name)
    (axCacheIn : AxCache) : MetaM (Array String × AxCache) := do
  let mut errs : Array String := #[]
  let mut axCache := axCacheIn
  let topProofMod := Name.str pkg "Proofs"
  let thmName := Name.str topProofMod "refines_model"
  let ifaceMod := Name.str pkg "Interface"
  let implMod := Name.str pkg "Impl"

  for mMod in modelMods do
    for imp in transImpsOf mMod do
      if imp.getRoot == `LeanSwe && imp.isStr && (imp.getString! == "Interface" || imp.getString! == "Impl") then
        errs := errs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mMod} transitively imports {imp}"

  let some (.thmInfo tv) := env.find? thmName
    | return (#[s!"MISSING_REFINES_MODEL: {pkg} lacks public theorem {thmName}"], axCache)
  if isPrivateName thmName || moduleOfConst env thmName != topProofMod then
    return (#[s!"MISSING_REFINES_MODEL: {thmName} must be a public theorem in {topProofMod}"], axCache)

  let (badAx?, nextAx) ← checkAxiomsOk axCache thmName
  axCache := nextAx
  if let some badAx := badAx? then
    errs := errs.push s!"UNALLOWED_AXIOM_IN_THEOREM: {thmName} uses [{badAx}]"

  let coveredPureOpsRef ← IO.mkRef ({} : Std.HashSet Name)
  let coveredStepOpsRef ← IO.mkRef ({} : Std.HashSet Name)
  let coveredExecFieldsRef ← IO.mkRef ({} : Std.HashSet (Name × Nat))
  let coveredImplHelpersRef ← IO.mkRef ({} : Std.HashSet Name)
  let coveredCapBuildersRef ← IO.mkRef ({} : Std.HashSet Name)
  let safeModelConstsRef ← IO.mkRef ({} : Std.HashSet Name)

  let conjErrs ← forallTelescope tv.type fun outerXs topBody => do
    let mut localErrs : Array String := #[]
    for ox in outerXs do
      if ← isProp (← inferType ox) then
        return #[s!"CONDITIONAL_REFINES_MODEL: {thmName} has Prop hypothesis"]
    if !outerXs.isEmpty then
      if !(← areOuterDataBindersInhabited env outerXs) then
        return #[s!"UNINHABITED_BINDER_IN_REFINES_MODEL: {thmName} has uninhabited outer binder"]
      return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} must bind typeclass parameters per conjunct, not at outer theorem level"]

    for conj in collectConclusionAtoms topBody do
      let atomErrs ← forallTelescope conj fun axs atomBody => do
        let mut aErrs : Array String := #[]
        let mut typeFVars : Array Expr := #[]
        let mut instBinds : Array (Expr × Expr) := #[]
        let mut allowedAtomFVs : Std.HashSet FVarId := {}
        for ax in axs do
          let axTy ← inferType ax
          if ← isProp axTy then
            return #[s!"CONDITIONAL_REFINES_MODEL: {thmName} conjunct has Prop hypothesis"]
          let bi ← ax.fvarId!.getBinderInfo
          let axTyClean := axTy.consumeMData
          if (bi == .implicit || bi == .strictImplicit) && axTyClean == .sort (.succ .zero) then
            typeFVars := typeFVars.push ax
            allowedAtomFVs := allowedAtomFVs.insert ax.fvarId!
          else if bi == .instImplicit then
            match axTyClean.getAppFn.consumeMData with
            | .const clsName _ =>
              if Lean.isClass env clsName &&
                  axTyClean.getAppArgs.all (fun ca => typeFVars.any (· == ca.consumeMData)) &&
                  !axTyClean.getAppArgs.isEmpty then
                instBinds := instBinds.push (ax, axTyClean)
                allowedAtomFVs := allowedAtomFVs.insert ax.fvarId!
              else
                return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} has unsupported binder {axTyClean}"]
            | _ =>
              return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} has non-class binder {axTyClean}"]
          else
            return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} has explicit or non-Type binder in conjunct"]

        let mut substPairs : Array (Expr × Expr) := #[]
        let candidateWitnessTys : Array Expr := #[mkConst ``String, mkConst ``Nat, mkConst ``Bool, mkConst ``Int]
        for tfv in typeFVars do
          let mut foundWitness? : Option (Expr × Array (Expr × Expr)) := none
          for candTy in candidateWitnessTys do
            if foundWitness?.isSome then break
            let trialSubst := substPairs.push (tfv, candTy)
            let mut allInstOk := true
            let mut instSubst : Array (Expr × Expr) := #[]
            for (instVar, instTy) in instBinds do
              if instTy.hasAnyFVar (· == tfv.fvarId!) then
                let instTyGround := instTy.replace fun u =>
                  (trialSubst.find? (fun (fr, _) => fr == u)).map Prod.snd
                match ← withLCtx {} #[] (runBoundedMeta none (some <$> synthInstance instTyGround)) with
                | some instVal => instSubst := instSubst.push (instVar, instVal)
                | none => allInstOk := false
            if allInstOk then
              foundWitness? := some (candTy, instSubst)
          match foundWitness? with
          | some (wTy, wInsts) => substPairs := (substPairs.push (tfv, wTy)) ++ wInsts
          | none =>
            return #[s!"NON_INHABITED_TYPECLASS_IN_REFINES_MODEL: {thmName} quantifies over a typeclass without String/Nat/Bool/Int instance"]

        let applySubst (e : Expr) : Expr :=
          if substPairs.isEmpty then e
          else e.replace fun u => (substPairs.find? (fun (fr, _) => fr == u)).map Prod.snd

        let ab := atomBody.consumeMData
        let pureInfo? : Option (Bool × Array Expr × Expr × Expr × Expr) :=
          if ab.isAppOfArity `Core.RefinesPure 4 then
            let args := ab.getAppArgs; some (false, #[args[0]!], args[1]!, args[2]!, args[3]!)
          else if ab.isAppOfArity `Core.RefinesPure2 5 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!], args[2]!, args[3]!, args[4]!)
          else if ab.isAppOfArity `Core.RefinesPure3 6 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!, args[2]!], args[3]!, args[4]!, args[5]!)
          else if ab.isAppOfArity `Core.RefinesPure4 7 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!, args[2]!, args[3]!], args[4]!, args[5]!, args[6]!)
          else if ab.isAppOfArity `Core.RefinesPureEq 4 then
            let args := ab.getAppArgs; some (true, #[args[0]!], args[1]!, args[2]!, args[3]!)
          else if ab.isAppOfArity `Core.RefinesPureEq2 5 then
            let args := ab.getAppArgs; some (true, #[args[0]!, args[1]!], args[2]!, args[3]!, args[4]!)
          else if ab.isAppOfArity `Core.RefinesPureEq3 6 then
            let args := ab.getAppArgs; some (true, #[args[0]!, args[1]!, args[2]!], args[3]!, args[4]!, args[5]!)
          else if ab.isAppOfArity `Core.RefinesPureEq4 7 then
            let args := ab.getAppArgs; some (true, #[args[0]!, args[1]!, args[2]!, args[3]!], args[4]!, args[5]!, args[6]!)
          else none

        if let some (isEqKind, inTys, outTy, implArg, specArg) := pureInfo? then
          let some implFn ← checkBareConstArg env allowedAtomFVs false implArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare impl argument in {thmName}"]
          let some specFn ← checkBareConstArg env allowedAtomFVs false specArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare model/allowed argument in {thmName}"]
          if isPrivateName implFn || moduleOfConst env implFn != ifaceMod then
            aErrs := aErrs.push s!"NON_INTERFACE_IMPL_IN_REFINES: {implFn} in {thmName} is not a public constant in {ifaceMod}"
          if isPrivateName specFn || !modelMods.contains (moduleOfConst env specFn) then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {specFn} in {thmName} is not a public constant in {pkg}.Model"
          if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef specFn then
            aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {specFn} in {thmName} transitively references Interface/Impl"
          let inTysSubst := inTys.map (fun t => applySubst (stripOptParamType t))
          let outTySubst := applySubst (stripOptParamType outTy)
          for inTyS in inTysSubst do
            if !(← isProvablyInhabitedDataType env 8 inTyS) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited input domain for {implFn} in {thmName}"
          if isEqKind then
            if ← isProp outTySubst then
              aErrs := aErrs.push s!"TRIVIAL_CODOMAIN_IN_REFINES: Prop codomain in RefinesPureEq for {implFn} in {thmName}"
            else
              let ow := (← whnf outTySubst).consumeMData
              if ow.isConstOf ``Unit || ow.isConstOf ``PUnit then
                aErrs := aErrs.push s!"TRIVIAL_CODOMAIN_IN_REFINES: Unit codomain in RefinesPureEq for {implFn} in {thmName}"
          else
            let specSubst := applySubst specArg
            if !(← checkPureAllowedNonTrivial env modelMods specSubst specFn inTysSubst outTySubst) then
              aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {specFn} for {implFn} in {thmName} is output-insensitive or tautological"
          if aErrs.isEmpty then
            coveredPureOpsRef.modify (·.insert implFn)
          return aErrs

        let stepInfo? : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
          if ab.isAppOfArity `Core.RefinesStep 8 then
            let args := ab.getAppArgs
            some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!)
          else if ab.isAppOfArity `Core.RefinesStepId 6 then
            let args := ab.getAppArgs
            let sTy := args[0]!
            some (sTy, sTy, args[1]!, args[2]!, mkApp (mkConst ``id [Level.succ Level.zero]) sTy, args[3]!, args[4]!, args[5]!)
          else none

        if let some (wTy, sTy, reqTy, outTy, projArg, wfArg, stepArg, allowedArg) := stepInfo? then
          if !axs.isEmpty then
            return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} RefinesStep conjunct cannot have binders"]
          let some projFn ← checkBareConstArg env {} true projArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare proj argument in {thmName}"]
          let some wfFn ← checkBareConstArg env {} false wfArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare wf argument in {thmName}"]
          let some stepFn ← checkBareConstArg env {} false stepArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare step argument in {thmName}"]
          let some allowedFn ← checkBareConstArg env {} false allowedArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare allowed argument in {thmName}"]
          if projFn != ``id && (isPrivateName projFn || !modelMods.contains (moduleOfConst env projFn)) then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {projFn} in {thmName} must be id or a public Model constant"
          if isPrivateName wfFn || !modelMods.contains (moduleOfConst env wfFn) then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {wfFn} in {thmName} is not a public constant in {pkg}.Model"
          if isPrivateName allowedFn || !modelMods.contains (moduleOfConst env allowedFn) then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {allowedFn} in {thmName} is not a public constant in {pkg}.Model"
          let stepMod := moduleOfConst env stepFn
          if isPrivateName stepFn || modelMods.contains stepMod || (stepMod != ifaceMod && stepMod != implMod) then
            aErrs := aErrs.push s!"NON_INTERFACE_IMPL_IN_REFINES: {stepFn} in {thmName} must be a public constant in {ifaceMod} or {implMod}"
          for mFn in #[wfFn, allowedFn] do
            if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef mFn then
              aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mFn} in {thmName} transitively references Interface/Impl"
          if projFn != ``id && (← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef projFn) then
            aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {projFn} in {thmName} transitively references Interface/Impl"
          if !(← isProvablyInhabitedDataType env 8 wTy) || !(← isProvablyInhabitedDataType env 8 sTy) ||
              !(← isProvablyInhabitedDataType env 8 reqTy) then
            aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited state/request domain in RefinesStep of {thmName}"
          if !(← checkWfNotVacuous env sTy wfFn) then
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {wfFn} in {thmName} is identically false or refutable"
          if !(← checkStepAllowedNonTrivial env modelMods allowedArg allowedFn sTy reqTy outTy) then
            aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {allowedFn} in {thmName} is output/state-insensitive or tautological"
          if aErrs.isEmpty then
            if stepMod == ifaceMod then
              coveredStepOpsRef.modify (·.insert stepFn)
            else if stepMod == implMod then
              coveredImplHelpersRef.modify (·.insert stepFn)
          return aErrs

        let stepFromInfo? : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Array (Expr × Expr × Expr × Expr)) :=
          if ab.isAppOfArity `Core.RefinesStepFrom 16 then
            let args := ab.getAppArgs
            some (args[0]!, args[1]!, args[6]!, args[7]!, args[8]!, args[9]!, args[12]!, args[13]!, args[14]!,
              #[(args[4]!, args[5]!, args[10]!, args[11]!), (args[6]!, args[7]!, args[14]!, args[15]!)])
          else if ab.isAppOfArity `Core.RefinesStepFrom2 21 then
            let args := ab.getAppArgs
            some (args[0]!, args[1]!, args[9]!, args[10]!, args[11]!, args[12]!, args[17]!, args[18]!, args[19]!,
              #[(args[5]!, args[6]!, args[13]!, args[14]!),
                (args[7]!, args[8]!, args[15]!, args[16]!),
                (args[9]!, args[10]!, args[19]!, args[20]!)])
          else none

        if let some (rawSTy, pkgSTy, pkgReqTy, _pkgOutTy, mapSArg, rawWfArg, pkgWfArg, mkApiArg, execPkgArg, stepLegs) := stepFromInfo? then
          if !axs.isEmpty then
            return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} RefinesStepFrom conjunct cannot have binders"]
          let some mapSFn ← checkBareConstArg env {} true mapSArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare mapS argument in {thmName}"]
          let some rawWfFn ← checkBareConstArg env {} false rawWfArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare rawWf argument in {thmName}"]
          let some pkgWfFn ← checkBareConstArg env {} false pkgWfArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare pkgWf argument in {thmName}"]
          let some mkApiFn ← checkBareConstArg env {} false mkApiArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare mkApi argument in {thmName}"]
          let some execPkgFn ← checkBareConstArg env {} false execPkgArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare execPkg argument in {thmName}"]
          if mapSFn != ``id && (isPrivateName mapSFn || !modelMods.contains (moduleOfConst env mapSFn)) then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {mapSFn} in {thmName} must be id or a public Model constant"
          if mapSFn != ``id && (← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef mapSFn) then
            aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mapSFn} in {thmName} transitively references Interface/Impl"
          for mFn in #[rawWfFn, pkgWfFn, execPkgFn] do
            if isPrivateName mFn || !modelMods.contains (moduleOfConst env mFn) then
              aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {mFn} in {thmName} is not a public constant in {pkg}.Model"
            if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef mFn then
              aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mFn} in {thmName} transitively references Interface/Impl"
          let mkApiMod := moduleOfConst env mkApiFn
          if isPrivateName mkApiFn || modelMods.contains mkApiMod || (mkApiMod != ifaceMod && mkApiMod != implMod) then
            aErrs := aErrs.push s!"NON_INTERFACE_IMPL_IN_REFINES: {mkApiFn} in {thmName} must be a public constant in {ifaceMod} or {implMod}"
          for dTy in #[rawSTy, pkgSTy, pkgReqTy] do
            if !(← isProvablyInhabitedDataType env 8 dTy) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited state/request domain in RefinesStepFrom of {thmName}"
          if !(← checkWfNotVacuous env rawSTy rawWfFn) then
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {rawWfFn} in {thmName} is identically false or refutable"
          if !(← checkWfNotVacuous env pkgSTy pkgWfFn) then
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {pkgWfFn} in {thmName} is identically false or refutable"
          for idx in [0 : stepLegs.size] do
            let (legReqTy, legOutTy, legExecArg, legAllowedArg) := stepLegs[idx]!
            let isPkgLeg := idx + 1 == stepLegs.size
            let legSTy := if isPkgLeg then pkgSTy else rawSTy
            let some legExecFn ← checkBareConstArg env {} false legExecArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare exec argument in {thmName}"]
            let some legAllowedFn ← checkBareConstArg env {} false legAllowedArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare allowed argument in {thmName}"]
            for mFn in #[legExecFn, legAllowedFn] do
              if isPrivateName mFn || !modelMods.contains (moduleOfConst env mFn) then
                aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {mFn} in {thmName} is not a public constant in {pkg}.Model"
              if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef mFn then
                aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mFn} in {thmName} transitively references Interface/Impl"
            if !(← isProvablyInhabitedDataType env 8 legReqTy) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited state/request domain in RefinesStepFrom of {thmName}"
            if !(← checkStepAllowedNonTrivial env modelMods legAllowedArg legAllowedFn legSTy legReqTy legOutTy) then
              aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {legAllowedFn} in {thmName} is output/state-insensitive or tautological"
          if aErrs.isEmpty then
            let execFlds := collectUsedStructFieldsTransitive env modelMods {} execPkgFn
            if execFlds.isEmpty then
              aErrs := aErrs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: {execPkgFn} in {thmName} projects zero capability fields"
            else
              coveredCapBuildersRef.modify (·.insert mkApiFn)
              for fld in execFlds do
                coveredExecFieldsRef.modify (·.insert fld)
              for h in (← collectCoveredMkApiImplHelpers env implMod mkApiFn execFlds) do
                coveredImplHelpersRef.modify (·.insert h)
          return aErrs

        return #[s!"INVALID_REFINES_CONJUNCT: unsupported conjunct head {ab.getAppFn} in {thmName}"]
      localErrs := localErrs ++ atomErrs
    return localErrs

  let coveredPureOps ← coveredPureOpsRef.get
  let coveredStepOps ← coveredStepOpsRef.get
  let coveredExecFields ← coveredExecFieldsRef.get
  let coveredImplHelpers ← coveredImplHelpersRef.get
  let coveredCapBuilders ← coveredCapBuildersRef.get

  errs := errs ++ conjErrs
  if errs.isEmpty then
    if let some ifaceIdx := env.header.moduleNames.findIdx? (· == ifaceMod) then
      if let some ifaceData := env.header.moduleData[ifaceIdx]? then
        let skipBundles : Std.HashSet Name :=
          Std.HashSet.emptyWithCapacity 2 |>.insert (Name.str pkg "defaultApi") |>.insert (Name.str pkg "defaultOps")
        let ifaceSingleton : Std.HashSet Name := Std.HashSet.emptyWithCapacity 1 |>.insert ifaceMod
        let mut sawAnyIfaceOp := false
        let mut sawAnyEffectfulOp := false
        for c in ifaceData.constants do
          let .defnInfo dv := c | continue
          if isPrivateName c.name || isCompilerAux c.name || env.isProjectionFn c.name then continue
          if (← Meta.isInstance c.name) || (← isClassInstanceOrAux env c.name c.type) then continue
          if ← isCapabilityBundleConst env knownPkgs pkg c.name c.type then continue
          sawAnyIfaceOp := true
          if ← isEffectfulInterfaceOp env c.type c.name then
            sawAnyEffectfulOp := true
            let opFields := collectUsedStructFieldsTransitive env ifaceSingleton skipBundles c.name
            let coveredByFields := !opFields.isEmpty && opFields.all coveredExecFields.contains
            let usedBody := dv.value.getUsedConstants
            let coveredByHelper := usedBody.any coveredImplHelpers.contains
            let coveredByBuilder := coveredCapBuilders.contains c.name || usedBody.any coveredCapBuilders.contains
            if !coveredStepOps.contains c.name && !coveredByFields && !coveredByHelper && !coveredByBuilder then
              errs := errs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: effectful Interface operation {c.name} is not covered by {thmName}"
          else
            if !coveredPureOps.contains c.name then
              errs := errs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: pure Interface operation {c.name} is missing from {thmName}"
        if sawAnyEffectfulOp && !coveredCapBuilders.isEmpty then
          if let some (.defnInfo defApiDv) := env.find? (Name.str pkg "defaultApi") then
            let defApiUsed := defApiDv.value.getUsedConstants
            let wiredToCap := defApiUsed.any fun u =>
              coveredCapBuilders.contains u ||
                (moduleOfConst env u == ifaceMod &&
                  match env.find? u with
                  | some (.defnInfo udv) => udv.value.getUsedConstants.any coveredCapBuilders.contains
                  | _ => false)
            if !wiredToCap then
              errs := errs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: {Name.str pkg "defaultApi"} is not wired to mkApi in {thmName}"
        if !sawAnyIfaceOp then
          errs := errs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: {ifaceMod} exposes zero public operations"
      else
        errs := errs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: missing module data for {ifaceMod}"
    else
      errs := errs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: {ifaceMod} is not imported"

  return (errs, axCache)

private structure CliConfig where
  libDir : System.FilePath := ".lake/build/lib/lean"
  repoDir : System.FilePath := "."
  logPath? : Option System.FilePath := none
  nonce? : Option String := none
  legacyAllowlist : Std.HashSet Name := {}
  deadBranchFuel : Nat := 4096
  argError? : Option String := none

private def parseCsvAllowlist (csv : String) (init : Std.HashSet Name) : Std.HashSet Name :=
  (csv.splitOn ",").foldl
    (fun s item =>
      let t := item.trimAscii.toString
      if t.isEmpty then s else s.insert t.toName)
    init

private def isExplicitPkgListArg (s : String) : Bool :=
  !s.startsWith "-" && !s.startsWith "." && !s.startsWith "/" &&
    (s.startsWith "LeanSwe" || (s.splitOn ",").length > 1)

private def parseArgs (args : List String) : CliConfig :=
  let defaultLegacy := legacyExemptionAllowlist.foldl (fun s n => s.insert n) {}
  let rec go (cfg : CliConfig) (pos : Nat) : (xs : List String) → CliConfig
    | [] => cfg
    | "--verify-log" :: lp :: rest => go { cfg with logPath? := some ⟨lp⟩ } pos rest
    | ["--verify-log"] => { cfg with argError? := some "MISSING_VERIFY_LOG_VALUE: --verify-log requires a path" }
    | "--nonce" :: nc :: rest => go { cfg with nonce? := some nc } pos rest
    | ["--nonce"] => { cfg with argError? := some "MISSING_NONCE_VALUE: --nonce requires a non-empty argument" }
    | "--dead-branch-fuel" :: nf :: rest =>
      match nf.toNat? with
      | some n => go { cfg with deadBranchFuel := n } pos rest
      | none => { cfg with argError? := some s!"INVALID_DEAD_BRANCH_FUEL: {nf}" }
    | ["--dead-branch-fuel"] => { cfg with argError? := some "MISSING_DEAD_BRANCH_FUEL: --dead-branch-fuel requires a Nat" }
    | "--allow-legacy" :: arg :: tail =>
      if arg.isEmpty then
        go { cfg with legacyAllowlist := {} } pos tail
      else if isExplicitPkgListArg arg then
        go { cfg with legacyAllowlist := parseCsvAllowlist arg cfg.legacyAllowlist } pos tail
      else
        go { cfg with legacyAllowlist := defaultLegacy } pos (arg :: tail)
    | ["--allow-legacy"] =>
      { cfg with legacyAllowlist := defaultLegacy }
    | arg :: rest =>
      if arg.startsWith "--allow-legacy=" then
        let csv := (arg.drop 15).toString
        go { cfg with legacyAllowlist := parseCsvAllowlist csv cfg.legacyAllowlist } pos rest
      else if pos == 0 then
        go { cfg with libDir := ⟨arg⟩ } 1 rest
      else if pos == 1 then
        go { cfg with repoDir := ⟨arg⟩ } 2 rest
      else
        go cfg (pos + 1) rest
  termination_by xs => xs.length
  go {} 0 args

/-- Audit compiled `.olean` artifacts for hardened checkable assumptions, error coverage, and `Core.Refines`. -/
unsafe def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args
  if let some err := cfg.argError? then
    IO.eprintln err
    return 1
  if cfg.nonce? == some "" then
    IO.eprintln "EMPTY_NONCE_FORBIDDEN: --nonce must be non-empty"
    return 1
  let libDir := cfg.libDir
  let repoDir ←
    if cfg.repoDir == System.FilePath.mk "." && !(← (cfg.repoDir / "LeanSwe.lean").pathExists) &&
        (← (libDir / ".." / ".." / ".." / ".." / "LeanSwe.lean").pathExists) then
      IO.FS.realPath (libDir / ".." / ".." / ".." / "..")
    else
      pure cfg.repoDir
  unless ← (libDir / "LeanSwe.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe ({libDir / "LeanSwe.olean"})"
    return 1
  let leanSweDir := repoDir / "LeanSwe"
  unless ← leanSweDir.pathExists do
    IO.eprintln s!"MISSING_SOURCE_DIR: {leanSweDir}"
    return 1
  let hasTestsMainOlean ← (libDir / "Tests" / "Main.olean").pathExists
  Lean.enableInitializersExecution
  initSearchPath (← findSysroot) [libDir]
  let rootImports :=
    if hasTestsMainOlean then #[{ module := `LeanSwe }, { module := `Tests.Main }]
    else #[{ module := `LeanSwe }]
  let env ← importModules rootImports {} (loadExts := true)
  let transImpsOf := buildTransitiveImportFn env

  let mut visited : Std.HashSet Name := {}
  let mut knownPkgs : Array Name := #[]
  for modName in env.header.moduleNames do
    if isProjectModule modName then
      visited := visited.insert modName
      if let .str p "SpecTests" := modName then
        knownPkgs := knownPkgs.push p

  let mut errors : Array String := #[]
  let mut diskRtPkgs : Std.HashSet Name := {}
  for entry in (← System.FilePath.walkDir leanSweDir) do
    if entry.extension == some "lean" then
      let modName := moduleNameUnderLeanSwe leanSweDir entry
      if !visited.contains modName then
        errors := errors.push s!"UNIMPORTED_MODULE: {entry} (module {modName} not imported by LeanSwe)"
      if entry.fileName == some "RuntimeTests.lean" then
        diskRtPkgs := diskRtPkgs.insert (pkgNamespaceOfSpecWith knownPkgs modName)

  let anyHasRt := knownPkgs.any fun p => visited.contains (Name.str p "RuntimeTests") || diskRtPkgs.contains p
  if anyHasRt && !hasTestsMainOlean then
    IO.eprintln s!"MISSING_OLEAN: Tests.Main ({libDir / "Tests" / "Main.olean"})"
    return 1

  let fuzzCoveredPkgs ← match ← parseFuzzCoveredPackages repoDir knownPkgs with
    | .ok s => pure s
    | .error err =>
      errors := errors.push err
      pure ({} : Std.HashSet Name)

  let mut specModules : Array Name := #[]
  let mut formalAssumptions : Array (Name × Name) := #[]
  let mut specAndProofRoots : Array Name := #[]
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if !isProjectOrTestModule m then continue
    let some data := env.header.moduleData[i]? | continue
    for c in data.constants do
      if let .axiomInfo _ := c then
        if !allowedAxioms.contains c.name then
          errors := errors.push s!"CUSTOM_AXIOM_FORBIDDEN: {c.name} in {m}"
      if m == `Tests.Main then
        let used := match c with
          | .defnInfo dv => dv.value.getUsedConstants
          | .opaqueInfo ov => ov.value.getUsedConstants
          | _ => #[]
        if used.any forbiddenTestMainConsts.contains then
          errors := errors.push s!"FORBIDDEN_IO_IN_TEST_MAIN: {c.name} in Tests.Main uses file/process IO"
      if m != `Core.Assumptions then
        let cVal? := match c with
          | .defnInfo dv => some dv.value
          | .opaqueInfo ov => some ov.value
          | .thmInfo tv => some tv.value
          | _ => none
        let valUsed := match cVal? with
          | some v => v.getUsedConstants
          | none => #[]
        let typeUsed := c.type.getUsedConstants
        if typeUsed.any (fun k => k == `Core.logAssumpPass || k == `Core.logErrPass) ||
            valUsed.any (fun k => k == `Core.logAssumpPass || k == `Core.logErrPass) then
          errors := errors.push s!"FORBIDDEN_DIRECT_LOG_CALL: {c.name} in {m}"
        let touchesRunner :=
          typeUsed.any (fun k => k == `Core.runRegisteredAssumptions || k == `Core.runRegisteredErrorTests) ||
          valUsed.any (fun k => k == `Core.runRegisteredAssumptions || k == `Core.runRegisteredErrorTests)
        if touchesRunner then
          let badInType := hasInvalidRunnerCall m c.type
          let badInVal := match cVal? with
            | some v => hasInvalidRunnerCall m v
            | none => false
          if badInType || badInVal then
            errors := errors.push s!"FORBIDDEN_OR_UNBOUND_REGISTERED_RUNNER: {c.name} in {m}"
        if let .defnInfo dv := c then
          if exprHasStringLitMatching (fun s =>
              (s.splitOn "ASSUMP_PASS").length > 1 || (s.splitOn "ERR_PASS").length > 1 ||
              (s.splitOn "ASSUMP_").length > 1 || (s.splitOn "|ERR_").length > 1 ||
              (s.splitOn "LOG_INIT").length > 1 || (s.splitOn "LOG_CLOSE").length > 1) dv.value then
            errors := errors.push s!"LOG_FORGERY_LITERAL: {c.name} in {m} embeds assumption log tags"
      if isProofsModule m then
        if let .thmInfo _ := c then
          specAndProofRoots := specAndProofRoots.push c.name
      if isCompilerAux c.name then continue
      if c.name.getString! == "EmpiricalAssumptions" then
        let pkg := pkgNamespaceOfSpecWith knownPkgs m
        if !cfg.legacyAllowlist.contains pkg then
          errors := errors.push s!"PROSE_EMPIRICAL_ASSUMPTIONS: {c.name} in {m}"
    if m.getString! == "SpecTests" then
      let pkg := pkgNamespaceOfSpecWith knownPkgs m
      if cfg.legacyAllowlist.contains pkg then continue
      specModules := specModules.push m
      for c in data.constants do
        if isCompilerAux c.name || isInductiveElimAux env c.name then continue
        let short := c.name.getString!
        if short.startsWith "empirical_" then
          errors := errors.push s!"RENAMED_OR_EMPIRICAL_ASSUMPTION: {c.name} in {m}"
        if short.startsWith "assume_" then
          formalAssumptions := formalAssumptions.push (m, c.name)
          specAndProofRoots := specAndProofRoots.push c.name
        if short.startsWith "test_" ||
            c.name == Name.str pkg "errorCoverage" ||
            c.name == Name.str pkg "externalAssumptions" then
          specAndProofRoots := specAndProofRoots.push c.name
        if isPrivateName c.name then
          if let .thmInfo _ := c then
            specAndProofRoots := specAndProofRoots.push c.name

  let usedInSpecsOrProofs := collectTransitiveDeps env specAndProofRoots
  let formalAssumpSet : Std.HashSet Name := formalAssumptions.foldl (fun s (_, a) => s.insert a) {}
  let ctx : Core.Context := { fileName := "<CheckAssumptions>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let state : Core.State := { env }
  let ((metaErrs, expectedAssumpNames, expectedErrorTests), _) ← (Meta.MetaM.run' do
    let mut errs : Array String := #[]
    let mut expAssumps : Array String := #[]
    let mut expErrTests : Array (String × String) := #[]
    let mut axCache : AxCache := {}
    let mut dbCache : DeadBranchCache := {}

    for h : i in [0 : env.header.moduleNames.size] do
      let m := env.header.moduleNames[i]
      if !isProjectModule m || isProofsModule m then continue
      let pkg := pkgNamespaceOfSpecWith knownPkgs m
      if cfg.legacyAllowlist.contains pkg then continue
      let some data := env.header.moduleData[i]? | continue
      for c in data.constants do
        if isCompilerAux c.name || isInductiveElimAux env c.name then continue
        if let .inductInfo ind := c then
          if ← hasPropField env ind.name then
            errs := errs.push s!"BARE_PROP_FIELD: {ind.name} in {m}"
        if m.getRoot == `LeanSwe then
          if c matches .defnInfo _ || c matches .opaqueInfo _ then
            if (← whnf c.type).consumeMData.isProp then
              if !c.name.getString!.startsWith "assume_" && !usedInSpecsOrProofs.contains c.name then
                errs := errs.push s!"BARE_PROP_DECLARATION: {c.name} in {m}"
        if m.getString! == "SpecTests" then
          let errCovName := Name.str pkg "errorCoverage"
          let extAssumpName := Name.str pkg "externalAssumptions"
          if c.name != errCovName && c.name != extAssumpName &&
              (c matches .defnInfo _ || c matches .opaqueInfo _) then
            if ← typeCarriesStringProse c.type then
              errs := errs.push s!"PROSE_LIST_ASSUMPTION: {c.name} in {m}"
            if ← hasPropCodomain c.type then
              if !c.name.getString!.startsWith "assume_" && !usedInSpecsOrProofs.contains c.name then
                errs := errs.push s!"BARE_PROP_DECLARATION: {c.name} in {m}"
          if !isPrivateName c.name && !env.isProjectionFn c.name &&
              !(← Meta.isInstance c.name) && !(← isClassInstanceOrAux env c.name c.type) then
            if c matches .defnInfo _ || c matches .opaqueInfo _ then
              let short := c.name.getString!
              if ← isNondetUnitSpecType c.type then
                if !short.startsWith "test_" && !short.startsWith "assume_" then
                  errs := errs.push s!"UNCLASSIFIED_SPECTEST_NONDET: {c.name} in {m}"
              else if !short.startsWith "test_" && !short.startsWith "assume_" &&
                  c.name != errCovName && c.name != extAssumpName &&
                  !usedInSpecsOrProofs.contains c.name then
                errs := errs.push s!"UNREFERENCED_SPECTEST_DECL: {c.name} in {m}"

    let mut assumpCanReach : Std.HashSet Name := {}
    let mut assumpUpperConsumed : Std.HashSet Name := {}
    for h : i in [0 : env.header.moduleNames.size] do
      let m := env.header.moduleNames[i]
      if !isProjectModule m || !isProofsModule m then continue
      let some data := env.header.moduleData[i]? | continue
      for c in data.constants do
        let .thmInfo tv := c | continue
        if isPrivateName c.name || isCompilerAux c.name || env.isProjectionFn c.name then continue
        if formalAssumpSet.isEmpty then continue
        let usedType := tv.type.getUsedConstants
        if !usedType.any formalAssumpSet.contains then continue
        let upperPkg := pkgNamespaceOfSpecWith knownPkgs m
        let upperMods : Array Name := #[Name.str upperPkg "Interface", Name.str upperPkg "Impl", Name.str upperPkg "SpecTests"]
        let (conclNonTriv, conclConsts, conclTouchesUpper) ← forallTelescope tv.type fun _ innerConcl => do
          let ic := innerConcl.consumeMData
          let isTrivEq := ic.isAppOfArity ``Eq 3 && (ic.getArg! 1).consumeMData == (ic.getArg! 2).consumeMData
          let nonTriv := !ic.isConstOf ``True && !isTrivEq
          let mut cSet : Std.HashSet Name := {}
          let mut touchesUpper := false
          for k in ic.getUsedConstants do
            cSet := cSet.insert k
            if upperMods.contains (moduleOfConst env k) && !isPrivateName k && !isCompilerAux k then
              touchesUpper := true
          return (nonTriv, cSet, touchesUpper)
        let consumedHere ←
          if !conclNonTriv || !conclTouchesUpper then
            pure #[]
          else
            lambdaTelescope tv.value fun xs proofBody => do
              let cleanProof ← normalizeProofForConsumeCheck proofBody
              let mut found : Array Name := #[]
              for x in xs do
                let xTy ← inferType x
                if ← isProp xTy then
                  if cleanProof.hasAnyFVar (· == x.fvarId!) then
                    for u in xTy.getUsedConstants do
                      if formalAssumpSet.contains u && !conclConsts.contains u then
                        let aPkg := pkgNamespaceOfSpecWith knownPkgs (moduleOfConst env u)
                        if upperPkg != aPkg then
                          found := found.push u
              return found
        if !consumedHere.isEmpty then
          let (badAx?, axCache') ← checkAxiomsOk axCache c.name
          axCache := axCache'
          if let some badAx := badAx? then
            errs := errs.push s!"UNALLOWED_AXIOM_IN_THEOREM: {c.name} uses [{badAx}]"
          else
            for u in consumedHere do
              assumpUpperConsumed := assumpUpperConsumed.insert u
        if !usedType.any (· == `Core.CanReach) then continue
        let isUncond ← withTransparency .reducible <| forallTelescope tv.type fun xs concl => do
          for x in xs do
            if ← isProp (← inferType x) then return none
          return some (collectConclusionAtoms concl)
        let some atoms := isUncond | continue
        let mut mentionsAssump := false
        for atom in atoms do
          if atom.isAppOfArity `Core.CanReach 1 then
            if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
              if formalAssumpSet.contains fn then
                mentionsAssump := true
        if mentionsAssump then
          let (badAx?, axCache') ← checkAxiomsOk axCache c.name
          axCache := axCache'
          if let some badAx := badAx? then
            errs := errs.push s!"UNALLOWED_AXIOM_IN_THEOREM: {c.name} uses [{badAx}]"
            continue
        for atom in atoms do
          if atom.isAppOfArity `Core.CanReach 1 then
            if let .const fn _ := atom.appArg!.consumeMData.getAppFn.consumeMData then
              if formalAssumpSet.contains fn then
                assumpCanReach := assumpCanReach.insert fn

    for (m, aName) in formalAssumptions do
      let pkgNs := pkgNamespaceOfSpecWith knownPkgs m
      if !isExternalBoundaryPkg env knownPkgs pkgNs then
        errs := errs.push s!"PURE_MODULE_ASSUMPTION_FORBIDDEN: {aName} in pure module {m} (use test_* promises)"
        continue
      let (badAx?, axCache') ← checkAxiomsOk axCache aName
      axCache := axCache'
      if let some badAx := badAx? then
        errs := errs.push s!"UNALLOWED_AXIOM_IN_ASSUMPTION: {aName} uses [{badAx}]"
      let usedAssert ← usesAnyConstActive env (Std.HashSet.emptyWithCapacity 1 |>.insert `Core.NondetTest.assert) aName
      if !usedAssert then
        errs := errs.push s!"COMMENT_ONLY_OR_TRIVIAL_ASSUMPTION: {aName} in {m} does not assert a check"
      else if let some (.defnInfo dv) := env.find? aName then
        let bodyOk ← lambdaTelescope dv.value fun xs body => do
          let mut explicitNonInst : Array FVarId := #[]
          for x in xs do
            let bi ← x.fvarId!.getBinderInfo
            let xTy ← whnf (← inferType x)
            if bi == .default && !xTy.isAppOfArity `Core.NondetTest 1 then
              explicitNonInst := explicitNonInst.push x.fvarId!
          let fvarSet : Std.HashSet FVarId := explicitNonInst.foldl (fun (s : Std.HashSet FVarId) fv => s.insert fv) {}
          if fvarSet.isEmpty then return false
          let (foundAssert, allOk) ← validateAssertsInExpr fvarSet {} body
          return foundAssert && allOk
        if !bodyOk then
          errs := errs.push s!"TRIVIAL_ASSUMPTION_ASSERT: {aName} in {m} has trivial, vacuous, or boundary-independent assert"
      if !assumpCanReach.contains aName then
        errs := errs.push s!"MISSING_ASSUMPTION_CANREACH: {aName} in {m}"
      if !assumpUpperConsumed.contains aName then
        errs := errs.push s!"UNUSED_FORMAL_ASSUMPTION: {aName} in {m} is not consumed as a hypothesis by any upper-layer Proofs theorem"


    let activeCacheRef ← IO.mkRef ({} : ActiveCallCache)
    if hasTestsMainOlean || anyHasRt then
      if env.contains `main then
        let (deadMain, dbCache') ← hasStaticDeadBranchTransitive env cfg.deadBranchFuel dbCache `main
        dbCache := dbCache'
        match deadMain with
        | .clean => pure ()
        | .hasDeadBranch => errs := errs.push "DEAD_CONDITIONAL_IN_RUNNER: main in Tests.Main"
        | .inconclusive reason => errs := errs.push s!"INCONCLUSIVE_DEAD_BRANCH_CHECK: main in Tests.Main ({reason})"
        unless ← usesAnyConstActiveCached env activeCacheRef (Std.HashSet.emptyWithCapacity 1 |>.insert `Core.initAssumpLog) `main do
          errs := errs.push "MISSING_ASSUMP_LOG_INIT: main does not call Core.initAssumpLog"
        unless ← usesAnyConstActiveCached env activeCacheRef (Std.HashSet.emptyWithCapacity 1 |>.insert `Core.closeAssumpLog) `main do
          errs := errs.push "MISSING_ASSUMP_LOG_CLOSE: main does not call Core.closeAssumpLog"
      else
        errs := errs.push "MISSING_MAIN: Tests.Main lacks main"

    for pkg in knownPkgs do
      if cfg.legacyAllowlist.contains pkg then continue
      let rtMod := Name.str pkg "RuntimeTests"
      let hasRt := visited.contains rtMod || diskRtPkgs.contains pkg
      let isRetired := !hasRt
      let inSuites := fuzzCoveredPkgs.contains pkg
      let isExtPkg := isExternalBoundaryPkg env knownPkgs pkg
      let isFloatPkg := usesRuntimeFloat env knownPkgs pkg
      if deferredRefinesModelPackages.contains pkg && env.contains (Name.str (Name.str pkg "Proofs") "refines_model") then
        errs := errs.push s!"STALE_REFINES_DEFERRAL: {pkg} defines Proofs.refines_model; remove from deferredRefinesModelPackages"
      if isRetired && (isExtPkg || isFloatPkg) && !inSuites then
        errs := errs.push s!"MISSING_FUZZ_SUITE: retired external-boundary package {pkg} is absent from Fuzz/suites.json"
      let modelMod := Name.str pkg "Model"
      let hasModel := visited.contains modelMod
      let hasDirectOwnExtern := hasDirectOwnExternInPkg env knownPkgs pkg
      let deferredExternalModel := !isRetired && isExtPkg && !inSuites
      let deferredSplitRefinesModel := !isRetired && !inSuites && deferredRefinesModelPackages.contains pkg
      let needsRefinesModel :=
        !hasDirectOwnExtern && !deferredSplitRefinesModel &&
          (isRetired || inSuites || (hasModel && !deferredExternalModel))
      if isRetired || needsRefinesModel then
        let mut modelMods : Std.HashSet Name := {}
        let modelPfx := modelMod.toString ++ "."
        for mCand in env.header.moduleNames do
          if isProjectModule mCand then
            if mCand == modelMod || mCand.toString.startsWith modelPfx ||
                (pkgNamespaceOfSpecWith knownPkgs mCand == pkg && mCand.getString! == "Model") then
              modelMods := modelMods.insert mCand
        if !hasModel then
          errs := errs.push s!"MISSING_MODEL_MODULE: {modelMod} for {pkg} is not imported by LeanSwe"
        else
          let mut modelDefCount := 0
          for mMod in modelMods do
            if let some mIdx := env.header.moduleNames.findIdx? (· == mMod) then
              if let some mData := env.header.moduleData[mIdx]? then
                for c in mData.constants do
                  if let .defnInfo _ := c then
                    if !isPrivateName c.name && !isCompilerAux c.name && !env.isProjectionFn c.name &&
                        !(← Meta.isInstance c.name) && !(← isClassInstanceOrAux env c.name c.type) then
                      let isGenuineModelFn ← forallTelescopeReducing c.type fun xs ret => do
                        if xs.isEmpty then return false
                        let rc := (← whnf ret).consumeMData
                        return !rc.isSort && !rc.isProp &&
                          !rc.isConstOf ``Unit && !rc.isConstOf ``PUnit && !rc.isConstOf ``True
                      if isGenuineModelFn then
                        modelDefCount := modelDefCount + 1
          if modelDefCount == 0 then
            errs := errs.push s!"EMPTY_OR_STUB_MODEL: {modelMod} for {pkg} defines zero non-trivial public computational functions"
        if needsRefinesModel then
          let (refErrs, nextAx) ← checkRefinesModelTheorem env transImpsOf knownPkgs pkg modelMods axCache
          axCache := nextAx
          errs := errs ++ refErrs

    let throwTargets : Std.HashSet Name :=
      Std.HashSet.emptyWithCapacity 6
        |>.insert `MonadExcept.throw
        |>.insert `MonadExceptOf.throw
        |>.insert `throwThe
        |>.insert `EStateM.throw
        |>.insert `IO.userError

    for specMod in specModules do
      let pkgNs := pkgNamespaceOfSpecWith knownPkgs specMod
      let isExtPkg := isExternalBoundaryPkg env knownPkgs pkgNs
      let rtMod := Name.str pkgNs "RuntimeTests"
      let hasRt := visited.contains rtMod || diskRtPkgs.contains pkgNs
      let mut runAllName := Name.str rtMod "runAll"
      if hasRt then
        if !visited.contains rtMod then
          errs := errs.push s!"MISSING_RUNTIMETESTS_MODULE: {rtMod} for {specMod}"
          continue
        let candidateRunAll := Name.str rtMod "runAll"
        let candidateRunAllOutcome := Name.str rtMod "runAllOutcome"
        let mut candidates : Array Name := #[]
        if env.contains candidateRunAllOutcome then
          candidates := candidates.push candidateRunAllOutcome
        if env.contains candidateRunAll then
          candidates := candidates.push candidateRunAll
        let mut activeEntry? : Option Name := none
        for cand in candidates do
          if ← usesAnyConstActiveCached env activeCacheRef (Std.HashSet.emptyWithCapacity 1 |>.insert cand) `main then
            activeEntry? := some cand
            break
        runAllName := activeEntry?.getD (candidates[0]?.getD candidateRunAll)
        if candidates.isEmpty then
          errs := errs.push s!"MISSING_RUNALL: {rtMod} lacks runAll / runAllOutcome"
        else
          let (deadRunAll, dbCache') ← hasStaticDeadBranchTransitive env cfg.deadBranchFuel dbCache runAllName
          dbCache := dbCache'
          match deadRunAll with
          | .clean => pure ()
          | .hasDeadBranch => errs := errs.push s!"DEAD_CONDITIONAL_IN_RUNNER: {runAllName}"
          | .inconclusive reason => errs := errs.push s!"INCONCLUSIVE_DEAD_BRANCH_CHECK: {runAllName} ({reason})"
          if activeEntry?.isNone then
            errs := errs.push s!"UNREGISTERED_RUNTIMETESTS_IN_MAIN: {runAllName} not actively invoked from main"

      let extAssumpConst := Name.str pkgNs "externalAssumptions"
      let regAssumpConst := Name.str rtMod "registeredAssumptions"
      if !isExtPkg then
        if env.contains extAssumpConst then
          errs := errs.push s!"PURE_MODULE_ASSUMPTION_FORBIDDEN: {extAssumpConst} in pure module {specMod}"
        if hasRt && env.contains regAssumpConst then
          errs := errs.push s!"PURE_MODULE_ASSUMPTION_FORBIDDEN: {regAssumpConst} in pure module {rtMod}"
      else if hasRt || env.contains extAssumpConst then
        let mut regAssumpMap : Std.HashMap String Name := {}
        if hasRt then
          if let some (.defnInfo dv) := env.find? regAssumpConst then
            unless ← usesAnyConstActiveCached env activeCacheRef (Std.HashSet.emptyWithCapacity 1 |>.insert regAssumpConst) runAllName do
              errs := errs.push s!"REGISTERED_ASSUMPTIONS_NOT_RUN: {runAllName} does not actively execute {regAssumpConst}"
            if let some elems ← extractArrayElems dv.value then
              for elem in elems do
                if let some (specName, runFn) ← parseRegisteredAssumption elem then
                  let runClean := runFn.consumeMData
                  if let .const fnName _ := runClean then
                    if moduleOfConst env fnName != rtMod || fnName.getString! != specName.toName.getString! then
                      errs := errs.push s!"RUNTIME_ASSUMPTION_NAME_MISMATCH: {specName} bound to {fnName}"
                    else
                      let (deadFn, dbCache') ← hasStaticDeadBranchTransitive env cfg.deadBranchFuel dbCache fnName
                      dbCache := dbCache'
                      match deadFn with
                      | .clean => pure ()
                      | .hasDeadBranch => errs := errs.push s!"DEAD_CONDITIONAL_IN_TEST: {fnName}"
                      | .inconclusive reason => errs := errs.push s!"INCONCLUSIVE_DEAD_BRANCH_CHECK: {fnName} ({reason})"
                      unless ← usesThrowTargetsActive env activeCacheRef throwTargets fnName do
                        errs := errs.push s!"TRIVIAL_RUNTIME_ASSUMPTION: {fnName} has no active failure/throw path"
                      unless ← usesPackageImplConstActiveCached env activeCacheRef pkgNs rtMod fnName do
                        errs := errs.push s!"MISSING_PACKAGE_REF_IN_TEST: {fnName} does not actively invoke {pkgNs} Interface/Impl"
                      regAssumpMap := regAssumpMap.insert specName fnName
                  else
                    errs := errs.push s!"RUNTIME_ASSUMPTION_NOT_NAMED_CONST: {specName} in {regAssumpConst}"
                else
                  errs := errs.push s!"MALFORMED_REGISTERED_ASSUMPTION: in {regAssumpConst}"
            else
              errs := errs.push s!"UNPARSEABLE_REGISTERED_ASSUMPTIONS: {regAssumpConst}"
          else
            errs := errs.push s!"MISSING_REGISTERED_ASSUMPTIONS: {regAssumpConst}"

        let mut listedFormalPreds : Std.HashSet Name := {}
        if let some (.defnInfo extDv) := env.find? extAssumpConst then
          if let some obElems ← extractListElems extDv.value then
            let ifaceMod := Name.str pkgNs "Interface"
            let implMod := Name.str pkgNs "Impl"
            for obElem in obElems do
              let some (obName, subjStr, fp?) ← parseAssumptionObligation obElem
                | errs := errs.push s!"MALFORMED_ASSUMPTION_OBLIGATION: in {extAssumpConst}"; continue
              let obConst := obName.toName
              if obConst.getPrefix != pkgNs || !obConst.getString!.startsWith "assume_" then
                errs := errs.push s!"MALFORMED_ASSUMPTION_NAME: {obName} in {extAssumpConst}"
              let subjName := subjStr.toName
              let subjMod := moduleOfConst env subjName
              if (subjMod != ifaceMod && subjMod != implMod) || isPrivateName subjName || isCompilerAux subjName then
                errs := errs.push s!"INVALID_ASSUMPTION_SUBJECT: {subjStr} in {extAssumpConst}"
              match fp? with
              | none =>
                if env.contains obConst then
                  errs := errs.push s!"UNLINKED_FORMAL_ASSUMPTION_PRED: {obName} exists in {specMod} with formalPred? = none"
              | some fpStr =>
                if fpStr != obName || !formalAssumpSet.contains obConst then
                  errs := errs.push s!"MISSING_FORMAL_ASSUMPTION_PRED: {fpStr} for {obName} in {extAssumpConst}"
                else
                  listedFormalPreds := listedFormalPreds.insert obConst
              if hasRt then
                if !regAssumpMap.contains obName then
                  errs := errs.push s!"MISSING_ASSUMPTION_TEST: {obName} not registered in {regAssumpConst}"
                expAssumps := expAssumps.push obName
          else
            errs := errs.push s!"UNPARSEABLE_EXTERNAL_ASSUMPTIONS: {extAssumpConst}"
        else if hasRt then
          errs := errs.push s!"MISSING_EXTERNAL_ASSUMPTIONS: {extAssumpConst}"

        for (m, aName) in formalAssumptions do
          if m == specMod && !listedFormalPreds.contains aName then
            errs := errs.push s!"UNLISTED_FORMAL_ASSUMPTION: {aName} missing from {extAssumpConst}"
      else
        for (m, aName) in formalAssumptions do
          if m == specMod then
            errs := errs.push s!"UNLISTED_FORMAL_ASSUMPTION: {aName} missing from {extAssumpConst}"

      let ifaceMod := Name.str pkgNs "Interface"
      let implMod := Name.str pkgNs "Impl"
      let mut fallibleReqs : Array Name := #[]
      let mut hasAnyFallibleIfaceSurface := false
      for targetMod in [ifaceMod, implMod] do
        if let some idx := env.header.moduleNames.findIdx? (· == targetMod) then
          if let some modData := env.header.moduleData[idx]? then
            for c in modData.constants do
              if isPrivateName c.name || isCompilerAux c.name then continue
              if targetMod == implMod && c.name.getPrefix != pkgNs then continue
              if targetMod == ifaceMod then
                if ← hasFallibleSurface env {} c.type then
                  hasAnyFallibleIfaceSurface := true
              if ← isFallibleCodomain c.type then
                fallibleReqs := fallibleReqs.push c.name

      let regErrConst := Name.str rtMod "registeredErrorTests"
      let errCovConst := Name.str pkgNs "errorCoverage"
      if !isExtPkg && fallibleReqs.isEmpty && !hasAnyFallibleIfaceSurface then
        if hasRt then
          if let some (.defnInfo dv) := env.find? regErrConst then
            match ← extractArrayElems dv.value with
            | some elems =>
              if !elems.isEmpty then
                errs := errs.push s!"PURE_TOTAL_ERROR_TESTS_FORBIDDEN: {regErrConst} must be empty when {pkgNs} has no fallible codomains"
            | none =>
              errs := errs.push s!"UNPARSEABLE_REGISTERED_ERROR_TESTS: {regErrConst}"
        if let some (.defnInfo dv) := env.find? errCovConst then
          match ← extractListElems dv.value with
          | some elems =>
            if !elems.isEmpty then
              errs := errs.push s!"PURE_TOTAL_ERROR_COVERAGE_FORBIDDEN: {errCovConst} must be empty when {pkgNs} has no fallible codomains"
          | none =>
            errs := errs.push s!"UNPARSEABLE_ERROR_COVERAGE: {errCovConst}"
      else
        let mut regErrMap : Std.HashMap String (Name × Name) := {}
        if hasRt then
          if let some (.defnInfo dv) := env.find? regErrConst then
            unless ← usesAnyConstActiveCached env activeCacheRef (Std.HashSet.emptyWithCapacity 1 |>.insert regErrConst) runAllName do
              errs := errs.push s!"REGISTERED_ERROR_TESTS_NOT_RUN: {runAllName} does not actively execute {regErrConst}"
            if let some elems ← extractArrayElems dv.value then
              for elem in elems do
                if let some (tName, modeCtor, runFn) ← parseRegisteredErrorTest elem then
                  let runClean := runFn.consumeMData
                  if let .const fnName _ := runClean then
                    if moduleOfConst env fnName != rtMod || fnName.toString != tName then
                      errs := errs.push s!"ERROR_TEST_NAME_MISMATCH: {tName} bound to {fnName}"
                    else
                      let (deadErrFn, dbCache') ← hasStaticDeadBranchTransitive env cfg.deadBranchFuel dbCache fnName
                      dbCache := dbCache'
                      match deadErrFn with
                      | .clean => pure ()
                      | .hasDeadBranch => errs := errs.push s!"DEAD_CONDITIONAL_IN_TEST: {fnName}"
                      | .inconclusive reason => errs := errs.push s!"INCONCLUSIVE_DEAD_BRANCH_CHECK: {fnName} ({reason})"
                      unless ← usesThrowTargetsActive env activeCacheRef throwTargets fnName do
                        errs := errs.push s!"TRIVIAL_ERROR_TEST: {fnName} has no active failure/throw path"
                      unless ← usesPackageImplConstActiveCached env activeCacheRef pkgNs rtMod fnName do
                        errs := errs.push s!"MISSING_PACKAGE_REF_IN_TEST: {fnName} does not actively invoke {pkgNs} Interface/Impl"
                      regErrMap := regErrMap.insert tName (modeCtor, fnName)
                  else
                    errs := errs.push s!"ERROR_TEST_NOT_NAMED_CONST: {tName} in {regErrConst}"
                else
                  errs := errs.push s!"MALFORMED_REGISTERED_ERROR_TEST: in {regErrConst}"
            else
              errs := errs.push s!"UNPARSEABLE_REGISTERED_ERROR_TESTS: {regErrConst}"
          else
            errs := errs.push s!"MISSING_REGISTERED_ERROR_TESTS: {regErrConst}"

        if let some (.defnInfo dv) := env.find? errCovConst then
          let enumName? ← do
            let ty ← whnf dv.type
            if ty.isAppOfArity ``List 1 then
              let ob ← whnf ty.appArg!
              if ob.isAppOfArity `Core.ErrorObligation 1 then
                let eTy ← whnf ob.appArg!
                pure (if let .const en _ := eTy.getAppFn then some en else none)
              else pure none
            else pure none
          let some enumName := enumName?
            | errs := errs.push s!"MALFORMED_ERROR_COVERAGE_TYPE: {errCovConst}"; continue
          let some (.inductInfo ind) := env.find? enumName
            | errs := errs.push s!"NON_INDUCTIVE_ERROR_ENUM: {enumName} in {errCovConst}"; continue
          let expectedCtors := ind.ctors
          let some elems ← extractListElems dv.value
            | errs := errs.push s!"UNPARSEABLE_ERROR_COVERAGE: {errCovConst}"; continue
          let mut byReq : Std.HashMap String (Std.HashSet Name) := {}
          for elem in elems do
            let some (req, kindCtor, tag, targetStr) ← parseErrorObligation elem
              | errs := errs.push s!"MALFORMED_ERROR_OBLIGATION: in {errCovConst}"; continue
            byReq := byReq.insert req ((byReq.getD req {}).insert kindCtor)
            if tag == `provedImpossible then
              let thmName := targetStr.toName
              let some (.thmInfo tv) := env.find? thmName
                | errs := errs.push s!"MISSING_IMPOSSIBLE_THEOREM: {thmName} for ({req}, {kindCtor})"; continue
              let thmMod := moduleOfConst env thmName
              if thmMod.getString! == "SpecTests" || thmMod.getString! == "RuntimeTests" then
                errs := errs.push s!"INVALID_THEOREM_LOCATION: {thmName} must be outside SpecTests/RuntimeTests"
              let (badAx?, axCache') ← checkAxiomsOk axCache thmName
              axCache := axCache'
              if let some badAx := badAx? then
                errs := errs.push s!"UNALLOWED_AXIOM_IN_THEOREM: {thmName} uses [{badAx}]"
              if let some shapeErr ← checkProvedImpossibleTheorem env tv req.toName kindCtor enumName then
                errs := errs.push s!"{shapeErr} ({thmName})"
            else if hasRt || !fuzzCoveredPkgs.contains pkgNs then
              let some (regMode, _) := regErrMap.get? targetStr
                | errs := errs.push s!"MISSING_ERROR_TEST: {targetStr} for ({req}, {kindCtor}) not in {regErrConst}"; continue
              if regMode != tag then
                errs := errs.push s!"MODE_MISMATCH_ERROR_TEST: {targetStr} declared {tag} vs registered {regMode}"
              expErrTests := expErrTests.push (targetStr, tag.toString)

          for reqName in fallibleReqs do
            unless byReq.contains reqName.toString do
              errs := errs.push s!"MISSING_REQUEST_IN_ERROR_COVERAGE: {reqName} omitted from {errCovConst}"

          if byReq.isEmpty then
            errs := errs.push s!"EMPTY_ERROR_COVERAGE: {errCovConst}"
          for (req, covered) in byReq.toList do
            for ctor in expectedCtors do
              if !covered.contains ctor then
                errs := errs.push s!"UNCOVERED_ERROR_KIND: ({req}, {ctor}) missing from {errCovConst}"
        else
          errs := errs.push s!"MISSING_ERROR_COVERAGE: {errCovConst}"

    return (errs, expAssumps, expErrTests)
  ).toIO ctx state

  errors := errors ++ metaErrs
  let mut verifiedLogCount := 0
  if let some logPath := cfg.logPath? then
    unless ← logPath.pathExists do
      errors := errors.push s!"MISSING_RUNTIME_LOG: {logPath}"
    if ← logPath.pathExists then
      let (assumpPass, errPass, badLines, sawInit, sawClose) ← parseLogFile logPath cfg.nonce?
      if badLines > 0 then
        errors := errors.push s!"INVALID_OR_UNAUTHENTICATED_LOG_LINES: {badLines} lines failed nonce/format check"
      if !sawInit || !sawClose then
        errors := errors.push "INCOMPLETE_OR_UNINITIALIZED_LOG: missing LOG_INIT or LOG_CLOSE"
      for aName in expectedAssumpNames do
        if !assumpPass.contains aName then
          errors := errors.push s!"ASSUMPTION_NOT_RUN_AT_RUNTIME: {aName}"
        else
          verifiedLogCount := verifiedLogCount + 1
      for (tName, modeStr) in expectedErrorTests do
        if !errPass.contains (tName, modeStr) then
          errors := errors.push s!"ERROR_TEST_NOT_RUN_AT_RUNTIME: {tName} ({modeStr})"
        else
          verifiedLogCount := verifiedLogCount + 1

  IO.println s!"ASSUMPTION_CHECK: spec_modules={specModules.size} assumptions={expectedAssumpNames.size} formal_assumptions={formalAssumptions.size} error_tests={expectedErrorTests.size} log_verified={verifiedLogCount} errors={errors.size}"
  if errors.isEmpty then
    return 0
  else
    for err in errors do
      IO.eprintln err
    return 1
