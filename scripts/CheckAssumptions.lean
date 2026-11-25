import Lean

/-!
Hardened checkable-assumptions, error-coverage, and `Core.Obeys` / `Core.Refines` model-refinement
gate audit for `lean-swe` compiled `.olean` artifacts.

Enforces:
1. Complete module & axiom hygiene:
   - Every `.lean` file under `LeanSwe/` must be transitively imported by `LeanSwe`.
   - Zero custom `axiom` declarations anywhere in `Core`, `LeanSwe`, or `Tests.Main`.
   - Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) on all `assume_*`, `CanReach`,
     upper-layer consumer theorems, `.provedImpossible` theorems, and `obeys_model` / `refines_model` theorems.
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
   - Formal `assume_*` predicates in `SpecTests` or `Model.Assumptions` are allowed only when `formalPred? = some name`,
     non-trivial over the boundary parameter (`isMeaningfulBoundaryProp`), satisfiable via `Core.CanReach`,
     and consumed as a used `Prop` hypothesis (after zeta and beta reduction) in an upper-layer `Proofs` theorem.
4. Runtime linking, active execution, non-noop checks, and nonce-log anti-forgery across `Tests.Main` and `RuntimeTests`,
   with clean `RuntimeTests` retirement support: impure external-boundary or runtime-`Float` packages require `<pkgNs>.Model`
   and `harness/Fuzz/suites.json` coverage upon retirement, while pure/composed Lean packages may retire `RuntimeTests` without
   `<pkgNs>.Model` (relying on `SpecTests` + `Proofs`), preserving unconditional `errorCoverage`, `externalAssumptions`
   subject/predicate, and axiom checks.
5. Error coverage completeness & canonical `.provedImpossible` shape (`Core.NeverErrorKind{IO,BaseIO,Pure}`).
6. `Core.Obeys` / `Core.Refines` model-refinement completeness: every non-`@[extern]`/non-CLI package that provides
   `<pkgNs>.Model` (mandatory for impure boundaries, optional for pure/composed packages; `deferredRefinesModelPackages`
   is currently empty, as no deferred packages remain) must prove `<pkgNs>.Proofs.obeys_model`
   or legacy `<pkgNs>.Proofs.refines_model` (never both) via `ObeysPure`, `ObeysPure2`, `ObeysPure3`, `ObeysPure4`,
   `ObeysPureEq`, `ObeysPureEq2`, `ObeysPureEq3`, `ObeysPureEq4`, `ObeysPureEqUpToErrMsg`, `ObeysPureEqUpToErrMsg2`,
   `ObeysPureEqUpToErrMsg3`, `ObeysPureEqUpToErrMsg4`, `ObeysInverseRender`, `ObeysStep`, `ObeysStepId`,
   `ObeysStepFrom`, `ObeysStepFromFinally`, or `ObeysStepFrom2` (or legacy `RefinesPure{,2,3,4}`,
   `RefinesPureEq{,2,3,4}`, `RefinesStep`, `RefinesStepId`, `RefinesStepFrom`, `RefinesStepFromFinally`,
   `RefinesStepFrom2` aliases) with bare-constant pinning and non-trivial `allowed` relations across the full public
   `<pkgNs>.Interface` surface.
7. Supports `--verify-log <path> [--nonce <token>]`, `--allow-legacy [<Csv>]`, and `--print-sig <Pkg>` (emits a
   starting template with explicit placeholders for `<Pkg>.Proofs.obeys_model`).
-/

open Lean Meta

private def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4 |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

private def legacyExemptionAllowlist : Array Name := #[]

/-- Packages with temporarily deferred `<pkgNs>.Proofs.obeys_model` / `refines_model` obligations; currently empty (no deferred packages remain). -/
private def deferredRefinesModelPackages : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity

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

private def isInModuleSubtree (m root : Name) : Bool :=
  let rComps := root.components
  !rComps.isEmpty && m.components.take rComps.length == rComps

private def isSpecOrRuntimeOrProofsModule (m : Name) : Bool :=
  isProofsModule m || m.components.contains `SpecTests || m.components.contains `RuntimeTests

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

private partial def evalClosedPropExpr? (prop : Expr) : MetaM (Option Bool) := do
  let pw := (← withTransparency .all (whnf prop)).consumeMData
  if pw.isConstOf ``Bool.true || pw.isConstOf ``True then return some true
  if pw.isConstOf ``Bool.false || pw.isConstOf ``False then return some false
  if pw.isAppOfArity ``Not 1 then
    return (← evalClosedPropExpr? pw.appArg!).map (!·)
  if pw.isAppOfArity ``Eq 3 then
    let lhs := (← withTransparency .all (Meta.reduce (pw.getArg! 1))).consumeMData
    let rhs := (← withTransparency .all (Meta.reduce (pw.getArg! 2))).consumeMData
    if (lhs.isConstOf ``Bool.true || lhs.isConstOf ``Bool.false) &&
        (rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false) then
      return some (lhs == rhs)
  return none

private def evalClosedDecidable? (prop decInst : Expr) : MetaM (Option Bool) := do
  let p := prop.consumeMData
  if p.isConstOf ``Bool.true || p.isConstOf ``True then return some true
  if p.isConstOf ``Bool.false || p.isConstOf ``False then return some false
  let decBool := (← withTransparency .all (whnf (mkApp2 (mkConst ``decide) prop decInst))).consumeMData
  if decBool.isConstOf ``Bool.true then return some true
  if decBool.isConstOf ``Bool.false then return some false
  let d ← withTransparency .all (Meta.reduce decInst (explicitOnly := false) (skipTypes := true) (skipProofs := true))
  let df := d.consumeMData.getAppFn.consumeMData
  if df.isConstOf ``Decidable.isTrue then return some true
  if df.isConstOf ``Decidable.isFalse then return some false
  evalClosedPropExpr? p

private def exprIsClosedModulo (closedLets : Std.HashSet FVarId) (e : Expr) : Bool :=
  !e.hasLooseBVars && !e.hasAnyFVar (fun fv => !closedLets.contains fv)

private def exprTouchesPkgImpl (env : Environment) (implLets : Std.HashSet FVarId) (e : Expr) : Bool :=
  exprUsesPkgImpl env e || e.hasAnyFVar (fun fv => implLets.contains fv)

private partial def classifyBranchNode?
    (env : Environment)
    (closedLets implLets : Std.HashSet FVarId)
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
    if exprIsClosedModulo closedLets prop && exprIsClosedModulo closedLets dec &&
        !exprTouchesPkgImpl env implLets prop && !exprTouchesPkgImpl env implLets dec then
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
    if exprIsClosedModulo closedLets prop && exprIsClosedModulo closedLets dec &&
        !exprTouchesPkgImpl env implLets prop && !exprTouchesPkgImpl env implLets dec then
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
    if exprIsClosedModulo closedLets b && !exprTouchesPkgImpl env implLets b then
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
              if exprIsClosedModulo closedLets major && !exprTouchesPkgImpl env implLets major then
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

private inductive BoundedBool where
  | isTrue
  | isFalse
  | inconclusive (reason : String)

private def runBoundedMeta {α : Type}
    (act : MetaM α)
    (maxHeartbeats : Nat := 500000)
    (maxRecDepth : Nat := 2048) : MetaM (Except String α) :=
  Lean.tryCatchRuntimeEx
    (try
      Core.withCurrHeartbeats <|
        withTheReader Core.Context
          (fun c => { c with maxHeartbeats := maxHeartbeats, maxRecDepth := min c.maxRecDepth maxRecDepth })
          (.ok <$> act)
    catch ex =>
      return .error (← ex.toMessageData.toString))
    (fun ex =>
      return .error (← ex.toMessageData.toString))

private inductive DeadBranchResult where
  | clean
  | hasDeadBranch
  | inconclusive (reason : String)

private partial def hasStaticDeadBranchExprAux
    (env : Environment)
    (bestFuelRef : IO.Ref (Std.HashMap Expr Nat))
    (closedLets implLets : Std.HashSet FVarId)
    (fuel : Nat)
    (e : Expr) : MetaM DeadBranchResult := do
  if fuel == 0 then return .inconclusive "AST depth budget exhausted"
  let cur := e.consumeMData
  if (← bestFuelRef.get).getD cur 0 >= fuel then return .clean
  bestFuelRef.modify (·.insert cur fuel)
  if cur.isLambda then
    return ← lambdaTelescope cur fun _ body =>
      hasStaticDeadBranchExprAux env bestFuelRef closedLets implLets (fuel - 1) body
  if let some (isStatic, subs) ← classifyBranchNode? env closedLets implLets cur then
    if isStatic then return .hasDeadBranch
    for s in subs do
      match ← hasStaticDeadBranchExprAux env bestFuelRef closedLets implLets (fuel - 1) s with
      | .clean => pure ()
      | bad => return bad
    return .clean
  match cur with
  | .app f a =>
    match ← hasStaticDeadBranchExprAux env bestFuelRef closedLets implLets (fuel - 1) f with
    | .clean => hasStaticDeadBranchExprAux env bestFuelRef closedLets implLets (fuel - 1) a
    | bad => return bad
  | .letE n t v b _ =>
    match ← hasStaticDeadBranchExprAux env bestFuelRef closedLets implLets (fuel - 1) v with
    | .clean =>
      if !b.hasLooseBVar 0 then
        hasStaticDeadBranchExprAux env bestFuelRef closedLets implLets (fuel - 1) (b.lowerLooseBVars 1 1)
      else
        let vClosed := exprIsClosedModulo closedLets v
        let vTouchesImpl := exprTouchesPkgImpl env implLets v
        withLetDecl n t v fun x =>
          let closedLets' := if vClosed then closedLets.insert x.fvarId! else closedLets
          let implLets' := if vTouchesImpl then implLets.insert x.fvarId! else implLets
          hasStaticDeadBranchExprAux env bestFuelRef closedLets' implLets' (fuel - 1) (b.instantiate1 x)
    | bad => return bad
  | .proj _ _ s => hasStaticDeadBranchExprAux env bestFuelRef closedLets implLets (fuel - 1) s
  | _ => return .clean

private def hasStaticDeadBranchExpr (env : Environment) (fuel : Nat) (e : Expr) : MetaM DeadBranchResult :=
  Lean.tryCatchRuntimeEx
    (try
      Core.withCurrHeartbeats <|
        withTheReader Core.Context
          (fun c => { c with maxHeartbeats := 5000000, maxRecDepth := max c.maxRecDepth 4096 }) do
          let bestFuelRef ← IO.mkRef (Std.HashMap.emptyWithCapacity (α := Expr) (β := Nat) 128)
          hasStaticDeadBranchExprAux env bestFuelRef {} {} fuel e
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

private inductive LetBindingInfo where
  | opaque
  | letVal (pureArg? : Option Expr) (usesRtHelper : Bool)
  deriving Inhabited

private def lookupLetInfo (stack : Array LetBindingInfo) (bvarIdx : Nat) : LetBindingInfo :=
  if h : bvarIdx < stack.size then stack[stack.size - 1 - bvarIdx] else .opaque

private partial def exprUsesRtHelperWithStack
    (env : Environment) (rtMod : Name) (stack : Array LetBindingInfo) (e : Expr) : Bool :=
  let rec go (depth : Nat) (cur : Expr) : Bool :=
    match cur with
    | .const c _ => isInModuleSubtree (moduleOfConst env c) rtMod
    | .bvar k =>
      if k < depth then false
      else
        match lookupLetInfo stack (k - depth) with
        | .letVal _ usesRt => usesRt
        | .opaque => false
    | .app f a => go depth f || go depth a
    | .lam _ t b _ | .forallE _ t b _ => go depth t || go (depth + 1) b
    | .letE _ t v b _ => go depth t || go depth v || go (depth + 1) b
    | .mdata _ b | .proj _ _ b => go depth b
    | _ => false
  go 0 e

private def pureArgOfAct (stack : Array LetBindingInfo) (actClean : Expr) : Option Expr :=
  if actClean.isAppOfArity ``Pure.pure 4 || actClean.isAppOfArity ``pure 4 then
    some actClean.appArg!
  else
    match actClean with
    | .bvar k =>
      match lookupLetInfo stack k with
      | .letVal (some a) _ => some (a.liftLooseBVars 0 (k + 1))
      | _ => none
    | _ => none

private partial def stripInertBindingsAux
    (env : Environment) (rtMod : Name) (stack : Array LetBindingInfo) (e : Expr) : Expr :=
  let cur := e.consumeMData
  if cur.getAppFn.consumeMData.isLambda then
    let red := cur.headBeta
    if red != cur then stripInertBindingsAux env rtMod stack red else cur
  else if cur.isAppOfArity ``Bind.bind 6 || cur.isAppOfArity ``bind 6 then
    let args := cur.getAppArgs
    let act := stripInertBindingsAux env rtMod stack args[4]!
    let actClean := act.consumeMData
    if let some pv := pureArgOfAct stack actClean then
      match args[5]!.consumeMData with
      | .lam n t rawBody _ =>
        if !rawBody.hasLooseBVar 0 then
          stripInertBindingsAux env rtMod stack (rawBody.lowerLooseBVars 1 1)
        else
          let pvInfo := LetBindingInfo.letVal
            (pureArgOfAct stack pv.consumeMData)
            (exprUsesRtHelperWithStack env rtMod stack pv)
          let b' := stripInertBindingsAux env rtMod (stack.push pvInfo) rawBody
          if !b'.hasLooseBVar 0 then
            b'.lowerLooseBVars 1 1
          else
            .letE n t pv b' false
      | other =>
        stripInertBindingsAux env rtMod stack (mkApp other pv).headBeta
    else
      let cont := match args[5]!.consumeMData with
        | .lam n t b bi => Expr.lam n t (stripInertBindingsAux env rtMod (stack.push .opaque) b) bi
        | other => stripInertBindingsAux env rtMod stack other
      if let .lam _ binderTy body _ := cont.consumeMData then
        let bt := binderTy.consumeMData
        let isUnitBinder := bt.isConstOf ``Unit || bt.isConstOf ``PUnit
        let usesRtHelper := exprUsesRtHelperWithStack env rtMod stack actClean
        if !body.hasLooseBVar 0 && !isUnitBinder && !usesRtHelper then
          body.lowerLooseBVars 1 1
        else
          mkAppN cur.getAppFn (args.set! 4 act |>.set! 5 cont)
      else
        mkAppN cur.getAppFn (args.set! 4 act |>.set! 5 cont)
  else
    match cur with
    | .letE n t v b nonDep =>
      if !b.hasLooseBVar 0 then
        stripInertBindingsAux env rtMod stack (b.lowerLooseBVars 1 1)
      else
        let v' := stripInertBindingsAux env rtMod stack v
        let vInfo := LetBindingInfo.letVal
          (pureArgOfAct stack v'.consumeMData)
          (exprUsesRtHelperWithStack env rtMod stack v')
        let b' := stripInertBindingsAux env rtMod (stack.push vInfo) b
        if !b'.hasLooseBVar 0 then
          b'.lowerLooseBVars 1 1
        else
          .letE n t v' b' nonDep
    | .lam n t b bi => .lam n t (stripInertBindingsAux env rtMod (stack.push .opaque) b) bi
    | .app f a => .app (stripInertBindingsAux env rtMod stack f) (stripInertBindingsAux env rtMod stack a)
    | .proj tn idx s => .proj tn idx (stripInertBindingsAux env rtMod stack s)
    | _ => cur

private def stripInertBindings (env : Environment) (rtMod : Name) (e : Expr) : Expr :=
  stripInertBindingsAux env rtMod #[] e

private structure ActiveCallCache where
  directPlain : Std.HashMap Name (Array Name) := {}
  directStripped : Std.HashMap (Name × Name) (Array Name) := {}
  reachesThrow : Std.HashMap Name Bool := {}
  scanErrors : Std.HashMap Name String := {}

private partial def exprActiveDirectConsts
    (env : Environment)
    (e : Expr) : MetaM (Except String (Array Name)) :=
  runBoundedMeta (maxHeartbeats := 5000000) (maxRecDepth := 4096) do
    let bestFuelRef ← IO.mkRef (Std.HashMap.emptyWithCapacity (α := Expr) (β := Nat) 128)
    let visitedLetsRef ← IO.mkRef (Std.HashSet.emptyWithCapacity (α := FVarId) 32)
    let outSetRef ← IO.mkRef (Std.HashSet.emptyWithCapacity (α := Name) 32)
    let rec collect (closedLets implLets : Std.HashSet FVarId)
        (letVals : Std.HashMap FVarId Expr) (fuel : Nat) (raw : Expr) : MetaM Unit := do
      if fuel == 0 then
        throwError "AST depth budget exhausted in active-const scan"
      let cur := raw.consumeMData
      if (← bestFuelRef.get).getD cur 0 >= fuel then return
      bestFuelRef.modify (·.insert cur fuel)
      if cur.isLambda then
        lambdaTelescope cur fun _ body =>
          collect closedLets implLets letVals (fuel - 1) body
        return
      if let some (_, subs) ← classifyBranchNode? env closedLets implLets cur then
        for s in subs do
          collect closedLets implLets letVals (fuel - 1) s
        return
      match cur with
      | .const c _ => outSetRef.modify (·.insert c)
      | .fvar fv =>
        if let some v := letVals.get? fv then
          if !(← visitedLetsRef.get).contains fv then
            visitedLetsRef.modify (·.insert fv)
            collect closedLets implLets letVals (fuel - 1) v
      | .app f a =>
        collect closedLets implLets letVals (fuel - 1) f
        collect closedLets implLets letVals (fuel - 1) a
      | .letE n t v b _ =>
        if !b.hasLooseBVar 0 then
          collect closedLets implLets letVals (fuel - 1) (b.lowerLooseBVars 1 1)
        else
          let vClosed := exprIsClosedModulo closedLets v
          let vTouchesImpl := exprTouchesPkgImpl env implLets v
          withLetDecl n t v fun x =>
            let closedLets' := if vClosed then closedLets.insert x.fvarId! else closedLets
            let implLets' := if vTouchesImpl then implLets.insert x.fvarId! else implLets
            let letVals' := letVals.insert x.fvarId! v
            collect closedLets' implLets' letVals' (fuel - 1) (b.instantiate1 x)
      | .proj _ _ s => collect closedLets implLets letVals (fuel - 1) s
      | _ => pure ()
    collect {} {} {} 4096 e
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
    let used ← match ← exprActiveDirectConsts env rawBody with
      | .ok arr => pure arr
      | .error reason =>
        cacheRef.modify fun c =>
          { c with scanErrors := if c.scanErrors.contains cur then c.scanErrors else c.scanErrors.insert cur reason }
        pure #[]
    cacheRef.modify fun c => { c with directPlain := c.directPlain.insert cur used }
    return used
  | some rtMod =>
    let keyMod :=
      if rawBody.getUsedConstants.any (fun k => isInModuleSubtree (moduleOfConst env k) rtMod) then rtMod
      else Name.anonymous
    let key := (cur, keyMod)
    if let some hit := cache.directStripped.get? key then
      return hit
    let stripped := stripInertBindings env keyMod (stripDeadPureLets rawBody)
    let used ← match ← exprActiveDirectConsts env stripped with
      | .ok arr => pure arr
      | .error reason =>
        cacheRef.modify fun c =>
          { c with scanErrors := if c.scanErrors.contains cur then c.scanErrors else c.scanErrors.insert cur reason }
        pure #[]
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
      (m == ifaceMod || isInModuleSubtree m implMod) && !isCompilerAux c)
    start

private partial def exprContainsAnyFVar (fvars : Std.HashSet FVarId) (e : Expr) : Bool :=
  e.hasAnyFVar (fun fv => fvars.contains fv)

private partial def isStaticFalseProp (e : Expr) : MetaM BoundedBool := do
  let p ← match ← runBoundedMeta (whnf e) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  if p.isConstOf ``False then return .isTrue
  if p.isAppOfArity ``Not 1 then
    let inner ← match ← runBoundedMeta (whnf p.appArg!) with
      | .ok w => pure w.consumeMData
      | .error r => return .inconclusive r
    if inner.isConstOf ``True then return .isTrue
    if inner.isAppOfArity ``Eq 3 then
      let args := inner.getAppArgs
      if args[1]! == args[2]! then return .isTrue
      match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq args[1]! args[2]!)) (maxRecDepth := 1024) with
      | .ok true => return .isTrue
      | .ok false => pure ()
      | .error r => return .inconclusive r
  if !p.hasFVar && !p.hasLooseBVars then
    match ← runBoundedMeta (withLCtx {} #[] (trySynthInstance (mkApp (mkConst ``Decidable) p))) (maxRecDepth := 1024) with
    | .error r => return .inconclusive r
    | .ok (.some inst) =>
      match ← runBoundedMeta (withTransparency .all (whnf (mkApp2 (mkConst ``decide) p inst))) (maxRecDepth := 1024) with
      | .error r => return .inconclusive r
      | .ok b => if b.consumeMData.isConstOf ``Bool.false then return .isTrue
    | .ok .none => pure ()
    | .ok .undef => return .inconclusive "Decidable instance synthesis incomplete"
  return .isFalse

private partial def isStaticTrueProp (e : Expr) : MetaM BoundedBool := do
  let p ← match ← runBoundedMeta (whnf e) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  if p.isConstOf ``True then return .isTrue
  if p.isAppOfArity ``And 2 then
    let l ← isStaticTrueProp p.appFn!.appArg!
    let r ← isStaticTrueProp p.appArg!
    match l, r with
    | .inconclusive msg, _ | _, .inconclusive msg => return .inconclusive msg
    | .isTrue, .isTrue => return .isTrue
    | _, _ => return .isFalse
  if p.isAppOfArity ``Not 1 then
    return ← isStaticFalseProp p.appArg!
  if p.isAppOfArity ``Eq 3 then
    let args := p.getAppArgs
    if args[1]! == args[2]! then return .isTrue
    match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq args[1]! args[2]!)) (maxRecDepth := 1024) with
    | .ok true => return .isTrue
    | .ok false => pure ()
    | .error r => return .inconclusive r
  if !p.hasFVar && !p.hasLooseBVars then
    match ← runBoundedMeta (withLCtx {} #[] (trySynthInstance (mkApp (mkConst ``Decidable) p))) (maxRecDepth := 1024) with
    | .error r => return .inconclusive r
    | .ok (.some inst) =>
      match ← runBoundedMeta (withTransparency .all (whnf (mkApp2 (mkConst ``decide) p inst))) (maxRecDepth := 1024) with
      | .error r => return .inconclusive r
      | .ok b => if b.consumeMData.isConstOf ``Bool.true then return .isTrue
    | .ok .none => pure ()
    | .ok .undef => return .inconclusive "Decidable instance synthesis incomplete"
  return .isFalse

private def isNegationPair (a b : Expr) : MetaM BoundedBool := do
  let a' ← match ← runBoundedMeta (whnf a) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  let b' ← match ← runBoundedMeta (whnf b) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  if b'.isAppOfArity ``Not 1 then
    match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq a' b'.appArg!)) (maxRecDepth := 1024) with
    | .ok true => return .isTrue
    | .ok false => pure ()
    | .error r => return .inconclusive r
  if a'.isAppOfArity ``Not 1 then
    match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq b' a'.appArg!)) (maxRecDepth := 1024) with
    | .ok true => return .isTrue
    | .ok false => pure ()
    | .error r => return .inconclusive r
  return .isFalse

private partial def isMeaningfulBoundaryProp
    (boundaryFVars assertBoundFVars : Std.HashSet FVarId)
    (e : Expr) : MetaM BoundedBool := do
  let p ← match ← runBoundedMeta (whnf e) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  match ← isStaticTrueProp p with
  | .isFalse => pure ()
  | .isTrue => return .isFalse
  | .inconclusive r => return .inconclusive r
  match ← isStaticFalseProp p with
  | .isFalse => pure ()
  | .isTrue => return .isFalse
  | .inconclusive r => return .inconclusive r
  if !exprContainsAnyFVar boundaryFVars p then return .isFalse
  if p.isAppOfArity ``And 2 then
    let lhs := p.appFn!.appArg!
    let rhs := p.appArg!
    for side in #[lhs, rhs] do
      match ← isStaticTrueProp side with
      | .isFalse => pure ()
      | .isTrue => return .isFalse
      | .inconclusive r => return .inconclusive r
      match ← isStaticFalseProp side with
      | .isFalse => pure ()
      | .isTrue => return .isFalse
      | .inconclusive r => return .inconclusive r
    if lhs.consumeMData.isForall then
      match ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs with
      | .isTrue => pure ()
      | bad => return bad
    if rhs.consumeMData.isForall then
      match ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars rhs with
      | .isTrue => pure ()
      | bad => return bad
    let lRes ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs
    let rRes ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars rhs
    match lRes, rRes with
    | .inconclusive r, _ | _, .inconclusive r => return .inconclusive r
    | .isTrue, _ | _, .isTrue => return .isTrue
    | .isFalse, .isFalse => return .isFalse
  if p.isAppOfArity ``Or 2 then
    let lhs := p.appFn!.appArg!
    let rhs := p.appArg!
    match ← isNegationPair lhs rhs with
    | .isFalse => pure ()
    | .isTrue => return .isFalse
    | .inconclusive r => return .inconclusive r
    match ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs with
    | .isTrue => return ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars rhs
    | bad => return bad
  if p.isAppOfArity ``Exists 2 then
    let dom := p.appFn!.appArg!
    if ← isProp dom then
      match ← isStaticFalseProp dom with
      | .isFalse => pure ()
      | .isTrue => return .isFalse
      | .inconclusive r => return .inconclusive r
    return ← lambdaBoundedTelescope p.appArg! 1 fun xs body => do
      let bVars := xs.foldl (fun (s : Std.HashSet FVarId) x => s.insert x.fvarId!) assertBoundFVars
      isMeaningfulBoundaryProp boundaryFVars bVars body
  if let .forallE n dom body bi := p then
    if ← isProp dom then
      match ← isStaticFalseProp dom with
      | .isFalse => pure ()
      | .isTrue => return .isFalse
      | .inconclusive r => return .inconclusive r
      match ← isStaticTrueProp dom with
      | .isFalse => pure ()
      | .isTrue => return .isFalse
      | .inconclusive r => return .inconclusive r
      if !body.hasLooseBVar 0 then
        match ← isStaticFalseProp body with
        | .isTrue => return ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars dom
        | .inconclusive r => return .inconclusive r
        | .isFalse => pure ()
      if !exprContainsAnyFVar assertBoundFVars dom then return .isFalse
      if exprContainsAnyFVar boundaryFVars dom then return .isFalse
      return ← withLocalDecl n bi dom fun h => do
        let concl := body.instantiate1 h
        match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq dom concl)) (maxRecDepth := 1024) with
        | .error r => return .inconclusive r
        | .ok true => return .isFalse
        | .ok false => isMeaningfulBoundaryProp boundaryFVars assertBoundFVars concl
    else
      let dClean ← match ← runBoundedMeta (whnf dom) with
        | .ok w => pure w.consumeMData
        | .error r => return .inconclusive r
      if dClean.isConstOf ``Empty || dClean.isConstOf ``PEmpty then return .isFalse
      return ← withLocalDecl n bi dom fun x =>
        isMeaningfulBoundaryProp boundaryFVars (assertBoundFVars.insert x.fvarId!) (body.instantiate1 x)
  if p.isAppOfArity ``Eq 3 then
    let args := p.getAppArgs
    let lhs := args[1]!
    let rhs := args[2]!
    if lhs == rhs then return .isFalse
    match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq lhs rhs)) (maxRecDepth := 1024) with
    | .error r => return .inconclusive r
    | .ok true => return .isFalse
    | .ok false => pure ()
    if lhs.consumeMData.isAppOfArity ``Decidable.decide 2 && rhs.consumeMData.isConstOf ``Bool.true then
      return ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars lhs.consumeMData.appFn!.appArg!
    return if exprContainsAnyFVar boundaryFVars lhs || exprContainsAnyFVar boundaryFVars rhs then .isTrue else .isFalse
  if p.isAppOfArity ``Not 1 then
    let inner ← match ← runBoundedMeta (whnf p.appArg!) with
      | .ok w => pure w.consumeMData
      | .error r => return .inconclusive r
    match ← isStaticTrueProp inner with
    | .isFalse => pure ()
    | .isTrue => return .isFalse
    | .inconclusive r => return .inconclusive r
    match ← isStaticFalseProp inner with
    | .isFalse => pure ()
    | .isTrue => return .isFalse
    | .inconclusive r => return .inconclusive r
    return ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars inner
  return if exprContainsAnyFVar boundaryFVars p then .isTrue else .isFalse

private partial def validateAssertsInExpr
    (boundaryFVars assertBoundFVars : Std.HashSet FVarId)
    (e : Expr) : MetaM (Bool × BoundedBool) := do
  let cur := e.consumeMData
  if cur.isAppOfArity `Core.NondetTest.assert 3 then
    let ok ← isMeaningfulBoundaryProp boundaryFVars assertBoundFVars cur.appArg!
    return (true, ok)
  match cur with
  | .app _ _ =>
    cur.withApp fun fn args => do
      let nonLamHasBoundary := exprContainsAnyFVar boundaryFVars fn ||
        args.any (fun a => !(a.consumeMData matches .lam _ _ _ _) && exprContainsAnyFVar boundaryFVars a)
      let (foundF, statusF) ← validateAssertsInExpr boundaryFVars assertBoundFVars fn
      match statusF with
      | .isTrue => pure ()
      | bad => if foundF then return (true, bad)
      let mut anyFound := foundF
      for arg in args do
        let aClean := arg.consumeMData
        if aClean.isLambda then
          let (foundA, statusA) ← lambdaTelescope aClean fun lxs lbody => do
            let mut nextBoundary := boundaryFVars
            let mut nextBound := assertBoundFVars
            for x in lxs do
              nextBound := nextBound.insert x.fvarId!
              if nonLamHasBoundary && !(← isProp (← inferType x)) then
                nextBoundary := nextBoundary.insert x.fvarId!
            validateAssertsInExpr nextBoundary nextBound lbody
          anyFound := anyFound || foundA
          if foundA then
            match statusA with
            | .isTrue => pure ()
            | bad => return (true, bad)
        else
          let (foundA, statusA) ← validateAssertsInExpr boundaryFVars assertBoundFVars arg
          anyFound := anyFound || foundA
          if foundA then
            match statusA with
            | .isTrue => pure ()
            | bad => return (true, bad)
      return (anyFound, .isTrue)
  | .lam n t b bi =>
    withLocalDecl n bi t fun x =>
      validateAssertsInExpr boundaryFVars (assertBoundFVars.insert x.fvarId!) (b.instantiate1 x)
  | .letE _ _ v b _ =>
    let (foundV, statusV) ← validateAssertsInExpr boundaryFVars assertBoundFVars v
    if foundV then
      match statusV with
      | .isTrue => pure ()
      | bad => return (true, bad)
    let (foundB, statusB) ← validateAssertsInExpr boundaryFVars assertBoundFVars (b.instantiate1 v)
    if foundB then
      return (true, statusB)
    return (foundV, .isTrue)
  | _ => return (false, .isTrue)

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
  let isProcessPkg := pkgNs == `LeanSwe.Process
  match env.header.moduleNames.findIdx? (· == ifaceMod) with
  | none => false
  | some idx =>
    match env.header.moduleData[idx]? with
    | none => false
    | some md => Id.run do
      if !isProcessPkg && md.imports.any (fun imp =>
          imp.module == `LeanSwe.Process.Interface || imp.module == `LeanSwe.Process.SysBridge) then
        return true
      let mut modImportsCli : Std.HashMap Name Bool := {}
      for h : mi in [0 : env.header.moduleNames.size] do
        let mName := env.header.moduleNames[mi]
        if let some mData := env.header.moduleData[mi]? then
          let usesProc := mData.imports.any fun imp =>
            imp.module == `LeanSwe.Process.Interface || imp.module == `LeanSwe.Process.SysBridge
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
            (cMod == `LeanSwe.Process.Interface || cMod == `LeanSwe.Process.SysBridge) then
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
  let wantFuzzRest := s!"harness/fuzz/{restSlash.toLower}/"
  let wantFuzzLast := s!"harness/fuzz/{lastSeg.toLower}/"
  return dirPats.any fun p =>
    let pl := p.toLower
    pl == wantFuzzRest || pl == wantFuzzLast ||
      normKey pl == normKey wantFuzzRest || normKey pl == normKey wantFuzzLast

private def parseFuzzCoveredPackages (repoDir : System.FilePath) (knownPkgs : Array Name) :
    IO (Except String (Std.HashSet Name)) := do
  let manifestPath := repoDir / "harness" / "Fuzz" / "suites.json"
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

private def usesExternalCliPkg (env : Environment) (knownPkgs : Array Name) (pkgNs : Name) : Bool := Id.run do
  if pkgNs == `LeanSwe.Process then
    return false
  for h : mi in [0 : env.header.moduleNames.size] do
    let mName := env.header.moduleNames[mi]
    if mName.getRoot == `LeanSwe && pkgNamespaceOfSpecWith knownPkgs mName == pkgNs &&
        !isSpecOrRuntimeOrProofsModule mName && mName.getString! != "Model" && mName.getString! != "SpecMutants" then
      if let some md := env.header.moduleData[mi]? then
        for c in md.constants do
          if isPrivateName c.name || isCompilerAux c.name then continue
          let used := match c with
            | .defnInfo dv => dv.type.getUsedConstants ++ dv.value.getUsedConstants
            | .opaqueInfo ov => ov.type.getUsedConstants ++ ov.value.getUsedConstants
            | _ => c.type.getUsedConstants
          if used.any fun u =>
              let uMod := moduleOfConst env u
              uMod == `LeanSwe.Process.Interface || uMod == `LeanSwe.Process.SysBridge then
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

private def nonProjectReducibilityStatus (env : Environment) (cName : Name) : ReducibilityStatus := Id.run do
  let mut st : ReducibilityStatus :=
    match env.getModuleIdxFor? cName with
    | some defIdx =>
      match (Lean.reducibilityCoreExt.getModuleEntries env defIdx).binSearch
          (cName, .semireducible) (fun a b => Name.quickLt a.1 b.1) with
      | some (_, s) => s
      | none => .semireducible
    | none => .semireducible
  for h : i in [0 : env.header.moduleNames.size] do
    if !isProjectOrTestModule env.header.moduleNames[i] then
      for entry in Lean.reducibilityExtraExt.ext.getModuleEntries env i do
        if let .global (n, s) := entry then
          if n == cName then
            st := s
  return st

/-- Run `act` while preserving the ambient `Core.State.cache`. `MonadEnv.modifyEnv` (used by
`setEnv`, `withEnv`, and `withoutModifyingEnv'`) clears `Core.State.cache := {}`, so saving before
and restoring after in `finally` keeps the ambient cache intact without leaking entries created
under a temporary `Environment`. -/
private def withPreservedCoreCache {m : Type → Type} {α : Type}
    [Monad m] [MonadFinally m] [MonadStateOf Core.State m] (act : m α) : m α := do
  let savedCache := (← getThe Core.State).cache
  try act
  finally modifyThe Core.State fun s => { s with cache := savedCache }

/-- Build a copy of the current `Environment` with project-applied `@[irreducible]` attributes
relaxed back to their pre-project reducibility status, leaving the ambient `CoreM` environment,
`Core.State.cache`, and stdlib `@[irreducible]` barriers unchanged. -/
private def mkRelaxedProjectIrreduciblesEnv : CoreM Environment := do
  let (_, relaxedEnv) ← withPreservedCoreCache <| withoutModifyingEnv' do
    let env ← getEnv
    let mut toRestore : Array (Name × ReducibilityStatus) := #[]
    for h : i in [0 : env.header.moduleNames.size] do
      if isProjectOrTestModule env.header.moduleNames[i] then
        for (cName, status) in Lean.reducibilityCoreExt.getModuleEntries env i do
          if status == .irreducible && (← isIrreducible cName) then
            toRestore := toRestore.push (cName, .semireducible)
        for entry in Lean.reducibilityExtraExt.ext.getModuleEntries env i do
          if let .global (cName, .irreducible) := entry then
            if (← isIrreducible cName) then
              let origStatus :=
                if isProjectOrTestModule (moduleOfConst env cName) then
                  .semireducible
                else
                  nonProjectReducibilityStatus env cName
              if origStatus != .irreducible then
                toRestore := toRestore.push (cName, origStatus)
    for (cName, status) in toRestore do
      setReducibilityStatus cName status
  return relaxedEnv

/-- Bounded Meta-level definitional-equality check for `Core.Refines` triviality gates.
Temporarily runs `Meta.isDefEq` at `.default` transparency under `relaxedEnv` with fresh
`CoreM`/`MetaM` caches so project `@[irreducible]` definitions (and cross-module global
`[irreducible]` attributes applied in project modules) unfold while preserving stdlib
`@[irreducible]` barriers, full Lean WHNF/defeq caching, and the unmodified ambient
`CoreM`/`MetaM` environment and caches outside this check (`setEnv` clears `Core.State.cache`
via `modifyEnv`, so `withPreservedCoreCache` restores the ambient `CoreM` cache after `withEnv`
drops entries computed under `relaxedEnv`). -/
private def boundedMetaDefEq (relaxedEnv : Environment) (a b : Expr) : MetaM BoundedBool := do
  withPreservedCoreCache <| Meta.withFreshCache <| withEnv relaxedEnv do
    match ← runBoundedMeta
        (Meta.withNewMCtxDepth <| Meta.withTransparency .default <| isDefEq a b)
        (maxRecDepth := 1024) with
    | .ok true => return .isTrue
    | .ok false => return .isFalse
    | .error r => return .inconclusive r

private def isDefEqPropAtom (relaxedEnv : Environment) (e : Expr) : MetaM BoundedBool := do
  let p := e.consumeMData
  if p.isAppOfArity ``Eq 3 then
    if (p.getArg! 1).consumeMData == (p.getArg! 2).consumeMData then return .isTrue
    return ← boundedMetaDefEq relaxedEnv (p.getArg! 1) (p.getArg! 2)
  if p.isAppOfArity ``Iff 2 then
    if (p.getArg! 0).consumeMData == (p.getArg! 1).consumeMData then return .isTrue
    return ← boundedMetaDefEq relaxedEnv (p.getArg! 0) (p.getArg! 1)
  return .isFalse

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
  match ← withLCtx {} #[] (runBoundedMeta (trySynthInstance (mkApp (mkConst ``Inhabited l0) ty))) with
  | .ok (.some _) => return true
  | _ => pure ()
  match ← withLCtx {} #[] (runBoundedMeta (trySynthInstance (mkApp (mkConst ``Nonempty l0) ty))) with
  | .ok (.some _) => return true
  | _ => pure ()
  let .ok wRaw ← runBoundedMeta (whnf ty) | return false
  let w := wRaw.consumeMData
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
            match ← isStaticTrueProp fTy with
            | .isTrue => pure ()
            | .isFalse | .inconclusive _ => return false
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
        match ← withLCtx {} #[] (runBoundedMeta (trySynthInstance xTy)) with
        | .ok (.some inst) => subst := subst.push (x, inst)
        | _ => return false
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
    (rawArg : Expr)
    (allowImplicitGroundTypeOnMk : Bool := false) : MetaM (Option Name) := do
  let clean := rawArg.consumeMData
  if allowId && clean.isAppOfArity ``id 1 then
    return some ``id
  let checkAppBody (allowedFVars : Std.HashSet FVarId) (body : Expr) : MetaM (Option Name) := do
    let bc := body.consumeMData
    let .const fn fnLvls := bc.getAppFn.consumeMData | return none
    if isCompilerAux fn then return none
    let appArgs := bc.getAppArgs
    if !allowImplicitGroundTypeOnMk then
      let mut seenFVs : Std.HashSet FVarId := {}
      for a in appArgs do
        let ac := a.consumeMData
        let .fvar fv := ac | return none
        if !allowedFVars.contains fv || seenFVs.contains fv then
          return none
        seenFVs := seenFVs.insert fv
      return some fn
    else
      let some ci := env.find? fn | return none
      let mut curTy := ci.type.instantiateLevelParams ci.levelParams fnLvls
      let mut seenFVs : Std.HashSet FVarId := {}
      for a in appArgs do
        let ac := a.consumeMData
        let mut paramDom? : Option Expr := none
        let mut paramBi? : Option BinderInfo := none
        match curTy.consumeMData with
        | .forallE _ dom rest bi =>
          curTy := rest.instantiate1 ac
          paramDom? := some dom.consumeMData
          paramBi? := some bi
        | _ => pure ()
        match ac with
        | .fvar fv =>
          if !allowedFVars.contains fv || seenFVs.contains fv then
            return none
          seenFVs := seenFVs.insert fv
        | _ =>
          let (some pDom, some pBi) := (paramDom?, paramBi?) | return none
          if pBi == .default || pBi == .instImplicit then return none
          if pDom != .sort (.succ .zero) then return none
          if ac.hasFVar || ac.hasLooseBVars then return none
          if (← inferType ac).consumeMData != .sort (.succ .zero) then return none
          if !(← isProvablyInhabitedDataType env 8 ac) then return none
      if !appArgs.isEmpty && seenFVs.isEmpty then return none
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
      checkAppBody allowed body
  else
    checkAppBody outerAllowedFVars clean

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

private partial def isPureReqProjExpr (reqFV : FVarId) (e : Expr) : Bool :=
  let c := e.consumeMData
  match c with
  | .fvar fv => fv == reqFV
  | .proj ``Prod _ inner => isPureReqProjExpr reqFV inner
  | _ =>
    let fn := c.getAppFn.consumeMData
    let args := c.getAppArgs
    if (fn.isConstOf ``Prod.fst || fn.isConstOf ``Prod.snd) && args.size == 3 then
      isPureReqProjExpr reqFV args[2]!
    else
      false

private def execPkgInvokesApiParam (env : Environment) (execPkgFn : Name) : MetaM Bool := do
  let some (.defnInfo dv) := env.find? execPkgFn | return false
  lambdaTelescope dv.value fun xs body => do
    if xs.size < 3 then return false
    let apiFV := xs[1]!.fvarId!
    let reqFV := xs[2]!.fvarId!
    let reqTy := (← inferType xs[2]!).consumeMData
    let reqTriv := reqTy.isConstOf ``Unit || reqTy.isConstOf ``PUnit
    let bc := body.consumeMData
    if bc.getAppFn.consumeMData != .fvar apiFV then return false
    let callArgs := bc.getAppArgs
    if callArgs.isEmpty then
      return reqTriv
    for i in [0 : callArgs.size] do
      let ai := callArgs[i]!.consumeMData
      if !isPureReqProjExpr reqFV ai then return false
      for j in [0 : i] do
        if callArgs[j]!.consumeMData == ai then return false
    return true

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
  if cName != Name.str pkg "defaultApi" && cName != Name.str pkg "defaultOps" &&
      cName != Name.str pkg "defaultOpsBase" && cName != Name.str pkg "defaultRawOps" then
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

private def checkWfNotVacuous (env : Environment) (sTy : Expr) (wfFn : Name) : MetaM BoundedBool := do
  let some (.defnInfo _) := env.find? wfFn | return .isFalse
  if !(← isProvablyInhabitedDataType env 8 sTy) then return .isFalse
  withLocalDeclD `_wfState sTy fun s => do
    let app := mkApp (mkConst wfFn) s
    let w ← match ← runBoundedMeta (withTransparency .all (whnf app)) with
      | .ok w' => pure w'
      | .error r => return .inconclusive r
    if w.consumeMData.isConstOf ``Bool.false then return .isFalse
    let eqTrue := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) app (mkConst ``Bool.true)
    match ← isStaticFalseProp eqTrue with
    | .isFalse => return .isTrue
    | .isTrue => return .isFalse
    | .inconclusive r => return .inconclusive r

private def isTrivialPayloadType (ty : Expr) : MetaM BoundedBool := do
  if ← isProp ty then return .isTrue
  match ← runBoundedMeta (whnf ty) with
  | .error r => return .inconclusive r
  | .ok wRaw =>
    let w := wRaw.consumeMData
    return if w.isConstOf ``Unit || w.isConstOf ``PUnit || w.isConstOf ``Empty || w.isConstOf ``PEmpty then
      .isTrue
    else .isFalse

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

private partial def reduceMatchersBounded (fuel : Nat) (e : Expr) : MetaM (Except String Expr) := do
  if fuel == 0 then return .ok e
  match ← runBoundedMeta (Core.betaReduce e) with
  | .error reason => return .error reason
  | .ok redE =>
    let b := redE.headBeta.consumeMData
    match ← runBoundedMeta (Meta.reduceMatcher? b) with
    | .error reason => return .error reason
    | .ok (.reduced b') => reduceMatchersBounded (fuel - 1) b'
    | .ok _ =>
      match b with
      | .app f a =>
        match ← reduceMatchersBounded (fuel - 1) f with
        | .error reason => return .error reason
        | .ok f' =>
          match ← reduceMatchersBounded (fuel - 1) a with
          | .error reason => return .error reason
          | .ok a' =>
            let appE := (Expr.app f' a').headBeta
            match ← runBoundedMeta (Meta.reduceMatcher? appE) with
            | .error reason => return .error reason
            | .ok (.reduced r) => reduceMatchersBounded (fuel - 1) r
            | .ok _ => return .ok appE
      | .lam n t body bi =>
        withLocalDecl n bi t fun x => do
          match ← reduceMatchersBounded (fuel - 1) (body.instantiate1 x) with
          | .error reason => return .error reason
          | .ok body' => return .ok (← mkLambdaFVars #[x] body')
      | .forallE n t body bi =>
        withLocalDecl n bi t fun x => do
          match ← reduceMatchersBounded (fuel - 1) (body.instantiate1 x) with
          | .error reason => return .error reason
          | .ok body' => return .ok (← mkForallFVars #[x] body')
      | .letE n t v body _ =>
        if !body.hasLooseBVar 0 then
          reduceMatchersBounded (fuel - 1) (body.lowerLooseBVars 1 1)
        else
          match ← reduceMatchersBounded (fuel - 1) v with
          | .error reason => return .error reason
          | .ok v' =>
            withLetDecl n t v' fun x => do
              match ← reduceMatchersBounded (fuel - 1) (body.instantiate1 x) with
              | .error reason => return .error reason
              | .ok body' => return .ok (← mkLetFVars #[x] body' (usedLetOnly := true))
      | _ => return .ok b

private def expandModelPropRels (env : Environment) (modelMods : Std.HashSet Name) (extraFn : Name) (e : Expr) :
    MetaM (Except String Expr) := do
  let shouldUnfold (fn : Name) : Bool :=
    fn == extraFn ||
      (modelMods.contains (moduleOfConst env fn) && !isCompilerAux fn &&
        match env.find? fn with
        | some (.defnInfo dv) =>
          dv.type.getForallBody.consumeMData == .sort .zero && (exprAstNodesAtMost 4096 dv.value).isSome
        | _ => false)
  match ← runBoundedMeta (Meta.deltaExpand e shouldUnfold (allowOpaque := false)) with
  | .error reason => return .error reason
  | .ok d =>
    match ← reduceMatchersBounded 16 d with
    | .error reason => return .error reason
    | .ok r => return .ok (stripSyntacticReflAtoms r)

private def isTrivialPropExpr (relaxedEnv : Environment) (e : Expr) : MetaM BoundedBool := do
  match ← isDefEqPropAtom relaxedEnv e with
  | .isFalse => isStaticTrueProp e
  | other => return other

private def checkWrappedPayloadSensitive
    (env relaxedEnv : Environment)
    (modelMods : Std.HashSet Name)
    (mkPred : Expr → MetaM Expr)
    (unfoldFn : Name)
    (ty : Expr) : MetaM BoundedBool := do
  let ow ← match ← runBoundedMeta (whnf ty) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  if ow.isAppOfArity ``Except 2 then
    let lvls := ow.getAppFn.consumeMData.constLevels!
    let errTy := ow.appFn!.appArg!
    let okTy := ow.appArg!
    match ← isTrivialPayloadType okTy with
    | .inconclusive r => return .inconclusive r
    | .isTrue => return .isTrue
    | .isFalse =>
      return ← withLocalDeclD `_refOk1 okTy fun v1 =>
        withLocalDeclD `_refOk2 okTy fun v2 => do
          let pOk1 ← mkPred (mkApp3 (mkConst ``Except.ok lvls) errTy okTy v1)
          let pOk2 ← mkPred (mkApp3 (mkConst ``Except.ok lvls) errTy okTy v2)
          let expOk1 ← match ← expandModelPropRels env modelMods unfoldFn pOk1 with
            | .ok e => pure e
            | .error r => return .inconclusive r
          if !expOk1.hasAnyFVar (· == v1.fvarId!) then return .isFalse
          match ← isTrivialPropExpr relaxedEnv expOk1 with
          | .isFalse => pure ()
          | .isTrue => return .isFalse
          | .inconclusive r => return .inconclusive r
          match ← boundedMetaDefEq relaxedEnv pOk1 pOk2 with
          | .isFalse => return .isTrue
          | .isTrue => return .isFalse
          | .inconclusive r => return .inconclusive r
  else if ow.isAppOfArity ``Option 1 then
    let lvls := ow.getAppFn.consumeMData.constLevels!
    let valTy := ow.appArg!
    match ← isTrivialPayloadType valTy with
    | .inconclusive r => return .inconclusive r
    | .isTrue => return .isTrue
    | .isFalse =>
      return ← withLocalDeclD `_refSome1 valTy fun v1 =>
        withLocalDeclD `_refSome2 valTy fun v2 => do
          let pSm1 ← mkPred (mkApp2 (mkConst ``Option.some lvls) valTy v1)
          let pSm2 ← mkPred (mkApp2 (mkConst ``Option.some lvls) valTy v2)
          let expSm1 ← match ← expandModelPropRels env modelMods unfoldFn pSm1 with
            | .ok e => pure e
            | .error r => return .inconclusive r
          if !expSm1.hasAnyFVar (· == v1.fvarId!) then return .isFalse
          match ← isTrivialPropExpr relaxedEnv expSm1 with
          | .isFalse => pure ()
          | .isTrue => return .isFalse
          | .inconclusive r => return .inconclusive r
          match ← boundedMetaDefEq relaxedEnv pSm1 pSm2 with
          | .isFalse => return .isTrue
          | .isTrue => return .isFalse
          | .inconclusive r => return .inconclusive r
  return .isTrue

private partial def hasVacuousInputBranch
    (relaxedEnv : Environment)
    (fuel : Nat)
    (outFV : FVarId)
    (isConjPart : Bool)
    (e : Expr) : MetaM BoundedBool := do
  if fuel == 0 then return .isFalse
  let c := e.consumeMData
  if !c.hasAnyFVar (· == outFV) then
    return .isTrue
  if c.isAppOfArity ``And 2 then
    match ← hasVacuousInputBranch relaxedEnv (fuel - 1) outFV true c.appFn!.appArg! with
    | .isFalse => return ← hasVacuousInputBranch relaxedEnv (fuel - 1) outFV true c.appArg!
    | other => return other
  if c.isAppOfArity ``ite 5 then
    let cond := c.getArg! 1
    let tBr := c.getArg! 3
    let eBr := c.getArg! 4
    if !cond.hasAnyFVar (· == outFV) then
      match ← hasVacuousInputBranch relaxedEnv (fuel - 1) outFV isConjPart tBr with
      | .isFalse => return ← hasVacuousInputBranch relaxedEnv (fuel - 1) outFV isConjPart eBr
      | other => return other
  if c.isAppOfArity ``dite 5 then
    let cond := c.getArg! 1
    let tLam := c.getArg! 3
    let eLam := c.getArg! 4
    if !cond.hasAnyFVar (· == outFV) then
      let resT ← withLocalDeclD `_ditePos cond fun hp =>
        hasVacuousInputBranch relaxedEnv (fuel - 1) outFV isConjPart ((Expr.app tLam hp).headBeta)
      match resT with
      | .isFalse =>
        let negCond := mkApp (mkConst ``Not) cond
        return ← withLocalDeclD `_diteNeg negCond fun hn =>
          hasVacuousInputBranch relaxedEnv (fuel - 1) outFV isConjPart ((Expr.app eLam hn).headBeta)
      | other => return other
  if let .forallE n dom body bi := c then
    if !dom.hasAnyFVar (· == outFV) then
      if ← isProp dom then
        if !isConjPart then
          match ← isStaticTrueProp dom with
          | .isTrue => pure ()
          | .isFalse => return .isTrue
          | .inconclusive r => return .inconclusive r
      return ← withLocalDecl n bi dom fun hx =>
        hasVacuousInputBranch relaxedEnv (fuel - 1) outFV isConjPart (body.instantiate1 hx)
  return ← isDefEqPropAtom relaxedEnv c

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

private def groundSamplesForType (ty : Expr) : MetaM (Except String (Option (Array Expr))) := do
  let w ← match ← runBoundedMeta (whnf ty) with
    | .ok w' => pure w'.consumeMData
    | .error r => return .error r
  let mkNatLitTyped (t : Expr) (n : Nat) : MetaM (Except String (Option Expr)) := do
    let instTy := mkApp2 (mkConst ``OfNat [Level.zero]) t (mkRawNatLit n)
    match ← withLCtx {} #[] (runBoundedMeta (trySynthInstance instTy)) with
    | .ok (.some inst) => pure (.ok (some (mkApp3 (mkConst ``OfNat.ofNat [Level.zero]) t (mkRawNatLit n) inst)))
    | .ok .none => pure (.ok none)
    | .ok .undef => pure (.error "OfNat instance synthesis incomplete")
    | .error r => pure (.error r)
  if w.isConstOf ``Nat || w.isConstOf ``Int ||
      w.isConstOf ``UInt8 || w.isConstOf ``UInt16 ||
      w.isConstOf ``UInt32 || w.isConstOf ``UInt64 || w.isConstOf ``USize then
    match ← mkNatLitTyped w 0, ← mkNatLitTyped w 1, ← mkNatLitTyped w 2 with
    | .ok (some v0), .ok (some v1), .ok (some v2) => return .ok (some #[v0, v1, v2])
    | .error r, _, _ | _, .error r, _ | _, _, .error r => return .error r
    | _, _, _ => return .ok none
  if w.isConstOf ``String then
    return .ok (some #[mkStrLit "", mkStrLit "a", mkStrLit "b"])
  if w.isConstOf ``Bool then
    return .ok (some #[mkConst ``Bool.false, mkConst ``Bool.true])
  return .ok none

private def checkPureAllowedNonTrivial
    (env relaxedEnv : Environment)
    (modelMods : Std.HashSet Name)
    (specSubst : Expr)
    (specFn : Name)
    (inTysSubst : Array Expr)
    (outTySubst : Expr) : MetaM BoundedBool := do
  let mut allGroundSamples : Option (Array (Array Expr)) := some #[]
  for inTy in inTysSubst do
    if let some arr := allGroundSamples then
      match ← groundSamplesForType inTy with
      | .error r => return .inconclusive r
      | .ok (some sVals) => allGroundSamples := some (arr.push sVals)
      | .ok none => allGroundSamples := none
  let rec withInputs (idx : Nat) (acc : Array Expr) : MetaM BoundedBool := do
    if h : idx < inTysSubst.size then
      withLocalDeclD (Name.num `_refIn idx) inTysSubst[idx] fun v =>
        withInputs (idx + 1) (acc.push v)
    else
      withLocalDeclD `_refOut1 outTySubst fun y1 =>
      withLocalDeclD `_refOut2 outTySubst fun y2 => do
        let p1 := (mkAppN specSubst (acc.push y1)).headBeta
        let p2 := (mkAppN specSubst (acc.push y2)).headBeta
        let exp1 ← match ← expandModelPropRels env modelMods specFn p1 with
          | .ok e => pure e
          | .error r => return .inconclusive r
        if !exp1.hasAnyFVar (· == y1.fvarId!) then return .isFalse
        match ← hasVacuousInputBranch relaxedEnv 32 y1.fvarId! false exp1 with
        | .isFalse => pure ()
        | .isTrue => return .isFalse
        | .inconclusive r => return .inconclusive r
        for k in [0 : inTysSubst.size] do
          match ← isTrivialPayloadType inTysSubst[k]! with
          | .inconclusive r => return .inconclusive r
          | .isTrue => pure ()
          | .isFalse =>
            if !exp1.hasAnyFVar (· == acc[k]!.fvarId!) then return .isFalse
        match ← boundedMetaDefEq relaxedEnv p1 p2 with
        | .isFalse => pure ()
        | .isTrue => return .isFalse
        | .inconclusive r => return .inconclusive r
        let u1Raw ← match ← runBoundedMeta (Meta.deltaExpand p1 (· == specFn) (allowOpaque := false)) with
          | .ok e => pure e
          | .error r => return .inconclusive r
        let u1 := u1Raw.headBeta
        for cand in #[p1, u1, exp1] do
          match ← isTrivialPropExpr relaxedEnv cand with
          | .isFalse => pure ()
          | .isTrue => return .isFalse
          | .inconclusive r => return .inconclusive r
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
                  match ← isStaticFalseProp (substIn g) with
                  | .isFalse =>
                    anyGuardPossible := true
                    break
                  | .isTrue => pure ()
                  | .inconclusive r => return .inconclusive r
                if !anyGuardPossible then
                  return .isFalse
        let u1w ← match ← runBoundedMeta (whnf u1) with
          | .ok w => pure w.consumeMData
          | .error r => return .inconclusive r
        if u1w.isAppOfArity ``Or 2 then
          match ← isNegationPair u1w.appFn!.appArg! u1w.appArg! with
          | .isFalse => pure ()
          | .isTrue => return .isFalse
          | .inconclusive r => return .inconclusive r
        if outTySubst.consumeMData.isConstOf ``Bool then
          let pT := (mkAppN specSubst (acc.push (mkConst ``Bool.true))).headBeta
          let pF := (mkAppN specSubst (acc.push (mkConst ``Bool.false))).headBeta
          match ← isStaticTrueProp pT, ← isStaticTrueProp pF with
          | .inconclusive r, _ | _, .inconclusive r => return .inconclusive r
          | .isTrue, .isTrue => return .isFalse
          | _, _ => pure ()
        checkWrappedPayloadSensitive env relaxedEnv modelMods
          (fun y => pure (mkAppN specSubst (acc.push y)).headBeta) specFn outTySubst
  withInputs 0 #[]

private def checkStepAllowedNonTrivial
    (env relaxedEnv : Environment)
    (modelMods : Std.HashSet Name)
    (allowedArg : Expr)
    (allowedFn : Name)
    (sTy reqTy outTy : Expr) : MetaM BoundedBool := do
  withLocalDeclD `_stPre sTy fun s =>
  withLocalDeclD `_stReq reqTy fun req =>
  withLocalDeclD `_stOut1 outTy fun o1 =>
  withLocalDeclD `_stOut2 outTy fun o2 =>
  withLocalDeclD `_stPost1 sTy fun s1' =>
  withLocalDeclD `_stPost2 sTy fun s2' => do
    let p1 := (mkApp4 allowedArg s req o1 s1').headBeta
    let p2 := (mkApp4 allowedArg s req o2 s2').headBeta
    let exp1 ← match ← expandModelPropRels env modelMods allowedFn p1 with
      | .ok e => pure e
      | .error r => return .inconclusive r
    if !exp1.hasAnyFVar (· == o1.fvarId!) && !exp1.hasAnyFVar (· == s1'.fvarId!) then
      return .isFalse
    match ← isTrivialPayloadType reqTy with
    | .inconclusive r => return .inconclusive r
    | .isTrue => pure ()
    | .isFalse =>
      if !exp1.hasAnyFVar (· == req.fvarId!) then return .isFalse
    match ← boundedMetaDefEq relaxedEnv p1 p2 with
    | .isFalse => pure ()
    | .isTrue => return .isFalse
    | .inconclusive r => return .inconclusive r
    let u1Raw ← match ← runBoundedMeta (Meta.deltaExpand p1 (· == allowedFn) (allowOpaque := false)) with
      | .ok e => pure e
      | .error r => return .inconclusive r
    let u1 := u1Raw.headBeta
    for cand in #[p1, u1, exp1] do
      match ← isTrivialPropExpr relaxedEnv cand with
      | .isFalse => pure ()
      | .isTrue => return .isFalse
      | .inconclusive r => return .inconclusive r
    let u1w ← match ← runBoundedMeta (whnf u1) with
      | .ok w => pure w.consumeMData
      | .error r => return .inconclusive r
    if u1w.isAppOfArity ``Or 2 then
      match ← isNegationPair u1w.appFn!.appArg! u1w.appArg! with
      | .isFalse => pure ()
      | .isTrue => return .isFalse
      | .inconclusive r => return .inconclusive r
    match ← checkWrappedPayloadSensitive env relaxedEnv modelMods
        (fun o => pure (mkApp4 allowedArg s req o s1').headBeta) allowedFn outTy with
    | .isTrue => pure ()
    | other => return other
    let ow ← match ← runBoundedMeta (whnf outTy) with
      | .ok w => pure w.consumeMData
      | .error r => return .inconclusive r
    if let .const outIndName outLvls := ow.getAppFn.consumeMData then
      if isProjectModule (moduleOfConst env outIndName) then
        if let some (.inductInfo iv) := env.find? outIndName then
          if iv.numParams == 0 && iv.numIndices == 0 then
            for ctorName in iv.ctors do
              if let some (.ctorInfo ci) := env.find? ctorName then
                if ci.numFields == 1 then
                  let ctorConst := mkConst ctorName outLvls
                  let cTy ← inferType ctorConst
                  let cTyW ← match ← runBoundedMeta (whnf cTy) with
                    | .ok w => pure w.consumeMData
                    | .error r => return .inconclusive r
                  if let .forallE _ fldTy _ _ := cTyW then
                    match ← checkWrappedPayloadSensitive env relaxedEnv modelMods
                        (fun inner => pure (mkApp4 allowedArg s req (mkApp ctorConst inner) s1').headBeta)
                        allowedFn fldTy with
                    | .isTrue => pure ()
                    | other => return other
    return .isTrue

private partial def sampleDistinctValues (env : Environment) (fuel : Nat) (ty : Expr) :
    MetaM (Except String (Array Expr)) := do
  if fuel == 0 then return .ok #[]
  match ← groundSamplesForType ty with
  | .error r => return .error r
  | .ok (some gs) => return .ok gs
  | .ok none => pure ()
  let w ← match ← runBoundedMeta (whnf ty) with
    | .ok w' => pure w'.consumeMData
    | .error r => return .error r
  if w.isConstOf ``Unit then
    return .ok #[mkConst ``Unit.unit]
  if w.isConstOf ``PUnit then
    return .ok #[mkConst ``PUnit.unit w.getAppFn.consumeMData.constLevels!]
  if w.isConstOf ``Char then
    return .ok #[mkApp (mkConst ``Char.ofNat) (mkRawNatLit 97), mkApp (mkConst ``Char.ofNat) (mkRawNatLit 98)]
  if w.isConstOf ``Float then
    let u0 := mkApp (mkConst ``UInt64.ofNat) (mkRawNatLit 0)
    let u1 := mkApp (mkConst ``UInt64.ofNat) (mkRawNatLit 1)
    return .ok #[mkApp (mkConst ``Float.ofBits) u0, mkApp (mkConst ``Float.ofBits) u1]
  if w.isConstOf ``ByteArray then
    let b0 := mkApp (mkConst ``UInt8.ofNat) (mkRawNatLit 0)
    return .ok #[mkConst ``ByteArray.empty, mkApp2 (mkConst ``ByteArray.push) (mkConst ``ByteArray.empty) b0]
  let .const indName lvls := w.getAppFn.consumeMData | return .ok #[]
  let some (.inductInfo iv) := env.find? indName | return .ok #[]
  if iv.numIndices > 0 || iv.ctors.isEmpty then return .ok #[]
  let indArgs := w.getAppArgs
  if indArgs.size < iv.numParams then return .ok #[]
  let params := indArgs.extract 0 iv.numParams
  let mut out : Array Expr := #[]
  let maxCtors := Nat.min iv.ctors.length 16
  for cIdx in [0 : maxCtors] do
    let ctorName := iv.ctors[cIdx]!
    if let some (.ctorInfo _) := env.find? ctorName then
      let ctorApp := mkAppN (mkConst ctorName lvls) params
      let ctorTy ← inferType ctorApp
      let fieldSamples? ← forallTelescope ctorTy fun fxs _ => do
        let mut fSamples : Array (Array Expr) := #[]
        for fx in fxs do
          let fTy ← inferType fx
          if ← isProp fTy then return none
          match ← sampleDistinctValues env (fuel - 1) fTy with
          | .error _ => return none
          | .ok arr =>
            if arr.isEmpty then return none
            fSamples := fSamples.push (arr.extract 0 (Nat.min arr.size 3))
        return some fSamples
      if let some fSamples := fieldSamples? then
        let baseArgs := fSamples.map (fun s => s[0]!)
        out := out.push (mkAppN ctorApp baseArgs)
        if iv.ctors.length == 1 then
          for fi in [0 : fSamples.size] do
            let alts := fSamples[fi]!
            for ai in [1 : alts.size] do
              out := out.push (mkAppN ctorApp (baseArgs.set! fi alts[ai]!))
  return .ok out

private partial def extractNatLit? (e : Expr) : Option Nat :=
  let c := e.consumeMData
  match c with
  | .lit (.natVal n) => some n
  | _ =>
    if c.isConstOf ``Nat.zero then some 0
    else if c.isAppOfArity ``Nat.succ 1 then (extractNatLit? c.appArg!).map (· + 1)
    else none

private partial def areDemonstrablyDistinctGroundAux (env : Environment) (fuel : Nat) (a b : Expr) :
    MetaM BoundedBool := do
  if fuel == 0 then return .inconclusive "ground comparison depth budget exhausted"
  if a.hasFVar || b.hasFVar || a.hasLooseBVars || b.hasLooseBVars then
    return .inconclusive "non-ground output expression"
  let aw ← match ← runBoundedMeta (Meta.withTransparency .default (whnf a)) (maxRecDepth := 1024) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  let bw ← match ← runBoundedMeta (Meta.withTransparency .default (whnf b)) (maxRecDepth := 1024) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  if aw.hasFVar || bw.hasFVar || aw.hasLooseBVars || bw.hasLooseBVars then
    return .inconclusive "reduced output contains free variable"
  match extractNatLit? aw, extractNatLit? bw with
  | some n1, some n2 => return if n1 != n2 then .isTrue else .isFalse
  | _, _ => pure ()
  match aw, bw with
  | .lit (.strVal s1), .lit (.strVal s2) => return if s1 != s2 then .isTrue else .isFalse
  | .lit l1, .lit l2 => return if l1 != l2 then .isTrue else .isFalse
  | _, _ => pure ()
  match aw.getAppFn.consumeMData, bw.getAppFn.consumeMData with
  | .const c1 _, .const c2 _ =>
    match env.find? c1, env.find? c2 with
    | some (.ctorInfo ci1), some (.ctorInfo _) =>
      if c1 != c2 then return .isTrue
      let args1 := aw.getAppArgs
      let args2 := bw.getAppArgs
      if args1.size != args2.size then
        return .inconclusive "mismatched constructor arity"
      let mut sawInc? : Option String := none
      for k in [ci1.numParams : args1.size] do
        let argTy ← inferType args1[k]!
        if (← isProp argTy) || argTy.consumeMData.isSort then continue
        match ← areDemonstrablyDistinctGroundAux env (fuel - 1) args1[k]! args2[k]! with
        | .isTrue => return .isTrue
        | .isFalse => pure ()
        | .inconclusive r => if sawInc?.isNone then sawInc? := some r
      match sawInc? with
      | some r => return .inconclusive r
      | none => return .isFalse
    | _, _ =>
      return .inconclusive s!"output did not reduce to ground constructor or literal ({c1} vs {c2})"
  | _, _ =>
    return .inconclusive "output did not reduce to ground constructor or literal"

private def areDemonstrablyDistinctGround (env relaxedEnv : Environment) (a b : Expr) : MetaM BoundedBool :=
  withPreservedCoreCache <| Meta.withFreshCache <| withEnv relaxedEnv <|
    areDemonstrablyDistinctGroundAux env 16 a b

private def checkFnNotConstantOnType
    (env relaxedEnv : Environment)
    (domTy : Expr)
    (applyFn : Expr → Expr) : MetaM BoundedBool := do
  let symEq ← withLocalDeclD `_cDom1 domTy fun x1 =>
    withLocalDeclD `_cDom2 domTy fun x2 =>
      boundedMetaDefEq relaxedEnv (applyFn x1) (applyFn x2)
  match symEq with
  | .isTrue => return .isFalse
  | .inconclusive r => return .inconclusive r
  | .isFalse => pure ()
  let samples ← match ← sampleDistinctValues env 5 domTy with
    | .ok s => pure s
    | .error r => return .inconclusive r
  if samples.size < 2 then
    return .inconclusive "insufficient distinct ground constructor witnesses"
  let v0 := applyFn samples[0]!
  let mut sawInc? : Option String := none
  for i in [1 : samples.size] do
    match ← areDemonstrablyDistinctGround env relaxedEnv v0 (applyFn samples[i]!) with
    | .isTrue => return .isTrue
    | .isFalse => pure ()
    | .inconclusive r => if sawInc?.isNone then sawInc? := some r
  match sawInc? with
  | some r => return .inconclusive r
  | none => return .isFalse

private def checkRenderNotConstantOnObj
    (env relaxedEnv : Environment)
    (objTy tapeTy renderFn : Expr) : MetaM BoundedBool := do
  let symEq ← withLocalDeclD `_invObj1 objTy fun o1 =>
    withLocalDeclD `_invObj2 objTy fun o2 =>
      withLocalDeclD `_invTape tapeTy fun t =>
        boundedMetaDefEq relaxedEnv (mkApp2 renderFn o1 t) (mkApp2 renderFn o2 t)
  match symEq with
  | .isTrue => return .isFalse
  | .inconclusive r => return .inconclusive r
  | .isFalse => pure ()
  let objSamples ← match ← sampleDistinctValues env 5 objTy with
    | .ok s => pure s
    | .error r => return .inconclusive r
  if objSamples.size < 2 then
    return .inconclusive "insufficient distinct object witnesses for ObeysInverseRender"
  let tapeSamples ← match ← sampleDistinctValues env 5 tapeTy with
    | .ok s => pure s
    | .error r => return .inconclusive r
  if tapeSamples.isEmpty then
    return .inconclusive "no ground tape witness for ObeysInverseRender"
  let maxTapes := Nat.min tapeSamples.size 4
  let mut sawInc? : Option String := none
  for ti in [0 : maxTapes] do
    let t := tapeSamples[ti]!
    let v0 := (mkApp2 renderFn objSamples[0]! t).headBeta
    for oi in [1 : objSamples.size] do
      match ← areDemonstrablyDistinctGround env relaxedEnv v0 (mkApp2 renderFn objSamples[oi]! t).headBeta with
      | .isTrue => return .isTrue
      | .isFalse => pure ()
      | .inconclusive r => if sawInc?.isNone then sawInc? := some r
  match sawInc? with
  | some r => return .inconclusive r
  | none => return .isFalse

private def isAllowedErrorExtractorConst
    (env : Environment) (pkg : Name) (modelMods : Std.HashSet Name) (fn : Name) : Bool :=
  if isPrivateName fn then false
  else
    let m := moduleOfConst env fn
    let typesMod := Name.str pkg "Types"
    modelMods.contains m ||
      m == typesMod ||
      m.toString.startsWith (typesMod.toString ++ ".") ||
      (env.isProjectionFn fn && m.getRoot == `LeanSwe && m.components.contains `Types)

private def findRefinesOrObeysThm? (env : Environment) (pkg : Name) : Except String (Option Name) :=
  let topProofMod := Name.str pkg "Proofs"
  let obeysName := Name.str topProofMod "obeys_model"
  let refinesName := Name.str topProofMod "refines_model"
  let hasObeys := env.contains obeysName
  let hasRefines := env.contains refinesName
  if hasObeys && hasRefines then
    .error s!"DUPLICATE_OBEYS_AND_REFINES_MODEL: {pkg} defines both {obeysName} and {refinesName}"
  else if hasObeys then
    .ok (some obeysName)
  else if hasRefines then
    .ok (some refinesName)
  else
    .ok none

private def checkRefinesModelTheorem
    (env relaxedEnv : Environment)
    (transImpsOf : Name → Std.HashSet Name)
    (knownPkgs : Array Name)
    (pkg : Name)
    (modelMods : Std.HashSet Name)
    (axCacheIn : AxCache) : MetaM (Array String × AxCache) := do
  let mut errs : Array String := #[]
  let mut axCache := axCacheIn
  let topProofMod := Name.str pkg "Proofs"
  let ifaceMod := Name.str pkg "Interface"
  let implMod := Name.str pkg "Impl"

  for mMod in modelMods do
    for imp in transImpsOf mMod do
      if imp.getRoot == `LeanSwe && imp.isStr && (imp.getString! == "Interface" || imp.getString! == "Impl") then
        errs := errs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mMod} transitively imports {imp}"

  let thmName ← match findRefinesOrObeysThm? env pkg with
    | .error dupErr => return (#[dupErr], axCache)
    | .ok (some n) => pure n
    | .ok none =>
      return (#[s!"MISSING_REFINES_MODEL: {pkg} lacks public theorem {Name.str topProofMod "obeys_model"} (or legacy {Name.str topProofMod "refines_model"})"], axCache)

  let some (.thmInfo tv) := env.find? thmName
    | return (#[s!"MISSING_REFINES_MODEL: {thmName} must be a theorem in {topProofMod}"], axCache)
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
                match ← withLCtx {} #[] (runBoundedMeta (trySynthInstance instTyGround)) with
                | .ok (.some instVal) => instSubst := instSubst.push (instVar, instVal)
                | _ => allInstOk := false
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
          if ab.isAppOfArity `Core.RefinesPure 4 || ab.isAppOfArity `Core.ObeysPure 4 then
            let args := ab.getAppArgs; some (false, #[args[0]!], args[1]!, args[2]!, args[3]!)
          else if ab.isAppOfArity `Core.RefinesPure2 5 || ab.isAppOfArity `Core.ObeysPure2 5 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!], args[2]!, args[3]!, args[4]!)
          else if ab.isAppOfArity `Core.RefinesPure3 6 || ab.isAppOfArity `Core.ObeysPure3 6 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!, args[2]!], args[3]!, args[4]!, args[5]!)
          else if ab.isAppOfArity `Core.RefinesPure4 7 || ab.isAppOfArity `Core.ObeysPure4 7 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!, args[2]!, args[3]!], args[4]!, args[5]!, args[6]!)
          else if ab.isAppOfArity `Core.RefinesPureEq 4 || ab.isAppOfArity `Core.ObeysPureEq 4 then
            let args := ab.getAppArgs; some (true, #[args[0]!], args[1]!, args[2]!, args[3]!)
          else if ab.isAppOfArity `Core.RefinesPureEq2 5 || ab.isAppOfArity `Core.ObeysPureEq2 5 then
            let args := ab.getAppArgs; some (true, #[args[0]!, args[1]!], args[2]!, args[3]!, args[4]!)
          else if ab.isAppOfArity `Core.RefinesPureEq3 6 || ab.isAppOfArity `Core.ObeysPureEq3 6 then
            let args := ab.getAppArgs; some (true, #[args[0]!, args[1]!, args[2]!], args[3]!, args[4]!, args[5]!)
          else if ab.isAppOfArity `Core.RefinesPureEq4 7 || ab.isAppOfArity `Core.ObeysPureEq4 7 then
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
            match ← checkPureAllowedNonTrivial env relaxedEnv modelMods specSubst specFn inTysSubst outTySubst with
            | .isTrue => pure ()
            | .isFalse =>
              aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {specFn} for {implFn} in {thmName} is output-insensitive or tautological"
            | .inconclusive reason =>
              aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {specFn} for {implFn} in {thmName} ({reason})"
          if aErrs.isEmpty then
            coveredPureOpsRef.modify (·.insert implFn)
          return aErrs

        let pureErrMsgInfo? : Option (Array Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
          if ab.isAppOfArity `Core.ObeysPureEqUpToErrMsg 8 then
            let a := ab.getAppArgs; some (#[a[0]!], a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!)
          else if ab.isAppOfArity `Core.ObeysPureEqUpToErrMsg2 9 then
            let a := ab.getAppArgs; some (#[a[0]!, a[1]!], a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, a[8]!)
          else if ab.isAppOfArity `Core.ObeysPureEqUpToErrMsg3 10 then
            let a := ab.getAppArgs; some (#[a[0]!, a[1]!, a[2]!], a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, a[8]!, a[9]!)
          else if ab.isAppOfArity `Core.ObeysPureEqUpToErrMsg4 11 then
            let a := ab.getAppArgs; some (#[a[0]!, a[1]!, a[2]!, a[3]!], a[4]!, a[5]!, a[6]!, a[7]!, a[8]!, a[9]!, a[10]!)
          else none

        if let some (inTys, errTy, kindTy, _okTy, kindArg, msgArg, implArg, modelArg) := pureErrMsgInfo? then
          let some kindFn ← checkBareConstArg env allowedAtomFVs false kindArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare kindOf argument in {thmName}"]
          let some msgFn ← checkBareConstArg env allowedAtomFVs false msgArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare msgOf argument in {thmName}"]
          let some implFn ← checkBareConstArg env allowedAtomFVs false implArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare impl argument in {thmName}"]
          let some modelFn ← checkBareConstArg env allowedAtomFVs false modelArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare model argument in {thmName}"]
          if isPrivateName implFn || moduleOfConst env implFn != ifaceMod then
            aErrs := aErrs.push s!"NON_INTERFACE_IMPL_IN_REFINES: {implFn} in {thmName} is not a public constant in {ifaceMod}"
          if isPrivateName modelFn || !modelMods.contains (moduleOfConst env modelFn) then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {modelFn} in {thmName} is not a public constant in {pkg}.Model"
          if !isAllowedErrorExtractorConst env pkg modelMods kindFn then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {kindFn} in {thmName} must be a public Types/Model constant"
          if !isAllowedErrorExtractorConst env pkg modelMods msgFn then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {msgFn} in {thmName} must be a public Types/Model constant"
          for mFn in #[kindFn, msgFn, modelFn] do
            if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef mFn then
              aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mFn} in {thmName} transitively references Interface/Impl"
          let inTysSubst := inTys.map (fun t => applySubst (stripOptParamType t))
          let errTySubst := applySubst (stripOptParamType errTy)
          let kindTySubst := applySubst (stripOptParamType kindTy)
          for inTyS in inTysSubst do
            if !(← isProvablyInhabitedDataType env 8 inTyS) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited input domain for {implFn} in {thmName}"
          if !(← isProvablyInhabitedDataType env 8 errTySubst) then
            aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited error domain for {implFn} in {thmName}"
          match ← isTrivialPayloadType kindTySubst with
          | .isTrue =>
            aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: trivial error-kind codomain for {implFn} in {thmName}"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {kindFn} for {implFn} in {thmName} ({reason})"
          | .isFalse =>
            let kindSubst := applySubst kindArg
            match ← checkFnNotConstantOnType env relaxedEnv errTySubst (fun e => (mkApp kindSubst e).headBeta) with
            | .isTrue => pure ()
            | .isFalse =>
              aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {kindFn} for {implFn} in {thmName} is constant on errors"
            | .inconclusive reason =>
              aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {kindFn} for {implFn} in {thmName} ({reason})"
          let msgSubst := applySubst msgArg
          match ← checkFnNotConstantOnType env relaxedEnv errTySubst (fun e => (mkApp msgSubst e).headBeta) with
          | .isTrue => pure ()
          | .isFalse =>
            aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {msgFn} for {implFn} in {thmName} is constant on errors"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {msgFn} for {implFn} in {thmName} ({reason})"
          if aErrs.isEmpty then
            coveredPureOpsRef.modify (·.insert implFn)
          return aErrs

        if ab.isAppOfArity `Core.ObeysInverseRender 9 || ab.isAppOfArity `Core.ObeysInverseRenderWithin 10 then
          let hasWithin := ab.isAppOfArity `Core.ObeysInverseRenderWithin 10
          let a := ab.getAppArgs
          let (objTy, tapeTy, rawTy, errTy) := (a[0]!, a[1]!, a[2]!, a[3]!)
          let parseArg := a[4]!
          let renderArg := a[5]!
          let withinArg? := if hasWithin then some a[6]! else none
          let (wfArg, equivArg, msgArg) := if hasWithin then (a[7]!, a[8]!, a[9]!) else (a[6]!, a[7]!, a[8]!)
          let some parseFn ← checkBareConstArg env allowedAtomFVs false parseArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare parse argument in {thmName}"]
          let some renderFn ← checkBareConstArg env allowedAtomFVs false renderArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare render argument in {thmName}"]
          let mut withinFn? : Option Name := none
          if let some withinArg := withinArg? then
            let some wfn ← checkBareConstArg env allowedAtomFVs false withinArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare withinLimits argument in {thmName}"]
            withinFn? := some wfn
          let some wfFn ← checkBareConstArg env allowedAtomFVs false wfArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare wf argument in {thmName}"]
          let some equivFn ←
            if equivArg.consumeMData.isAppOfArity ``Eq 1 then pure (some ``Eq)
            else checkBareConstArg env allowedAtomFVs false equivArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare equiv argument in {thmName}"]
          let some msgFn ← checkBareConstArg env allowedAtomFVs false msgArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare msgOf argument in {thmName}"]
          if isPrivateName parseFn || moduleOfConst env parseFn != ifaceMod then
            aErrs := aErrs.push s!"NON_INTERFACE_IMPL_IN_REFINES: {parseFn} in {thmName} is not a public constant in {ifaceMod}"
          let mut modelReqFns := #[renderFn, wfFn]
          if let some wfn := withinFn? then modelReqFns := modelReqFns.push wfn
          for mFn in modelReqFns do
            if isPrivateName mFn || !modelMods.contains (moduleOfConst env mFn) then
              aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {mFn} in {thmName} is not a public constant in {pkg}.Model"
          if equivFn != ``Eq && (isPrivateName equivFn || !modelMods.contains (moduleOfConst env equivFn)) then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {equivFn} in {thmName} must be Eq or a public constant in {pkg}.Model"
          if !isAllowedErrorExtractorConst env pkg modelMods msgFn then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {msgFn} in {thmName} must be a public Types/Model constant"
          for mFn in modelReqFns ++ #[equivFn, msgFn] do
            if mFn != ``Eq && (← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef mFn) then
              aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mFn} in {thmName} transitively references Interface/Impl"
          let objTyS := applySubst (stripOptParamType objTy)
          let tapeTyS := applySubst (stripOptParamType tapeTy)
          let rawTyS := applySubst (stripOptParamType rawTy)
          let errTyS := applySubst (stripOptParamType errTy)
          for dTy in #[objTyS, tapeTyS, rawTyS, errTyS] do
            if !(← isProvablyInhabitedDataType env 8 dTy) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited domain in ObeysInverseRender for {parseFn} in {thmName}"
          if let (some withinArg, some withinFn) := (withinArg?, withinFn?) then
            let withinSubst := applySubst withinArg
            let withinCheck ← withLocalDeclD `_invTape tapeTyS fun t => isStaticFalseProp (mkApp withinSubst t)
            match withinCheck with
            | .isFalse => pure ()
            | .isTrue =>
              aErrs := aErrs.push s!"VACUOUS_WITHIN_LIMITS_IN_REFINES: {withinFn} in {thmName} is identically false"
            | .inconclusive reason =>
              aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {withinFn} in {thmName} ({reason})"
          let wfSubst := applySubst wfArg
          let wfCheck ← withLocalDeclD `_invObj objTyS fun o => isStaticFalseProp (mkApp wfSubst o)
          match wfCheck with
          | .isFalse => pure ()
          | .isTrue =>
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {wfFn} in {thmName} is identically false"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {wfFn} in {thmName} ({reason})"
          let renderSubst := applySubst renderArg
          match ← checkRenderNotConstantOnObj env relaxedEnv objTyS tapeTyS renderSubst with
          | .isTrue => pure ()
          | .isFalse =>
            aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {renderFn} for {parseFn} in {thmName} is object-insensitive"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {renderFn} for {parseFn} in {thmName} ({reason})"
          let msgSubst := applySubst msgArg
          match ← checkFnNotConstantOnType env relaxedEnv errTyS (fun e => (mkApp msgSubst e).headBeta) with
          | .isTrue => pure ()
          | .isFalse =>
            aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {msgFn} for {parseFn} in {thmName} is constant on errors"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {msgFn} for {parseFn} in {thmName} ({reason})"
          if aErrs.isEmpty then
            coveredPureOpsRef.modify (·.insert parseFn)
          return aErrs

        let stepInfo? : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
          if ab.isAppOfArity `Core.RefinesStep 8 || ab.isAppOfArity `Core.ObeysStep 8 then
            let args := ab.getAppArgs
            some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!)
          else if ab.isAppOfArity `Core.RefinesStepId 6 || ab.isAppOfArity `Core.ObeysStepId 6 then
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
          match ← checkWfNotVacuous env sTy wfFn with
          | .isTrue => pure ()
          | .isFalse =>
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {wfFn} in {thmName} is identically false or refutable"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {wfFn} in {thmName} ({reason})"
          match ← checkStepAllowedNonTrivial env relaxedEnv modelMods allowedArg allowedFn sTy reqTy outTy with
          | .isTrue => pure ()
          | .isFalse =>
            aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {allowedFn} in {thmName} is output/state-insensitive or tautological"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {allowedFn} in {thmName} ({reason})"
          if aErrs.isEmpty then
            if stepMod == ifaceMod then
              coveredStepOpsRef.modify (·.insert stepFn)
            else if stepMod == implMod then
              coveredImplHelpersRef.modify (·.insert stepFn)
          return aErrs

        let stepFromInfo? : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Array (Expr × Expr × Expr × Expr)) :=
          if ab.isAppOfArity `Core.RefinesStepFrom 16 ||
              ab.isAppOfArity `Core.RefinesStepFromFinally 16 ||
              ab.isAppOfArity `Core.ObeysStepFrom 16 ||
              ab.isAppOfArity `Core.ObeysStepFromFinally 16 then
            let args := ab.getAppArgs
            some (args[0]!, args[1]!, args[6]!, args[7]!, args[8]!, args[9]!, args[12]!, args[13]!, args[14]!,
              #[(args[4]!, args[5]!, args[10]!, args[11]!), (args[6]!, args[7]!, args[14]!, args[15]!)])
          else if ab.isAppOfArity `Core.RefinesStepFrom2 21 ||
              ab.isAppOfArity `Core.ObeysStepFrom2 21 then
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
          let some mkApiFn ← checkBareConstArg env {} false mkApiArg (allowImplicitGroundTypeOnMk := true)
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
          match ← checkWfNotVacuous env rawSTy rawWfFn with
          | .isTrue => pure ()
          | .isFalse =>
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {rawWfFn} in {thmName} is identically false or refutable"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {rawWfFn} in {thmName} ({reason})"
          match ← checkWfNotVacuous env pkgSTy pkgWfFn with
          | .isTrue => pure ()
          | .isFalse =>
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {pkgWfFn} in {thmName} is identically false or refutable"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {pkgWfFn} in {thmName} ({reason})"
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
            match ← checkStepAllowedNonTrivial env relaxedEnv modelMods legAllowedArg legAllowedFn legSTy legReqTy legOutTy with
            | .isTrue => pure ()
            | .isFalse =>
              aErrs := aErrs.push s!"TRIVIAL_ALLOWED_IN_REFINES: {legAllowedFn} in {thmName} is output/state-insensitive or tautological"
            | .inconclusive reason =>
              aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {legAllowedFn} in {thmName} ({reason})"
          if aErrs.isEmpty then
            let isDirectIfaceComb :=
              mkApiMod == ifaceMod && !isPrivateName mkApiFn &&
              !(mkApiFn.isStr && mkApiFn.getString!.startsWith "mk")
            if isDirectIfaceComb then
              if !(← execPkgInvokesApiParam env execPkgFn) then
                aErrs := aErrs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: {execPkgFn} in {thmName} must directly invoke {mkApiFn} on request projections"
              else
                coveredStepOpsRef.modify (·.insert mkApiFn)
            else
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
          Std.HashSet.emptyWithCapacity 4
            |>.insert (Name.str pkg "defaultApi")
            |>.insert (Name.str pkg "defaultOps")
            |>.insert (Name.str pkg "defaultOpsBase")
            |>.insert (Name.str pkg "defaultRawOps")
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
  coverageLogPath? : Option System.FilePath := none
  coverageNonce? : Option String := none
  strictCentralCoverage : Bool := false
  printSigPkg? : Option Name := none
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
    | "--coverage-log" :: lp :: rest => go { cfg with coverageLogPath? := some ⟨lp⟩ } pos rest
    | ["--coverage-log"] => { cfg with argError? := some "MISSING_COVERAGE_LOG_VALUE: --coverage-log requires a path" }
    | "--coverage-nonce" :: nc :: rest => go { cfg with coverageNonce? := some nc } pos rest
    | ["--coverage-nonce"] => { cfg with argError? := some "MISSING_COVERAGE_NONCE_VALUE: --coverage-nonce requires a non-empty argument" }
    | "--strict-central-coverage" :: rest => go { cfg with strictCentralCoverage := true } pos rest
    | "--print-sig" :: pkgStr :: rest => go { cfg with printSigPkg? := some pkgStr.toName } pos rest
    | ["--print-sig"] => { cfg with argError? := some "MISSING_PRINT_SIG_VALUE: --print-sig requires a package name" }
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

private structure CoverageOverrideEntry where
  op : String
  kind : String
  mode : String
  testSymbol : String
  reason : String

private structure ExternalAssumptionEntry where
  id : String
  package : String
  whyUnfuzzable : String
  formalPred? : Option String

private structure CoverageLogData where
  errHits : Std.HashMap (String × String) (Std.HashSet String) := {}
  fuzzEquiv : Array (String × String × Nat × Nat × Nat × Bool) := #[]
  badLines : Nat := 0
  sawInit : Bool := false
  sawClose : Bool := false

private def parsePackagePurityMap (repoDir : System.FilePath) :
    IO (Except String (Bool × Std.HashMap Name String)) := do
  let manifestPath := repoDir / "scripts" / "package_manifest.json"
  if !(← manifestPath.pathExists) then
    return .ok (false, {})
  let raw ← IO.FS.readFile manifestPath
  match Lean.Json.parse raw with
  | .error err => return .error s!"MALFORMED_PACKAGE_MANIFEST: {err}"
  | .ok j =>
    let .ok (.obj pkgs) := j.getObjVal? "packages"
      | return .error "MALFORMED_PACKAGE_MANIFEST: missing 'packages' object"
    let mut out : Std.HashMap Name String := {}
    for (pkgStr, entry) in pkgs do
      if let .ok pStr := entry.getObjValAs? String "purity" then
        out := out.insert pkgStr.toName pStr
    return .ok (true, out)

private def isPurePackage (env : Environment) (knownPkgs : Array Name)
    (purityMap : Std.HashMap Name String) (pkg : Name) : Bool :=
  match purityMap.get? pkg with
  | some p => p == "pure"
  | none => !isExternalBoundaryPkg env knownPkgs pkg

private def parseCoverageOverridesJson (repoDir : System.FilePath) (requireFile : Bool) :
    IO (Except String (Array CoverageOverrideEntry)) := do
  let path := repoDir / "scripts" / "coverage_overrides.json"
  if !(← path.pathExists) then
    if requireFile then
      return .error s!"MISSING_COVERAGE_OVERRIDES: missing {path}"
    return .ok #[]
  let raw ← IO.FS.readFile path
  let j ← match Lean.Json.parse raw with
    | .ok v => pure v
    | .error err => return .error s!"MALFORMED_COVERAGE_OVERRIDES: {err}"
  let .obj rootMap := j
    | return .error "MALFORMED_COVERAGE_OVERRIDES: root must be JSON object"
  for (k, _) in rootMap do
    if k != "version" && k != "overrides" then
      return .error s!"MALFORMED_COVERAGE_OVERRIDES: unknown root key '{k}'"
  match j.getObjValAs? Nat "version" with
  | .ok 1 => pure ()
  | _ => return .error "MALFORMED_COVERAGE_OVERRIDES: 'version' must be 1"
  let .ok (.arr arr) := j.getObjVal? "overrides"
    | return .error "MALFORMED_COVERAGE_OVERRIDES: 'overrides' must be a JSON array"
  let mut out : Array CoverageOverrideEntry := #[]
  for item in arr do
    let .obj kvs := item
      | return .error "MALFORMED_COVERAGE_OVERRIDES: each override entry must be a JSON object"
    for (k, _) in kvs do
      if k != "op" && k != "kind" && k != "mode" && k != "test_symbol" && k != "reason" then
        return .error s!"MALFORMED_COVERAGE_OVERRIDES: unknown override field '{k}'"
    let .ok op := item.getObjValAs? String "op"
      | return .error "MALFORMED_COVERAGE_OVERRIDES: override missing string 'op'"
    let .ok kind := item.getObjValAs? String "kind"
      | return .error "MALFORMED_COVERAGE_OVERRIDES: override missing string 'kind'"
    let .ok mode := item.getObjValAs? String "mode"
      | return .error "MALFORMED_COVERAGE_OVERRIDES: override missing string 'mode'"
    let .ok reason := item.getObjValAs? String "reason"
      | return .error "MALFORMED_COVERAGE_OVERRIDES: override missing string 'reason'"
    let testSymbol ← match item.getObjVal? "test_symbol" with
      | .ok (.str s) => pure s
      | .ok .null => pure ""
      | .error _ => pure ""
      | .ok _ => return .error "MALFORMED_COVERAGE_OVERRIDES: 'test_symbol' must be string or null"
    if op.trimAscii.toString.isEmpty || kind.trimAscii.toString.isEmpty || reason.trimAscii.toString.isEmpty then
      return .error "MALFORMED_COVERAGE_OVERRIDES: 'op', 'kind', and 'reason' must be non-empty"
    if mode != "mocked" && mode != "untriggerable" then
      return .error s!"INVALID_COVERAGE_OVERRIDE_MODE: '{mode}' for ({op}, {kind}) (expected 'mocked' or 'untriggerable')"
    out := out.push { op, kind, mode, testSymbol, reason }
  return .ok out

private def parseExternalAssumptionsJson (repoDir : System.FilePath) (requireFile : Bool) :
    IO (Except String (Array ExternalAssumptionEntry)) := do
  let path := repoDir / "scripts" / "external_assumptions.json"
  if !(← path.pathExists) then
    if requireFile then
      return .error s!"MISSING_EXTERNAL_ASSUMPTIONS_JSON: missing {path}"
    return .ok #[]
  let raw ← IO.FS.readFile path
  let j ← match Lean.Json.parse raw with
    | .ok v => pure v
    | .error err => return .error s!"MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: {err}"
  let .obj rootMap := j
    | return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: root must be JSON object"
  for (k, _) in rootMap do
    if k != "version" && k != "assumptions" then
      return .error s!"MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: unknown root key '{k}'"
  match j.getObjValAs? Nat "version" with
  | .ok 1 => pure ()
  | _ => return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: 'version' must be 1"
  let .ok (.arr arr) := j.getObjVal? "assumptions"
    | return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: 'assumptions' must be a JSON array"
  let mut out : Array ExternalAssumptionEntry := #[]
  for item in arr do
    let .obj kvs := item
      | return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: each entry must be a JSON object"
    for (k, _) in kvs do
      if k != "id" && k != "package" && k != "why_unfuzzable" && k != "formal_pred" then
        return .error s!"MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: unknown entry field '{k}'"
    let .ok id := item.getObjValAs? String "id"
      | return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: entry missing string 'id'"
    let .ok pkg := item.getObjValAs? String "package"
      | return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: entry missing string 'package'"
    let .ok why := item.getObjValAs? String "why_unfuzzable"
      | return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: entry missing string 'why_unfuzzable'"
    let fp? ← match item.getObjVal? "formal_pred" with
      | .ok (.str s) =>
        if s.trimAscii.toString.isEmpty then
          return .error s!"MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: empty 'formal_pred' in '{id}'"
        pure (some s)
      | .ok .null => pure none
      | .error _ => pure none
      | .ok _ => return .error s!"MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: 'formal_pred' must be string or null in '{id}'"
    if id.trimAscii.toString.isEmpty || pkg.trimAscii.toString.isEmpty || why.trimAscii.toString.isEmpty then
      return .error "MALFORMED_EXTERNAL_ASSUMPTIONS_JSON: 'id', 'package', and 'why_unfuzzable' must be non-empty"
    out := out.push { id, package := pkg, whyUnfuzzable := why, formalPred? := fp? }
  return .ok out

private def parseCoverageLogFile (logPath : System.FilePath) (expectedNonce : String) :
    IO CoverageLogData := do
  let txt ← IO.FS.readFile logPath
  let mut errHits : Std.HashMap (String × String) (Std.HashSet String) := {}
  let mut fuzzEquiv : Array (String × String × Nat × Nat × Nat × Bool) := #[]
  let mut badLines : Nat := 0
  let mut sawInit := false
  let mut sawClose := false
  for line in txt.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    let parts := trimmed.splitOn "|"
    match parts with
    | [nonce, "LOG_INIT"] =>
      if nonce == expectedNonce then sawInit := true else badLines := badLines + 1
    | [nonce, "LOG_CLOSE"] =>
      if nonce == expectedNonce then sawClose := true else badLines := badLines + 1
    | [nonce, "ERR_HIT", qualOp, kindCtor, mode] =>
      let validMode := mode == "real" || mode == "fault_injected" || mode == "mocked"
      if nonce == expectedNonce && !qualOp.isEmpty && !kindCtor.isEmpty && validMode then
        let key := (qualOp, kindCtor)
        let prev := errHits.getD key {}
        errHits := errHits.insert key (prev.insert mode)
      else
        badLines := badLines + 1
    | [nonce, "FUZZ_EQUIV", pkg, suite, stepsStr, bucketsStr, okField] =>
      let okVal? : Option Bool :=
        if okField == "ok=true" then some true
        else if okField == "ok=false" then some false
        else none
      let bucketPair? : Option (Nat × Nat) :=
        match bucketsStr.splitOn "/" with
        | [hStr, tStr] =>
          match hStr.toNat?, tStr.toNat? with
          | some h, some t => if h <= t then some (h, t) else none
          | _, _ => none
        | _ => none
      match stepsStr.toNat?, bucketPair?, okVal? with
      | some steps, some (hit, total), some okVal =>
        if nonce == expectedNonce && !pkg.isEmpty && !suite.isEmpty then
          fuzzEquiv := fuzzEquiv.push (pkg, suite, steps, hit, total, okVal)
        else
          badLines := badLines + 1
      | _, _, _ =>
        badLines := badLines + 1
    | _ =>
      badLines := badLines + 1
  return { errHits, fuzzEquiv, badLines, sawInit, sawClose }

private partial def extractFallibleErrorType? (ty : Expr) : MetaM (Option Name) := do
  let rec go (e : Expr) : MetaM (Option Name) := do
    let e := e.consumeMData
    if e.isAppOfArity ``Except 2 then
      return e.appFn!.appArg!.consumeMData.getAppFn.consumeMData.constName?
    if e.isAppOfArity ``ExceptT 3 then
      return (e.getArg! 0).consumeMData.getAppFn.consumeMData.constName?
    if e.isAppOfArity ``IO 1 || e.isAppOfArity ``BaseIO 1 then
      return ← go e.appArg!
    if e.isAppOfArity ``EIO 2 || e.isAppOfArity ``EST 3 || e.isAppOfArity ``EST.Out 3 then
      return ← go e.appArg!
    if e.isForall then
      return ← forallTelescope e fun _ inner => go inner
    let e' ← whnf e
    if e' != e then
      return ← go e'
    return none
  go ty

private def findPkgErrorKindEnum? (env : Environment) (pkg : Name) : Option Name := Id.run do
  let typesMod := Name.str pkg "Types"
  let mut found : Array Name := #[]
  if let some idx := env.header.moduleNames.findIdx? (· == typesMod) then
    if let some md := env.header.moduleData[idx]? then
      for c in md.constants do
        if let .inductInfo ind := c then
          if !isPrivateName ind.name && !isCompilerAux ind.name &&
              ind.name.isStr && ind.name.getString!.endsWith "ErrorKind" then
            found := found.push ind.name
  if found.size == 1 then some found[0]!
  else none

private def isNullaryEnumInductive (env : Environment) (ind : InductiveVal) : Bool :=
  !ind.ctors.isEmpty && ind.numParams == 0 && ind.numIndices == 0 &&
    ind.ctors.all fun cn =>
      match env.find? cn with
      | some (.ctorInfo ci) => ci.numFields == 0
      | _ => false

private def resolveErrorKindEnum? (env : Environment) (pkg errTypeName : Name)
    (legacyEnum? : Option Name := none) : MetaM (Option Name) := do
  if Lean.isStructure env errTypeName then
    let kindProj := Name.str errTypeName "kind"
    if env.isProjectionFn kindProj then
      if let some cinfo := env.find? kindProj then
        let kName? ← forallTelescopeReducing cinfo.type fun _ ret => do
          let rw := (← whnf ret).consumeMData
          return rw.getAppFn.consumeMData.constName?
        if let some kName := kName? then
          if let some (.inductInfo _) := env.find? kName then
            return some kName
  if errTypeName == `LeanSwe.LinuxSyscall.Errno then
    if let some pk := findPkgErrorKindEnum? env pkg then
      return some pk
  if errTypeName.isStr then
    let cand := Name.str errTypeName.getPrefix (errTypeName.getString! ++ "Kind")
    if let some (.inductInfo _) := env.find? cand then
      return some cand
  if let some pk := findPkgErrorKindEnum? env pkg then
    return some pk
  if let some (.inductInfo ind) := env.find? errTypeName then
    if isNullaryEnumInductive env ind then
      return some errTypeName
  return legacyEnum?

private def discoverProvedImpossibleCells
    (env : Environment)
    (knownPkgs : Array Name)
    (axCacheIn : AxCache) : MetaM (Std.HashMap (String × String) Name × Array String × AxCache) := do
  let mut cells : Std.HashMap (String × String) Name := {}
  let mut errs : Array String := #[]
  let mut axCache := axCacheIn
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if !isProjectModule m || !isProofsModule m then continue
    let some data := env.header.moduleData[i]? | continue
    let pkg := pkgNamespaceOfSpecWith knownPkgs m
    let ifaceMod := Name.str pkg "Interface"
    let implMod := Name.str pkg "Impl"
    for c in data.constants do
      let .thmInfo tv := c | continue
      if isPrivateName c.name || isCompilerAux c.name || env.isProjectionFn c.name then continue
      let usedTy := tv.type.getUsedConstants
      let hasNever := usedTy.any fun u =>
        u == `Core.NeverErrorKindIO || u == `Core.NeverErrorKindBaseIO || u == `Core.NeverErrorKindPure
      if !hasNever then continue
      let matched? ← forallTelescope tv.type fun xs concl => do
        for x in xs do
          if ← isProp (← inferType x) then return none
        let cc := concl.consumeMData
        let info? : Option (Expr × Expr × Expr × Expr × Expr × Bool × Option Expr) :=
          if cc.isAppOfArity `Core.NeverErrorKindIO 7 || cc.isAppOfArity `Core.NeverErrorKindBaseIO 7 then
            let a := cc.getAppArgs
            some (a[0]!, a[1]!, a[3]!, a[4]!, a[5]!, true, some a[6]!)
          else if cc.isAppOfArity `Core.NeverErrorKindPure 6 then
            let a := cc.getAppArgs
            some (a[0]!, a[1]!, a[3]!, a[4]!, a[5]!, false, none)
          else none
        let some (errTy, enumTy, kindFn, forbidden, actExpr, isIo, wExpr?) := info? | return none
        let some errTypeName := errTy.consumeMData.getAppFn.consumeMData.constName? | return none
        let some enumName := enumTy.consumeMData.getAppFn.consumeMData.constName? | return none
        let some (.inductInfo enumInd) := env.find? enumName | return none
        let some kindCtor := forbidden.consumeMData.constName? | return none
        if !enumInd.ctors.contains kindCtor then return none
        unless ← checkKindExtractorValid env errTypeName enumName kindFn do return none
        let neededFVs : Array FVarId ←
          if isIo then
            match wExpr? with
            | some wE =>
              let wc := wE.consumeMData
              if xs.size == 0 || !wc.isFVar || wc.fvarId! != xs.back!.fvarId! then return none
              pure #[xs.back!.fvarId!]
            | none => return none
          else
            pure #[]
        let actClean := actExpr.consumeMData
        let some opName := actClean.getAppFn.consumeMData.constName? | return none
        if isPrivateName opName || isCompilerAux opName then return none
        let opMod := moduleOfConst env opName
        if opMod != ifaceMod && !(opMod == implMod && opName.getPrefix == pkg) then return none
        let appArgs := actClean.getAppArgs
        let fvs := appArgs.filterMap fun a => if a.consumeMData.isFVar then some a.consumeMData.fvarId! else none
        if fvs.size != appArgs.size then return none
        let initSet := neededFVs.foldl (fun (s : Std.HashSet FVarId) fv => s.insert fv) {}
        let distinct := fvs.foldl (fun (s : Std.HashSet FVarId) fv => s.insert fv) initSet
        if distinct.size != fvs.size + neededFVs.size then return none
        return some (opName.toString, kindCtor.toString)
      if let some cell := matched? then
        let (badAx?, axCache') ← checkAxiomsOk axCache c.name
        axCache := axCache'
        if let some badAx := badAx? then
          errs := errs.push s!"UNALLOWED_AXIOM_IN_THEOREM: {c.name} uses [{badAx}]"
        else
          cells := cells.insert cell c.name
  return (cells, errs, axCache)

private def renderExpectedObeysSig (env : Environment) (knownPkgs : Array Name) (rawPkg : Name) :
    MetaM (Except String String) := do
  let leanSweCand := ("LeanSwe." ++ rawPkg.toString).toName
  let pkg :=
    if env.header.moduleNames.contains (Name.str rawPkg "Interface") then rawPkg
    else if rawPkg.getRoot != `LeanSwe &&
        env.header.moduleNames.contains (Name.str leanSweCand "Interface") then
      leanSweCand
    else rawPkg
  let ifaceMod := Name.str pkg "Interface"
  let some ifaceIdx := env.header.moduleNames.findIdx? (· == ifaceMod)
    | return .error s!"UNKNOWN_PACKAGE_FOR_PRINT_SIG: {rawPkg} has no imported module {ifaceMod}"
  let some ifaceData := env.header.moduleData[ifaceIdx]?
    | return .error s!"UNKNOWN_PACKAGE_FOR_PRINT_SIG: missing module data for {ifaceMod}"
  let mut pureOps : Array (Name × Expr) := #[]
  let mut effOps : Array Name := #[]
  for c in ifaceData.constants do
    let .defnInfo _ := c | continue
    if isPrivateName c.name || isCompilerAux c.name || env.isProjectionFn c.name then continue
    if (← Meta.isInstance c.name) || (← isClassInstanceOrAux env c.name c.type) then continue
    if ← isCapabilityBundleConst env knownPkgs pkg c.name c.type then continue
    if ← isEffectfulInterfaceOp env c.type c.name then
      effOps := effOps.push c.name
    else
      pureOps := pureOps.push (c.name, c.type)
  pureOps := pureOps.qsort (fun a b => a.1.toString < b.1.toString)
  effOps := effOps.qsort (fun a b => a.toString < b.toString)
  let modelMod := Name.str pkg "Model"
  let mut conjuncts : Array String := #[]
  for (opName, opTy) in pureOps do
    let short := opName.getString!
    let modelCand1 := Name.str modelMod short
    let modelCand2 := Name.str modelMod (short ++ "Model")
    let modelStr :=
      if env.contains modelCand1 then s!"Model.{short}"
      else if env.contains modelCand2 then s!"Model.{short}Model"
      else s!"<MODEL_FN_FOR_{short}>"
    let (explicitCount, hasPoly, exceptErrTy?) ← forallTelescope opTy fun xs ret => do
      let mut expN := 0
      let mut poly := false
      for x in xs do
        let bi ← x.fvarId!.getBinderInfo
        if bi == .default then expN := expN + 1
        else poly := true
      let retW := (← whnf ret).consumeMData
      let errTy? := if retW.isAppOfArity ``Except 2 then some retW.appFn!.appArg! else none
      return (expN, poly, errTy?)
    let line :=
      if hasPoly then
        s!"<MANUAL_TEMPLATE_POLY: {opName} (bind type/class params per conjunct; arity={explicitCount}, model={modelStr})>"
      else if explicitCount == 0 || explicitCount > 4 then
        s!"<MANUAL_TEMPLATE_ARITY_{explicitCount}: {opName} (Core.ObeysPure* supports arities 1..4; model={modelStr})>"
      else
        match exceptErrTy? with
        | some errTy =>
          let pred := match explicitCount with
            | 1 => "Core.ObeysPureEqUpToErrMsg"
            | 2 => "Core.ObeysPureEqUpToErrMsg2"
            | 3 => "Core.ObeysPureEqUpToErrMsg3"
            | _ => "Core.ObeysPureEqUpToErrMsg4"
          let (kindStr, msgStr) :=
            match errTy.consumeMData.getAppFn.consumeMData with
            | .const stName _ =>
              if Lean.isStructure env stName then
                let flds := Lean.getStructureFields env stName
                let k := if flds.contains `kind then s!"{stName}.kind" else "<ERR_KIND_OF>"
                let m :=
                  if flds.contains `msg then s!"{stName}.msg"
                  else if flds.contains `message then s!"{stName}.message"
                  else "<ERR_MSG_OF>"
                (k, m)
              else ("<ERR_KIND_OF>", "<ERR_MSG_OF>")
            | _ => ("<ERR_KIND_OF>", "<ERR_MSG_OF>")
          s!"{pred} {kindStr} {msgStr} {opName} {modelStr}"
        | none =>
          let pred := match explicitCount with
            | 1 => "Core.ObeysPureEq"
            | 2 => "Core.ObeysPureEq2"
            | 3 => "Core.ObeysPureEq3"
            | _ => "Core.ObeysPureEq4"
          s!"{pred} {opName} {modelStr}"
    conjuncts := conjuncts.push line
  if !effOps.isEmpty then
    let mkApiCand := Name.str (Name.str pkg "Internal") "mkApiM"
    let (stepPred, builderStr) :=
      match env.find? mkApiCand with
      | some ci =>
        let pred :=
          if ci.type.getUsedConstants.contains ``MonadFinally then "Core.ObeysStepFromFinally"
          else "Core.ObeysStepFrom"
        (pred, mkApiCand.toString)
      | none => ("Core.ObeysStepFrom", "<MK_API_M>")
    conjuncts := conjuncts.push
      s!"{stepPred} <MAP_S> <RAW_WF> <EXEC_RAW> <RAW_ALLOWED> <PKG_WF> {builderStr} <EXEC_PKG> <PKG_ALLOWED>"
  if conjuncts.isEmpty then
    return .error s!"EMPTY_INTERFACE_FOR_PRINT_SIG: {ifaceMod} exposes zero public operations"
  let body := String.intercalate " ∧\n    " conjuncts.toList
  let header := s!"Template for {pkg}.Proofs.obeys_model (starting skeleton; replace any <...> placeholders before compiling):"
  return .ok s!"{header}\nnamespace {pkg}.Proofs\n\ntheorem obeys_model :\n    {body}\n\nend {pkg}.Proofs"

/-- Audit compiled `.olean` artifacts for hardened checkable assumptions, error coverage, and `Core.Obeys` / `Core.Refines`. -/
unsafe def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args
  if let some err := cfg.argError? then
    IO.eprintln err
    return 1
  if cfg.nonce? == some "" then
    IO.eprintln "EMPTY_NONCE_FORBIDDEN: --nonce must be non-empty"
    return 1
  if cfg.coverageNonce? == some "" then
    IO.eprintln "EMPTY_COVERAGE_NONCE_FORBIDDEN: --coverage-nonce must be non-empty"
    return 1
  let effectiveCovNonce? := cfg.coverageNonce?.orElse (fun _ => cfg.nonce?)
  if cfg.coverageLogPath?.isSome && effectiveCovNonce?.isNone then
    IO.eprintln "MISSING_COVERAGE_NONCE: --coverage-log requires --coverage-nonce or --nonce"
    return 1
  let libDir := cfg.libDir
  let repoDir := cfg.repoDir
  unless ← (libDir / "LeanSwe.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe ({libDir / "LeanSwe.olean"})"
    return 1
  let leanSweDir := repoDir / "LeanSwe"
  unless ← leanSweDir.pathExists do
    IO.eprintln s!"MISSING_SOURCE_DIR: {leanSweDir}"
    return 1
  let harnessLibDir := repoDir / "harness" / ".lake" / "build" / "lib" / "lean"
  let hasTestsMainOlean ← (harnessLibDir / "Tests" / "Main.olean").pathExists
  let hasPostForkVerifiedSrc ← (leanSweDir / "PostFork" / "Verified.lean").pathExists
  if hasPostForkVerifiedSrc then
    unless ← (libDir / "LeanSwe" / "PostFork" / "Verified.olean").pathExists do
      IO.eprintln s!"MISSING_OLEAN: LeanSwe.PostFork.Verified ({libDir / "LeanSwe" / "PostFork" / "Verified.olean"})"
      return 1
  let hasInitVerifiedSrc ← (leanSweDir / "ProcessSandbox" / "Init" / "Verified.lean").pathExists
  if hasInitVerifiedSrc then
    unless ← (libDir / "LeanSwe" / "ProcessSandbox" / "Init" / "Verified.olean").pathExists do
      IO.eprintln s!"MISSING_OLEAN: LeanSwe.ProcessSandbox.Init.Verified ({libDir / "LeanSwe" / "ProcessSandbox" / "Init" / "Verified.olean"})"
      return 1
  Lean.enableInitializersExecution
  let searchDirs := if hasTestsMainOlean then [harnessLibDir, libDir] else [libDir]
  initSearchPath (← findSysroot) searchDirs
  let mut rootImports : Array Import := #[{ module := `LeanSwe }]
  if hasTestsMainOlean then
    rootImports := rootImports.push { module := `Tests.Main }
  if hasPostForkVerifiedSrc then
    rootImports := rootImports.push { module := `LeanSwe.PostFork.Verified }
  if hasInitVerifiedSrc then
    rootImports := rootImports.push { module := `LeanSwe.ProcessSandbox.Init.Verified }
  let env ← importModules rootImports {} (loadExts := true)
  let transImpsOf := buildTransitiveImportFn env

  let mut visited : Std.HashSet Name := {}
  let mut knownPkgs : Array Name := #[]
  for modName in env.header.moduleNames do
    if isProjectModule modName then
      visited := visited.insert modName
      if let .str p "SpecTests" := modName then
        knownPkgs := knownPkgs.push p

  if let some targetPkg := cfg.printSigPkg? then
    let ctx : Core.Context := { fileName := "<CheckAssumptions>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
    let state : Core.State := { env }
    let (res, _) ← (Meta.MetaM.run' (renderExpectedObeysSig env knownPkgs targetPkg)).toIO ctx state
    match res with
    | .ok sigText =>
      IO.println sigText
      return 0
    | .error err =>
      IO.eprintln err
      return 1

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
    IO.eprintln s!"MISSING_OLEAN: Tests.Main ({harnessLibDir / "Tests" / "Main.olean"})"
    return 1

  let fuzzCoveredPkgs ← match ← parseFuzzCoveredPackages repoDir knownPkgs with
    | .ok s => pure s
    | .error err =>
      errors := errors.push err
      pure ({} : Std.HashSet Name)

  let (hasPkgManifest, purityMap) ← match ← parsePackagePurityMap repoDir with
    | .ok res => pure res
    | .error err =>
      errors := errors.push err
      pure (false, ({} : Std.HashMap Name String))

  let coverageOverrideEntries ← match ← parseCoverageOverridesJson repoDir hasPkgManifest with
    | .ok arr => pure arr
    | .error err =>
      errors := errors.push err
      pure #[]

  let externalAssumpJsonEntries ← match ← parseExternalAssumptionsJson repoDir hasPkgManifest with
    | .ok arr => pure arr
    | .error err =>
      errors := errors.push err
      pure #[]

  let mut covLogData : CoverageLogData := {}
  let mut hasValidCovLog := false
  if let some covPath := cfg.coverageLogPath? then
    unless ← covPath.pathExists do
      errors := errors.push s!"MISSING_COVERAGE_LOG: {covPath}"
    if ← covPath.pathExists then
      let expectedCovNonce := effectiveCovNonce?.getD ""
      covLogData ← parseCoverageLogFile covPath expectedCovNonce
      if covLogData.badLines > 0 then
        errors := errors.push s!"INVALID_OR_UNAUTHENTICATED_COVERAGE_LOG_LINES: {covLogData.badLines} lines failed nonce/format check"
      if !covLogData.sawInit || !covLogData.sawClose then
        errors := errors.push "INCOMPLETE_OR_UNINITIALIZED_COVERAGE_LOG: missing LOG_INIT or LOG_CLOSE"
      if covLogData.badLines == 0 && covLogData.sawInit && covLogData.sawClose then
        hasValidCovLog := true
      for (pkgStr, suiteStr, _, _, _, okVal) in covLogData.fuzzEquiv do
        if !okVal then
          errors := errors.push s!"FUZZ_EQUIV_FAILED: {pkgStr} ({suiteStr}) reported ok=false"
      for ((qualOp, kindCtor), modes) in covLogData.errHits do
        if modes.contains "mocked" then
          let opName := qualOp.toName
          let opMod := moduleOfConst env opName
          let opPkg :=
            if opMod != .anonymous then pkgNamespaceOfSpecWith knownPkgs opMod
            else pkgNamespaceOfSpecWith knownPkgs opName
          if isPurePackage env knownPkgs purityMap opPkg then
            errors := errors.push s!"PURE_PACKAGE_MOCKED_ERR_HIT: ({qualOp}, {kindCtor}) in pure package {opPkg}"

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
        if typeUsed.any (fun k => k == `Core.logAssumpPass || k == `Core.logErrPass || k == `Core.logErrHit) ||
            valUsed.any (fun k => k == `Core.logAssumpPass || k == `Core.logErrPass || k == `Core.logErrHit) then
          errors := errors.push s!"FORBIDDEN_DIRECT_LOG_CALL: {c.name} in {m}"
        if m != `Tests.Main &&
            (typeUsed.any (· == `Core.setErrTestPassHook) || valUsed.any (· == `Core.setErrTestPassHook)) then
          errors := errors.push s!"FORBIDDEN_DIRECT_LOG_CALL: {c.name} in {m} mutates Core.setErrTestPassHook"
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
    else if m.getRoot == `LeanSwe && !isProofsModule m && !m.components.contains `RuntimeTests &&
        (m.components.contains `Model || m.components.contains `SpecTests) then
      let pkg := pkgNamespaceOfSpecWith knownPkgs m
      if cfg.legacyAllowlist.contains pkg then continue
      for c in data.constants do
        if isCompilerAux c.name || isInductiveElimAux env c.name then continue
        let short := c.name.getString!
        if short.startsWith "empirical_" then
          errors := errors.push s!"RENAMED_OR_EMPIRICAL_ASSUMPTION: {c.name} in {m}"
        if short.startsWith "assume_" then
          formalAssumptions := formalAssumptions.push (m, c.name)
          specAndProofRoots := specAndProofRoots.push c.name

  let usedInSpecsOrProofs := collectTransitiveDeps env specAndProofRoots
  let formalAssumpSet0 : Std.HashSet Name := formalAssumptions.foldl (fun s (_, a) => s.insert a) {}
  let formalAssumpSet : Std.HashSet Name := externalAssumpJsonEntries.foldl (init := formalAssumpSet0) fun s entry =>
    match entry.formalPred? with
    | some fp =>
      let pn := fp.toName
      if env.contains pn then s.insert pn else s
    | none => s
  let ctx : Core.Context := { fileName := "<CheckAssumptions>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let state : Core.State := { env }
  let ((metaErrs, expectedAssumpNames, expectedErrorTests, oleanNeverErrCount, centralCellsChecked), _) ← (Meta.MetaM.run' do
    let mut errs : Array String := #[]
    let mut expAssumps : Array String := #[]
    let mut expErrTests : Array (String × String) := #[]
    let mut axCache : AxCache := {}
    let mut dbCache : DeadBranchCache := {}
    let mut centralCellsN : Nat := 0

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

    let (provedImpossibleCells, piErrs, axCacheAfterPi) ← discoverProvedImpossibleCells env knownPkgs axCache
    axCache := axCacheAfterPi
    errs := errs ++ piErrs

    let mut overrideCells : Std.HashSet (String × String) := {}
    for entry in coverageOverrideEntries do
      let cellKey := (entry.op, entry.kind)
      if overrideCells.contains cellKey then
        errs := errs.push s!"DUPLICATE_COVERAGE_OVERRIDE: ({entry.op}, {entry.kind})"
        continue
      let opName := entry.op.toName
      let some opInfo := env.find? opName
        | errs := errs.push s!"INVALID_COVERAGE_OVERRIDE_OP: {entry.op} not found in compiled environment"; continue
      let opMod := moduleOfConst env opName
      let opPkg := pkgNamespaceOfSpecWith knownPkgs opMod
      let isPublicPkgOp := !isPrivateName opName && !isCompilerAux opName &&
        (opMod == Name.str opPkg "Interface" || (opMod == Name.str opPkg "Impl" && opName.getPrefix == opPkg))
      if !isPublicPkgOp || !(← isFallibleCodomain opInfo.type) then
        errs := errs.push s!"INVALID_COVERAGE_OVERRIDE_OP: {entry.op} is not a fallible public Interface operation"
        continue
      let kindName := entry.kind.toName
      let some (.ctorInfo kindCtorInfo) := env.find? kindName
        | errs := errs.push s!"INVALID_COVERAGE_OVERRIDE_KIND: {entry.kind} is not an inductive constructor"; continue
      let mut kindMatches := false
      if let some errTyName ← extractFallibleErrorType? opInfo.type then
        if let some resolvedEnum ← resolveErrorKindEnum? env opPkg errTyName then
          if resolvedEnum == kindCtorInfo.induct then
            kindMatches := true
      if !kindMatches then
        errs := errs.push s!"INVALID_COVERAGE_OVERRIDE_KIND: {entry.kind} does not match error kind enum of {entry.op}"
        continue
      if entry.mode == "mocked" then
        if isPurePackage env knownPkgs purityMap opPkg then
          errs := errs.push s!"PURE_PACKAGE_MOCKED_OVERRIDE: ({entry.op}, {entry.kind}) cannot use mode 'mocked' on pure package {opPkg}"
          continue
        if entry.testSymbol.trimAscii.toString.isEmpty then
          errs := errs.push s!"MISSING_COVERAGE_OVERRIDE_TEST_SYMBOL: ({entry.op}, {entry.kind}) with mode 'mocked' requires non-empty test_symbol"
          continue
      overrideCells := overrideCells.insert cellKey

    let mut seenExtJsonIds : Std.HashSet String := {}
    for entry in externalAssumpJsonEntries do
      if seenExtJsonIds.contains entry.id then
        errs := errs.push s!"DUPLICATE_EXTERNAL_ASSUMPTION_ID: {entry.id}"
        continue
      seenExtJsonIds := seenExtJsonIds.insert entry.id
      let pkgName := entry.package.toName
      let pkgKnown := purityMap.contains pkgName || knownPkgs.contains pkgName || visited.contains (Name.str pkgName "Interface")
      if !pkgKnown then
        errs := errs.push s!"UNKNOWN_EXTERNAL_ASSUMPTION_PACKAGE: {entry.package} in '{entry.id}'"
        continue
      if isPurePackage env knownPkgs purityMap pkgName then
        errs := errs.push s!"PURE_PACKAGE_EXTERNAL_ASSUMPTION: '{entry.id}' targets pure package {entry.package}"
        continue
      if let some fpStr := entry.formalPred? then
        let fpName := fpStr.toName
        let some _ := env.find? fpName
          | errs := errs.push s!"MISSING_EXTERNAL_ASSUMPTION_FORMAL_PRED: {fpStr} in '{entry.id}' not found in compiled environment"; continue
        let fpPkg := pkgNamespaceOfSpecWith knownPkgs (moduleOfConst env fpName)
        if fpPkg != pkgName then
          errs := errs.push s!"INVALID_EXTERNAL_ASSUMPTION_FORMAL_PRED_PKG: {fpStr} belongs to {fpPkg}, expected {pkgName}"
        let (badAx?, axCache') ← checkAxiomsOk axCache fpName
        axCache := axCache'
        if let some badAx := badAx? then
          errs := errs.push s!"UNALLOWED_AXIOM_IN_ASSUMPTION: {fpName} uses [{badAx}]"
        if !assumpCanReach.contains fpName then
          errs := errs.push s!"MISSING_ASSUMPTION_CANREACH: {fpName} referenced by external_assumptions.json '{entry.id}'"
        if !assumpUpperConsumed.contains fpName then
          errs := errs.push s!"UNUSED_FORMAL_ASSUMPTION: {fpName} referenced by external_assumptions.json '{entry.id}'"

    let activeCacheRef ← IO.mkRef ({} : ActiveCallCache)

    for (m, aName) in formalAssumptions do
      let pkgNs := pkgNamespaceOfSpecWith knownPkgs m
      if !isExternalBoundaryPkg env knownPkgs pkgNs then
        errs := errs.push s!"PURE_MODULE_ASSUMPTION_FORBIDDEN: {aName} in pure module {m} (use test_* promises)"
        continue
      let (badAx?, axCache') ← checkAxiomsOk axCache aName
      axCache := axCache'
      if let some badAx := badAx? then
        errs := errs.push s!"UNALLOWED_AXIOM_IN_ASSUMPTION: {aName} uses [{badAx}]"
      let usedAssert ← usesAnyConstActiveCached env activeCacheRef (Std.HashSet.emptyWithCapacity 1 |>.insert `Core.NondetTest.assert) aName
      if !usedAssert then
        errs := errs.push s!"COMMENT_ONLY_OR_TRIVIAL_ASSUMPTION: {aName} in {m} does not assert a check"
      else if let some (.defnInfo dv) := env.find? aName then
        let bodyStatus ← lambdaTelescope dv.value fun xs body => do
          let mut explicitNonInst : Array FVarId := #[]
          for x in xs do
            let bi ← x.fvarId!.getBinderInfo
            let xTy ← whnf (← inferType x)
            if bi == .default && !xTy.isAppOfArity `Core.NondetTest 1 then
              explicitNonInst := explicitNonInst.push x.fvarId!
          let fvarSet : Std.HashSet FVarId := explicitNonInst.foldl (fun (s : Std.HashSet FVarId) fv => s.insert fv) {}
          if fvarSet.isEmpty then return BoundedBool.isFalse
          let (foundAssert, assertStatus) ← validateAssertsInExpr fvarSet {} body
          if !foundAssert then return BoundedBool.isFalse
          return assertStatus
        match bodyStatus with
        | .isTrue => pure ()
        | .isFalse =>
          errs := errs.push s!"TRIVIAL_ASSUMPTION_ASSERT: {aName} in {m} has trivial, vacuous, or boundary-independent assert"
        | .inconclusive reason =>
          errs := errs.push s!"INCONCLUSIVE_ASSUMPTION_CHECK: {aName} in {m} ({reason})"
      if !assumpCanReach.contains aName then
        errs := errs.push s!"MISSING_ASSUMPTION_CANREACH: {aName} in {m}"
      if !assumpUpperConsumed.contains aName then
        errs := errs.push s!"UNUSED_FORMAL_ASSUMPTION: {aName} in {m} is not consumed as a hypothesis by any upper-layer Proofs theorem"

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

    let relaxedEnv ← mkRelaxedProjectIrreduciblesEnv
    for pkg in knownPkgs do
      if cfg.legacyAllowlist.contains pkg then continue
      let rtMod := Name.str pkg "RuntimeTests"
      let hasRt := visited.contains rtMod || diskRtPkgs.contains pkg
      let isRetired := !hasRt
      let inSuites := fuzzCoveredPkgs.contains pkg
      let isExtPkg := isExternalBoundaryPkg env knownPkgs pkg
      let isFloatPkg := usesRuntimeFloat env knownPkgs pkg
      let isImpureBoundary := isExtPkg || isFloatPkg
      let hasRefinesThm := match findRefinesOrObeysThm? env pkg with
        | .ok (some _) => true
        | .error _ => true
        | .ok none => false
      if deferredRefinesModelPackages.contains pkg && hasRefinesThm then
        errs := errs.push s!"STALE_REFINES_DEFERRAL: {pkg} defines Proofs.obeys_model or Proofs.refines_model; remove from deferredRefinesModelPackages"
      if isRetired && isImpureBoundary && !inSuites then
        errs := errs.push s!"MISSING_FUZZ_SUITE: retired external-boundary package {pkg} is absent from harness/Fuzz/suites.json"
      let modelMod := Name.str pkg "Model"
      let hasModel := visited.contains modelMod
      let hasDirectOwnExtern := hasDirectOwnExternInPkg env knownPkgs pkg
      let usesExtCli := usesExternalCliPkg env knownPkgs pkg
      let isUnprovableExternalBoundary := hasDirectOwnExtern || usesExtCli
      let deferredExternalModel := !isRetired && isExtPkg && !inSuites
      let deferredSplitRefinesModel := !isRetired && !inSuites && deferredRefinesModelPackages.contains pkg
      let needsModel :=
        (isRetired && isImpureBoundary) || inSuites || (hasModel && !deferredExternalModel)
      let needsRefinesModel :=
        hasRefinesThm ||
          (!isUnprovableExternalBoundary && !deferredSplitRefinesModel && (hasModel && !deferredExternalModel))
      if needsModel then
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
          let (refErrs, nextAx) ← checkRefinesModelTheorem env relaxedEnv transImpsOf knownPkgs pkg modelMods axCache
          axCache := nextAx
          errs := errs ++ refErrs

    let throwTargets : Std.HashSet Name :=
      Std.HashSet.emptyWithCapacity 6
        |>.insert `MonadExcept.throw
        |>.insert `MonadExceptOf.throw
        |>.insert `throwThe
        |>.insert `EStateM.throw
        |>.insert `IO.userError

    let mut checkedSpecPkgs : Std.HashSet Name := {}
    for specMod in specModules do
      let pkgNs := pkgNamespaceOfSpecWith knownPkgs specMod
      checkedSpecPkgs := checkedSpecPkgs.insert pkgNs
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
                    if !isInModuleSubtree (moduleOfConst env fnName) rtMod || fnName.getString! != specName.toName.getString! then
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
                  errs := errs.push s!"UNLINKED_FORMAL_ASSUMPTION_PRED: {obName} exists in {moduleOfConst env obConst} with formalPred? = none"
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
          if pkgNamespaceOfSpecWith knownPkgs m == pkgNs && !listedFormalPreds.contains aName then
            errs := errs.push s!"UNLISTED_FORMAL_ASSUMPTION: {aName} missing from {extAssumpConst}"
      else
        for (m, aName) in formalAssumptions do
          if pkgNamespaceOfSpecWith knownPkgs m == pkgNs then
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
                    if !isInModuleSubtree (moduleOfConst env fnName) rtMod || fnName.toString != tName then
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

        let mut legacyEnum? : Option Name := none
        let hasLegacyErrCov := (env.find? errCovConst).isSome
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
          legacyEnum? := enumName?
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
              if thmMod.components.contains `SpecTests || thmMod.components.contains `RuntimeTests then
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
        else if !hasValidCovLog && !cfg.strictCentralCoverage then
          errs := errs.push s!"MISSING_ERROR_COVERAGE: {errCovConst}"

        let runCentralDischarge :=
          cfg.strictCentralCoverage || (hasValidCovLog && (hasRt || !hasLegacyErrCov))
        if runCentralDischarge then
          let mut pkgCentralCells : Nat := 0
          for reqName in fallibleReqs do
            let some reqInfo := env.find? reqName
              | errs := errs.push s!"UNRESOLVABLE_FALLIBLE_OP: {reqName} in {pkgNs} not found in compiled environment"; continue
            let some errTyName ← extractFallibleErrorType? reqInfo.type
              | errs := errs.push s!"UNEXTRACTABLE_ERROR_TYPE: {reqName} in {pkgNs} has fallible codomain without extractable Except error type"; continue
            let some enumName ← resolveErrorKindEnum? env pkgNs errTyName legacyEnum?
              | errs := errs.push s!"UNRESOLVABLE_ERROR_KIND_ENUM: {reqName} (error type {errTyName}) in {pkgNs}"; continue
            let some (.inductInfo enumInd) := env.find? enumName
              | errs := errs.push s!"EMPTY_OR_NON_INDUCTIVE_ERROR_ENUM: {enumName} for {reqName} in {pkgNs}"; continue
            if enumInd.ctors.isEmpty then
              errs := errs.push s!"EMPTY_OR_NON_INDUCTIVE_ERROR_ENUM: {enumName} for {reqName} in {pkgNs}"
              continue
            for ctor in enumInd.ctors do
              pkgCentralCells := pkgCentralCells + 1
              centralCellsN := centralCellsN + 1
              let cell := (reqName.toString, ctor.toString)
              let discharged :=
                provedImpossibleCells.contains cell ||
                covLogData.errHits.contains cell ||
                overrideCells.contains cell
              unless discharged do
                errs := errs.push s!"UNCOVERED_CENTRAL_ERROR_CELL: ({reqName}, {ctor}) in {pkgNs} not discharged by NeverErrorKind*, ERR_HIT log, or coverage_overrides.json"
          if !hasLegacyErrCov && (hasAnyFallibleIfaceSurface || !fallibleReqs.isEmpty) && pkgCentralCells == 0 then
            errs := errs.push s!"MISSING_ERROR_COVERAGE: {errCovConst} (central coverage checked 0 cells for fallible surface in {pkgNs})"

    for (m, aName) in formalAssumptions do
      let pkgNs := pkgNamespaceOfSpecWith knownPkgs m
      if !checkedSpecPkgs.contains pkgNs then
        let extAssumpConst := Name.str pkgNs "externalAssumptions"
        errs := errs.push s!"UNLISTED_FORMAL_ASSUMPTION: {aName} missing from {extAssumpConst}"

    let activeScanErrs := (← activeCacheRef.get).scanErrors.toArray.qsort (fun a b => a.1.toString < b.1.toString)
    for (fnName, reason) in activeScanErrs do
      errs := errs.push s!"INCONCLUSIVE_ACTIVE_CALL_CHECK: {fnName} ({reason})"

    return (errs, expAssumps, expErrTests, provedImpossibleCells.size, centralCellsN)
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

  IO.println s!"CENTRAL_COVERAGE_CHECK: olean_never_error={oleanNeverErrCount} err_hits={covLogData.errHits.size} fuzz_equiv={covLogData.fuzzEquiv.size} overrides={coverageOverrideEntries.size} ext_assumps={externalAssumpJsonEntries.size} central_cells={centralCellsChecked}"
  IO.println s!"ASSUMPTION_CHECK: spec_modules={specModules.size} assumptions={expectedAssumpNames.size} formal_assumptions={formalAssumptions.size} error_tests={expectedErrorTests.size} log_verified={verifiedLogCount} errors={errors.size}"
  if errors.isEmpty then
    return 0
  else
    for err in errors do
      IO.eprintln err
    return 1
