import Lean

/-!
Hardened checkable-assumptions, error-coverage, and `Core.Obeys` model-refinement
gate audit for `lean-swe` compiled `.olean` artifacts.

Enforces:
1. Complete module & axiom hygiene:
   - Every `.lean` file under `LeanSwe/` must be transitively imported by `LeanSwe`.
   - Zero custom `axiom` declarations anywhere in `Core` or `LeanSwe`.
   - Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) on all `assume_*`, `CanReach`,
     upper-layer consumer theorems, `NeverErrorKind*` theorems, and `obeys_model` theorems.
2. Zero prose-only, renamed, or hidden assumptions across non-`Proofs` project modules:
   - No `EmpiricalAssumptions` constant anywhere.
   - No `Prop`-typed inductive/structure field in any non-`Proofs` project module.
   - No standalone `0`-ary `: Prop` declarations across non-`Proofs` `LeanSwe` modules, and no unused `... → Prop`
     predicates or unreferenced public declarations in `SpecTests`.
   - No `String`-carrying data/collection top-level declarations in `SpecTests`.
   - No `empirical_*` or unclassified public `NondetTest`-returning declaration in `SpecTests`.
   - Permanent ban on legacy `errorCoverage` and `externalAssumptions` Lean declarations.
3. Pure vs External-Boundary separation:
   - Pure modules without `@[extern]`, host `IO` syscalls, or external CLI invocations must declare zero
     `assume_*` predicates and cannot appear in `scripts/external_assumptions.json`.
   - Impure external-boundary or runtime-`Float` packages require `<pkgNs>.Model` and a valid
     `fuzz_suite` entry in `scripts/package_manifest.json` present in `harness/Fuzz/suites.json`.
   - Formal `assume_*` predicates in `SpecTests` or `Model.Assumptions` must be listed in
     `scripts/external_assumptions.json`, non-trivial over the boundary parameter (`isMeaningfulBoundaryProp`),
     satisfiable via `Core.CanReach`, and consumed as a used `Prop` hypothesis (after zeta and beta reduction)
     in an upper-layer `Proofs` theorem.
4. Central error-coverage & differential-fuzz attestation:
   - Auto-discovers canonical `Core.NeverErrorKind{IO,BaseIO,Pure}` theorems from compiled `.olean`s.
   - Validates fail-closed `scripts/package_manifest.json` (`purity`, `external_boundary`, `fuzz_suite`)
     and `scripts/external_assumptions.json`.
   - Supports on-demand `--coverage-log <path> [--coverage-nonce <token> | --nonce <token>]`,
     `--strict-central-coverage`, and `--require-fuzz-equiv`, checking `LOG_INIT`/`LOG_CLOSE`, nonce,
     `ERR_HIT`, and `FUZZ_EQUIV` (`ok=true`, `steps > 0`, `total > 0`, `hit == total`, matching `fuzz_suite`).
5. `Core.Obeys` model-refinement structural completeness: every non-`@[extern]`/non-CLI package with
   `<pkgNs>.Model` (and any package defining `<pkgNs>.Proofs.obeys_model`) must prove public
   `<pkgNs>.Proofs.obeys_model` using bare-constant pinning, Model-to-Impl isolation, inhabited domains,
   and complete coverage of public `<pkgNs>.Interface` operations.
6. Supports `--print-sig <Pkg>` (emits a starting template with explicit placeholders for
   `<Pkg>.Proofs.obeys_model`).
-/

open Lean Meta

private def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4 |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

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

private def isProofsModule (m : Name) : Bool :=
  m.components.any (· == `Proofs)

private def isSpecOrProofsModule (m : Name) : Bool :=
  isProofsModule m || m.components.contains `SpecTests

private def moduleOfConst (env : Environment) (cName : Name) : Name :=
  env.getModuleIdxFor? cName |>.bind (env.header.moduleNames[·]?) |>.getD .anonymous

private def exprUsesPkgImpl (env : Environment) (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    let m := moduleOfConst env c
    m.getRoot == `LeanSwe && !isSpecOrProofsModule m && m.getString! != "Types"

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

private structure ActiveCallCache where
  directPlain : Std.HashMap Name (Array Name) := {}
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
    (cur : Name)
    (rawBody : Expr) : MetaM (Array Name) := do
  if let some hit := (← cacheRef.get).directPlain.get? cur then
    return hit
  let used ← match ← exprActiveDirectConsts env rawBody with
    | .ok arr => pure arr
    | .error reason =>
      cacheRef.modify fun c =>
        { c with scanErrors := if c.scanErrors.contains cur then c.scanErrors else c.scanErrors.insert cur reason }
      pure #[]
  cacheRef.modify fun c => { c with directPlain := c.directPlain.insert cur used }
  return used

private partial def usesPredConstActiveCached
    (env : Environment)
    (cacheRef : IO.Ref ActiveCallCache)
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
    if !isProjectModule modName then continue
    let body? := match env.find? cur with
      | some (.defnInfo dv) => some dv.value
      | some (.opaqueInfo ov) => some ov.value
      | _ => none
    if let some rawBody := body? then
      let used ← constActiveDirectConsts env cacheRef cur rawBody
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
  usesPredConstActiveCached env cacheRef (fun c => targets.contains c) start

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

private def unwrapNegatedProp? (e : Expr) : Option Expr :=
  let c := e.consumeMData
  if c.isAppOfArity ``Not 1 then
    some c.appArg!
  else if c.isAppOfArity ``Ne 3 then
    some (mkApp3 (mkConst ``Eq c.getAppFn.consumeMData.constLevels!) (c.getArg! 0) (c.getArg! 1) (c.getArg! 2))
  else
    match c with
    | .forallE _ dom body _ =>
      if !body.hasLooseBVar 0 && body.consumeMData.isConstOf ``False then
        some dom
      else
        none
    | _ => none

private def isNegationPair (a b : Expr) : MetaM BoundedBool := do
  let a' ← match ← runBoundedMeta (whnf a) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  let b' ← match ← runBoundedMeta (whnf b) with
    | .ok w => pure w.consumeMData
    | .error r => return .inconclusive r
  if let some inner := (unwrapNegatedProp? b).orElse (fun _ => unwrapNegatedProp? b') then
    match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq a' inner)) (maxRecDepth := 1024) with
    | .ok true => return .isTrue
    | .ok false => pure ()
    | .error r => return .inconclusive r
  if let some inner := (unwrapNegatedProp? a).orElse (fun _ => unwrapNegatedProp? a') then
    match ← runBoundedMeta (Meta.withNewMCtxDepth (isDefEq b' inner)) (maxRecDepth := 1024) with
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
          (pkgNamespaceOfSpecWith knownPkgs cMod == pkgNs && !isSpecOrProofsModule cMod)
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

private def parseFuzzSuiteNames (repoDir : System.FilePath) :
    IO (Except String (Bool × Std.HashSet String)) := do
  let manifestPath := repoDir / "harness" / "Fuzz" / "suites.json"
  if !(← manifestPath.pathExists) then
    return .ok (false, {})
  let raw ← IO.FS.readFile manifestPath
  match Lean.Json.parse raw with
  | .error err => return .error s!"MALFORMED_FUZZ_MANIFEST: {err}"
  | .ok j =>
    let .ok (.obj kvs) := j.getObjVal? "suites"
      | return .error "MALFORMED_FUZZ_MANIFEST: missing 'suites' object"
    let mut names : Std.HashSet String := {}
    for (suiteKey, suiteObj) in kvs do
      let .ok (.arr pathElems) := suiteObj.getObjVal? "paths"
        | return .error s!"MALFORMED_FUZZ_MANIFEST: suite '{suiteKey}' missing 'paths' array"
      for pe in pathElems do
        let .str _ := pe
          | return .error s!"MALFORMED_FUZZ_MANIFEST: suite '{suiteKey}' path entry must be string"
      names := names.insert suiteKey
    return .ok (true, names)

private def usesRuntimeFloat (env : Environment) (knownPkgs : Array Name) (pkgNs : Name) : Bool := Id.run do
  for h : mi in [0 : env.header.moduleNames.size] do
    let mName := env.header.moduleNames[mi]
    if mName.getRoot == `LeanSwe && pkgNamespaceOfSpecWith knownPkgs mName == pkgNs &&
        !isSpecOrProofsModule mName && mName.getString! != "Model" then
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
        !isSpecOrProofsModule mName && mName.getString! != "Model" then
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
        !isSpecOrProofsModule mName && mName.getString! != "Model" && mName.getString! != "SpecMutants" then
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

private partial def peelLambdasRefines (e : Expr) : Expr :=
  match e.consumeMData with
  | .lam _ _ b _ => peelLambdasRefines b
  | cur => cur

private def constValueClosureTouchesSweImplOrIface (env : Environment) (start : Name) : Bool := Id.run do
  let mut work : Array Name := #[start]
  let mut seen : Std.HashSet Name := {}
  while !work.isEmpty do
    let cur := work.back!
    work := work.pop
    if seen.contains cur then continue
    seen := seen.insert cur
    let m := moduleOfConst env cur
    if m.getRoot == `LeanSwe &&
        (m.components.contains `Impl || m.components.contains `Interface || m.components.contains `SysBridge) then
      return true
    if !isProjectModule m then continue
    if let some ci := env.find? cur then
      let valUsed := match ci with
        | .defnInfo v => v.value.getUsedConstants
        | .thmInfo v => v.value.getUsedConstants
        | .opaqueInfo v => v.value.getUsedConstants
        | _ => #[]
      for u in ci.type.getUsedConstants ++ valUsed do
        if !seen.contains u then
          work := work.push u
  return false

private def hasPureFromModelWitness
    (env : Environment) (depPkg pkg : Name) (depTy depObeys : Expr) (axCacheIn : AxCache) :
    MetaM (Bool × AxCache) := do
  let mut axCache := axCacheIn
  let depModelMod := Name.str depPkg "Model"
  let depModelPfx := depModelMod.toString ++ "."
  let proofsMod := Name.str pkg "Proofs"
  let proofsPfx := proofsMod.toString ++ "."
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    let inDepModel := m == depModelMod || m.toString.startsWith depModelPfx
    let inPkgProofs := m == proofsMod || m.toString.startsWith proofsPfx
    if !inDepModel && !inPkgProofs then continue
    let some data := env.header.moduleData[i]? | continue
    for c in data.constants do
      let .thmInfo tv := c | continue
      if isPrivateName c.name || isCompilerAux c.name || env.isProjectionFn c.name then continue
      let tc := tv.type.consumeMData
      if !tc.isAppOfArity ``Exists 2 then continue
      let okTy ← match ← runBoundedMeta (Meta.withNewMCtxDepth <| Meta.withTransparency .default do
          if !(← isDefEq tc.appFn!.appArg! depTy) then return false
          withLocalDeclD `_depWit depTy fun d =>
            isDefEq (mkApp tc.appArg! d) (mkApp depObeys d)) (maxRecDepth := 1024) with
        | .ok b => pure b
        | .error _ => pure false
      if !okTy then continue
      let (badAx?, nextAx) ← checkAxiomsOk axCache c.name
      axCache := nextAx
      if badAx?.isSome then continue
      if constValueClosureTouchesSweImplOrIface env c.name then continue
      return (true, axCache)
  return (false, axCache)

private def resolveInterfaceOpForProj?
    (env : Environment) (ifaceMod defApiName projFn : Name) : Option Name := Id.run do
  let stName := projFn.getPrefix
  let fldShort := Name.mkSimple projFn.getString!
  let fldIdx? := (Lean.getStructureFields env stName).findIdx? (· == fldShort)
  let some idx := env.header.moduleNames.findIdx? (· == ifaceMod) | return none
  let some data := env.header.moduleData[idx]? | return none
  let mut matchesFound : Array Name := #[]
  for c in data.constants do
    let .defnInfo dv := c | continue
    if isPrivateName c.name || isCompilerAux c.name || env.isProjectionFn c.name || c.name == defApiName then
      continue
    let body := peelLambdasRefines dv.value
    let fn := body.getAppFn.consumeMData
    let args := body.getAppArgs
    let hitsProj := match fn with
      | .proj s i inner =>
        s == stName && fldIdx? == some i && inner.consumeMData.isConstOf defApiName
      | .const pFn _ =>
        pFn == projFn && args.any (fun a => a.consumeMData.isConstOf defApiName)
      | _ => false
    if hitsProj then
      matchesFound := matchesFound.push c.name
  return if matchesFound.size == 1 then some matchesFound[0]! else none

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
  let ifaceMod := Name.str pkg "Interface"
  let implMod := Name.str pkg "Impl"

  for mMod in modelMods do
    for imp in transImpsOf mMod do
      if imp.getRoot == `LeanSwe && imp.isStr && (imp.getString! == "Interface" || imp.getString! == "Impl") then
        errs := errs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mMod} transitively imports {imp}"

  let thmName := Name.str topProofMod "obeys_model"
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
          if ab.isAppOfArity `Core.ObeysPure 4 then
            let args := ab.getAppArgs; some (false, #[args[0]!], args[1]!, args[2]!, args[3]!)
          else if ab.isAppOfArity `Core.ObeysPure2 5 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!], args[2]!, args[3]!, args[4]!)
          else if ab.isAppOfArity `Core.ObeysPure3 6 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!, args[2]!], args[3]!, args[4]!, args[5]!)
          else if ab.isAppOfArity `Core.ObeysPure4 7 then
            let args := ab.getAppArgs; some (false, #[args[0]!, args[1]!, args[2]!, args[3]!], args[4]!, args[5]!, args[6]!)
          else if ab.isAppOfArity `Core.ObeysPureEq 4 then
            let args := ab.getAppArgs; some (true, #[args[0]!], args[1]!, args[2]!, args[3]!)
          else if ab.isAppOfArity `Core.ObeysPureEq2 5 then
            let args := ab.getAppArgs; some (true, #[args[0]!, args[1]!], args[2]!, args[3]!, args[4]!)
          else if ab.isAppOfArity `Core.ObeysPureEq3 6 then
            let args := ab.getAppArgs; some (true, #[args[0]!, args[1]!, args[2]!], args[3]!, args[4]!, args[5]!)
          else if ab.isAppOfArity `Core.ObeysPureEq4 7 then
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
          for inTyS in inTysSubst do
            if !(← isProvablyInhabitedDataType env 8 inTyS) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited input domain for {implFn} in {thmName}"
          if isEqKind then
            let outTySubst := applySubst (stripOptParamType outTy)
            if ← isProp outTySubst then
              aErrs := aErrs.push s!"TRIVIAL_CODOMAIN_IN_REFINES: Prop codomain in ObeysPureEq for {implFn} in {thmName}"
            else
              let ow := (← whnf outTySubst).consumeMData
              if ow.isConstOf ``Unit || ow.isConstOf ``PUnit then
                aErrs := aErrs.push s!"TRIVIAL_CODOMAIN_IN_REFINES: Unit codomain in ObeysPureEq for {implFn} in {thmName}"
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

        if let some (inTys, errTy, _kindTy, _okTy, kindArg, msgArg, implArg, modelArg) := pureErrMsgInfo? then
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
          for inTyS in inTysSubst do
            if !(← isProvablyInhabitedDataType env 8 inTyS) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited input domain for {implFn} in {thmName}"
          if !(← isProvablyInhabitedDataType env 8 errTySubst) then
            aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited error domain for {implFn} in {thmName}"
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
          if aErrs.isEmpty then
            coveredPureOpsRef.modify (·.insert parseFn)
          return aErrs

        if ab.isAppOfArity `Core.ObeysPureFrom 8 || ab.isAppOfArity `Core.ObeysInverseRenderFrom 13 then
          let isInvFrom := ab.isAppOfArity `Core.ObeysInverseRenderFrom 13
          let a := ab.getAppArgs
          let depTy := a[0]!
          let pkgApiTy := a[1]!
          let (depObeysArg, mkApiArg, projArg) :=
            if isInvFrom then (a[6]!, a[7]!, a[8]!) else (a[4]!, a[5]!, a[6]!)
          let some depObeysFn ← checkBareConstArg env allowedAtomFVs false depObeysArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare depObeys argument in {thmName}"]
          let some mkApiFn ← checkBareConstArg env allowedAtomFVs false mkApiArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare mkApi argument in {thmName}"]
          let some projFn ← checkBareConstArg env allowedAtomFVs false projArg
            | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare projOp argument in {thmName}"]
          let depMod := moduleOfConst env depObeysFn
          let depPkg := pkgNamespaceOfSpecWith knownPkgs depMod
          let depModelMod := Name.str depPkg "Model"
          let inDepModel := depMod == depModelMod || depMod.toString.startsWith (depModelMod.toString ++ ".")
          if isPrivateName depObeysFn || depPkg == pkg || !inDepModel then
            aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {depObeysFn} in {thmName} must be a public cross-package Model constant"
          if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef depObeysFn then
            aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {depObeysFn} in {thmName} transitively references Interface/Impl"
          let mkMod := moduleOfConst env mkApiFn
          if isPrivateName mkApiFn || modelMods.contains mkMod || (mkMod != ifaceMod && mkMod != implMod) then
            aErrs := aErrs.push s!"NON_INTERFACE_IMPL_IN_REFINES: {mkApiFn} in {thmName} must be a public constant in {ifaceMod} or {implMod}"
          let pkgTypesMod := Name.str pkg "Types"
          let pkgApiHead? := pkgApiTy.consumeMData.getAppFn.consumeMData.constName?
          if isPrivateName projFn || !env.isProjectionFn projFn ||
              moduleOfConst env projFn != pkgTypesMod || pkgApiHead? != some projFn.getPrefix then
            aErrs := aErrs.push s!"NON_INTERFACE_IMPL_IN_REFINES: {projFn} in {thmName} must be a structure projection of {pkgApiTy} in {pkgTypesMod}"
          let defApiName := Name.str pkg "defaultApi"
          let depDefaultApi := Name.str depPkg "defaultApi"
          let wiredOk := match env.find? defApiName with
            | some (.defnInfo defDv) =>
              moduleOfConst env defApiName == ifaceMod &&
                let b := defDv.value.consumeMData
                let bArgs := b.getAppArgs
                b.getAppFn.consumeMData.constName? == some mkApiFn &&
                  bArgs.size == 1 && bArgs[0]!.consumeMData.isConstOf depDefaultApi
            | _ => false
          if !wiredOk then
            aErrs := aErrs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: {defApiName} must wire {mkApiFn} directly to {depDefaultApi}"
          let implOp? := resolveInterfaceOpForProj? env ifaceMod defApiName projFn
          if implOp?.isNone then
            aErrs := aErrs.push s!"INCOMPLETE_INTERFACE_REFINEMENT: no unique Interface operation in {ifaceMod} delegates via {projFn} to {defApiName}"
          let depObeysThm := Name.str (Name.str depPkg "Proofs") "obeys_model"
          match env.find? depDefaultApi, env.find? depObeysThm with
          | some (.defnInfo _), some (.thmInfo depTv) =>
            let bridgeOk ← match ← runBoundedMeta
                (Meta.withNewMCtxDepth <| Meta.withTransparency .default <|
                  isDefEq depTv.type (mkApp depObeysArg (mkConst depDefaultApi [])).headBeta)
                (maxRecDepth := 1024) with
              | .ok b => pure b
              | .error _ => pure false
            if !bridgeOk then
              aErrs := aErrs.push s!"PURE_FROM_OBEYS_MISMATCH: {depObeysFn} on {depDefaultApi} is not definitionally equal to {depObeysThm}"
          | _, _ =>
            aErrs := aErrs.push s!"PURE_FROM_OBEYS_MISMATCH: missing {depDefaultApi} or {depObeysThm} for {depObeysFn} in {thmName}"
          if !(← isProvablyInhabitedDataType env 8 depTy) then
            aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited capability domain {depTy} in {thmName}"
          let depVac ← withLocalDeclD `_depVal depTy fun d => isStaticFalseProp (mkApp depObeysArg d)
          match depVac with
          | .isFalse => pure ()
          | .isTrue =>
            aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {depObeysFn} in {thmName} is identically false"
          | .inconclusive reason =>
            aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {depObeysFn} in {thmName} ({reason})"
          let (hasWit, _) ← hasPureFromModelWitness env depPkg pkg depTy depObeysArg {}
          if !hasWit then
            aErrs := aErrs.push s!"MISSING_PURE_FROM_WITNESS: {thmName} lacks an Impl/Interface-free theorem ∃ d, {depObeysFn} d"
          if !isInvFrom then
            let inTy := a[2]!
            let specArg := a[7]!
            let some specFn ← checkBareConstArg env allowedAtomFVs false specArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare allowed argument in {thmName}"]
            if isPrivateName specFn || !modelMods.contains (moduleOfConst env specFn) then
              aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {specFn} in {thmName} is not a public constant in {pkg}.Model"
            if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef specFn then
              aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {specFn} in {thmName} transitively references Interface/Impl"
            let inTyS := applySubst (stripOptParamType inTy)
            if !(← isProvablyInhabitedDataType env 8 inTyS) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited input domain for {projFn} in {thmName}"
          else
            let (objTy, tapeTy, rawTy, errTy) := (a[2]!, a[3]!, a[4]!, a[5]!)
            let (renderArg, wfArg, equivArg, msgArg) := (a[9]!, a[10]!, a[11]!, a[12]!)
            let some renderFn ← checkBareConstArg env allowedAtomFVs false renderArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare render argument in {thmName}"]
            let some wfFn ← checkBareConstArg env allowedAtomFVs false wfArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare wf argument in {thmName}"]
            let some equivFn ←
              if equivArg.consumeMData.isAppOfArity ``Eq 1 then pure (some ``Eq)
              else checkBareConstArg env allowedAtomFVs false equivArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare equiv argument in {thmName}"]
            let some msgFn ← checkBareConstArg env allowedAtomFVs false msgArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare msgOf argument in {thmName}"]
            for mFn in #[renderFn, wfFn] do
              if isPrivateName mFn || !modelMods.contains (moduleOfConst env mFn) then
                aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {mFn} in {thmName} is not a public constant in {pkg}.Model"
            if equivFn != ``Eq && (isPrivateName equivFn || !modelMods.contains (moduleOfConst env equivFn)) then
              aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {equivFn} in {thmName} must be Eq or a public constant in {pkg}.Model"
            if !isAllowedErrorExtractorConst env pkg modelMods msgFn then
              aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {msgFn} in {thmName} must be a public Types/Model constant"
            for mFn in #[renderFn, wfFn, equivFn, msgFn] do
              if mFn != ``Eq && (← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef mFn) then
                aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {mFn} in {thmName} transitively references Interface/Impl"
            let objTyS := applySubst (stripOptParamType objTy)
            let tapeTyS := applySubst (stripOptParamType tapeTy)
            let rawTyS := applySubst (stripOptParamType rawTy)
            let errTyS := applySubst (stripOptParamType errTy)
            for dTy in #[objTyS, tapeTyS, rawTyS, errTyS] do
              if !(← isProvablyInhabitedDataType env 8 dTy) then
                aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited domain in ObeysInverseRenderFrom for {projFn} in {thmName}"
            let wfSubst := applySubst wfArg
            let wfCheck ← withLocalDeclD `_invObj objTyS fun o => isStaticFalseProp (mkApp wfSubst o)
            match wfCheck with
            | .isFalse => pure ()
            | .isTrue =>
              aErrs := aErrs.push s!"VACUOUS_WF_IN_REFINES: {wfFn} in {thmName} is identically false"
            | .inconclusive reason =>
              aErrs := aErrs.push s!"INCONCLUSIVE_REFINES_CHECK: {wfFn} in {thmName} ({reason})"
          if aErrs.isEmpty then
            if let some implFn := implOp? then
              coveredPureOpsRef.modify (·.insert implFn)
          return aErrs

        let stepInfo? : Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr) :=
          if ab.isAppOfArity `Core.ObeysStep 8 then
            let args := ab.getAppArgs
            some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!)
          else if ab.isAppOfArity `Core.ObeysStepExcept 8 then
            let args := ab.getAppArgs
            let exOutTy := mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``IO.Error) args[3]!
            some (args[0]!, args[1]!, args[2]!, exOutTy, args[4]!, args[5]!, args[6]!, args[7]!)
          else if ab.isAppOfArity `Core.ObeysStepId 6 then
            let args := ab.getAppArgs
            let sTy := args[0]!
            some (sTy, sTy, args[1]!, args[2]!, mkApp (mkConst ``id [Level.succ Level.zero]) sTy, args[3]!, args[4]!, args[5]!)
          else none

        if let some (wTy, sTy, reqTy, _outTy, projArg, wfArg, stepArg, allowedArg) := stepInfo? then
          if !axs.isEmpty then
            return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} ObeysStep conjunct cannot have binders"]
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
            aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited state/request domain in ObeysStep of {thmName}"
          if aErrs.isEmpty then
            if stepMod == ifaceMod then
              coveredStepOpsRef.modify (·.insert stepFn)
            else if stepMod == implMod then
              coveredImplHelpersRef.modify (·.insert stepFn)
          return aErrs

        let stepFromInfo? : Option (Option (Expr × Expr) × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Array (Expr × Expr × Expr × Expr)) :=
          if ab.isAppOfArity `Core.ObeysStepFrom 16 ||
              ab.isAppOfArity `Core.ObeysStepFromFinally 16 ||
              ab.isAppOfArity `Core.ObeysStepFromConc 16 then
            let args := ab.getAppArgs
            some (none, args[0]!, args[1]!, args[6]!, args[7]!, args[8]!, args[9]!, args[12]!, args[13]!, args[14]!,
              #[(args[4]!, args[5]!, args[10]!, args[11]!), (args[6]!, args[7]!, args[14]!, args[15]!)])
          else if ab.isAppOfArity `Core.ObeysStepFromExcept 16 then
            let args := ab.getAppArgs
            let exRawOutTy := mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``IO.Error) args[5]!
            let exPkgOutTy := mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``IO.Error) args[7]!
            some (none, args[0]!, args[1]!, args[6]!, exPkgOutTy, args[8]!, args[9]!, args[12]!, args[13]!, args[14]!,
              #[(args[4]!, exRawOutTy, args[10]!, args[11]!), (args[6]!, exPkgOutTy, args[14]!, args[15]!)])
          else if ab.isAppOfArity `Core.ObeysStepFromConcCell 19 then
            let args := ab.getAppArgs
            some (some (args[1]!, args[11]!), args[0]!, args[2]!, args[8]!, args[9]!, args[10]!, args[12]!, args[15]!, args[16]!, args[17]!,
              #[(args[6]!, args[7]!, args[13]!, args[14]!), (args[8]!, args[9]!, args[17]!, args[18]!)])
          else if ab.isAppOfArity `Core.ObeysStepFrom2 21 then
            let args := ab.getAppArgs
            some (none, args[0]!, args[1]!, args[9]!, args[10]!, args[11]!, args[12]!, args[17]!, args[18]!, args[19]!,
              #[(args[5]!, args[6]!, args[13]!, args[14]!),
                (args[7]!, args[8]!, args[15]!, args[16]!),
                (args[9]!, args[10]!, args[19]!, args[20]!)])
          else none

        if let some (cellInfo?, rawSTy, pkgSTy, pkgReqTy, _pkgOutTy, mapSArg, rawWfArg, pkgWfArg, mkApiArg, execPkgArg, stepLegs) := stepFromInfo? then
          if !axs.isEmpty then
            return #[s!"INVALID_REFINES_ATOM_BINDER: {thmName} ObeysStepFrom conjunct cannot have binders"]
          if let some (cellModelSTy, cellToModelArg) := cellInfo? then
            let some cellToModelFn ← checkBareConstArg env {} false cellToModelArg
              | return #[s!"LAMBDA_OR_PARTIAL_APP_IN_REFINES: non-bare cellToModel argument in {thmName}"]
            if isPrivateName cellToModelFn || !modelMods.contains (moduleOfConst env cellToModelFn) then
              aErrs := aErrs.push s!"NON_MODEL_SPEC_IN_REFINES: {cellToModelFn} in {thmName} is not a public constant in {pkg}.Model"
            if ← constTransitivelyTouchesSweImplOrIfaceCached env safeModelConstsRef cellToModelFn then
              aErrs := aErrs.push s!"MODEL_REFERENCES_IMPL_IN_REFINES: {cellToModelFn} in {thmName} transitively references Interface/Impl"
            if !(← isProvablyInhabitedDataType env 8 cellModelSTy) then
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited cellModelS domain in ObeysStepFromConcCell of {thmName}"
          let some mapSFn ← checkBareConstArg env {} cellInfo?.isNone mapSArg
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
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited state/request domain in ObeysStepFrom of {thmName}"
          for (legReqTy, _legOutTy, legExecArg, legAllowedArg) in stepLegs do
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
              aErrs := aErrs.push s!"UNINHABITED_DOMAIN_IN_REFINES: uninhabited state/request domain in ObeysStepFrom of {thmName}"
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
  proofsLibDir? : Option System.FilePath := none
  nonce? : Option String := none
  coverageLogPaths : Array System.FilePath := #[]
  coverageNonce? : Option String := none
  strictCentralCoverage : Bool := false
  requireFuzzEquiv : Bool := false
  printSigPkg? : Option Name := none
  argError? : Option String := none

private def parseArgs (args : List String) : CliConfig :=
  let rec go (cfg : CliConfig) (pos : Nat) : (xs : List String) → CliConfig
    | [] => cfg
    | "--proofs-lib" :: p :: rest => go { cfg with proofsLibDir? := some ⟨p⟩ } pos rest
    | ["--proofs-lib"] => { cfg with argError? := some "MISSING_PROOFS_LIB_VALUE: --proofs-lib requires a path" }
    | "--nonce" :: nc :: rest => go { cfg with nonce? := some nc } pos rest
    | ["--nonce"] => { cfg with argError? := some "MISSING_NONCE_VALUE: --nonce requires a non-empty argument" }
    | "--coverage-log" :: lp :: rest => go { cfg with coverageLogPaths := cfg.coverageLogPaths.push ⟨lp⟩ } pos rest
    | ["--coverage-log"] => { cfg with argError? := some "MISSING_COVERAGE_LOG_VALUE: --coverage-log requires a path" }
    | "--coverage-nonce" :: nc :: rest => go { cfg with coverageNonce? := some nc } pos rest
    | ["--coverage-nonce"] => { cfg with argError? := some "MISSING_COVERAGE_NONCE_VALUE: --coverage-nonce requires a non-empty argument" }
    | "--strict-central-coverage" :: rest => go { cfg with strictCentralCoverage := true } pos rest
    | "--require-fuzz-equiv" :: rest => go { cfg with requireFuzzEquiv := true } pos rest
    | "--print-sig" :: pkgStr :: rest => go { cfg with printSigPkg? := some pkgStr.toName } pos rest
    | ["--print-sig"] => { cfg with argError? := some "MISSING_PRINT_SIG_VALUE: --print-sig requires a package name" }
    | arg :: rest =>
      if arg.startsWith "-" then
        { cfg with argError? := some s!"UNKNOWN_FLAG: {arg}" }
      else if pos == 0 then
        go { cfg with libDir := ⟨arg⟩ } 1 rest
      else if pos == 1 then
        go { cfg with repoDir := ⟨arg⟩ } 2 rest
      else
        { cfg with argError? := some s!"UNEXPECTED_POSITIONAL_ARG: {arg}" }
  termination_by xs => xs.length
  go {} 0 args

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

private def parsePackageManifest (repoDir : System.FilePath) :
    IO (Except String (Bool × Std.HashMap Name String × Std.HashMap Name Bool × Std.HashMap Name String)) := do
  let manifestPath := repoDir / "scripts" / "package_manifest.json"
  if !(← manifestPath.pathExists) then
    return .ok (false, {}, {}, {})
  let raw ← IO.FS.readFile manifestPath
  match Lean.Json.parse raw with
  | .error err => return .error s!"MALFORMED_PACKAGE_MANIFEST: {err}"
  | .ok j =>
    let .ok (.obj pkgs) := j.getObjVal? "packages"
      | return .error "MALFORMED_PACKAGE_MANIFEST: missing 'packages' object"
    let mut purityOut : Std.HashMap Name String := {}
    let mut extBoundaryOut : Std.HashMap Name Bool := {}
    let mut fuzzSuiteOut : Std.HashMap Name String := {}
    for (pkgStr, entry) in pkgs do
      let .obj _ := entry
        | return .error s!"MALFORMED_PACKAGE_MANIFEST: package '{pkgStr}' entry must be a JSON object"
      match entry.getObjVal? "purity" with
      | .error _ => pure ()
      | .ok pVal =>
        match pVal.getStr? with
        | .ok pStr => purityOut := purityOut.insert pkgStr.toName pStr
        | .error _ => return .error s!"MALFORMED_PACKAGE_MANIFEST: package '{pkgStr}' has non-string 'purity'"
      match entry.getObjValAs? Bool "external_boundary" with
      | .ok eb => extBoundaryOut := extBoundaryOut.insert pkgStr.toName eb
      | .error _ =>
        return .error s!"MALFORMED_PACKAGE_MANIFEST: package '{pkgStr}' missing or non-boolean 'external_boundary'"
      match entry.getObjVal? "fuzz_suite" with
      | .error _ => pure ()
      | .ok fsVal =>
        match fsVal.getStr? with
        | .ok fsStr =>
          if fsStr.trimAscii.toString.isEmpty then
            return .error s!"MALFORMED_PACKAGE_MANIFEST: package '{pkgStr}' has empty 'fuzz_suite'"
          fuzzSuiteOut := fuzzSuiteOut.insert pkgStr.toName fsStr
        | .error _ =>
          return .error s!"MALFORMED_PACKAGE_MANIFEST: package '{pkgStr}' has non-string 'fuzz_suite'"
    return .ok (true, purityOut, extBoundaryOut, fuzzSuiteOut)

private def isPurePackage (env : Environment) (knownPkgs : Array Name)
    (purityMap : Std.HashMap Name String) (pkg : Name) : Bool :=
  match purityMap.get? pkg with
  | some p => p == "pure"
  | none => !isExternalBoundaryPkg env knownPkgs pkg

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

private def resolveErrorKindEnum? (env : Environment) (pkg errTypeName : Name) : MetaM (Option Name) := do
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
  if errTypeName.isStr then
    let cand := Name.str errTypeName.getPrefix (errTypeName.getString! ++ "Kind")
    if let some (.inductInfo _) := env.find? cand then
      return some cand
  if let some pk := findPkgErrorKindEnum? env pkg then
    return some pk
  if let some (.inductInfo ind) := env.find? errTypeName then
    if isNullaryEnumInductive env ind then
      return some errTypeName
  return none

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
    let mkApiCand :=
      let c1 := Name.str (Name.str pkg "Internal") "mkApiM"
      let c2 := Name.str (Name.str pkg "Internal") "mkApiFromCapsM"
      if env.contains c2 then c2 else c1
    let mkFullCand := Name.str (Name.str pkg "Internal") "mkFullApiM"
    let (isConcCell, stepPred, builderStr) :=
      match (env.find? mkFullCand).orElse (fun _ => env.find? mkApiCand) with
      | some ci =>
        let used := ci.type.getUsedConstants
        let cc := used.contains `Core.ConcOpsM && used.contains `Core.StateCellM
        let pred :=
          if cc then "Core.ObeysStepFromConcCell"
          else if used.contains `Core.ConcOpsM then "Core.ObeysStepFromConc"
          else if used.contains ``MonadExceptOf then "Core.ObeysStepFromExcept"
          else if used.contains ``MonadFinally then "Core.ObeysStepFromFinally"
          else "Core.ObeysStepFrom"
        let bName := if (env.find? mkFullCand).isSome then mkFullCand else mkApiCand
        (cc, pred, bName.toString)
      | none => (false, "Core.ObeysStepFrom", "<MK_API_M>")
    let stepTemplate :=
      if isConcCell then
        s!"{stepPred} <MAP_S> <CELL_TO_MODEL> <RAW_WF> <EXEC_RAW> <RAW_ALLOWED> <PKG_WF> {builderStr} <EXEC_PKG> <PKG_ALLOWED>"
      else
        s!"{stepPred} <MAP_S> <RAW_WF> <EXEC_RAW> <RAW_ALLOWED> <PKG_WF> {builderStr} <EXEC_PKG> <PKG_ALLOWED>"
    conjuncts := conjuncts.push stepTemplate
  if conjuncts.isEmpty then
    return .error s!"EMPTY_INTERFACE_FOR_PRINT_SIG: {ifaceMod} exposes zero public operations"
  let body := String.intercalate " ∧\n    " conjuncts.toList
  let header := s!"Template for {pkg}.Proofs.obeys_model (starting skeleton; replace any <...> placeholders before compiling):"
  return .ok s!"{header}\nnamespace {pkg}.Proofs\n\ntheorem obeys_model :\n    {body}\n\nend {pkg}.Proofs"

private def isOleanArtifactName (s : String) : Bool :=
  s.endsWith ".olean" || s.endsWith ".olean.server" || s.endsWith ".olean.private"

private def withMergedOleanSearchPath {α : Type}
    (searchPaths : List System.FilePath) (k : Except String Unit → IO α) : IO α := do
  if searchPaths.length <= 1 then
    initSearchPath (← findSysroot) searchPaths
    return ← k (.ok ())
  let mk ← IO.Process.output { cmd := "mktemp", args := #["-d", "/tmp/leanswe-assump-olean.XXXXXX"] }
  if mk.exitCode != 0 then
    return ← k (.error s!"MERGED_OLEAN_DIR_ERROR: mktemp failed ({mk.stderr.trimAscii.toString})")
  let mergedDir : System.FilePath := mk.stdout.trimAscii.toString
  try
    let mut seen : Std.HashMap String System.FilePath := {}
    let mut byParent : Std.HashMap String (Array System.FilePath) := {}
    for srcDir in searchPaths do
      if !(← srcDir.isDir) then continue
      let absSrcDir ← IO.FS.realPath srcDir
      let absPrefix := absSrcDir.toString ++ "/"
      for entry in (← System.FilePath.walkDir absSrcDir) do
        if ← entry.isDir then continue
        let es := entry.toString
        if !isOleanArtifactName es || !es.startsWith absPrefix then continue
        let rel := (es.drop absPrefix.length).toString
        if let some prev := seen.get? rel then
          return ← k (.error s!"DUPLICATE_MODULE_OLEAN: {rel} exists in both {prev} and {entry}")
        seen := seen.insert rel entry
        let dst := mergedDir / rel
        let parentStr := (dst.parent.getD mergedDir).toString
        byParent := byParent.insert parentStr ((byParent.getD parentStr #[]).push entry)
    for (parentStr, srcs) in byParent.toList do
      IO.FS.createDirAll parentStr
      let ln ← IO.Process.output {
        cmd := "ln"
        args := #["-s", "-t", parentStr] ++ srcs.map (·.toString)
      }
      if ln.exitCode != 0 then
        return ← k (.error s!"MERGED_OLEAN_DIR_ERROR: ln -s failed for {parentStr} ({ln.stderr.trimAscii.toString})")
    initSearchPath (← findSysroot) [mergedDir]
    k (.ok ())
  finally
    try IO.FS.removeDirAll mergedDir catch _ => pure ()

/-- Audit compiled `.olean` artifacts for hardened checkable assumptions, error coverage, and `Core.Obeys`. -/
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
  if !cfg.coverageLogPaths.isEmpty && effectiveCovNonce?.isNone then
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
  let proofsLeanSweDir := repoDir / "proofs" / "LeanSwe"
  let hasProofsTree ← proofsLeanSweDir.isDir
  let proofsLibDir := cfg.proofsLibDir?.getD (repoDir / "proofs" / ".lake" / "build" / "lib" / "lean")
  if hasProofsTree then
    unless ← (proofsLibDir / "LeanSweProofs.olean").pathExists do
      IO.eprintln s!"MISSING_OLEAN: LeanSweProofs ({proofsLibDir / "LeanSweProofs.olean"})"
      return 1
  let hasProofsVerifiedSrc ←
    if hasProofsTree then (proofsLeanSweDir / "PostFork" / "Verified.lean").pathExists else pure false
  let hasRootVerifiedSrc ← (leanSweDir / "PostFork" / "Verified.lean").pathExists
  let hasPostForkVerifiedSrc := hasProofsVerifiedSrc || hasRootVerifiedSrc
  if hasPostForkVerifiedSrc then
    let vOlean :=
      if hasProofsVerifiedSrc then proofsLibDir / "LeanSwe" / "PostFork" / "Verified.olean"
      else libDir / "LeanSwe" / "PostFork" / "Verified.olean"
    unless ← vOlean.pathExists do
      IO.eprintln s!"MISSING_OLEAN: LeanSwe.PostFork.Verified ({vOlean})"
      return 1
  Lean.enableInitializersExecution
  let searchPaths := if hasProofsTree then [proofsLibDir, libDir] else [libDir]
  withMergedOleanSearchPath searchPaths fun spRes => do
  match spRes with
  | .error err =>
    IO.eprintln err
    return 1
  | .ok () => pure ()
  let mut rootImports : Array Import := #[{ module := `LeanSwe }]
  if hasProofsTree then
    rootImports := rootImports.push { module := `LeanSweProofs }
  if hasPostForkVerifiedSrc then
    rootImports := rootImports.push { module := `LeanSwe.PostFork.Verified }
  let env ← importModules rootImports {} (loadExts := true)
  let transImpsOf := buildTransitiveImportFn env

  let mut visited : Std.HashSet Name := {}
  let mut knownPkgSet : Std.HashSet Name := {}
  let mut knownPkgs : Array Name := #[]
  for modName in env.header.moduleNames do
    if isProjectModule modName then
      visited := visited.insert modName
      match modName with
      | .str p "SpecTests"
      | .str p "Interface" =>
        if p.getRoot == `LeanSwe && p != `LeanSwe && !knownPkgSet.contains p then
          knownPkgSet := knownPkgSet.insert p
          knownPkgs := knownPkgs.push p
      | _ => pure ()

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
  let mut seenSourceMods : Std.HashSet Name := {}
  let srcRoots : Array System.FilePath :=
    if hasProofsTree then #[leanSweDir, proofsLeanSweDir] else #[leanSweDir]
  for srcRoot in srcRoots do
    for entry in (← System.FilePath.walkDir srcRoot) do
      if entry.extension == some "lean" then
        let modName := moduleNameUnderLeanSwe srcRoot entry
        if seenSourceMods.contains modName then
          errors := errors.push s!"DUPLICATE_MODULE_SOURCE: {entry} duplicates module {modName} across Layer 1 and Layer 2"
        else
          seenSourceMods := seenSourceMods.insert modName
        if !visited.contains modName then
          errors := errors.push s!"UNIMPORTED_MODULE: {entry} (module {modName} not imported by LeanSwe)"

  let (hasSuitesJson, validSuites, suitesManifestFailed) ← match ← parseFuzzSuiteNames repoDir with
    | .ok (present, names) => pure (present, names, false)
    | .error err =>
      errors := errors.push err
      pure (false, ({} : Std.HashSet String), true)

  let (hasPkgManifest, purityMap, extBoundaryMap, fuzzSuiteMap) ← match ← parsePackageManifest repoDir with
    | .ok res => pure res
    | .error err =>
      errors := errors.push err
      pure (false, ({} : Std.HashMap Name String), ({} : Std.HashMap Name Bool), ({} : Std.HashMap Name String))

  let mut fuzzCoveredPkgs : Std.HashSet Name := {}
  if !suitesManifestFailed then
    for (pkg, suiteName) in (fuzzSuiteMap.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)) do
      if !hasSuitesJson then
        errors := errors.push s!"MISSING_FUZZ_MANIFEST: {pkg} declares fuzz_suite '{suiteName}' but harness/Fuzz/suites.json is missing"
      else if !validSuites.contains suiteName then
        errors := errors.push s!"UNKNOWN_FUZZ_SUITE: {pkg} references fuzz_suite '{suiteName}' absent from harness/Fuzz/suites.json"
      else
        fuzzCoveredPkgs := fuzzCoveredPkgs.insert pkg

  let externalAssumpJsonEntries ← match ← parseExternalAssumptionsJson repoDir hasPkgManifest with
    | .ok arr => pure arr
    | .error err =>
      errors := errors.push err
      pure #[]

  let mut covLogData : CoverageLogData := {}
  let mut hasValidCovLog := false
  let mut passingFuzzEquivPkgs : Std.HashSet Name := {}
  if (cfg.strictCentralCoverage || cfg.requireFuzzEquiv) && cfg.coverageLogPaths.isEmpty then
    errors := errors.push "MISSING_COVERAGE_LOG: --strict-central-coverage / --require-fuzz-equiv requires --coverage-log"
  if !cfg.coverageLogPaths.isEmpty then
    let expectedCovNonce := effectiveCovNonce?.getD ""
    let mut allLogsOk := true
    for covPath in cfg.coverageLogPaths do
      unless ← covPath.pathExists do
        errors := errors.push s!"MISSING_COVERAGE_LOG: {covPath}"
        allLogsOk := false
      if ← covPath.pathExists then
        let one ← parseCoverageLogFile covPath expectedCovNonce
        if one.badLines > 0 then
          errors := errors.push s!"INVALID_OR_UNAUTHENTICATED_COVERAGE_LOG_LINES: {one.badLines} lines failed nonce/format check in {covPath}"
          allLogsOk := false
        if !one.sawInit || !one.sawClose then
          errors := errors.push s!"INCOMPLETE_OR_UNINITIALIZED_COVERAGE_LOG: missing LOG_INIT or LOG_CLOSE in {covPath}"
          allLogsOk := false
        let mut mergedHits := covLogData.errHits
        for (k, modes) in one.errHits.toList do
          let prev := mergedHits.getD k {}
          let combined := modes.fold (init := prev) fun acc m => acc.insert m
          mergedHits := mergedHits.insert k combined
        covLogData := {
          errHits := mergedHits
          fuzzEquiv := covLogData.fuzzEquiv ++ one.fuzzEquiv
          badLines := covLogData.badLines + one.badLines
          sawInit := covLogData.sawInit || one.sawInit
          sawClose := covLogData.sawClose || one.sawClose
        }
    hasValidCovLog := allLogsOk
    for (pkgStr, suiteStr, steps, hit, total, okVal) in covLogData.fuzzEquiv do
      let pkgName := pkgStr.toName
      if !okVal then
        errors := errors.push s!"FUZZ_EQUIV_FAILED: {pkgStr} ({suiteStr}) reported ok=false"
      else if !(steps > 0 && hit == total && total > 0) then
        errors := errors.push s!"FUZZ_EQUIV_INCOMPLETE: {pkgStr} ({suiteStr}) reported steps={steps} buckets={hit}/{total} (requires steps > 0, total > 0, and hit == total)"
      else if (fuzzSuiteMap.get? pkgName).all (· == suiteStr) then
        passingFuzzEquivPkgs := passingFuzzEquivPkgs.insert pkgName
    for ((qualOp, kindCtor), modes) in covLogData.errHits do
      let opName := qualOp.toName
      let kindName := kindCtor.toName
      if !env.contains opName then
        errors := errors.push s!"INVALID_COVERAGE_ERR_HIT: operation {qualOp} not found in compiled environment"
      else
        match env.find? kindName with
        | some (.ctorInfo _) => pure ()
        | _ => errors := errors.push s!"INVALID_COVERAGE_ERR_HIT: error kind {kindCtor} is not an inductive constructor in compiled environment"
      if modes.contains "mocked" then
        let opMod := moduleOfConst env opName
        let opPkg :=
          if opMod != .anonymous then pkgNamespaceOfSpecWith knownPkgs opMod
          else pkgNamespaceOfSpecWith knownPkgs opName
        if isPurePackage env knownPkgs purityMap opPkg then
          errors := errors.push s!"PURE_PACKAGE_MOCKED_ERR_HIT: ({qualOp}, {kindCtor}) in pure package {opPkg}"
  if (cfg.requireFuzzEquiv || cfg.strictCentralCoverage) && hasValidCovLog then
    if covLogData.errHits.isEmpty then
      errors := errors.push "EMPTY_COVERAGE_ERR_HITS: no ERR_HIT records observed across coverage logs"
    for pkg in (fuzzCoveredPkgs.toList.toArray.qsort (fun a b => a.toString < b.toString)) do
      if !passingFuzzEquivPkgs.contains pkg then
        errors := errors.push s!"MISSING_FUZZ_EQUIV: {pkg} missing passing FUZZ_EQUIV attestation in coverage log"

  let mut specModules : Array Name := #[]
  let mut formalAssumptions : Array (Name × Name) := #[]
  let mut specAndProofRoots : Array Name := #[]
  let mut obsErrCovPkgs : Std.HashSet String := {}
  let mut obsExtAssumpPkgs : Std.HashSet String := {}
  for h : i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if !isProjectModule m then continue
    let some data := env.header.moduleData[i]? | continue
    let mPkg := pkgNamespaceOfSpecWith knownPkgs m
    for c in data.constants do
      if let .axiomInfo _ := c then
        if !allowedAxioms.contains c.name then
          errors := errors.push s!"CUSTOM_AXIOM_FORBIDDEN: {c.name} in {m}"
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
        if typeUsed.any (· == `Core.setErrTestPassHook) || valUsed.any (· == `Core.setErrTestPassHook) then
          errors := errors.push s!"FORBIDDEN_DIRECT_LOG_CALL: {c.name} in {m} mutates Core.setErrTestPassHook"
        if typeUsed.any (fun k => k == `Core.runRegisteredAssumptions || k == `Core.runRegisteredErrorTests) ||
            valUsed.any (fun k => k == `Core.runRegisteredAssumptions || k == `Core.runRegisteredErrorTests) then
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
      if m.getRoot == `LeanSwe && !isProofsModule m then
        if c.name.getString! == "errorCoverage" && !obsErrCovPkgs.contains mPkg.toString then
          obsErrCovPkgs := obsErrCovPkgs.insert mPkg.toString
          errors := errors.push s!"DISALLOWED_LEGACY_ERROR_COVERAGE: {mPkg} declares retired legacy errorCoverage"
        if c.name.getString! == "externalAssumptions" && !obsExtAssumpPkgs.contains mPkg.toString then
          obsExtAssumpPkgs := obsExtAssumpPkgs.insert mPkg.toString
          errors := errors.push s!"DISALLOWED_LEGACY_EXTERNAL_ASSUMPTIONS: {mPkg} declares retired legacy externalAssumptions"
      if c.name.getString! == "EmpiricalAssumptions" then
        errors := errors.push s!"PROSE_EMPIRICAL_ASSUMPTIONS: {c.name} in {m}"
    if m.getString! == "SpecTests" then
      let pkg := pkgNamespaceOfSpecWith knownPkgs m
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
    else if m.getRoot == `LeanSwe && !isProofsModule m &&
        (m.components.contains `Model || m.components.contains `SpecTests) then
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
  let ((metaErrs, oleanNeverErrCount, centralCellsChecked), _) ← (Meta.MetaM.run' do
    let mut errs : Array String := #[]
    let mut axCache : AxCache := {}
    let mut centralCellsN : Nat := 0

    for h : i in [0 : env.header.moduleNames.size] do
      let m := env.header.moduleNames[i]
      if !isProjectModule m || isProofsModule m then continue
      let pkg := pkgNamespaceOfSpecWith knownPkgs m
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

    let mut obeysVerifiedPkgs : Std.HashSet Name := {}
    for pkg in knownPkgs do
      let inSuites := fuzzCoveredPkgs.contains pkg
      let isExtPkg := isExternalBoundaryPkg env knownPkgs pkg
      let isFloatPkg := usesRuntimeFloat env knownPkgs pkg
      let isImpureBoundary := isExtPkg || isFloatPkg
      let hasObeysThm := env.contains (Name.str (Name.str pkg "Proofs") "obeys_model")
      if isImpureBoundary && !inSuites then
        errs := errs.push s!"MISSING_FUZZ_SUITE: external-boundary package {pkg} lacks a valid fuzz_suite in scripts/package_manifest.json"
      let modelMod := Name.str pkg "Model"
      let hasModel := visited.contains modelMod
      let hasDirectOwnExtern := hasDirectOwnExternInPkg env knownPkgs pkg
      let usesExtCli := usesExternalCliPkg env knownPkgs pkg
      let isUnprovableExternalBoundary := hasDirectOwnExtern || usesExtCli
      let needsModel := isImpureBoundary || inSuites || hasModel
      let needsRefinesModel := hasObeysThm || (!isUnprovableExternalBoundary && hasModel)
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
          let (refErrs, nextAx) ← checkRefinesModelTheorem env transImpsOf knownPkgs pkg modelMods axCache
          axCache := nextAx
          errs := errs ++ refErrs
          if refErrs.isEmpty then
            obeysVerifiedPkgs := obeysVerifiedPkgs.insert pkg

    let mut checkedSpecPkgs : Std.HashSet Name := {}
    for pkgNs in knownPkgs do
      let specMod := Name.str pkgNs "SpecTests"
      let pkgLabel := if visited.contains specMod then specMod.toString else pkgNs.toString
      checkedSpecPkgs := checkedSpecPkgs.insert pkgNs
      let isExtPkg := isExternalBoundaryPkg env knownPkgs pkgNs
      let extAssumpConst := Name.str pkgNs "externalAssumptions"
      if !isExtPkg then
        if env.contains extAssumpConst then
          errs := errs.push s!"PURE_MODULE_ASSUMPTION_FORBIDDEN: {extAssumpConst} in pure module {pkgLabel}"
      else
        let mut listedFormalPreds : Std.HashSet Name := {}
        for entry in externalAssumpJsonEntries do
          if entry.package.toName == pkgNs then
            if let some fpStr := entry.formalPred? then
              let fpName := fpStr.toName
              if formalAssumpSet.contains fpName then
                listedFormalPreds := listedFormalPreds.insert fpName
        for (m, aName) in formalAssumptions do
          if pkgNamespaceOfSpecWith knownPkgs m == pkgNs then
            if !listedFormalPreds.contains aName then
              errs := errs.push s!"UNLISTED_FORMAL_ASSUMPTION: {aName} missing from scripts/external_assumptions.json"

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

      let isManifestBoundary ←
        if hasPkgManifest then
          match extBoundaryMap.get? pkgNs with
          | some eb => pure eb
          | none =>
            errs := errs.push s!"MISSING_PACKAGE_MANIFEST_ENTRY: {pkgNs} missing from scripts/package_manifest.json"
            pure true
        else
          pure false
      let isBoundaryPkg := isExtPkg || isManifestBoundary
      if isBoundaryPkg || !fallibleReqs.isEmpty || hasAnyFallibleIfaceSurface then
        let hasModel := visited.contains (Name.str pkgNs "Model")
        let hasObeysThm := env.contains (Name.str (Name.str pkgNs "Proofs") "obeys_model")
        let isModelConstrainedNonBoundary :=
          hasPkgManifest && !isBoundaryPkg && hasModel && hasObeysThm && obeysVerifiedPkgs.contains pkgNs
        let isFuzzed := fuzzCoveredPkgs.contains pkgNs
        let hasBadCovLog := !cfg.coverageLogPaths.isEmpty && !hasValidCovLog
        if isBoundaryPkg && fallibleReqs.isEmpty && !hasAnyFallibleIfaceSurface then
          errs := errs.push s!"MISSING_ERROR_COVERAGE: {pkgNs} (external boundary package exposes zero fallible Except operations)"
        else
          let mut pkgResolvedCells : Array (Name × Name) := #[]
          let mut pkgRequiredCells : Array (Name × Name) := #[]
          for reqName in fallibleReqs do
            let some reqInfo := env.find? reqName
              | errs := errs.push s!"UNRESOLVABLE_FALLIBLE_OP: {reqName} in {pkgNs} not found in compiled environment"; continue
            let some errTyName ← extractFallibleErrorType? reqInfo.type
              | errs := errs.push s!"UNEXTRACTABLE_ERROR_TYPE: {reqName} in {pkgNs} has fallible codomain without extractable Except error type"; continue
            let some enumName ← resolveErrorKindEnum? env pkgNs errTyName
              | errs := errs.push s!"UNRESOLVABLE_ERROR_KIND_ENUM: {reqName} (error type {errTyName}) in {pkgNs}"; continue
            let some (.inductInfo enumInd) := env.find? enumName
              | errs := errs.push s!"EMPTY_OR_NON_INDUCTIVE_ERROR_ENUM: {enumName} for {reqName} in {pkgNs}"; continue
            if enumInd.ctors.isEmpty then
              errs := errs.push s!"EMPTY_OR_NON_INDUCTIVE_ERROR_ENUM: {enumName} for {reqName} in {pkgNs}"
              continue
            let opModelConstrained ← do
              if !isModelConstrainedNonBoundary then pure false
              else if moduleOfConst env reqName != ifaceMod then pure false
              else
                match reqInfo with
                | .defnInfo dv =>
                  if isPrivateName reqName || isCompilerAux reqName || env.isProjectionFn reqName then
                    pure false
                  else if (← Meta.isInstance reqName) || (← isClassInstanceOrAux env reqName dv.type) then
                    pure false
                  else if ← isCapabilityBundleConst env knownPkgs pkgNs reqName dv.type then
                    pure false
                  else
                    pure true
                | _ => pure false
            for ctor in enumInd.ctors do
              pkgResolvedCells := pkgResolvedCells.push (reqName, ctor)
              if !opModelConstrained then
                pkgRequiredCells := pkgRequiredCells.push (reqName, ctor)

          let hasZeroResolvedFallible :=
            (hasAnyFallibleIfaceSurface || !fallibleReqs.isEmpty) && pkgResolvedCells.isEmpty
          let needsRuntimeDischarge := !pkgRequiredCells.isEmpty || hasZeroResolvedFallible
          if hasBadCovLog && needsRuntimeDischarge then
            errs := errs.push s!"MISSING_ERROR_COVERAGE: {pkgNs} (invalid or incomplete coverage log)"
          else
            let runCentralDischarge :=
              cfg.strictCentralCoverage || (hasValidCovLog && (!isFuzzed || cfg.requireFuzzEquiv))
            if runCentralDischarge then
              for (reqName, ctor) in pkgRequiredCells do
                centralCellsN := centralCellsN + 1
                let cell := (reqName.toString, ctor.toString)
                let discharged :=
                  provedImpossibleCells.contains cell ||
                  covLogData.errHits.contains cell
                unless discharged do
                  errs := errs.push s!"UNCOVERED_CENTRAL_ERROR_CELL: ({reqName}, {ctor}) in {pkgNs} not discharged by NeverErrorKind* or ERR_HIT log"
              if hasZeroResolvedFallible then
                errs := errs.push s!"MISSING_ERROR_COVERAGE: {pkgNs} (central coverage checked 0 cells for fallible surface)"
            else if !isFuzzed then
              let mut hasUndischargedStatic := false
              for (reqName, ctor) in pkgRequiredCells do
                let cell := (reqName.toString, ctor.toString)
                if !provedImpossibleCells.contains cell then
                  hasUndischargedStatic := true
              if hasZeroResolvedFallible then
                errs := errs.push s!"MISSING_ERROR_COVERAGE: {pkgNs} (fallible surface has 0 resolved error cells)"
              else if hasUndischargedStatic then
                errs := errs.push s!"MISSING_ERROR_COVERAGE: {pkgNs} (pass --coverage-log or add NeverErrorKind* proofs)"

    for (m, aName) in formalAssumptions do
      let pkgNs := pkgNamespaceOfSpecWith knownPkgs m
      if !checkedSpecPkgs.contains pkgNs then
        errs := errs.push s!"UNLISTED_FORMAL_ASSUMPTION: {aName} missing from scripts/external_assumptions.json"

    let activeScanErrs := (← activeCacheRef.get).scanErrors.toArray.qsort (fun a b => a.1.toString < b.1.toString)
    for (fnName, reason) in activeScanErrs do
      errs := errs.push s!"INCONCLUSIVE_ACTIVE_CALL_CHECK: {fnName} ({reason})"

    return (errs, provedImpossibleCells.size, centralCellsN)
  ).toIO ctx state

  errors := errors ++ metaErrs
  IO.println s!"CENTRAL_COVERAGE_CHECK: olean_never_error={oleanNeverErrCount} err_hits={covLogData.errHits.size} fuzz_equiv={covLogData.fuzzEquiv.size} ext_assumps={externalAssumpJsonEntries.size} central_cells={centralCellsChecked}"
  IO.println s!"ASSUMPTION_CHECK: spec_modules={specModules.size} formal_assumptions={formalAssumptions.size} errors={errors.size}"
  if errors.isEmpty then
    return 0
  else
    for err in errors do
      IO.eprintln err
    return 1
