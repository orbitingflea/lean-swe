import Lean

/-!
Hardened checkable-assumptions and error-coverage gate audit for `lean-swe` compiled `.olean` artifacts.

Enforces:
1. Complete module & axiom hygiene:
   - Every `.lean` file under `LeanSwe/` must be transitively imported by `LeanSwe`.
   - Zero custom `axiom` declarations anywhere in `Core`, `LeanSwe`, or `Tests.Main`.
   - Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) on all `assume_*`, `CanReach`,
     upper-layer consumer theorems, and `.provedImpossible` theorems.
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
   - External-boundary modules declare `externalAssumptions : List AssumptionObligation` linking each
     obligation to a real `<pkgNs>.Interface`/`Impl` `subject` and 1-to-1 to a named `RuntimeTests` probe.
   - Formal `assume_*` predicates in `SpecTests` are allowed only when `formalPred? = some name`,
     non-trivial over the boundary parameter (`isMeaningfulBoundaryProp`), satisfiable via `Core.CanReach`,
     and consumed as a used `Prop` hypothesis (after zeta and beta reduction) in an upper-layer `Proofs` theorem.
4. Runtime linking, active execution, non-noop checks, and nonce-log anti-forgery across `Tests.Main` and `RuntimeTests`.
5. Error coverage completeness & canonical `.provedImpossible` shape (`Core.NeverErrorKind{IO,BaseIO,Pure}`).
6. Supports `--verify-log <path> [--nonce <token>]` and `--allow-legacy [<Csv>]` for phased migration.
-/

open Lean Meta

private def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.emptyWithCapacity 4 |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

private def legacyExemptionAllowlist : Array Name := #[
  `LeanSwe.Base64,
  `LeanSwe.CmdLine,
  `LeanSwe.Compress,
  `LeanSwe.ConnectProxy,
  `LeanSwe.ConnectProxy.Raw,
  `LeanSwe.CryptoHash,
  `LeanSwe.CryptoHash.Raw,
  `LeanSwe.EnvVars,
  `LeanSwe.EnvVars.Raw,
  `LeanSwe.Fs,
  `LeanSwe.Fs.Raw,
  `LeanSwe.Git,
  `LeanSwe.Glob,
  `LeanSwe.Json,
  `LeanSwe.NumParse,
  `LeanSwe.Process,
  `LeanSwe.Process.Raw,
  `LeanSwe.ProcessSandbox,
  `LeanSwe.ProcessSandbox.Raw,
  `LeanSwe.RegExp,
  `LeanSwe.SlotPool,
  `LeanSwe.Sqlite,
  `LeanSwe.Sqlite.Raw,
  `LeanSwe.Tar,
  `LeanSwe.TempDir,
  `LeanSwe.Time,
  `LeanSwe.Toml,
  `LeanSwe.Uuid,
  `LeanSwe.Uuid.Raw
]

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

private partial def hasStaticDeadBranchExpr (env : Environment) (e : Expr) : MetaM Bool := do
  let cur := e.consumeMData
  if cur.isLambda then
    return ← lambdaTelescope cur fun _ body => hasStaticDeadBranchExpr env body
  if let some (isStatic, subs) ← classifyBranchNode? env cur then
    if isStatic then return true
    for s in subs do
      if ← hasStaticDeadBranchExpr env s then return true
    return false
  match cur with
  | .app f a => return (← hasStaticDeadBranchExpr env f) || (← hasStaticDeadBranchExpr env a)
  | .letE _ _ v b _ =>
    return (← hasStaticDeadBranchExpr env v) || (← hasStaticDeadBranchExpr env (b.instantiate1 v))
  | .proj _ _ s => hasStaticDeadBranchExpr env s
  | _ => return false

private structure DeadBranchCache where
  cleanConsts : Std.HashSet Name := {}
  cleanSubgraphs : Std.HashSet Name := {}

private partial def hasStaticDeadBranchTransitive
    (env : Environment)
    (cache : DeadBranchCache)
    (start : Name) : MetaM (Bool × DeadBranchCache) := do
  let mut queue : List Name := [start]
  let mut seen : Std.HashSet Name := {}
  let mut cleanConsts := cache.cleanConsts
  let cleanSubgraphs := cache.cleanSubgraphs
  while !queue.isEmpty do
    let cur := queue.head!
    queue := queue.tail!
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
        if ← hasStaticDeadBranchExpr env body then
          return (true, { cleanConsts, cleanSubgraphs })
        cleanConsts := cleanConsts.insert cur
      for u in body.getUsedConstants do
        if !seen.contains u && !cleanSubgraphs.contains u then
          queue := u :: queue
  return (false, { cleanConsts, cleanSubgraphs := cleanSubgraphs.insert start })

private partial def stripInertBindings (env : Environment) (rtMod : Name) (e : Expr) : Expr :=
  let cur := e.consumeMData
  if cur.getAppFn.consumeMData.isLambda then
    let red := cur.headBeta
    if red != cur then stripInertBindings env rtMod red else cur
  else if cur.isAppOfArity ``Bind.bind 6 || cur.isAppOfArity ``bind 6 then
    let args := cur.getAppArgs
    let act := stripInertBindings env rtMod args[4]!
    let cont := stripInertBindings env rtMod args[5]!
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
    | .letE _ _ v b _ => stripInertBindings env rtMod (b.instantiate1 v)
    | .lam n t b bi => .lam n t (stripInertBindings env rtMod b) bi
    | .app f a => .app (stripInertBindings env rtMod f) (stripInertBindings env rtMod a)
    | .proj tn idx s => .proj tn idx (stripInertBindings env rtMod s)
    | _ => cur

private partial def exprContainsActiveTarget
    (env : Environment)
    (pred : Name → Bool)
    (e : Expr) : MetaM (Option (Array Name)) := do
  let rec collect (raw : Expr) (acc : Array Name) : MetaM (Option (Array Name)) := do
    let cur := raw.consumeMData
    if cur.isLambda then
      return ← lambdaTelescope cur fun _ body => collect body acc
    if let some (_, subs) ← classifyBranchNode? env cur then
      let mut curAcc := acc
      for s in subs do
        let some nextAcc ← collect s curAcc | return none
        curAcc := nextAcc
      return some curAcc
    match cur with
    | .const c _ =>
      if pred c then return none
      return some (acc.push c)
    | .app f a =>
      let some r1 ← collect f acc | return none
      collect a r1
    | .letE _ _ v b _ =>
      let some r1 ← collect v acc | return none
      collect (b.instantiate1 v) r1
    | .proj _ _ s => collect s acc
    | _ => return some acc
  collect e #[]

private partial def usesPredConstActive
    (env : Environment)
    (stripRtMod? : Option Name)
    (pred : Name → Bool)
    (start : Name) : MetaM Bool := do
  let mut queue : List Name := [start]
  let mut seen : Std.HashSet Name := {}
  while !queue.isEmpty do
    let cur := queue.head!
    queue := queue.tail!
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
      let body := match stripRtMod? with
        | some rtMod => stripInertBindings env rtMod rawBody
        | none => rawBody
      match ← exprContainsActiveTarget env pred body with
      | none => return true
      | some used =>
        for u in used do
          if !seen.contains u then
            queue := u :: queue
  return false

private def usesAnyConstActive
    (env : Environment)
    (targets : Std.HashSet Name)
    (start : Name) : MetaM Bool :=
  usesPredConstActive env none (fun c => targets.contains c) start

private def usesPackageImplConstActive
    (env : Environment)
    (pkgNs rtMod : Name)
    (start : Name) : MetaM Bool :=
  let ifaceMod := Name.str pkgNs "Interface"
  let implMod := Name.str pkgNs "Impl"
  usesPredConstActive env (some rtMod)
    (fun c =>
      let m := moduleOfConst env c
      (m == ifaceMod || m == implMod) && !isCompilerAux c)
    start

private partial def exprContainsAnyFVar (fvars : Std.HashSet FVarId) (e : Expr) : Bool :=
  e.hasAnyFVar (fun fv => fvars.contains fv)

private partial def isStaticFalseProp (e : Expr) : MetaM Bool := do
  let p := (← whnf e).consumeMData
  if p.isConstOf ``False then return true
  if p.isAppOfArity ``Not 1 then
    let inner := (← whnf p.appArg!).consumeMData
    if inner.isConstOf ``True then return true
    if inner.isAppOfArity ``Eq 3 then
      let args := inner.getAppArgs
      if args[1]! == args[2]! || (← isDefEq args[1]! args[2]!) then return true
  if !p.hasFVar && !p.hasLooseBVars then
    try
      let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
      let r ← withTransparency .all (whnf inst)
      if r.consumeMData.getAppFn.consumeMData.isConstOf ``Decidable.isFalse then return true
    catch _ => pure ()
  return false

private partial def isStaticTrueProp (e : Expr) : MetaM Bool := do
  let p := (← whnf e).consumeMData
  if p.isConstOf ``True then return true
  if p.isAppOfArity ``Not 1 then
    return ← isStaticFalseProp p.appArg!
  if p.isAppOfArity ``Eq 3 then
    let args := p.getAppArgs
    if args[1]! == args[2]! || (← isDefEq args[1]! args[2]!) then return true
  if !p.hasFVar && !p.hasLooseBVars then
    try
      let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
      let r ← withTransparency .all (whnf inst)
      if r.consumeMData.getAppFn.consumeMData.isConstOf ``Decidable.isTrue then return true
    catch _ => pure ()
  return false

private def isNegationPair (a b : Expr) : MetaM Bool := do
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
        if isOwnedByPkg then
          if Lean.isExtern env cname then
            return true
          if !isProcessPkg && modImportsCli.getD cMod false then
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

private structure CliConfig where
  libDir : System.FilePath := ".lake/build/lib/lean"
  repoDir : System.FilePath := "."
  logPath? : Option System.FilePath := none
  nonce? : Option String := none
  legacyAllowlist : Std.HashSet Name := {}
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

/-- Audit compiled `.olean` artifacts for hardened checkable assumptions and error coverage. -/
def main (args : List String) : IO UInt32 := do
  let cfg := parseArgs args
  if let some err := cfg.argError? then
    IO.eprintln err
    return 1
  if cfg.nonce? == some "" then
    IO.eprintln "EMPTY_NONCE_FORBIDDEN: --nonce must be non-empty"
    return 1
  let libDir := cfg.libDir
  let repoDir := cfg.repoDir
  unless ← (libDir / "LeanSwe.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: LeanSwe ({libDir / "LeanSwe.olean"})"
    return 1
  unless ← (libDir / "Tests" / "Main.olean").pathExists do
    IO.eprintln s!"MISSING_OLEAN: Tests.Main ({libDir / "Tests" / "Main.olean"})"
    return 1
  initSearchPath (← findSysroot) [libDir]
  let env ← importModules #[{ module := `LeanSwe }, { module := `Tests.Main }] {}

  let mut visited : Std.HashSet Name := {}
  let mut knownPkgs : Array Name := #[]
  for modName in env.header.moduleNames do
    if isProjectModule modName then
      visited := visited.insert modName
      if let .str p "SpecTests" := modName then
        knownPkgs := knownPkgs.push p

  let mut errors : Array String := #[]
  let leanSweDir := repoDir / "LeanSwe"
  if ← leanSweDir.pathExists then
    for entry in (← System.FilePath.walkDir leanSweDir) do
      if entry.extension == some "lean" then
        let modName := moduleNameUnderLeanSwe leanSweDir entry
        if !visited.contains modName then
          errors := errors.push s!"UNIMPORTED_MODULE: {entry} (module {modName} not imported by LeanSwe)"

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
        if isCompilerAux c.name then continue
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
        if isCompilerAux c.name then continue
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

    if env.contains `main then
      let (deadMain, dbCache') ← hasStaticDeadBranchTransitive env dbCache `main
      dbCache := dbCache'
      if deadMain then
        errs := errs.push "DEAD_CONDITIONAL_IN_RUNNER: main in Tests.Main"
      unless ← usesAnyConstActive env (Std.HashSet.emptyWithCapacity 1 |>.insert `Core.initAssumpLog) `main do
        errs := errs.push "MISSING_ASSUMP_LOG_INIT: main does not call Core.initAssumpLog"
      unless ← usesAnyConstActive env (Std.HashSet.emptyWithCapacity 1 |>.insert `Core.closeAssumpLog) `main do
        errs := errs.push "MISSING_ASSUMP_LOG_CLOSE: main does not call Core.closeAssumpLog"
    else
      errs := errs.push "MISSING_MAIN: Tests.Main lacks main"

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
        if ← usesAnyConstActive env (Std.HashSet.emptyWithCapacity 1 |>.insert cand) `main then
          activeEntry? := some cand
          break
      let runAllName := activeEntry?.getD (candidates[0]?.getD candidateRunAll)
      if candidates.isEmpty then
        errs := errs.push s!"MISSING_RUNALL: {rtMod} lacks runAll / runAllOutcome"
      else
        let (deadRunAll, dbCache') ← hasStaticDeadBranchTransitive env dbCache runAllName
        dbCache := dbCache'
        if deadRunAll then
          errs := errs.push s!"DEAD_CONDITIONAL_IN_RUNNER: {runAllName}"
        if activeEntry?.isNone then
          errs := errs.push s!"UNREGISTERED_RUNTIMETESTS_IN_MAIN: {runAllName} not actively invoked from main"

      let extAssumpConst := Name.str pkgNs "externalAssumptions"
      let regAssumpConst := Name.str rtMod "registeredAssumptions"
      if !isExtPkg then
        if env.contains extAssumpConst then
          errs := errs.push s!"PURE_MODULE_ASSUMPTION_FORBIDDEN: {extAssumpConst} in pure module {specMod}"
        if env.contains regAssumpConst then
          errs := errs.push s!"PURE_MODULE_ASSUMPTION_FORBIDDEN: {regAssumpConst} in pure module {rtMod}"
      else
        let mut regAssumpMap : Std.HashMap String Name := {}
        if let some (.defnInfo dv) := env.find? regAssumpConst then
          unless ← usesAnyConstActive env (Std.HashSet.emptyWithCapacity 1 |>.insert regAssumpConst) runAllName do
            errs := errs.push s!"REGISTERED_ASSUMPTIONS_NOT_RUN: {runAllName} does not actively execute {regAssumpConst}"
          if let some elems ← extractArrayElems dv.value then
            for elem in elems do
              if let some (specName, runFn) ← parseRegisteredAssumption elem then
                let runClean := runFn.consumeMData
                if let .const fnName _ := runClean then
                  if moduleOfConst env fnName != rtMod || fnName.getString! != specName.toName.getString! then
                    errs := errs.push s!"RUNTIME_ASSUMPTION_NAME_MISMATCH: {specName} bound to {fnName}"
                  else
                    let (deadFn, dbCache') ← hasStaticDeadBranchTransitive env dbCache fnName
                    dbCache := dbCache'
                    if deadFn then
                      errs := errs.push s!"DEAD_CONDITIONAL_IN_TEST: {fnName}"
                    unless ← usesAnyConstActive env throwTargets fnName do
                      errs := errs.push s!"TRIVIAL_RUNTIME_ASSUMPTION: {fnName} has no active failure/throw path"
                    unless ← usesPackageImplConstActive env pkgNs rtMod fnName do
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
              if !regAssumpMap.contains obName then
                errs := errs.push s!"MISSING_ASSUMPTION_TEST: {obName} not registered in {regAssumpConst}"
              expAssumps := expAssumps.push obName
          else
            errs := errs.push s!"UNPARSEABLE_EXTERNAL_ASSUMPTIONS: {extAssumpConst}"
        else
          errs := errs.push s!"MISSING_EXTERNAL_ASSUMPTIONS: {extAssumpConst}"

        for (m, aName) in formalAssumptions do
          if m == specMod && !listedFormalPreds.contains aName then
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
        if let some (.defnInfo dv) := env.find? regErrConst then
          unless ← usesAnyConstActive env (Std.HashSet.emptyWithCapacity 1 |>.insert regErrConst) runAllName do
            errs := errs.push s!"REGISTERED_ERROR_TESTS_NOT_RUN: {runAllName} does not actively execute {regErrConst}"
          if let some elems ← extractArrayElems dv.value then
            for elem in elems do
              if let some (tName, modeCtor, runFn) ← parseRegisteredErrorTest elem then
                let runClean := runFn.consumeMData
                if let .const fnName _ := runClean then
                  if moduleOfConst env fnName != rtMod || fnName.toString != tName then
                    errs := errs.push s!"ERROR_TEST_NAME_MISMATCH: {tName} bound to {fnName}"
                  else
                    let (deadErrFn, dbCache') ← hasStaticDeadBranchTransitive env dbCache fnName
                    dbCache := dbCache'
                    if deadErrFn then
                      errs := errs.push s!"DEAD_CONDITIONAL_IN_TEST: {fnName}"
                    unless ← usesAnyConstActive env throwTargets fnName do
                      errs := errs.push s!"TRIVIAL_ERROR_TEST: {fnName} has no active failure/throw path"
                    unless ← usesPackageImplConstActive env pkgNs rtMod fnName do
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
            else
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
