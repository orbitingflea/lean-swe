import LeanSwe.Sqlite.Types
import LeanSwe.Sqlite.Model

namespace Fuzz.Sqlite

open LeanSwe.Sqlite

/-- Target database specification resolved inside an isolated per-episode workspace. -/
inductive TargetSpec where
  /-- Ephemeral `":memory:"` database. -/
  | memory
  /-- Shared writable slot `<epDir>/db0.sqlite`. -/
  | db0
  /-- Shared writable slot `<epDir>/db1.sqlite`. -/
  | db1
  /-- Uncreated file `<epDir>/missing.sqlite`. -/
  | missing
  /-- Path under missing parent `<epDir>/no_such_dir/db.sqlite`. -/
  | missingParent
  /-- Pre-existing directory `<epDir>/subdir`. -/
  | subdir
  /-- Pre-seeded `0444` read-only file `<epDir>/ro0444.sqlite`. -/
  | ro0444
  /-- Pre-seeded `0444` read-only WAL-mode file `<epDir>/walro0444.sqlite`. -/
  | walRo0444
  /-- Pre-seeded corrupt non-SQLite file `<epDir>/corrupt.sqlite`. -/
  | corrupt
  /-- Chained symlink `<epDir>/sym_deep.sqlite -> sym_db0.sqlite -> db0.sqlite`. -/
  | symDeep
  /-- Long 45-hop symlink chain `<epDir>/sym_45.sqlite -> ... -> db0.sqlite` (`SQLITE_MAX_SYMLINK = 200`). -/
  | sym45
  /-- Circular symlink pair `<epDir>/sym_loop_a.sqlite <-> sym_loop_b.sqlite`. -/
  | symLoop
  /-- Relative `../` symlink `<epDir>/subdir/sym_rel_db0.sqlite -> ../db0.sqlite`. -/
  | symRelDb0
  /-- File accessed through directory symlink `<epDir>/sym_dir/db_via_sym.sqlite`. -/
  | symDirDb0
  /-- Dangling symlink `<epDir>/sym_dangling.sqlite -> dangling_target.sqlite`. -/
  | symDangling
  /-- Path formed by appending `suffix` onto `<epDir>` (testing `.`/`..`/`//`/trailing `/`). -/
  | epSuffix (suffix : String)
  /-- `"file:"` URI formed by concatenating `uriPrefix ++ <epDir> ++ suffix`. -/
  | epUri (uriPrefix : String) (suffix : String)
  /-- Multi-segment path under `<epDir>/a{200}/b{200}/...` padded to exact UTF-8 byte length `totalBytes`. -/
  | exactPathBytes (totalBytes : Nat)
  /-- Intermediate path under `<epDir>/a{200}/b{200}/...` of exact `intermBytes` bytes followed by `/../../../db0.sqlite`. -/
  | intermDotDotBytes (intermBytes : Nat)
  /-- Unsanitized raw path string (`""`, embedded NUL, `"file:"` URI, oversized). -/
  | raw (path : String)
  deriving Repr, BEq

/-- Resolve `TargetSpec` to the filesystem or special path string passed to `Sqlite.withDb`. -/
def TargetSpec.resolve (epDir : System.FilePath) : TargetSpec → String
  | .memory => ":memory:"
  | .db0 => (epDir / "db0.sqlite").toString
  | .db1 => (epDir / "db1.sqlite").toString
  | .missing => (epDir / "missing.sqlite").toString
  | .missingParent => (epDir / "no_such_dir" / "db.sqlite").toString
  | .subdir => (epDir / "subdir").toString
  | .ro0444 => (epDir / "ro0444.sqlite").toString
  | .walRo0444 => (epDir / "walro0444.sqlite").toString
  | .corrupt => (epDir / "corrupt.sqlite").toString
  | .symDeep => (epDir / "sym_deep.sqlite").toString
  | .sym45 => (epDir / "sym_45.sqlite").toString
  | .symLoop => (epDir / "sym_loop_a.sqlite").toString
  | .symRelDb0 => (epDir / "subdir" / "sym_rel_db0.sqlite").toString
  | .symDirDb0 => (epDir / "sym_dir" / "db_via_sym.sqlite").toString
  | .symDangling => (epDir / "sym_dangling.sqlite").toString
  | .epSuffix suf => epDir.toString ++ suf
  | .epUri uriPre suf => uriPre ++ epDir.toString ++ suf
  | .exactPathBytes totalBytes =>
    let d1 := String.ofList (List.replicate 200 'a')
    let d2 := String.ofList (List.replicate 200 'b')
    let base := (epDir / d1 / d2).toString ++ "/"
    let rem := if totalBytes > base.toUTF8.size then totalBytes - base.toUTF8.size else 1
    base ++ String.ofList (List.replicate rem 'f')
  | .intermDotDotBytes intermBytes =>
    let d1 := String.ofList (List.replicate 200 'a')
    let d2 := String.ofList (List.replicate 200 'b')
    let base := (epDir / d1 / d2).toString ++ "/"
    let rem := if intermBytes > base.toUTF8.size then intermBytes - base.toUTF8.size else 1
    base ++ String.ofList (List.replicate rem 'c') ++ "/../../../db0.sqlite"
  | .raw p => p

/-- Reference to a closed or forged `DbHandle` tested outside `withDb`. -/
inductive ClosedHandleRef where
  /-- Zero handle `{ id := 0 }`. -/
  | zero
  /-- Unused large handle `{ id := 999999 }`. -/
  | huge
  /-- Arbitrary raw `UInt64` handle id. -/
  | raw (id : UInt64)
  /-- Previously closed genuine `DbHandle` captured from `escapedHandles[idx]`. -/
  | escaped (idx : Nat)
  deriving Repr, BEq

/-- Leaf SQL statement operation against an open or closed `DbHandle`. -/
inductive LeafSqlOp where
  /-- Execute non-query or DDL/DML/control SQL via `exec`. -/
  | exec (sql : String) (params : Array SqliteValue)
  /-- Query all rows via `query`. -/
  | query (sql : String) (params : Array SqliteValue)
  /-- Query optional first row via `queryOne`. -/
  | queryOne (sql : String) (params : Array SqliteValue)
  deriving Repr, BEq

/-- Return or exception exit mode for `withDb` and `withTransaction` scopes. -/
inductive ExitMode where
  /-- Normal `.ok ()` completion. -/
  | returnOk
  /-- Caller-returned `.error err`. -/
  | returnCallerErr (err : SqliteError)
  /-- Thrown `IO.userError msg` escaping the scope via `MonadFinally`. -/
  | throwIoUserError (msg : String)
  deriving Repr, BEq

/-- Connection-scoped operation executed inside an open `withDb` callback. -/
inductive DbConnOp where
  /-- Single `exec`, `query`, or `queryOne` call. -/
  | leaf (op : LeafSqlOp)
  /-- Transaction scope `withTransaction db` running `txOps` then exiting via `exitMode`. -/
  | withTx (txOps : Array LeafSqlOp) (exitMode : ExitMode)
  /-- Nested second `withDb` session (`db2`) interleaving operations (`false` = `db1`, `true` = `db2`). -/
  | nestedWithDb (target2 : TargetSpec) (cfg2 : OpenConfig)
      (dualOps : Array (Bool × LeafSqlOp)) (exitMode2 : ExitMode)
  deriving Repr, BEq

/-- Single low-level `RawSqliteOps` operation inside a lockstep `rawSession` trace. -/
inductive RawStepOp where
  /-- Prepare `sql` into statement slot `slot`. -/
  | prepare (slot : Nat) (sql : String)
  /-- Bind `params` to statement in `slot`. -/
  | bind (slot : Nat) (params : Array SqliteValue)
  /-- Step statement in `slot` once. -/
  | step (slot : Nat)
  /-- Finalize statement in `slot`. -/
  | finalize (slot : Nat)
  /-- Execute `sql` with `params` on an auxiliary peer connection against the same target. -/
  | peerExec (sql : String) (params : Array SqliteValue)
  /-- Execute `sql` with `params` on an auxiliary `Raw.openDb` peer connection (supporting `"file:"` URIs). -/
  | rawPeerExec (target : TargetSpec) (cfg : OpenConfig) (sql : String) (params : Array SqliteValue)
  deriving Repr, BEq

/-- Top-level action inside a differential fuzz episode. -/
inductive TopAction where
  /-- Check `Sqlite.validateConfig cfg == Model.validateConfig cfg`. -/
  | validateConfig (cfg : OpenConfig)
  /-- Check `Sqlite.mapRawError raw == Model.mapRawError raw`. -/
  | mapRawError (raw : SqliteRawError)
  /-- Call `exec`/`query`/`queryOne` on a closed or forged `DbHandle`. -/
  | closedHandleOp (ref : ClosedHandleRef) (op : LeafSqlOp)
  /-- Call `withTransaction` on a closed or forged `DbHandle`. -/
  | closedHandleTx (ref : ClosedHandleRef) (txOps : Array LeafSqlOp) (exitMode : ExitMode)
  /-- Open `withDb` session, execute `ops`, and close via `exitMode`. -/
  | withDbSession (target : TargetSpec) (cfg : OpenConfig) (ops : Array DbConnOp) (exitMode : ExitMode)
  /-- Exercise stateful `Raw.{openDb, prepare, bind, step, finalize, closeDb}` lockstep against `Model.modelRawOps`. -/
  | rawSession (target : TargetSpec) (cfg : OpenConfig) (ops : Array RawStepOp)
  deriving Repr, BEq

/-- Complete stateful differential fuzz episode. -/
abbrev SqliteEpisode := Array TopAction

/-- Produce smaller `SqliteValue` candidates for inner-pass trace shrinking. -/
def shrinkSqliteValue : SqliteValue → List SqliteValue
  | .null => []
  | .int i => if i == 0 then [.null] else [.null, .int 0]
  | .real f =>
    if f.toBits == 0 then [.null] else [.null, .real 0.0]
  | .text s =>
    if s.isEmpty then [.null] else [.null, .text ""]
  | .bytes b =>
    if b.isEmpty then [.null] else [.null, .bytes ByteArray.empty]

private def shrinkParamsList (params : Array SqliteValue) : List (Array SqliteValue) :=
  let dropLast := if params.isEmpty then [] else [params.extract 0 (params.size - 1)]
  let shrinkEach :=
    Id.run do
      let mut out : List (Array SqliteValue) := []
      for i in List.range params.size do
        match params[i]? with
        | some v =>
          for v' in shrinkSqliteValue v do
            out := out ++ [params.setIfInBounds i v']
        | none => pure ()
      return out
  dropLast ++ shrinkEach

private def shrinkLeafWith (ctor : String → Array SqliteValue → LeafSqlOp)
    (sql : String) (params : Array SqliteValue) : List LeafSqlOp :=
  (shrinkParamsList params).map (ctor sql)

/-- Produce smaller `LeafSqlOp` candidates (dropping params or shrinking any parameter payload). -/
def shrinkLeafSqlOp : LeafSqlOp → List LeafSqlOp
  | .exec sql params => shrinkLeafWith .exec sql params
  | .query sql params => shrinkLeafWith .query sql params
  | .queryOne sql params => shrinkLeafWith .queryOne sql params

private def shrinkArrayDrop {α : Type} (xs : Array α) : List (Array α) :=
  if xs.isEmpty then []
  else if xs.size == 1 then [#[]]
  else
    let half := xs.size / 2
    let base := [#[], xs.extract 0 half, xs.extract half xs.size]
    let singles : List (Array α) :=
      (List.range xs.size).map fun i => xs.extract 0 i ++ xs.extract (i + 1) xs.size
    base ++ singles

private def shrinkClosedHandleRef : ClosedHandleRef → List ClosedHandleRef
  | .zero => []
  | _ => [.zero]

private def shrinkTargetSpec : TargetSpec → List TargetSpec
  | .memory => []
  | .db0 => [.memory]
  | .raw "" => [.memory]
  | .raw _ => [.raw "", .memory]
  | .epUri _ _ => [.memory, .db0]
  | .exactPathBytes n =>
    (if n > 505 then [.exactPathBytes 505] else []) ++ [.memory, .db0]
  | .intermDotDotBytes n =>
    (if n > 512 then [.intermDotDotBytes 512] else []) ++ [.memory, .db0]
  | _ => [.memory, .db0]

private def shrinkOpenConfig (cfg : OpenConfig) : List OpenConfig :=
  let out0 :=
    if cfg.busyTimeoutMs > maxBusyTimeoutMs + 1 then
      [{ cfg with busyTimeoutMs := maxBusyTimeoutMs + 1 }]
    else []
  let out1 := if cfg.busyTimeoutMs != 0 then [{ cfg with busyTimeoutMs := 0 }] else []
  let out2 := if cfg.foreignKeys then [{ cfg with foreignKeys := false }] else []
  let out3 := if cfg.walMode then [{ cfg with walMode := false }] else []
  let out4 := if cfg.readOnly then [{ cfg with readOnly := false }] else []
  let out5 := if cfg.createIfMissing then [{ cfg with createIfMissing := false }] else []
  out0 ++ out1 ++ out2 ++ out3 ++ out4 ++ out5

private def shrinkRawError : SqliteRawError → List SqliteRawError
  | .cantOpen path? code detail =>
    let pCands :=
      match path? with
      | none => []
      | some p =>
        if p.isEmpty then [.cantOpen none code detail]
        else [.cantOpen none code detail, .cantOpen (some "") code detail]
    let dCands := if detail.isEmpty then [] else [.cantOpen path? code ""]
    pCands ++ dCands
  | .busy code detail => if detail.isEmpty then [] else [.busy code ""]
  | .constraint code detail => if detail.isEmpty then [] else [.constraint code ""]
  | .misuse code detail => if detail.isEmpty then [] else [.misuse code ""]
  | .invalidArgument detail => if detail.isEmpty then [] else [.invalidArgument ""]
  | .ioFailure code detail => if detail.isEmpty then [] else [.ioFailure code ""]
  | .sqliteCodeError code detail => if detail.isEmpty then [] else [.sqliteCodeError code ""]
  | .userError detail => if detail.isEmpty then [] else [.userError ""]

private def rawStepUsesNonZeroSlot : RawStepOp → Bool
  | .prepare slot _ | .bind slot _ | .step slot | .finalize slot => slot > 0
  | .peerExec _ _ | .rawPeerExec _ _ _ _ => false

private def rawStepZeroSlot : RawStepOp → RawStepOp
  | .prepare _ sql => .prepare 0 sql
  | .bind _ ps => .bind 0 ps
  | .step _ => .step 0
  | .finalize _ => .finalize 0
  | other => other

private def shrinkRawStepOp : RawStepOp → List RawStepOp
  | .prepare slot sql =>
    if slot > 0 then [.prepare 0 sql] else []
  | .bind slot ps =>
    (if slot > 0 then [.bind 0 ps] else []) ++ (shrinkParamsList ps).map (.bind slot)
  | .step slot =>
    if slot > 0 then [.step 0] else []
  | .finalize slot =>
    if slot > 0 then [.finalize 0] else []
  | .peerExec sql ps => (shrinkParamsList ps).map (.peerExec sql)
  | .rawPeerExec tgt pCfg sql ps =>
    [.peerExec sql ps] ++
    (shrinkTargetSpec tgt).map (fun t' => .rawPeerExec t' pCfg sql ps) ++
    (shrinkOpenConfig pCfg).map (fun c' => .rawPeerExec tgt c' sql ps) ++
    (shrinkParamsList ps).map (.rawPeerExec tgt pCfg sql)

/-- Produce smaller `DbConnOp` candidates for pass-2 shrinking. -/
def shrinkDbConnOp : DbConnOp → List DbConnOp
  | .leaf op => (shrinkLeafSqlOp op).map .leaf
  | .withTx txOps exitMode =>
    let unwrap :=
      if txOps.size == 1 && exitMode == .returnOk then
        match txOps[0]? with
        | some op => [.leaf op]
        | none => []
      else []
    let subArrays := (shrinkArrayDrop txOps).map fun sub => DbConnOp.withTx sub exitMode
    let shrinkInner :=
      Id.run do
        let mut out : List DbConnOp := []
        for i in List.range txOps.size do
          match txOps[i]? with
          | some op =>
            for op' in shrinkLeafSqlOp op do
              out := out ++ [DbConnOp.withTx (txOps.setIfInBounds i op') exitMode]
          | none => pure ()
        return out
    let simpExit :=
      match exitMode with
      | .returnOk => []
      | _ => [DbConnOp.withTx txOps .returnOk]
    unwrap ++ subArrays ++ shrinkInner ++ simpExit
  | .nestedWithDb t2 cfg2 dualOps exitMode2 =>
    let unwrap :=
      if dualOps.size == 1 then
        match dualOps[0]? with
        | some (false, op) => [.leaf op]
        | _ => []
      else []
    let flipAllToFirst :=
      if dualOps.any (·.1) then
        [DbConnOp.nestedWithDb t2 cfg2 (dualOps.map fun (_, op) => (false, op)) exitMode2]
      else []
    let subArrays := (shrinkArrayDrop dualOps).map fun sub =>
      DbConnOp.nestedWithDb t2 cfg2 sub exitMode2
    let shrinkInner :=
      Id.run do
        let mut out : List DbConnOp := []
        for i in List.range dualOps.size do
          match dualOps[i]? with
          | some (b, op) =>
            if b then
              out := out ++ [DbConnOp.nestedWithDb t2 cfg2 (dualOps.setIfInBounds i (false, op)) exitMode2]
            for op' in shrinkLeafSqlOp op do
              out := out ++ [DbConnOp.nestedWithDb t2 cfg2 (dualOps.setIfInBounds i (b, op')) exitMode2]
          | none => pure ()
        return out
    let simpTarget := (shrinkTargetSpec t2).map fun t2' => DbConnOp.nestedWithDb t2' cfg2 dualOps exitMode2
    let simpCfg := (shrinkOpenConfig cfg2).map fun cfg2' => DbConnOp.nestedWithDb t2 cfg2' dualOps exitMode2
    let simpExit :=
      match exitMode2 with
      | .returnOk => []
      | _ => [DbConnOp.nestedWithDb t2 cfg2 dualOps .returnOk]
    unwrap ++ flipAllToFirst ++ subArrays ++ shrinkInner ++ simpTarget ++ simpCfg ++ simpExit

/-- Produce smaller `TopAction` candidates for pass-2 element shrinking. -/
def shrinkTopAction : TopAction → List TopAction
  | .validateConfig cfg => (shrinkOpenConfig cfg).map .validateConfig
  | .mapRawError raw => (shrinkRawError raw).map .mapRawError
  | .closedHandleOp ref op =>
    (shrinkClosedHandleRef ref).map (fun r' => .closedHandleOp r' op) ++
    (shrinkLeafSqlOp op).map (.closedHandleOp ref)
  | .closedHandleTx ref txOps exitMode =>
    let simpRef := (shrinkClosedHandleRef ref).map fun r' => .closedHandleTx r' txOps exitMode
    let unwrap :=
      if txOps.size == 1 then
        match txOps[0]? with
        | some op => [.closedHandleOp ref op]
        | none => []
      else []
    let subArrays := (shrinkArrayDrop txOps).map fun sub => .closedHandleTx ref sub exitMode
    let shrinkInner :=
      Id.run do
        let mut out : List TopAction := []
        for i in List.range txOps.size do
          match txOps[i]? with
          | some op =>
            for op' in shrinkLeafSqlOp op do
              out := out ++ [TopAction.closedHandleTx ref (txOps.setIfInBounds i op') exitMode]
          | none => pure ()
        return out
    let simpExit :=
      match exitMode with
      | .returnOk => []
      | _ => [TopAction.closedHandleTx ref txOps .returnOk]
    unwrap ++ simpRef ++ subArrays ++ shrinkInner ++ simpExit
  | .withDbSession target cfg ops exitMode =>
    let subOps := (shrinkArrayDrop ops).map fun sub =>
      TopAction.withDbSession target cfg sub exitMode
    let spliceWrapped :=
      Id.run do
        let mut out : List TopAction := []
        for i in List.range ops.size do
          match ops[i]? with
          | some (.nestedWithDb _ _ dualOps _) =>
            if dualOps.all (!·.1) then
              let lifted := dualOps.map fun p => DbConnOp.leaf p.2
              let nextOps := ops.extract 0 i ++ lifted ++ ops.extract (i + 1) ops.size
              out := out ++ [TopAction.withDbSession target cfg nextOps exitMode]
          | some (.withTx txOps .returnOk) =>
            let lifted := txOps.map DbConnOp.leaf
            let nextOps := ops.extract 0 i ++ lifted ++ ops.extract (i + 1) ops.size
            out := out ++ [TopAction.withDbSession target cfg nextOps exitMode]
          | _ => pure ()
        return out
    let shrinkEachOp :=
      Id.run do
        let mut out : List TopAction := []
        for i in List.range ops.size do
          match ops[i]? with
          | some op =>
            for op' in shrinkDbConnOp op do
              out := out ++ [TopAction.withDbSession target cfg (ops.setIfInBounds i op') exitMode]
          | none => pure ()
        return out
    let promoteNested :=
      Id.run do
        let mut out : List TopAction := []
        for op in ops do
          match op with
          | .nestedWithDb t2 cfg2 dualOps em2 =>
            if dualOps.all (·.1) then
              out := out ++ [TopAction.withDbSession t2 cfg2 (dualOps.map fun p => DbConnOp.leaf p.2) em2]
          | _ => pure ()
        return out
    let simpTarget := (shrinkTargetSpec target).map fun t' => TopAction.withDbSession t' cfg ops exitMode
    let simpCfg := (shrinkOpenConfig cfg).map fun c' => TopAction.withDbSession target c' ops exitMode
    let simpExit :=
      match exitMode with
      | .returnOk => []
      | _ => [TopAction.withDbSession target cfg ops .returnOk]
    promoteNested ++ spliceWrapped ++ subOps ++ shrinkEachOp ++ simpTarget ++ simpCfg ++ simpExit
  | .rawSession target cfg ops =>
    let normSlots :=
      if ops.any rawStepUsesNonZeroSlot then
        [TopAction.rawSession target cfg (ops.map rawStepZeroSlot)]
      else []
    let subOps := (shrinkArrayDrop ops).map fun sub =>
      TopAction.rawSession target cfg sub
    let shrinkEachOp :=
      Id.run do
        let mut out : List TopAction := []
        for i in List.range ops.size do
          match ops[i]? with
          | some op =>
            for op' in shrinkRawStepOp op do
              out := out ++ [TopAction.rawSession target cfg (ops.setIfInBounds i op')]
          | none => pure ()
        return out
    let simpTarget := (shrinkTargetSpec target).map fun t' => TopAction.rawSession t' cfg ops
    let simpCfg := (shrinkOpenConfig cfg).map fun c' => TopAction.rawSession target c' ops
    normSlots ++ subOps ++ shrinkEachOp ++ simpTarget ++ simpCfg

end Fuzz.Sqlite
